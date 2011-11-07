/*
 * Userspace Probes (UProbes)
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (C) IBM Corporation, 2008-2011
 * Authors:
 *	Srikar Dronamraju
 *	Jim Keniston
 */

#include <linux/kernel.h>
#include <linux/highmem.h>
#include <linux/pagemap.h>	/* grab_cache_page */
#include <linux/slab.h>
#include <linux/sched.h>
#include <linux/rmap.h>		/* anon_vma_prepare */
#include <linux/mmu_notifier.h>	/* set_pte_at_notify */
#include <linux/swap.h>		/* try_to_free_swap */
#include <linux/ptrace.h>	/* user_enable_single_step */
#include <linux/kdebug.h>	/* notifier mechanism */
#include <linux/mman.h>		/* PROT_EXEC, MAP_PRIVATE */
#include <linux/init_task.h>	/* init_cred */
#include <linux/uprobes.h>

#define UINSNS_PER_PAGE	(PAGE_SIZE/UPROBES_XOL_SLOT_BYTES)
#define MAX_UPROBES_XOL_SLOTS UINSNS_PER_PAGE

static struct rb_root uprobes_tree = RB_ROOT;
static DEFINE_SPINLOCK(uprobes_treelock);	/* serialize (un)register */
static DEFINE_MUTEX(uprobes_mmap_mutex);	/* uprobe->pending_list */

/*
 * Maintain a temporary per vma info that can be used to search if a vma
 * has already been handled. This structure is introduced since extending
 * vm_area_struct wasnt recommended.
 */
struct vma_info {
	struct list_head probe_list;
	struct mm_struct *mm;
	loff_t vaddr;
};

/*
 * valid_vma: Verify if the specified vma is an executable vma,
 * but not an XOL vma.
 *	- Return 1 if the specified virtual address is in an
 *	  executable vma, but not in an XOL vma.
 */
static bool valid_vma(struct vm_area_struct *vma)
{
	struct uprobes_xol_area *area = vma->vm_mm->uprobes_xol_area;

	if (!vma->vm_file)
		return false;

	if (area && (area->vaddr == vma->vm_start))
			return false;

	if ((vma->vm_flags & (VM_READ|VM_WRITE|VM_EXEC|VM_SHARED)) ==
						(VM_READ|VM_EXEC))
		return true;

	return false;
}

/**
 * __replace_page - replace page in vma by new page.
 * based on replace_page in mm/ksm.c
 *
 * @vma:      vma that holds the pte pointing to page
 * @page:     the cowed page we are replacing by kpage
 * @kpage:    the modified page we replace page by
 *
 * Returns 0 on success, -EFAULT on failure.
 */
static int __replace_page(struct vm_area_struct *vma, struct page *page,
					struct page *kpage)
{
	struct mm_struct *mm = vma->vm_mm;
	pgd_t *pgd;
	pud_t *pud;
	pmd_t *pmd;
	pte_t *ptep;
	spinlock_t *ptl;
	unsigned long addr;
	int err = -EFAULT;

	addr = page_address_in_vma(page, vma);
	if (addr == -EFAULT)
		goto out;

	pgd = pgd_offset(mm, addr);
	if (!pgd_present(*pgd))
		goto out;

	pud = pud_offset(pgd, addr);
	if (!pud_present(*pud))
		goto out;

	pmd = pmd_offset(pud, addr);
	if (!pmd_present(*pmd))
		goto out;

	ptep = pte_offset_map_lock(mm, pmd, addr, &ptl);
	if (!ptep)
		goto out;

	get_page(kpage);
	page_add_new_anon_rmap(kpage, vma, addr);

	flush_cache_page(vma, addr, pte_pfn(*ptep));
	ptep_clear_flush(vma, addr, ptep);
	set_pte_at_notify(mm, addr, ptep, mk_pte(kpage, vma->vm_page_prot));

	page_remove_rmap(page);
	if (!page_mapped(page))
		try_to_free_swap(page);
	put_page(page);
	pte_unmap_unlock(ptep, ptl);
	err = 0;

out:
	return err;
}

/*
 * NOTE:
 * Expect the breakpoint instruction to be the smallest size instruction for
 * the architecture. If an arch has variable length instruction and the
 * breakpoint instruction is not of the smallest length instruction
 * supported by that architecture then we need to modify read_opcode /
 * write_opcode accordingly. This would never be a problem for archs that
 * have fixed length instructions.
 */

/*
 * write_opcode - write the opcode at a given virtual address.
 * @tsk: the probed task.
 * @uprobe: the breakpointing information.
 * @vaddr: the virtual address to store the opcode.
 * @opcode: opcode to be written at @vaddr.
 *
 * Called with tsk->mm->mmap_sem held (for read and with a reference to
 * tsk->mm).
 *
 * For task @tsk, write the opcode at @vaddr.
 * Return 0 (success) or a negative errno.
 */
static int write_opcode(struct task_struct *tsk, struct uprobe * uprobe,
			unsigned long vaddr, uprobe_opcode_t opcode)
{
	struct page *old_page, *new_page;
	struct address_space *mapping;
	void *vaddr_old, *vaddr_new;
	struct vm_area_struct *vma;
	unsigned long addr;
	int ret;

	/* Read the page with vaddr into memory */
	ret = get_user_pages(tsk, tsk->mm, vaddr, 1, 0, 0, &old_page, &vma);
	if (ret <= 0)
		return ret;
	ret = -EINVAL;

	/*
	 * We are interested in text pages only. Our pages of interest
	 * should be mapped for read and execute only. We desist from
	 * adding probes in write mapped pages since the breakpoints
	 * might end up in the file copy.
	 */
	if (!valid_vma(vma))
		goto put_out;

	mapping = uprobe->inode->i_mapping;
	if (mapping != vma->vm_file->f_mapping)
		goto put_out;

	addr = vma->vm_start + uprobe->offset;
	addr -= vma->vm_pgoff << PAGE_SHIFT;
	if (vaddr != (unsigned long) addr)
		goto put_out;

	/* Allocate a page */
	new_page = alloc_page_vma(GFP_HIGHUSER_MOVABLE, vma, vaddr);
	if (!new_page) {
		ret = -ENOMEM;
		goto put_out;
	}

	/*
	 * lock page will serialize against do_wp_page()'s
	 * PageAnon() handling
	 */
	lock_page(old_page);
	/* copy the page now that we've got it stable */
	vaddr_old = kmap_atomic(old_page);
	vaddr_new = kmap_atomic(new_page);

	memcpy(vaddr_new, vaddr_old, PAGE_SIZE);
	/* poke the new insn in, ASSUMES we don't cross page boundary */
	vaddr &= ~PAGE_MASK;
	memcpy(vaddr_new + vaddr, &opcode, uprobe_opcode_sz);

	kunmap_atomic(vaddr_new);
	kunmap_atomic(vaddr_old);

	ret = anon_vma_prepare(vma);
	if (ret) {
		page_cache_release(new_page);
		goto unlock_out;
	}

	lock_page(new_page);
	ret = __replace_page(vma, old_page, new_page);
	unlock_page(new_page);
	if (ret != 0)
		page_cache_release(new_page);
unlock_out:
	unlock_page(old_page);

put_out:
	put_page(old_page); /* we did a get_page in the beginning */
	return ret;
}

/**
 * read_opcode - read the opcode at a given virtual address.
 * @tsk: the probed task.
 * @vaddr: the virtual address to read the opcode.
 * @opcode: location to store the read opcode.
 *
 * Called with tsk->mm->mmap_sem held (for read and with a reference to
 * tsk->mm.
 *
 * For task @tsk, read the opcode at @vaddr and store it in @opcode.
 * Return 0 (success) or a negative errno.
 */
int __weak read_opcode(struct task_struct *tsk, unsigned long vaddr,
						uprobe_opcode_t *opcode)
{
	struct vm_area_struct *vma;
	struct page *page;
	void *vaddr_new;
	int ret;

	ret = get_user_pages(tsk, tsk->mm, vaddr, 1, 0, 0, &page, &vma);
	if (ret <= 0)
		return ret;
	ret = -EINVAL;

	/*
	 * We are interested in text pages only. Our pages of interest
	 * should be mapped for read and execute only. We desist from
	 * adding probes in write mapped pages since the breakpoints
	 * might end up in the file copy.
	 */
	if (!valid_vma(vma))
		goto put_out;

	lock_page(page);
	vaddr_new = kmap_atomic(page);
	vaddr &= ~PAGE_MASK;
	memcpy(opcode, vaddr_new + vaddr, uprobe_opcode_sz);
	kunmap_atomic(vaddr_new);
	unlock_page(page);
	ret =  0;

put_out:
	put_page(page); /* we did a get_user_pages in the beginning */
	return ret;
}

/**
 * set_bkpt - store breakpoint at a given address.
 * @tsk: the probed task.
 * @uprobe: the probepoint information.
 * @vaddr: the virtual address to insert the opcode.
 *
 * For task @tsk, store the breakpoint instruction at @vaddr.
 * Return 0 (success) or a negative errno.
 */
int __weak set_bkpt(struct task_struct *tsk, struct uprobe *uprobe,
						unsigned long vaddr)
{
	return write_opcode(tsk, uprobe, vaddr, UPROBES_BKPT_INSN);
}

/**
 * set_orig_insn - Restore the original instruction.
 * @tsk: the probed task.
 * @uprobe: the probepoint information.
 * @vaddr: the virtual address to insert the opcode.
 * @verify: if true, verify existance of breakpoint instruction.
 *
 * For task @tsk, restore the original opcode (opcode) at @vaddr.
 * Return 0 (success) or a negative errno.
 */
int __weak set_orig_insn(struct task_struct *tsk, struct uprobe *uprobe,
				unsigned long vaddr, bool verify)
{
	if (verify) {
		uprobe_opcode_t opcode;
		int result = read_opcode(tsk, vaddr, &opcode);
		if (result)
			return result;
		if (opcode != UPROBES_BKPT_INSN)
			return -EINVAL;
	}
	return write_opcode(tsk, uprobe, vaddr,
			*(uprobe_opcode_t *) uprobe->insn);
}

/**
 * is_bkpt_insn - check if instruction is breakpoint instruction.
 * @insn: instruction to be checked.
 * Default implementation of is_bkpt_insn
 * Returns true if @insn is a breakpoint instruction.
 */
bool __weak is_bkpt_insn(u8 *insn)
{
	uprobe_opcode_t opcode;

	memcpy(&opcode, insn, UPROBES_BKPT_INSN_SIZE);
	return (opcode == UPROBES_BKPT_INSN);
}

static int match_uprobe(struct uprobe *l, struct uprobe *r, int *match_inode)
{
	/*
	 * if match_inode is non NULL then indicate if the
	 * inode atleast match.
	 */
	if (match_inode)
		*match_inode = 0;

	if (l->inode < r->inode)
		return -1;
	if (l->inode > r->inode)
		return 1;
	else {
		if (match_inode)
			*match_inode = 1;

		if (l->offset < r->offset)
			return -1;

		if (l->offset > r->offset)
			return 1;
	}

	return 0;
}

static struct uprobe *__find_uprobe(struct inode * inode, loff_t offset,
					struct rb_node **close_match)
{
	struct uprobe u = { .inode = inode, .offset = offset };
	struct rb_node *n = uprobes_tree.rb_node;
	struct uprobe *uprobe;
	int match, match_inode;

	while (n) {
		uprobe = rb_entry(n, struct uprobe, rb_node);
		match = match_uprobe(&u, uprobe, &match_inode);
		if (close_match && match_inode)
			*close_match = n;

		if (!match) {
			atomic_inc(&uprobe->ref);
			return uprobe;
		}
		if (match < 0)
			n = n->rb_left;
		else
			n = n->rb_right;

	}
	return NULL;
}

/*
 * Find a uprobe corresponding to a given inode:offset
 * Acquires uprobes_treelock
 */
static struct uprobe *find_uprobe(struct inode * inode, loff_t offset)
{
	struct uprobe *uprobe;
	unsigned long flags;

	spin_lock_irqsave(&uprobes_treelock, flags);
	uprobe = __find_uprobe(inode, offset, NULL);
	spin_unlock_irqrestore(&uprobes_treelock, flags);
	return uprobe;
}

static struct uprobe *__insert_uprobe(struct uprobe *uprobe)
{
	struct rb_node **p = &uprobes_tree.rb_node;
	struct rb_node *parent = NULL;
	struct uprobe *u;
	int match;

	while (*p) {
		parent = *p;
		u = rb_entry(parent, struct uprobe, rb_node);
		match = match_uprobe(uprobe, u, NULL);
		if (!match) {
			atomic_inc(&u->ref);
			return u;
		}

		if (match < 0)
			p = &parent->rb_left;
		else
			p = &parent->rb_right;

	}
	u = NULL;
	rb_link_node(&uprobe->rb_node, parent, p);
	rb_insert_color(&uprobe->rb_node, &uprobes_tree);
	/* get access + drop ref */
	atomic_set(&uprobe->ref, 2);
	return u;
}

/*
 * Acquires uprobes_treelock.
 * Matching uprobe already exists in rbtree;
 *	increment (access refcount) and return the matching uprobe.
 *
 * No matching uprobe; insert the uprobe in rb_tree;
 *	get a double refcount (access + creation) and return NULL.
 */
static struct uprobe *insert_uprobe(struct uprobe *uprobe)
{
	unsigned long flags;
	struct uprobe *u;

	spin_lock_irqsave(&uprobes_treelock, flags);
	u = __insert_uprobe(uprobe);
	spin_unlock_irqrestore(&uprobes_treelock, flags);
	return u;
}

static void put_uprobe(struct uprobe *uprobe)
{
	if (atomic_dec_and_test(&uprobe->ref))
		kfree(uprobe);
}

static struct uprobe *alloc_uprobe(struct inode *inode, loff_t offset)
{
	struct uprobe *uprobe, *cur_uprobe;

	uprobe = kzalloc(sizeof(struct uprobe), GFP_KERNEL);
	if (!uprobe)
		return NULL;

	uprobe->inode = igrab(inode);
	uprobe->offset = offset;
	init_rwsem(&uprobe->consumer_rwsem);
	INIT_LIST_HEAD(&uprobe->pending_list);

	/* add to uprobes_tree, sorted on inode:offset */
	cur_uprobe = insert_uprobe(uprobe);

	/* a uprobe exists for this inode:offset combination*/
	if (cur_uprobe) {
		kfree(uprobe);
		uprobe = cur_uprobe;
		iput(inode);
	}
	return uprobe;
}

static void handler_chain(struct uprobe *uprobe, struct pt_regs *regs)
{
	struct uprobe_consumer *consumer;

	down_read(&uprobe->consumer_rwsem);
	consumer = uprobe->consumers;
	for (consumer = uprobe->consumers; consumer;
			consumer = consumer->next) {
		if (!consumer->filter ||
				consumer->filter(consumer, current))
			consumer->handler(consumer, regs);
	}
	up_read(&uprobe->consumer_rwsem);
}

/* Returns the previous consumer */
static struct uprobe_consumer *add_consumer(struct uprobe *uprobe,
				struct uprobe_consumer *consumer)
{
	down_write(&uprobe->consumer_rwsem);
	consumer->next = uprobe->consumers;
	uprobe->consumers = consumer;
	up_write(&uprobe->consumer_rwsem);
	return consumer->next;
}

/*
 * For uprobe @uprobe, delete the consumer @consumer.
 * Return true if the @consumer is deleted successfully
 * or return false.
 */
static bool del_consumer(struct uprobe *uprobe,
				struct uprobe_consumer *consumer)
{
	struct uprobe_consumer *con;
	bool ret = false;

	down_write(&uprobe->consumer_rwsem);
	con = uprobe->consumers;
	if (consumer == con) {
		uprobe->consumers = con->next;
		ret = true;
	} else {
		for (; con; con = con->next) {
			if (con->next == consumer) {
				con->next = consumer->next;
				ret = true;
				break;
			}
		}
	}
	up_write(&uprobe->consumer_rwsem);
	return ret;
}

static int __copy_insn(struct address_space *mapping,
			struct vm_area_struct *vma, char *insn,
			unsigned long nbytes, unsigned long offset)
{
	struct file *filp = vma->vm_file;
	struct page *page;
	void *vaddr;
	unsigned long off1;
	unsigned long idx;

	if (!filp)
		return -EINVAL;

	idx = (unsigned long) (offset >> PAGE_CACHE_SHIFT);
	off1 = offset &= ~PAGE_MASK;

	/*
	 * Ensure that the page that has the original instruction is
	 * populated and in page-cache.
	 */
	page_cache_sync_readahead(mapping, &filp->f_ra, filp, idx, 1);
	page = grab_cache_page(mapping, idx);
	if (!page)
		return -ENOMEM;

	vaddr = kmap_atomic(page);
	memcpy(insn, vaddr + off1, nbytes);
	kunmap_atomic(vaddr);
	unlock_page(page);
	page_cache_release(page);
	return 0;
}

static int copy_insn(struct uprobe *uprobe, struct vm_area_struct *vma,
					unsigned long addr)
{
	struct address_space *mapping;
	int bytes;
	unsigned long nbytes;

	addr &= ~PAGE_MASK;
	nbytes = PAGE_SIZE - addr;
	mapping = uprobe->inode->i_mapping;

	/* Instruction at end of binary; copy only available bytes */
	if (uprobe->offset + MAX_UINSN_BYTES > uprobe->inode->i_size)
		bytes = uprobe->inode->i_size - uprobe->offset;
	else
		bytes = MAX_UINSN_BYTES;

	/* Instruction at the page-boundary; copy bytes in second page */
	if (nbytes < bytes) {
		if (__copy_insn(mapping, vma, uprobe->insn + nbytes,
				bytes - nbytes, uprobe->offset + nbytes))
			return -ENOMEM;
		bytes = nbytes;
	}
	return __copy_insn(mapping, vma, uprobe->insn, bytes, uprobe->offset);
}

static struct task_struct *get_mm_owner(struct mm_struct *mm)
{
	struct task_struct *tsk;

	rcu_read_lock();
	tsk = rcu_dereference(mm->owner);
	if (tsk)
		get_task_struct(tsk);
	rcu_read_unlock();
	return tsk;
}

static int install_breakpoint(struct mm_struct *mm, struct uprobe *uprobe,
				struct vm_area_struct *vma, loff_t vaddr)
{
	struct task_struct *tsk;
	unsigned long addr;
	int ret = -EINVAL;

	if (!uprobe->consumers)
		return 0;

	tsk = get_mm_owner(mm);
	if (!tsk)	/* task is probably exiting; bail-out */
		return -ESRCH;

	if (vaddr > TASK_SIZE_OF(tsk))
		goto put_return;

	addr = (unsigned long) vaddr;
	if (!uprobe->copy) {
		ret = copy_insn(uprobe, vma, addr);
		if (ret)
			goto put_return;
		if (is_bkpt_insn(uprobe->insn)) {
			ret = -EEXIST;
			goto put_return;
		}
		ret = analyze_insn(tsk, uprobe);
		if (ret)
			goto put_return;
		uprobe->copy = 1;
	}

	ret = set_bkpt(tsk, uprobe, addr);
	if (!ret)
		atomic_inc(&mm->mm_uprobes_count);

put_return:
	put_task_struct(tsk);
	return ret;
}

static void remove_breakpoint(struct mm_struct *mm, struct uprobe *uprobe,
							loff_t vaddr)
{
	struct task_struct *tsk = get_mm_owner(mm);

	if (!tsk)	/* task is probably exiting; bail-out */
		return;

	if (!set_orig_insn(tsk, uprobe, (unsigned long) vaddr, true))
		atomic_dec(&mm->mm_uprobes_count);

	put_task_struct(tsk);
}

/*
 * There could be threads that have hit the breakpoint and are entering the
 * notifier code and trying to acquire the uprobes_treelock. The thread
 * calling delete_uprobe() that is removing the uprobe from the rb_tree can
 * race with these threads and might acquire the uprobes_treelock compared
 * to some of the breakpoint hit threads. In such a case, the breakpoint hit
 * threads will not find the uprobe. Finding if a "trap" instruction was
 * present at the interrupting address is racy. Hence provide some extra
 * time (by way of synchronize_sched() for breakpoint hit threads to acquire
 * the uprobes_treelock before the uprobe is removed from the rbtree.
 */
static void delete_uprobe(struct uprobe *uprobe)
{
	unsigned long flags;

	synchronize_sched();
	spin_lock_irqsave(&uprobes_treelock, flags);
	rb_erase(&uprobe->rb_node, &uprobes_tree);
	spin_unlock_irqrestore(&uprobes_treelock, flags);
	put_uprobe(uprobe);
	iput(uprobe->inode);
}

static struct vma_info *__find_next_vma_info(struct list_head *head,
			loff_t offset, struct address_space *mapping,
			struct vma_info *vi)
{
	struct prio_tree_iter iter;
	struct vm_area_struct *vma;
	struct vma_info *tmpvi;
	loff_t vaddr;
	unsigned long pgoff = offset >> PAGE_SHIFT;
	int existing_vma;

	vma_prio_tree_foreach(vma, &iter, &mapping->i_mmap, pgoff, pgoff) {
		if (!vma || !valid_vma(vma))
			return NULL;

		existing_vma = 0;
		vaddr = vma->vm_start + offset;
		vaddr -= vma->vm_pgoff << PAGE_SHIFT;
		list_for_each_entry(tmpvi, head, probe_list) {
			if (tmpvi->mm == vma->vm_mm && tmpvi->vaddr == vaddr) {
				existing_vma = 1;
				break;
			}
		}
		if (!existing_vma &&
				atomic_inc_not_zero(&vma->vm_mm->mm_users)) {
			vi->mm = vma->vm_mm;
			vi->vaddr = vaddr;
			list_add(&vi->probe_list, head);
			return vi;
		}
	}
	return NULL;
}

/*
 * Iterate in the rmap prio tree  and find a vma where a probe has not
 * yet been inserted.
 */
static struct vma_info *find_next_vma_info(struct list_head *head,
			loff_t offset, struct address_space *mapping)
{
	struct vma_info *vi, *retvi;
	vi = kzalloc(sizeof(struct vma_info), GFP_KERNEL);
	if (!vi)
		return ERR_PTR(-ENOMEM);

	INIT_LIST_HEAD(&vi->probe_list);
	mutex_lock(&mapping->i_mmap_mutex);
	retvi = __find_next_vma_info(head, offset, mapping, vi);
	mutex_unlock(&mapping->i_mmap_mutex);

	if (!retvi)
		kfree(vi);
	return retvi;
}

static int __register_uprobe(struct inode *inode, loff_t offset,
				struct uprobe *uprobe)
{
	struct list_head try_list;
	struct vm_area_struct *vma;
	struct address_space *mapping;
	struct vma_info *vi, *tmpvi;
	struct mm_struct *mm;
	int ret = 0;

	mapping = inode->i_mapping;
	INIT_LIST_HEAD(&try_list);
	while ((vi = find_next_vma_info(&try_list, offset,
							mapping)) != NULL) {
		if (IS_ERR(vi)) {
			ret = -ENOMEM;
			break;
		}
		mm = vi->mm;
		down_read(&mm->mmap_sem);
		vma = find_vma(mm, (unsigned long) vi->vaddr);
		if (!vma || !valid_vma(vma)) {
			list_del(&vi->probe_list);
			kfree(vi);
			up_read(&mm->mmap_sem);
			mmput(mm);
			continue;
		}
		ret = install_breakpoint(mm, uprobe, vma, vi->vaddr);
		if (ret && (ret != -ESRCH || ret != -EEXIST)) {
			up_read(&mm->mmap_sem);
			mmput(mm);
			break;
		}
		ret = 0;
		up_read(&mm->mmap_sem);
		mmput(mm);
	}
	list_for_each_entry_safe(vi, tmpvi, &try_list, probe_list) {
		list_del(&vi->probe_list);
		kfree(vi);
	}
	return ret;
}

static void __unregister_uprobe(struct inode *inode, loff_t offset,
						struct uprobe *uprobe)
{
	struct list_head try_list;
	struct address_space *mapping;
	struct vma_info *vi, *tmpvi;
	struct vm_area_struct *vma;
	struct mm_struct *mm;

	mapping = inode->i_mapping;
	INIT_LIST_HEAD(&try_list);
	while ((vi = find_next_vma_info(&try_list, offset,
							mapping)) != NULL) {
		if (IS_ERR(vi))
			break;
		mm = vi->mm;
		down_read(&mm->mmap_sem);
		vma = find_vma(mm, (unsigned long) vi->vaddr);
		if (!vma || !valid_vma(vma)) {
			list_del(&vi->probe_list);
			kfree(vi);
			up_read(&mm->mmap_sem);
			mmput(mm);
			continue;
		}
		remove_breakpoint(mm, uprobe, vi->vaddr);
		up_read(&mm->mmap_sem);
		mmput(mm);
	}

	list_for_each_entry_safe(vi, tmpvi, &try_list, probe_list) {
		list_del(&vi->probe_list);
		kfree(vi);
	}
	delete_uprobe(uprobe);
}

/*
 * register_uprobe - register a probe
 * @inode: the file in which the probe has to be placed.
 * @offset: offset from the start of the file.
 * @consumer: information on howto handle the probe..
 *
 * Apart from the access refcount, register_uprobe() takes a creation
 * refcount (thro alloc_uprobe) if and only if this @uprobe is getting
 * inserted into the rbtree (i.e first consumer for a @inode:@offset
 * tuple).  Creation refcount stops unregister_uprobe from freeing the
 * @uprobe even before the register operation is complete. Creation
 * refcount is released when the last @consumer for the @uprobe
 * unregisters.
 *
 * Return errno if it cannot successully install probes
 * else return 0 (success)
 */
int register_uprobe(struct inode *inode, loff_t offset,
				struct uprobe_consumer *consumer)
{
	struct uprobe *uprobe;
	int ret = 0;

	inode = igrab(inode);
	if (!inode || !consumer || consumer->next)
		return -EINVAL;

	if (offset > inode->i_size)
		return -EINVAL;

	mutex_lock(&inode->i_mutex);
	uprobe = alloc_uprobe(inode, offset);
	if (!uprobe)
		return -ENOMEM;

	if (!add_consumer(uprobe, consumer)) {
		ret = __register_uprobe(inode, offset, uprobe);
		if (ret)
			__unregister_uprobe(inode, offset, uprobe);
	}

	mutex_unlock(&inode->i_mutex);
	put_uprobe(uprobe);
	iput(inode);
	return ret;
}

/*
 * unregister_uprobe - unregister a already registered probe.
 * @inode: the file in which the probe has to be removed.
 * @offset: offset from the start of the file.
 * @consumer: identify which probe if multiple probes are colocated.
 */
void unregister_uprobe(struct inode *inode, loff_t offset,
				struct uprobe_consumer *consumer)
{
	struct uprobe *uprobe;

	inode = igrab(inode);
	if (!inode || !consumer)
		return;

	if (offset > inode->i_size)
		return;

	uprobe = find_uprobe(inode, offset);
	if (!uprobe)
		return;

	if (!del_consumer(uprobe, consumer)) {
		put_uprobe(uprobe);
		return;
	}

	mutex_lock(&inode->i_mutex);
	if (!uprobe->consumers)
		__unregister_uprobe(inode, offset, uprobe);

	mutex_unlock(&inode->i_mutex);
	put_uprobe(uprobe);
	iput(inode);
}

/*
 * For a given inode, build a list of probes that need to be inserted.
 */
static void build_probe_list(struct inode *inode, struct list_head *head)
{
	struct uprobe *uprobe;
	struct rb_node *n;
	unsigned long flags;

	n = uprobes_tree.rb_node;
	spin_lock_irqsave(&uprobes_treelock, flags);
	uprobe = __find_uprobe(inode, 0, &n);
	/*
	 * If indeed there is a probe for the inode and with offset zero,
	 * then lets release its reference. (ref got thro __find_uprobe)
	 */
	if (uprobe)
		put_uprobe(uprobe);
	for (; n; n = rb_next(n)) {
		uprobe = rb_entry(n, struct uprobe, rb_node);
		if (uprobe->inode != inode)
			break;
		list_add(&uprobe->pending_list, head);
		atomic_inc(&uprobe->ref);
	}
	spin_unlock_irqrestore(&uprobes_treelock, flags);
}

/*
 * Called from mmap_region.
 * called with mm->mmap_sem acquired.
 *
 * Return -ve no if we fail to insert probes and we cannot
 * bail-out.
 * Return 0 otherwise. i.e :
 *	- successful insertion of probes
 *	- (or) no possible probes to be inserted.
 *	- (or) insertion of probes failed but we can bail-out.
 */
int mmap_uprobe(struct vm_area_struct *vma)
{
	struct list_head tmp_list;
	struct uprobe *uprobe, *u;
	struct inode *inode;
	int ret = 0;

	if (!valid_vma(vma))
		return ret;	/* Bail-out */

	inode = igrab(vma->vm_file->f_mapping->host);
	if (!inode)
		return ret;

	INIT_LIST_HEAD(&tmp_list);
	mutex_lock(&uprobes_mmap_mutex);
	build_probe_list(inode, &tmp_list);
	list_for_each_entry_safe(uprobe, u, &tmp_list, pending_list) {
		loff_t vaddr;

		list_del(&uprobe->pending_list);
		if (!ret && uprobe->consumers) {
			vaddr = vma->vm_start + uprobe->offset;
			vaddr -= vma->vm_pgoff << PAGE_SHIFT;
			if (vaddr < vma->vm_start || vaddr >= vma->vm_end)
				continue;
			ret = install_breakpoint(vma->vm_mm, uprobe, vma,
								vaddr);
			if (ret && (ret == -ESRCH || ret == -EEXIST))
				ret = 0;
		}
		put_uprobe(uprobe);
	}

	mutex_unlock(&uprobes_mmap_mutex);
	iput(inode);
	return ret;
}

static void dec_mm_uprobes_count(struct vm_area_struct *vma,
		struct inode *inode)
{
	struct uprobe *uprobe;
	struct rb_node *n;
	unsigned long flags;

	n = uprobes_tree.rb_node;
	spin_lock_irqsave(&uprobes_treelock, flags);
	uprobe = __find_uprobe(inode, 0, &n);

	/*
	 * If indeed there is a probe for the inode and with offset zero,
	 * then lets release its reference. (ref got thro __find_uprobe)
	 */
	if (uprobe)
		put_uprobe(uprobe);
	for (; n; n = rb_next(n)) {
		loff_t vaddr;

		uprobe = rb_entry(n, struct uprobe, rb_node);
		if (uprobe->inode != inode)
			break;
		vaddr = vma->vm_start + uprobe->offset;
		vaddr -= vma->vm_pgoff << PAGE_SHIFT;
		if (vaddr < vma->vm_start || vaddr >= vma->vm_end)
			continue;
		atomic_dec(&vma->vm_mm->mm_uprobes_count);
	}
	spin_unlock_irqrestore(&uprobes_treelock, flags);
}

/*
 * Called in context of a munmap of a vma.
 */
void munmap_uprobe(struct vm_area_struct *vma)
{
	struct inode *inode;

	if (!valid_vma(vma))
		return;		/* Bail-out */

	if (!atomic_read(&vma->vm_mm->mm_uprobes_count))
		return;

	inode = igrab(vma->vm_file->f_mapping->host);
	if (!inode)
		return;

	dec_mm_uprobes_count(vma, inode);
	iput(inode);
	return;
}

/* Slot allocation for XOL */
static int xol_add_vma(struct uprobes_xol_area *area)
{
	const struct cred *curr_cred;
	struct vm_area_struct *vma;
	struct mm_struct *mm;
	unsigned long addr;
	int ret = -ENOMEM;

	mm = get_task_mm(current);
	if (!mm)
		return -ESRCH;

	down_write(&mm->mmap_sem);
	if (mm->uprobes_xol_area) {
		ret = -EALREADY;
		goto fail;
	}

	/*
	 * Find the end of the top mapping and skip a page.
	 * If there is no space for PAGE_SIZE above
	 * that, mmap will ignore our address hint.
	 *
	 * override credentials otherwise anonymous memory might
	 * not be granted execute permission when the selinux
	 * security hooks have their way.
	 */
	vma = rb_entry(rb_last(&mm->mm_rb), struct vm_area_struct, vm_rb);
	addr = vma->vm_end + PAGE_SIZE;
	curr_cred = override_creds(&init_cred);
	addr = do_mmap_pgoff(NULL, addr, PAGE_SIZE, PROT_EXEC, MAP_PRIVATE, 0);
	revert_creds(curr_cred);

	if (addr & ~PAGE_MASK)
		goto fail;
	vma = find_vma(mm, addr);

	/* Don't expand vma on mremap(). */
	vma->vm_flags |= VM_DONTEXPAND | VM_DONTCOPY;
	area->vaddr = vma->vm_start;
	if (get_user_pages(current, mm, area->vaddr, 1, 1, 1, &area->page,
				&vma) > 0)
		ret = 0;

fail:
	up_write(&mm->mmap_sem);
	mmput(mm);
	return ret;
}

/*
 * xol_alloc_area - Allocate process's uprobes_xol_area.
 * This area will be used for storing instructions for execution out of
 * line.
 *
 * Returns the allocated area or NULL.
 */
static struct uprobes_xol_area *xol_alloc_area(void)
{
	struct uprobes_xol_area *area = NULL;

	area = kzalloc(sizeof(*area), GFP_KERNEL);
	if (unlikely(!area))
		return NULL;

	area->bitmap = kzalloc(BITS_TO_LONGS(UINSNS_PER_PAGE) * sizeof(long),
								GFP_KERNEL);

	if (!area->bitmap)
		goto fail;

	init_waitqueue_head(&area->wq);
	spin_lock_init(&area->slot_lock);
	if (!xol_add_vma(area) && !current->mm->uprobes_xol_area) {
		task_lock(current);
		if (!current->mm->uprobes_xol_area) {
			current->mm->uprobes_xol_area = area;
			task_unlock(current);
			return area;
		}
		task_unlock(current);
	}

fail:
	kfree(area->bitmap);
	kfree(area);
	return current->mm->uprobes_xol_area;
}

/*
 * free_uprobes_xol_area - Free the area allocated for slots.
 */
void free_uprobes_xol_area(struct mm_struct *mm)
{
	struct uprobes_xol_area *area = mm->uprobes_xol_area;

	if (!area)
		return;

	put_page(area->page);
	kfree(area->bitmap);
	kfree(area);
}

static void xol_wait_event(struct uprobes_xol_area *area)
{
	if (atomic_read(&area->slot_count) >= UINSNS_PER_PAGE)
		wait_event(area->wq,
			(atomic_read(&area->slot_count) < UINSNS_PER_PAGE));
}

/*
 *  - search for a free slot.
 */
static unsigned long xol_take_insn_slot(struct uprobes_xol_area *area)
{
	unsigned long slot_addr, flags;
	int slot_nr;

	do {
		spin_lock_irqsave(&area->slot_lock, flags);
		slot_nr = find_first_zero_bit(area->bitmap, UINSNS_PER_PAGE);
		if (slot_nr < UINSNS_PER_PAGE) {
			__set_bit(slot_nr, area->bitmap);
			slot_addr = area->vaddr +
					(slot_nr * UPROBES_XOL_SLOT_BYTES);
			atomic_inc(&area->slot_count);
		}
		spin_unlock_irqrestore(&area->slot_lock, flags);
		if (slot_nr >= UINSNS_PER_PAGE)
			xol_wait_event(area);

	} while (slot_nr >= UINSNS_PER_PAGE);

	return slot_addr;
}

/*
 * xol_get_insn_slot - If was not allocated a slot, then
 * allocate a slot.
 * Returns the allocated slot address or 0.
 */
static unsigned long xol_get_insn_slot(struct uprobe *uprobe,
					unsigned long slot_addr)
{
	struct uprobes_xol_area *area = current->mm->uprobes_xol_area;
	unsigned long offset;
	void *vaddr;

	if (!area) {
		area = xol_alloc_area();
		if (!area)
			return 0;
	}
	current->utask->xol_vaddr = xol_take_insn_slot(area);

	/*
	 * Initialize the slot if xol_vaddr points to valid
	 * instruction slot.
	 */
	if (unlikely(!current->utask->xol_vaddr))
		return 0;

	current->utask->vaddr = slot_addr;
	offset = current->utask->xol_vaddr & ~PAGE_MASK;
	vaddr = kmap_atomic(area->page);
	memcpy(vaddr + offset, uprobe->insn, MAX_UINSN_BYTES);
	kunmap_atomic(vaddr);
	return current->utask->xol_vaddr;
}

/*
 * xol_free_insn_slot - If slot was earlier allocated by
 * @xol_get_insn_slot(), make the slot available for
 * subsequent requests.
 */
static void xol_free_insn_slot(struct task_struct *tsk)
{
	struct uprobes_xol_area *area;
	unsigned long vma_end;
	unsigned long slot_addr;

	if (!tsk->mm || !tsk->mm->uprobes_xol_area || !tsk->utask)
		return;

	slot_addr = tsk->utask->xol_vaddr;

	if (unlikely(!slot_addr || IS_ERR_VALUE(slot_addr)))
		return;

	area = tsk->mm->uprobes_xol_area;
	vma_end = area->vaddr + PAGE_SIZE;
	if (area->vaddr <= slot_addr && slot_addr < vma_end) {
		int slot_nr;
		unsigned long offset = slot_addr - area->vaddr;
		unsigned long flags;

		slot_nr = offset / UPROBES_XOL_SLOT_BYTES;
		if (slot_nr >= UINSNS_PER_PAGE)
			return;

		spin_lock_irqsave(&area->slot_lock, flags);
		__clear_bit(slot_nr, area->bitmap);
		spin_unlock_irqrestore(&area->slot_lock, flags);
		atomic_dec(&area->slot_count);
		if (waitqueue_active(&area->wq))
			wake_up(&area->wq);
		tsk->utask->xol_vaddr = 0;
	}
}

/**
 * get_uprobe_bkpt_addr - compute address of bkpt given post-bkpt regs
 * @regs: Reflects the saved state of the task after it has hit a breakpoint
 * instruction.
 * Return the address of the breakpoint instruction.
 */
unsigned long __weak get_uprobe_bkpt_addr(struct pt_regs *regs)
{
	return instruction_pointer(regs) - UPROBES_BKPT_INSN_SIZE;
}

/*
 * Called with no locks held.
 * Called in context of a exiting or a exec-ing thread.
 */
void free_uprobe_utask(struct task_struct *tsk)
{
	struct uprobe_task *utask = tsk->utask;

	if (!utask)
		return;

	if (utask->active_uprobe)
		put_uprobe(utask->active_uprobe);

	xol_free_insn_slot(tsk);
	kfree(utask);
	tsk->utask = NULL;
}

/*
 * Allocate a uprobe_task object for the task.
 * Called when the thread hits a breakpoint for the first time.
 *
 * Returns:
 * - pointer to new uprobe_task on success
 * - negative errno otherwise
 */
static struct uprobe_task *add_utask(void)
{
	struct uprobe_task *utask;
	struct sigpending *delayed;

	utask = kzalloc(sizeof *utask, GFP_KERNEL);
	if (unlikely(utask == NULL))
		return ERR_PTR(-ENOMEM);

	delayed = &utask->delayed;
	INIT_LIST_HEAD(&delayed->list);
	utask->active_uprobe = NULL;
	current->utask = utask;
	return utask;
}

/* Prepare to single-step probed instruction out of line. */
static int pre_ssout(struct uprobe *uprobe, struct pt_regs *regs,
				unsigned long vaddr)
{
	if (xol_get_insn_slot(uprobe, vaddr) && !pre_xol(uprobe, regs)) {
		set_instruction_pointer(regs, current->utask->xol_vaddr);
		return 0;
	}
	return -EFAULT;
}

/*
 * Verify from Instruction Pointer if singlestep has indeed occurred.
 * If Singlestep has occurred, then do post singlestep fix-ups.
 */
static bool sstep_complete(struct uprobe *uprobe, struct pt_regs *regs)
{
	unsigned long vaddr = instruction_pointer(regs);

	/*
	 * If we have executed out of line, Instruction pointer
	 * cannot be same as virtual address of XOL slot.
	 */
	if (vaddr == current->utask->xol_vaddr)
		return false;
	post_xol(uprobe, regs);
	return true;
}

static void pushback_signals(struct sigpending *pending)
{
	struct sigqueue *q, *tmpq;

	list_for_each_entry_safe(q, tmpq, &pending->list, list) {
		list_del(&q->list);
		send_sigqueue(q, current, 0);
	}
}

/*
 * uprobe_notify_resume gets called in task context just before returning
 * to userspace.
 *
 *  If its the first time the probepoint is hit, slot gets allocated here.
 *  If its the first time the thread hit a breakpoint, utask gets
 *  allocated here.
 */
void uprobe_notify_resume(struct pt_regs *regs)
{
	struct vm_area_struct *vma;
	struct uprobe_task *utask;
	struct mm_struct *mm;
	struct uprobe *u = NULL;
	unsigned long probept;

	utask = current->utask;
	mm = current->mm;
	if (!utask || utask->state == UTASK_BP_HIT) {
		probept = get_uprobe_bkpt_addr(regs);
		down_read(&mm->mmap_sem);
		vma = find_vma(mm, probept);
		if (vma && valid_vma(vma))
			u = find_uprobe(vma->vm_file->f_mapping->host,
					probept - vma->vm_start +
					(vma->vm_pgoff << PAGE_SHIFT));
		up_read(&mm->mmap_sem);
		if (!u)
			/* No matching uprobe; signal SIGTRAP. */
			goto cleanup_ret;
		if (!utask) {
			utask = add_utask();
			/* Cannot Allocate; re-execute the instruction. */
			if (!utask)
				goto cleanup_ret;
		}
		utask->active_uprobe = u;
		handler_chain(u, regs);
		utask->state = UTASK_SSTEP;
		if (!pre_ssout(u, regs, probept))
			user_enable_single_step(current);
		else
			/* Cannot Singlestep; re-execute the instruction. */
			goto cleanup_ret;
	} else if (utask->state == UTASK_SSTEP) {
		u = utask->active_uprobe;
		if (sstep_complete(u, regs)) {
			put_uprobe(u);
			utask->active_uprobe = NULL;
			utask->state = UTASK_RUNNING;
			user_disable_single_step(current);
			xol_free_insn_slot(current);
			pushback_signals(&current->utask->delayed);
		}
	}
	return;

cleanup_ret:
	if (utask) {
		utask->active_uprobe = NULL;
		utask->state = UTASK_RUNNING;
	}
	if (u) {
		put_uprobe(u);
		set_instruction_pointer(regs, probept);
	} else
		send_sig(SIGTRAP, current, 0);
}

/*
 * uprobe_bkpt_notifier gets called from interrupt context
 * it gets a reference to the ppt and sets TIF_UPROBE flag,
 */
int uprobe_bkpt_notifier(struct pt_regs *regs)
{
	struct uprobe_task *utask;

	if (!current->mm || !atomic_read(&current->mm->mm_uprobes_count))
		/* task is currently not uprobed */
		return 0;

	utask = current->utask;
	if (utask)
		utask->state = UTASK_BP_HIT;
	set_thread_flag(TIF_UPROBE);
	return 1;
}

/*
 * uprobe_post_notifier gets called in interrupt context.
 * It completes the single step operation.
 */
int uprobe_post_notifier(struct pt_regs *regs)
{
	struct uprobe *uprobe;
	struct uprobe_task *utask;

	if (!current->mm || !current->utask || !current->utask->active_uprobe)
		/* task is currently not uprobed */
		return 0;

	utask = current->utask;
	uprobe = utask->active_uprobe;
	set_thread_flag(TIF_UPROBE);
	return 1;
}

struct notifier_block uprobe_exception_nb = {
	.notifier_call = uprobe_exception_notify,
	.priority = INT_MAX - 1,	/* notified after kprobes, kgdb */
};

static int __init init_uprobes(void)
{
	return register_die_notifier(&uprobe_exception_nb);
}

static void __exit exit_uprobes(void)
{
}

module_init(init_uprobes);
module_exit(exit_uprobes);
