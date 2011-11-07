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
#include <linux/uprobes.h>

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
 * valid_vma: Verify if the specified vma is an executable vma
 *	- Return 1 if the specified virtual address is in an
 *	  executable vma.
 */
static bool valid_vma(struct vm_area_struct *vma)
{
	if (!vma->vm_file)
		return false;

	if ((vma->vm_flags & (VM_READ|VM_WRITE|VM_EXEC|VM_SHARED)) ==
						(VM_READ|VM_EXEC))
		return true;

	return false;
}

int __weak set_bkpt(struct task_struct *tsk, struct uprobe *uprobe,
						unsigned long vaddr)
{
	/* placeholder: yet to be implemented */
	return 0;
}

int __weak set_orig_insn(struct task_struct *tsk, struct uprobe *uprobe,
					unsigned long vaddr, bool verify)
{
	/* placeholder: yet to be implemented */
	return 0;
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
		/* TODO : Analysis and verification of instruction */
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

static void delete_uprobe(struct uprobe *uprobe)
{
	unsigned long flags;

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
