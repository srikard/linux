/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Copyright (C) 2020  IBM Corporation
 */

#ifndef __POWERPC_KVM_GUEST_H__
#define __POWERPC_KVM_GUEST_H__

#if defined(CONFIG_PPC_PSERIES) || defined(CONFIG_KVM_GUEST)
#include <linux/jump_label.h>

DECLARE_STATIC_KEY_FALSE(kvm_guest);

static inline bool is_kvm_guest(void)
{
	return static_branch_unlikely(&kvm_guest);
}

bool check_kvm_guest(void);
#else
static inline bool is_kvm_guest(void) { return false; }
static inline bool check_kvm_guest(void) { return false; }
#endif

#endif /* __POWERPC_KVM_GUEST_H__ */
