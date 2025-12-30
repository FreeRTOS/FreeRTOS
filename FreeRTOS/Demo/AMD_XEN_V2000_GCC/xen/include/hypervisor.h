/******************************************************************************
 * hypervisor.h
 * 
 * Hypervisor handling.
 * 
 *
 * Copyright (c) 2002, K A Fraser
 * Copyright (c) 2005, Grzegorz Milos
 * Updates: Aravindh Puthiyaparambil <aravindh.puthiyaparambil@unisys.com>
 */

#ifndef _HYPERVISOR_H_
#define _HYPERVISOR_H_

#include <types.h>
#include <xen/xen.h>
#if defined(__i386__)
#include <hypercall-x86_32.h>
#elif defined(__x86_64__)
#include <hypercall-x86_64.h>
#elif defined(__arm__) || defined(__aarch64__)
#include <hypercall-arm.h>
#else
#error "Unsupported architecture"
#endif
#include <xen/hvm/hvm_op.h>

/* hypervisor.c */
#ifdef CONFIG_PARAVIRT
/*
 * a placeholder for the start of day information passed up from the hypervisor
 */
union start_info_union
{
    start_info_t start_info;
    char padding[512];
};
extern union start_info_union start_info_union;
#define start_info (start_info_union.start_info)
#else
int hvm_get_parameter(int idx, uint64_t *value);
int hvm_set_parameter(int idx, uint64_t value);
#endif
shared_info_t *map_shared_info(void *p);
void unmap_shared_info(void);
void force_evtchn_callback(void);
void do_hypervisor_callback(void *regs);
void mask_evtchn(uint32_t port);
void unmask_evtchn(uint32_t port);
void clear_evtchn(uint32_t port);

#endif /* __HYPERVISOR_H__ */
