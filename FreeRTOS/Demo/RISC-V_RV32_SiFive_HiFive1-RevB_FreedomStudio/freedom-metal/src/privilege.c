/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <stddef.h>

#include <metal/privilege.h>

#define METAL_MSTATUS_MIE_OFFSET	3
#define METAL_MSTATUS_MPIE_OFFSET	7
#define METAL_MSTATUS_SIE_OFFSET	1
#define METAL_MSTATUS_SPIE_OFFSET	5
#define METAL_MSTATUS_UIE_OFFSET	0
#define METAL_MSTATUS_UPIE_OFFSET	4

#define METAL_MSTATUS_MPP_OFFSET	11
#define METAL_MSTATUS_MPP_MASK		3

void metal_privilege_drop_to_mode(enum metal_privilege_mode mode,
				  struct metal_register_file regfile,
				  metal_privilege_entry_point_t entry_point)
{
	uintptr_t mstatus;
	__asm__ volatile("csrr %0, mstatus" : "=r" (mstatus));

	/* Set xPIE bits based on current xIE bits */
	if(mstatus && (1 << METAL_MSTATUS_MIE_OFFSET)) {
		mstatus |= (1 << METAL_MSTATUS_MPIE_OFFSET);
	} else {
		mstatus &= ~(1 << METAL_MSTATUS_MPIE_OFFSET);
	}
	if(mstatus && (1 << METAL_MSTATUS_SIE_OFFSET)) {
		mstatus |= (1 << METAL_MSTATUS_SPIE_OFFSET);
	} else {
		mstatus &= ~(1 << METAL_MSTATUS_SPIE_OFFSET);
	}
	if(mstatus && (1 << METAL_MSTATUS_UIE_OFFSET)) {
		mstatus |= (1 << METAL_MSTATUS_UPIE_OFFSET);
	} else {
		mstatus &= ~(1 << METAL_MSTATUS_UPIE_OFFSET);
	}

	/* Set MPP to the requested privilege mode */
	mstatus &= ~(METAL_MSTATUS_MPP_MASK << METAL_MSTATUS_MPP_OFFSET);
	mstatus |= (mode << METAL_MSTATUS_MPP_OFFSET);

	__asm__ volatile("csrw mstatus, %0" :: "r" (mstatus));

	/* Set the entry point in MEPC */
	__asm__ volatile("csrw mepc, %0" :: "r" (entry_point));

	/* Set the register file */
	__asm__ volatile("mv ra, %0" :: "r" (regfile.ra));
	__asm__ volatile("mv sp, %0" :: "r" (regfile.sp));

	__asm__ volatile("mret");
}

