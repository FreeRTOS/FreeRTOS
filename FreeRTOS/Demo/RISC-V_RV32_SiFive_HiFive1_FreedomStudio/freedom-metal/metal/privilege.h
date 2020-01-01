/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__PRIVILEGE_H
#define METAL__PRIVILEGE_H

/*!
 * @file metal/privilege.h
 *
 * @brief API for manipulating the privilege mode of a RISC-V system
 *
 * Additional information about privilege modes on RISC-V systems can be found
 * by reading the RISC-V Privileged Architecture Specification v1.10.
 */

#include <stdint.h>

enum metal_privilege_mode {
	METAL_PRIVILEGE_USER = 0,
	METAL_PRIVILEGE_SUPERVISOR = 1,
	METAL_PRIVILEGE_MACHINE = 3,
};

#if __riscv_xlen == 32
typedef uint32_t metal_xreg_t;
#elif __riscv_xlen == 64
typedef uint64_t metal_xreg_t;
#endif

#if __riscv_flen == 32
typedef uint32_t metal_freg_t;
#elif __riscv_flen == 64
typedef uint64_t metal_freg_t;
#endif

struct metal_register_file {
	metal_xreg_t ra;
	metal_xreg_t sp;
	metal_xreg_t gp;
	metal_xreg_t tp;

	metal_xreg_t t0;
	metal_xreg_t t1;
	metal_xreg_t t2;

	metal_xreg_t s0;
	metal_xreg_t s1;

	metal_xreg_t a0;
	metal_xreg_t a1;
	metal_xreg_t a2;
	metal_xreg_t a3;
	metal_xreg_t a4;
	metal_xreg_t a5;
#ifndef __riscv_32e
	metal_xreg_t a6;
	metal_xreg_t a7;

	metal_xreg_t s2;
	metal_xreg_t s3;
	metal_xreg_t s4;
	metal_xreg_t s5;
	metal_xreg_t s6;
	metal_xreg_t s7;
	metal_xreg_t s8;
	metal_xreg_t s9;
	metal_xreg_t s10;
	metal_xreg_t s11;

	metal_xreg_t t3;
	metal_xreg_t t4;
	metal_xreg_t t5;
	metal_xreg_t t6;
#endif /* __riscv_32e */

#ifdef __riscv_flen
	metal_freg_t ft0;
	metal_freg_t ft1;
	metal_freg_t ft2;
	metal_freg_t ft3;
	metal_freg_t ft4;
	metal_freg_t ft5;
	metal_freg_t ft6;
	metal_freg_t ft7;

	metal_freg_t fs0;
	metal_freg_t fs1;

	metal_freg_t fa0;
	metal_freg_t fa1;
	metal_freg_t fa2;
	metal_freg_t fa3;
	metal_freg_t fa4;
	metal_freg_t fa5;
	metal_freg_t fa6;
	metal_freg_t fa7;

	metal_freg_t fs2;
	metal_freg_t fs3;
	metal_freg_t fs4;
	metal_freg_t fs5;
	metal_freg_t fs6;
	metal_freg_t fs7;
	metal_freg_t fs8;
	metal_freg_t fs9;
	metal_freg_t fs10;
	metal_freg_t fs11;

	metal_freg_t ft8;
	metal_freg_t ft9;
	metal_freg_t ft10;
	metal_freg_t ft11;
#endif /* __riscv_flen */
};

typedef void (*metal_privilege_entry_point_t)(void);

void metal_privilege_drop_to_mode(enum metal_privilege_mode mode,
				  struct metal_register_file regfile,
				  metal_privilege_entry_point_t entry_point);

#endif
