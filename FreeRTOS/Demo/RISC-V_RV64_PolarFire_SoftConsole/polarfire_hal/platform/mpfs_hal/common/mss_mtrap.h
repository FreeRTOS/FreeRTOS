/*
    Copyright (c) 2013, The Regents of the University of California (Regents).
    All Rights Reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:
    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.
    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in the
       documentation and/or other materials provided with the distribution.
    3. Neither the name of the Regents nor the
       names of its contributors may be used to endorse or promote products
       derived from this software without specific prior written permission.

    IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
    SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING
    OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS
    BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
    THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
    PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED
    HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE
    MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
*/

/***********************************************************************************
 * Record of Microchip changes
 */
#ifndef RISCV_MTRAP_H
#define RISCV_MTRAP_H

#ifdef __cplusplus
extern "C" {
#endif

#ifndef __ASSEMBLER__
#define read_const_csr(reg) ({ unsigned long __tmp; \
  asm ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })
#endif

#define IPI_SOFT          0x01
#define IPI_FENCE_I       0x02
#define IPI_SFENCE_VMA    0x04

#define MACHINE_STACK_SIZE  (RISCV_PGSIZE)    /* this is 4k for HLS and 4k for the stack*/
#define MENTRY_HLS_OFFSET   (INTEGER_CONTEXT_SIZE + SOFT_FLOAT_CONTEXT_SIZE)
#define MENTRY_FRAME_SIZE   (MENTRY_HLS_OFFSET + HLS_SIZE)
#define MENTRY_IPI_OFFSET   (MENTRY_HLS_OFFSET)
#define MENTRY_IPI_PENDING_OFFSET (MENTRY_HLS_OFFSET + REGBYTES)

#ifdef __riscv_flen
# define SOFT_FLOAT_CONTEXT_SIZE (0)
#else
# define SOFT_FLOAT_CONTEXT_SIZE (8 * 32)
#endif

#define HLS_SIZE          (64)
#define INTEGER_CONTEXT_SIZE (32 * REGBYTES)

#ifndef __ASSEMBLER__
typedef struct {
  volatile uint32_t *  ipi;
  volatile int         mipi_pending;
  volatile int         padding;
  volatile uint64_t *  timecmp;
  volatile uint32_t *  plic_m_thresh;
  volatile uintptr_t * plic_m_ie;
  volatile uint32_t *  plic_s_thresh;
  volatile uintptr_t * plic_s_ie;
} hls_t;

/* This code relies on the stack being allocated on a 4K boundary */
/* also can  not be bigger than 4k */
#define MACHINE_STACK_TOP() ({ \
  register uintptr_t sp asm ("sp"); \
  (void *)((sp + RISCV_PGSIZE) & -RISCV_PGSIZE); })

// hart-local storage
#define HLS() ((hls_t*)(MACHINE_STACK_TOP() - HLS_SIZE))
#define OTHER_HLS(id) ((hls_t*)((void *)HLS() + RISCV_PGSIZE * ((id) - read_const_csr(mhartid))))

#endif

#ifdef __cplusplus
}
#endif

#endif /*RISCV_MTRAP_H*/

