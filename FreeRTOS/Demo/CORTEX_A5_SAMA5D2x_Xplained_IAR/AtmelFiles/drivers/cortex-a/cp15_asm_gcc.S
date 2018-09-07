/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \file */

/*----------------------------------------------------------------------------
 *        Functions to access CP15 coprocessor register
 *----------------------------------------------------------------------------*/

	.section .text.cp15_read_id
	.global   cp15_read_id
cp15_read_id:
	mov     r0, #0
	mrc     p15, 0, r0, c0, c0, 0   // read MIDR
	bx      lr

	.section .text.cp15_isb
	.global   cp15_isb
cp15_isb:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c5, 4   // CP15ISB()
	nop
	bx      lr

	.section .text.cp15_dsb
	.global   cp15_dsb
cp15_dsb:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c10, 4  // CP15DSB()
	nop
	bx      lr

	.section .text.cp15_dmb
	.global   cp15_dmb
cp15_dmb:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c10, 5  // CP15DMB
	nop
	bx      lr

	.section .text.cp15_invalidate_tlb
	.global  cp15_invalidate_tlb
cp15_invalidate_tlb:
	mov     r0, #0
	mcr     p15, 0, r0, c8, c7, 0   // TLBIALL()
	dsb
	bx      lr

	.section .text.cp15_exclusive_cache
	.global   cp15_exclusive_cache
cp15_exclusive_cache:
	mov     r0, #0
	mrc     p15, 0, r0, c1, c0, 1   // Read ACTLR
	orr     r0, r0, #0x00000080     // Set EXCL
	mcr     p15, 0, r0, c1, c0, 1   // Write ACTLR
	nop
	bx      lr

	.section .text.cp15_non_exclusive_cache
	.global   cp15_non_exclusive_cache
cp15_non_exclusive_cache:
	mov     r0, #0
	mrc     p15, 0, r0, c1, c0, 1   // Read ACTLR
	bic     r0, r0, #0x00000080     // Clear EXCL
	mcr     p15, 0, r0, c1, c0, 1   // Write ACTLR
	nop
	bx      lr

	.section .text.cp15_select_icache
	.global   cp15_select_icache
cp15_select_icache:
	mrc     p15, 2, r0, c0, c0, 0   // Read CSSELR
	orr     r0,  r0, #0x1           // Set InD: cache type = ICache
	mcr     p15, 2, r0, c0, c0, 0   // Write CSSELR
	nop
	bx      lr

	.section .text.cp15_select_dcache
	.global   cp15_select_dcache
cp15_select_dcache:
	mrc     p15, 2, r0, c0, c0, 0   // Read CSSELR
	and     r0,  r0, #0xFFFFFFFE    // Clear InD: cache type = DCache
	mcr     p15, 2, r0, c0, c0, 0   // Write CSSELR
	nop
	bx      lr

	.section .text.cp15_read_control
	.global   cp15_read_control
cp15_read_control:
	mov     r0, #0
	mrc     p15, 0, r0, c1, c0, 0   // read SCTLR
	bx      lr

	.section .text.cp15_write_control
	.global   cp15_write_control
cp15_write_control:
	mcr     p15, 0, r0, c1, c0, 0   // rewrite SCTLR
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	bx      lr

	.section .text.cp15_write_domain_access_control
	.global   cp15_write_domain_access_control
cp15_write_domain_access_control:
	mcr     p15, 0, r0, c3, c0, 0   // rewrite DACR
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	bx      lr

	.section .text.cp15_write_ttb
	.global   cp15_write_ttb
cp15_write_ttb:
	mcr     p15, 0, r0, c2, c0, 0   // rewrite TTBR0
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	bx     lr

	.section .text.cp15_invalid_icache_inner_sharable
	.global   cp15_invalid_icache_inner_sharable
cp15_invalid_icache_inner_sharable:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c1, 0   // ICIALLUIS()
	bx      lr

	.section .text.cp15_invalid_btb_inner_sharable
	.global   cp15_invalid_btb_inner_sharable
cp15_invalid_btb_inner_sharable:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c1, 6   // BPIALLIS()
	bx      lr

	.section .text.cp15_invalid_icache
	.global   cp15_invalid_icache
cp15_invalid_icache:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c5, 0   // ICIALLU()
	bx      lr

	.section .text.cp15_invalid_icache_by_mva
	.global   cp15_invalid_icache_by_mva
cp15_invalid_icache_by_mva:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c5, 1   // ICIMVAU()
	bx      lr

	.section .text.cp15_invalid_btb
	.global   cp15_invalid_btb
cp15_invalid_btb:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c5, 6   // BPIALL()
	bx      lr

	.section .text.cp15_invalid_btb_by_mva
	.global   cp15_invalid_btb_by_mva
cp15_invalid_btb_by_mva:
	mcr     p15, 0, r0, c7, c5, 7   // BPIMVA()
	bx      lr

/***********************************************************
 *        Data Cache related maintenance functions
 ***********************************************************/

	.section .text.cp15_invalid_dcache_by_set_way
	.global   cp15_invalid_dcache_by_set_way
cp15_invalid_dcache_by_set_way:
	push    {r1-r4}
	mrc     p15, 1, r0, c0, c0, 0   // Read CCSIDR
	mov     r1, r0, lsr #3          // Get Associativity (num of ways)
	and     r1, r1, #3              // 3 is specific to CortexA5 with 32 KB
	mov     r2, r0, lsr #13         // Get NumSets (num of sets)
	and     r2, r2, #0xFF           // 8bit is specific to CortexA5 with 32 KB
	mov     r0, #0                  // 0:SHL:5
1:
	lsl     r4, r1, #30
	mov     r3, r2
2:
	orr     r0, r4, r3, lsl #5
	mcr     p15, 0, r0, c7, c6, 2   // DCISW()
	subs    r3, r3, #1              // 1:SHL:30
	bpl     2b
	subs    r1, r1, #1
	bpl     1b
	dsb
	pop     {r1-r4}
	bx      lr

	.section .text.cp15_clean_dcache_by_set_way
	.global   cp15_clean_dcache_by_set_way
cp15_clean_dcache_by_set_way:
	push    {r1-r4}
	mrc     p15, 1, r0, c0, c0, 0   // Read CCSIDR
	mov     r1, r0, lsr #3          // Get Associativity (num of ways)
	and     r1, r1, #3              // 3 is specific to CortexA5 with 32 KB
	mov     r2, r0, lsr #13         // Get NumSets (num of sets)
	and     r2, r2, #0xFF           // 8bit is specific to CortexA5 with 32 KB
	mov     r0, #0                  // 0:SHL:5
1:
	lsl     r4, r1, #30
	mov     r3, r2
2:
	orr     r0, r4, r3, lsl #5
	mcr     p15, 0, r0, c7, c10, 2  // DCCSW()
	subs    r3, r3, #1              // 1:SHL:30
	bpl     2b
	subs    r1, r1, #1
	bpl     1b
	dsb
	pop     {r1-r4}
	bx      lr

	.section .text.cp15_clean_invalid_dcache_by_set_way
	.global   cp15_clean_invalid_dcache_by_set_way
cp15_clean_invalid_dcache_by_set_way:
	push    {r1-r4}
	mrc     p15, 1, r0, c0, c0, 0   // Read CCSIDR
	mov     r1, r0, lsr #3          // Get Associativity (num of ways)
	and     r1, r1, #3              // 3 is specific to CortexA5 with 32 KB
	mov     r2, r0, lsr #13         // Get NumSets (num of sets)
	and     r2, r2, #0xFF           // 8bit is specific to CortexA5 with 32 KB
	mov     r0, #0                  // 0:SHL:5
1:
	lsl     r4, r1, #30
	mov     r3, r2
2:
	orr     r0, r4, r3, lsl #5
	mcr     p15, 0, r0, c7, c14, 2  // DCCISW()
	subs    r3, r3, #1              // 1:SHL:30
	bpl     2b
	subs    r1, r1, #1
	bpl     1b
	dsb
	pop     {r1-r4}
	bx      lr

	.section .text.cp15_invalid_dcache_by_mva
	.global   cp15_invalid_dcache_by_mva
cp15_invalid_dcache_by_mva:
	mov     r2, #0x20               // Eight words per line, Cortex-A5 L1 Line Size 32 Bytes
	mov     r3, r0
inv_loop:
	mcr     p15, 0, r0, c7, c6, 1   // DCIMVAC()
	add     r3, r3, r2
	cmp     r3, r1
	bls     inv_loop
	bx      lr

	.section .text.cp15_clean_dcache_by_mva
	.global   cp15_clean_dcache_by_mva
cp15_clean_dcache_by_mva:
	mov     r2, #0x20               // Eight words per line, Cortex-A5 L1 Line Size 32 Bytes
	mov     r3, r0
clean_loop:
	mcr     p15, 0, r0, c7, c10, 1  // DCCMVAC()
	add     r3, r3, r2
	cmp     r3, r1
	bls     clean_loop
	bx      lr

	.section .text.cp15_clean_dcache_umva
	.global   cp15_clean_dcache_umva
cp15_clean_dcache_umva:
	mov     r0, #0
	mcr     p15, 0, r0, c7, c11, 1  // DCCMVAU()
	bx      lr

	.section .text.cp15_clean_invalid_dcache_by_mva
	.global   cp15_clean_invalid_dcache_by_mva
cp15_clean_invalid_dcache_by_mva:
	mov     r2, #0x20               // Eight words per line, Cortex-A5 L1 Line Size 32 Bytes
	mov     r3, r0
clinv_loop:
	mcr     p15, 0, r0, c7, c14, 1  // DCCIMVAC()
	add     r3, r3, r2
	cmp     r3, r1
	bls     clinv_loop
	bx      lr

	.section .text.cp15_coherent_dcache_for_dma
	.global   cp15_coherent_dcache_for_dma
cp15_coherent_dcache_for_dma:
	push    {r2-r4}
	mrc     p15, 0, r3, c0, c0, 1   // read Cache Type Register
	lsr     r3, r3, #16
	and     r3, r3, #0xf            // DminLine
	mov     r2, #4
	mov     r2, r2, lsl r3          // cache line size, in bytes (4*2^DminLine)

	sub     r3, r2, #1              // cache line mask
	bic     r4, r0, r3              // address of the first cache line
1:
	mcr     p15, 0, r4, c7, c11, 1  // DCCMVAU()
	add     r4, r4, r2
	cmp     r4, r1
	blo     1b
	dsb

	bic     r4, r0, r3
2:
	mcr     p15, 0, r4, c7, c5, 1   // ICIMVAU()
	add     r4, r4, r2
	cmp     r4, r1
	blo     2b
	mov     r0, #0
	mcr     p15, 0, r0, c7, c1, 6   // BPIALLIS()
	mcr     p15, 0, r0, c7, c5, 6   // BPIALL()
	dsb
	isb
	pop     {r2-r4}
	bx      lr

	.section .text.cp15_invalidate_dcache_for_dma
	.global   cp15_invalidate_dcache_for_dma
cp15_invalidate_dcache_for_dma:
	push    {r2-r3}
	mrc     p15, 0, r3, c0, c0, 1   // read CP15 Cache Type Register
	lsr     r3, r3, #16
	and     r3, r3, #0xf            // DminLine
	mov     r2, #4
	mov     r2, r2, lsl r3          // cache line size, in bytes (4*2^DminLine)

	sub     r3, r2, #1              // cache line mask
	bic     r0, r0, r3              // address of the first cache line
3:
	mcr     p15, 0, r0, c7, c6, 1   // CP15:DCIMVAC(r0)
	add     r0, r0, r2
	cmp     r0, r1                  // while ('cache line address' < 'end')
	blo     3b
	dsb
	pop     {r2-r3}
	bx      lr

	.section .text.cp15_clean_dcache_for_dma
	.global   cp15_clean_dcache_for_dma
cp15_clean_dcache_for_dma:
	mrc     p15, 0, r3, c0, c0, 1   // read Cache Type Register
	lsr     r3, r3, #16
	and     r3, r3, #0xf            // DminLine
	mov     r2, #4
	mov     r2, r2, lsl r3          // cache line size, in bytes (4*2^DminLine)

	sub     r3, r2, #1              // cache line mask
	bic     r0, r0, r3              // address of the first cache line
4:
	mcr     p15, 0, r0, c7, c10, 1  // DCCMVAC()
	add     r0, r0, r2
	cmp     r0, r1
	blo     4b
	dsb
	bx      lr

	.section .text.cp15_flush_dcache_for_dma
	.global   cp15_flush_dcache_for_dma
cp15_flush_dcache_for_dma:
	mrc     p15, 0, r3, c0, c0, 1   // read Cache Type Register
	lsr     r3, r3, #16
	and     r3, r3, #0xf            // DminLine
	mov     r2, #4
	mov     r2, r2, lsl r3          // cache line size, in bytes (4*2^DminLine)

	sub     r3, r2, #1              // cache line mask
	bic     r0, r0, r3              // address of the first cache line
5:
	mcr     p15, 0, r0, c7, c14, 1  // DCCIMVAC()
	add     r0, r0, r2
	cmp     r0, r1
	blo     5b
	dsb
	bx      lr
