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

	MODULE  ?cpsr

	/* Forward declaration of sections. */
	SECTION IRQ_STACK:DATA:NOROOT(2)
	SECTION CSTACK:DATA:NOROOT(3)

/*----------------------------------------------------------------------------
 *        Functions to access CPSR
 *----------------------------------------------------------------------------*/

	SECTION .v_arm_clr_cpsr_bits:CODE:NOROOT(2)
	PUBLIC v_arm_clr_cpsr_bits
v_arm_clr_cpsr_bits:
	push	{r1}
	mrs	r1, cpsr
	mvn	r0, r0
	and	r1, r1,r0
	msr	CPSR_c, r1
	pop	{r1}
	bx	lr

	SECTION .v_arm_set_cpsr_bits:CODE:NOROOT(2)
	PUBLIC v_arm_set_cpsr_bits
v_arm_set_cpsr_bits:
	push	{r1}
	mrs	r1, cpsr
	orr	r1, r1, r0
	msr	cpsr_c, r1
	pop	{r1}
	bx	lr

	END
