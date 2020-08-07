/* armv8-32-curve25519
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/* Generated using (from wolfssl):
 *   cd ../scripts
 *   ruby ./x25519/x25519.rb arm32 ../wolfssl/wolfcrypt/src/port/arm/armv8-32-curve25519.S
 */

#ifdef WOLFSSL_ARMASM
#ifndef __aarch64__
	.text
	.align	2
	.globl	fe_init
	.type	fe_init, %function
fe_init:
	bx	lr
	.size	fe_init,.-fe_init
	.text
	.align	2
	.globl	fe_frombytes
	.type	fe_frombytes, %function
fe_frombytes:
	push	{r4, r5, r6, r7, lr}
	ldrd	r2, r3, [r1]
	ldr	r12, [r1, #8]
	ldr	lr, [r1, #12]
	ldrd	r4, r5, [r1, #16]
	ldrd	r6, r7, [r1, #24]
	and	r7, r7, #0x7fffffff
	strd	r2, r3, [r0]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	strd	r4, r5, [r0, #16]
	strd	r6, r7, [r0, #24]
	pop	{r4, r5, r6, r7, pc}
	.size	fe_frombytes,.-fe_frombytes
	.text
	.align	2
	.globl	fe_tobytes
	.type	fe_tobytes, %function
fe_tobytes:
	push	{r4, r5, r6, r7, r8, lr}
	ldrd	r2, r3, [r1]
	ldr	r12, [r1, #8]
	ldr	lr, [r1, #12]
	ldrd	r4, r5, [r1, #16]
	ldrd	r6, r7, [r1, #24]
	adds	r8, r2, #19
	adcs	r8, r3, #0
	adcs	r8, r12, #0
	adcs	r8, lr, #0
	adcs	r8, r4, #0
	adcs	r8, r5, #0
	adcs	r8, r6, #0
	adc	r8, r7, #0
	asr	r8, r8, #31
	and	r8, r8, #19
	adds	r2, r2, r8
	adcs	r3, r3, #0
	adcs	r12, r12, #0
	adcs	lr, lr, #0
	adcs	r4, r4, #0
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adc	r7, r7, #0
	and	r7, r7, #0x7fffffff
	strd	r2, r3, [r0]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	strd	r4, r5, [r0, #16]
	strd	r6, r7, [r0, #24]
	pop	{r4, r5, r6, r7, r8, pc}
	.size	fe_tobytes,.-fe_tobytes
	.text
	.align	2
	.globl	fe_1
	.type	fe_1, %function
fe_1:
	# Set one
	mov	r2, #1
	mov	r1, #0
	str	r2, [r0]
	str	r1, [r0, #4]
	str	r1, [r0, #8]
	str	r1, [r0, #12]
	str	r1, [r0, #16]
	str	r1, [r0, #20]
	str	r1, [r0, #24]
	str	r1, [r0, #28]
	bx	lr
	.size	fe_1,.-fe_1
	.text
	.align	2
	.globl	fe_0
	.type	fe_0, %function
fe_0:
	# Set zero
	mov	r1, #0
	str	r1, [r0]
	str	r1, [r0, #4]
	str	r1, [r0, #8]
	str	r1, [r0, #12]
	str	r1, [r0, #16]
	str	r1, [r0, #20]
	str	r1, [r0, #24]
	str	r1, [r0, #28]
	bx	lr
	.size	fe_0,.-fe_0
	.text
	.align	2
	.globl	fe_copy
	.type	fe_copy, %function
fe_copy:
	push	{lr}
	# Copy
	ldrd	r2, r3, [r1]
	ldr	r12, [r1, #8]
	ldr	lr, [r1, #12]
	strd	r2, r3, [r0]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	ldrd	r2, r3, [r1, #16]
	ldr	r12, [r1, #24]
	ldr	lr, [r1, #28]
	strd	r2, r3, [r0, #16]
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	pop	{pc}
	.size	fe_copy,.-fe_copy
	.text
	.align	2
	.globl	fe_sub
	.type	fe_sub, %function
fe_sub:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	# Sub
	ldr	r12, [r1]
	ldr	lr, [r1, #4]
	ldrd	r4, r5, [r1, #8]
	ldrd	r6, r7, [r2]
	ldrd	r8, r9, [r2, #8]
	subs	r6, r12, r6
	sbcs	r7, lr, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	strd	r6, r7, [r0]
	strd	r8, r9, [r0, #8]
	ldr	r12, [r1, #16]
	ldr	lr, [r1, #20]
	ldrd	r4, r5, [r1, #24]
	ldrd	r6, r7, [r2, #16]
	ldrd	r8, r9, [r2, #24]
	sbcs	r6, r12, r6
	sbcs	r7, lr, r7
	sbcs	r8, r4, r8
	sbc	r9, r5, r9
	mov	r10, #-19
	asr	r3, r9, #31
	#   Mask the modulus
	and	r10, r3, r10
	and	r11, r3, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	adds	r12, r12, r10
	adcs	lr, lr, r3
	adcs	r4, r4, r3
	adcs	r5, r5, r3
	adcs	r6, r6, r3
	adcs	r7, r7, r3
	adcs	r8, r8, r3
	adc	r9, r9, r11
	str	r12, [r0]
	str	lr, [r0, #4]
	strd	r4, r5, [r0, #8]
	strd	r6, r7, [r0, #16]
	strd	r8, r9, [r0, #24]
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_sub,.-fe_sub
	.text
	.align	2
	.globl	fe_add
	.type	fe_add, %function
fe_add:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	# Add
	ldr	r12, [r1]
	ldr	lr, [r1, #4]
	ldrd	r4, r5, [r1, #8]
	ldrd	r6, r7, [r2]
	ldrd	r8, r9, [r2, #8]
	adds	r6, r12, r6
	adcs	r7, lr, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	strd	r6, r7, [r0]
	strd	r8, r9, [r0, #8]
	ldr	r12, [r1, #16]
	ldr	lr, [r1, #20]
	ldrd	r4, r5, [r1, #24]
	ldrd	r6, r7, [r2, #16]
	ldrd	r8, r9, [r2, #24]
	adcs	r6, r12, r6
	adcs	r7, lr, r7
	adcs	r8, r4, r8
	adc	r9, r5, r9
	mov	r10, #-19
	asr	r3, r9, #31
	#   Mask the modulus
	and	r10, r3, r10
	and	r11, r3, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	subs	r12, r12, r10
	sbcs	lr, lr, r3
	sbcs	r4, r4, r3
	sbcs	r5, r5, r3
	sbcs	r6, r6, r3
	sbcs	r7, r7, r3
	sbcs	r8, r8, r3
	sbc	r9, r9, r11
	str	r12, [r0]
	str	lr, [r0, #4]
	strd	r4, r5, [r0, #8]
	strd	r6, r7, [r0, #16]
	strd	r8, r9, [r0, #24]
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_add,.-fe_add
	.text
	.align	2
	.globl	fe_neg
	.type	fe_neg, %function
fe_neg:
	push	{r4, r5, lr}
	mov	r5, #-1
	mov	r4, #-19
	ldrd	r2, r3, [r1]
	ldr	r12, [r1, #8]
	ldr	lr, [r1, #12]
	subs	r2, r4, r2
	sbcs	r3, r5, r3
	sbcs	r12, r5, r12
	sbcs	lr, r5, lr
	strd	r2, r3, [r0]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	mov	r4, #0x7fffffff
	ldrd	r2, r3, [r1, #16]
	ldr	r12, [r1, #24]
	ldr	lr, [r1, #28]
	sbcs	r2, r5, r2
	sbcs	r3, r5, r3
	sbcs	r12, r5, r12
	sbc	lr, r4, lr
	strd	r2, r3, [r0, #16]
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	pop	{r4, r5, pc}
	.size	fe_neg,.-fe_neg
	.text
	.align	2
	.globl	fe_isnonzero
	.type	fe_isnonzero, %function
fe_isnonzero:
	push	{r4, r5, r6, r7, r8, lr}
	ldrd	r2, r3, [r0]
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [r0, #24]
	adds	r1, r2, #19
	adcs	r1, r3, #0
	adcs	r1, r12, #0
	adcs	r1, lr, #0
	adcs	r1, r4, #0
	adcs	r1, r5, #0
	adcs	r1, r6, #0
	adc	r1, r7, #0
	asr	r1, r1, #31
	and	r1, r1, #19
	adds	r2, r2, r1
	adcs	r3, r3, #0
	adcs	r12, r12, #0
	adcs	lr, lr, #0
	adcs	r4, r4, #0
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adc	r7, r7, #0
	and	r7, r7, #0x7fffffff
	orr	r2, r2, r3
	orr	r12, r12, lr
	orr	r4, r4, r5
	orr	r6, r6, r7
	orr	r12, r12, r4
	orr	r2, r2, r6
	orr	r0, r2, r12
	pop	{r4, r5, r6, r7, r8, pc}
	.size	fe_isnonzero,.-fe_isnonzero
	.text
	.align	2
	.globl	fe_isnegative
	.type	fe_isnegative, %function
fe_isnegative:
	push	{lr}
	ldrd	r2, r3, [r0]
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	adds	r1, r2, #19
	adcs	r1, r3, #0
	adcs	r1, r12, #0
	adcs	r1, lr, #0
	ldrd	r2, r3, [r0, #16]
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	adcs	r1, r2, #0
	adcs	r1, r3, #0
	adcs	r1, r12, #0
	ldr	r2, [r0]
	adc	r1, lr, #0
	and	r0, r2, #1
	lsr	r1, r1, #31
	eor	r0, r0, r1
	pop	{pc}
	.size	fe_isnegative,.-fe_isnegative
	.text
	.align	2
	.globl	fe_cmov_table
	.type	fe_cmov_table, %function
fe_cmov_table:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sxtb	r2, r2
	sbfx	r7, r2, #7, #1
	eor	r10, r2, r7
	sub	r10, r10, r7
	mov	r3, #1
	mov	r12, #0
	mov	lr, #1
	mov	r4, #0
	mov	r5, #0
	mov	r6, #0
	mov	r7, #0x80000000
	ror	r7, r7, #31
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #30
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #29
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #28
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #27
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #26
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #25
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #24
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #32]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #64]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	sub	r1, r1, #0x2a0
	mov	r8, #-19
	mov	r9, #-1
	subs	r8, r8, r5
	sbcs	r9, r9, r6
	sbc	r11, r11, r11
	asr	r10, r2, #31
	eor	r7, r3, lr
	and	r7, r7, r10
	eor	r3, r3, r7
	eor	lr, lr, r7
	eor	r7, r12, r4
	and	r7, r7, r10
	eor	r12, r12, r7
	eor	r4, r4, r7
	eor	r8, r8, r5
	and	r8, r8, r10
	eor	r5, r5, r8
	eor	r9, r9, r6
	and	r9, r9, r10
	eor	r6, r6, r9
	str	r3, [r0]
	str	r12, [r0, #4]
	str	lr, [r0, #32]
	str	r4, [r0, #36]
	str	r5, [r0, #64]
	str	r6, [r0, #68]
	sbfx	r7, r2, #7, #1
	eor	r10, r2, r7
	sub	r10, r10, r7
	mov	r3, #0
	mov	r12, #0
	mov	lr, #0
	mov	r4, #0
	mov	r5, #0
	mov	r6, #0
	mov	r7, #0x80000000
	ror	r7, r7, #31
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #30
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #29
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #28
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #27
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #26
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #25
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #24
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #8]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #40]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #72]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	sub	r1, r1, #0x2a0
	mov	r8, #-1
	mov	r9, #-1
	rsbs	r11, r11, #0
	sbcs	r8, r8, r5
	sbcs	r9, r9, r6
	sbc	r11, r11, r11
	asr	r10, r2, #31
	eor	r7, r3, lr
	and	r7, r7, r10
	eor	r3, r3, r7
	eor	lr, lr, r7
	eor	r7, r12, r4
	and	r7, r7, r10
	eor	r12, r12, r7
	eor	r4, r4, r7
	eor	r8, r8, r5
	and	r8, r8, r10
	eor	r5, r5, r8
	eor	r9, r9, r6
	and	r9, r9, r10
	eor	r6, r6, r9
	str	r3, [r0, #8]
	str	r12, [r0, #12]
	str	lr, [r0, #40]
	str	r4, [r0, #44]
	str	r5, [r0, #72]
	str	r6, [r0, #76]
	sbfx	r7, r2, #7, #1
	eor	r10, r2, r7
	sub	r10, r10, r7
	mov	r3, #0
	mov	r12, #0
	mov	lr, #0
	mov	r4, #0
	mov	r5, #0
	mov	r6, #0
	mov	r7, #0x80000000
	ror	r7, r7, #31
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #30
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #29
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #28
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #27
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #26
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #25
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #24
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #16]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #48]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #80]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	sub	r1, r1, #0x2a0
	mov	r8, #-1
	mov	r9, #-1
	rsbs	r11, r11, #0
	sbcs	r8, r8, r5
	sbcs	r9, r9, r6
	sbc	r11, r11, r11
	asr	r10, r2, #31
	eor	r7, r3, lr
	and	r7, r7, r10
	eor	r3, r3, r7
	eor	lr, lr, r7
	eor	r7, r12, r4
	and	r7, r7, r10
	eor	r12, r12, r7
	eor	r4, r4, r7
	eor	r8, r8, r5
	and	r8, r8, r10
	eor	r5, r5, r8
	eor	r9, r9, r6
	and	r9, r9, r10
	eor	r6, r6, r9
	str	r3, [r0, #16]
	str	r12, [r0, #20]
	str	lr, [r0, #48]
	str	r4, [r0, #52]
	str	r5, [r0, #80]
	str	r6, [r0, #84]
	sbfx	r7, r2, #7, #1
	eor	r10, r2, r7
	sub	r10, r10, r7
	mov	r3, #0
	mov	r12, #0
	mov	lr, #0
	mov	r4, #0
	mov	r5, #0
	mov	r6, #0
	mov	r7, #0x80000000
	ror	r7, r7, #31
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #30
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #29
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #28
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #27
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #26
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #25
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	add	r1, r1, #0x60
	mov	r7, #0x80000000
	ror	r7, r7, #24
	ror	r7, r7, r10
	asr	r7, r7, #31
	ldrd	r8, r9, [r1, #24]
	eor	r8, r8, r3
	eor	r9, r9, r12
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r3, r3, r8
	eor	r12, r12, r9
	ldrd	r8, r9, [r1, #56]
	eor	r8, r8, lr
	eor	r9, r9, r4
	and	r8, r8, r7
	and	r9, r9, r7
	eor	lr, lr, r8
	eor	r4, r4, r9
	ldrd	r8, r9, [r1, #88]
	eor	r8, r8, r5
	eor	r9, r9, r6
	and	r8, r8, r7
	and	r9, r9, r7
	eor	r5, r5, r8
	eor	r6, r6, r9
	sub	r1, r1, #0x2a0
	mov	r8, #-1
	mov	r9, #0x7fffffff
	rsbs	r11, r11, #0
	sbcs	r8, r8, r5
	sbc	r9, r9, r6
	asr	r10, r2, #31
	eor	r7, r3, lr
	and	r7, r7, r10
	eor	r3, r3, r7
	eor	lr, lr, r7
	eor	r7, r12, r4
	and	r7, r7, r10
	eor	r12, r12, r7
	eor	r4, r4, r7
	eor	r8, r8, r5
	and	r8, r8, r10
	eor	r5, r5, r8
	eor	r9, r9, r6
	and	r9, r9, r10
	eor	r6, r6, r9
	str	r3, [r0, #24]
	str	r12, [r0, #28]
	str	lr, [r0, #56]
	str	r4, [r0, #60]
	str	r5, [r0, #88]
	str	r6, [r0, #92]
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_cmov_table,.-fe_cmov_table
	.text
	.align	2
	.globl	fe_mul
	.type	fe_mul, %function
fe_mul:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #0x40
	# Multiply
	ldr	r7, [r1]
	ldr	r8, [r1, #4]
	ldr	r9, [r2]
	ldr	lr, [r2, #4]
	#  A[0] * B[0] = 0
	umull	r4, r5, r7, r9
	str	r4, [sp]
	#  A[0] * B[1] = 1
	umull	r3, r6, r7, lr
	adds	r5, r5, r3
	adc	r6, r6, #0
	#  A[1] * B[0] = 1
	umull	r3, r12, r8, r9
	adds	r5, r5, r3
	mov	r4, #0
	adcs	r6, r6, r12
	adc	r4, r4, #0
	str	r5, [sp, #4]
	#  A[2] * B[0] = 2
	ldr	r10, [r1, #8]
	umull	r3, r12, r10, r9
	adds	r6, r6, r3
	adc	r4, r4, r12
	#  A[1] * B[1] = 2
	umull	r3, r12, r8, lr
	adds	r6, r6, r3
	mov	r5, #0
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[0] * B[2] = 2
	ldr	r11, [r2, #8]
	umull	r3, r12, r7, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	str	r6, [sp, #8]
	#  A[0] * B[3] = 3
	ldr	r11, [r2, #12]
	umull	r3, r12, r7, r11
	adds	r4, r4, r3
	mov	r6, #0
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[1] * B[2] = 3
	ldr	r11, [r2, #8]
	umull	r3, r12, r8, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[2] * B[1] = 3
	umull	r3, r12, r10, lr
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[3] * B[0] = 3
	ldr	r10, [r1, #12]
	umull	r3, r12, r10, r9
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	str	r4, [sp, #12]
	#  A[4] * B[0] = 4
	ldr	r10, [r1, #16]
	umull	r3, r12, r10, r9
	adds	r5, r5, r3
	mov	r4, #0
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[3] * B[1] = 4
	ldr	r10, [r1, #12]
	umull	r3, r12, r10, lr
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[2] * B[2] = 4
	ldr	r10, [r1, #8]
	umull	r3, r12, r10, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[1] * B[3] = 4
	ldr	r11, [r2, #12]
	umull	r3, r12, r8, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[0] * B[4] = 4
	ldr	r11, [r2, #16]
	umull	r3, r12, r7, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	str	r5, [sp, #16]
	#  A[0] * B[5] = 5
	ldr	r11, [r2, #20]
	umull	r3, r12, r7, r11
	adds	r6, r6, r3
	mov	r5, #0
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[1] * B[4] = 5
	ldr	r11, [r2, #16]
	umull	r3, r12, r8, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[2] * B[3] = 5
	ldr	r11, [r2, #12]
	umull	r3, r12, r10, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[3] * B[2] = 5
	ldr	r10, [r1, #12]
	ldr	r11, [r2, #8]
	umull	r3, r12, r10, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[4] * B[1] = 5
	ldr	r10, [r1, #16]
	umull	r3, r12, r10, lr
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[5] * B[0] = 5
	ldr	r10, [r1, #20]
	umull	r3, r12, r10, r9
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	str	r6, [sp, #20]
	#  A[6] * B[0] = 6
	ldr	r10, [r1, #24]
	umull	r3, r12, r10, r9
	adds	r4, r4, r3
	mov	r6, #0
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[5] * B[1] = 6
	ldr	r10, [r1, #20]
	umull	r3, r12, r10, lr
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[4] * B[2] = 6
	ldr	r10, [r1, #16]
	umull	r3, r12, r10, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[3] * B[3] = 6
	ldr	r10, [r1, #12]
	ldr	r11, [r2, #12]
	umull	r3, r12, r10, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[2] * B[4] = 6
	ldr	r10, [r1, #8]
	ldr	r11, [r2, #16]
	umull	r3, r12, r10, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[1] * B[5] = 6
	ldr	r11, [r2, #20]
	umull	r3, r12, r8, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[0] * B[6] = 6
	ldr	r11, [r2, #24]
	umull	r3, r12, r7, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	str	r4, [sp, #24]
	#  A[0] * B[7] = 7
	ldr	r11, [r2, #28]
	umull	r3, r12, r7, r11
	adds	r5, r5, r3
	mov	r4, #0
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[1] * B[6] = 7
	ldr	r11, [r2, #24]
	umull	r3, r12, r8, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[2] * B[5] = 7
	ldr	r11, [r2, #20]
	umull	r3, r12, r10, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[3] * B[4] = 7
	ldr	r10, [r1, #12]
	ldr	r11, [r2, #16]
	umull	r3, r12, r10, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[4] * B[3] = 7
	ldr	r10, [r1, #16]
	ldr	r11, [r2, #12]
	umull	r3, r12, r10, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[5] * B[2] = 7
	ldr	r10, [r1, #20]
	ldr	r11, [r2, #8]
	umull	r3, r12, r10, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[6] * B[1] = 7
	ldr	r10, [r1, #24]
	umull	r3, r12, r10, lr
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[7] * B[0] = 7
	ldr	r10, [r1, #28]
	umull	r3, r12, r10, r9
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	str	r5, [sp, #28]
	ldr	r7, [r1, #24]
	ldr	r9, [r2, #24]
	#  A[7] * B[1] = 8
	umull	r3, r12, r10, lr
	adds	r6, r6, r3
	mov	r5, #0
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[6] * B[2] = 8
	umull	r3, r12, r7, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[5] * B[3] = 8
	ldr	r10, [r1, #20]
	ldr	r11, [r2, #12]
	umull	r3, r12, r10, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[4] * B[4] = 8
	ldr	r10, [r1, #16]
	ldr	r11, [r2, #16]
	umull	r3, r12, r10, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[3] * B[5] = 8
	ldr	r10, [r1, #12]
	ldr	r11, [r2, #20]
	umull	r3, r12, r10, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[2] * B[6] = 8
	ldr	r10, [r1, #8]
	umull	r3, r12, r10, r9
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[1] * B[7] = 8
	ldr	r11, [r2, #28]
	umull	r3, r12, r8, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	str	r6, [sp, #32]
	ldr	r8, [r1, #28]
	mov	lr, r11
	#  A[2] * B[7] = 9
	umull	r3, r12, r10, lr
	adds	r4, r4, r3
	mov	r6, #0
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[3] * B[6] = 9
	ldr	r10, [r1, #12]
	umull	r3, r12, r10, r9
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[4] * B[5] = 9
	ldr	r10, [r1, #16]
	ldr	r11, [r2, #20]
	umull	r3, r12, r10, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[5] * B[4] = 9
	ldr	r10, [r1, #20]
	ldr	r11, [r2, #16]
	umull	r3, r12, r10, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[6] * B[3] = 9
	ldr	r11, [r2, #12]
	umull	r3, r12, r7, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[7] * B[2] = 9
	ldr	r11, [r2, #8]
	umull	r3, r12, r8, r11
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	str	r4, [sp, #36]
	#  A[7] * B[3] = 10
	ldr	r11, [r2, #12]
	umull	r3, r12, r8, r11
	adds	r5, r5, r3
	mov	r4, #0
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[6] * B[4] = 10
	ldr	r11, [r2, #16]
	umull	r3, r12, r7, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[5] * B[5] = 10
	ldr	r11, [r2, #20]
	umull	r3, r12, r10, r11
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[4] * B[6] = 10
	ldr	r10, [r1, #16]
	umull	r3, r12, r10, r9
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[3] * B[7] = 10
	ldr	r10, [r1, #12]
	umull	r3, r12, r10, lr
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	str	r5, [sp, #40]
	#  A[4] * B[7] = 11
	ldr	r10, [r1, #16]
	umull	r3, r12, r10, lr
	adds	r6, r6, r3
	mov	r5, #0
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[5] * B[6] = 11
	ldr	r10, [r1, #20]
	umull	r3, r12, r10, r9
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[6] * B[5] = 11
	umull	r3, r12, r7, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	#  A[7] * B[4] = 11
	ldr	r11, [r2, #16]
	umull	r3, r12, r8, r11
	adds	r6, r6, r3
	adcs	r4, r4, r12
	adc	r5, r5, #0
	str	r6, [sp, #44]
	#  A[7] * B[5] = 12
	ldr	r11, [r2, #20]
	umull	r3, r12, r8, r11
	adds	r4, r4, r3
	mov	r6, #0
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[6] * B[6] = 12
	umull	r3, r12, r7, r9
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	#  A[5] * B[7] = 12
	umull	r3, r12, r10, lr
	adds	r4, r4, r3
	adcs	r5, r5, r12
	adc	r6, r6, #0
	str	r4, [sp, #48]
	#  A[6] * B[7] = 13
	umull	r3, r12, r7, lr
	adds	r5, r5, r3
	mov	r4, #0
	adcs	r6, r6, r12
	adc	r4, r4, #0
	#  A[7] * B[6] = 13
	umull	r3, r12, r8, r9
	adds	r5, r5, r3
	adcs	r6, r6, r12
	adc	r4, r4, #0
	str	r5, [sp, #52]
	#  A[7] * B[7] = 14
	umull	r3, r12, r8, lr
	adds	r6, r6, r3
	adc	r4, r4, r12
	str	r6, [sp, #56]
	str	r4, [sp, #60]
	# Reduce
	#  Load bottom half
	ldrd	r4, r5, [sp]
	ldrd	r6, r7, [sp, #8]
	ldrd	r8, r9, [sp, #16]
	ldrd	r10, r11, [sp, #24]
	lsr	r3, r11, #31
	and	r11, r11, #0x7fffffff
	mov	lr, #19
	ldr	r1, [sp, #32]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	adds	r4, r4, r3
	mov	r2, #0
	adcs	r5, r5, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #36]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	add	r12, r12, r2
	adds	r5, r5, r3
	mov	r2, #0
	adcs	r6, r6, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #40]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	add	r12, r12, r2
	adds	r6, r6, r3
	mov	r2, #0
	adcs	r7, r7, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #44]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	add	r12, r12, r2
	adds	r7, r7, r3
	mov	r2, #0
	adcs	r8, r8, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #48]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	add	r12, r12, r2
	adds	r8, r8, r3
	mov	r2, #0
	adcs	r9, r9, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #52]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	add	r12, r12, r2
	adds	r9, r9, r3
	mov	r2, #0
	adcs	r10, r10, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #56]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	add	r12, r12, r2
	adds	r10, r10, r3
	mov	r2, #0
	adcs	r11, r11, r12
	adc	r2, r2, #0
	lsr	r3, r1, #31
	ldr	r1, [sp, #60]
	orr	r3, r3, r1, lsl #1
	umull	r3, r12, lr, r3
	adds	r11, r11, r3
	adc	r3, r12, r2
	#  Overflow
	lsl	r3, r3, #1
	orr	r3, r3, r11, lsr #31
	mul	r3, r3, lr
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r3
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	# Reduce if top bit set
	asr	r3, r11, #31
	and	r3, r3, lr
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r3
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	# Store
	strd	r4, r5, [r0]
	strd	r6, r7, [r0, #8]
	strd	r8, r9, [r0, #16]
	strd	r10, r11, [r0, #24]
	add	sp, sp, #0x40
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_mul,.-fe_mul
	.text
	.align	2
	.globl	fe_sq
	.type	fe_sq, %function
fe_sq:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #0x40
	# Square
	ldr	r7, [r1]
	ldr	r8, [r1, #4]
	ldr	r9, [r1, #8]
	ldr	r10, [r1, #12]
	ldr	r12, [r1, #16]
	#  A[0] * A[0] = 0
	umull	r4, r5, r7, r7
	str	r4, [sp]
	#  A[0] * A[1] = 1
	umull	r2, r3, r7, r8
	mov	r6, #0
	adds	r5, r5, r2
	adc	r6, r6, r3
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #4]
	#  A[1] * A[1] = 2
	umull	r2, r3, r8, r8
	adds	r6, r6, r2
	adc	r4, r4, r3
	#  A[0] * A[2] = 2
	umull	r2, r3, r7, r9
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #8]
	#  A[0] * A[3] = 3
	umull	r2, r3, r7, r10
	adds	r4, r4, r2
	adc	r5, r5, r3
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[1] * A[2] = 3
	umull	r2, r3, r8, r9
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #12]
	#  A[2] * A[2] = 4
	umull	r2, r3, r9, r9
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[1] * A[3] = 4
	umull	r2, r3, r8, r10
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[0] * A[4] = 4
	umull	r2, r3, r7, r12
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #16]
	#  A[0] * A[5] = 5
	ldr	r11, [r1, #20]
	umull	r2, r3, r7, r11
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[1] * A[4] = 5
	umull	r2, r3, r8, r12
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[2] * A[3] = 5
	umull	r2, r3, r9, r10
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #20]
	#  A[3] * A[3] = 6
	umull	r2, r3, r10, r10
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[2] * A[4] = 6
	umull	r2, r3, r9, r12
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[1] * A[5] = 6
	umull	r2, r3, r8, r11
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[0] * A[6] = 6
	ldr	r11, [r1, #24]
	umull	r2, r3, r7, r11
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #24]
	#  A[0] * A[7] = 7
	ldr	r11, [r1, #28]
	umull	r2, r3, r7, r11
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[1] * A[6] = 7
	ldr	r11, [r1, #24]
	umull	r2, r3, r8, r11
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[2] * A[5] = 7
	ldr	r11, [r1, #20]
	umull	r2, r3, r9, r11
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[3] * A[4] = 7
	umull	r2, r3, r10, r12
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #28]
	#  A[4] * A[4] = 8
	umull	r2, r3, r12, r12
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[3] * A[5] = 8
	umull	r2, r3, r10, r11
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[2] * A[6] = 8
	ldr	r11, [r1, #24]
	umull	r2, r3, r9, r11
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[1] * A[7] = 8
	ldr	r11, [r1, #28]
	umull	r2, r3, r8, r11
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #32]
	ldr	r7, [r1, #20]
	#  A[2] * A[7] = 9
	umull	r2, r3, r9, r11
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[3] * A[6] = 9
	ldr	r11, [r1, #24]
	umull	r2, r3, r10, r11
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[4] * A[5] = 9
	umull	r2, r3, r12, r7
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #36]
	mov	r8, r11
	#  A[5] * A[5] = 10
	umull	r2, r3, r7, r7
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[4] * A[6] = 10
	umull	r2, r3, r12, r8
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[3] * A[7] = 10
	ldr	r11, [r1, #28]
	umull	r2, r3, r10, r11
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #40]
	mov	r9, r11
	#  A[4] * A[7] = 11
	umull	r2, r3, r12, r9
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[5] * A[6] = 11
	umull	r2, r3, r7, r8
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #44]
	#  A[6] * A[6] = 12
	umull	r2, r3, r8, r8
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[5] * A[7] = 12
	umull	r2, r3, r7, r9
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #48]
	#  A[6] * A[7] = 13
	umull	r2, r3, r8, r9
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #52]
	#  A[7] * A[7] = 14
	umull	r2, r3, r9, r9
	adds	r6, r6, r2
	adc	r4, r4, r3
	str	r6, [sp, #56]
	str	r4, [sp, #60]
	# Reduce
	#  Load bottom half
	ldrd	r4, r5, [sp]
	ldrd	r6, r7, [sp, #8]
	ldrd	r8, r9, [sp, #16]
	ldrd	r10, r11, [sp, #24]
	lsr	r2, r11, #31
	and	r11, r11, #0x7fffffff
	mov	r12, #19
	ldr	r1, [sp, #32]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	adds	r4, r4, r2
	mov	lr, #0
	adcs	r5, r5, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #36]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r5, r5, r2
	mov	lr, #0
	adcs	r6, r6, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #40]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r6, r6, r2
	mov	lr, #0
	adcs	r7, r7, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #44]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r7, r7, r2
	mov	lr, #0
	adcs	r8, r8, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #48]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r8, r8, r2
	mov	lr, #0
	adcs	r9, r9, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #52]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r9, r9, r2
	mov	lr, #0
	adcs	r10, r10, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #56]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r10, r10, r2
	mov	lr, #0
	adcs	r11, r11, r3
	adc	lr, lr, #0
	lsr	r2, r1, #31
	ldr	r1, [sp, #60]
	orr	r2, r2, r1, lsl #1
	umull	r2, r3, r12, r2
	adds	r11, r11, r2
	adc	r2, r3, lr
	#  Overflow
	lsl	r2, r2, #1
	orr	r2, r2, r11, lsr #31
	mul	r2, r2, r12
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r2
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	# Reduce if top bit set
	asr	r2, r11, #31
	and	r2, r2, r12
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r2
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	# Store
	strd	r4, r5, [r0]
	strd	r6, r7, [r0, #8]
	strd	r8, r9, [r0, #16]
	strd	r10, r11, [r0, #24]
	add	sp, sp, #0x40
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_sq,.-fe_sq
	.text
	.align	2
	.globl	fe_mul121666
	.type	fe_mul121666, %function
fe_mul121666:
	push	{r4, r5, r6, r7, r8, r9, r10, lr}
	# Multiply by 121666
	ldrd	r2, r3, [r1]
	ldrd	r4, r5, [r1, #8]
	ldrd	r6, r7, [r1, #16]
	ldrd	r8, r9, [r1, #24]
	movw	lr, #0xdb42
	movt	lr, #1
	umull	r2, r10, r2, lr
	umull	r3, r12, r3, lr
	adds	r3, r3, r10
	adc	r10, r12, #0
	umull	r4, r12, r4, lr
	adds	r4, r4, r10
	adc	r10, r12, #0
	umull	r5, r12, r5, lr
	adds	r5, r5, r10
	adc	r10, r12, #0
	umull	r6, r12, r6, lr
	adds	r6, r6, r10
	adc	r10, r12, #0
	umull	r7, r12, r7, lr
	adds	r7, r7, r10
	adc	r10, r12, #0
	umull	r8, r12, r8, lr
	adds	r8, r8, r10
	adc	r10, r12, #0
	umull	r9, r12, r9, lr
	adds	r9, r9, r10
	adc	r10, r12, #0
	mov	lr, #19
	lsl	r10, r10, #1
	orr	r10, r10, r9, lsr #31
	mul	r10, r10, lr
	and	r9, r9, #0x7fffffff
	adds	r2, r2, r10
	adcs	r3, r3, #0
	adcs	r4, r4, #0
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adc	r9, r9, #0
	strd	r2, r3, [r0]
	strd	r4, r5, [r0, #8]
	strd	r6, r7, [r0, #16]
	strd	r8, r9, [r0, #24]
	pop	{r4, r5, r6, r7, r8, r9, r10, pc}
	.size	fe_mul121666,.-fe_mul121666
	.text
	.align	2
	.globl	fe_sq2
	.type	fe_sq2, %function
fe_sq2:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #0x40
	# Square * 2
	ldr	r7, [r1]
	ldr	r8, [r1, #4]
	ldr	r9, [r1, #8]
	ldr	r10, [r1, #12]
	ldr	r12, [r1, #16]
	#  A[0] * A[0] = 0
	umull	r4, r5, r7, r7
	str	r4, [sp]
	#  A[0] * A[1] = 1
	umull	r2, r3, r7, r8
	mov	r6, #0
	adds	r5, r5, r2
	adc	r6, r6, r3
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #4]
	#  A[1] * A[1] = 2
	umull	r2, r3, r8, r8
	adds	r6, r6, r2
	adc	r4, r4, r3
	#  A[0] * A[2] = 2
	umull	r2, r3, r7, r9
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #8]
	#  A[0] * A[3] = 3
	umull	r2, r3, r7, r10
	adds	r4, r4, r2
	adc	r5, r5, r3
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[1] * A[2] = 3
	umull	r2, r3, r8, r9
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #12]
	#  A[2] * A[2] = 4
	umull	r2, r3, r9, r9
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[1] * A[3] = 4
	umull	r2, r3, r8, r10
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[0] * A[4] = 4
	umull	r2, r3, r7, r12
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #16]
	#  A[0] * A[5] = 5
	ldr	r11, [r1, #20]
	umull	r2, r3, r7, r11
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[1] * A[4] = 5
	umull	r2, r3, r8, r12
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[2] * A[3] = 5
	umull	r2, r3, r9, r10
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #20]
	#  A[3] * A[3] = 6
	umull	r2, r3, r10, r10
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[2] * A[4] = 6
	umull	r2, r3, r9, r12
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[1] * A[5] = 6
	umull	r2, r3, r8, r11
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[0] * A[6] = 6
	ldr	r11, [r1, #24]
	umull	r2, r3, r7, r11
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #24]
	#  A[0] * A[7] = 7
	ldr	r11, [r1, #28]
	umull	r2, r3, r7, r11
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[1] * A[6] = 7
	ldr	r11, [r1, #24]
	umull	r2, r3, r8, r11
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[2] * A[5] = 7
	ldr	r11, [r1, #20]
	umull	r2, r3, r9, r11
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[3] * A[4] = 7
	umull	r2, r3, r10, r12
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #28]
	#  A[4] * A[4] = 8
	umull	r2, r3, r12, r12
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[3] * A[5] = 8
	umull	r2, r3, r10, r11
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[2] * A[6] = 8
	ldr	r11, [r1, #24]
	umull	r2, r3, r9, r11
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[1] * A[7] = 8
	ldr	r11, [r1, #28]
	umull	r2, r3, r8, r11
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #32]
	ldr	r7, [r1, #20]
	#  A[2] * A[7] = 9
	umull	r2, r3, r9, r11
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[3] * A[6] = 9
	ldr	r11, [r1, #24]
	umull	r2, r3, r10, r11
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[4] * A[5] = 9
	umull	r2, r3, r12, r7
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #36]
	mov	r8, r11
	#  A[5] * A[5] = 10
	umull	r2, r3, r7, r7
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[4] * A[6] = 10
	umull	r2, r3, r12, r8
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	#  A[3] * A[7] = 10
	ldr	r11, [r1, #28]
	umull	r2, r3, r10, r11
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #40]
	mov	r9, r11
	#  A[4] * A[7] = 11
	umull	r2, r3, r12, r9
	adds	r6, r6, r2
	mov	r5, #0
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	#  A[5] * A[6] = 11
	umull	r2, r3, r7, r8
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	adds	r6, r6, r2
	adcs	r4, r4, r3
	adc	r5, r5, #0
	str	r6, [sp, #44]
	#  A[6] * A[6] = 12
	umull	r2, r3, r8, r8
	adds	r4, r4, r2
	mov	r6, #0
	adcs	r5, r5, r3
	adc	r6, r6, #0
	#  A[5] * A[7] = 12
	umull	r2, r3, r7, r9
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	adds	r4, r4, r2
	adcs	r5, r5, r3
	adc	r6, r6, #0
	str	r4, [sp, #48]
	#  A[6] * A[7] = 13
	umull	r2, r3, r8, r9
	adds	r5, r5, r2
	mov	r4, #0
	adcs	r6, r6, r3
	adc	r4, r4, #0
	adds	r5, r5, r2
	adcs	r6, r6, r3
	adc	r4, r4, #0
	str	r5, [sp, #52]
	#  A[7] * A[7] = 14
	umull	r2, r3, r9, r9
	adds	r6, r6, r2
	adc	r4, r4, r3
	str	r6, [sp, #56]
	str	r4, [sp, #60]
	# Double and Reduce
	#  Load bottom half
	ldrd	r4, r5, [sp]
	ldrd	r6, r7, [sp, #8]
	ldrd	r8, r9, [sp, #16]
	ldrd	r10, r11, [sp, #24]
	lsr	r2, r11, #30
	lsl	r11, r11, #1
	orr	r11, r11, r10, lsr #31
	lsl	r10, r10, #1
	orr	r10, r10, r9, lsr #31
	lsl	r9, r9, #1
	orr	r9, r9, r8, lsr #31
	lsl	r8, r8, #1
	orr	r8, r8, r7, lsr #31
	lsl	r7, r7, #1
	orr	r7, r7, r6, lsr #31
	lsl	r6, r6, #1
	orr	r6, r6, r5, lsr #31
	lsl	r5, r5, #1
	orr	r5, r5, r4, lsr #31
	lsl	r4, r4, #1
	and	r11, r11, #0x7fffffff
	mov	r12, #19
	ldr	r1, [sp, #32]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	adds	r4, r4, r2
	mov	lr, #0
	adcs	r5, r5, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #36]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r5, r5, r2
	mov	lr, #0
	adcs	r6, r6, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #40]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r6, r6, r2
	mov	lr, #0
	adcs	r7, r7, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #44]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r7, r7, r2
	mov	lr, #0
	adcs	r8, r8, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #48]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r8, r8, r2
	mov	lr, #0
	adcs	r9, r9, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #52]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r9, r9, r2
	mov	lr, #0
	adcs	r10, r10, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #56]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	add	r3, r3, lr
	adds	r10, r10, r2
	mov	lr, #0
	adcs	r11, r11, r3
	adc	lr, lr, #0
	lsr	r2, r1, #30
	ldr	r1, [sp, #60]
	orr	r2, r2, r1, lsl #2
	umull	r2, r3, r12, r2
	adds	r11, r11, r2
	adc	r2, r3, lr
	#  Overflow
	lsl	r2, r2, #1
	orr	r2, r2, r11, lsr #31
	mul	r2, r2, r12
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r2
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	# Reduce if top bit set
	asr	r2, r11, #31
	and	r2, r2, r12
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r2
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	# Store
	strd	r4, r5, [r0]
	strd	r6, r7, [r0, #8]
	strd	r8, r9, [r0, #16]
	strd	r10, r11, [r0, #24]
	add	sp, sp, #0x40
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_sq2,.-fe_sq2
	.text
	.align	2
	.globl	fe_invert
	.type	fe_invert, %function
fe_invert:
	push	{r4, lr}
	sub	sp, sp, #0x88
	# Invert
	str	r0, [sp, #128]
	str	r1, [sp, #132]
	mov	r0, sp
	ldr	r1, [sp, #132]
	bl	fe_sq
	add	r0, sp, #32
	mov	r1, sp
	bl	fe_sq
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	add	r0, sp, #32
	ldr	r1, [sp, #132]
	add	r2, sp, #32
	bl	fe_mul
	mov	r0, sp
	mov	r1, sp
	add	r2, sp, #32
	bl	fe_mul
	add	r0, sp, #0x40
	mov	r1, sp
	bl	fe_sq
	add	r0, sp, #32
	add	r1, sp, #32
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #0x40
	add	r1, sp, #32
	bl	fe_sq
	mov	r4, #4
L_fe_invert1:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert1
	add	r0, sp, #32
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	add	r0, sp, #0x40
	add	r1, sp, #32
	bl	fe_sq
	mov	r4, #9
L_fe_invert2:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert2
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	add	r0, sp, #0x60
	add	r1, sp, #0x40
	bl	fe_sq
	mov	r4, #19
L_fe_invert3:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert3
	add	r0, sp, #0x40
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	mov	r4, #10
L_fe_invert4:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert4
	add	r0, sp, #32
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	add	r0, sp, #0x40
	add	r1, sp, #32
	bl	fe_sq
	mov	r4, #49
L_fe_invert5:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert5
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	add	r0, sp, #0x60
	add	r1, sp, #0x40
	bl	fe_sq
	mov	r4, #0x63
L_fe_invert6:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert6
	add	r0, sp, #0x40
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	mov	r4, #50
L_fe_invert7:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert7
	add	r0, sp, #32
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	mov	r4, #5
L_fe_invert8:
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_invert8
	ldr	r0, [sp, #128]
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	ldr	r1, [sp, #132]
	ldr	r0, [sp, #128]
	add	sp, sp, #0x88
	pop	{r4, pc}
	.size	fe_invert,.-fe_invert
	.text
	.align	2
	.globl	curve25519
	.type	curve25519, %function
curve25519:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #0xbc
	str	r0, [sp, #160]
	str	r1, [sp, #164]
	str	r2, [sp, #168]
	mov	r1, #0
	str	r1, [sp, #172]
	# Set one
	mov	r11, #1
	mov	r10, #0
	str	r11, [r0]
	str	r10, [r0, #4]
	str	r10, [r0, #8]
	str	r10, [r0, #12]
	str	r10, [r0, #16]
	str	r10, [r0, #20]
	str	r10, [r0, #24]
	str	r10, [r0, #28]
	# Set zero
	mov	r10, #0
	str	r10, [sp]
	str	r10, [sp, #4]
	str	r10, [sp, #8]
	str	r10, [sp, #12]
	str	r10, [sp, #16]
	str	r10, [sp, #20]
	str	r10, [sp, #24]
	str	r10, [sp, #28]
	# Set one
	mov	r11, #1
	mov	r10, #0
	str	r11, [sp, #32]
	str	r10, [sp, #36]
	str	r10, [sp, #40]
	str	r10, [sp, #44]
	str	r10, [sp, #48]
	str	r10, [sp, #52]
	str	r10, [sp, #56]
	str	r10, [sp, #60]
	# Copy
	ldrd	r4, r5, [r2]
	ldrd	r6, r7, [r2, #8]
	strd	r4, r5, [sp, #64]
	strd	r6, r7, [sp, #72]
	ldrd	r4, r5, [r2, #16]
	ldrd	r6, r7, [r2, #24]
	strd	r4, r5, [sp, #80]
	strd	r6, r7, [sp, #88]
	mov	r1, #30
	str	r1, [sp, #180]
	mov	r2, #28
	str	r2, [sp, #176]
L_curve25519_words:
L_curve25519_bits:
	ldr	r1, [sp, #164]
	ldr	r2, [r1, r2]
	ldr	r1, [sp, #180]
	lsr	r2, r2, r1
	and	r2, r2, #1
	str	r2, [sp, #184]
	ldr	r1, [sp, #172]
	eor	r1, r1, r2
	str	r1, [sp, #172]
	ldr	r0, [sp, #160]
	# Conditional Swap
	neg	r1, r1
	ldrd	r4, r5, [r0]
	ldrd	r6, r7, [sp, #64]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [r0]
	strd	r6, r7, [sp, #64]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [sp, #72]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [r0, #8]
	strd	r6, r7, [sp, #72]
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [sp, #80]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [r0, #16]
	strd	r6, r7, [sp, #80]
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [sp, #88]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [r0, #24]
	strd	r6, r7, [sp, #88]
	ldr	r1, [sp, #172]
	# Conditional Swap
	neg	r1, r1
	ldrd	r4, r5, [sp]
	ldrd	r6, r7, [sp, #32]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [sp]
	strd	r6, r7, [sp, #32]
	ldrd	r4, r5, [sp, #8]
	ldrd	r6, r7, [sp, #40]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [sp, #8]
	strd	r6, r7, [sp, #40]
	ldrd	r4, r5, [sp, #16]
	ldrd	r6, r7, [sp, #48]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [sp, #16]
	strd	r6, r7, [sp, #48]
	ldrd	r4, r5, [sp, #24]
	ldrd	r6, r7, [sp, #56]
	eor	r8, r4, r6
	eor	r9, r5, r7
	and	r8, r8, r1
	and	r9, r9, r1
	eor	r4, r4, r8
	eor	r5, r5, r9
	eor	r6, r6, r8
	eor	r7, r7, r9
	strd	r4, r5, [sp, #24]
	strd	r6, r7, [sp, #56]
	ldr	r1, [sp, #184]
	str	r1, [sp, #172]
	# Add-Sub
	#  Add
	ldrd	r4, r5, [r0]
	ldrd	r6, r7, [sp]
	adds	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [r0]
	#  Sub
	subs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #128]
	#  Add
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [sp, #8]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [r0, #8]
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #136]
	#  Add
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [sp, #16]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [r0, #16]
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #144]
	#  Add
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [sp, #24]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	adc	r9, r5, r7
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	sbc	r11, r5, r7
	mov	r3, #-19
	asr	r2, r9, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Sub modulus (if overflow)
	ldrd	r4, r5, [r0]
	subs	r4, r4, r3
	sbcs	r5, r5, r2
	strd	r4, r5, [r0]
	ldrd	r4, r5, [r0, #8]
	sbcs	r4, r4, r2
	sbcs	r5, r5, r2
	strd	r4, r5, [r0, #8]
	ldrd	r4, r5, [r0, #16]
	sbcs	r4, r4, r2
	sbcs	r5, r5, r2
	strd	r4, r5, [r0, #16]
	sbcs	r8, r8, r2
	sbc	r9, r9, r12
	strd	r8, r9, [r0, #24]
	mov	r3, #-19
	asr	r2, r11, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Add modulus (if underflow)
	ldrd	r4, r5, [sp, #128]
	adds	r4, r4, r3
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #128]
	ldrd	r4, r5, [sp, #136]
	adcs	r4, r4, r2
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #136]
	ldrd	r4, r5, [sp, #144]
	adcs	r4, r4, r2
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #144]
	adcs	r10, r10, r2
	adc	r11, r11, r12
	strd	r10, r11, [sp, #152]
	# Add-Sub
	#  Add
	ldrd	r4, r5, [sp, #64]
	ldrd	r6, r7, [sp, #32]
	adds	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [sp]
	#  Sub
	subs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #96]
	#  Add
	ldrd	r4, r5, [sp, #72]
	ldrd	r6, r7, [sp, #40]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [sp, #8]
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #104]
	#  Add
	ldrd	r4, r5, [sp, #80]
	ldrd	r6, r7, [sp, #48]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [sp, #16]
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #112]
	#  Add
	ldrd	r4, r5, [sp, #88]
	ldrd	r6, r7, [sp, #56]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	adc	r9, r5, r7
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	sbc	r11, r5, r7
	mov	r3, #-19
	asr	r2, r9, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Sub modulus (if overflow)
	ldrd	r4, r5, [sp]
	subs	r4, r4, r3
	sbcs	r5, r5, r2
	strd	r4, r5, [sp]
	ldrd	r4, r5, [sp, #8]
	sbcs	r4, r4, r2
	sbcs	r5, r5, r2
	strd	r4, r5, [sp, #8]
	ldrd	r4, r5, [sp, #16]
	sbcs	r4, r4, r2
	sbcs	r5, r5, r2
	strd	r4, r5, [sp, #16]
	sbcs	r8, r8, r2
	sbc	r9, r9, r12
	strd	r8, r9, [sp, #24]
	mov	r3, #-19
	asr	r2, r11, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Add modulus (if underflow)
	ldrd	r4, r5, [sp, #96]
	adds	r4, r4, r3
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #96]
	ldrd	r4, r5, [sp, #104]
	adcs	r4, r4, r2
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #104]
	ldrd	r4, r5, [sp, #112]
	adcs	r4, r4, r2
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #112]
	adcs	r10, r10, r2
	adc	r11, r11, r12
	strd	r10, r11, [sp, #120]
	ldr	r2, [sp, #160]
	add	r1, sp, #0x60
	add	r0, sp, #32
	bl	fe_mul
	add	r2, sp, #0x80
	add	r1, sp, #0
	add	r0, sp, #0
	bl	fe_mul
	add	r1, sp, #0x80
	add	r0, sp, #0x60
	bl	fe_sq
	ldr	r1, [sp, #160]
	add	r0, sp, #0x80
	bl	fe_sq
	# Add-Sub
	#  Add
	ldrd	r4, r5, [sp, #32]
	ldrd	r6, r7, [sp]
	adds	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [sp, #64]
	#  Sub
	subs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp]
	#  Add
	ldrd	r4, r5, [sp, #40]
	ldrd	r6, r7, [sp, #8]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [sp, #72]
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #8]
	#  Add
	ldrd	r4, r5, [sp, #48]
	ldrd	r6, r7, [sp, #16]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	mov	r3, #0
	adcs	r9, r5, r7
	adc	r3, r3, #0
	strd	r8, r9, [sp, #80]
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	mov	r12, #0
	sbcs	r11, r5, r7
	adc	r12, r12, #0
	strd	r10, r11, [sp, #16]
	#  Add
	ldrd	r4, r5, [sp, #56]
	ldrd	r6, r7, [sp, #24]
	adds	r3, r3, #-1
	adcs	r8, r4, r6
	adc	r9, r5, r7
	#  Sub
	adds	r12, r12, #-1
	sbcs	r10, r4, r6
	sbc	r11, r5, r7
	mov	r3, #-19
	asr	r2, r9, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Sub modulus (if overflow)
	ldrd	r4, r5, [sp, #64]
	subs	r4, r4, r3
	sbcs	r5, r5, r2
	strd	r4, r5, [sp, #64]
	ldrd	r4, r5, [sp, #72]
	sbcs	r4, r4, r2
	sbcs	r5, r5, r2
	strd	r4, r5, [sp, #72]
	ldrd	r4, r5, [sp, #80]
	sbcs	r4, r4, r2
	sbcs	r5, r5, r2
	strd	r4, r5, [sp, #80]
	sbcs	r8, r8, r2
	sbc	r9, r9, r12
	strd	r8, r9, [sp, #88]
	mov	r3, #-19
	asr	r2, r11, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Add modulus (if underflow)
	ldrd	r4, r5, [sp]
	adds	r4, r4, r3
	adcs	r5, r5, r2
	strd	r4, r5, [sp]
	ldrd	r4, r5, [sp, #8]
	adcs	r4, r4, r2
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #8]
	ldrd	r4, r5, [sp, #16]
	adcs	r4, r4, r2
	adcs	r5, r5, r2
	strd	r4, r5, [sp, #16]
	adcs	r10, r10, r2
	adc	r11, r11, r12
	strd	r10, r11, [sp, #24]
	add	r2, sp, #0x60
	add	r1, sp, #0x80
	ldr	r0, [sp, #160]
	bl	fe_mul
	# Sub
	ldrd	r4, r5, [sp, #128]
	ldrd	r6, r7, [sp, #136]
	ldrd	r8, r9, [sp, #96]
	ldrd	r10, r11, [sp, #104]
	subs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	sbcs	r11, r7, r11
	strd	r8, r9, [sp, #128]
	strd	r10, r11, [sp, #136]
	ldrd	r4, r5, [sp, #144]
	ldrd	r6, r7, [sp, #152]
	ldrd	r8, r9, [sp, #112]
	ldrd	r10, r11, [sp, #120]
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	sbc	r11, r7, r11
	mov	r3, #-19
	asr	r2, r11, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Add modulus (if underflow)
	ldrd	r4, r5, [sp, #128]
	ldrd	r6, r7, [sp, #136]
	adds	r4, r4, r3
	adcs	r5, r5, r2
	adcs	r6, r6, r2
	adcs	r7, r7, r2
	adcs	r8, r8, r2
	adcs	r9, r9, r2
	adcs	r10, r10, r2
	adc	r11, r11, r12
	strd	r4, r5, [sp, #128]
	strd	r6, r7, [sp, #136]
	strd	r8, r9, [sp, #144]
	strd	r10, r11, [sp, #152]
	add	r1, sp, #0
	add	r0, sp, #0
	bl	fe_sq
	# Multiply by 121666
	ldrd	r4, r5, [sp, #128]
	ldrd	r6, r7, [sp, #136]
	ldrd	r8, r9, [sp, #144]
	ldrd	r10, r11, [sp, #152]
	movw	r12, #0xdb42
	movt	r12, #1
	umull	r4, r2, r4, r12
	umull	r5, r3, r5, r12
	adds	r5, r5, r2
	adc	r2, r3, #0
	umull	r6, r3, r6, r12
	adds	r6, r6, r2
	adc	r2, r3, #0
	umull	r7, r3, r7, r12
	adds	r7, r7, r2
	adc	r2, r3, #0
	umull	r8, r3, r8, r12
	adds	r8, r8, r2
	adc	r2, r3, #0
	umull	r9, r3, r9, r12
	adds	r9, r9, r2
	adc	r2, r3, #0
	umull	r10, r3, r10, r12
	adds	r10, r10, r2
	adc	r2, r3, #0
	umull	r11, r3, r11, r12
	adds	r11, r11, r2
	adc	r2, r3, #0
	mov	r12, #19
	lsl	r2, r2, #1
	orr	r2, r2, r11, lsr #31
	mul	r2, r2, r12
	and	r11, r11, #0x7fffffff
	adds	r4, r4, r2
	adcs	r5, r5, #0
	adcs	r6, r6, #0
	adcs	r7, r7, #0
	adcs	r8, r8, #0
	adcs	r9, r9, #0
	adcs	r10, r10, #0
	adc	r11, r11, #0
	strd	r4, r5, [sp, #32]
	strd	r6, r7, [sp, #40]
	strd	r8, r9, [sp, #48]
	strd	r10, r11, [sp, #56]
	add	r1, sp, #0x40
	add	r0, sp, #0x40
	bl	fe_sq
	# Add
	ldrd	r4, r5, [sp, #96]
	ldrd	r6, r7, [sp, #104]
	ldrd	r8, r9, [sp, #32]
	ldrd	r10, r11, [sp, #40]
	adds	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	adcs	r11, r7, r11
	strd	r8, r9, [sp, #96]
	strd	r10, r11, [sp, #104]
	ldrd	r4, r5, [sp, #112]
	ldrd	r6, r7, [sp, #120]
	ldrd	r8, r9, [sp, #48]
	ldrd	r10, r11, [sp, #56]
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	adc	r11, r7, r11
	mov	r3, #-19
	asr	r2, r11, #31
	#   Mask the modulus
	and	r3, r2, r3
	and	r12, r2, #0x7fffffff
	#   Sub modulus (if overflow)
	ldrd	r4, r5, [sp, #96]
	ldrd	r6, r7, [sp, #104]
	subs	r4, r4, r3
	sbcs	r5, r5, r2
	sbcs	r6, r6, r2
	sbcs	r7, r7, r2
	sbcs	r8, r8, r2
	sbcs	r9, r9, r2
	sbcs	r10, r10, r2
	sbc	r11, r11, r12
	strd	r4, r5, [sp, #96]
	strd	r6, r7, [sp, #104]
	strd	r8, r9, [sp, #112]
	strd	r10, r11, [sp, #120]
	add	r2, sp, #0
	ldr	r1, [sp, #168]
	add	r0, sp, #32
	bl	fe_mul
	add	r2, sp, #0x60
	add	r1, sp, #0x80
	add	r0, sp, #0
	bl	fe_mul
	ldr	r2, [sp, #176]
	ldr	r1, [sp, #180]
	subs	r1, r1, #1
	str	r1, [sp, #180]
	bge	L_curve25519_bits
	mov	r1, #31
	str	r1, [sp, #180]
	subs	r2, r2, #4
	str	r2, [sp, #176]
	bge	L_curve25519_words
	# Invert
	add	r0, sp, #32
	add	r1, sp, #0
	bl	fe_sq
	add	r0, sp, #0x40
	add	r1, sp, #32
	bl	fe_sq
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	add	r0, sp, #0x40
	add	r1, sp, #0
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #32
	add	r1, sp, #32
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #0x60
	add	r1, sp, #32
	bl	fe_sq
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	add	r2, sp, #0x60
	bl	fe_mul
	add	r0, sp, #0x60
	add	r1, sp, #0x40
	bl	fe_sq
	mov	r4, #4
L_curve25519_inv_1:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_1
	add	r0, sp, #0x40
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #0x60
	add	r1, sp, #0x40
	bl	fe_sq
	mov	r4, #9
L_curve25519_inv_2:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_2
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #0x80
	add	r1, sp, #0x60
	bl	fe_sq
	mov	r4, #19
L_curve25519_inv_3:
	add	r0, sp, #0x80
	add	r1, sp, #0x80
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_3
	add	r0, sp, #0x60
	add	r1, sp, #0x80
	add	r2, sp, #0x60
	bl	fe_mul
	mov	r4, #10
L_curve25519_inv_4:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_4
	add	r0, sp, #0x40
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #0x60
	add	r1, sp, #0x40
	bl	fe_sq
	mov	r4, #49
L_curve25519_inv_5:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_5
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	add	r0, sp, #0x80
	add	r1, sp, #0x60
	bl	fe_sq
	mov	r4, #0x63
L_curve25519_inv_6:
	add	r0, sp, #0x80
	add	r1, sp, #0x80
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_6
	add	r0, sp, #0x60
	add	r1, sp, #0x80
	add	r2, sp, #0x60
	bl	fe_mul
	mov	r4, #50
L_curve25519_inv_7:
	add	r0, sp, #0x60
	add	r1, sp, #0x60
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_7
	add	r0, sp, #0x40
	add	r1, sp, #0x60
	add	r2, sp, #0x40
	bl	fe_mul
	mov	r4, #5
L_curve25519_inv_8:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_curve25519_inv_8
	add	r0, sp, #0
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	add	r2, sp, #0
	ldr	r1, [sp, #160]
	ldr	r0, [sp, #160]
	bl	fe_mul
	mov	r0, #0
	add	sp, sp, #0xbc
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	curve25519,.-curve25519
	.text
	.align	2
	.globl	fe_pow22523
	.type	fe_pow22523, %function
fe_pow22523:
	push	{r4, lr}
	sub	sp, sp, #0x68
	# pow22523
	str	r0, [sp, #96]
	str	r1, [sp, #100]
	mov	r0, sp
	ldr	r1, [sp, #100]
	bl	fe_sq
	add	r0, sp, #32
	mov	r1, sp
	bl	fe_sq
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	add	r0, sp, #32
	ldr	r1, [sp, #100]
	add	r2, sp, #32
	bl	fe_mul
	mov	r0, sp
	mov	r1, sp
	add	r2, sp, #32
	bl	fe_mul
	mov	r0, sp
	mov	r1, sp
	bl	fe_sq
	mov	r0, sp
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	add	r0, sp, #32
	mov	r1, sp
	bl	fe_sq
	mov	r4, #4
L_fe_pow22523_1:
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_1
	mov	r0, sp
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	add	r0, sp, #32
	mov	r1, sp
	bl	fe_sq
	mov	r4, #9
L_fe_pow22523_2:
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_2
	add	r0, sp, #32
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	add	r0, sp, #0x40
	add	r1, sp, #32
	bl	fe_sq
	mov	r4, #19
L_fe_pow22523_3:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_3
	add	r0, sp, #32
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	mov	r4, #10
L_fe_pow22523_4:
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_4
	mov	r0, sp
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	add	r0, sp, #32
	mov	r1, sp
	bl	fe_sq
	mov	r4, #49
L_fe_pow22523_5:
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_5
	add	r0, sp, #32
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	add	r0, sp, #0x40
	add	r1, sp, #32
	bl	fe_sq
	mov	r4, #0x63
L_fe_pow22523_6:
	add	r0, sp, #0x40
	add	r1, sp, #0x40
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_6
	add	r0, sp, #32
	add	r1, sp, #0x40
	add	r2, sp, #32
	bl	fe_mul
	mov	r4, #50
L_fe_pow22523_7:
	add	r0, sp, #32
	add	r1, sp, #32
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_7
	mov	r0, sp
	add	r1, sp, #32
	mov	r2, sp
	bl	fe_mul
	mov	r4, #2
L_fe_pow22523_8:
	mov	r0, sp
	mov	r1, sp
	bl	fe_sq
	sub	r4, r4, #1
	cmp	r4, #0
	bne	L_fe_pow22523_8
	ldr	r0, [sp, #96]
	mov	r1, sp
	ldr	r2, [sp, #100]
	bl	fe_mul
	ldr	r1, [sp, #100]
	ldr	r0, [sp, #96]
	add	sp, sp, #0x68
	pop	{r4, pc}
	.size	fe_pow22523,.-fe_pow22523
	.text
	.align	2
	.globl	fe_ge_to_p2
	.type	fe_ge_to_p2, %function
fe_ge_to_p2:
	push	{lr}
	sub	sp, sp, #16
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r2, [sp, #28]
	ldr	r1, [sp, #12]
	ldr	r0, [sp]
	bl	fe_mul
	ldr	r2, [sp, #24]
	ldr	r1, [sp, #20]
	ldr	r0, [sp, #4]
	bl	fe_mul
	ldr	r2, [sp, #28]
	ldr	r1, [sp, #24]
	ldr	r0, [sp, #8]
	bl	fe_mul
	add	sp, sp, #16
	pop	{pc}
	.size	fe_ge_to_p2,.-fe_ge_to_p2
	.text
	.align	2
	.globl	fe_ge_to_p3
	.type	fe_ge_to_p3, %function
fe_ge_to_p3:
	push	{lr}
	sub	sp, sp, #16
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r2, [sp, #32]
	ldr	r1, [sp, #20]
	ldr	r0, [sp]
	bl	fe_mul
	ldr	r2, [sp, #28]
	ldr	r1, [sp, #24]
	ldr	r0, [sp, #4]
	bl	fe_mul
	ldr	r2, [sp, #32]
	ldr	r1, [sp, #28]
	ldr	r0, [sp, #8]
	bl	fe_mul
	ldr	r2, [sp, #24]
	ldr	r1, [sp, #20]
	ldr	r0, [sp, #12]
	bl	fe_mul
	add	sp, sp, #16
	pop	{pc}
	.size	fe_ge_to_p3,.-fe_ge_to_p3
	.text
	.align	2
	.globl	fe_ge_dbl
	.type	fe_ge_dbl, %function
fe_ge_dbl:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #16
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r1, [sp, #52]
	ldr	r0, [sp]
	bl	fe_sq
	ldr	r1, [sp, #56]
	ldr	r0, [sp, #8]
	bl	fe_sq
	ldr	r0, [sp, #4]
	ldr	r1, [sp, #52]
	ldr	r2, [sp, #56]
	# Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	adds	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	adcs	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r1, [sp, #4]
	ldr	r0, [sp, #12]
	bl	fe_sq
	ldr	r0, [sp, #4]
	ldr	r1, [sp, #8]
	ldr	r2, [sp]
	# Add-Sub
	#  Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r2]
	ldr	r6, [r2, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	ldr	r5, [r2, #8]
	ldr	r6, [r2, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r2, #16]
	ldr	r6, [r2, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r1, #24]
	ldr	r4, [r1, #28]
	ldr	r5, [r2, #24]
	ldr	r6, [r2, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	ldr	r0, [sp]
	ldr	r1, [sp, #12]
	ldr	r2, [sp, #4]
	# Sub
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	subs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	sbcs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	adcs	r5, r5, r11
	adcs	r6, r6, r11
	adcs	r7, r7, r11
	adcs	r8, r8, r11
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r1, [sp, #60]
	ldr	r0, [sp, #12]
	bl	fe_sq2
	ldr	r0, [sp, #12]
	ldr	r1, [sp, #8]
	# Sub
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	ldr	r7, [r1]
	ldr	r8, [r1, #4]
	ldr	r9, [r1, #8]
	ldr	r10, [r1, #12]
	subs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	ldr	r7, [r1, #16]
	ldr	r8, [r1, #20]
	ldr	r9, [r1, #24]
	ldr	r10, [r1, #28]
	sbcs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	adcs	r5, r5, r11
	adcs	r6, r6, r11
	adcs	r7, r7, r11
	adcs	r8, r8, r11
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	add	sp, sp, #16
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_ge_dbl,.-fe_ge_dbl
	.text
	.align	2
	.globl	fe_ge_madd
	.type	fe_ge_madd, %function
fe_ge_madd:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #32
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r0, [sp]
	ldr	r1, [sp, #72]
	ldr	r2, [sp, #68]
	# Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	adds	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	adcs	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #4]
	ldr	r1, [sp, #72]
	ldr	r2, [sp, #68]
	# Sub
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	subs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	sbcs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	adcs	r5, r5, r11
	adcs	r6, r6, r11
	adcs	r7, r7, r11
	adcs	r8, r8, r11
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r2, [sp, #88]
	ldr	r1, [sp]
	ldr	r0, [sp, #8]
	bl	fe_mul
	ldr	r2, [sp, #92]
	ldr	r1, [sp, #4]
	ldr	r0, [sp, #4]
	bl	fe_mul
	ldr	r2, [sp, #80]
	ldr	r1, [sp, #84]
	ldr	r0, [sp, #12]
	bl	fe_mul
	ldr	r0, [sp, #4]
	ldr	r1, [sp]
	ldr	r2, [sp, #8]
	# Add-Sub
	#  Add
	ldr	r3, [r2]
	ldr	r4, [r2, #4]
	ldr	r5, [r0]
	ldr	r6, [r0, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r2, #8]
	ldr	r4, [r2, #12]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r2, #16]
	ldr	r4, [r2, #20]
	ldr	r5, [r0, #16]
	ldr	r6, [r0, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r2, #24]
	ldr	r4, [r2, #28]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	ldr	r0, [sp, #8]
	ldr	r1, [sp, #76]
	# Double
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r1, #16]
	ldr	r8, [r1, #20]
	ldr	r9, [r1, #24]
	ldr	r10, [r1, #28]
	adds	r3, r3, r3
	adcs	r4, r4, r4
	adcs	r5, r5, r5
	adcs	r6, r6, r6
	adcs	r7, r7, r7
	adcs	r8, r8, r8
	adcs	r9, r9, r9
	adc	r10, r10, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #8]
	ldr	r1, [sp, #12]
	# Add-Sub
	#  Add
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r1]
	ldr	r6, [r1, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	ldr	r5, [r1, #16]
	ldr	r6, [r1, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r0, #24]
	ldr	r4, [r0, #28]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	add	sp, sp, #32
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_ge_madd,.-fe_ge_madd
	.text
	.align	2
	.globl	fe_ge_msub
	.type	fe_ge_msub, %function
fe_ge_msub:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #32
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r0, [sp]
	ldr	r1, [sp, #72]
	ldr	r2, [sp, #68]
	# Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	adds	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	adcs	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #4]
	ldr	r1, [sp, #72]
	ldr	r2, [sp, #68]
	# Sub
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	subs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	sbcs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	adcs	r5, r5, r11
	adcs	r6, r6, r11
	adcs	r7, r7, r11
	adcs	r8, r8, r11
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r2, [sp, #92]
	ldr	r1, [sp]
	ldr	r0, [sp, #8]
	bl	fe_mul
	ldr	r2, [sp, #88]
	ldr	r1, [sp, #4]
	ldr	r0, [sp, #4]
	bl	fe_mul
	ldr	r2, [sp, #80]
	ldr	r1, [sp, #84]
	ldr	r0, [sp, #12]
	bl	fe_mul
	ldr	r0, [sp, #4]
	ldr	r1, [sp]
	ldr	r2, [sp, #8]
	# Add-Sub
	#  Add
	ldr	r3, [r2]
	ldr	r4, [r2, #4]
	ldr	r5, [r0]
	ldr	r6, [r0, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r2, #8]
	ldr	r4, [r2, #12]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r2, #16]
	ldr	r4, [r2, #20]
	ldr	r5, [r0, #16]
	ldr	r6, [r0, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r2, #24]
	ldr	r4, [r2, #28]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	ldr	r0, [sp, #8]
	ldr	r1, [sp, #76]
	# Double
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r1, #16]
	ldr	r8, [r1, #20]
	ldr	r9, [r1, #24]
	ldr	r10, [r1, #28]
	adds	r3, r3, r3
	adcs	r4, r4, r4
	adcs	r5, r5, r5
	adcs	r6, r6, r6
	adcs	r7, r7, r7
	adcs	r8, r8, r8
	adcs	r9, r9, r9
	adc	r10, r10, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #12]
	ldr	r1, [sp, #8]
	# Add-Sub
	#  Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r0]
	ldr	r6, [r0, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r0, #16]
	ldr	r6, [r0, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r1, #24]
	ldr	r4, [r1, #28]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	add	sp, sp, #32
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_ge_msub,.-fe_ge_msub
	.text
	.align	2
	.globl	fe_ge_add
	.type	fe_ge_add, %function
fe_ge_add:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #0x60
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r0, [sp]
	ldr	r1, [sp, #136]
	ldr	r2, [sp, #132]
	# Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	adds	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	adcs	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #4]
	ldr	r1, [sp, #136]
	ldr	r2, [sp, #132]
	# Sub
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	subs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	sbcs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	adcs	r5, r5, r11
	adcs	r6, r6, r11
	adcs	r7, r7, r11
	adcs	r8, r8, r11
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r2, [sp, #156]
	ldr	r1, [sp]
	ldr	r0, [sp, #8]
	bl	fe_mul
	ldr	r2, [sp, #160]
	ldr	r1, [sp, #4]
	ldr	r0, [sp, #4]
	bl	fe_mul
	ldr	r2, [sp, #144]
	ldr	r1, [sp, #152]
	ldr	r0, [sp, #12]
	bl	fe_mul
	ldr	r2, [sp, #148]
	ldr	r1, [sp, #140]
	ldr	r0, [sp]
	bl	fe_mul
	add	r0, sp, #16
	ldr	r1, [sp]
	# Double
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r1, #16]
	ldr	r8, [r1, #20]
	ldr	r9, [r1, #24]
	ldr	r10, [r1, #28]
	adds	r3, r3, r3
	adcs	r4, r4, r4
	adcs	r5, r5, r5
	adcs	r6, r6, r6
	adcs	r7, r7, r7
	adcs	r8, r8, r8
	adcs	r9, r9, r9
	adc	r10, r10, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #4]
	ldr	r1, [sp]
	ldr	r2, [sp, #8]
	# Add-Sub
	#  Add
	ldr	r3, [r2]
	ldr	r4, [r2, #4]
	ldr	r5, [r0]
	ldr	r6, [r0, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r2, #8]
	ldr	r4, [r2, #12]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r2, #16]
	ldr	r4, [r2, #20]
	ldr	r5, [r0, #16]
	ldr	r6, [r0, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r2, #24]
	ldr	r4, [r2, #28]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	ldr	r0, [sp, #8]
	ldr	r1, [sp, #12]
	add	r2, sp, #16
	# Add-Sub
	#  Add
	ldr	r3, [r2]
	ldr	r4, [r2, #4]
	ldr	r5, [r1]
	ldr	r6, [r1, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r2, #8]
	ldr	r4, [r2, #12]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r2, #16]
	ldr	r4, [r2, #20]
	ldr	r5, [r1, #16]
	ldr	r6, [r1, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r2, #24]
	ldr	r4, [r2, #28]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	add	sp, sp, #0x60
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_ge_add,.-fe_ge_add
	.text
	.align	2
	.globl	fe_ge_sub
	.type	fe_ge_sub, %function
fe_ge_sub:
	push	{r4, r5, r6, r7, r8, r9, r10, r11, lr}
	sub	sp, sp, #0x60
	str	r0, [sp]
	str	r1, [sp, #4]
	str	r2, [sp, #8]
	str	r3, [sp, #12]
	ldr	r0, [sp]
	ldr	r1, [sp, #136]
	ldr	r2, [sp, #132]
	# Add
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	adds	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	adcs	r7, r3, r7
	adcs	r8, r4, r8
	adcs	r9, r5, r9
	adc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #4]
	ldr	r1, [sp, #136]
	ldr	r2, [sp, #132]
	# Sub
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r2]
	ldr	r8, [r2, #4]
	ldr	r9, [r2, #8]
	ldr	r10, [r2, #12]
	subs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbcs	r10, r6, r10
	str	r7, [r0]
	str	r8, [r0, #4]
	str	r9, [r0, #8]
	str	r10, [r0, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	ldr	r5, [r1, #24]
	ldr	r6, [r1, #28]
	ldr	r7, [r2, #16]
	ldr	r8, [r2, #20]
	ldr	r9, [r2, #24]
	ldr	r10, [r2, #28]
	sbcs	r7, r3, r7
	sbcs	r8, r4, r8
	sbcs	r9, r5, r9
	sbc	r10, r6, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	adcs	r5, r5, r11
	adcs	r6, r6, r11
	adcs	r7, r7, r11
	adcs	r8, r8, r11
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r2, [sp, #160]
	ldr	r1, [sp]
	ldr	r0, [sp, #8]
	bl	fe_mul
	ldr	r2, [sp, #156]
	ldr	r1, [sp, #4]
	ldr	r0, [sp, #4]
	bl	fe_mul
	ldr	r2, [sp, #144]
	ldr	r1, [sp, #152]
	ldr	r0, [sp, #12]
	bl	fe_mul
	ldr	r2, [sp, #148]
	ldr	r1, [sp, #140]
	ldr	r0, [sp]
	bl	fe_mul
	add	r0, sp, #16
	ldr	r1, [sp]
	# Double
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	ldr	r5, [r1, #8]
	ldr	r6, [r1, #12]
	ldr	r7, [r1, #16]
	ldr	r8, [r1, #20]
	ldr	r9, [r1, #24]
	ldr	r10, [r1, #28]
	adds	r3, r3, r3
	adcs	r4, r4, r4
	adcs	r5, r5, r5
	adcs	r6, r6, r6
	adcs	r7, r7, r7
	adcs	r8, r8, r8
	adcs	r9, r9, r9
	adc	r10, r10, r10
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	sbcs	r5, r5, r11
	sbcs	r6, r6, r11
	sbcs	r7, r7, r11
	sbcs	r8, r8, r11
	sbcs	r9, r9, r11
	sbc	r10, r10, lr
	str	r3, [r0]
	str	r4, [r0, #4]
	str	r5, [r0, #8]
	str	r6, [r0, #12]
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	str	r9, [r0, #24]
	str	r10, [r0, #28]
	ldr	r0, [sp, #4]
	ldr	r1, [sp]
	ldr	r2, [sp, #8]
	# Add-Sub
	#  Add
	ldr	r3, [r2]
	ldr	r4, [r2, #4]
	ldr	r5, [r0]
	ldr	r6, [r0, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r2, #8]
	ldr	r4, [r2, #12]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r2, #16]
	ldr	r4, [r2, #20]
	ldr	r5, [r0, #16]
	ldr	r6, [r0, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r2, #24]
	ldr	r4, [r2, #28]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	ldr	r0, [sp, #12]
	ldr	r1, [sp, #8]
	add	r2, sp, #16
	# Add-Sub
	#  Add
	ldr	r3, [r2]
	ldr	r4, [r2, #4]
	ldr	r5, [r0]
	ldr	r6, [r0, #4]
	adds	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0]
	str	r8, [r0, #4]
	#  Sub
	subs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1]
	str	r10, [r1, #4]
	#  Add
	ldr	r3, [r2, #8]
	ldr	r4, [r2, #12]
	ldr	r5, [r0, #8]
	ldr	r6, [r0, #12]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #8]
	str	r8, [r0, #12]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #8]
	str	r10, [r1, #12]
	#  Add
	ldr	r3, [r2, #16]
	ldr	r4, [r2, #20]
	ldr	r5, [r0, #16]
	ldr	r6, [r0, #20]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	mov	r12, #0
	adcs	r8, r4, r6
	adc	r12, r12, #0
	str	r7, [r0, #16]
	str	r8, [r0, #20]
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	mov	lr, #0
	sbcs	r10, r4, r6
	adc	lr, lr, #0
	str	r9, [r1, #16]
	str	r10, [r1, #20]
	#  Add
	ldr	r3, [r2, #24]
	ldr	r4, [r2, #28]
	ldr	r5, [r0, #24]
	ldr	r6, [r0, #28]
	adds	r12, r12, #-1
	adcs	r7, r3, r5
	adc	r8, r4, r6
	#  Sub
	adds	lr, lr, #-1
	sbcs	r9, r3, r5
	sbc	r10, r4, r6
	mov	r12, #-19
	asr	r11, r8, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Sub modulus (if overflow)
	ldr	r3, [r0]
	ldr	r4, [r0, #4]
	subs	r3, r3, r12
	sbcs	r4, r4, r11
	str	r3, [r0]
	str	r4, [r0, #4]
	ldr	r3, [r0, #8]
	ldr	r4, [r0, #12]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #8]
	str	r4, [r0, #12]
	ldr	r3, [r0, #16]
	ldr	r4, [r0, #20]
	sbcs	r3, r3, r11
	sbcs	r4, r4, r11
	str	r3, [r0, #16]
	str	r4, [r0, #20]
	sbcs	r7, r7, r11
	sbc	r8, r8, lr
	str	r7, [r0, #24]
	str	r8, [r0, #28]
	mov	r12, #-19
	asr	r11, r10, #31
	#   Mask the modulus
	and	r12, r11, r12
	and	lr, r11, #0x7fffffff
	#   Add modulus (if underflow)
	ldr	r3, [r1]
	ldr	r4, [r1, #4]
	adds	r3, r3, r12
	adcs	r4, r4, r11
	str	r3, [r1]
	str	r4, [r1, #4]
	ldr	r3, [r1, #8]
	ldr	r4, [r1, #12]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #8]
	str	r4, [r1, #12]
	ldr	r3, [r1, #16]
	ldr	r4, [r1, #20]
	adcs	r3, r3, r11
	adcs	r4, r4, r11
	str	r3, [r1, #16]
	str	r4, [r1, #20]
	adcs	r9, r9, r11
	adc	r10, r10, lr
	str	r9, [r1, #24]
	str	r10, [r1, #28]
	add	sp, sp, #0x60
	pop	{r4, r5, r6, r7, r8, r9, r10, r11, pc}
	.size	fe_ge_sub,.-fe_ge_sub
#endif /* !__aarch64__ */
#endif /* WOLFSSL_ARMASM */
