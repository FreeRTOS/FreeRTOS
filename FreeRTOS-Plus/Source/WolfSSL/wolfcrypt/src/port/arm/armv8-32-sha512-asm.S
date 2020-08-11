/* armv8-32-sha512-asm
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
 *   ruby ./sha2/sha512.rb arm32 ../wolfssl/wolfcrypt/src/port/arm/armv8-32-sha512-asm.S
 */

#ifdef WOLFSSL_ARMASM
#ifndef __aarch64__
#ifdef WOLFSSL_ARMASM_NO_NEON
	.text
	.type	L_SHA512_transform_len_k, %object
	.size	L_SHA512_transform_len_k, 640
	.align	3
L_SHA512_transform_len_k:
	.word	0xd728ae22
	.word	0x428a2f98
	.word	0x23ef65cd
	.word	0x71374491
	.word	0xec4d3b2f
	.word	0xb5c0fbcf
	.word	0x8189dbbc
	.word	0xe9b5dba5
	.word	0xf348b538
	.word	0x3956c25b
	.word	0xb605d019
	.word	0x59f111f1
	.word	0xaf194f9b
	.word	0x923f82a4
	.word	0xda6d8118
	.word	0xab1c5ed5
	.word	0xa3030242
	.word	0xd807aa98
	.word	0x45706fbe
	.word	0x12835b01
	.word	0x4ee4b28c
	.word	0x243185be
	.word	0xd5ffb4e2
	.word	0x550c7dc3
	.word	0xf27b896f
	.word	0x72be5d74
	.word	0x3b1696b1
	.word	0x80deb1fe
	.word	0x25c71235
	.word	0x9bdc06a7
	.word	0xcf692694
	.word	0xc19bf174
	.word	0x9ef14ad2
	.word	0xe49b69c1
	.word	0x384f25e3
	.word	0xefbe4786
	.word	0x8b8cd5b5
	.word	0xfc19dc6
	.word	0x77ac9c65
	.word	0x240ca1cc
	.word	0x592b0275
	.word	0x2de92c6f
	.word	0x6ea6e483
	.word	0x4a7484aa
	.word	0xbd41fbd4
	.word	0x5cb0a9dc
	.word	0x831153b5
	.word	0x76f988da
	.word	0xee66dfab
	.word	0x983e5152
	.word	0x2db43210
	.word	0xa831c66d
	.word	0x98fb213f
	.word	0xb00327c8
	.word	0xbeef0ee4
	.word	0xbf597fc7
	.word	0x3da88fc2
	.word	0xc6e00bf3
	.word	0x930aa725
	.word	0xd5a79147
	.word	0xe003826f
	.word	0x6ca6351
	.word	0xa0e6e70
	.word	0x14292967
	.word	0x46d22ffc
	.word	0x27b70a85
	.word	0x5c26c926
	.word	0x2e1b2138
	.word	0x5ac42aed
	.word	0x4d2c6dfc
	.word	0x9d95b3df
	.word	0x53380d13
	.word	0x8baf63de
	.word	0x650a7354
	.word	0x3c77b2a8
	.word	0x766a0abb
	.word	0x47edaee6
	.word	0x81c2c92e
	.word	0x1482353b
	.word	0x92722c85
	.word	0x4cf10364
	.word	0xa2bfe8a1
	.word	0xbc423001
	.word	0xa81a664b
	.word	0xd0f89791
	.word	0xc24b8b70
	.word	0x654be30
	.word	0xc76c51a3
	.word	0xd6ef5218
	.word	0xd192e819
	.word	0x5565a910
	.word	0xd6990624
	.word	0x5771202a
	.word	0xf40e3585
	.word	0x32bbd1b8
	.word	0x106aa070
	.word	0xb8d2d0c8
	.word	0x19a4c116
	.word	0x5141ab53
	.word	0x1e376c08
	.word	0xdf8eeb99
	.word	0x2748774c
	.word	0xe19b48a8
	.word	0x34b0bcb5
	.word	0xc5c95a63
	.word	0x391c0cb3
	.word	0xe3418acb
	.word	0x4ed8aa4a
	.word	0x7763e373
	.word	0x5b9cca4f
	.word	0xd6b2b8a3
	.word	0x682e6ff3
	.word	0x5defb2fc
	.word	0x748f82ee
	.word	0x43172f60
	.word	0x78a5636f
	.word	0xa1f0ab72
	.word	0x84c87814
	.word	0x1a6439ec
	.word	0x8cc70208
	.word	0x23631e28
	.word	0x90befffa
	.word	0xde82bde9
	.word	0xa4506ceb
	.word	0xb2c67915
	.word	0xbef9a3f7
	.word	0xe372532b
	.word	0xc67178f2
	.word	0xea26619c
	.word	0xca273ece
	.word	0x21c0c207
	.word	0xd186b8c7
	.word	0xcde0eb1e
	.word	0xeada7dd6
	.word	0xee6ed178
	.word	0xf57d4f7f
	.word	0x72176fba
	.word	0x6f067aa
	.word	0xa2c898a6
	.word	0xa637dc5
	.word	0xbef90dae
	.word	0x113f9804
	.word	0x131c471b
	.word	0x1b710b35
	.word	0x23047d84
	.word	0x28db77f5
	.word	0x40c72493
	.word	0x32caab7b
	.word	0x15c9bebc
	.word	0x3c9ebe0a
	.word	0x9c100d4c
	.word	0x431d67c4
	.word	0xcb3e42b6
	.word	0x4cc5d4be
	.word	0xfc657e2a
	.word	0x597f299c
	.word	0x3ad6faec
	.word	0x5fcb6fab
	.word	0x4a475817
	.word	0x6c44198c
	.text
	.align	2
	.globl	Transform_Sha512_Len
	.type	Transform_Sha512_Len, %function
Transform_Sha512_Len:
	push	{r4, r5, r6, r7, r8, r9, r10, lr}
	sub	sp, sp, #0xc0
	adr	r3, L_SHA512_transform_len_k
	# Copy digest to add in at end
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [r0, #16]
	ldrd	r8, r9, [r0, #24]
	str	r12, [sp, #128]
	str	lr, [sp, #132]
	strd	r4, r5, [sp, #136]
	strd	r6, r7, [sp, #144]
	strd	r8, r9, [sp, #152]
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r4, r5, [r0, #40]
	ldrd	r6, r7, [r0, #48]
	ldrd	r8, r9, [r0, #56]
	str	r12, [sp, #160]
	str	lr, [sp, #164]
	strd	r4, r5, [sp, #168]
	strd	r6, r7, [sp, #176]
	strd	r8, r9, [sp, #184]
	# Start of loop processing a block
L_sha512_len_neon_begin:
	# Load, Reverse and Store W
	ldr	r12, [r1]
	ldr	lr, [r1, #4]
	ldrd	r4, r5, [r1, #8]
	ldrd	r6, r7, [r1, #16]
	ldrd	r8, r9, [r1, #24]
	rev	r12, r12
	rev	lr, lr
	rev	r4, r4
	rev	r5, r5
	rev	r6, r6
	rev	r7, r7
	rev	r8, r8
	rev	r9, r9
	str	lr, [sp]
	str	r12, [sp, #4]
	str	r5, [sp, #8]
	str	r4, [sp, #12]
	str	r7, [sp, #16]
	str	r6, [sp, #20]
	str	r9, [sp, #24]
	str	r8, [sp, #28]
	ldr	r12, [r1, #32]
	ldr	lr, [r1, #36]
	ldrd	r4, r5, [r1, #40]
	ldrd	r6, r7, [r1, #48]
	ldrd	r8, r9, [r1, #56]
	rev	r12, r12
	rev	lr, lr
	rev	r4, r4
	rev	r5, r5
	rev	r6, r6
	rev	r7, r7
	rev	r8, r8
	rev	r9, r9
	str	lr, [sp, #32]
	str	r12, [sp, #36]
	str	r5, [sp, #40]
	str	r4, [sp, #44]
	str	r7, [sp, #48]
	str	r6, [sp, #52]
	str	r9, [sp, #56]
	str	r8, [sp, #60]
	ldr	r12, [r1, #64]
	ldr	lr, [r1, #68]
	ldrd	r4, r5, [r1, #72]
	ldrd	r6, r7, [r1, #80]
	ldrd	r8, r9, [r1, #88]
	rev	r12, r12
	rev	lr, lr
	rev	r4, r4
	rev	r5, r5
	rev	r6, r6
	rev	r7, r7
	rev	r8, r8
	rev	r9, r9
	str	lr, [sp, #64]
	str	r12, [sp, #68]
	str	r5, [sp, #72]
	str	r4, [sp, #76]
	str	r7, [sp, #80]
	str	r6, [sp, #84]
	str	r9, [sp, #88]
	str	r8, [sp, #92]
	ldr	r12, [r1, #96]
	ldr	lr, [r1, #100]
	ldrd	r4, r5, [r1, #104]
	ldrd	r6, r7, [r1, #112]
	ldrd	r8, r9, [r1, #120]
	rev	r12, r12
	rev	lr, lr
	rev	r4, r4
	rev	r5, r5
	rev	r6, r6
	rev	r7, r7
	rev	r8, r8
	rev	r9, r9
	str	lr, [sp, #96]
	str	r12, [sp, #100]
	str	r5, [sp, #104]
	str	r4, [sp, #108]
	str	r7, [sp, #112]
	str	r6, [sp, #116]
	str	r9, [sp, #120]
	str	r8, [sp, #124]
	# Pre-calc: b ^ c
	ldrd	r8, r9, [r0, #8]
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r8, r8, r12
	eor	r9, r9, lr
	mov	r10, #4
	# Start of 16 rounds
L_sha512_len_neon_start:
	# Round 0
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r4, r5, [r0, #40]
	ldrd	r6, r7, [r0, #48]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r6, r7, [sp]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	strd	r6, r7, [r0, #24]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0]
	ldrd	r4, r5, [r0, #8]
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #56]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #56]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[0]
	ldr	r12, [sp, #112]
	ldr	lr, [sp, #116]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp]
	ldr	lr, [sp, #4]
	ldrd	r6, r7, [sp, #72]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp]
	str	lr, [sp, #4]
	ldr	r12, [sp, #8]
	ldr	lr, [sp, #12]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp]
	ldr	lr, [sp, #4]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp]
	str	lr, [sp, #4]
	# Round 1
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r4, r5, [r0, #32]
	ldrd	r6, r7, [r0, #40]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r6, r7, [sp, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #8]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	strd	r6, r7, [r0, #16]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #56]
	ldrd	r4, r5, [r0]
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #48]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #48]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[1]
	ldr	r12, [sp, #120]
	ldr	lr, [sp, #124]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #8]
	ldr	lr, [sp, #12]
	ldrd	r6, r7, [sp, #80]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #8]
	str	lr, [sp, #12]
	ldr	r12, [sp, #16]
	ldr	lr, [sp, #20]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #8]
	ldr	lr, [sp, #12]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #8]
	str	lr, [sp, #12]
	# Round 2
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [r0, #32]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r6, r7, [sp, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #16]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	strd	r6, r7, [r0, #8]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #48]
	ldrd	r4, r5, [r0, #56]
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #40]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #40]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[2]
	ldr	r12, [sp]
	ldr	lr, [sp, #4]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #16]
	ldr	lr, [sp, #20]
	ldrd	r6, r7, [sp, #88]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #16]
	str	lr, [sp, #20]
	ldr	r12, [sp, #24]
	ldr	lr, [sp, #28]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #16]
	ldr	lr, [sp, #20]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #16]
	str	lr, [sp, #20]
	# Round 3
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [r0, #24]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r6, r7, [sp, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #24]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	strd	r6, r7, [r0]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #40]
	ldrd	r4, r5, [r0, #48]
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #32]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #32]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[3]
	ldr	r12, [sp, #8]
	ldr	lr, [sp, #12]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #24]
	ldr	lr, [sp, #28]
	ldrd	r6, r7, [sp, #96]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #24]
	str	lr, [sp, #28]
	ldr	r12, [sp, #32]
	ldr	lr, [sp, #36]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #24]
	ldr	lr, [sp, #28]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #24]
	str	lr, [sp, #28]
	# Round 4
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [r0, #16]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r6, r7, [sp, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #32]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	strd	r6, r7, [r0, #56]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #32]
	ldrd	r4, r5, [r0, #40]
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #24]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #24]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[4]
	ldr	r12, [sp, #16]
	ldr	lr, [sp, #20]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #32]
	ldr	lr, [sp, #36]
	ldrd	r6, r7, [sp, #104]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #32]
	str	lr, [sp, #36]
	ldr	r12, [sp, #40]
	ldr	lr, [sp, #44]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #32]
	ldr	lr, [sp, #36]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #32]
	str	lr, [sp, #36]
	# Round 5
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r4, r5, [r0]
	ldrd	r6, r7, [r0, #8]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r6, r7, [sp, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #40]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	strd	r6, r7, [r0, #48]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #24]
	ldrd	r4, r5, [r0, #32]
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #16]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #16]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[5]
	ldr	r12, [sp, #24]
	ldr	lr, [sp, #28]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #40]
	ldr	lr, [sp, #44]
	ldrd	r6, r7, [sp, #112]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #40]
	str	lr, [sp, #44]
	ldr	r12, [sp, #48]
	ldr	lr, [sp, #52]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #40]
	ldr	lr, [sp, #44]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #40]
	str	lr, [sp, #44]
	# Round 6
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r4, r5, [r0, #56]
	ldrd	r6, r7, [r0]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r6, r7, [sp, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #48]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	strd	r6, r7, [r0, #40]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #16]
	ldrd	r4, r5, [r0, #24]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #8]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #8]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[6]
	ldr	r12, [sp, #32]
	ldr	lr, [sp, #36]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #48]
	ldr	lr, [sp, #52]
	ldrd	r6, r7, [sp, #120]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #48]
	str	lr, [sp, #52]
	ldr	r12, [sp, #56]
	ldr	lr, [sp, #60]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #48]
	ldr	lr, [sp, #52]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #48]
	str	lr, [sp, #52]
	# Round 7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r4, r5, [r0, #48]
	ldrd	r6, r7, [r0, #56]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r6, r7, [sp, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #56]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	strd	r6, r7, [r0, #32]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #8]
	ldrd	r4, r5, [r0, #16]
	str	r12, [r0]
	str	lr, [r0, #4]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[7]
	ldr	r12, [sp, #40]
	ldr	lr, [sp, #44]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #56]
	ldr	lr, [sp, #60]
	ldrd	r6, r7, [sp]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #56]
	str	lr, [sp, #60]
	ldr	r12, [sp, #64]
	ldr	lr, [sp, #68]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #56]
	ldr	lr, [sp, #60]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #56]
	str	lr, [sp, #60]
	# Round 8
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r4, r5, [r0, #40]
	ldrd	r6, r7, [r0, #48]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r6, r7, [sp, #64]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #64]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	strd	r6, r7, [r0, #24]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0]
	ldrd	r4, r5, [r0, #8]
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #56]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #56]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[8]
	ldr	r12, [sp, #48]
	ldr	lr, [sp, #52]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #64]
	ldr	lr, [sp, #68]
	ldrd	r6, r7, [sp, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #64]
	str	lr, [sp, #68]
	ldr	r12, [sp, #72]
	ldr	lr, [sp, #76]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #64]
	ldr	lr, [sp, #68]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #64]
	str	lr, [sp, #68]
	# Round 9
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r4, r5, [r0, #32]
	ldrd	r6, r7, [r0, #40]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r6, r7, [sp, #72]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #72]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	strd	r6, r7, [r0, #16]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #56]
	ldrd	r4, r5, [r0]
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #48]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #48]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[9]
	ldr	r12, [sp, #56]
	ldr	lr, [sp, #60]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #72]
	ldr	lr, [sp, #76]
	ldrd	r6, r7, [sp, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #72]
	str	lr, [sp, #76]
	ldr	r12, [sp, #80]
	ldr	lr, [sp, #84]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #72]
	ldr	lr, [sp, #76]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #72]
	str	lr, [sp, #76]
	# Round 10
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [r0, #32]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r6, r7, [sp, #80]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #80]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	strd	r6, r7, [r0, #8]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #48]
	ldrd	r4, r5, [r0, #56]
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #40]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #40]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[10]
	ldr	r12, [sp, #64]
	ldr	lr, [sp, #68]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #80]
	ldr	lr, [sp, #84]
	ldrd	r6, r7, [sp, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #80]
	str	lr, [sp, #84]
	ldr	r12, [sp, #88]
	ldr	lr, [sp, #92]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #80]
	ldr	lr, [sp, #84]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #80]
	str	lr, [sp, #84]
	# Round 11
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [r0, #24]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r6, r7, [sp, #88]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #88]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	strd	r6, r7, [r0]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #40]
	ldrd	r4, r5, [r0, #48]
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #32]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #32]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[11]
	ldr	r12, [sp, #72]
	ldr	lr, [sp, #76]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #88]
	ldr	lr, [sp, #92]
	ldrd	r6, r7, [sp, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #88]
	str	lr, [sp, #92]
	ldr	r12, [sp, #96]
	ldr	lr, [sp, #100]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #88]
	ldr	lr, [sp, #92]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #88]
	str	lr, [sp, #92]
	# Round 12
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [r0, #16]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r6, r7, [sp, #96]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #96]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	strd	r6, r7, [r0, #56]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #32]
	ldrd	r4, r5, [r0, #40]
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #24]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #24]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[12]
	ldr	r12, [sp, #80]
	ldr	lr, [sp, #84]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #96]
	ldr	lr, [sp, #100]
	ldrd	r6, r7, [sp, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #96]
	str	lr, [sp, #100]
	ldr	r12, [sp, #104]
	ldr	lr, [sp, #108]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #96]
	ldr	lr, [sp, #100]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #96]
	str	lr, [sp, #100]
	# Round 13
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r4, r5, [r0]
	ldrd	r6, r7, [r0, #8]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r6, r7, [sp, #104]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #104]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	strd	r6, r7, [r0, #48]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #24]
	ldrd	r4, r5, [r0, #32]
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #16]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #16]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[13]
	ldr	r12, [sp, #88]
	ldr	lr, [sp, #92]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #104]
	ldr	lr, [sp, #108]
	ldrd	r6, r7, [sp, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #104]
	str	lr, [sp, #108]
	ldr	r12, [sp, #112]
	ldr	lr, [sp, #116]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #104]
	ldr	lr, [sp, #108]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #104]
	str	lr, [sp, #108]
	# Round 14
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r4, r5, [r0, #56]
	ldrd	r6, r7, [r0]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r6, r7, [sp, #112]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #112]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	strd	r6, r7, [r0, #40]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #16]
	ldrd	r4, r5, [r0, #24]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #8]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #8]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[14]
	ldr	r12, [sp, #96]
	ldr	lr, [sp, #100]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #112]
	ldr	lr, [sp, #116]
	ldrd	r6, r7, [sp, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #112]
	str	lr, [sp, #116]
	ldr	r12, [sp, #120]
	ldr	lr, [sp, #124]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #112]
	ldr	lr, [sp, #116]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #112]
	str	lr, [sp, #116]
	# Round 15
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r4, r5, [r0, #48]
	ldrd	r6, r7, [r0, #56]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r6, r7, [sp, #120]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #120]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	strd	r6, r7, [r0, #32]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #8]
	ldrd	r4, r5, [r0, #16]
	str	r12, [r0]
	str	lr, [r0, #4]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0]
	mov	r8, r6
	mov	r9, r7
	# Calc new W[15]
	ldr	r12, [sp, #104]
	ldr	lr, [sp, #108]
	lsrs	r4, r12, #19
	lsrs	r5, lr, #19
	orr	r5, r5, r12, lsl #13
	orr	r4, r4, lr, lsl #13
	lsls	r6, r12, #3
	lsls	r7, lr, #3
	orr	r7, r7, r12, lsr #29
	orr	r6, r6, lr, lsr #29
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #6
	lsrs	r7, lr, #6
	orr	r6, r6, lr, lsl #26
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #120]
	ldr	lr, [sp, #124]
	ldrd	r6, r7, [sp, #64]
	adds	r12, r12, r4
	adc	lr, lr, r5
	adds	r12, r12, r6
	adc	lr, lr, r7
	str	r12, [sp, #120]
	str	lr, [sp, #124]
	ldr	r12, [sp]
	ldr	lr, [sp, #4]
	lsrs	r4, r12, #1
	lsrs	r5, lr, #1
	orr	r5, r5, r12, lsl #31
	orr	r4, r4, lr, lsl #31
	lsrs	r6, r12, #8
	lsrs	r7, lr, #8
	orr	r7, r7, r12, lsl #24
	orr	r6, r6, lr, lsl #24
	eor	r5, r5, r7
	eor	r4, r4, r6
	lsrs	r6, r12, #7
	lsrs	r7, lr, #7
	orr	r6, r6, lr, lsl #25
	eor	r5, r5, r7
	eor	r4, r4, r6
	ldr	r12, [sp, #120]
	ldr	lr, [sp, #124]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [sp, #120]
	str	lr, [sp, #124]
	add	r3, r3, #0x80
	subs	r10, r10, #1
	bne	L_sha512_len_neon_start
	# Round 0
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r4, r5, [r0, #40]
	ldrd	r6, r7, [r0, #48]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r6, r7, [sp]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	strd	r6, r7, [r0, #24]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0]
	ldrd	r4, r5, [r0, #8]
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #56]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #56]
	mov	r8, r6
	mov	r9, r7
	# Round 1
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r4, r5, [r0, #32]
	ldrd	r6, r7, [r0, #40]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r6, r7, [sp, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #8]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	strd	r6, r7, [r0, #16]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #56]
	ldrd	r4, r5, [r0]
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #48]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #48]
	mov	r8, r6
	mov	r9, r7
	# Round 2
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [r0, #32]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r6, r7, [sp, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #16]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	strd	r6, r7, [r0, #8]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #48]
	ldrd	r4, r5, [r0, #56]
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #40]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #40]
	mov	r8, r6
	mov	r9, r7
	# Round 3
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [r0, #24]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r6, r7, [sp, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #24]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	strd	r6, r7, [r0]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #40]
	ldrd	r4, r5, [r0, #48]
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #32]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #32]
	mov	r8, r6
	mov	r9, r7
	# Round 4
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [r0, #16]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r6, r7, [sp, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #32]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	strd	r6, r7, [r0, #56]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #32]
	ldrd	r4, r5, [r0, #40]
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #24]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #24]
	mov	r8, r6
	mov	r9, r7
	# Round 5
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r4, r5, [r0]
	ldrd	r6, r7, [r0, #8]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r6, r7, [sp, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #40]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	strd	r6, r7, [r0, #48]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #24]
	ldrd	r4, r5, [r0, #32]
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #16]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #16]
	mov	r8, r6
	mov	r9, r7
	# Round 6
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r4, r5, [r0, #56]
	ldrd	r6, r7, [r0]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r6, r7, [sp, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #48]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	strd	r6, r7, [r0, #40]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #16]
	ldrd	r4, r5, [r0, #24]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #8]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #8]
	mov	r8, r6
	mov	r9, r7
	# Round 7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r4, r5, [r0, #48]
	ldrd	r6, r7, [r0, #56]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r6, r7, [sp, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #56]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	strd	r6, r7, [r0, #32]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #8]
	ldrd	r4, r5, [r0, #16]
	str	r12, [r0]
	str	lr, [r0, #4]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0]
	mov	r8, r6
	mov	r9, r7
	# Round 8
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r4, r5, [r0, #40]
	ldrd	r6, r7, [r0, #48]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r6, r7, [sp, #64]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #64]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #24]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	strd	r6, r7, [r0, #24]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0]
	ldrd	r4, r5, [r0, #8]
	str	r12, [r0, #56]
	str	lr, [r0, #60]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #56]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #56]
	mov	r8, r6
	mov	r9, r7
	# Round 9
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r4, r5, [r0, #32]
	ldrd	r6, r7, [r0, #40]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r6, r7, [sp, #72]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #72]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #16]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	strd	r6, r7, [r0, #16]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #56]
	ldrd	r4, r5, [r0]
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #48]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #48]
	mov	r8, r6
	mov	r9, r7
	# Round 10
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [r0, #32]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r6, r7, [sp, #80]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #80]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #8]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	strd	r6, r7, [r0, #8]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #48]
	ldrd	r4, r5, [r0, #56]
	str	r12, [r0, #40]
	str	lr, [r0, #44]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #40]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #40]
	mov	r8, r6
	mov	r9, r7
	# Round 11
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r4, r5, [r0, #16]
	ldrd	r6, r7, [r0, #24]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r6, r7, [sp, #88]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #88]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	strd	r6, r7, [r0]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #40]
	ldrd	r4, r5, [r0, #48]
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #32]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #32]
	mov	r8, r6
	mov	r9, r7
	# Round 12
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [r0, #16]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	ldrd	r6, r7, [sp, #96]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #96]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #56]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	strd	r6, r7, [r0, #56]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #32]
	ldrd	r4, r5, [r0, #40]
	str	r12, [r0, #24]
	str	lr, [r0, #28]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #24]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #24]
	mov	r8, r6
	mov	r9, r7
	# Round 13
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	ldr	r12, [r0, #56]
	ldr	lr, [r0, #60]
	ldrd	r4, r5, [r0]
	ldrd	r6, r7, [r0, #8]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r6, r7, [sp, #104]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #104]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #48]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #24]
	ldr	lr, [r0, #28]
	strd	r6, r7, [r0, #48]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #24]
	ldrd	r4, r5, [r0, #32]
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #16]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #16]
	mov	r8, r6
	mov	r9, r7
	# Round 14
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r4, r5, [r0, #56]
	ldrd	r6, r7, [r0]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	ldrd	r6, r7, [sp, #112]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #112]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #40]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	strd	r6, r7, [r0, #40]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #16]
	ldrd	r4, r5, [r0, #24]
	str	r12, [r0, #8]
	str	lr, [r0, #12]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0, #8]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0, #8]
	mov	r8, r6
	mov	r9, r7
	# Round 15
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	lsrs	r4, r12, #14
	lsrs	r5, lr, #14
	orr	r5, r5, r12, lsl #18
	orr	r4, r4, lr, lsl #18
	lsrs	r6, r12, #18
	lsrs	r7, lr, #18
	orr	r7, r7, r12, lsl #14
	orr	r6, r6, lr, lsl #14
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #23
	lsls	r7, lr, #23
	orr	r7, r7, r12, lsr #9
	orr	r6, r6, lr, lsr #9
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	ldr	r12, [r0, #40]
	ldr	lr, [r0, #44]
	ldrd	r4, r5, [r0, #48]
	ldrd	r6, r7, [r0, #56]
	eor	r4, r4, r6
	eor	r5, r5, r7
	and	r4, r4, r12
	and	r5, r5, lr
	eor	r4, r4, r6
	eor	r5, r5, r7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r6, r7, [sp, #120]
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r4, r5, [r3, #120]
	adds	r12, r12, r6
	adc	lr, lr, r7
	ldrd	r6, r7, [r0, #32]
	adds	r12, r12, r4
	adc	lr, lr, r5
	str	r12, [r0]
	str	lr, [r0, #4]
	adds	r6, r6, r12
	adc	r7, r7, lr
	ldr	r12, [r0, #8]
	ldr	lr, [r0, #12]
	strd	r6, r7, [r0, #32]
	lsrs	r4, r12, #28
	lsrs	r5, lr, #28
	orr	r5, r5, r12, lsl #4
	orr	r4, r4, lr, lsl #4
	lsls	r6, r12, #30
	lsls	r7, lr, #30
	orr	r7, r7, r12, lsr #2
	orr	r6, r6, lr, lsr #2
	eor	r4, r4, r6
	eor	r5, r5, r7
	lsls	r6, r12, #25
	lsls	r7, lr, #25
	orr	r7, r7, r12, lsr #7
	orr	r6, r6, lr, lsr #7
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	eor	r4, r4, r6
	eor	r5, r5, r7
	adds	r12, r12, r4
	adc	lr, lr, r5
	ldrd	r6, r7, [r0, #8]
	ldrd	r4, r5, [r0, #16]
	str	r12, [r0]
	str	lr, [r0, #4]
	eor	r6, r6, r4
	eor	r7, r7, r5
	and	r8, r8, r6
	and	r9, r9, r7
	eor	r8, r8, r4
	eor	r9, r9, r5
	ldrd	r4, r5, [r0]
	adds	r4, r4, r8
	adc	r5, r5, r9
	strd	r4, r5, [r0]
	mov	r8, r6
	mov	r9, r7
	# Add in digest from start
	ldr	r12, [r0]
	ldr	lr, [r0, #4]
	ldrd	r4, r5, [r0, #8]
	ldrd	r6, r7, [sp, #128]
	ldrd	r8, r9, [sp, #136]
	adds	r12, r12, r6
	adc	lr, lr, r7
	adds	r4, r4, r8
	adc	r5, r5, r9
	str	r12, [r0]
	str	lr, [r0, #4]
	strd	r4, r5, [r0, #8]
	str	r12, [sp, #128]
	str	lr, [sp, #132]
	strd	r4, r5, [sp, #136]
	ldr	r12, [r0, #16]
	ldr	lr, [r0, #20]
	ldrd	r4, r5, [r0, #24]
	ldrd	r6, r7, [sp, #144]
	ldrd	r8, r9, [sp, #152]
	adds	r12, r12, r6
	adc	lr, lr, r7
	adds	r4, r4, r8
	adc	r5, r5, r9
	str	r12, [r0, #16]
	str	lr, [r0, #20]
	strd	r4, r5, [r0, #24]
	str	r12, [sp, #144]
	str	lr, [sp, #148]
	strd	r4, r5, [sp, #152]
	ldr	r12, [r0, #32]
	ldr	lr, [r0, #36]
	ldrd	r4, r5, [r0, #40]
	ldrd	r6, r7, [sp, #160]
	ldrd	r8, r9, [sp, #168]
	adds	r12, r12, r6
	adc	lr, lr, r7
	adds	r4, r4, r8
	adc	r5, r5, r9
	str	r12, [r0, #32]
	str	lr, [r0, #36]
	strd	r4, r5, [r0, #40]
	str	r12, [sp, #160]
	str	lr, [sp, #164]
	strd	r4, r5, [sp, #168]
	ldr	r12, [r0, #48]
	ldr	lr, [r0, #52]
	ldrd	r4, r5, [r0, #56]
	ldrd	r6, r7, [sp, #176]
	ldrd	r8, r9, [sp, #184]
	adds	r12, r12, r6
	adc	lr, lr, r7
	adds	r4, r4, r8
	adc	r5, r5, r9
	str	r12, [r0, #48]
	str	lr, [r0, #52]
	strd	r4, r5, [r0, #56]
	str	r12, [sp, #176]
	str	lr, [sp, #180]
	strd	r4, r5, [sp, #184]
	subs	r2, r2, #0x80
	sub	r3, r3, #0x200
	add	r1, r1, #0x80
	bne	L_sha512_len_neon_begin
	eor	r0, r0, r0
	add	sp, sp, #0xc0
	pop	{r4, r5, r6, r7, r8, r9, r10, pc}
	.size	Transform_Sha512_Len,.-Transform_Sha512_Len
#endif /* WOLFSSL_ARMASM_NO_NEON */
#ifndef WOLFSSL_ARMASM_NO_NEON
	.text
	.type	L_SHA512_transform_neon_len_k, %object
	.size	L_SHA512_transform_neon_len_k, 640
	.align	3
L_SHA512_transform_neon_len_k:
	.word	0xd728ae22
	.word	0x428a2f98
	.word	0x23ef65cd
	.word	0x71374491
	.word	0xec4d3b2f
	.word	0xb5c0fbcf
	.word	0x8189dbbc
	.word	0xe9b5dba5
	.word	0xf348b538
	.word	0x3956c25b
	.word	0xb605d019
	.word	0x59f111f1
	.word	0xaf194f9b
	.word	0x923f82a4
	.word	0xda6d8118
	.word	0xab1c5ed5
	.word	0xa3030242
	.word	0xd807aa98
	.word	0x45706fbe
	.word	0x12835b01
	.word	0x4ee4b28c
	.word	0x243185be
	.word	0xd5ffb4e2
	.word	0x550c7dc3
	.word	0xf27b896f
	.word	0x72be5d74
	.word	0x3b1696b1
	.word	0x80deb1fe
	.word	0x25c71235
	.word	0x9bdc06a7
	.word	0xcf692694
	.word	0xc19bf174
	.word	0x9ef14ad2
	.word	0xe49b69c1
	.word	0x384f25e3
	.word	0xefbe4786
	.word	0x8b8cd5b5
	.word	0xfc19dc6
	.word	0x77ac9c65
	.word	0x240ca1cc
	.word	0x592b0275
	.word	0x2de92c6f
	.word	0x6ea6e483
	.word	0x4a7484aa
	.word	0xbd41fbd4
	.word	0x5cb0a9dc
	.word	0x831153b5
	.word	0x76f988da
	.word	0xee66dfab
	.word	0x983e5152
	.word	0x2db43210
	.word	0xa831c66d
	.word	0x98fb213f
	.word	0xb00327c8
	.word	0xbeef0ee4
	.word	0xbf597fc7
	.word	0x3da88fc2
	.word	0xc6e00bf3
	.word	0x930aa725
	.word	0xd5a79147
	.word	0xe003826f
	.word	0x6ca6351
	.word	0xa0e6e70
	.word	0x14292967
	.word	0x46d22ffc
	.word	0x27b70a85
	.word	0x5c26c926
	.word	0x2e1b2138
	.word	0x5ac42aed
	.word	0x4d2c6dfc
	.word	0x9d95b3df
	.word	0x53380d13
	.word	0x8baf63de
	.word	0x650a7354
	.word	0x3c77b2a8
	.word	0x766a0abb
	.word	0x47edaee6
	.word	0x81c2c92e
	.word	0x1482353b
	.word	0x92722c85
	.word	0x4cf10364
	.word	0xa2bfe8a1
	.word	0xbc423001
	.word	0xa81a664b
	.word	0xd0f89791
	.word	0xc24b8b70
	.word	0x654be30
	.word	0xc76c51a3
	.word	0xd6ef5218
	.word	0xd192e819
	.word	0x5565a910
	.word	0xd6990624
	.word	0x5771202a
	.word	0xf40e3585
	.word	0x32bbd1b8
	.word	0x106aa070
	.word	0xb8d2d0c8
	.word	0x19a4c116
	.word	0x5141ab53
	.word	0x1e376c08
	.word	0xdf8eeb99
	.word	0x2748774c
	.word	0xe19b48a8
	.word	0x34b0bcb5
	.word	0xc5c95a63
	.word	0x391c0cb3
	.word	0xe3418acb
	.word	0x4ed8aa4a
	.word	0x7763e373
	.word	0x5b9cca4f
	.word	0xd6b2b8a3
	.word	0x682e6ff3
	.word	0x5defb2fc
	.word	0x748f82ee
	.word	0x43172f60
	.word	0x78a5636f
	.word	0xa1f0ab72
	.word	0x84c87814
	.word	0x1a6439ec
	.word	0x8cc70208
	.word	0x23631e28
	.word	0x90befffa
	.word	0xde82bde9
	.word	0xa4506ceb
	.word	0xb2c67915
	.word	0xbef9a3f7
	.word	0xe372532b
	.word	0xc67178f2
	.word	0xea26619c
	.word	0xca273ece
	.word	0x21c0c207
	.word	0xd186b8c7
	.word	0xcde0eb1e
	.word	0xeada7dd6
	.word	0xee6ed178
	.word	0xf57d4f7f
	.word	0x72176fba
	.word	0x6f067aa
	.word	0xa2c898a6
	.word	0xa637dc5
	.word	0xbef90dae
	.word	0x113f9804
	.word	0x131c471b
	.word	0x1b710b35
	.word	0x23047d84
	.word	0x28db77f5
	.word	0x40c72493
	.word	0x32caab7b
	.word	0x15c9bebc
	.word	0x3c9ebe0a
	.word	0x9c100d4c
	.word	0x431d67c4
	.word	0xcb3e42b6
	.word	0x4cc5d4be
	.word	0xfc657e2a
	.word	0x597f299c
	.word	0x3ad6faec
	.word	0x5fcb6fab
	.word	0x4a475817
	.word	0x6c44198c
	.text
	.align	2
	.globl	Transform_Sha512_Len
	.type	Transform_Sha512_Len, %function
Transform_Sha512_Len:
	vpush	{d8-d15}
	# Load digest into working vars
	vldm.64	r0, {d0-d7}
	# Start of loop processing a block
L_sha512_len_neon_begin:
	# Load W
	vldm.64	r1!, {d16-d31}
	vrev64.8	q8, q8
	vrev64.8	q9, q9
	vrev64.8	q10, q10
	vrev64.8	q11, q11
	vrev64.8	q12, q12
	vrev64.8	q13, q13
	vrev64.8	q14, q14
	vrev64.8	q15, q15
	adr	r3, L_SHA512_transform_neon_len_k
	mov	r12, #4
	# Start of 16 rounds
L_sha512_len_neon_start:
	# Round 0
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d4, #50
	vsri.u64	d8, d4, #14
	vshl.u64	d9, d0, #36
	vsri.u64	d9, d0, #28
	vshl.u64	d10, d4, #46
	vsri.u64	d10, d4, #18
	vshl.u64	d11, d0, #30
	vsri.u64	d11, d0, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d4, #23
	vsri.u64	d10, d4, #41
	vshl.u64	d11, d0, #25
	vsri.u64	d11, d0, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d7, d8
	vadd.i64	d12, d16
	vmov	d8, d4
	veor	d10, d1, d2
	vadd.i64	d7, d12
	vbsl	d8, d5, d6
	vbsl	d10, d0, d2
	vadd.i64	d7, d8
	vadd.i64	d10, d9
	vadd.i64	d3, d7
	vadd.i64	d7, d10
	# Round 1
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d3, #50
	vsri.u64	d8, d3, #14
	vshl.u64	d9, d7, #36
	vsri.u64	d9, d7, #28
	vshl.u64	d10, d3, #46
	vsri.u64	d10, d3, #18
	vshl.u64	d11, d7, #30
	vsri.u64	d11, d7, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d3, #23
	vsri.u64	d10, d3, #41
	vshl.u64	d11, d7, #25
	vsri.u64	d11, d7, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d6, d8
	vadd.i64	d12, d17
	vmov	d8, d3
	veor	d10, d0, d1
	vadd.i64	d6, d12
	vbsl	d8, d4, d5
	vbsl	d10, d7, d1
	vadd.i64	d6, d8
	vadd.i64	d10, d9
	vadd.i64	d2, d6
	vadd.i64	d6, d10
	# Calc new W[0]-W[1]
	vext.8	q6, q8, q9, #8
	vshl.u64	q4, q15, #45
	vsri.u64	q4, q15, #19
	vshl.u64	q5, q15, #3
	vsri.u64	q5, q15, #61
	veor	q5, q4
	vshr.u64	q4, q15, #6
	veor	q5, q4
	vadd.i64	q8, q5
	vext.8	q7, q12, q13, #8
	vadd.i64	q8, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q8, q5
	# Round 2
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d2, #50
	vsri.u64	d8, d2, #14
	vshl.u64	d9, d6, #36
	vsri.u64	d9, d6, #28
	vshl.u64	d10, d2, #46
	vsri.u64	d10, d2, #18
	vshl.u64	d11, d6, #30
	vsri.u64	d11, d6, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d2, #23
	vsri.u64	d10, d2, #41
	vshl.u64	d11, d6, #25
	vsri.u64	d11, d6, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d5, d8
	vadd.i64	d12, d18
	vmov	d8, d2
	veor	d10, d7, d0
	vadd.i64	d5, d12
	vbsl	d8, d3, d4
	vbsl	d10, d6, d0
	vadd.i64	d5, d8
	vadd.i64	d10, d9
	vadd.i64	d1, d5
	vadd.i64	d5, d10
	# Round 3
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d1, #50
	vsri.u64	d8, d1, #14
	vshl.u64	d9, d5, #36
	vsri.u64	d9, d5, #28
	vshl.u64	d10, d1, #46
	vsri.u64	d10, d1, #18
	vshl.u64	d11, d5, #30
	vsri.u64	d11, d5, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d1, #23
	vsri.u64	d10, d1, #41
	vshl.u64	d11, d5, #25
	vsri.u64	d11, d5, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d4, d8
	vadd.i64	d12, d19
	vmov	d8, d1
	veor	d10, d6, d7
	vadd.i64	d4, d12
	vbsl	d8, d2, d3
	vbsl	d10, d5, d7
	vadd.i64	d4, d8
	vadd.i64	d10, d9
	vadd.i64	d0, d4
	vadd.i64	d4, d10
	# Calc new W[2]-W[3]
	vext.8	q6, q9, q10, #8
	vshl.u64	q4, q8, #45
	vsri.u64	q4, q8, #19
	vshl.u64	q5, q8, #3
	vsri.u64	q5, q8, #61
	veor	q5, q4
	vshr.u64	q4, q8, #6
	veor	q5, q4
	vadd.i64	q9, q5
	vext.8	q7, q13, q14, #8
	vadd.i64	q9, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q9, q5
	# Round 4
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d0, #50
	vsri.u64	d8, d0, #14
	vshl.u64	d9, d4, #36
	vsri.u64	d9, d4, #28
	vshl.u64	d10, d0, #46
	vsri.u64	d10, d0, #18
	vshl.u64	d11, d4, #30
	vsri.u64	d11, d4, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d0, #23
	vsri.u64	d10, d0, #41
	vshl.u64	d11, d4, #25
	vsri.u64	d11, d4, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d3, d8
	vadd.i64	d12, d20
	vmov	d8, d0
	veor	d10, d5, d6
	vadd.i64	d3, d12
	vbsl	d8, d1, d2
	vbsl	d10, d4, d6
	vadd.i64	d3, d8
	vadd.i64	d10, d9
	vadd.i64	d7, d3
	vadd.i64	d3, d10
	# Round 5
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d7, #50
	vsri.u64	d8, d7, #14
	vshl.u64	d9, d3, #36
	vsri.u64	d9, d3, #28
	vshl.u64	d10, d7, #46
	vsri.u64	d10, d7, #18
	vshl.u64	d11, d3, #30
	vsri.u64	d11, d3, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d7, #23
	vsri.u64	d10, d7, #41
	vshl.u64	d11, d3, #25
	vsri.u64	d11, d3, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d2, d8
	vadd.i64	d12, d21
	vmov	d8, d7
	veor	d10, d4, d5
	vadd.i64	d2, d12
	vbsl	d8, d0, d1
	vbsl	d10, d3, d5
	vadd.i64	d2, d8
	vadd.i64	d10, d9
	vadd.i64	d6, d2
	vadd.i64	d2, d10
	# Calc new W[4]-W[5]
	vext.8	q6, q10, q11, #8
	vshl.u64	q4, q9, #45
	vsri.u64	q4, q9, #19
	vshl.u64	q5, q9, #3
	vsri.u64	q5, q9, #61
	veor	q5, q4
	vshr.u64	q4, q9, #6
	veor	q5, q4
	vadd.i64	q10, q5
	vext.8	q7, q14, q15, #8
	vadd.i64	q10, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q10, q5
	# Round 6
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d6, #50
	vsri.u64	d8, d6, #14
	vshl.u64	d9, d2, #36
	vsri.u64	d9, d2, #28
	vshl.u64	d10, d6, #46
	vsri.u64	d10, d6, #18
	vshl.u64	d11, d2, #30
	vsri.u64	d11, d2, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d6, #23
	vsri.u64	d10, d6, #41
	vshl.u64	d11, d2, #25
	vsri.u64	d11, d2, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d1, d8
	vadd.i64	d12, d22
	vmov	d8, d6
	veor	d10, d3, d4
	vadd.i64	d1, d12
	vbsl	d8, d7, d0
	vbsl	d10, d2, d4
	vadd.i64	d1, d8
	vadd.i64	d10, d9
	vadd.i64	d5, d1
	vadd.i64	d1, d10
	# Round 7
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d5, #50
	vsri.u64	d8, d5, #14
	vshl.u64	d9, d1, #36
	vsri.u64	d9, d1, #28
	vshl.u64	d10, d5, #46
	vsri.u64	d10, d5, #18
	vshl.u64	d11, d1, #30
	vsri.u64	d11, d1, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d5, #23
	vsri.u64	d10, d5, #41
	vshl.u64	d11, d1, #25
	vsri.u64	d11, d1, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d0, d8
	vadd.i64	d12, d23
	vmov	d8, d5
	veor	d10, d2, d3
	vadd.i64	d0, d12
	vbsl	d8, d6, d7
	vbsl	d10, d1, d3
	vadd.i64	d0, d8
	vadd.i64	d10, d9
	vadd.i64	d4, d0
	vadd.i64	d0, d10
	# Calc new W[6]-W[7]
	vext.8	q6, q11, q12, #8
	vshl.u64	q4, q10, #45
	vsri.u64	q4, q10, #19
	vshl.u64	q5, q10, #3
	vsri.u64	q5, q10, #61
	veor	q5, q4
	vshr.u64	q4, q10, #6
	veor	q5, q4
	vadd.i64	q11, q5
	vext.8	q7, q15, q8, #8
	vadd.i64	q11, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q11, q5
	# Round 8
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d4, #50
	vsri.u64	d8, d4, #14
	vshl.u64	d9, d0, #36
	vsri.u64	d9, d0, #28
	vshl.u64	d10, d4, #46
	vsri.u64	d10, d4, #18
	vshl.u64	d11, d0, #30
	vsri.u64	d11, d0, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d4, #23
	vsri.u64	d10, d4, #41
	vshl.u64	d11, d0, #25
	vsri.u64	d11, d0, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d7, d8
	vadd.i64	d12, d24
	vmov	d8, d4
	veor	d10, d1, d2
	vadd.i64	d7, d12
	vbsl	d8, d5, d6
	vbsl	d10, d0, d2
	vadd.i64	d7, d8
	vadd.i64	d10, d9
	vadd.i64	d3, d7
	vadd.i64	d7, d10
	# Round 9
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d3, #50
	vsri.u64	d8, d3, #14
	vshl.u64	d9, d7, #36
	vsri.u64	d9, d7, #28
	vshl.u64	d10, d3, #46
	vsri.u64	d10, d3, #18
	vshl.u64	d11, d7, #30
	vsri.u64	d11, d7, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d3, #23
	vsri.u64	d10, d3, #41
	vshl.u64	d11, d7, #25
	vsri.u64	d11, d7, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d6, d8
	vadd.i64	d12, d25
	vmov	d8, d3
	veor	d10, d0, d1
	vadd.i64	d6, d12
	vbsl	d8, d4, d5
	vbsl	d10, d7, d1
	vadd.i64	d6, d8
	vadd.i64	d10, d9
	vadd.i64	d2, d6
	vadd.i64	d6, d10
	# Calc new W[8]-W[9]
	vext.8	q6, q12, q13, #8
	vshl.u64	q4, q11, #45
	vsri.u64	q4, q11, #19
	vshl.u64	q5, q11, #3
	vsri.u64	q5, q11, #61
	veor	q5, q4
	vshr.u64	q4, q11, #6
	veor	q5, q4
	vadd.i64	q12, q5
	vext.8	q7, q8, q9, #8
	vadd.i64	q12, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q12, q5
	# Round 10
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d2, #50
	vsri.u64	d8, d2, #14
	vshl.u64	d9, d6, #36
	vsri.u64	d9, d6, #28
	vshl.u64	d10, d2, #46
	vsri.u64	d10, d2, #18
	vshl.u64	d11, d6, #30
	vsri.u64	d11, d6, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d2, #23
	vsri.u64	d10, d2, #41
	vshl.u64	d11, d6, #25
	vsri.u64	d11, d6, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d5, d8
	vadd.i64	d12, d26
	vmov	d8, d2
	veor	d10, d7, d0
	vadd.i64	d5, d12
	vbsl	d8, d3, d4
	vbsl	d10, d6, d0
	vadd.i64	d5, d8
	vadd.i64	d10, d9
	vadd.i64	d1, d5
	vadd.i64	d5, d10
	# Round 11
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d1, #50
	vsri.u64	d8, d1, #14
	vshl.u64	d9, d5, #36
	vsri.u64	d9, d5, #28
	vshl.u64	d10, d1, #46
	vsri.u64	d10, d1, #18
	vshl.u64	d11, d5, #30
	vsri.u64	d11, d5, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d1, #23
	vsri.u64	d10, d1, #41
	vshl.u64	d11, d5, #25
	vsri.u64	d11, d5, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d4, d8
	vadd.i64	d12, d27
	vmov	d8, d1
	veor	d10, d6, d7
	vadd.i64	d4, d12
	vbsl	d8, d2, d3
	vbsl	d10, d5, d7
	vadd.i64	d4, d8
	vadd.i64	d10, d9
	vadd.i64	d0, d4
	vadd.i64	d4, d10
	# Calc new W[10]-W[11]
	vext.8	q6, q13, q14, #8
	vshl.u64	q4, q12, #45
	vsri.u64	q4, q12, #19
	vshl.u64	q5, q12, #3
	vsri.u64	q5, q12, #61
	veor	q5, q4
	vshr.u64	q4, q12, #6
	veor	q5, q4
	vadd.i64	q13, q5
	vext.8	q7, q9, q10, #8
	vadd.i64	q13, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q13, q5
	# Round 12
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d0, #50
	vsri.u64	d8, d0, #14
	vshl.u64	d9, d4, #36
	vsri.u64	d9, d4, #28
	vshl.u64	d10, d0, #46
	vsri.u64	d10, d0, #18
	vshl.u64	d11, d4, #30
	vsri.u64	d11, d4, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d0, #23
	vsri.u64	d10, d0, #41
	vshl.u64	d11, d4, #25
	vsri.u64	d11, d4, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d3, d8
	vadd.i64	d12, d28
	vmov	d8, d0
	veor	d10, d5, d6
	vadd.i64	d3, d12
	vbsl	d8, d1, d2
	vbsl	d10, d4, d6
	vadd.i64	d3, d8
	vadd.i64	d10, d9
	vadd.i64	d7, d3
	vadd.i64	d3, d10
	# Round 13
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d7, #50
	vsri.u64	d8, d7, #14
	vshl.u64	d9, d3, #36
	vsri.u64	d9, d3, #28
	vshl.u64	d10, d7, #46
	vsri.u64	d10, d7, #18
	vshl.u64	d11, d3, #30
	vsri.u64	d11, d3, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d7, #23
	vsri.u64	d10, d7, #41
	vshl.u64	d11, d3, #25
	vsri.u64	d11, d3, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d2, d8
	vadd.i64	d12, d29
	vmov	d8, d7
	veor	d10, d4, d5
	vadd.i64	d2, d12
	vbsl	d8, d0, d1
	vbsl	d10, d3, d5
	vadd.i64	d2, d8
	vadd.i64	d10, d9
	vadd.i64	d6, d2
	vadd.i64	d2, d10
	# Calc new W[12]-W[13]
	vext.8	q6, q14, q15, #8
	vshl.u64	q4, q13, #45
	vsri.u64	q4, q13, #19
	vshl.u64	q5, q13, #3
	vsri.u64	q5, q13, #61
	veor	q5, q4
	vshr.u64	q4, q13, #6
	veor	q5, q4
	vadd.i64	q14, q5
	vext.8	q7, q10, q11, #8
	vadd.i64	q14, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q14, q5
	# Round 14
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d6, #50
	vsri.u64	d8, d6, #14
	vshl.u64	d9, d2, #36
	vsri.u64	d9, d2, #28
	vshl.u64	d10, d6, #46
	vsri.u64	d10, d6, #18
	vshl.u64	d11, d2, #30
	vsri.u64	d11, d2, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d6, #23
	vsri.u64	d10, d6, #41
	vshl.u64	d11, d2, #25
	vsri.u64	d11, d2, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d1, d8
	vadd.i64	d12, d30
	vmov	d8, d6
	veor	d10, d3, d4
	vadd.i64	d1, d12
	vbsl	d8, d7, d0
	vbsl	d10, d2, d4
	vadd.i64	d1, d8
	vadd.i64	d10, d9
	vadd.i64	d5, d1
	vadd.i64	d1, d10
	# Round 15
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d5, #50
	vsri.u64	d8, d5, #14
	vshl.u64	d9, d1, #36
	vsri.u64	d9, d1, #28
	vshl.u64	d10, d5, #46
	vsri.u64	d10, d5, #18
	vshl.u64	d11, d1, #30
	vsri.u64	d11, d1, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d5, #23
	vsri.u64	d10, d5, #41
	vshl.u64	d11, d1, #25
	vsri.u64	d11, d1, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d0, d8
	vadd.i64	d12, d31
	vmov	d8, d5
	veor	d10, d2, d3
	vadd.i64	d0, d12
	vbsl	d8, d6, d7
	vbsl	d10, d1, d3
	vadd.i64	d0, d8
	vadd.i64	d10, d9
	vadd.i64	d4, d0
	vadd.i64	d0, d10
	# Calc new W[14]-W[15]
	vext.8	q6, q15, q8, #8
	vshl.u64	q4, q14, #45
	vsri.u64	q4, q14, #19
	vshl.u64	q5, q14, #3
	vsri.u64	q5, q14, #61
	veor	q5, q4
	vshr.u64	q4, q14, #6
	veor	q5, q4
	vadd.i64	q15, q5
	vext.8	q7, q11, q12, #8
	vadd.i64	q15, q7
	vshl.u64	q4, q6, #63
	vsri.u64	q4, q6, #1
	vshl.u64	q5, q6, #56
	vsri.u64	q5, q6, #8
	veor	q5, q4
	vshr.u64	q6, #7
	veor	q5, q6
	vadd.i64	q15, q5
	subs	r12, r12, #1
	bne	L_sha512_len_neon_start
	# Round 0
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d4, #50
	vsri.u64	d8, d4, #14
	vshl.u64	d9, d0, #36
	vsri.u64	d9, d0, #28
	vshl.u64	d10, d4, #46
	vsri.u64	d10, d4, #18
	vshl.u64	d11, d0, #30
	vsri.u64	d11, d0, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d4, #23
	vsri.u64	d10, d4, #41
	vshl.u64	d11, d0, #25
	vsri.u64	d11, d0, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d7, d8
	vadd.i64	d12, d16
	vmov	d8, d4
	veor	d10, d1, d2
	vadd.i64	d7, d12
	vbsl	d8, d5, d6
	vbsl	d10, d0, d2
	vadd.i64	d7, d8
	vadd.i64	d10, d9
	vadd.i64	d3, d7
	vadd.i64	d7, d10
	# Round 1
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d3, #50
	vsri.u64	d8, d3, #14
	vshl.u64	d9, d7, #36
	vsri.u64	d9, d7, #28
	vshl.u64	d10, d3, #46
	vsri.u64	d10, d3, #18
	vshl.u64	d11, d7, #30
	vsri.u64	d11, d7, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d3, #23
	vsri.u64	d10, d3, #41
	vshl.u64	d11, d7, #25
	vsri.u64	d11, d7, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d6, d8
	vadd.i64	d12, d17
	vmov	d8, d3
	veor	d10, d0, d1
	vadd.i64	d6, d12
	vbsl	d8, d4, d5
	vbsl	d10, d7, d1
	vadd.i64	d6, d8
	vadd.i64	d10, d9
	vadd.i64	d2, d6
	vadd.i64	d6, d10
	# Round 2
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d2, #50
	vsri.u64	d8, d2, #14
	vshl.u64	d9, d6, #36
	vsri.u64	d9, d6, #28
	vshl.u64	d10, d2, #46
	vsri.u64	d10, d2, #18
	vshl.u64	d11, d6, #30
	vsri.u64	d11, d6, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d2, #23
	vsri.u64	d10, d2, #41
	vshl.u64	d11, d6, #25
	vsri.u64	d11, d6, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d5, d8
	vadd.i64	d12, d18
	vmov	d8, d2
	veor	d10, d7, d0
	vadd.i64	d5, d12
	vbsl	d8, d3, d4
	vbsl	d10, d6, d0
	vadd.i64	d5, d8
	vadd.i64	d10, d9
	vadd.i64	d1, d5
	vadd.i64	d5, d10
	# Round 3
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d1, #50
	vsri.u64	d8, d1, #14
	vshl.u64	d9, d5, #36
	vsri.u64	d9, d5, #28
	vshl.u64	d10, d1, #46
	vsri.u64	d10, d1, #18
	vshl.u64	d11, d5, #30
	vsri.u64	d11, d5, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d1, #23
	vsri.u64	d10, d1, #41
	vshl.u64	d11, d5, #25
	vsri.u64	d11, d5, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d4, d8
	vadd.i64	d12, d19
	vmov	d8, d1
	veor	d10, d6, d7
	vadd.i64	d4, d12
	vbsl	d8, d2, d3
	vbsl	d10, d5, d7
	vadd.i64	d4, d8
	vadd.i64	d10, d9
	vadd.i64	d0, d4
	vadd.i64	d4, d10
	# Round 4
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d0, #50
	vsri.u64	d8, d0, #14
	vshl.u64	d9, d4, #36
	vsri.u64	d9, d4, #28
	vshl.u64	d10, d0, #46
	vsri.u64	d10, d0, #18
	vshl.u64	d11, d4, #30
	vsri.u64	d11, d4, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d0, #23
	vsri.u64	d10, d0, #41
	vshl.u64	d11, d4, #25
	vsri.u64	d11, d4, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d3, d8
	vadd.i64	d12, d20
	vmov	d8, d0
	veor	d10, d5, d6
	vadd.i64	d3, d12
	vbsl	d8, d1, d2
	vbsl	d10, d4, d6
	vadd.i64	d3, d8
	vadd.i64	d10, d9
	vadd.i64	d7, d3
	vadd.i64	d3, d10
	# Round 5
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d7, #50
	vsri.u64	d8, d7, #14
	vshl.u64	d9, d3, #36
	vsri.u64	d9, d3, #28
	vshl.u64	d10, d7, #46
	vsri.u64	d10, d7, #18
	vshl.u64	d11, d3, #30
	vsri.u64	d11, d3, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d7, #23
	vsri.u64	d10, d7, #41
	vshl.u64	d11, d3, #25
	vsri.u64	d11, d3, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d2, d8
	vadd.i64	d12, d21
	vmov	d8, d7
	veor	d10, d4, d5
	vadd.i64	d2, d12
	vbsl	d8, d0, d1
	vbsl	d10, d3, d5
	vadd.i64	d2, d8
	vadd.i64	d10, d9
	vadd.i64	d6, d2
	vadd.i64	d2, d10
	# Round 6
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d6, #50
	vsri.u64	d8, d6, #14
	vshl.u64	d9, d2, #36
	vsri.u64	d9, d2, #28
	vshl.u64	d10, d6, #46
	vsri.u64	d10, d6, #18
	vshl.u64	d11, d2, #30
	vsri.u64	d11, d2, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d6, #23
	vsri.u64	d10, d6, #41
	vshl.u64	d11, d2, #25
	vsri.u64	d11, d2, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d1, d8
	vadd.i64	d12, d22
	vmov	d8, d6
	veor	d10, d3, d4
	vadd.i64	d1, d12
	vbsl	d8, d7, d0
	vbsl	d10, d2, d4
	vadd.i64	d1, d8
	vadd.i64	d10, d9
	vadd.i64	d5, d1
	vadd.i64	d1, d10
	# Round 7
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d5, #50
	vsri.u64	d8, d5, #14
	vshl.u64	d9, d1, #36
	vsri.u64	d9, d1, #28
	vshl.u64	d10, d5, #46
	vsri.u64	d10, d5, #18
	vshl.u64	d11, d1, #30
	vsri.u64	d11, d1, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d5, #23
	vsri.u64	d10, d5, #41
	vshl.u64	d11, d1, #25
	vsri.u64	d11, d1, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d0, d8
	vadd.i64	d12, d23
	vmov	d8, d5
	veor	d10, d2, d3
	vadd.i64	d0, d12
	vbsl	d8, d6, d7
	vbsl	d10, d1, d3
	vadd.i64	d0, d8
	vadd.i64	d10, d9
	vadd.i64	d4, d0
	vadd.i64	d0, d10
	# Round 8
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d4, #50
	vsri.u64	d8, d4, #14
	vshl.u64	d9, d0, #36
	vsri.u64	d9, d0, #28
	vshl.u64	d10, d4, #46
	vsri.u64	d10, d4, #18
	vshl.u64	d11, d0, #30
	vsri.u64	d11, d0, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d4, #23
	vsri.u64	d10, d4, #41
	vshl.u64	d11, d0, #25
	vsri.u64	d11, d0, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d7, d8
	vadd.i64	d12, d24
	vmov	d8, d4
	veor	d10, d1, d2
	vadd.i64	d7, d12
	vbsl	d8, d5, d6
	vbsl	d10, d0, d2
	vadd.i64	d7, d8
	vadd.i64	d10, d9
	vadd.i64	d3, d7
	vadd.i64	d7, d10
	# Round 9
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d3, #50
	vsri.u64	d8, d3, #14
	vshl.u64	d9, d7, #36
	vsri.u64	d9, d7, #28
	vshl.u64	d10, d3, #46
	vsri.u64	d10, d3, #18
	vshl.u64	d11, d7, #30
	vsri.u64	d11, d7, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d3, #23
	vsri.u64	d10, d3, #41
	vshl.u64	d11, d7, #25
	vsri.u64	d11, d7, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d6, d8
	vadd.i64	d12, d25
	vmov	d8, d3
	veor	d10, d0, d1
	vadd.i64	d6, d12
	vbsl	d8, d4, d5
	vbsl	d10, d7, d1
	vadd.i64	d6, d8
	vadd.i64	d10, d9
	vadd.i64	d2, d6
	vadd.i64	d6, d10
	# Round 10
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d2, #50
	vsri.u64	d8, d2, #14
	vshl.u64	d9, d6, #36
	vsri.u64	d9, d6, #28
	vshl.u64	d10, d2, #46
	vsri.u64	d10, d2, #18
	vshl.u64	d11, d6, #30
	vsri.u64	d11, d6, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d2, #23
	vsri.u64	d10, d2, #41
	vshl.u64	d11, d6, #25
	vsri.u64	d11, d6, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d5, d8
	vadd.i64	d12, d26
	vmov	d8, d2
	veor	d10, d7, d0
	vadd.i64	d5, d12
	vbsl	d8, d3, d4
	vbsl	d10, d6, d0
	vadd.i64	d5, d8
	vadd.i64	d10, d9
	vadd.i64	d1, d5
	vadd.i64	d5, d10
	# Round 11
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d1, #50
	vsri.u64	d8, d1, #14
	vshl.u64	d9, d5, #36
	vsri.u64	d9, d5, #28
	vshl.u64	d10, d1, #46
	vsri.u64	d10, d1, #18
	vshl.u64	d11, d5, #30
	vsri.u64	d11, d5, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d1, #23
	vsri.u64	d10, d1, #41
	vshl.u64	d11, d5, #25
	vsri.u64	d11, d5, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d4, d8
	vadd.i64	d12, d27
	vmov	d8, d1
	veor	d10, d6, d7
	vadd.i64	d4, d12
	vbsl	d8, d2, d3
	vbsl	d10, d5, d7
	vadd.i64	d4, d8
	vadd.i64	d10, d9
	vadd.i64	d0, d4
	vadd.i64	d4, d10
	# Round 12
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d0, #50
	vsri.u64	d8, d0, #14
	vshl.u64	d9, d4, #36
	vsri.u64	d9, d4, #28
	vshl.u64	d10, d0, #46
	vsri.u64	d10, d0, #18
	vshl.u64	d11, d4, #30
	vsri.u64	d11, d4, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d0, #23
	vsri.u64	d10, d0, #41
	vshl.u64	d11, d4, #25
	vsri.u64	d11, d4, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d3, d8
	vadd.i64	d12, d28
	vmov	d8, d0
	veor	d10, d5, d6
	vadd.i64	d3, d12
	vbsl	d8, d1, d2
	vbsl	d10, d4, d6
	vadd.i64	d3, d8
	vadd.i64	d10, d9
	vadd.i64	d7, d3
	vadd.i64	d3, d10
	# Round 13
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d7, #50
	vsri.u64	d8, d7, #14
	vshl.u64	d9, d3, #36
	vsri.u64	d9, d3, #28
	vshl.u64	d10, d7, #46
	vsri.u64	d10, d7, #18
	vshl.u64	d11, d3, #30
	vsri.u64	d11, d3, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d7, #23
	vsri.u64	d10, d7, #41
	vshl.u64	d11, d3, #25
	vsri.u64	d11, d3, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d2, d8
	vadd.i64	d12, d29
	vmov	d8, d7
	veor	d10, d4, d5
	vadd.i64	d2, d12
	vbsl	d8, d0, d1
	vbsl	d10, d3, d5
	vadd.i64	d2, d8
	vadd.i64	d10, d9
	vadd.i64	d6, d2
	vadd.i64	d2, d10
	# Round 14
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d6, #50
	vsri.u64	d8, d6, #14
	vshl.u64	d9, d2, #36
	vsri.u64	d9, d2, #28
	vshl.u64	d10, d6, #46
	vsri.u64	d10, d6, #18
	vshl.u64	d11, d2, #30
	vsri.u64	d11, d2, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d6, #23
	vsri.u64	d10, d6, #41
	vshl.u64	d11, d2, #25
	vsri.u64	d11, d2, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d1, d8
	vadd.i64	d12, d30
	vmov	d8, d6
	veor	d10, d3, d4
	vadd.i64	d1, d12
	vbsl	d8, d7, d0
	vbsl	d10, d2, d4
	vadd.i64	d1, d8
	vadd.i64	d10, d9
	vadd.i64	d5, d1
	vadd.i64	d1, d10
	# Round 15
	vld1.64	{d12}, [r3:64]!
	vshl.u64	d8, d5, #50
	vsri.u64	d8, d5, #14
	vshl.u64	d9, d1, #36
	vsri.u64	d9, d1, #28
	vshl.u64	d10, d5, #46
	vsri.u64	d10, d5, #18
	vshl.u64	d11, d1, #30
	vsri.u64	d11, d1, #34
	veor	d8, d10
	veor	d9, d11
	vshl.u64	d10, d5, #23
	vsri.u64	d10, d5, #41
	vshl.u64	d11, d1, #25
	vsri.u64	d11, d1, #39
	veor	d8, d10
	veor	d9, d11
	vadd.i64	d0, d8
	vadd.i64	d12, d31
	vmov	d8, d5
	veor	d10, d2, d3
	vadd.i64	d0, d12
	vbsl	d8, d6, d7
	vbsl	d10, d1, d3
	vadd.i64	d0, d8
	vadd.i64	d10, d9
	vadd.i64	d4, d0
	vadd.i64	d0, d10
	# Add in digest from start
	vldm.64	r0, {d8-d15}
	vadd.i64	q0, q0, q4
	vadd.i64	q1, q1, q5
	vadd.i64	q2, q2, q6
	vadd.i64	q3, q3, q7
	vstm.64	r0, {d0-d7}
	subs	r2, r2, #0x80
	bne	L_sha512_len_neon_begin
	vpop	{d8-d15}
	bx	lr
	.size	Transform_Sha512_Len,.-Transform_Sha512_Len
#endif /* !WOLFSSL_ARMASM_NO_NEON */
#endif /* !__aarch64__ */
#endif /* WOLFSSL_ARMASM */
