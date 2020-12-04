/* aes_gcm_asm
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
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

#ifndef HAVE_INTEL_AVX1
#define HAVE_INTEL_AVX1
#endif /* HAVE_INTEL_AVX1 */
#ifndef NO_AVX2_SUPPORT
#define HAVE_INTEL_AVX2
#endif /* NO_AVX2_SUPPORT */

#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_one:
.quad	0x0, 0x1
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_two:
.quad	0x0, 0x2
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_three:
.quad	0x0, 0x3
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_four:
.quad	0x0, 0x4
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_five:
.quad	0x0, 0x5
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_six:
.quad	0x0, 0x6
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_seven:
.quad	0x0, 0x7
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_eight:
.quad	0x0, 0x8
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_bswap_epi64:
.quad	0x1020304050607, 0x8090a0b0c0d0e0f
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_bswap_mask:
.quad	0x8090a0b0c0d0e0f, 0x1020304050607
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_aes_gcm_mod2_128:
.quad	0x1, 0xc200000000000000
#ifndef __APPLE__
.text
.globl	AES_GCM_encrypt
.type	AES_GCM_encrypt,@function
.align	4
AES_GCM_encrypt:
#else
.section	__TEXT,__text
.globl	_AES_GCM_encrypt
.p2align	2
_AES_GCM_encrypt:
#endif /* __APPLE__ */
        pushq	%r13
        pushq	%r12
        pushq	%rbx
        pushq	%r14
        pushq	%r15
        movq	%rdx, %r12
        movq	%rcx, %rax
        movl	48(%rsp), %r11d
        movl	56(%rsp), %ebx
        movl	64(%rsp), %r14d
        movq	72(%rsp), %r15
        movl	80(%rsp), %r10d
        subq	$0xa0, %rsp
        pxor	%xmm4, %xmm4
        pxor	%xmm6, %xmm6
        cmpl	$12, %ebx
        movl	%ebx, %edx
        jne	L_AES_GCM_encrypt_iv_not_12
        # # Calculate values when IV is 12 bytes
        # Set counter based on IV
        movl	$0x1000000, %ecx
        pinsrq	$0x00, (%rax), %xmm4
        pinsrd	$2, 8(%rax), %xmm4
        pinsrd	$3, %ecx, %xmm4
        # H = Encrypt X(=0) and T = Encrypt counter
        movdqa	%xmm4, %xmm1
        movdqa	(%r15), %xmm5
        pxor	%xmm5, %xmm1
        movdqa	16(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	32(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	48(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	64(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	80(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	96(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	112(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	128(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	144(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm7
        jl	L_AES_GCM_encrypt_calc_iv_12_last
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	176(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm7
        jl	L_AES_GCM_encrypt_calc_iv_12_last
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	208(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	224(%r15), %xmm7
L_AES_GCM_encrypt_calc_iv_12_last:
        aesenclast	%xmm7, %xmm5
        aesenclast	%xmm7, %xmm1
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm5
        movdqa	%xmm1, 144(%rsp)
        jmp	L_AES_GCM_encrypt_iv_done
L_AES_GCM_encrypt_iv_not_12:
        # Calculate values when IV is not 12 bytes
        # H = Encrypt X(=0)
        movdqa	(%r15), %xmm5
        aesenc	16(%r15), %xmm5
        aesenc	32(%r15), %xmm5
        aesenc	48(%r15), %xmm5
        aesenc	64(%r15), %xmm5
        aesenc	80(%r15), %xmm5
        aesenc	96(%r15), %xmm5
        aesenc	112(%r15), %xmm5
        aesenc	128(%r15), %xmm5
        aesenc	144(%r15), %xmm5
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_calc_iv_1_aesenc_avx_last
        aesenc	%xmm9, %xmm5
        aesenc	176(%r15), %xmm5
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_calc_iv_1_aesenc_avx_last
        aesenc	%xmm9, %xmm5
        aesenc	208(%r15), %xmm5
        movdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_calc_iv_1_aesenc_avx_last:
        aesenclast	%xmm9, %xmm5
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm5
        # Calc counter
        # Initialization vector
        cmpl	$0x00, %edx
        movq	$0x00, %rcx
        je	L_AES_GCM_encrypt_calc_iv_done
        cmpl	$16, %edx
        jl	L_AES_GCM_encrypt_calc_iv_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_encrypt_calc_iv_16_loop:
        movdqu	(%rax,%rcx,1), %xmm8
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm4
        pshufd	$0x4e, %xmm4, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm4, %xmm3
        pclmulqdq	$0x00, %xmm4, %xmm0
        pxor	%xmm4, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm4
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm4, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm4
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm4
        por	%xmm0, %xmm7
        por	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm4
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_calc_iv_16_loop
        movl	%ebx, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_encrypt_calc_iv_done
L_AES_GCM_encrypt_calc_iv_lt16:
        subq	$16, %rsp
        pxor	%xmm8, %xmm8
        xorl	%ebx, %ebx
        movdqa	%xmm8, (%rsp)
L_AES_GCM_encrypt_calc_iv_loop:
        movzbl	(%rax,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_calc_iv_loop
        movdqa	(%rsp), %xmm8
        addq	$16, %rsp
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm4
        pshufd	$0x4e, %xmm4, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm4, %xmm3
        pclmulqdq	$0x00, %xmm4, %xmm0
        pxor	%xmm4, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm4
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm4, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm4
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm4
        por	%xmm0, %xmm7
        por	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm4
L_AES_GCM_encrypt_calc_iv_done:
        # T = Encrypt counter
        pxor	%xmm0, %xmm0
        shll	$3, %edx
        pinsrq	$0x00, %rdx, %xmm0
        pxor	%xmm0, %xmm4
        pshufd	$0x4e, %xmm4, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm4, %xmm3
        pclmulqdq	$0x00, %xmm4, %xmm0
        pxor	%xmm4, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm4
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm4, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm4
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm4
        por	%xmm0, %xmm7
        por	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm4
        #   Encrypt counter
        movdqa	(%r15), %xmm8
        pxor	%xmm4, %xmm8
        aesenc	16(%r15), %xmm8
        aesenc	32(%r15), %xmm8
        aesenc	48(%r15), %xmm8
        aesenc	64(%r15), %xmm8
        aesenc	80(%r15), %xmm8
        aesenc	96(%r15), %xmm8
        aesenc	112(%r15), %xmm8
        aesenc	128(%r15), %xmm8
        aesenc	144(%r15), %xmm8
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_calc_iv_2_aesenc_avx_last
        aesenc	%xmm9, %xmm8
        aesenc	176(%r15), %xmm8
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_calc_iv_2_aesenc_avx_last
        aesenc	%xmm9, %xmm8
        aesenc	208(%r15), %xmm8
        movdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_calc_iv_2_aesenc_avx_last:
        aesenclast	%xmm9, %xmm8
        movdqa	%xmm8, 144(%rsp)
L_AES_GCM_encrypt_iv_done:
        # Additional authentication data
        movl	%r11d, %edx
        cmpl	$0x00, %edx
        je	L_AES_GCM_encrypt_calc_aad_done
        xorl	%ecx, %ecx
        cmpl	$16, %edx
        jl	L_AES_GCM_encrypt_calc_aad_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_encrypt_calc_aad_16_loop:
        movdqu	(%r12,%rcx,1), %xmm8
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm6
        pshufd	$0x4e, %xmm6, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm6, %xmm3
        pclmulqdq	$0x00, %xmm6, %xmm0
        pxor	%xmm6, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm6, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm6
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm6
        por	%xmm0, %xmm7
        por	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm6
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_calc_aad_16_loop
        movl	%r11d, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_encrypt_calc_aad_done
L_AES_GCM_encrypt_calc_aad_lt16:
        subq	$16, %rsp
        pxor	%xmm8, %xmm8
        xorl	%ebx, %ebx
        movdqa	%xmm8, (%rsp)
L_AES_GCM_encrypt_calc_aad_loop:
        movzbl	(%r12,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_calc_aad_loop
        movdqa	(%rsp), %xmm8
        addq	$16, %rsp
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm6
        pshufd	$0x4e, %xmm6, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm6, %xmm3
        pclmulqdq	$0x00, %xmm6, %xmm0
        pxor	%xmm6, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm6, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm6
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm6
        por	%xmm0, %xmm7
        por	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm6
L_AES_GCM_encrypt_calc_aad_done:
        # Calculate counter and H
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm4
        movdqa	%xmm5, %xmm9
        paddd	L_aes_gcm_one(%rip), %xmm4
        movdqa	%xmm5, %xmm8
        movdqa	%xmm4, 128(%rsp)
        psrlq	$63, %xmm9
        psllq	$0x01, %xmm8
        pslldq	$8, %xmm9
        por	%xmm9, %xmm8
        pshufd	$0xff, %xmm5, %xmm5
        psrad	$31, %xmm5
        pand	L_aes_gcm_mod2_128(%rip), %xmm5
        pxor	%xmm8, %xmm5
        xorq	%rbx, %rbx
        cmpl	$0x80, %r9d
        movl	%r9d, %r13d
        jl	L_AES_GCM_encrypt_done_128
        andl	$0xffffff80, %r13d
        movdqa	%xmm6, %xmm2
        # H ^ 1
        movdqa	%xmm5, (%rsp)
        # H ^ 2
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm5, %xmm10
        movdqa	%xmm5, %xmm11
        movdqa	%xmm5, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm5, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm0
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm0
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm0
        movdqa	%xmm0, 16(%rsp)
        # H ^ 3
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm0, %xmm10
        movdqa	%xmm0, %xmm11
        movdqa	%xmm0, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm0, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm1
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm1
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm1
        movdqa	%xmm1, 32(%rsp)
        # H ^ 4
        pshufd	$0x4e, %xmm0, %xmm9
        pshufd	$0x4e, %xmm0, %xmm10
        movdqa	%xmm0, %xmm11
        movdqa	%xmm0, %xmm8
        pclmulqdq	$0x11, %xmm0, %xmm11
        pclmulqdq	$0x00, %xmm0, %xmm8
        pxor	%xmm0, %xmm9
        pxor	%xmm0, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm3
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm3
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm3
        movdqa	%xmm3, 48(%rsp)
        # H ^ 5
        pshufd	$0x4e, %xmm0, %xmm9
        pshufd	$0x4e, %xmm1, %xmm10
        movdqa	%xmm1, %xmm11
        movdqa	%xmm1, %xmm8
        pclmulqdq	$0x11, %xmm0, %xmm11
        pclmulqdq	$0x00, %xmm0, %xmm8
        pxor	%xmm0, %xmm9
        pxor	%xmm1, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 64(%rsp)
        # H ^ 6
        pshufd	$0x4e, %xmm1, %xmm9
        pshufd	$0x4e, %xmm1, %xmm10
        movdqa	%xmm1, %xmm11
        movdqa	%xmm1, %xmm8
        pclmulqdq	$0x11, %xmm1, %xmm11
        pclmulqdq	$0x00, %xmm1, %xmm8
        pxor	%xmm1, %xmm9
        pxor	%xmm1, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 80(%rsp)
        # H ^ 7
        pshufd	$0x4e, %xmm1, %xmm9
        pshufd	$0x4e, %xmm3, %xmm10
        movdqa	%xmm3, %xmm11
        movdqa	%xmm3, %xmm8
        pclmulqdq	$0x11, %xmm1, %xmm11
        pclmulqdq	$0x00, %xmm1, %xmm8
        pxor	%xmm1, %xmm9
        pxor	%xmm3, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 96(%rsp)
        # H ^ 8
        pshufd	$0x4e, %xmm3, %xmm9
        pshufd	$0x4e, %xmm3, %xmm10
        movdqa	%xmm3, %xmm11
        movdqa	%xmm3, %xmm8
        pclmulqdq	$0x11, %xmm3, %xmm11
        pclmulqdq	$0x00, %xmm3, %xmm8
        pxor	%xmm3, %xmm9
        pxor	%xmm3, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 112(%rsp)
        # First 128 bytes of input
        movdqa	128(%rsp), %xmm8
        movdqa	L_aes_gcm_bswap_epi64(%rip), %xmm1
        movdqa	%xmm8, %xmm0
        pshufb	%xmm1, %xmm8
        movdqa	%xmm0, %xmm9
        paddd	L_aes_gcm_one(%rip), %xmm9
        pshufb	%xmm1, %xmm9
        movdqa	%xmm0, %xmm10
        paddd	L_aes_gcm_two(%rip), %xmm10
        pshufb	%xmm1, %xmm10
        movdqa	%xmm0, %xmm11
        paddd	L_aes_gcm_three(%rip), %xmm11
        pshufb	%xmm1, %xmm11
        movdqa	%xmm0, %xmm12
        paddd	L_aes_gcm_four(%rip), %xmm12
        pshufb	%xmm1, %xmm12
        movdqa	%xmm0, %xmm13
        paddd	L_aes_gcm_five(%rip), %xmm13
        pshufb	%xmm1, %xmm13
        movdqa	%xmm0, %xmm14
        paddd	L_aes_gcm_six(%rip), %xmm14
        pshufb	%xmm1, %xmm14
        movdqa	%xmm0, %xmm15
        paddd	L_aes_gcm_seven(%rip), %xmm15
        pshufb	%xmm1, %xmm15
        paddd	L_aes_gcm_eight(%rip), %xmm0
        movdqa	(%r15), %xmm7
        movdqa	%xmm0, 128(%rsp)
        pxor	%xmm7, %xmm8
        pxor	%xmm7, %xmm9
        pxor	%xmm7, %xmm10
        pxor	%xmm7, %xmm11
        pxor	%xmm7, %xmm12
        pxor	%xmm7, %xmm13
        pxor	%xmm7, %xmm14
        pxor	%xmm7, %xmm15
        movdqa	16(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	32(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	48(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	64(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	80(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	96(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	112(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	128(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	144(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm7
        jl	L_AES_GCM_encrypt_enc_done
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	176(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm7
        jl	L_AES_GCM_encrypt_enc_done
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	208(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	224(%r15), %xmm7
L_AES_GCM_encrypt_enc_done:
        aesenclast	%xmm7, %xmm8
        aesenclast	%xmm7, %xmm9
        movdqu	(%rdi), %xmm0
        movdqu	16(%rdi), %xmm1
        pxor	%xmm0, %xmm8
        pxor	%xmm1, %xmm9
        movdqu	%xmm8, (%rsi)
        movdqu	%xmm9, 16(%rsi)
        aesenclast	%xmm7, %xmm10
        aesenclast	%xmm7, %xmm11
        movdqu	32(%rdi), %xmm0
        movdqu	48(%rdi), %xmm1
        pxor	%xmm0, %xmm10
        pxor	%xmm1, %xmm11
        movdqu	%xmm10, 32(%rsi)
        movdqu	%xmm11, 48(%rsi)
        aesenclast	%xmm7, %xmm12
        aesenclast	%xmm7, %xmm13
        movdqu	64(%rdi), %xmm0
        movdqu	80(%rdi), %xmm1
        pxor	%xmm0, %xmm12
        pxor	%xmm1, %xmm13
        movdqu	%xmm12, 64(%rsi)
        movdqu	%xmm13, 80(%rsi)
        aesenclast	%xmm7, %xmm14
        aesenclast	%xmm7, %xmm15
        movdqu	96(%rdi), %xmm0
        movdqu	112(%rdi), %xmm1
        pxor	%xmm0, %xmm14
        pxor	%xmm1, %xmm15
        movdqu	%xmm14, 96(%rsi)
        movdqu	%xmm15, 112(%rsi)
        cmpl	$0x80, %r13d
        movl	$0x80, %ebx
        jle	L_AES_GCM_encrypt_end_128
        # More 128 bytes of input
L_AES_GCM_encrypt_ghash_128:
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        movdqa	128(%rsp), %xmm8
        movdqa	L_aes_gcm_bswap_epi64(%rip), %xmm1
        movdqa	%xmm8, %xmm0
        pshufb	%xmm1, %xmm8
        movdqa	%xmm0, %xmm9
        paddd	L_aes_gcm_one(%rip), %xmm9
        pshufb	%xmm1, %xmm9
        movdqa	%xmm0, %xmm10
        paddd	L_aes_gcm_two(%rip), %xmm10
        pshufb	%xmm1, %xmm10
        movdqa	%xmm0, %xmm11
        paddd	L_aes_gcm_three(%rip), %xmm11
        pshufb	%xmm1, %xmm11
        movdqa	%xmm0, %xmm12
        paddd	L_aes_gcm_four(%rip), %xmm12
        pshufb	%xmm1, %xmm12
        movdqa	%xmm0, %xmm13
        paddd	L_aes_gcm_five(%rip), %xmm13
        pshufb	%xmm1, %xmm13
        movdqa	%xmm0, %xmm14
        paddd	L_aes_gcm_six(%rip), %xmm14
        pshufb	%xmm1, %xmm14
        movdqa	%xmm0, %xmm15
        paddd	L_aes_gcm_seven(%rip), %xmm15
        pshufb	%xmm1, %xmm15
        paddd	L_aes_gcm_eight(%rip), %xmm0
        movdqa	(%r15), %xmm7
        movdqa	%xmm0, 128(%rsp)
        pxor	%xmm7, %xmm8
        pxor	%xmm7, %xmm9
        pxor	%xmm7, %xmm10
        pxor	%xmm7, %xmm11
        pxor	%xmm7, %xmm12
        pxor	%xmm7, %xmm13
        pxor	%xmm7, %xmm14
        pxor	%xmm7, %xmm15
        movdqa	112(%rsp), %xmm7
        movdqu	-128(%rdx), %xmm0
        aesenc	16(%r15), %xmm8
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        pxor	%xmm2, %xmm0
        pshufd	$0x4e, %xmm7, %xmm1
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm7, %xmm1
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm3
        pclmulqdq	$0x11, %xmm7, %xmm3
        aesenc	16(%r15), %xmm9
        aesenc	16(%r15), %xmm10
        movdqa	%xmm0, %xmm2
        pclmulqdq	$0x00, %xmm7, %xmm2
        aesenc	16(%r15), %xmm11
        aesenc	16(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm1
        aesenc	16(%r15), %xmm13
        aesenc	16(%r15), %xmm14
        aesenc	16(%r15), %xmm15
        pxor	%xmm2, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	96(%rsp), %xmm7
        movdqu	-112(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	32(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	32(%r15), %xmm9
        aesenc	32(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	32(%r15), %xmm11
        aesenc	32(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	32(%r15), %xmm13
        aesenc	32(%r15), %xmm14
        aesenc	32(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	80(%rsp), %xmm7
        movdqu	-96(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	48(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	48(%r15), %xmm9
        aesenc	48(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	48(%r15), %xmm11
        aesenc	48(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	48(%r15), %xmm13
        aesenc	48(%r15), %xmm14
        aesenc	48(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	64(%rsp), %xmm7
        movdqu	-80(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	64(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	64(%r15), %xmm9
        aesenc	64(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	64(%r15), %xmm11
        aesenc	64(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	64(%r15), %xmm13
        aesenc	64(%r15), %xmm14
        aesenc	64(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	48(%rsp), %xmm7
        movdqu	-64(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	80(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	80(%r15), %xmm9
        aesenc	80(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	80(%r15), %xmm11
        aesenc	80(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	80(%r15), %xmm13
        aesenc	80(%r15), %xmm14
        aesenc	80(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	32(%rsp), %xmm7
        movdqu	-48(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	96(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	96(%r15), %xmm9
        aesenc	96(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	96(%r15), %xmm11
        aesenc	96(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	96(%r15), %xmm13
        aesenc	96(%r15), %xmm14
        aesenc	96(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	16(%rsp), %xmm7
        movdqu	-32(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	112(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	112(%r15), %xmm9
        aesenc	112(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	112(%r15), %xmm11
        aesenc	112(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	112(%r15), %xmm13
        aesenc	112(%r15), %xmm14
        aesenc	112(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	(%rsp), %xmm7
        movdqu	-16(%rdx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	128(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	128(%r15), %xmm9
        aesenc	128(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	128(%r15), %xmm11
        aesenc	128(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	128(%r15), %xmm13
        aesenc	128(%r15), %xmm14
        aesenc	128(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	%xmm1, %xmm5
        psrldq	$8, %xmm1
        pslldq	$8, %xmm5
        aesenc	144(%r15), %xmm8
        pxor	%xmm5, %xmm2
        pxor	%xmm1, %xmm3
        movdqa	%xmm2, %xmm7
        movdqa	%xmm2, %xmm4
        movdqa	%xmm2, %xmm5
        aesenc	144(%r15), %xmm9
        pslld	$31, %xmm7
        pslld	$30, %xmm4
        pslld	$25, %xmm5
        aesenc	144(%r15), %xmm10
        pxor	%xmm4, %xmm7
        pxor	%xmm5, %xmm7
        aesenc	144(%r15), %xmm11
        movdqa	%xmm7, %xmm4
        pslldq	$12, %xmm7
        psrldq	$4, %xmm4
        aesenc	144(%r15), %xmm12
        pxor	%xmm7, %xmm2
        movdqa	%xmm2, %xmm5
        movdqa	%xmm2, %xmm1
        movdqa	%xmm2, %xmm0
        aesenc	144(%r15), %xmm13
        psrld	$0x01, %xmm5
        psrld	$2, %xmm1
        psrld	$7, %xmm0
        aesenc	144(%r15), %xmm14
        pxor	%xmm1, %xmm5
        pxor	%xmm0, %xmm5
        aesenc	144(%r15), %xmm15
        pxor	%xmm4, %xmm5
        pxor	%xmm5, %xmm2
        pxor	%xmm3, %xmm2
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm7
        jl	L_AES_GCM_encrypt_aesenc_128_ghash_avx_done
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	176(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm7
        jl	L_AES_GCM_encrypt_aesenc_128_ghash_avx_done
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	208(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	224(%r15), %xmm7
L_AES_GCM_encrypt_aesenc_128_ghash_avx_done:
        aesenclast	%xmm7, %xmm8
        aesenclast	%xmm7, %xmm9
        movdqu	(%rcx), %xmm0
        movdqu	16(%rcx), %xmm1
        pxor	%xmm0, %xmm8
        pxor	%xmm1, %xmm9
        movdqu	%xmm8, (%rdx)
        movdqu	%xmm9, 16(%rdx)
        aesenclast	%xmm7, %xmm10
        aesenclast	%xmm7, %xmm11
        movdqu	32(%rcx), %xmm0
        movdqu	48(%rcx), %xmm1
        pxor	%xmm0, %xmm10
        pxor	%xmm1, %xmm11
        movdqu	%xmm10, 32(%rdx)
        movdqu	%xmm11, 48(%rdx)
        aesenclast	%xmm7, %xmm12
        aesenclast	%xmm7, %xmm13
        movdqu	64(%rcx), %xmm0
        movdqu	80(%rcx), %xmm1
        pxor	%xmm0, %xmm12
        pxor	%xmm1, %xmm13
        movdqu	%xmm12, 64(%rdx)
        movdqu	%xmm13, 80(%rdx)
        aesenclast	%xmm7, %xmm14
        aesenclast	%xmm7, %xmm15
        movdqu	96(%rcx), %xmm0
        movdqu	112(%rcx), %xmm1
        pxor	%xmm0, %xmm14
        pxor	%xmm1, %xmm15
        movdqu	%xmm14, 96(%rdx)
        movdqu	%xmm15, 112(%rdx)
        addl	$0x80, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_encrypt_ghash_128
L_AES_GCM_encrypt_end_128:
        movdqa	L_aes_gcm_bswap_mask(%rip), %xmm4
        pshufb	%xmm4, %xmm8
        pshufb	%xmm4, %xmm9
        pshufb	%xmm4, %xmm10
        pshufb	%xmm4, %xmm11
        pxor	%xmm2, %xmm8
        pshufb	%xmm4, %xmm12
        pshufb	%xmm4, %xmm13
        pshufb	%xmm4, %xmm14
        pshufb	%xmm4, %xmm15
        movdqa	112(%rsp), %xmm7
        pshufd	$0x4e, %xmm8, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm8, %xmm3
        pclmulqdq	$0x00, %xmm8, %xmm0
        pxor	%xmm8, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm4
        movdqa	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	96(%rsp), %xmm7
        pshufd	$0x4e, %xmm9, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm9, %xmm3
        pclmulqdq	$0x00, %xmm9, %xmm0
        pxor	%xmm9, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	80(%rsp), %xmm7
        pshufd	$0x4e, %xmm10, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm10, %xmm3
        pclmulqdq	$0x00, %xmm10, %xmm0
        pxor	%xmm10, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	64(%rsp), %xmm7
        pshufd	$0x4e, %xmm11, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm11, %xmm3
        pclmulqdq	$0x00, %xmm11, %xmm0
        pxor	%xmm11, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	48(%rsp), %xmm7
        pshufd	$0x4e, %xmm12, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm12, %xmm3
        pclmulqdq	$0x00, %xmm12, %xmm0
        pxor	%xmm12, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	32(%rsp), %xmm7
        pshufd	$0x4e, %xmm13, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm13, %xmm3
        pclmulqdq	$0x00, %xmm13, %xmm0
        pxor	%xmm13, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	16(%rsp), %xmm7
        pshufd	$0x4e, %xmm14, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm14, %xmm3
        pclmulqdq	$0x00, %xmm14, %xmm0
        pxor	%xmm14, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	(%rsp), %xmm7
        pshufd	$0x4e, %xmm15, %xmm1
        pshufd	$0x4e, %xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        pclmulqdq	$0x11, %xmm15, %xmm3
        pclmulqdq	$0x00, %xmm15, %xmm0
        pxor	%xmm15, %xmm1
        pxor	%xmm7, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        pxor	%xmm0, %xmm4
        pxor	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm4
        pxor	%xmm1, %xmm6
        movdqa	%xmm4, %xmm0
        movdqa	%xmm4, %xmm1
        movdqa	%xmm4, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm4
        movdqa	%xmm4, %xmm2
        movdqa	%xmm4, %xmm3
        movdqa	%xmm4, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm4, %xmm2
        pxor	%xmm2, %xmm6
        movdqa	(%rsp), %xmm5
L_AES_GCM_encrypt_done_128:
        movl	%r9d, %edx
        cmpl	%edx, %ebx
        jge	L_AES_GCM_encrypt_done_enc
        movl	%r9d, %r13d
        andl	$0xfffffff0, %r13d
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_encrypt_last_block_done
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        movdqa	128(%rsp), %xmm8
        movdqa	%xmm8, %xmm9
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm8
        paddd	L_aes_gcm_one(%rip), %xmm9
        pxor	(%r15), %xmm8
        movdqa	%xmm9, 128(%rsp)
        aesenc	16(%r15), %xmm8
        aesenc	32(%r15), %xmm8
        aesenc	48(%r15), %xmm8
        aesenc	64(%r15), %xmm8
        aesenc	80(%r15), %xmm8
        aesenc	96(%r15), %xmm8
        aesenc	112(%r15), %xmm8
        aesenc	128(%r15), %xmm8
        aesenc	144(%r15), %xmm8
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_aesenc_block_aesenc_avx_last
        aesenc	%xmm9, %xmm8
        aesenc	176(%r15), %xmm8
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_aesenc_block_aesenc_avx_last
        aesenc	%xmm9, %xmm8
        aesenc	208(%r15), %xmm8
        movdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_aesenc_block_aesenc_avx_last:
        aesenclast	%xmm9, %xmm8
        movdqu	(%rcx), %xmm9
        pxor	%xmm9, %xmm8
        movdqu	%xmm8, (%rdx)
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm6
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_encrypt_last_block_ghash
L_AES_GCM_encrypt_last_block_start:
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        movdqa	128(%rsp), %xmm8
        movdqa	%xmm8, %xmm9
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm8
        paddd	L_aes_gcm_one(%rip), %xmm9
        pxor	(%r15), %xmm8
        movdqa	%xmm9, 128(%rsp)
        movdqa	%xmm6, %xmm10
        pclmulqdq	$16, %xmm5, %xmm10
        aesenc	16(%r15), %xmm8
        aesenc	32(%r15), %xmm8
        movdqa	%xmm6, %xmm11
        pclmulqdq	$0x01, %xmm5, %xmm11
        aesenc	48(%r15), %xmm8
        aesenc	64(%r15), %xmm8
        movdqa	%xmm6, %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm12
        aesenc	80(%r15), %xmm8
        movdqa	%xmm6, %xmm1
        pclmulqdq	$0x11, %xmm5, %xmm1
        aesenc	96(%r15), %xmm8
        pxor	%xmm11, %xmm10
        movdqa	%xmm10, %xmm2
        psrldq	$8, %xmm10
        pslldq	$8, %xmm2
        aesenc	112(%r15), %xmm8
        movdqa	%xmm1, %xmm3
        pxor	%xmm12, %xmm2
        pxor	%xmm10, %xmm3
        movdqa	L_aes_gcm_mod2_128(%rip), %xmm0
        movdqa	%xmm2, %xmm11
        pclmulqdq	$16, %xmm0, %xmm11
        aesenc	128(%r15), %xmm8
        pshufd	$0x4e, %xmm2, %xmm10
        pxor	%xmm11, %xmm10
        movdqa	%xmm10, %xmm11
        pclmulqdq	$16, %xmm0, %xmm11
        aesenc	144(%r15), %xmm8
        pshufd	$0x4e, %xmm10, %xmm6
        pxor	%xmm11, %xmm6
        pxor	%xmm3, %xmm6
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_aesenc_gfmul_last
        aesenc	%xmm9, %xmm8
        aesenc	176(%r15), %xmm8
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_aesenc_gfmul_last
        aesenc	%xmm9, %xmm8
        aesenc	208(%r15), %xmm8
        movdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_aesenc_gfmul_last:
        aesenclast	%xmm9, %xmm8
        movdqu	(%rcx), %xmm9
        pxor	%xmm9, %xmm8
        movdqu	%xmm8, (%rdx)
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm6
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_encrypt_last_block_start
L_AES_GCM_encrypt_last_block_ghash:
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm6, %xmm10
        movdqa	%xmm6, %xmm11
        movdqa	%xmm6, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm6, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm6
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm6
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm6
L_AES_GCM_encrypt_last_block_done:
        movl	%r9d, %ecx
        movl	%ecx, %edx
        andl	$15, %ecx
        jz	L_AES_GCM_encrypt_aesenc_last15_enc_avx_done
        movdqa	128(%rsp), %xmm4
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm4
        pxor	(%r15), %xmm4
        aesenc	16(%r15), %xmm4
        aesenc	32(%r15), %xmm4
        aesenc	48(%r15), %xmm4
        aesenc	64(%r15), %xmm4
        aesenc	80(%r15), %xmm4
        aesenc	96(%r15), %xmm4
        aesenc	112(%r15), %xmm4
        aesenc	128(%r15), %xmm4
        aesenc	144(%r15), %xmm4
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_aesenc_last15_enc_avx_aesenc_avx_last
        aesenc	%xmm9, %xmm4
        aesenc	176(%r15), %xmm4
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_aesenc_last15_enc_avx_aesenc_avx_last
        aesenc	%xmm9, %xmm4
        aesenc	208(%r15), %xmm4
        movdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_aesenc_last15_enc_avx_aesenc_avx_last:
        aesenclast	%xmm9, %xmm4
        subq	$16, %rsp
        xorl	%ecx, %ecx
        movdqa	%xmm4, (%rsp)
L_AES_GCM_encrypt_aesenc_last15_enc_avx_loop:
        movzbl	(%rdi,%rbx,1), %r13d
        xorb	(%rsp,%rcx,1), %r13b
        movb	%r13b, (%rsi,%rbx,1)
        movb	%r13b, (%rsp,%rcx,1)
        incl	%ebx
        incl	%ecx
        cmpl	%edx, %ebx
        jl	L_AES_GCM_encrypt_aesenc_last15_enc_avx_loop
        xorq	%r13, %r13
        cmpl	$16, %ecx
        je	L_AES_GCM_encrypt_aesenc_last15_enc_avx_finish_enc
L_AES_GCM_encrypt_aesenc_last15_enc_avx_byte_loop:
        movb	%r13b, (%rsp,%rcx,1)
        incl	%ecx
        cmpl	$16, %ecx
        jl	L_AES_GCM_encrypt_aesenc_last15_enc_avx_byte_loop
L_AES_GCM_encrypt_aesenc_last15_enc_avx_finish_enc:
        movdqa	(%rsp), %xmm4
        addq	$16, %rsp
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm4
        pxor	%xmm4, %xmm6
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm6, %xmm10
        movdqa	%xmm6, %xmm11
        movdqa	%xmm6, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm6, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm6
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm6
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm6
L_AES_GCM_encrypt_aesenc_last15_enc_avx_done:
L_AES_GCM_encrypt_done_enc:
        movl	%r9d, %edx
        movl	%r11d, %ecx
        shlq	$3, %rdx
        shlq	$3, %rcx
        pinsrq	$0x00, %rdx, %xmm0
        pinsrq	$0x01, %rcx, %xmm0
        pxor	%xmm0, %xmm6
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm6, %xmm10
        movdqa	%xmm6, %xmm11
        movdqa	%xmm6, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm6, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm6
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm6
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm6
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm6
        movdqa	144(%rsp), %xmm0
        pxor	%xmm6, %xmm0
        cmpl	$16, %r14d
        je	L_AES_GCM_encrypt_store_tag_16
        xorq	%rcx, %rcx
        movdqa	%xmm0, (%rsp)
L_AES_GCM_encrypt_store_tag_loop:
        movzbl	(%rsp,%rcx,1), %r13d
        movb	%r13b, (%r8,%rcx,1)
        incl	%ecx
        cmpl	%r14d, %ecx
        jne	L_AES_GCM_encrypt_store_tag_loop
        jmp	L_AES_GCM_encrypt_store_tag_done
L_AES_GCM_encrypt_store_tag_16:
        movdqu	%xmm0, (%r8)
L_AES_GCM_encrypt_store_tag_done:
        addq	$0xa0, %rsp
        popq	%r15
        popq	%r14
        popq	%rbx
        popq	%r12
        popq	%r13
        repz retq
#ifndef __APPLE__
.size	AES_GCM_encrypt,.-AES_GCM_encrypt
#endif /* __APPLE__ */
#ifndef __APPLE__
.text
.globl	AES_GCM_decrypt
.type	AES_GCM_decrypt,@function
.align	4
AES_GCM_decrypt:
#else
.section	__TEXT,__text
.globl	_AES_GCM_decrypt
.p2align	2
_AES_GCM_decrypt:
#endif /* __APPLE__ */
        pushq	%r13
        pushq	%r12
        pushq	%rbx
        pushq	%r14
        pushq	%r15
        pushq	%rbp
        movq	%rdx, %r12
        movq	%rcx, %rax
        movl	56(%rsp), %r11d
        movl	64(%rsp), %ebx
        movl	72(%rsp), %r14d
        movq	80(%rsp), %r15
        movl	88(%rsp), %r10d
        movq	96(%rsp), %rbp
        subq	$0xa8, %rsp
        pxor	%xmm4, %xmm4
        pxor	%xmm6, %xmm6
        cmpl	$12, %ebx
        movl	%ebx, %edx
        jne	L_AES_GCM_decrypt_iv_not_12
        # # Calculate values when IV is 12 bytes
        # Set counter based on IV
        movl	$0x1000000, %ecx
        pinsrq	$0x00, (%rax), %xmm4
        pinsrd	$2, 8(%rax), %xmm4
        pinsrd	$3, %ecx, %xmm4
        # H = Encrypt X(=0) and T = Encrypt counter
        movdqa	%xmm4, %xmm1
        movdqa	(%r15), %xmm5
        pxor	%xmm5, %xmm1
        movdqa	16(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	32(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	48(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	64(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	80(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	96(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	112(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	128(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	144(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm7
        jl	L_AES_GCM_decrypt_calc_iv_12_last
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	176(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm7
        jl	L_AES_GCM_decrypt_calc_iv_12_last
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	208(%r15), %xmm7
        aesenc	%xmm7, %xmm5
        aesenc	%xmm7, %xmm1
        movdqa	224(%r15), %xmm7
L_AES_GCM_decrypt_calc_iv_12_last:
        aesenclast	%xmm7, %xmm5
        aesenclast	%xmm7, %xmm1
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm5
        movdqa	%xmm1, 144(%rsp)
        jmp	L_AES_GCM_decrypt_iv_done
L_AES_GCM_decrypt_iv_not_12:
        # Calculate values when IV is not 12 bytes
        # H = Encrypt X(=0)
        movdqa	(%r15), %xmm5
        aesenc	16(%r15), %xmm5
        aesenc	32(%r15), %xmm5
        aesenc	48(%r15), %xmm5
        aesenc	64(%r15), %xmm5
        aesenc	80(%r15), %xmm5
        aesenc	96(%r15), %xmm5
        aesenc	112(%r15), %xmm5
        aesenc	128(%r15), %xmm5
        aesenc	144(%r15), %xmm5
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_calc_iv_1_aesenc_avx_last
        aesenc	%xmm9, %xmm5
        aesenc	176(%r15), %xmm5
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_calc_iv_1_aesenc_avx_last
        aesenc	%xmm9, %xmm5
        aesenc	208(%r15), %xmm5
        movdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_calc_iv_1_aesenc_avx_last:
        aesenclast	%xmm9, %xmm5
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm5
        # Calc counter
        # Initialization vector
        cmpl	$0x00, %edx
        movq	$0x00, %rcx
        je	L_AES_GCM_decrypt_calc_iv_done
        cmpl	$16, %edx
        jl	L_AES_GCM_decrypt_calc_iv_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_decrypt_calc_iv_16_loop:
        movdqu	(%rax,%rcx,1), %xmm8
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm4
        pshufd	$0x4e, %xmm4, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm4, %xmm3
        pclmulqdq	$0x00, %xmm4, %xmm0
        pxor	%xmm4, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm4
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm4, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm4
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm4
        por	%xmm0, %xmm7
        por	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm4
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_calc_iv_16_loop
        movl	%ebx, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_decrypt_calc_iv_done
L_AES_GCM_decrypt_calc_iv_lt16:
        subq	$16, %rsp
        pxor	%xmm8, %xmm8
        xorl	%ebx, %ebx
        movdqa	%xmm8, (%rsp)
L_AES_GCM_decrypt_calc_iv_loop:
        movzbl	(%rax,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_calc_iv_loop
        movdqa	(%rsp), %xmm8
        addq	$16, %rsp
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm4
        pshufd	$0x4e, %xmm4, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm4, %xmm3
        pclmulqdq	$0x00, %xmm4, %xmm0
        pxor	%xmm4, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm4
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm4, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm4
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm4
        por	%xmm0, %xmm7
        por	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm4
L_AES_GCM_decrypt_calc_iv_done:
        # T = Encrypt counter
        pxor	%xmm0, %xmm0
        shll	$3, %edx
        pinsrq	$0x00, %rdx, %xmm0
        pxor	%xmm0, %xmm4
        pshufd	$0x4e, %xmm4, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm4, %xmm3
        pclmulqdq	$0x00, %xmm4, %xmm0
        pxor	%xmm4, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm4
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm4, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm4
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm4
        por	%xmm0, %xmm7
        por	%xmm1, %xmm4
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm4
        #   Encrypt counter
        movdqa	(%r15), %xmm8
        pxor	%xmm4, %xmm8
        aesenc	16(%r15), %xmm8
        aesenc	32(%r15), %xmm8
        aesenc	48(%r15), %xmm8
        aesenc	64(%r15), %xmm8
        aesenc	80(%r15), %xmm8
        aesenc	96(%r15), %xmm8
        aesenc	112(%r15), %xmm8
        aesenc	128(%r15), %xmm8
        aesenc	144(%r15), %xmm8
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_calc_iv_2_aesenc_avx_last
        aesenc	%xmm9, %xmm8
        aesenc	176(%r15), %xmm8
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_calc_iv_2_aesenc_avx_last
        aesenc	%xmm9, %xmm8
        aesenc	208(%r15), %xmm8
        movdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_calc_iv_2_aesenc_avx_last:
        aesenclast	%xmm9, %xmm8
        movdqa	%xmm8, 144(%rsp)
L_AES_GCM_decrypt_iv_done:
        # Additional authentication data
        movl	%r11d, %edx
        cmpl	$0x00, %edx
        je	L_AES_GCM_decrypt_calc_aad_done
        xorl	%ecx, %ecx
        cmpl	$16, %edx
        jl	L_AES_GCM_decrypt_calc_aad_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_decrypt_calc_aad_16_loop:
        movdqu	(%r12,%rcx,1), %xmm8
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm6
        pshufd	$0x4e, %xmm6, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm6, %xmm3
        pclmulqdq	$0x00, %xmm6, %xmm0
        pxor	%xmm6, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm6, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm6
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm6
        por	%xmm0, %xmm7
        por	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm6
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_calc_aad_16_loop
        movl	%r11d, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_decrypt_calc_aad_done
L_AES_GCM_decrypt_calc_aad_lt16:
        subq	$16, %rsp
        pxor	%xmm8, %xmm8
        xorl	%ebx, %ebx
        movdqa	%xmm8, (%rsp)
L_AES_GCM_decrypt_calc_aad_loop:
        movzbl	(%r12,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_calc_aad_loop
        movdqa	(%rsp), %xmm8
        addq	$16, %rsp
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm8
        pxor	%xmm8, %xmm6
        pshufd	$0x4e, %xmm6, %xmm1
        pshufd	$0x4e, %xmm5, %xmm2
        movdqa	%xmm5, %xmm3
        movdqa	%xmm5, %xmm0
        pclmulqdq	$0x11, %xmm6, %xmm3
        pclmulqdq	$0x00, %xmm6, %xmm0
        pxor	%xmm6, %xmm1
        pxor	%xmm5, %xmm2
        pclmulqdq	$0x00, %xmm2, %xmm1
        pxor	%xmm0, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	%xmm1, %xmm2
        movdqa	%xmm0, %xmm7
        movdqa	%xmm3, %xmm6
        pslldq	$8, %xmm2
        psrldq	$8, %xmm1
        pxor	%xmm2, %xmm7
        pxor	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm6, %xmm1
        psrld	$31, %xmm0
        psrld	$31, %xmm1
        pslld	$0x01, %xmm7
        pslld	$0x01, %xmm6
        movdqa	%xmm0, %xmm2
        pslldq	$4, %xmm0
        psrldq	$12, %xmm2
        pslldq	$4, %xmm1
        por	%xmm2, %xmm6
        por	%xmm0, %xmm7
        por	%xmm1, %xmm6
        movdqa	%xmm7, %xmm0
        movdqa	%xmm7, %xmm1
        movdqa	%xmm7, %xmm2
        pslld	$31, %xmm0
        pslld	$30, %xmm1
        pslld	$25, %xmm2
        pxor	%xmm1, %xmm0
        pxor	%xmm2, %xmm0
        movdqa	%xmm0, %xmm1
        psrldq	$4, %xmm1
        pslldq	$12, %xmm0
        pxor	%xmm0, %xmm7
        movdqa	%xmm7, %xmm2
        movdqa	%xmm7, %xmm3
        movdqa	%xmm7, %xmm0
        psrld	$0x01, %xmm2
        psrld	$2, %xmm3
        psrld	$7, %xmm0
        pxor	%xmm3, %xmm2
        pxor	%xmm0, %xmm2
        pxor	%xmm1, %xmm2
        pxor	%xmm7, %xmm2
        pxor	%xmm2, %xmm6
L_AES_GCM_decrypt_calc_aad_done:
        # Calculate counter and H
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm4
        movdqa	%xmm5, %xmm9
        paddd	L_aes_gcm_one(%rip), %xmm4
        movdqa	%xmm5, %xmm8
        movdqa	%xmm4, 128(%rsp)
        psrlq	$63, %xmm9
        psllq	$0x01, %xmm8
        pslldq	$8, %xmm9
        por	%xmm9, %xmm8
        pshufd	$0xff, %xmm5, %xmm5
        psrad	$31, %xmm5
        pand	L_aes_gcm_mod2_128(%rip), %xmm5
        pxor	%xmm8, %xmm5
        xorl	%ebx, %ebx
        cmpl	$0x80, %r9d
        movl	%r9d, %r13d
        jl	L_AES_GCM_decrypt_done_128
        andl	$0xffffff80, %r13d
        movdqa	%xmm6, %xmm2
        # H ^ 1
        movdqa	%xmm5, (%rsp)
        # H ^ 2
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm5, %xmm10
        movdqa	%xmm5, %xmm11
        movdqa	%xmm5, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm5, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm0
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm0
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm0
        movdqa	%xmm0, 16(%rsp)
        # H ^ 3
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm0, %xmm10
        movdqa	%xmm0, %xmm11
        movdqa	%xmm0, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm0, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm1
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm1
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm1
        movdqa	%xmm1, 32(%rsp)
        # H ^ 4
        pshufd	$0x4e, %xmm0, %xmm9
        pshufd	$0x4e, %xmm0, %xmm10
        movdqa	%xmm0, %xmm11
        movdqa	%xmm0, %xmm8
        pclmulqdq	$0x11, %xmm0, %xmm11
        pclmulqdq	$0x00, %xmm0, %xmm8
        pxor	%xmm0, %xmm9
        pxor	%xmm0, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm3
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm3
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm3
        movdqa	%xmm3, 48(%rsp)
        # H ^ 5
        pshufd	$0x4e, %xmm0, %xmm9
        pshufd	$0x4e, %xmm1, %xmm10
        movdqa	%xmm1, %xmm11
        movdqa	%xmm1, %xmm8
        pclmulqdq	$0x11, %xmm0, %xmm11
        pclmulqdq	$0x00, %xmm0, %xmm8
        pxor	%xmm0, %xmm9
        pxor	%xmm1, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 64(%rsp)
        # H ^ 6
        pshufd	$0x4e, %xmm1, %xmm9
        pshufd	$0x4e, %xmm1, %xmm10
        movdqa	%xmm1, %xmm11
        movdqa	%xmm1, %xmm8
        pclmulqdq	$0x11, %xmm1, %xmm11
        pclmulqdq	$0x00, %xmm1, %xmm8
        pxor	%xmm1, %xmm9
        pxor	%xmm1, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 80(%rsp)
        # H ^ 7
        pshufd	$0x4e, %xmm1, %xmm9
        pshufd	$0x4e, %xmm3, %xmm10
        movdqa	%xmm3, %xmm11
        movdqa	%xmm3, %xmm8
        pclmulqdq	$0x11, %xmm1, %xmm11
        pclmulqdq	$0x00, %xmm1, %xmm8
        pxor	%xmm1, %xmm9
        pxor	%xmm3, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 96(%rsp)
        # H ^ 8
        pshufd	$0x4e, %xmm3, %xmm9
        pshufd	$0x4e, %xmm3, %xmm10
        movdqa	%xmm3, %xmm11
        movdqa	%xmm3, %xmm8
        pclmulqdq	$0x11, %xmm3, %xmm11
        pclmulqdq	$0x00, %xmm3, %xmm8
        pxor	%xmm3, %xmm9
        pxor	%xmm3, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm7
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm7
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm7
        movdqa	%xmm7, 112(%rsp)
L_AES_GCM_decrypt_ghash_128:
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        movdqa	128(%rsp), %xmm8
        movdqa	L_aes_gcm_bswap_epi64(%rip), %xmm1
        movdqa	%xmm8, %xmm0
        pshufb	%xmm1, %xmm8
        movdqa	%xmm0, %xmm9
        paddd	L_aes_gcm_one(%rip), %xmm9
        pshufb	%xmm1, %xmm9
        movdqa	%xmm0, %xmm10
        paddd	L_aes_gcm_two(%rip), %xmm10
        pshufb	%xmm1, %xmm10
        movdqa	%xmm0, %xmm11
        paddd	L_aes_gcm_three(%rip), %xmm11
        pshufb	%xmm1, %xmm11
        movdqa	%xmm0, %xmm12
        paddd	L_aes_gcm_four(%rip), %xmm12
        pshufb	%xmm1, %xmm12
        movdqa	%xmm0, %xmm13
        paddd	L_aes_gcm_five(%rip), %xmm13
        pshufb	%xmm1, %xmm13
        movdqa	%xmm0, %xmm14
        paddd	L_aes_gcm_six(%rip), %xmm14
        pshufb	%xmm1, %xmm14
        movdqa	%xmm0, %xmm15
        paddd	L_aes_gcm_seven(%rip), %xmm15
        pshufb	%xmm1, %xmm15
        paddd	L_aes_gcm_eight(%rip), %xmm0
        movdqa	(%r15), %xmm7
        movdqa	%xmm0, 128(%rsp)
        pxor	%xmm7, %xmm8
        pxor	%xmm7, %xmm9
        pxor	%xmm7, %xmm10
        pxor	%xmm7, %xmm11
        pxor	%xmm7, %xmm12
        pxor	%xmm7, %xmm13
        pxor	%xmm7, %xmm14
        pxor	%xmm7, %xmm15
        movdqa	112(%rsp), %xmm7
        movdqu	(%rcx), %xmm0
        aesenc	16(%r15), %xmm8
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        pxor	%xmm2, %xmm0
        pshufd	$0x4e, %xmm7, %xmm1
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm7, %xmm1
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm3
        pclmulqdq	$0x11, %xmm7, %xmm3
        aesenc	16(%r15), %xmm9
        aesenc	16(%r15), %xmm10
        movdqa	%xmm0, %xmm2
        pclmulqdq	$0x00, %xmm7, %xmm2
        aesenc	16(%r15), %xmm11
        aesenc	16(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm1
        aesenc	16(%r15), %xmm13
        aesenc	16(%r15), %xmm14
        aesenc	16(%r15), %xmm15
        pxor	%xmm2, %xmm1
        pxor	%xmm3, %xmm1
        movdqa	96(%rsp), %xmm7
        movdqu	16(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	32(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	32(%r15), %xmm9
        aesenc	32(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	32(%r15), %xmm11
        aesenc	32(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	32(%r15), %xmm13
        aesenc	32(%r15), %xmm14
        aesenc	32(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	80(%rsp), %xmm7
        movdqu	32(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	48(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	48(%r15), %xmm9
        aesenc	48(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	48(%r15), %xmm11
        aesenc	48(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	48(%r15), %xmm13
        aesenc	48(%r15), %xmm14
        aesenc	48(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	64(%rsp), %xmm7
        movdqu	48(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	64(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	64(%r15), %xmm9
        aesenc	64(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	64(%r15), %xmm11
        aesenc	64(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	64(%r15), %xmm13
        aesenc	64(%r15), %xmm14
        aesenc	64(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	48(%rsp), %xmm7
        movdqu	64(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	80(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	80(%r15), %xmm9
        aesenc	80(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	80(%r15), %xmm11
        aesenc	80(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	80(%r15), %xmm13
        aesenc	80(%r15), %xmm14
        aesenc	80(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	32(%rsp), %xmm7
        movdqu	80(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	96(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	96(%r15), %xmm9
        aesenc	96(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	96(%r15), %xmm11
        aesenc	96(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	96(%r15), %xmm13
        aesenc	96(%r15), %xmm14
        aesenc	96(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	16(%rsp), %xmm7
        movdqu	96(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	112(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	112(%r15), %xmm9
        aesenc	112(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	112(%r15), %xmm11
        aesenc	112(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	112(%r15), %xmm13
        aesenc	112(%r15), %xmm14
        aesenc	112(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	(%rsp), %xmm7
        movdqu	112(%rcx), %xmm0
        pshufd	$0x4e, %xmm7, %xmm4
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm0
        aesenc	128(%r15), %xmm8
        pxor	%xmm7, %xmm4
        pshufd	$0x4e, %xmm0, %xmm5
        pxor	%xmm0, %xmm5
        movdqa	%xmm0, %xmm6
        pclmulqdq	$0x11, %xmm7, %xmm6
        aesenc	128(%r15), %xmm9
        aesenc	128(%r15), %xmm10
        pclmulqdq	$0x00, %xmm0, %xmm7
        aesenc	128(%r15), %xmm11
        aesenc	128(%r15), %xmm12
        pclmulqdq	$0x00, %xmm5, %xmm4
        aesenc	128(%r15), %xmm13
        aesenc	128(%r15), %xmm14
        aesenc	128(%r15), %xmm15
        pxor	%xmm7, %xmm1
        pxor	%xmm7, %xmm2
        pxor	%xmm6, %xmm1
        pxor	%xmm6, %xmm3
        pxor	%xmm4, %xmm1
        movdqa	%xmm1, %xmm5
        psrldq	$8, %xmm1
        pslldq	$8, %xmm5
        aesenc	144(%r15), %xmm8
        pxor	%xmm5, %xmm2
        pxor	%xmm1, %xmm3
        movdqa	%xmm2, %xmm7
        movdqa	%xmm2, %xmm4
        movdqa	%xmm2, %xmm5
        aesenc	144(%r15), %xmm9
        pslld	$31, %xmm7
        pslld	$30, %xmm4
        pslld	$25, %xmm5
        aesenc	144(%r15), %xmm10
        pxor	%xmm4, %xmm7
        pxor	%xmm5, %xmm7
        aesenc	144(%r15), %xmm11
        movdqa	%xmm7, %xmm4
        pslldq	$12, %xmm7
        psrldq	$4, %xmm4
        aesenc	144(%r15), %xmm12
        pxor	%xmm7, %xmm2
        movdqa	%xmm2, %xmm5
        movdqa	%xmm2, %xmm1
        movdqa	%xmm2, %xmm0
        aesenc	144(%r15), %xmm13
        psrld	$0x01, %xmm5
        psrld	$2, %xmm1
        psrld	$7, %xmm0
        aesenc	144(%r15), %xmm14
        pxor	%xmm1, %xmm5
        pxor	%xmm0, %xmm5
        aesenc	144(%r15), %xmm15
        pxor	%xmm4, %xmm5
        pxor	%xmm5, %xmm2
        pxor	%xmm3, %xmm2
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm7
        jl	L_AES_GCM_decrypt_aesenc_128_ghash_avx_done
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	176(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm7
        jl	L_AES_GCM_decrypt_aesenc_128_ghash_avx_done
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	208(%r15), %xmm7
        aesenc	%xmm7, %xmm8
        aesenc	%xmm7, %xmm9
        aesenc	%xmm7, %xmm10
        aesenc	%xmm7, %xmm11
        aesenc	%xmm7, %xmm12
        aesenc	%xmm7, %xmm13
        aesenc	%xmm7, %xmm14
        aesenc	%xmm7, %xmm15
        movdqa	224(%r15), %xmm7
L_AES_GCM_decrypt_aesenc_128_ghash_avx_done:
        aesenclast	%xmm7, %xmm8
        aesenclast	%xmm7, %xmm9
        movdqu	(%rcx), %xmm0
        movdqu	16(%rcx), %xmm1
        pxor	%xmm0, %xmm8
        pxor	%xmm1, %xmm9
        movdqu	%xmm8, (%rdx)
        movdqu	%xmm9, 16(%rdx)
        aesenclast	%xmm7, %xmm10
        aesenclast	%xmm7, %xmm11
        movdqu	32(%rcx), %xmm0
        movdqu	48(%rcx), %xmm1
        pxor	%xmm0, %xmm10
        pxor	%xmm1, %xmm11
        movdqu	%xmm10, 32(%rdx)
        movdqu	%xmm11, 48(%rdx)
        aesenclast	%xmm7, %xmm12
        aesenclast	%xmm7, %xmm13
        movdqu	64(%rcx), %xmm0
        movdqu	80(%rcx), %xmm1
        pxor	%xmm0, %xmm12
        pxor	%xmm1, %xmm13
        movdqu	%xmm12, 64(%rdx)
        movdqu	%xmm13, 80(%rdx)
        aesenclast	%xmm7, %xmm14
        aesenclast	%xmm7, %xmm15
        movdqu	96(%rcx), %xmm0
        movdqu	112(%rcx), %xmm1
        pxor	%xmm0, %xmm14
        pxor	%xmm1, %xmm15
        movdqu	%xmm14, 96(%rdx)
        movdqu	%xmm15, 112(%rdx)
        addl	$0x80, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_decrypt_ghash_128
        movdqa	%xmm2, %xmm6
        movdqa	(%rsp), %xmm5
L_AES_GCM_decrypt_done_128:
        movl	%r9d, %edx
        cmpl	%edx, %ebx
        jge	L_AES_GCM_decrypt_done_dec
        movl	%r9d, %r13d
        andl	$0xfffffff0, %r13d
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_decrypt_last_block_done
L_AES_GCM_decrypt_last_block_start:
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        movdqu	(%rcx), %xmm1
        movdqa	%xmm5, %xmm0
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm1
        pxor	%xmm6, %xmm1
        movdqa	128(%rsp), %xmm8
        movdqa	%xmm8, %xmm9
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm8
        paddd	L_aes_gcm_one(%rip), %xmm9
        pxor	(%r15), %xmm8
        movdqa	%xmm9, 128(%rsp)
        movdqa	%xmm1, %xmm10
        pclmulqdq	$16, %xmm0, %xmm10
        aesenc	16(%r15), %xmm8
        aesenc	32(%r15), %xmm8
        movdqa	%xmm1, %xmm11
        pclmulqdq	$0x01, %xmm0, %xmm11
        aesenc	48(%r15), %xmm8
        aesenc	64(%r15), %xmm8
        movdqa	%xmm1, %xmm12
        pclmulqdq	$0x00, %xmm0, %xmm12
        aesenc	80(%r15), %xmm8
        movdqa	%xmm1, %xmm1
        pclmulqdq	$0x11, %xmm0, %xmm1
        aesenc	96(%r15), %xmm8
        pxor	%xmm11, %xmm10
        movdqa	%xmm10, %xmm2
        psrldq	$8, %xmm10
        pslldq	$8, %xmm2
        aesenc	112(%r15), %xmm8
        movdqa	%xmm1, %xmm3
        pxor	%xmm12, %xmm2
        pxor	%xmm10, %xmm3
        movdqa	L_aes_gcm_mod2_128(%rip), %xmm0
        movdqa	%xmm2, %xmm11
        pclmulqdq	$16, %xmm0, %xmm11
        aesenc	128(%r15), %xmm8
        pshufd	$0x4e, %xmm2, %xmm10
        pxor	%xmm11, %xmm10
        movdqa	%xmm10, %xmm11
        pclmulqdq	$16, %xmm0, %xmm11
        aesenc	144(%r15), %xmm8
        pshufd	$0x4e, %xmm10, %xmm6
        pxor	%xmm11, %xmm6
        pxor	%xmm3, %xmm6
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_aesenc_gfmul_last
        aesenc	%xmm9, %xmm8
        aesenc	176(%r15), %xmm8
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_aesenc_gfmul_last
        aesenc	%xmm9, %xmm8
        aesenc	208(%r15), %xmm8
        movdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_aesenc_gfmul_last:
        aesenclast	%xmm9, %xmm8
        movdqu	(%rcx), %xmm9
        pxor	%xmm9, %xmm8
        movdqu	%xmm8, (%rdx)
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_decrypt_last_block_start
L_AES_GCM_decrypt_last_block_done:
        movl	%r9d, %ecx
        movl	%ecx, %edx
        andl	$15, %ecx
        jz	L_AES_GCM_decrypt_aesenc_last15_dec_avx_done
        movdqa	128(%rsp), %xmm4
        pshufb	L_aes_gcm_bswap_epi64(%rip), %xmm4
        pxor	(%r15), %xmm4
        aesenc	16(%r15), %xmm4
        aesenc	32(%r15), %xmm4
        aesenc	48(%r15), %xmm4
        aesenc	64(%r15), %xmm4
        aesenc	80(%r15), %xmm4
        aesenc	96(%r15), %xmm4
        aesenc	112(%r15), %xmm4
        aesenc	128(%r15), %xmm4
        aesenc	144(%r15), %xmm4
        cmpl	$11, %r10d
        movdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_aesenc_last15_dec_avx_aesenc_avx_last
        aesenc	%xmm9, %xmm4
        aesenc	176(%r15), %xmm4
        cmpl	$13, %r10d
        movdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_aesenc_last15_dec_avx_aesenc_avx_last
        aesenc	%xmm9, %xmm4
        aesenc	208(%r15), %xmm4
        movdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_aesenc_last15_dec_avx_aesenc_avx_last:
        aesenclast	%xmm9, %xmm4
        subq	$32, %rsp
        xorl	%ecx, %ecx
        movdqa	%xmm4, (%rsp)
        pxor	%xmm0, %xmm0
        movdqa	%xmm0, 16(%rsp)
L_AES_GCM_decrypt_aesenc_last15_dec_avx_loop:
        movzbl	(%rdi,%rbx,1), %r13d
        movb	%r13b, 16(%rsp,%rcx,1)
        xorb	(%rsp,%rcx,1), %r13b
        movb	%r13b, (%rsi,%rbx,1)
        incl	%ebx
        incl	%ecx
        cmpl	%edx, %ebx
        jl	L_AES_GCM_decrypt_aesenc_last15_dec_avx_loop
        movdqa	16(%rsp), %xmm4
        addq	$32, %rsp
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm4
        pxor	%xmm4, %xmm6
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm6, %xmm10
        movdqa	%xmm6, %xmm11
        movdqa	%xmm6, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm6, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm6
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm6
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm6
L_AES_GCM_decrypt_aesenc_last15_dec_avx_done:
L_AES_GCM_decrypt_done_dec:
        movl	%r9d, %edx
        movl	%r11d, %ecx
        shlq	$3, %rdx
        shlq	$3, %rcx
        pinsrq	$0x00, %rdx, %xmm0
        pinsrq	$0x01, %rcx, %xmm0
        pxor	%xmm0, %xmm6
        pshufd	$0x4e, %xmm5, %xmm9
        pshufd	$0x4e, %xmm6, %xmm10
        movdqa	%xmm6, %xmm11
        movdqa	%xmm6, %xmm8
        pclmulqdq	$0x11, %xmm5, %xmm11
        pclmulqdq	$0x00, %xmm5, %xmm8
        pxor	%xmm5, %xmm9
        pxor	%xmm6, %xmm10
        pclmulqdq	$0x00, %xmm10, %xmm9
        pxor	%xmm8, %xmm9
        pxor	%xmm11, %xmm9
        movdqa	%xmm9, %xmm10
        movdqa	%xmm11, %xmm6
        pslldq	$8, %xmm10
        psrldq	$8, %xmm9
        pxor	%xmm10, %xmm8
        pxor	%xmm9, %xmm6
        movdqa	%xmm8, %xmm12
        movdqa	%xmm8, %xmm13
        movdqa	%xmm8, %xmm14
        pslld	$31, %xmm12
        pslld	$30, %xmm13
        pslld	$25, %xmm14
        pxor	%xmm13, %xmm12
        pxor	%xmm14, %xmm12
        movdqa	%xmm12, %xmm13
        psrldq	$4, %xmm13
        pslldq	$12, %xmm12
        pxor	%xmm12, %xmm8
        movdqa	%xmm8, %xmm14
        movdqa	%xmm8, %xmm10
        movdqa	%xmm8, %xmm9
        psrld	$0x01, %xmm14
        psrld	$2, %xmm10
        psrld	$7, %xmm9
        pxor	%xmm10, %xmm14
        pxor	%xmm9, %xmm14
        pxor	%xmm13, %xmm14
        pxor	%xmm8, %xmm14
        pxor	%xmm14, %xmm6
        pshufb	L_aes_gcm_bswap_mask(%rip), %xmm6
        movdqa	144(%rsp), %xmm0
        pxor	%xmm6, %xmm0
        cmpl	$16, %r14d
        je	L_AES_GCM_decrypt_cmp_tag_16
        subq	$16, %rsp
        xorq	%rcx, %rcx
        xorq	%rbx, %rbx
        movdqa	%xmm0, (%rsp)
L_AES_GCM_decrypt_cmp_tag_loop:
        movzbl	(%rsp,%rcx,1), %r13d
        xorb	(%r8,%rcx,1), %r13b
        orb	%r13b, %bl
        incl	%ecx
        cmpl	%r14d, %ecx
        jne	L_AES_GCM_decrypt_cmp_tag_loop
        cmpb	$0x00, %bl
        sete	%bl
        addq	$16, %rsp
        xorq	%rcx, %rcx
        jmp	L_AES_GCM_decrypt_cmp_tag_done
L_AES_GCM_decrypt_cmp_tag_16:
        movdqu	(%r8), %xmm1
        pcmpeqb	%xmm1, %xmm0
        pmovmskb	%xmm0, %rdx
        # %%edx == 0xFFFF then return 1 else => return 0
        xorl	%ebx, %ebx
        cmpl	$0xffff, %edx
        sete	%bl
L_AES_GCM_decrypt_cmp_tag_done:
        movl	%ebx, (%rbp)
        addq	$0xa8, %rsp
        popq	%rbp
        popq	%r15
        popq	%r14
        popq	%rbx
        popq	%r12
        popq	%r13
        repz retq
#ifndef __APPLE__
.size	AES_GCM_decrypt,.-AES_GCM_decrypt
#endif /* __APPLE__ */
#ifdef HAVE_INTEL_AVX1
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_one:
.quad	0x0, 0x1
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_two:
.quad	0x0, 0x2
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_three:
.quad	0x0, 0x3
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_four:
.quad	0x0, 0x4
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_five:
.quad	0x0, 0x5
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_six:
.quad	0x0, 0x6
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_seven:
.quad	0x0, 0x7
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_eight:
.quad	0x0, 0x8
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_bswap_epi64:
.quad	0x1020304050607, 0x8090a0b0c0d0e0f
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_bswap_mask:
.quad	0x8090a0b0c0d0e0f, 0x1020304050607
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx1_aes_gcm_mod2_128:
.quad	0x1, 0xc200000000000000
#ifndef __APPLE__
.text
.globl	AES_GCM_encrypt_avx1
.type	AES_GCM_encrypt_avx1,@function
.align	4
AES_GCM_encrypt_avx1:
#else
.section	__TEXT,__text
.globl	_AES_GCM_encrypt_avx1
.p2align	2
_AES_GCM_encrypt_avx1:
#endif /* __APPLE__ */
        pushq	%r13
        pushq	%r12
        pushq	%rbx
        pushq	%r14
        pushq	%r15
        movq	%rdx, %r12
        movq	%rcx, %rax
        movl	48(%rsp), %r11d
        movl	56(%rsp), %ebx
        movl	64(%rsp), %r14d
        movq	72(%rsp), %r15
        movl	80(%rsp), %r10d
        subq	$0xa0, %rsp
        vpxor	%xmm4, %xmm4, %xmm4
        vpxor	%xmm6, %xmm6, %xmm6
        movl	%ebx, %edx
        cmpl	$12, %edx
        jne	L_AES_GCM_encrypt_avx1_iv_not_12
        # # Calculate values when IV is 12 bytes
        # Set counter based on IV
        movl	$0x1000000, %ecx
        vpinsrq	$0x00, (%rax), %xmm4, %xmm4
        vpinsrd	$2, 8(%rax), %xmm4, %xmm4
        vpinsrd	$3, %ecx, %xmm4, %xmm4
        # H = Encrypt X(=0) and T = Encrypt counter
        vmovdqa	(%r15), %xmm5
        vpxor	%xmm5, %xmm4, %xmm1
        vmovdqa	16(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	32(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	48(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	64(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	80(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	96(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	112(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	128(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	144(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm7
        jl	L_AES_GCM_encrypt_avx1_calc_iv_12_last
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	176(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm7
        jl	L_AES_GCM_encrypt_avx1_calc_iv_12_last
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	208(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	224(%r15), %xmm7
L_AES_GCM_encrypt_avx1_calc_iv_12_last:
        vaesenclast	%xmm7, %xmm5, %xmm5
        vaesenclast	%xmm7, %xmm1, %xmm1
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
        vmovdqa	%xmm1, 144(%rsp)
        jmp	L_AES_GCM_encrypt_avx1_iv_done
L_AES_GCM_encrypt_avx1_iv_not_12:
        # Calculate values when IV is not 12 bytes
        # H = Encrypt X(=0)
        vmovdqa	(%r15), %xmm5
        vaesenc	16(%r15), %xmm5, %xmm5
        vaesenc	32(%r15), %xmm5, %xmm5
        vaesenc	48(%r15), %xmm5, %xmm5
        vaesenc	64(%r15), %xmm5, %xmm5
        vaesenc	80(%r15), %xmm5, %xmm5
        vaesenc	96(%r15), %xmm5, %xmm5
        vaesenc	112(%r15), %xmm5, %xmm5
        vaesenc	128(%r15), %xmm5, %xmm5
        vaesenc	144(%r15), %xmm5, %xmm5
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm9, %xmm5, %xmm5
        vaesenc	176(%r15), %xmm5, %xmm5
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm9, %xmm5, %xmm5
        vaesenc	208(%r15), %xmm5, %xmm5
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_avx1_calc_iv_1_aesenc_avx_last:
        vaesenclast	%xmm9, %xmm5, %xmm5
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
        # Calc counter
        # Initialization vector
        cmpl	$0x00, %edx
        movq	$0x00, %rcx
        je	L_AES_GCM_encrypt_avx1_calc_iv_done
        cmpl	$16, %edx
        jl	L_AES_GCM_encrypt_avx1_calc_iv_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_encrypt_avx1_calc_iv_16_loop:
        vmovdqu	(%rax,%rcx,1), %xmm8
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm4, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpxor	%xmm4, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm4
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm4, %xmm4
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm4, %xmm4
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx1_calc_iv_16_loop
        movl	%ebx, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_encrypt_avx1_calc_iv_done
L_AES_GCM_encrypt_avx1_calc_iv_lt16:
        subq	$16, %rsp
        vpxor	%xmm8, %xmm8, %xmm8
        xorl	%ebx, %ebx
        vmovdqa	%xmm8, (%rsp)
L_AES_GCM_encrypt_avx1_calc_iv_loop:
        movzbl	(%rax,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx1_calc_iv_loop
        vmovdqa	(%rsp), %xmm8
        addq	$16, %rsp
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm4, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpxor	%xmm4, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm4
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm4, %xmm4
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm4, %xmm4
L_AES_GCM_encrypt_avx1_calc_iv_done:
        # T = Encrypt counter
        vpxor	%xmm0, %xmm0, %xmm0
        shll	$3, %edx
        vpinsrq	$0x00, %rdx, %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm4, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpxor	%xmm4, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm4
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm4, %xmm4
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm4, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        #   Encrypt counter
        vmovdqa	(%r15), %xmm8
        vpxor	%xmm4, %xmm8, %xmm8
        vaesenc	16(%r15), %xmm8, %xmm8
        vaesenc	32(%r15), %xmm8, %xmm8
        vaesenc	48(%r15), %xmm8, %xmm8
        vaesenc	64(%r15), %xmm8, %xmm8
        vaesenc	80(%r15), %xmm8, %xmm8
        vaesenc	96(%r15), %xmm8, %xmm8
        vaesenc	112(%r15), %xmm8, %xmm8
        vaesenc	128(%r15), %xmm8, %xmm8
        vaesenc	144(%r15), %xmm8, %xmm8
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	176(%r15), %xmm8, %xmm8
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	208(%r15), %xmm8, %xmm8
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_avx1_calc_iv_2_aesenc_avx_last:
        vaesenclast	%xmm9, %xmm8, %xmm8
        vmovdqa	%xmm8, 144(%rsp)
L_AES_GCM_encrypt_avx1_iv_done:
        # Additional authentication data
        movl	%r11d, %edx
        cmpl	$0x00, %edx
        je	L_AES_GCM_encrypt_avx1_calc_aad_done
        xorl	%ecx, %ecx
        cmpl	$16, %edx
        jl	L_AES_GCM_encrypt_avx1_calc_aad_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_encrypt_avx1_calc_aad_16_loop:
        vmovdqu	(%r12,%rcx,1), %xmm8
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm6, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm6, %xmm6
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm6, %xmm6
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx1_calc_aad_16_loop
        movl	%r11d, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_encrypt_avx1_calc_aad_done
L_AES_GCM_encrypt_avx1_calc_aad_lt16:
        subq	$16, %rsp
        vpxor	%xmm8, %xmm8, %xmm8
        xorl	%ebx, %ebx
        vmovdqa	%xmm8, (%rsp)
L_AES_GCM_encrypt_avx1_calc_aad_loop:
        movzbl	(%r12,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx1_calc_aad_loop
        vmovdqa	(%rsp), %xmm8
        addq	$16, %rsp
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm6, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm6, %xmm6
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm6, %xmm6
L_AES_GCM_encrypt_avx1_calc_aad_done:
        # Calculate counter and H
        vpsrlq	$63, %xmm5, %xmm9
        vpsllq	$0x01, %xmm5, %xmm8
        vpslldq	$8, %xmm9, %xmm9
        vpor	%xmm9, %xmm8, %xmm8
        vpshufd	$0xff, %xmm5, %xmm5
        vpsrad	$31, %xmm5, %xmm5
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpand	L_avx1_aes_gcm_mod2_128(%rip), %xmm5, %xmm5
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm4, %xmm4
        vpxor	%xmm8, %xmm5, %xmm5
        vmovdqa	%xmm4, 128(%rsp)
        xorl	%ebx, %ebx
        cmpl	$0x80, %r9d
        movl	%r9d, %r13d
        jl	L_AES_GCM_encrypt_avx1_done_128
        andl	$0xffffff80, %r13d
        vmovdqa	%xmm6, %xmm2
        # H ^ 1
        vmovdqa	%xmm5, (%rsp)
        # H ^ 2
        vpclmulqdq	$0x00, %xmm5, %xmm5, %xmm8
        vpclmulqdq	$0x11, %xmm5, %xmm5, %xmm0
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm0, %xmm0
        vmovdqa	%xmm0, 16(%rsp)
        # H ^ 3
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm0, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm0, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm0, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm0, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm1
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm1, %xmm1
        vmovdqa	%xmm1, 32(%rsp)
        # H ^ 4
        vpclmulqdq	$0x00, %xmm0, %xmm0, %xmm8
        vpclmulqdq	$0x11, %xmm0, %xmm0, %xmm3
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm3, %xmm3
        vmovdqa	%xmm3, 48(%rsp)
        # H ^ 5
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm0, %xmm9
        vpshufd	$0x4e, %xmm1, %xmm10
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm11
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm8
        vpxor	%xmm0, %xmm9, %xmm9
        vpxor	%xmm1, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 64(%rsp)
        # H ^ 6
        vpclmulqdq	$0x00, %xmm1, %xmm1, %xmm8
        vpclmulqdq	$0x11, %xmm1, %xmm1, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 80(%rsp)
        # H ^ 7
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm1, %xmm9
        vpshufd	$0x4e, %xmm3, %xmm10
        vpclmulqdq	$0x11, %xmm1, %xmm3, %xmm11
        vpclmulqdq	$0x00, %xmm1, %xmm3, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vpxor	%xmm3, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 96(%rsp)
        # H ^ 8
        vpclmulqdq	$0x00, %xmm3, %xmm3, %xmm8
        vpclmulqdq	$0x11, %xmm3, %xmm3, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 112(%rsp)
        # First 128 bytes of input
        vmovdqa	128(%rsp), %xmm0
        vmovdqa	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm1
        vpshufb	%xmm1, %xmm0, %xmm8
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm0, %xmm9
        vpshufb	%xmm1, %xmm9, %xmm9
        vpaddd	L_avx1_aes_gcm_two(%rip), %xmm0, %xmm10
        vpshufb	%xmm1, %xmm10, %xmm10
        vpaddd	L_avx1_aes_gcm_three(%rip), %xmm0, %xmm11
        vpshufb	%xmm1, %xmm11, %xmm11
        vpaddd	L_avx1_aes_gcm_four(%rip), %xmm0, %xmm12
        vpshufb	%xmm1, %xmm12, %xmm12
        vpaddd	L_avx1_aes_gcm_five(%rip), %xmm0, %xmm13
        vpshufb	%xmm1, %xmm13, %xmm13
        vpaddd	L_avx1_aes_gcm_six(%rip), %xmm0, %xmm14
        vpshufb	%xmm1, %xmm14, %xmm14
        vpaddd	L_avx1_aes_gcm_seven(%rip), %xmm0, %xmm15
        vpshufb	%xmm1, %xmm15, %xmm15
        vpaddd	L_avx1_aes_gcm_eight(%rip), %xmm0, %xmm0
        vmovdqa	(%r15), %xmm7
        vmovdqa	%xmm0, 128(%rsp)
        vpxor	%xmm7, %xmm8, %xmm8
        vpxor	%xmm7, %xmm9, %xmm9
        vpxor	%xmm7, %xmm10, %xmm10
        vpxor	%xmm7, %xmm11, %xmm11
        vpxor	%xmm7, %xmm12, %xmm12
        vpxor	%xmm7, %xmm13, %xmm13
        vpxor	%xmm7, %xmm14, %xmm14
        vpxor	%xmm7, %xmm15, %xmm15
        vmovdqa	16(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	32(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	48(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	64(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	80(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	96(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	112(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	128(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	144(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm7
        jl	L_AES_GCM_encrypt_avx1_aesenc_128_enc_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	176(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm7
        jl	L_AES_GCM_encrypt_avx1_aesenc_128_enc_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	208(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	224(%r15), %xmm7
L_AES_GCM_encrypt_avx1_aesenc_128_enc_done:
        vaesenclast	%xmm7, %xmm8, %xmm8
        vaesenclast	%xmm7, %xmm9, %xmm9
        vmovdqu	(%rdi), %xmm0
        vmovdqu	16(%rdi), %xmm1
        vpxor	%xmm0, %xmm8, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vmovdqu	%xmm8, (%rsi)
        vmovdqu	%xmm9, 16(%rsi)
        vaesenclast	%xmm7, %xmm10, %xmm10
        vaesenclast	%xmm7, %xmm11, %xmm11
        vmovdqu	32(%rdi), %xmm0
        vmovdqu	48(%rdi), %xmm1
        vpxor	%xmm0, %xmm10, %xmm10
        vpxor	%xmm1, %xmm11, %xmm11
        vmovdqu	%xmm10, 32(%rsi)
        vmovdqu	%xmm11, 48(%rsi)
        vaesenclast	%xmm7, %xmm12, %xmm12
        vaesenclast	%xmm7, %xmm13, %xmm13
        vmovdqu	64(%rdi), %xmm0
        vmovdqu	80(%rdi), %xmm1
        vpxor	%xmm0, %xmm12, %xmm12
        vpxor	%xmm1, %xmm13, %xmm13
        vmovdqu	%xmm12, 64(%rsi)
        vmovdqu	%xmm13, 80(%rsi)
        vaesenclast	%xmm7, %xmm14, %xmm14
        vaesenclast	%xmm7, %xmm15, %xmm15
        vmovdqu	96(%rdi), %xmm0
        vmovdqu	112(%rdi), %xmm1
        vpxor	%xmm0, %xmm14, %xmm14
        vpxor	%xmm1, %xmm15, %xmm15
        vmovdqu	%xmm14, 96(%rsi)
        vmovdqu	%xmm15, 112(%rsi)
        cmpl	$0x80, %r13d
        movl	$0x80, %ebx
        jle	L_AES_GCM_encrypt_avx1_end_128
        # More 128 bytes of input
L_AES_GCM_encrypt_avx1_ghash_128:
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        vmovdqa	128(%rsp), %xmm0
        vmovdqa	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm1
        vpshufb	%xmm1, %xmm0, %xmm8
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm0, %xmm9
        vpshufb	%xmm1, %xmm9, %xmm9
        vpaddd	L_avx1_aes_gcm_two(%rip), %xmm0, %xmm10
        vpshufb	%xmm1, %xmm10, %xmm10
        vpaddd	L_avx1_aes_gcm_three(%rip), %xmm0, %xmm11
        vpshufb	%xmm1, %xmm11, %xmm11
        vpaddd	L_avx1_aes_gcm_four(%rip), %xmm0, %xmm12
        vpshufb	%xmm1, %xmm12, %xmm12
        vpaddd	L_avx1_aes_gcm_five(%rip), %xmm0, %xmm13
        vpshufb	%xmm1, %xmm13, %xmm13
        vpaddd	L_avx1_aes_gcm_six(%rip), %xmm0, %xmm14
        vpshufb	%xmm1, %xmm14, %xmm14
        vpaddd	L_avx1_aes_gcm_seven(%rip), %xmm0, %xmm15
        vpshufb	%xmm1, %xmm15, %xmm15
        vpaddd	L_avx1_aes_gcm_eight(%rip), %xmm0, %xmm0
        vmovdqa	(%r15), %xmm7
        vmovdqa	%xmm0, 128(%rsp)
        vpxor	%xmm7, %xmm8, %xmm8
        vpxor	%xmm7, %xmm9, %xmm9
        vpxor	%xmm7, %xmm10, %xmm10
        vpxor	%xmm7, %xmm11, %xmm11
        vpxor	%xmm7, %xmm12, %xmm12
        vpxor	%xmm7, %xmm13, %xmm13
        vpxor	%xmm7, %xmm14, %xmm14
        vpxor	%xmm7, %xmm15, %xmm15
        vmovdqa	112(%rsp), %xmm7
        vmovdqu	-128(%rdx), %xmm0
        vaesenc	16(%r15), %xmm8, %xmm8
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm3
        vaesenc	16(%r15), %xmm9, %xmm9
        vaesenc	16(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm2
        vaesenc	16(%r15), %xmm11, %xmm11
        vaesenc	16(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm1, %xmm1
        vaesenc	16(%r15), %xmm13, %xmm13
        vaesenc	16(%r15), %xmm14, %xmm14
        vaesenc	16(%r15), %xmm15, %xmm15
        vpxor	%xmm2, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	96(%rsp), %xmm7
        vmovdqu	-112(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	32(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	32(%r15), %xmm9, %xmm9
        vaesenc	32(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	32(%r15), %xmm11, %xmm11
        vaesenc	32(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	32(%r15), %xmm13, %xmm13
        vaesenc	32(%r15), %xmm14, %xmm14
        vaesenc	32(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	80(%rsp), %xmm7
        vmovdqu	-96(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	48(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	48(%r15), %xmm9, %xmm9
        vaesenc	48(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	48(%r15), %xmm11, %xmm11
        vaesenc	48(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	48(%r15), %xmm13, %xmm13
        vaesenc	48(%r15), %xmm14, %xmm14
        vaesenc	48(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	64(%rsp), %xmm7
        vmovdqu	-80(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	64(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	64(%r15), %xmm9, %xmm9
        vaesenc	64(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	64(%r15), %xmm11, %xmm11
        vaesenc	64(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	64(%r15), %xmm13, %xmm13
        vaesenc	64(%r15), %xmm14, %xmm14
        vaesenc	64(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	48(%rsp), %xmm7
        vmovdqu	-64(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	80(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	80(%r15), %xmm9, %xmm9
        vaesenc	80(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	80(%r15), %xmm11, %xmm11
        vaesenc	80(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	80(%r15), %xmm13, %xmm13
        vaesenc	80(%r15), %xmm14, %xmm14
        vaesenc	80(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	32(%rsp), %xmm7
        vmovdqu	-48(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	96(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	96(%r15), %xmm9, %xmm9
        vaesenc	96(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	96(%r15), %xmm11, %xmm11
        vaesenc	96(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	96(%r15), %xmm13, %xmm13
        vaesenc	96(%r15), %xmm14, %xmm14
        vaesenc	96(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	16(%rsp), %xmm7
        vmovdqu	-32(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	112(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	112(%r15), %xmm9, %xmm9
        vaesenc	112(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	112(%r15), %xmm11, %xmm11
        vaesenc	112(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	112(%r15), %xmm13, %xmm13
        vaesenc	112(%r15), %xmm14, %xmm14
        vaesenc	112(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	(%rsp), %xmm7
        vmovdqu	-16(%rdx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	128(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	128(%r15), %xmm9, %xmm9
        vaesenc	128(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	128(%r15), %xmm11, %xmm11
        vaesenc	128(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	128(%r15), %xmm13, %xmm13
        vaesenc	128(%r15), %xmm14, %xmm14
        vaesenc	128(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vpslldq	$8, %xmm1, %xmm5
        vpsrldq	$8, %xmm1, %xmm1
        vaesenc	144(%r15), %xmm8, %xmm8
        vpxor	%xmm5, %xmm2, %xmm2
        vpxor	%xmm1, %xmm3, %xmm3
        vaesenc	144(%r15), %xmm9, %xmm9
        vpslld	$31, %xmm2, %xmm7
        vpslld	$30, %xmm2, %xmm4
        vpslld	$25, %xmm2, %xmm5
        vaesenc	144(%r15), %xmm10, %xmm10
        vpxor	%xmm4, %xmm7, %xmm7
        vpxor	%xmm5, %xmm7, %xmm7
        vaesenc	144(%r15), %xmm11, %xmm11
        vpsrldq	$4, %xmm7, %xmm4
        vpslldq	$12, %xmm7, %xmm7
        vaesenc	144(%r15), %xmm12, %xmm12
        vpxor	%xmm7, %xmm2, %xmm2
        vpsrld	$0x01, %xmm2, %xmm5
        vaesenc	144(%r15), %xmm13, %xmm13
        vpsrld	$2, %xmm2, %xmm1
        vpsrld	$7, %xmm2, %xmm0
        vaesenc	144(%r15), %xmm14, %xmm14
        vpxor	%xmm1, %xmm5, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vaesenc	144(%r15), %xmm15, %xmm15
        vpxor	%xmm4, %xmm5, %xmm5
        vpxor	%xmm5, %xmm2, %xmm2
        vpxor	%xmm3, %xmm2, %xmm2
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm7
        jl	L_AES_GCM_encrypt_avx1_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	176(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm7
        jl	L_AES_GCM_encrypt_avx1_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	208(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	224(%r15), %xmm7
L_AES_GCM_encrypt_avx1_aesenc_128_ghash_avx_done:
        vaesenclast	%xmm7, %xmm8, %xmm8
        vaesenclast	%xmm7, %xmm9, %xmm9
        vmovdqu	(%rcx), %xmm0
        vmovdqu	16(%rcx), %xmm1
        vpxor	%xmm0, %xmm8, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vmovdqu	%xmm8, (%rdx)
        vmovdqu	%xmm9, 16(%rdx)
        vaesenclast	%xmm7, %xmm10, %xmm10
        vaesenclast	%xmm7, %xmm11, %xmm11
        vmovdqu	32(%rcx), %xmm0
        vmovdqu	48(%rcx), %xmm1
        vpxor	%xmm0, %xmm10, %xmm10
        vpxor	%xmm1, %xmm11, %xmm11
        vmovdqu	%xmm10, 32(%rdx)
        vmovdqu	%xmm11, 48(%rdx)
        vaesenclast	%xmm7, %xmm12, %xmm12
        vaesenclast	%xmm7, %xmm13, %xmm13
        vmovdqu	64(%rcx), %xmm0
        vmovdqu	80(%rcx), %xmm1
        vpxor	%xmm0, %xmm12, %xmm12
        vpxor	%xmm1, %xmm13, %xmm13
        vmovdqu	%xmm12, 64(%rdx)
        vmovdqu	%xmm13, 80(%rdx)
        vaesenclast	%xmm7, %xmm14, %xmm14
        vaesenclast	%xmm7, %xmm15, %xmm15
        vmovdqu	96(%rcx), %xmm0
        vmovdqu	112(%rcx), %xmm1
        vpxor	%xmm0, %xmm14, %xmm14
        vpxor	%xmm1, %xmm15, %xmm15
        vmovdqu	%xmm14, 96(%rdx)
        vmovdqu	%xmm15, 112(%rdx)
        addl	$0x80, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_encrypt_avx1_ghash_128
L_AES_GCM_encrypt_avx1_end_128:
        vmovdqa	L_avx1_aes_gcm_bswap_mask(%rip), %xmm4
        vpshufb	%xmm4, %xmm8, %xmm8
        vpshufb	%xmm4, %xmm9, %xmm9
        vpshufb	%xmm4, %xmm10, %xmm10
        vpshufb	%xmm4, %xmm11, %xmm11
        vpxor	%xmm2, %xmm8, %xmm8
        vpshufb	%xmm4, %xmm12, %xmm12
        vpshufb	%xmm4, %xmm13, %xmm13
        vpshufb	%xmm4, %xmm14, %xmm14
        vpshufb	%xmm4, %xmm15, %xmm15
        vmovdqa	(%rsp), %xmm7
        vmovdqa	16(%rsp), %xmm5
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm15, %xmm1
        vpshufd	$0x4e, %xmm7, %xmm2
        vpclmulqdq	$0x11, %xmm15, %xmm7, %xmm3
        vpclmulqdq	$0x00, %xmm15, %xmm7, %xmm0
        vpxor	%xmm15, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm4
        vmovdqa	%xmm3, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm14, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm14, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm14, %xmm5, %xmm0
        vpxor	%xmm14, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        vmovdqa	32(%rsp), %xmm7
        vmovdqa	48(%rsp), %xmm5
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm13, %xmm1
        vpshufd	$0x4e, %xmm7, %xmm2
        vpclmulqdq	$0x11, %xmm13, %xmm7, %xmm3
        vpclmulqdq	$0x00, %xmm13, %xmm7, %xmm0
        vpxor	%xmm13, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm12, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm12, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm12, %xmm5, %xmm0
        vpxor	%xmm12, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        vmovdqa	64(%rsp), %xmm7
        vmovdqa	80(%rsp), %xmm5
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm11, %xmm1
        vpshufd	$0x4e, %xmm7, %xmm2
        vpclmulqdq	$0x11, %xmm11, %xmm7, %xmm3
        vpclmulqdq	$0x00, %xmm11, %xmm7, %xmm0
        vpxor	%xmm11, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm10, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm10, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm10, %xmm5, %xmm0
        vpxor	%xmm10, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        vmovdqa	96(%rsp), %xmm7
        vmovdqa	112(%rsp), %xmm5
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm9, %xmm1
        vpshufd	$0x4e, %xmm7, %xmm2
        vpclmulqdq	$0x11, %xmm9, %xmm7, %xmm3
        vpclmulqdq	$0x00, %xmm9, %xmm7, %xmm0
        vpxor	%xmm9, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        # ghash_gfmul_xor_avx
        vpshufd	$0x4e, %xmm8, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm8, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm8, %xmm5, %xmm0
        vpxor	%xmm8, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vpxor	%xmm0, %xmm4, %xmm4
        vpxor	%xmm3, %xmm6, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm4, %xmm4
        vpxor	%xmm1, %xmm6, %xmm6
        vpslld	$31, %xmm4, %xmm0
        vpslld	$30, %xmm4, %xmm1
        vpslld	$25, %xmm4, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        vpsrld	$0x01, %xmm4, %xmm2
        vpsrld	$2, %xmm4, %xmm3
        vpsrld	$7, %xmm4, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm4, %xmm2, %xmm2
        vpxor	%xmm2, %xmm6, %xmm6
        vmovdqa	(%rsp), %xmm5
L_AES_GCM_encrypt_avx1_done_128:
        movl	%r9d, %edx
        cmpl	%edx, %ebx
        jge	L_AES_GCM_encrypt_avx1_done_enc
        movl	%r9d, %r13d
        andl	$0xfffffff0, %r13d
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_encrypt_avx1_last_block_done
        vmovdqa	128(%rsp), %xmm9
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm9, %xmm8
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm9, %xmm9
        vmovdqa	%xmm9, 128(%rsp)
        vpxor	(%r15), %xmm8, %xmm8
        vaesenc	16(%r15), %xmm8, %xmm8
        vaesenc	32(%r15), %xmm8, %xmm8
        vaesenc	48(%r15), %xmm8, %xmm8
        vaesenc	64(%r15), %xmm8, %xmm8
        vaesenc	80(%r15), %xmm8, %xmm8
        vaesenc	96(%r15), %xmm8, %xmm8
        vaesenc	112(%r15), %xmm8, %xmm8
        vaesenc	128(%r15), %xmm8, %xmm8
        vaesenc	144(%r15), %xmm8, %xmm8
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_aesenc_block_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	176(%r15), %xmm8, %xmm8
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_aesenc_block_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	208(%r15), %xmm8, %xmm8
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_avx1_aesenc_block_last:
        vaesenclast	%xmm9, %xmm8, %xmm8
        vmovdqu	(%rdi,%rbx,1), %xmm9
        vpxor	%xmm9, %xmm8, %xmm8
        vmovdqu	%xmm8, (%rsi,%rbx,1)
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm6, %xmm6
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_encrypt_avx1_last_block_ghash
L_AES_GCM_encrypt_avx1_last_block_start:
        vmovdqu	(%rdi,%rbx,1), %xmm13
        vmovdqa	128(%rsp), %xmm9
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm9, %xmm8
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm9, %xmm9
        vmovdqa	%xmm9, 128(%rsp)
        vpxor	(%r15), %xmm8, %xmm8
        vpclmulqdq	$16, %xmm5, %xmm6, %xmm10
        vaesenc	16(%r15), %xmm8, %xmm8
        vaesenc	32(%r15), %xmm8, %xmm8
        vpclmulqdq	$0x01, %xmm5, %xmm6, %xmm11
        vaesenc	48(%r15), %xmm8, %xmm8
        vaesenc	64(%r15), %xmm8, %xmm8
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm12
        vaesenc	80(%r15), %xmm8, %xmm8
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm1
        vaesenc	96(%r15), %xmm8, %xmm8
        vpxor	%xmm11, %xmm10, %xmm10
        vpslldq	$8, %xmm10, %xmm2
        vpsrldq	$8, %xmm10, %xmm10
        vaesenc	112(%r15), %xmm8, %xmm8
        vpxor	%xmm12, %xmm2, %xmm2
        vpxor	%xmm10, %xmm1, %xmm3
        vmovdqa	L_avx1_aes_gcm_mod2_128(%rip), %xmm0
        vpclmulqdq	$16, %xmm0, %xmm2, %xmm11
        vaesenc	128(%r15), %xmm8, %xmm8
        vpshufd	$0x4e, %xmm2, %xmm10
        vpxor	%xmm11, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm0, %xmm10, %xmm11
        vaesenc	144(%r15), %xmm8, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpxor	%xmm11, %xmm10, %xmm10
        vpxor	%xmm3, %xmm10, %xmm6
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_aesenc_gfmul_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	176(%r15), %xmm8, %xmm8
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_aesenc_gfmul_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	208(%r15), %xmm8, %xmm8
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_avx1_aesenc_gfmul_last:
        vaesenclast	%xmm9, %xmm8, %xmm8
        vmovdqa	%xmm13, %xmm0
        vpxor	%xmm0, %xmm8, %xmm8
        vmovdqu	%xmm8, (%rsi,%rbx,1)
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        addl	$16, %ebx
        vpxor	%xmm8, %xmm6, %xmm6
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_encrypt_avx1_last_block_start
L_AES_GCM_encrypt_avx1_last_block_ghash:
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm6, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm6, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm6
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm6, %xmm6
L_AES_GCM_encrypt_avx1_last_block_done:
        movl	%r9d, %ecx
        movl	%ecx, %edx
        andl	$15, %ecx
        jz	L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_done
        vmovdqa	128(%rsp), %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpxor	(%r15), %xmm4, %xmm4
        vaesenc	16(%r15), %xmm4, %xmm4
        vaesenc	32(%r15), %xmm4, %xmm4
        vaesenc	48(%r15), %xmm4, %xmm4
        vaesenc	64(%r15), %xmm4, %xmm4
        vaesenc	80(%r15), %xmm4, %xmm4
        vaesenc	96(%r15), %xmm4, %xmm4
        vaesenc	112(%r15), %xmm4, %xmm4
        vaesenc	128(%r15), %xmm4, %xmm4
        vaesenc	144(%r15), %xmm4, %xmm4
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_aesenc_avx_last
        vaesenc	%xmm9, %xmm4, %xmm4
        vaesenc	176(%r15), %xmm4, %xmm4
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_aesenc_avx_last
        vaesenc	%xmm9, %xmm4, %xmm4
        vaesenc	208(%r15), %xmm4, %xmm4
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_aesenc_avx_last:
        vaesenclast	%xmm9, %xmm4, %xmm4
        subq	$16, %rsp
        xorl	%ecx, %ecx
        vmovdqa	%xmm4, (%rsp)
L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_loop:
        movzbl	(%rdi,%rbx,1), %r13d
        xorb	(%rsp,%rcx,1), %r13b
        movb	%r13b, (%rsi,%rbx,1)
        movb	%r13b, (%rsp,%rcx,1)
        incl	%ebx
        incl	%ecx
        cmpl	%edx, %ebx
        jl	L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_loop
        xorq	%r13, %r13
        cmpl	$16, %ecx
        je	L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_finish_enc
L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_byte_loop:
        movb	%r13b, (%rsp,%rcx,1)
        incl	%ecx
        cmpl	$16, %ecx
        jl	L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_byte_loop
L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_finish_enc:
        vmovdqa	(%rsp), %xmm4
        addq	$16, %rsp
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        vpxor	%xmm4, %xmm6, %xmm6
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm6, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm6, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm6
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm6, %xmm6
L_AES_GCM_encrypt_avx1_aesenc_last15_enc_avx_done:
L_AES_GCM_encrypt_avx1_done_enc:
        movl	%r9d, %edx
        movl	%r11d, %ecx
        shlq	$3, %rdx
        shlq	$3, %rcx
        vpinsrq	$0x00, %rdx, %xmm0, %xmm0
        vpinsrq	$0x01, %rcx, %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm6, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm6, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm6
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm6, %xmm6
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm6, %xmm6
        vpxor	144(%rsp), %xmm6, %xmm0
        cmpl	$16, %r14d
        je	L_AES_GCM_encrypt_avx1_store_tag_16
        xorq	%rcx, %rcx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_encrypt_avx1_store_tag_loop:
        movzbl	(%rsp,%rcx,1), %r13d
        movb	%r13b, (%r8,%rcx,1)
        incl	%ecx
        cmpl	%r14d, %ecx
        jne	L_AES_GCM_encrypt_avx1_store_tag_loop
        jmp	L_AES_GCM_encrypt_avx1_store_tag_done
L_AES_GCM_encrypt_avx1_store_tag_16:
        vmovdqu	%xmm0, (%r8)
L_AES_GCM_encrypt_avx1_store_tag_done:
        vzeroupper
        addq	$0xa0, %rsp
        popq	%r15
        popq	%r14
        popq	%rbx
        popq	%r12
        popq	%r13
        repz retq
#ifndef __APPLE__
.size	AES_GCM_encrypt_avx1,.-AES_GCM_encrypt_avx1
#endif /* __APPLE__ */
#ifndef __APPLE__
.text
.globl	AES_GCM_decrypt_avx1
.type	AES_GCM_decrypt_avx1,@function
.align	4
AES_GCM_decrypt_avx1:
#else
.section	__TEXT,__text
.globl	_AES_GCM_decrypt_avx1
.p2align	2
_AES_GCM_decrypt_avx1:
#endif /* __APPLE__ */
        pushq	%r13
        pushq	%r12
        pushq	%rbx
        pushq	%r14
        pushq	%r15
        pushq	%rbp
        movq	%rdx, %r12
        movq	%rcx, %rax
        movl	56(%rsp), %r11d
        movl	64(%rsp), %ebx
        movl	72(%rsp), %r14d
        movq	80(%rsp), %r15
        movl	88(%rsp), %r10d
        movq	96(%rsp), %rbp
        subq	$0xa8, %rsp
        vpxor	%xmm4, %xmm4, %xmm4
        vpxor	%xmm6, %xmm6, %xmm6
        cmpl	$12, %ebx
        movl	%ebx, %edx
        jne	L_AES_GCM_decrypt_avx1_iv_not_12
        # # Calculate values when IV is 12 bytes
        # Set counter based on IV
        movl	$0x1000000, %ecx
        vpinsrq	$0x00, (%rax), %xmm4, %xmm4
        vpinsrd	$2, 8(%rax), %xmm4, %xmm4
        vpinsrd	$3, %ecx, %xmm4, %xmm4
        # H = Encrypt X(=0) and T = Encrypt counter
        vmovdqa	(%r15), %xmm5
        vpxor	%xmm5, %xmm4, %xmm1
        vmovdqa	16(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	32(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	48(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	64(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	80(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	96(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	112(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	128(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	144(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm7
        jl	L_AES_GCM_decrypt_avx1_calc_iv_12_last
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	176(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm7
        jl	L_AES_GCM_decrypt_avx1_calc_iv_12_last
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	208(%r15), %xmm7
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm1, %xmm1
        vmovdqa	224(%r15), %xmm7
L_AES_GCM_decrypt_avx1_calc_iv_12_last:
        vaesenclast	%xmm7, %xmm5, %xmm5
        vaesenclast	%xmm7, %xmm1, %xmm1
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
        vmovdqa	%xmm1, 144(%rsp)
        jmp	L_AES_GCM_decrypt_avx1_iv_done
L_AES_GCM_decrypt_avx1_iv_not_12:
        # Calculate values when IV is not 12 bytes
        # H = Encrypt X(=0)
        vmovdqa	(%r15), %xmm5
        vaesenc	16(%r15), %xmm5, %xmm5
        vaesenc	32(%r15), %xmm5, %xmm5
        vaesenc	48(%r15), %xmm5, %xmm5
        vaesenc	64(%r15), %xmm5, %xmm5
        vaesenc	80(%r15), %xmm5, %xmm5
        vaesenc	96(%r15), %xmm5, %xmm5
        vaesenc	112(%r15), %xmm5, %xmm5
        vaesenc	128(%r15), %xmm5, %xmm5
        vaesenc	144(%r15), %xmm5, %xmm5
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm9, %xmm5, %xmm5
        vaesenc	176(%r15), %xmm5, %xmm5
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm9, %xmm5, %xmm5
        vaesenc	208(%r15), %xmm5, %xmm5
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_avx1_calc_iv_1_aesenc_avx_last:
        vaesenclast	%xmm9, %xmm5, %xmm5
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
        # Calc counter
        # Initialization vector
        cmpl	$0x00, %edx
        movq	$0x00, %rcx
        je	L_AES_GCM_decrypt_avx1_calc_iv_done
        cmpl	$16, %edx
        jl	L_AES_GCM_decrypt_avx1_calc_iv_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_decrypt_avx1_calc_iv_16_loop:
        vmovdqu	(%rax,%rcx,1), %xmm8
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm4, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpxor	%xmm4, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm4
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm4, %xmm4
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm4, %xmm4
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx1_calc_iv_16_loop
        movl	%ebx, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_decrypt_avx1_calc_iv_done
L_AES_GCM_decrypt_avx1_calc_iv_lt16:
        subq	$16, %rsp
        vpxor	%xmm8, %xmm8, %xmm8
        xorl	%ebx, %ebx
        vmovdqa	%xmm8, (%rsp)
L_AES_GCM_decrypt_avx1_calc_iv_loop:
        movzbl	(%rax,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx1_calc_iv_loop
        vmovdqa	(%rsp), %xmm8
        addq	$16, %rsp
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm4, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpxor	%xmm4, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm4
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm4, %xmm4
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm4, %xmm4
L_AES_GCM_decrypt_avx1_calc_iv_done:
        # T = Encrypt counter
        vpxor	%xmm0, %xmm0, %xmm0
        shll	$3, %edx
        vpinsrq	$0x00, %rdx, %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm4, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpxor	%xmm4, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm4
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm4, %xmm4
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm4, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        #   Encrypt counter
        vmovdqa	(%r15), %xmm8
        vpxor	%xmm4, %xmm8, %xmm8
        vaesenc	16(%r15), %xmm8, %xmm8
        vaesenc	32(%r15), %xmm8, %xmm8
        vaesenc	48(%r15), %xmm8, %xmm8
        vaesenc	64(%r15), %xmm8, %xmm8
        vaesenc	80(%r15), %xmm8, %xmm8
        vaesenc	96(%r15), %xmm8, %xmm8
        vaesenc	112(%r15), %xmm8, %xmm8
        vaesenc	128(%r15), %xmm8, %xmm8
        vaesenc	144(%r15), %xmm8, %xmm8
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	176(%r15), %xmm8, %xmm8
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	208(%r15), %xmm8, %xmm8
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_avx1_calc_iv_2_aesenc_avx_last:
        vaesenclast	%xmm9, %xmm8, %xmm8
        vmovdqa	%xmm8, 144(%rsp)
L_AES_GCM_decrypt_avx1_iv_done:
        # Additional authentication data
        movl	%r11d, %edx
        cmpl	$0x00, %edx
        je	L_AES_GCM_decrypt_avx1_calc_aad_done
        xorl	%ecx, %ecx
        cmpl	$16, %edx
        jl	L_AES_GCM_decrypt_avx1_calc_aad_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_decrypt_avx1_calc_aad_16_loop:
        vmovdqu	(%r12,%rcx,1), %xmm8
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm6, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm6, %xmm6
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm6, %xmm6
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx1_calc_aad_16_loop
        movl	%r11d, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_decrypt_avx1_calc_aad_done
L_AES_GCM_decrypt_avx1_calc_aad_lt16:
        subq	$16, %rsp
        vpxor	%xmm8, %xmm8, %xmm8
        xorl	%ebx, %ebx
        vmovdqa	%xmm8, (%rsp)
L_AES_GCM_decrypt_avx1_calc_aad_loop:
        movzbl	(%r12,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx1_calc_aad_loop
        vmovdqa	(%rsp), %xmm8
        addq	$16, %rsp
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm8, %xmm8
        vpxor	%xmm8, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpshufd	$0x4e, %xmm6, %xmm1
        vpshufd	$0x4e, %xmm5, %xmm2
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm5, %xmm2, %xmm2
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	%xmm0, %xmm7
        vmovdqa	%xmm3, %xmm6
        vpslldq	$8, %xmm1, %xmm2
        vpsrldq	$8, %xmm1, %xmm1
        vpxor	%xmm2, %xmm7, %xmm7
        vpxor	%xmm1, %xmm6, %xmm6
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        vpslld	$31, %xmm7, %xmm0
        vpslld	$30, %xmm7, %xmm1
        vpslld	$25, %xmm7, %xmm2
        vpxor	%xmm1, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm0, %xmm1
        vpsrldq	$4, %xmm1, %xmm1
        vpslldq	$12, %xmm0, %xmm0
        vpxor	%xmm0, %xmm7, %xmm7
        vpsrld	$0x01, %xmm7, %xmm2
        vpsrld	$2, %xmm7, %xmm3
        vpsrld	$7, %xmm7, %xmm0
        vpxor	%xmm3, %xmm2, %xmm2
        vpxor	%xmm0, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm2, %xmm6, %xmm6
L_AES_GCM_decrypt_avx1_calc_aad_done:
        # Calculate counter and H
        vpsrlq	$63, %xmm5, %xmm9
        vpsllq	$0x01, %xmm5, %xmm8
        vpslldq	$8, %xmm9, %xmm9
        vpor	%xmm9, %xmm8, %xmm8
        vpshufd	$0xff, %xmm5, %xmm5
        vpsrad	$31, %xmm5, %xmm5
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpand	L_avx1_aes_gcm_mod2_128(%rip), %xmm5, %xmm5
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm4, %xmm4
        vpxor	%xmm8, %xmm5, %xmm5
        vmovdqa	%xmm4, 128(%rsp)
        xorl	%ebx, %ebx
        cmpl	$0x80, %r9d
        movl	%r9d, %r13d
        jl	L_AES_GCM_decrypt_avx1_done_128
        andl	$0xffffff80, %r13d
        vmovdqa	%xmm6, %xmm2
        # H ^ 1
        vmovdqa	%xmm5, (%rsp)
        # H ^ 2
        vpclmulqdq	$0x00, %xmm5, %xmm5, %xmm8
        vpclmulqdq	$0x11, %xmm5, %xmm5, %xmm0
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm0, %xmm0
        vmovdqa	%xmm0, 16(%rsp)
        # H ^ 3
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm0, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm0, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm0, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm0, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm1
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm1, %xmm1
        vmovdqa	%xmm1, 32(%rsp)
        # H ^ 4
        vpclmulqdq	$0x00, %xmm0, %xmm0, %xmm8
        vpclmulqdq	$0x11, %xmm0, %xmm0, %xmm3
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm3, %xmm3
        vmovdqa	%xmm3, 48(%rsp)
        # H ^ 5
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm0, %xmm9
        vpshufd	$0x4e, %xmm1, %xmm10
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm11
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm8
        vpxor	%xmm0, %xmm9, %xmm9
        vpxor	%xmm1, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 64(%rsp)
        # H ^ 6
        vpclmulqdq	$0x00, %xmm1, %xmm1, %xmm8
        vpclmulqdq	$0x11, %xmm1, %xmm1, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 80(%rsp)
        # H ^ 7
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm1, %xmm9
        vpshufd	$0x4e, %xmm3, %xmm10
        vpclmulqdq	$0x11, %xmm1, %xmm3, %xmm11
        vpclmulqdq	$0x00, %xmm1, %xmm3, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vpxor	%xmm3, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 96(%rsp)
        # H ^ 8
        vpclmulqdq	$0x00, %xmm3, %xmm3, %xmm8
        vpclmulqdq	$0x11, %xmm3, %xmm3, %xmm7
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm7, %xmm7
        vmovdqa	%xmm7, 112(%rsp)
L_AES_GCM_decrypt_avx1_ghash_128:
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%rsi,%rbx,1), %rdx
        vmovdqa	128(%rsp), %xmm0
        vmovdqa	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm1
        vpshufb	%xmm1, %xmm0, %xmm8
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm0, %xmm9
        vpshufb	%xmm1, %xmm9, %xmm9
        vpaddd	L_avx1_aes_gcm_two(%rip), %xmm0, %xmm10
        vpshufb	%xmm1, %xmm10, %xmm10
        vpaddd	L_avx1_aes_gcm_three(%rip), %xmm0, %xmm11
        vpshufb	%xmm1, %xmm11, %xmm11
        vpaddd	L_avx1_aes_gcm_four(%rip), %xmm0, %xmm12
        vpshufb	%xmm1, %xmm12, %xmm12
        vpaddd	L_avx1_aes_gcm_five(%rip), %xmm0, %xmm13
        vpshufb	%xmm1, %xmm13, %xmm13
        vpaddd	L_avx1_aes_gcm_six(%rip), %xmm0, %xmm14
        vpshufb	%xmm1, %xmm14, %xmm14
        vpaddd	L_avx1_aes_gcm_seven(%rip), %xmm0, %xmm15
        vpshufb	%xmm1, %xmm15, %xmm15
        vpaddd	L_avx1_aes_gcm_eight(%rip), %xmm0, %xmm0
        vmovdqa	(%r15), %xmm7
        vmovdqa	%xmm0, 128(%rsp)
        vpxor	%xmm7, %xmm8, %xmm8
        vpxor	%xmm7, %xmm9, %xmm9
        vpxor	%xmm7, %xmm10, %xmm10
        vpxor	%xmm7, %xmm11, %xmm11
        vpxor	%xmm7, %xmm12, %xmm12
        vpxor	%xmm7, %xmm13, %xmm13
        vpxor	%xmm7, %xmm14, %xmm14
        vpxor	%xmm7, %xmm15, %xmm15
        vmovdqa	112(%rsp), %xmm7
        vmovdqu	(%rcx), %xmm0
        vaesenc	16(%r15), %xmm8, %xmm8
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm3
        vaesenc	16(%r15), %xmm9, %xmm9
        vaesenc	16(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm2
        vaesenc	16(%r15), %xmm11, %xmm11
        vaesenc	16(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm1, %xmm1
        vaesenc	16(%r15), %xmm13, %xmm13
        vaesenc	16(%r15), %xmm14, %xmm14
        vaesenc	16(%r15), %xmm15, %xmm15
        vpxor	%xmm2, %xmm1, %xmm1
        vpxor	%xmm3, %xmm1, %xmm1
        vmovdqa	96(%rsp), %xmm7
        vmovdqu	16(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	32(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	32(%r15), %xmm9, %xmm9
        vaesenc	32(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	32(%r15), %xmm11, %xmm11
        vaesenc	32(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	32(%r15), %xmm13, %xmm13
        vaesenc	32(%r15), %xmm14, %xmm14
        vaesenc	32(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	80(%rsp), %xmm7
        vmovdqu	32(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	48(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	48(%r15), %xmm9, %xmm9
        vaesenc	48(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	48(%r15), %xmm11, %xmm11
        vaesenc	48(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	48(%r15), %xmm13, %xmm13
        vaesenc	48(%r15), %xmm14, %xmm14
        vaesenc	48(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	64(%rsp), %xmm7
        vmovdqu	48(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	64(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	64(%r15), %xmm9, %xmm9
        vaesenc	64(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	64(%r15), %xmm11, %xmm11
        vaesenc	64(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	64(%r15), %xmm13, %xmm13
        vaesenc	64(%r15), %xmm14, %xmm14
        vaesenc	64(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	48(%rsp), %xmm7
        vmovdqu	64(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	80(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	80(%r15), %xmm9, %xmm9
        vaesenc	80(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	80(%r15), %xmm11, %xmm11
        vaesenc	80(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	80(%r15), %xmm13, %xmm13
        vaesenc	80(%r15), %xmm14, %xmm14
        vaesenc	80(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	32(%rsp), %xmm7
        vmovdqu	80(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	96(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	96(%r15), %xmm9, %xmm9
        vaesenc	96(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	96(%r15), %xmm11, %xmm11
        vaesenc	96(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	96(%r15), %xmm13, %xmm13
        vaesenc	96(%r15), %xmm14, %xmm14
        vaesenc	96(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	16(%rsp), %xmm7
        vmovdqu	96(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	112(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	112(%r15), %xmm9, %xmm9
        vaesenc	112(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	112(%r15), %xmm11, %xmm11
        vaesenc	112(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	112(%r15), %xmm13, %xmm13
        vaesenc	112(%r15), %xmm14, %xmm14
        vaesenc	112(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vmovdqa	(%rsp), %xmm7
        vmovdqu	112(%rcx), %xmm0
        vpshufd	$0x4e, %xmm7, %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vaesenc	128(%r15), %xmm8, %xmm8
        vpxor	%xmm7, %xmm4, %xmm4
        vpshufd	$0x4e, %xmm0, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vpclmulqdq	$0x11, %xmm7, %xmm0, %xmm6
        vaesenc	128(%r15), %xmm9, %xmm9
        vaesenc	128(%r15), %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm7, %xmm0, %xmm7
        vaesenc	128(%r15), %xmm11, %xmm11
        vaesenc	128(%r15), %xmm12, %xmm12
        vpclmulqdq	$0x00, %xmm5, %xmm4, %xmm4
        vaesenc	128(%r15), %xmm13, %xmm13
        vaesenc	128(%r15), %xmm14, %xmm14
        vaesenc	128(%r15), %xmm15, %xmm15
        vpxor	%xmm7, %xmm1, %xmm1
        vpxor	%xmm7, %xmm2, %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpxor	%xmm6, %xmm3, %xmm3
        vpxor	%xmm4, %xmm1, %xmm1
        vpslldq	$8, %xmm1, %xmm5
        vpsrldq	$8, %xmm1, %xmm1
        vaesenc	144(%r15), %xmm8, %xmm8
        vpxor	%xmm5, %xmm2, %xmm2
        vpxor	%xmm1, %xmm3, %xmm3
        vaesenc	144(%r15), %xmm9, %xmm9
        vpslld	$31, %xmm2, %xmm7
        vpslld	$30, %xmm2, %xmm4
        vpslld	$25, %xmm2, %xmm5
        vaesenc	144(%r15), %xmm10, %xmm10
        vpxor	%xmm4, %xmm7, %xmm7
        vpxor	%xmm5, %xmm7, %xmm7
        vaesenc	144(%r15), %xmm11, %xmm11
        vpsrldq	$4, %xmm7, %xmm4
        vpslldq	$12, %xmm7, %xmm7
        vaesenc	144(%r15), %xmm12, %xmm12
        vpxor	%xmm7, %xmm2, %xmm2
        vpsrld	$0x01, %xmm2, %xmm5
        vaesenc	144(%r15), %xmm13, %xmm13
        vpsrld	$2, %xmm2, %xmm1
        vpsrld	$7, %xmm2, %xmm0
        vaesenc	144(%r15), %xmm14, %xmm14
        vpxor	%xmm1, %xmm5, %xmm5
        vpxor	%xmm0, %xmm5, %xmm5
        vaesenc	144(%r15), %xmm15, %xmm15
        vpxor	%xmm4, %xmm5, %xmm5
        vpxor	%xmm5, %xmm2, %xmm2
        vpxor	%xmm3, %xmm2, %xmm2
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm7
        jl	L_AES_GCM_decrypt_avx1_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	176(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm7
        jl	L_AES_GCM_decrypt_avx1_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	208(%r15), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	224(%r15), %xmm7
L_AES_GCM_decrypt_avx1_aesenc_128_ghash_avx_done:
        vaesenclast	%xmm7, %xmm8, %xmm8
        vaesenclast	%xmm7, %xmm9, %xmm9
        vmovdqu	(%rcx), %xmm0
        vmovdqu	16(%rcx), %xmm1
        vpxor	%xmm0, %xmm8, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vmovdqu	%xmm8, (%rdx)
        vmovdqu	%xmm9, 16(%rdx)
        vaesenclast	%xmm7, %xmm10, %xmm10
        vaesenclast	%xmm7, %xmm11, %xmm11
        vmovdqu	32(%rcx), %xmm0
        vmovdqu	48(%rcx), %xmm1
        vpxor	%xmm0, %xmm10, %xmm10
        vpxor	%xmm1, %xmm11, %xmm11
        vmovdqu	%xmm10, 32(%rdx)
        vmovdqu	%xmm11, 48(%rdx)
        vaesenclast	%xmm7, %xmm12, %xmm12
        vaesenclast	%xmm7, %xmm13, %xmm13
        vmovdqu	64(%rcx), %xmm0
        vmovdqu	80(%rcx), %xmm1
        vpxor	%xmm0, %xmm12, %xmm12
        vpxor	%xmm1, %xmm13, %xmm13
        vmovdqu	%xmm12, 64(%rdx)
        vmovdqu	%xmm13, 80(%rdx)
        vaesenclast	%xmm7, %xmm14, %xmm14
        vaesenclast	%xmm7, %xmm15, %xmm15
        vmovdqu	96(%rcx), %xmm0
        vmovdqu	112(%rcx), %xmm1
        vpxor	%xmm0, %xmm14, %xmm14
        vpxor	%xmm1, %xmm15, %xmm15
        vmovdqu	%xmm14, 96(%rdx)
        vmovdqu	%xmm15, 112(%rdx)
        addl	$0x80, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_decrypt_avx1_ghash_128
        vmovdqa	%xmm2, %xmm6
        vmovdqa	(%rsp), %xmm5
L_AES_GCM_decrypt_avx1_done_128:
        movl	%r9d, %edx
        cmpl	%edx, %ebx
        jge	L_AES_GCM_decrypt_avx1_done_dec
        movl	%r9d, %r13d
        andl	$0xfffffff0, %r13d
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_decrypt_avx1_last_block_done
L_AES_GCM_decrypt_avx1_last_block_start:
        vmovdqu	(%rdi,%rbx,1), %xmm13
        vmovdqa	%xmm5, %xmm0
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm13, %xmm1
        vpxor	%xmm6, %xmm1, %xmm1
        vmovdqa	128(%rsp), %xmm9
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm9, %xmm8
        vpaddd	L_avx1_aes_gcm_one(%rip), %xmm9, %xmm9
        vmovdqa	%xmm9, 128(%rsp)
        vpxor	(%r15), %xmm8, %xmm8
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm10
        vaesenc	16(%r15), %xmm8, %xmm8
        vaesenc	32(%r15), %xmm8, %xmm8
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm11
        vaesenc	48(%r15), %xmm8, %xmm8
        vaesenc	64(%r15), %xmm8, %xmm8
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm12
        vaesenc	80(%r15), %xmm8, %xmm8
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vaesenc	96(%r15), %xmm8, %xmm8
        vpxor	%xmm11, %xmm10, %xmm10
        vpslldq	$8, %xmm10, %xmm2
        vpsrldq	$8, %xmm10, %xmm10
        vaesenc	112(%r15), %xmm8, %xmm8
        vpxor	%xmm12, %xmm2, %xmm2
        vpxor	%xmm10, %xmm1, %xmm3
        vmovdqa	L_avx1_aes_gcm_mod2_128(%rip), %xmm0
        vpclmulqdq	$16, %xmm0, %xmm2, %xmm11
        vaesenc	128(%r15), %xmm8, %xmm8
        vpshufd	$0x4e, %xmm2, %xmm10
        vpxor	%xmm11, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm0, %xmm10, %xmm11
        vaesenc	144(%r15), %xmm8, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpxor	%xmm11, %xmm10, %xmm10
        vpxor	%xmm3, %xmm10, %xmm6
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_aesenc_gfmul_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	176(%r15), %xmm8, %xmm8
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_aesenc_gfmul_last
        vaesenc	%xmm9, %xmm8, %xmm8
        vaesenc	208(%r15), %xmm8, %xmm8
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_avx1_aesenc_gfmul_last:
        vaesenclast	%xmm9, %xmm8, %xmm8
        vmovdqa	%xmm13, %xmm0
        vpxor	%xmm0, %xmm8, %xmm8
        vmovdqu	%xmm8, (%rsi,%rbx,1)
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_decrypt_avx1_last_block_start
L_AES_GCM_decrypt_avx1_last_block_done:
        movl	%r9d, %ecx
        movl	%ecx, %edx
        andl	$15, %ecx
        jz	L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_done
        vmovdqa	128(%rsp), %xmm4
        vpshufb	L_avx1_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpxor	(%r15), %xmm4, %xmm4
        vaesenc	16(%r15), %xmm4, %xmm4
        vaesenc	32(%r15), %xmm4, %xmm4
        vaesenc	48(%r15), %xmm4, %xmm4
        vaesenc	64(%r15), %xmm4, %xmm4
        vaesenc	80(%r15), %xmm4, %xmm4
        vaesenc	96(%r15), %xmm4, %xmm4
        vaesenc	112(%r15), %xmm4, %xmm4
        vaesenc	128(%r15), %xmm4, %xmm4
        vaesenc	144(%r15), %xmm4, %xmm4
        cmpl	$11, %r10d
        vmovdqa	160(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_aesenc_avx_last
        vaesenc	%xmm9, %xmm4, %xmm4
        vaesenc	176(%r15), %xmm4, %xmm4
        cmpl	$13, %r10d
        vmovdqa	192(%r15), %xmm9
        jl	L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_aesenc_avx_last
        vaesenc	%xmm9, %xmm4, %xmm4
        vaesenc	208(%r15), %xmm4, %xmm4
        vmovdqa	224(%r15), %xmm9
L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_aesenc_avx_last:
        vaesenclast	%xmm9, %xmm4, %xmm4
        subq	$32, %rsp
        xorl	%ecx, %ecx
        vmovdqa	%xmm4, (%rsp)
        vpxor	%xmm0, %xmm0, %xmm0
        vmovdqa	%xmm0, 16(%rsp)
L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_loop:
        movzbl	(%rdi,%rbx,1), %r13d
        movb	%r13b, 16(%rsp,%rcx,1)
        xorb	(%rsp,%rcx,1), %r13b
        movb	%r13b, (%rsi,%rbx,1)
        incl	%ebx
        incl	%ecx
        cmpl	%edx, %ebx
        jl	L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_loop
        vmovdqa	16(%rsp), %xmm4
        addq	$32, %rsp
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        vpxor	%xmm4, %xmm6, %xmm6
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm6, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm6, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm6
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm6, %xmm6
L_AES_GCM_decrypt_avx1_aesenc_last15_dec_avx_done:
L_AES_GCM_decrypt_avx1_done_dec:
        movl	%r9d, %edx
        movl	%r11d, %ecx
        shlq	$3, %rdx
        shlq	$3, %rcx
        vpinsrq	$0x00, %rdx, %xmm0, %xmm0
        vpinsrq	$0x01, %rcx, %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        # ghash_gfmul_red_avx
        vpshufd	$0x4e, %xmm5, %xmm9
        vpshufd	$0x4e, %xmm6, %xmm10
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm11
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm8
        vpxor	%xmm5, %xmm9, %xmm9
        vpxor	%xmm6, %xmm10, %xmm10
        vpclmulqdq	$0x00, %xmm10, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm11, %xmm9, %xmm9
        vpslldq	$8, %xmm9, %xmm10
        vpsrldq	$8, %xmm9, %xmm9
        vpxor	%xmm10, %xmm8, %xmm8
        vpxor	%xmm9, %xmm11, %xmm6
        vpslld	$31, %xmm8, %xmm12
        vpslld	$30, %xmm8, %xmm13
        vpslld	$25, %xmm8, %xmm14
        vpxor	%xmm13, %xmm12, %xmm12
        vpxor	%xmm14, %xmm12, %xmm12
        vpsrldq	$4, %xmm12, %xmm13
        vpslldq	$12, %xmm12, %xmm12
        vpxor	%xmm12, %xmm8, %xmm8
        vpsrld	$0x01, %xmm8, %xmm14
        vpsrld	$2, %xmm8, %xmm10
        vpsrld	$7, %xmm8, %xmm9
        vpxor	%xmm10, %xmm14, %xmm14
        vpxor	%xmm9, %xmm14, %xmm14
        vpxor	%xmm13, %xmm14, %xmm14
        vpxor	%xmm8, %xmm14, %xmm14
        vpxor	%xmm14, %xmm6, %xmm6
        vpshufb	L_avx1_aes_gcm_bswap_mask(%rip), %xmm6, %xmm6
        vpxor	144(%rsp), %xmm6, %xmm0
        cmpl	$16, %r14d
        je	L_AES_GCM_decrypt_avx1_cmp_tag_16
        subq	$16, %rsp
        xorq	%rcx, %rcx
        xorq	%rbx, %rbx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_decrypt_avx1_cmp_tag_loop:
        movzbl	(%rsp,%rcx,1), %r13d
        xorb	(%r8,%rcx,1), %r13b
        orb	%r13b, %bl
        incl	%ecx
        cmpl	%r14d, %ecx
        jne	L_AES_GCM_decrypt_avx1_cmp_tag_loop
        cmpb	$0x00, %bl
        sete	%bl
        addq	$16, %rsp
        xorq	%rcx, %rcx
        jmp	L_AES_GCM_decrypt_avx1_cmp_tag_done
L_AES_GCM_decrypt_avx1_cmp_tag_16:
        vmovdqu	(%r8), %xmm1
        vpcmpeqb	%xmm1, %xmm0, %xmm0
        vpmovmskb	%xmm0, %rdx
        # %%edx == 0xFFFF then return 1 else => return 0
        xorl	%ebx, %ebx
        cmpl	$0xffff, %edx
        sete	%bl
L_AES_GCM_decrypt_avx1_cmp_tag_done:
        movl	%ebx, (%rbp)
        vzeroupper
        addq	$0xa8, %rsp
        popq	%rbp
        popq	%r15
        popq	%r14
        popq	%rbx
        popq	%r12
        popq	%r13
        repz retq
#ifndef __APPLE__
.size	AES_GCM_decrypt_avx1,.-AES_GCM_decrypt_avx1
#endif /* __APPLE__ */
#endif /* HAVE_INTEL_AVX1 */
#ifdef HAVE_INTEL_AVX2
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_one:
.quad	0x0, 0x1
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_two:
.quad	0x0, 0x2
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_three:
.quad	0x0, 0x3
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_four:
.quad	0x0, 0x4
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_five:
.quad	0x0, 0x5
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_six:
.quad	0x0, 0x6
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_seven:
.quad	0x0, 0x7
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_eight:
.quad	0x0, 0x8
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_bswap_one:
.quad	0x0, 0x100000000000000
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_bswap_epi64:
.quad	0x1020304050607, 0x8090a0b0c0d0e0f
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_bswap_mask:
.quad	0x8090a0b0c0d0e0f, 0x1020304050607
#ifndef __APPLE__
.data
#else
.section	__DATA,__data
#endif /* __APPLE__ */
#ifndef __APPLE__
.align	16
#else
.p2align	4
#endif /* __APPLE__ */
L_avx2_aes_gcm_mod2_128:
.quad	0x1, 0xc200000000000000
#ifndef __APPLE__
.text
.globl	AES_GCM_encrypt_avx2
.type	AES_GCM_encrypt_avx2,@function
.align	4
AES_GCM_encrypt_avx2:
#else
.section	__TEXT,__text
.globl	_AES_GCM_encrypt_avx2
.p2align	2
_AES_GCM_encrypt_avx2:
#endif /* __APPLE__ */
        pushq	%r13
        pushq	%r12
        pushq	%r15
        pushq	%rbx
        pushq	%r14
        movq	%rdx, %r12
        movq	%rcx, %rax
        movq	%r8, %r15
        movq	%rsi, %r8
        movl	%r9d, %r10d
        movl	48(%rsp), %r11d
        movl	56(%rsp), %ebx
        movl	64(%rsp), %r14d
        movq	72(%rsp), %rsi
        movl	80(%rsp), %r9d
        subq	$0xa0, %rsp
        vpxor	%xmm4, %xmm4, %xmm4
        vpxor	%xmm6, %xmm6, %xmm6
        movl	%ebx, %edx
        cmpl	$12, %edx
        je	L_AES_GCM_encrypt_avx2_iv_12
        # Calculate values when IV is not 12 bytes
        # H = Encrypt X(=0)
        vmovdqa	(%rsi), %xmm5
        vaesenc	16(%rsi), %xmm5, %xmm5
        vaesenc	32(%rsi), %xmm5, %xmm5
        vaesenc	48(%rsi), %xmm5, %xmm5
        vaesenc	64(%rsi), %xmm5, %xmm5
        vaesenc	80(%rsi), %xmm5, %xmm5
        vaesenc	96(%rsi), %xmm5, %xmm5
        vaesenc	112(%rsi), %xmm5, %xmm5
        vaesenc	128(%rsi), %xmm5, %xmm5
        vaesenc	144(%rsi), %xmm5, %xmm5
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	176(%rsi), %xmm5, %xmm5
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	208(%rsi), %xmm5, %xmm5
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_encrypt_avx2_calc_iv_1_aesenc_avx_last:
        vaesenclast	%xmm0, %xmm5, %xmm5
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
        # Calc counter
        # Initialization vector
        cmpl	$0x00, %edx
        movq	$0x00, %rcx
        je	L_AES_GCM_encrypt_avx2_calc_iv_done
        cmpl	$16, %edx
        jl	L_AES_GCM_encrypt_avx2_calc_iv_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_encrypt_avx2_calc_iv_16_loop:
        vmovdqu	(%rax,%rcx,1), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm4, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm4, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm4
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm4, %xmm4
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx2_calc_iv_16_loop
        movl	%ebx, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_encrypt_avx2_calc_iv_done
L_AES_GCM_encrypt_avx2_calc_iv_lt16:
        vpxor	%xmm0, %xmm0, %xmm0
        xorl	%ebx, %ebx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_encrypt_avx2_calc_iv_loop:
        movzbl	(%rax,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx2_calc_iv_loop
        vmovdqa	(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm4, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm4, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm4
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm4, %xmm4
L_AES_GCM_encrypt_avx2_calc_iv_done:
        # T = Encrypt counter
        vpxor	%xmm0, %xmm0, %xmm0
        shll	$3, %edx
        vpinsrq	$0x00, %rdx, %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm4, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm4, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm4
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm4, %xmm4
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        #   Encrypt counter
        vmovdqa	(%rsi), %xmm15
        vpxor	%xmm4, %xmm15, %xmm15
        vaesenc	16(%rsi), %xmm15, %xmm15
        vaesenc	32(%rsi), %xmm15, %xmm15
        vaesenc	48(%rsi), %xmm15, %xmm15
        vaesenc	64(%rsi), %xmm15, %xmm15
        vaesenc	80(%rsi), %xmm15, %xmm15
        vaesenc	96(%rsi), %xmm15, %xmm15
        vaesenc	112(%rsi), %xmm15, %xmm15
        vaesenc	128(%rsi), %xmm15, %xmm15
        vaesenc	144(%rsi), %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm0, %xmm15, %xmm15
        vaesenc	176(%rsi), %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm0, %xmm15, %xmm15
        vaesenc	208(%rsi), %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_encrypt_avx2_calc_iv_2_aesenc_avx_last:
        vaesenclast	%xmm0, %xmm15, %xmm15
        jmp	L_AES_GCM_encrypt_avx2_iv_done
L_AES_GCM_encrypt_avx2_iv_12:
        # # Calculate values when IV is 12 bytes
        # Set counter based on IV
        vmovdqa	L_avx2_aes_gcm_bswap_one(%rip), %xmm4
        vmovdqa	(%rsi), %xmm5
        vpblendd	$7, (%rax), %xmm4, %xmm4
        # H = Encrypt X(=0) and T = Encrypt counter
        vmovdqa	16(%rsi), %xmm7
        vpxor	%xmm5, %xmm4, %xmm15
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	32(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	48(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	64(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	80(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	96(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	112(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	128(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	144(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_calc_iv_12_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	176(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_calc_iv_12_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	208(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_encrypt_avx2_calc_iv_12_last:
        vaesenclast	%xmm0, %xmm5, %xmm5
        vaesenclast	%xmm0, %xmm15, %xmm15
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
L_AES_GCM_encrypt_avx2_iv_done:
        # Additional authentication data
        movl	%r11d, %edx
        cmpl	$0x00, %edx
        je	L_AES_GCM_encrypt_avx2_calc_aad_done
        xorl	%ecx, %ecx
        cmpl	$16, %edx
        jl	L_AES_GCM_encrypt_avx2_calc_aad_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_encrypt_avx2_calc_aad_16_loop:
        vmovdqu	(%r12,%rcx,1), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm6, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm6, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm6
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm6, %xmm6
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx2_calc_aad_16_loop
        movl	%r11d, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_encrypt_avx2_calc_aad_done
L_AES_GCM_encrypt_avx2_calc_aad_lt16:
        vpxor	%xmm0, %xmm0, %xmm0
        xorl	%ebx, %ebx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_encrypt_avx2_calc_aad_loop:
        movzbl	(%r12,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_encrypt_avx2_calc_aad_loop
        vmovdqa	(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm6, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm6, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm6
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm6, %xmm6
L_AES_GCM_encrypt_avx2_calc_aad_done:
        # Calculate counter and H
        vpsrlq	$63, %xmm5, %xmm1
        vpsllq	$0x01, %xmm5, %xmm0
        vpslldq	$8, %xmm1, %xmm1
        vpor	%xmm1, %xmm0, %xmm0
        vpshufd	$0xff, %xmm5, %xmm5
        vpsrad	$31, %xmm5, %xmm5
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpand	L_avx2_aes_gcm_mod2_128(%rip), %xmm5, %xmm5
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm4, %xmm4
        vpxor	%xmm0, %xmm5, %xmm5
        xorl	%ebx, %ebx
        cmpl	$0x80, %r10d
        movl	%r10d, %r13d
        jl	L_AES_GCM_encrypt_avx2_done_128
        andl	$0xffffff80, %r13d
        vmovdqa	%xmm4, 128(%rsp)
        vmovdqa	%xmm15, 144(%rsp)
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm3
        # H ^ 1 and H ^ 2
        vpclmulqdq	$0x00, %xmm5, %xmm5, %xmm9
        vpclmulqdq	$0x11, %xmm5, %xmm5, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm9, %xmm8
        vpshufd	$0x4e, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm9, %xmm8
        vpshufd	$0x4e, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm9, %xmm10, %xmm0
        vmovdqa	%xmm5, (%rsp)
        vmovdqa	%xmm0, 16(%rsp)
        # H ^ 3 and H ^ 4
        vpclmulqdq	$16, %xmm5, %xmm0, %xmm11
        vpclmulqdq	$0x01, %xmm5, %xmm0, %xmm10
        vpclmulqdq	$0x00, %xmm5, %xmm0, %xmm9
        vpclmulqdq	$0x11, %xmm5, %xmm0, %xmm12
        vpclmulqdq	$0x00, %xmm0, %xmm0, %xmm13
        vpclmulqdq	$0x11, %xmm0, %xmm0, %xmm14
        vpxor	%xmm10, %xmm11, %xmm11
        vpslldq	$8, %xmm11, %xmm10
        vpsrldq	$8, %xmm11, %xmm11
        vpxor	%xmm9, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm9, %xmm10, %xmm10
        vpxor	%xmm8, %xmm13, %xmm13
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm11, %xmm12, %xmm12
        vpxor	%xmm8, %xmm13, %xmm13
        vpxor	%xmm12, %xmm10, %xmm10
        vpxor	%xmm14, %xmm13, %xmm2
        vpxor	%xmm9, %xmm10, %xmm1
        vmovdqa	%xmm1, 32(%rsp)
        vmovdqa	%xmm2, 48(%rsp)
        # H ^ 5 and H ^ 6
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm11
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm10
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm9
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm12
        vpclmulqdq	$0x00, %xmm1, %xmm1, %xmm13
        vpclmulqdq	$0x11, %xmm1, %xmm1, %xmm14
        vpxor	%xmm10, %xmm11, %xmm11
        vpslldq	$8, %xmm11, %xmm10
        vpsrldq	$8, %xmm11, %xmm11
        vpxor	%xmm9, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm9, %xmm10, %xmm10
        vpxor	%xmm8, %xmm13, %xmm13
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm11, %xmm12, %xmm12
        vpxor	%xmm8, %xmm13, %xmm13
        vpxor	%xmm12, %xmm10, %xmm10
        vpxor	%xmm14, %xmm13, %xmm0
        vpxor	%xmm9, %xmm10, %xmm7
        vmovdqa	%xmm7, 64(%rsp)
        vmovdqa	%xmm0, 80(%rsp)
        # H ^ 7 and H ^ 8
        vpclmulqdq	$16, %xmm1, %xmm2, %xmm11
        vpclmulqdq	$0x01, %xmm1, %xmm2, %xmm10
        vpclmulqdq	$0x00, %xmm1, %xmm2, %xmm9
        vpclmulqdq	$0x11, %xmm1, %xmm2, %xmm12
        vpclmulqdq	$0x00, %xmm2, %xmm2, %xmm13
        vpclmulqdq	$0x11, %xmm2, %xmm2, %xmm14
        vpxor	%xmm10, %xmm11, %xmm11
        vpslldq	$8, %xmm11, %xmm10
        vpsrldq	$8, %xmm11, %xmm11
        vpxor	%xmm9, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm9, %xmm10, %xmm10
        vpxor	%xmm8, %xmm13, %xmm13
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm11, %xmm12, %xmm12
        vpxor	%xmm8, %xmm13, %xmm13
        vpxor	%xmm12, %xmm10, %xmm10
        vpxor	%xmm14, %xmm13, %xmm0
        vpxor	%xmm9, %xmm10, %xmm7
        vmovdqa	%xmm7, 96(%rsp)
        vmovdqa	%xmm0, 112(%rsp)
        # First 128 bytes of input
        # aesenc_128
        # aesenc_ctr
        vmovdqa	128(%rsp), %xmm0
        vmovdqa	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm1
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm0, %xmm9
        vpshufb	%xmm1, %xmm0, %xmm8
        vpaddd	L_avx2_aes_gcm_two(%rip), %xmm0, %xmm10
        vpshufb	%xmm1, %xmm9, %xmm9
        vpaddd	L_avx2_aes_gcm_three(%rip), %xmm0, %xmm11
        vpshufb	%xmm1, %xmm10, %xmm10
        vpaddd	L_avx2_aes_gcm_four(%rip), %xmm0, %xmm12
        vpshufb	%xmm1, %xmm11, %xmm11
        vpaddd	L_avx2_aes_gcm_five(%rip), %xmm0, %xmm13
        vpshufb	%xmm1, %xmm12, %xmm12
        vpaddd	L_avx2_aes_gcm_six(%rip), %xmm0, %xmm14
        vpshufb	%xmm1, %xmm13, %xmm13
        vpaddd	L_avx2_aes_gcm_seven(%rip), %xmm0, %xmm15
        vpshufb	%xmm1, %xmm14, %xmm14
        vpaddd	L_avx2_aes_gcm_eight(%rip), %xmm0, %xmm0
        vpshufb	%xmm1, %xmm15, %xmm15
        # aesenc_xor
        vmovdqa	(%rsi), %xmm7
        vmovdqa	%xmm0, 128(%rsp)
        vpxor	%xmm7, %xmm8, %xmm8
        vpxor	%xmm7, %xmm9, %xmm9
        vpxor	%xmm7, %xmm10, %xmm10
        vpxor	%xmm7, %xmm11, %xmm11
        vpxor	%xmm7, %xmm12, %xmm12
        vpxor	%xmm7, %xmm13, %xmm13
        vpxor	%xmm7, %xmm14, %xmm14
        vpxor	%xmm7, %xmm15, %xmm15
        vmovdqa	16(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	32(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	48(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	64(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	80(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	96(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	112(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	128(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	144(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm7
        jl	L_AES_GCM_encrypt_avx2_aesenc_128_enc_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	176(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm7
        jl	L_AES_GCM_encrypt_avx2_aesenc_128_enc_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	208(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm7
L_AES_GCM_encrypt_avx2_aesenc_128_enc_done:
        # aesenc_last
        vaesenclast	%xmm7, %xmm8, %xmm8
        vaesenclast	%xmm7, %xmm9, %xmm9
        vaesenclast	%xmm7, %xmm10, %xmm10
        vaesenclast	%xmm7, %xmm11, %xmm11
        vmovdqu	(%rdi), %xmm0
        vmovdqu	16(%rdi), %xmm1
        vmovdqu	32(%rdi), %xmm2
        vmovdqu	48(%rdi), %xmm3
        vpxor	%xmm0, %xmm8, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vpxor	%xmm2, %xmm10, %xmm10
        vpxor	%xmm3, %xmm11, %xmm11
        vmovdqu	%xmm8, (%r8)
        vmovdqu	%xmm9, 16(%r8)
        vmovdqu	%xmm10, 32(%r8)
        vmovdqu	%xmm11, 48(%r8)
        vaesenclast	%xmm7, %xmm12, %xmm12
        vaesenclast	%xmm7, %xmm13, %xmm13
        vaesenclast	%xmm7, %xmm14, %xmm14
        vaesenclast	%xmm7, %xmm15, %xmm15
        vmovdqu	64(%rdi), %xmm0
        vmovdqu	80(%rdi), %xmm1
        vmovdqu	96(%rdi), %xmm2
        vmovdqu	112(%rdi), %xmm3
        vpxor	%xmm0, %xmm12, %xmm12
        vpxor	%xmm1, %xmm13, %xmm13
        vpxor	%xmm2, %xmm14, %xmm14
        vpxor	%xmm3, %xmm15, %xmm15
        vmovdqu	%xmm12, 64(%r8)
        vmovdqu	%xmm13, 80(%r8)
        vmovdqu	%xmm14, 96(%r8)
        vmovdqu	%xmm15, 112(%r8)
        cmpl	$0x80, %r13d
        movl	$0x80, %ebx
        jle	L_AES_GCM_encrypt_avx2_end_128
        # More 128 bytes of input
L_AES_GCM_encrypt_avx2_ghash_128:
        # aesenc_128_ghash
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%r8,%rbx,1), %rdx
        # aesenc_ctr
        vmovdqa	128(%rsp), %xmm0
        vmovdqa	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm1
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm0, %xmm9
        vpshufb	%xmm1, %xmm0, %xmm8
        vpaddd	L_avx2_aes_gcm_two(%rip), %xmm0, %xmm10
        vpshufb	%xmm1, %xmm9, %xmm9
        vpaddd	L_avx2_aes_gcm_three(%rip), %xmm0, %xmm11
        vpshufb	%xmm1, %xmm10, %xmm10
        vpaddd	L_avx2_aes_gcm_four(%rip), %xmm0, %xmm12
        vpshufb	%xmm1, %xmm11, %xmm11
        vpaddd	L_avx2_aes_gcm_five(%rip), %xmm0, %xmm13
        vpshufb	%xmm1, %xmm12, %xmm12
        vpaddd	L_avx2_aes_gcm_six(%rip), %xmm0, %xmm14
        vpshufb	%xmm1, %xmm13, %xmm13
        vpaddd	L_avx2_aes_gcm_seven(%rip), %xmm0, %xmm15
        vpshufb	%xmm1, %xmm14, %xmm14
        vpaddd	L_avx2_aes_gcm_eight(%rip), %xmm0, %xmm0
        vpshufb	%xmm1, %xmm15, %xmm15
        # aesenc_xor
        vmovdqa	(%rsi), %xmm7
        vmovdqa	%xmm0, 128(%rsp)
        vpxor	%xmm7, %xmm8, %xmm8
        vpxor	%xmm7, %xmm9, %xmm9
        vpxor	%xmm7, %xmm10, %xmm10
        vpxor	%xmm7, %xmm11, %xmm11
        vpxor	%xmm7, %xmm12, %xmm12
        vpxor	%xmm7, %xmm13, %xmm13
        vpxor	%xmm7, %xmm14, %xmm14
        vpxor	%xmm7, %xmm15, %xmm15
        # aesenc_pclmul_1
        vmovdqu	-128(%rdx), %xmm1
        vmovdqu	16(%rsi), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vmovdqa	112(%rsp), %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm5
        vpclmulqdq	$0x01, %xmm2, %xmm1, %xmm3
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm6
        vpclmulqdq	$0x11, %xmm2, %xmm1, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_2
        vmovdqu	-112(%rdx), %xmm1
        vmovdqa	96(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	32(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	-96(%rdx), %xmm1
        vmovdqa	80(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	48(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	-80(%rdx), %xmm1
        vmovdqa	64(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	64(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	-64(%rdx), %xmm1
        vmovdqa	48(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	80(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	-48(%rdx), %xmm1
        vmovdqa	32(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	96(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	-32(%rdx), %xmm1
        vmovdqa	16(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	112(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	-16(%rdx), %xmm1
        vmovdqa	(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	128(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_l
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm4, %xmm6, %xmm6
        vpxor	%xmm3, %xmm5, %xmm5
        vpslldq	$8, %xmm5, %xmm1
        vpsrldq	$8, %xmm5, %xmm5
        vmovdqa	144(%rsi), %xmm4
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm0
        vaesenc	%xmm4, %xmm8, %xmm8
        vpxor	%xmm1, %xmm6, %xmm6
        vpxor	%xmm5, %xmm7, %xmm7
        vpclmulqdq	$16, %xmm0, %xmm6, %xmm3
        vaesenc	%xmm4, %xmm9, %xmm9
        vaesenc	%xmm4, %xmm10, %xmm10
        vaesenc	%xmm4, %xmm11, %xmm11
        vpshufd	$0x4e, %xmm6, %xmm6
        vpxor	%xmm3, %xmm6, %xmm6
        vpclmulqdq	$16, %xmm0, %xmm6, %xmm3
        vaesenc	%xmm4, %xmm12, %xmm12
        vaesenc	%xmm4, %xmm13, %xmm13
        vaesenc	%xmm4, %xmm14, %xmm14
        vpshufd	$0x4e, %xmm6, %xmm6
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm7, %xmm6, %xmm6
        vaesenc	%xmm4, %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm7
        jl	L_AES_GCM_encrypt_avx2_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	176(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm7
        jl	L_AES_GCM_encrypt_avx2_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	208(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm7
L_AES_GCM_encrypt_avx2_aesenc_128_ghash_avx_done:
        # aesenc_last
        vaesenclast	%xmm7, %xmm8, %xmm8
        vaesenclast	%xmm7, %xmm9, %xmm9
        vaesenclast	%xmm7, %xmm10, %xmm10
        vaesenclast	%xmm7, %xmm11, %xmm11
        vmovdqu	(%rcx), %xmm0
        vmovdqu	16(%rcx), %xmm1
        vmovdqu	32(%rcx), %xmm2
        vmovdqu	48(%rcx), %xmm3
        vpxor	%xmm0, %xmm8, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vpxor	%xmm2, %xmm10, %xmm10
        vpxor	%xmm3, %xmm11, %xmm11
        vmovdqu	%xmm8, (%rdx)
        vmovdqu	%xmm9, 16(%rdx)
        vmovdqu	%xmm10, 32(%rdx)
        vmovdqu	%xmm11, 48(%rdx)
        vaesenclast	%xmm7, %xmm12, %xmm12
        vaesenclast	%xmm7, %xmm13, %xmm13
        vaesenclast	%xmm7, %xmm14, %xmm14
        vaesenclast	%xmm7, %xmm15, %xmm15
        vmovdqu	64(%rcx), %xmm0
        vmovdqu	80(%rcx), %xmm1
        vmovdqu	96(%rcx), %xmm2
        vmovdqu	112(%rcx), %xmm3
        vpxor	%xmm0, %xmm12, %xmm12
        vpxor	%xmm1, %xmm13, %xmm13
        vpxor	%xmm2, %xmm14, %xmm14
        vpxor	%xmm3, %xmm15, %xmm15
        vmovdqu	%xmm12, 64(%rdx)
        vmovdqu	%xmm13, 80(%rdx)
        vmovdqu	%xmm14, 96(%rdx)
        vmovdqu	%xmm15, 112(%rdx)
        # aesenc_128_ghash - end
        addl	$0x80, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_encrypt_avx2_ghash_128
L_AES_GCM_encrypt_avx2_end_128:
        vmovdqa	L_avx2_aes_gcm_bswap_mask(%rip), %xmm4
        vpshufb	%xmm4, %xmm8, %xmm8
        vpshufb	%xmm4, %xmm9, %xmm9
        vpshufb	%xmm4, %xmm10, %xmm10
        vpshufb	%xmm4, %xmm11, %xmm11
        vpshufb	%xmm4, %xmm12, %xmm12
        vpshufb	%xmm4, %xmm13, %xmm13
        vpshufb	%xmm4, %xmm14, %xmm14
        vpshufb	%xmm4, %xmm15, %xmm15
        vpxor	%xmm6, %xmm8, %xmm8
        vmovdqu	(%rsp), %xmm7
        vpclmulqdq	$16, %xmm15, %xmm7, %xmm5
        vpclmulqdq	$0x01, %xmm15, %xmm7, %xmm1
        vpclmulqdq	$0x00, %xmm15, %xmm7, %xmm4
        vpclmulqdq	$0x11, %xmm15, %xmm7, %xmm6
        vpxor	%xmm1, %xmm5, %xmm5
        vmovdqu	16(%rsp), %xmm7
        vpclmulqdq	$16, %xmm14, %xmm7, %xmm2
        vpclmulqdq	$0x01, %xmm14, %xmm7, %xmm1
        vpclmulqdq	$0x00, %xmm14, %xmm7, %xmm0
        vpclmulqdq	$0x11, %xmm14, %xmm7, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vmovdqu	32(%rsp), %xmm15
        vmovdqu	48(%rsp), %xmm7
        vpclmulqdq	$16, %xmm13, %xmm15, %xmm2
        vpclmulqdq	$0x01, %xmm13, %xmm15, %xmm1
        vpclmulqdq	$0x00, %xmm13, %xmm15, %xmm0
        vpclmulqdq	$0x11, %xmm13, %xmm15, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vpclmulqdq	$16, %xmm12, %xmm7, %xmm2
        vpclmulqdq	$0x01, %xmm12, %xmm7, %xmm1
        vpclmulqdq	$0x00, %xmm12, %xmm7, %xmm0
        vpclmulqdq	$0x11, %xmm12, %xmm7, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vmovdqu	64(%rsp), %xmm15
        vmovdqu	80(%rsp), %xmm7
        vpclmulqdq	$16, %xmm11, %xmm15, %xmm2
        vpclmulqdq	$0x01, %xmm11, %xmm15, %xmm1
        vpclmulqdq	$0x00, %xmm11, %xmm15, %xmm0
        vpclmulqdq	$0x11, %xmm11, %xmm15, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vpclmulqdq	$16, %xmm10, %xmm7, %xmm2
        vpclmulqdq	$0x01, %xmm10, %xmm7, %xmm1
        vpclmulqdq	$0x00, %xmm10, %xmm7, %xmm0
        vpclmulqdq	$0x11, %xmm10, %xmm7, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vmovdqu	96(%rsp), %xmm15
        vmovdqu	112(%rsp), %xmm7
        vpclmulqdq	$16, %xmm9, %xmm15, %xmm2
        vpclmulqdq	$0x01, %xmm9, %xmm15, %xmm1
        vpclmulqdq	$0x00, %xmm9, %xmm15, %xmm0
        vpclmulqdq	$0x11, %xmm9, %xmm15, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vpclmulqdq	$16, %xmm8, %xmm7, %xmm2
        vpclmulqdq	$0x01, %xmm8, %xmm7, %xmm1
        vpclmulqdq	$0x00, %xmm8, %xmm7, %xmm0
        vpclmulqdq	$0x11, %xmm8, %xmm7, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm0, %xmm4, %xmm4
        vpslldq	$8, %xmm5, %xmm7
        vpsrldq	$8, %xmm5, %xmm5
        vpxor	%xmm7, %xmm4, %xmm4
        vpxor	%xmm5, %xmm6, %xmm6
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm4, %xmm0
        vpshufd	$0x4e, %xmm4, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm6, %xmm6
        vmovdqa	(%rsp), %xmm5
        vmovdqu	128(%rsp), %xmm4
        vmovdqu	144(%rsp), %xmm15
L_AES_GCM_encrypt_avx2_done_128:
        cmpl	%r10d, %ebx
        je	L_AES_GCM_encrypt_avx2_done_enc
        movl	%r10d, %r13d
        andl	$0xfffffff0, %r13d
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_encrypt_avx2_last_block_done
        # aesenc_block
        vmovdqa	%xmm4, %xmm1
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm1, %xmm0
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm1, %xmm1
        vpxor	(%rsi), %xmm0, %xmm0
        vmovdqa	16(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	32(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	48(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	64(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	80(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	96(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	112(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	128(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	144(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	%xmm1, %xmm4
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm1
        jl	L_AES_GCM_encrypt_avx2_aesenc_block_last
        vaesenc	%xmm1, %xmm0, %xmm0
        vmovdqa	176(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm1
        jl	L_AES_GCM_encrypt_avx2_aesenc_block_last
        vaesenc	%xmm1, %xmm0, %xmm0
        vmovdqa	208(%rsi), %xmm2
        vaesenc	%xmm2, %xmm0, %xmm0
        vmovdqa	224(%rsi), %xmm1
L_AES_GCM_encrypt_avx2_aesenc_block_last:
        vaesenclast	%xmm1, %xmm0, %xmm0
        vmovdqu	(%rdi,%rbx,1), %xmm1
        vpxor	%xmm1, %xmm0, %xmm0
        vmovdqu	%xmm0, (%r8,%rbx,1)
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_encrypt_avx2_last_block_ghash
L_AES_GCM_encrypt_avx2_last_block_start:
        vmovdqu	(%rdi,%rbx,1), %xmm12
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm11
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm4, %xmm4
        # aesenc_gfmul_sb
        vpclmulqdq	$0x01, %xmm5, %xmm6, %xmm2
        vpclmulqdq	$16, %xmm5, %xmm6, %xmm3
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm1
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm8
        vpxor	(%rsi), %xmm11, %xmm11
        vaesenc	16(%rsi), %xmm11, %xmm11
        vpxor	%xmm2, %xmm3, %xmm3
        vpslldq	$8, %xmm3, %xmm2
        vpsrldq	$8, %xmm3, %xmm3
        vaesenc	32(%rsi), %xmm11, %xmm11
        vpxor	%xmm1, %xmm2, %xmm2
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm2, %xmm1
        vaesenc	48(%rsi), %xmm11, %xmm11
        vaesenc	64(%rsi), %xmm11, %xmm11
        vaesenc	80(%rsi), %xmm11, %xmm11
        vpshufd	$0x4e, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm2, %xmm1
        vaesenc	96(%rsi), %xmm11, %xmm11
        vaesenc	112(%rsi), %xmm11, %xmm11
        vaesenc	128(%rsi), %xmm11, %xmm11
        vpshufd	$0x4e, %xmm2, %xmm2
        vaesenc	144(%rsi), %xmm11, %xmm11
        vpxor	%xmm3, %xmm8, %xmm8
        vpxor	%xmm8, %xmm2, %xmm2
        vmovdqa	160(%rsi), %xmm0
        cmpl	$11, %r9d
        jl	L_AES_GCM_encrypt_avx2_aesenc_gfmul_sb_last
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	176(%rsi), %xmm11, %xmm11
        vmovdqa	192(%rsi), %xmm0
        cmpl	$13, %r9d
        jl	L_AES_GCM_encrypt_avx2_aesenc_gfmul_sb_last
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	208(%rsi), %xmm11, %xmm11
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_encrypt_avx2_aesenc_gfmul_sb_last:
        vaesenclast	%xmm0, %xmm11, %xmm11
        vpxor	%xmm1, %xmm2, %xmm6
        vpxor	%xmm12, %xmm11, %xmm11
        vmovdqu	%xmm11, (%r8,%rbx,1)
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm11, %xmm11
        vpxor	%xmm11, %xmm6, %xmm6
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_encrypt_avx2_last_block_start
L_AES_GCM_encrypt_avx2_last_block_ghash:
        # ghash_gfmul_red
        vpclmulqdq	$16, %xmm5, %xmm6, %xmm10
        vpclmulqdq	$0x01, %xmm5, %xmm6, %xmm9
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm8
        vpxor	%xmm9, %xmm10, %xmm10
        vpslldq	$8, %xmm10, %xmm9
        vpsrldq	$8, %xmm10, %xmm10
        vpxor	%xmm8, %xmm9, %xmm9
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm6
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm9, %xmm8
        vpshufd	$0x4e, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm9, %xmm8
        vpshufd	$0x4e, %xmm9, %xmm9
        vpxor	%xmm10, %xmm6, %xmm6
        vpxor	%xmm9, %xmm6, %xmm6
        vpxor	%xmm8, %xmm6, %xmm6
L_AES_GCM_encrypt_avx2_last_block_done:
        movl	%r10d, %ecx
        movl	%r10d, %edx
        andl	$15, %ecx
        jz	L_AES_GCM_encrypt_avx2_done_enc
        # aesenc_last15_enc
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpxor	(%rsi), %xmm4, %xmm4
        vaesenc	16(%rsi), %xmm4, %xmm4
        vaesenc	32(%rsi), %xmm4, %xmm4
        vaesenc	48(%rsi), %xmm4, %xmm4
        vaesenc	64(%rsi), %xmm4, %xmm4
        vaesenc	80(%rsi), %xmm4, %xmm4
        vaesenc	96(%rsi), %xmm4, %xmm4
        vaesenc	112(%rsi), %xmm4, %xmm4
        vaesenc	128(%rsi), %xmm4, %xmm4
        vaesenc	144(%rsi), %xmm4, %xmm4
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_aesenc_last15_enc_avx_aesenc_avx_last
        vaesenc	%xmm0, %xmm4, %xmm4
        vaesenc	176(%rsi), %xmm4, %xmm4
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_encrypt_avx2_aesenc_last15_enc_avx_aesenc_avx_last
        vaesenc	%xmm0, %xmm4, %xmm4
        vaesenc	208(%rsi), %xmm4, %xmm4
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_encrypt_avx2_aesenc_last15_enc_avx_aesenc_avx_last:
        vaesenclast	%xmm0, %xmm4, %xmm4
        xorl	%ecx, %ecx
        vpxor	%xmm0, %xmm0, %xmm0
        vmovdqa	%xmm4, (%rsp)
        vmovdqa	%xmm0, 16(%rsp)
L_AES_GCM_encrypt_avx2_aesenc_last15_enc_avx_loop:
        movzbl	(%rdi,%rbx,1), %r13d
        xorb	(%rsp,%rcx,1), %r13b
        movb	%r13b, 16(%rsp,%rcx,1)
        movb	%r13b, (%r8,%rbx,1)
        incl	%ebx
        incl	%ecx
        cmpl	%edx, %ebx
        jl	L_AES_GCM_encrypt_avx2_aesenc_last15_enc_avx_loop
L_AES_GCM_encrypt_avx2_aesenc_last15_enc_avx_finish_enc:
        vmovdqa	16(%rsp), %xmm4
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        vpxor	%xmm4, %xmm6, %xmm6
        # ghash_gfmul_red
        vpclmulqdq	$16, %xmm5, %xmm6, %xmm2
        vpclmulqdq	$0x01, %xmm5, %xmm6, %xmm1
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm0
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm6
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm2, %xmm6, %xmm6
        vpxor	%xmm1, %xmm6, %xmm6
        vpxor	%xmm0, %xmm6, %xmm6
L_AES_GCM_encrypt_avx2_done_enc:
        # calc_tag
        shlq	$3, %r10
        vpinsrq	$0x00, %r10, %xmm0, %xmm0
        shlq	$3, %r11
        vpinsrq	$0x01, %r11, %xmm1, %xmm1
        vpblendd	$12, %xmm1, %xmm0, %xmm0
        vpxor	%xmm6, %xmm0, %xmm0
        # ghash_gfmul_red
        vpclmulqdq	$16, %xmm5, %xmm0, %xmm4
        vpclmulqdq	$0x01, %xmm5, %xmm0, %xmm3
        vpclmulqdq	$0x00, %xmm5, %xmm0, %xmm2
        vpxor	%xmm3, %xmm4, %xmm4
        vpslldq	$8, %xmm4, %xmm3
        vpsrldq	$8, %xmm4, %xmm4
        vpxor	%xmm2, %xmm3, %xmm3
        vpclmulqdq	$0x11, %xmm5, %xmm0, %xmm0
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm3, %xmm2
        vpshufd	$0x4e, %xmm3, %xmm3
        vpxor	%xmm2, %xmm3, %xmm3
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm3, %xmm2
        vpshufd	$0x4e, %xmm3, %xmm3
        vpxor	%xmm4, %xmm0, %xmm0
        vpxor	%xmm3, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm15, %xmm0, %xmm0
        # store_tag
        cmpl	$16, %r14d
        je	L_AES_GCM_encrypt_avx2_store_tag_16
        xorq	%rcx, %rcx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_encrypt_avx2_store_tag_loop:
        movzbl	(%rsp,%rcx,1), %r13d
        movb	%r13b, (%r15,%rcx,1)
        incl	%ecx
        cmpl	%r14d, %ecx
        jne	L_AES_GCM_encrypt_avx2_store_tag_loop
        jmp	L_AES_GCM_encrypt_avx2_store_tag_done
L_AES_GCM_encrypt_avx2_store_tag_16:
        vmovdqu	%xmm0, (%r15)
L_AES_GCM_encrypt_avx2_store_tag_done:
        vzeroupper
        addq	$0xa0, %rsp
        popq	%r14
        popq	%rbx
        popq	%r15
        popq	%r12
        popq	%r13
        repz retq
#ifndef __APPLE__
.size	AES_GCM_encrypt_avx2,.-AES_GCM_encrypt_avx2
#endif /* __APPLE__ */
#ifndef __APPLE__
.text
.globl	AES_GCM_decrypt_avx2
.type	AES_GCM_decrypt_avx2,@function
.align	4
AES_GCM_decrypt_avx2:
#else
.section	__TEXT,__text
.globl	_AES_GCM_decrypt_avx2
.p2align	2
_AES_GCM_decrypt_avx2:
#endif /* __APPLE__ */
        pushq	%r13
        pushq	%r12
        pushq	%r14
        pushq	%rbx
        pushq	%r15
        pushq	%rbp
        movq	%rdx, %r12
        movq	%rcx, %rax
        movq	%r8, %r14
        movq	%rsi, %r8
        movl	%r9d, %r10d
        movl	56(%rsp), %r11d
        movl	64(%rsp), %ebx
        movl	72(%rsp), %r15d
        movq	80(%rsp), %rsi
        movl	88(%rsp), %r9d
        movq	96(%rsp), %rbp
        subq	$0xa8, %rsp
        vpxor	%xmm4, %xmm4, %xmm4
        vpxor	%xmm6, %xmm6, %xmm6
        movl	%ebx, %edx
        cmpl	$12, %edx
        je	L_AES_GCM_decrypt_avx2_iv_12
        # Calculate values when IV is not 12 bytes
        # H = Encrypt X(=0)
        vmovdqa	(%rsi), %xmm5
        vaesenc	16(%rsi), %xmm5, %xmm5
        vaesenc	32(%rsi), %xmm5, %xmm5
        vaesenc	48(%rsi), %xmm5, %xmm5
        vaesenc	64(%rsi), %xmm5, %xmm5
        vaesenc	80(%rsi), %xmm5, %xmm5
        vaesenc	96(%rsi), %xmm5, %xmm5
        vaesenc	112(%rsi), %xmm5, %xmm5
        vaesenc	128(%rsi), %xmm5, %xmm5
        vaesenc	144(%rsi), %xmm5, %xmm5
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_decrypt_avx2_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	176(%rsi), %xmm5, %xmm5
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_decrypt_avx2_calc_iv_1_aesenc_avx_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	208(%rsi), %xmm5, %xmm5
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_decrypt_avx2_calc_iv_1_aesenc_avx_last:
        vaesenclast	%xmm0, %xmm5, %xmm5
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
        # Calc counter
        # Initialization vector
        cmpl	$0x00, %edx
        movq	$0x00, %rcx
        je	L_AES_GCM_decrypt_avx2_calc_iv_done
        cmpl	$16, %edx
        jl	L_AES_GCM_decrypt_avx2_calc_iv_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_decrypt_avx2_calc_iv_16_loop:
        vmovdqu	(%rax,%rcx,1), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm4, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm4, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm4
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm4, %xmm4
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx2_calc_iv_16_loop
        movl	%ebx, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_decrypt_avx2_calc_iv_done
L_AES_GCM_decrypt_avx2_calc_iv_lt16:
        vpxor	%xmm0, %xmm0, %xmm0
        xorl	%ebx, %ebx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_decrypt_avx2_calc_iv_loop:
        movzbl	(%rax,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx2_calc_iv_loop
        vmovdqa	(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm4, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm4, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm4
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm4, %xmm4
L_AES_GCM_decrypt_avx2_calc_iv_done:
        # T = Encrypt counter
        vpxor	%xmm0, %xmm0, %xmm0
        shll	$3, %edx
        vpinsrq	$0x00, %rdx, %xmm0, %xmm0
        vpxor	%xmm0, %xmm4, %xmm4
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm4, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm4, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm4, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm4, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm4
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm4, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm4, %xmm4
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm4, %xmm4
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm4, %xmm4
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm4, %xmm4
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        #   Encrypt counter
        vmovdqa	(%rsi), %xmm15
        vpxor	%xmm4, %xmm15, %xmm15
        vaesenc	16(%rsi), %xmm15, %xmm15
        vaesenc	32(%rsi), %xmm15, %xmm15
        vaesenc	48(%rsi), %xmm15, %xmm15
        vaesenc	64(%rsi), %xmm15, %xmm15
        vaesenc	80(%rsi), %xmm15, %xmm15
        vaesenc	96(%rsi), %xmm15, %xmm15
        vaesenc	112(%rsi), %xmm15, %xmm15
        vaesenc	128(%rsi), %xmm15, %xmm15
        vaesenc	144(%rsi), %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_decrypt_avx2_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm0, %xmm15, %xmm15
        vaesenc	176(%rsi), %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_decrypt_avx2_calc_iv_2_aesenc_avx_last
        vaesenc	%xmm0, %xmm15, %xmm15
        vaesenc	208(%rsi), %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_decrypt_avx2_calc_iv_2_aesenc_avx_last:
        vaesenclast	%xmm0, %xmm15, %xmm15
        jmp	L_AES_GCM_decrypt_avx2_iv_done
L_AES_GCM_decrypt_avx2_iv_12:
        # # Calculate values when IV is 12 bytes
        # Set counter based on IV
        vmovdqa	L_avx2_aes_gcm_bswap_one(%rip), %xmm4
        vmovdqa	(%rsi), %xmm5
        vpblendd	$7, (%rax), %xmm4, %xmm4
        # H = Encrypt X(=0) and T = Encrypt counter
        vmovdqa	16(%rsi), %xmm7
        vpxor	%xmm5, %xmm4, %xmm15
        vaesenc	%xmm7, %xmm5, %xmm5
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	32(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	48(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	64(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	80(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	96(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	112(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	128(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	144(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm0
        jl	L_AES_GCM_decrypt_avx2_calc_iv_12_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	176(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm0
        jl	L_AES_GCM_decrypt_avx2_calc_iv_12_last
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	208(%rsi), %xmm0
        vaesenc	%xmm0, %xmm5, %xmm5
        vaesenc	%xmm0, %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_decrypt_avx2_calc_iv_12_last:
        vaesenclast	%xmm0, %xmm5, %xmm5
        vaesenclast	%xmm0, %xmm15, %xmm15
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm5, %xmm5
L_AES_GCM_decrypt_avx2_iv_done:
        # Additional authentication data
        movl	%r11d, %edx
        cmpl	$0x00, %edx
        je	L_AES_GCM_decrypt_avx2_calc_aad_done
        xorl	%ecx, %ecx
        cmpl	$16, %edx
        jl	L_AES_GCM_decrypt_avx2_calc_aad_lt16
        andl	$0xfffffff0, %edx
L_AES_GCM_decrypt_avx2_calc_aad_16_loop:
        vmovdqu	(%r12,%rcx,1), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm6, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm6, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm6
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm6, %xmm6
        addl	$16, %ecx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx2_calc_aad_16_loop
        movl	%r11d, %edx
        cmpl	%edx, %ecx
        je	L_AES_GCM_decrypt_avx2_calc_aad_done
L_AES_GCM_decrypt_avx2_calc_aad_lt16:
        vpxor	%xmm0, %xmm0, %xmm0
        xorl	%ebx, %ebx
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_decrypt_avx2_calc_aad_loop:
        movzbl	(%r12,%rcx,1), %r13d
        movb	%r13b, (%rsp,%rbx,1)
        incl	%ecx
        incl	%ebx
        cmpl	%edx, %ecx
        jl	L_AES_GCM_decrypt_avx2_calc_aad_loop
        vmovdqa	(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm0, %xmm6, %xmm6
        # ghash_gfmul_avx
        vpclmulqdq	$16, %xmm6, %xmm5, %xmm2
        vpclmulqdq	$0x01, %xmm6, %xmm5, %xmm1
        vpclmulqdq	$0x00, %xmm6, %xmm5, %xmm0
        vpclmulqdq	$0x11, %xmm6, %xmm5, %xmm3
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm1, %xmm0, %xmm7
        vpxor	%xmm2, %xmm3, %xmm6
        # ghash_mid
        vpsrld	$31, %xmm7, %xmm0
        vpsrld	$31, %xmm6, %xmm1
        vpslld	$0x01, %xmm7, %xmm7
        vpslld	$0x01, %xmm6, %xmm6
        vpsrldq	$12, %xmm0, %xmm2
        vpslldq	$4, %xmm0, %xmm0
        vpslldq	$4, %xmm1, %xmm1
        vpor	%xmm2, %xmm6, %xmm6
        vpor	%xmm0, %xmm7, %xmm7
        vpor	%xmm1, %xmm6, %xmm6
        # ghash_red
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm2
        vpclmulqdq	$16, %xmm2, %xmm7, %xmm0
        vpshufd	$0x4e, %xmm7, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpxor	%xmm1, %xmm6, %xmm6
L_AES_GCM_decrypt_avx2_calc_aad_done:
        # Calculate counter and H
        vpsrlq	$63, %xmm5, %xmm1
        vpsllq	$0x01, %xmm5, %xmm0
        vpslldq	$8, %xmm1, %xmm1
        vpor	%xmm1, %xmm0, %xmm0
        vpshufd	$0xff, %xmm5, %xmm5
        vpsrad	$31, %xmm5, %xmm5
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpand	L_avx2_aes_gcm_mod2_128(%rip), %xmm5, %xmm5
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm4, %xmm4
        vpxor	%xmm0, %xmm5, %xmm5
        xorl	%ebx, %ebx
        cmpl	$0x80, %r10d
        movl	%r10d, %r13d
        jl	L_AES_GCM_decrypt_avx2_done_128
        andl	$0xffffff80, %r13d
        vmovdqa	%xmm4, 128(%rsp)
        vmovdqa	%xmm15, 144(%rsp)
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm3
        # H ^ 1 and H ^ 2
        vpclmulqdq	$0x00, %xmm5, %xmm5, %xmm9
        vpclmulqdq	$0x11, %xmm5, %xmm5, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm9, %xmm8
        vpshufd	$0x4e, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm9, %xmm8
        vpshufd	$0x4e, %xmm9, %xmm9
        vpxor	%xmm8, %xmm9, %xmm9
        vpxor	%xmm9, %xmm10, %xmm0
        vmovdqa	%xmm5, (%rsp)
        vmovdqa	%xmm0, 16(%rsp)
        # H ^ 3 and H ^ 4
        vpclmulqdq	$16, %xmm5, %xmm0, %xmm11
        vpclmulqdq	$0x01, %xmm5, %xmm0, %xmm10
        vpclmulqdq	$0x00, %xmm5, %xmm0, %xmm9
        vpclmulqdq	$0x11, %xmm5, %xmm0, %xmm12
        vpclmulqdq	$0x00, %xmm0, %xmm0, %xmm13
        vpclmulqdq	$0x11, %xmm0, %xmm0, %xmm14
        vpxor	%xmm10, %xmm11, %xmm11
        vpslldq	$8, %xmm11, %xmm10
        vpsrldq	$8, %xmm11, %xmm11
        vpxor	%xmm9, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm9, %xmm10, %xmm10
        vpxor	%xmm8, %xmm13, %xmm13
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm11, %xmm12, %xmm12
        vpxor	%xmm8, %xmm13, %xmm13
        vpxor	%xmm12, %xmm10, %xmm10
        vpxor	%xmm14, %xmm13, %xmm2
        vpxor	%xmm9, %xmm10, %xmm1
        vmovdqa	%xmm1, 32(%rsp)
        vmovdqa	%xmm2, 48(%rsp)
        # H ^ 5 and H ^ 6
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm11
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm10
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm9
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm12
        vpclmulqdq	$0x00, %xmm1, %xmm1, %xmm13
        vpclmulqdq	$0x11, %xmm1, %xmm1, %xmm14
        vpxor	%xmm10, %xmm11, %xmm11
        vpslldq	$8, %xmm11, %xmm10
        vpsrldq	$8, %xmm11, %xmm11
        vpxor	%xmm9, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm9, %xmm10, %xmm10
        vpxor	%xmm8, %xmm13, %xmm13
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm11, %xmm12, %xmm12
        vpxor	%xmm8, %xmm13, %xmm13
        vpxor	%xmm12, %xmm10, %xmm10
        vpxor	%xmm14, %xmm13, %xmm0
        vpxor	%xmm9, %xmm10, %xmm7
        vmovdqa	%xmm7, 64(%rsp)
        vmovdqa	%xmm0, 80(%rsp)
        # H ^ 7 and H ^ 8
        vpclmulqdq	$16, %xmm1, %xmm2, %xmm11
        vpclmulqdq	$0x01, %xmm1, %xmm2, %xmm10
        vpclmulqdq	$0x00, %xmm1, %xmm2, %xmm9
        vpclmulqdq	$0x11, %xmm1, %xmm2, %xmm12
        vpclmulqdq	$0x00, %xmm2, %xmm2, %xmm13
        vpclmulqdq	$0x11, %xmm2, %xmm2, %xmm14
        vpxor	%xmm10, %xmm11, %xmm11
        vpslldq	$8, %xmm11, %xmm10
        vpsrldq	$8, %xmm11, %xmm11
        vpxor	%xmm9, %xmm10, %xmm10
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm9, %xmm10, %xmm10
        vpxor	%xmm8, %xmm13, %xmm13
        vpclmulqdq	$16, %xmm3, %xmm10, %xmm9
        vpclmulqdq	$16, %xmm3, %xmm13, %xmm8
        vpshufd	$0x4e, %xmm10, %xmm10
        vpshufd	$0x4e, %xmm13, %xmm13
        vpxor	%xmm11, %xmm12, %xmm12
        vpxor	%xmm8, %xmm13, %xmm13
        vpxor	%xmm12, %xmm10, %xmm10
        vpxor	%xmm14, %xmm13, %xmm0
        vpxor	%xmm9, %xmm10, %xmm7
        vmovdqa	%xmm7, 96(%rsp)
        vmovdqa	%xmm0, 112(%rsp)
L_AES_GCM_decrypt_avx2_ghash_128:
        # aesenc_128_ghash
        leaq	(%rdi,%rbx,1), %rcx
        leaq	(%r8,%rbx,1), %rdx
        # aesenc_ctr
        vmovdqa	128(%rsp), %xmm0
        vmovdqa	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm1
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm0, %xmm9
        vpshufb	%xmm1, %xmm0, %xmm8
        vpaddd	L_avx2_aes_gcm_two(%rip), %xmm0, %xmm10
        vpshufb	%xmm1, %xmm9, %xmm9
        vpaddd	L_avx2_aes_gcm_three(%rip), %xmm0, %xmm11
        vpshufb	%xmm1, %xmm10, %xmm10
        vpaddd	L_avx2_aes_gcm_four(%rip), %xmm0, %xmm12
        vpshufb	%xmm1, %xmm11, %xmm11
        vpaddd	L_avx2_aes_gcm_five(%rip), %xmm0, %xmm13
        vpshufb	%xmm1, %xmm12, %xmm12
        vpaddd	L_avx2_aes_gcm_six(%rip), %xmm0, %xmm14
        vpshufb	%xmm1, %xmm13, %xmm13
        vpaddd	L_avx2_aes_gcm_seven(%rip), %xmm0, %xmm15
        vpshufb	%xmm1, %xmm14, %xmm14
        vpaddd	L_avx2_aes_gcm_eight(%rip), %xmm0, %xmm0
        vpshufb	%xmm1, %xmm15, %xmm15
        # aesenc_xor
        vmovdqa	(%rsi), %xmm7
        vmovdqa	%xmm0, 128(%rsp)
        vpxor	%xmm7, %xmm8, %xmm8
        vpxor	%xmm7, %xmm9, %xmm9
        vpxor	%xmm7, %xmm10, %xmm10
        vpxor	%xmm7, %xmm11, %xmm11
        vpxor	%xmm7, %xmm12, %xmm12
        vpxor	%xmm7, %xmm13, %xmm13
        vpxor	%xmm7, %xmm14, %xmm14
        vpxor	%xmm7, %xmm15, %xmm15
        # aesenc_pclmul_1
        vmovdqu	(%rcx), %xmm1
        vmovdqu	16(%rsi), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vmovdqa	112(%rsp), %xmm2
        vpxor	%xmm6, %xmm1, %xmm1
        vpclmulqdq	$16, %xmm2, %xmm1, %xmm5
        vpclmulqdq	$0x01, %xmm2, %xmm1, %xmm3
        vpclmulqdq	$0x00, %xmm2, %xmm1, %xmm6
        vpclmulqdq	$0x11, %xmm2, %xmm1, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_2
        vmovdqu	16(%rcx), %xmm1
        vmovdqa	96(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	32(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	32(%rcx), %xmm1
        vmovdqa	80(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	48(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	48(%rcx), %xmm1
        vmovdqa	64(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	64(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	64(%rcx), %xmm1
        vmovdqa	48(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	80(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	80(%rcx), %xmm1
        vmovdqa	32(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	96(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	96(%rcx), %xmm1
        vmovdqa	16(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	112(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_n
        vmovdqu	112(%rcx), %xmm1
        vmovdqa	(%rsp), %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm1, %xmm1
        vpxor	%xmm2, %xmm5, %xmm5
        vpclmulqdq	$16, %xmm0, %xmm1, %xmm2
        vpxor	%xmm3, %xmm5, %xmm5
        vpclmulqdq	$0x01, %xmm0, %xmm1, %xmm3
        vpxor	%xmm4, %xmm6, %xmm6
        vpclmulqdq	$0x00, %xmm0, %xmm1, %xmm4
        vpclmulqdq	$0x11, %xmm0, %xmm1, %xmm1
        vmovdqu	128(%rsi), %xmm0
        vpxor	%xmm1, %xmm7, %xmm7
        vaesenc	%xmm0, %xmm8, %xmm8
        vaesenc	%xmm0, %xmm9, %xmm9
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	%xmm0, %xmm11, %xmm11
        vaesenc	%xmm0, %xmm12, %xmm12
        vaesenc	%xmm0, %xmm13, %xmm13
        vaesenc	%xmm0, %xmm14, %xmm14
        vaesenc	%xmm0, %xmm15, %xmm15
        # aesenc_pclmul_l
        vpxor	%xmm2, %xmm5, %xmm5
        vpxor	%xmm4, %xmm6, %xmm6
        vpxor	%xmm3, %xmm5, %xmm5
        vpslldq	$8, %xmm5, %xmm1
        vpsrldq	$8, %xmm5, %xmm5
        vmovdqa	144(%rsi), %xmm4
        vmovdqa	L_avx2_aes_gcm_mod2_128(%rip), %xmm0
        vaesenc	%xmm4, %xmm8, %xmm8
        vpxor	%xmm1, %xmm6, %xmm6
        vpxor	%xmm5, %xmm7, %xmm7
        vpclmulqdq	$16, %xmm0, %xmm6, %xmm3
        vaesenc	%xmm4, %xmm9, %xmm9
        vaesenc	%xmm4, %xmm10, %xmm10
        vaesenc	%xmm4, %xmm11, %xmm11
        vpshufd	$0x4e, %xmm6, %xmm6
        vpxor	%xmm3, %xmm6, %xmm6
        vpclmulqdq	$16, %xmm0, %xmm6, %xmm3
        vaesenc	%xmm4, %xmm12, %xmm12
        vaesenc	%xmm4, %xmm13, %xmm13
        vaesenc	%xmm4, %xmm14, %xmm14
        vpshufd	$0x4e, %xmm6, %xmm6
        vpxor	%xmm3, %xmm6, %xmm6
        vpxor	%xmm7, %xmm6, %xmm6
        vaesenc	%xmm4, %xmm15, %xmm15
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm7
        jl	L_AES_GCM_decrypt_avx2_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	176(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm7
        jl	L_AES_GCM_decrypt_avx2_aesenc_128_ghash_avx_done
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	208(%rsi), %xmm7
        vaesenc	%xmm7, %xmm8, %xmm8
        vaesenc	%xmm7, %xmm9, %xmm9
        vaesenc	%xmm7, %xmm10, %xmm10
        vaesenc	%xmm7, %xmm11, %xmm11
        vaesenc	%xmm7, %xmm12, %xmm12
        vaesenc	%xmm7, %xmm13, %xmm13
        vaesenc	%xmm7, %xmm14, %xmm14
        vaesenc	%xmm7, %xmm15, %xmm15
        vmovdqa	224(%rsi), %xmm7
L_AES_GCM_decrypt_avx2_aesenc_128_ghash_avx_done:
        # aesenc_last
        vaesenclast	%xmm7, %xmm8, %xmm8
        vaesenclast	%xmm7, %xmm9, %xmm9
        vaesenclast	%xmm7, %xmm10, %xmm10
        vaesenclast	%xmm7, %xmm11, %xmm11
        vmovdqu	(%rcx), %xmm0
        vmovdqu	16(%rcx), %xmm1
        vmovdqu	32(%rcx), %xmm2
        vmovdqu	48(%rcx), %xmm3
        vpxor	%xmm0, %xmm8, %xmm8
        vpxor	%xmm1, %xmm9, %xmm9
        vpxor	%xmm2, %xmm10, %xmm10
        vpxor	%xmm3, %xmm11, %xmm11
        vmovdqu	%xmm8, (%rdx)
        vmovdqu	%xmm9, 16(%rdx)
        vmovdqu	%xmm10, 32(%rdx)
        vmovdqu	%xmm11, 48(%rdx)
        vaesenclast	%xmm7, %xmm12, %xmm12
        vaesenclast	%xmm7, %xmm13, %xmm13
        vaesenclast	%xmm7, %xmm14, %xmm14
        vaesenclast	%xmm7, %xmm15, %xmm15
        vmovdqu	64(%rcx), %xmm0
        vmovdqu	80(%rcx), %xmm1
        vmovdqu	96(%rcx), %xmm2
        vmovdqu	112(%rcx), %xmm3
        vpxor	%xmm0, %xmm12, %xmm12
        vpxor	%xmm1, %xmm13, %xmm13
        vpxor	%xmm2, %xmm14, %xmm14
        vpxor	%xmm3, %xmm15, %xmm15
        vmovdqu	%xmm12, 64(%rdx)
        vmovdqu	%xmm13, 80(%rdx)
        vmovdqu	%xmm14, 96(%rdx)
        vmovdqu	%xmm15, 112(%rdx)
        # aesenc_128_ghash - end
        addl	$0x80, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_decrypt_avx2_ghash_128
        vmovdqa	(%rsp), %xmm5
        vmovdqa	128(%rsp), %xmm4
        vmovdqa	144(%rsp), %xmm15
L_AES_GCM_decrypt_avx2_done_128:
        cmpl	%r10d, %ebx
        jge	L_AES_GCM_decrypt_avx2_done_dec
        movl	%r10d, %r13d
        andl	$0xfffffff0, %r13d
        cmpl	%r13d, %ebx
        jge	L_AES_GCM_decrypt_avx2_last_block_done
L_AES_GCM_decrypt_avx2_last_block_start:
        vmovdqu	(%rdi,%rbx,1), %xmm11
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm10
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm11, %xmm12
        vpaddd	L_avx2_aes_gcm_one(%rip), %xmm4, %xmm4
        vpxor	%xmm6, %xmm12, %xmm12
        # aesenc_gfmul_sb
        vpclmulqdq	$0x01, %xmm5, %xmm12, %xmm2
        vpclmulqdq	$16, %xmm5, %xmm12, %xmm3
        vpclmulqdq	$0x00, %xmm5, %xmm12, %xmm1
        vpclmulqdq	$0x11, %xmm5, %xmm12, %xmm8
        vpxor	(%rsi), %xmm10, %xmm10
        vaesenc	16(%rsi), %xmm10, %xmm10
        vpxor	%xmm2, %xmm3, %xmm3
        vpslldq	$8, %xmm3, %xmm2
        vpsrldq	$8, %xmm3, %xmm3
        vaesenc	32(%rsi), %xmm10, %xmm10
        vpxor	%xmm1, %xmm2, %xmm2
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm2, %xmm1
        vaesenc	48(%rsi), %xmm10, %xmm10
        vaesenc	64(%rsi), %xmm10, %xmm10
        vaesenc	80(%rsi), %xmm10, %xmm10
        vpshufd	$0x4e, %xmm2, %xmm2
        vpxor	%xmm1, %xmm2, %xmm2
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm2, %xmm1
        vaesenc	96(%rsi), %xmm10, %xmm10
        vaesenc	112(%rsi), %xmm10, %xmm10
        vaesenc	128(%rsi), %xmm10, %xmm10
        vpshufd	$0x4e, %xmm2, %xmm2
        vaesenc	144(%rsi), %xmm10, %xmm10
        vpxor	%xmm3, %xmm8, %xmm8
        vpxor	%xmm8, %xmm2, %xmm2
        vmovdqa	160(%rsi), %xmm0
        cmpl	$11, %r9d
        jl	L_AES_GCM_decrypt_avx2_aesenc_gfmul_sb_last
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	176(%rsi), %xmm10, %xmm10
        vmovdqa	192(%rsi), %xmm0
        cmpl	$13, %r9d
        jl	L_AES_GCM_decrypt_avx2_aesenc_gfmul_sb_last
        vaesenc	%xmm0, %xmm10, %xmm10
        vaesenc	208(%rsi), %xmm10, %xmm10
        vmovdqa	224(%rsi), %xmm0
L_AES_GCM_decrypt_avx2_aesenc_gfmul_sb_last:
        vaesenclast	%xmm0, %xmm10, %xmm10
        vpxor	%xmm1, %xmm2, %xmm6
        vpxor	%xmm11, %xmm10, %xmm10
        vmovdqu	%xmm10, (%r8,%rbx,1)
        addl	$16, %ebx
        cmpl	%r13d, %ebx
        jl	L_AES_GCM_decrypt_avx2_last_block_start
L_AES_GCM_decrypt_avx2_last_block_done:
        movl	%r10d, %ecx
        movl	%r10d, %edx
        andl	$15, %ecx
        jz	L_AES_GCM_decrypt_avx2_done_dec
        # aesenc_last15_dec
        vpshufb	L_avx2_aes_gcm_bswap_epi64(%rip), %xmm4, %xmm4
        vpxor	(%rsi), %xmm4, %xmm4
        vaesenc	16(%rsi), %xmm4, %xmm4
        vaesenc	32(%rsi), %xmm4, %xmm4
        vaesenc	48(%rsi), %xmm4, %xmm4
        vaesenc	64(%rsi), %xmm4, %xmm4
        vaesenc	80(%rsi), %xmm4, %xmm4
        vaesenc	96(%rsi), %xmm4, %xmm4
        vaesenc	112(%rsi), %xmm4, %xmm4
        vaesenc	128(%rsi), %xmm4, %xmm4
        vaesenc	144(%rsi), %xmm4, %xmm4
        cmpl	$11, %r9d
        vmovdqa	160(%rsi), %xmm1
        jl	L_AES_GCM_decrypt_avx2_aesenc_last15_dec_avx_aesenc_avx_last
        vaesenc	%xmm1, %xmm4, %xmm4
        vaesenc	176(%rsi), %xmm4, %xmm4
        cmpl	$13, %r9d
        vmovdqa	192(%rsi), %xmm1
        jl	L_AES_GCM_decrypt_avx2_aesenc_last15_dec_avx_aesenc_avx_last
        vaesenc	%xmm1, %xmm4, %xmm4
        vaesenc	208(%rsi), %xmm4, %xmm4
        vmovdqa	224(%rsi), %xmm1
L_AES_GCM_decrypt_avx2_aesenc_last15_dec_avx_aesenc_avx_last:
        vaesenclast	%xmm1, %xmm4, %xmm4
        xorl	%ecx, %ecx
        vpxor	%xmm0, %xmm0, %xmm0
        vmovdqa	%xmm4, (%rsp)
        vmovdqa	%xmm0, 16(%rsp)
L_AES_GCM_decrypt_avx2_aesenc_last15_dec_avx_loop:
        movzbl	(%rdi,%rbx,1), %r13d
        movb	%r13b, 16(%rsp,%rcx,1)
        xorb	(%rsp,%rcx,1), %r13b
        movb	%r13b, (%r8,%rbx,1)
        incl	%ebx
        incl	%ecx
        cmpl	%edx, %ebx
        jl	L_AES_GCM_decrypt_avx2_aesenc_last15_dec_avx_loop
        vmovdqa	16(%rsp), %xmm4
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm4, %xmm4
        vpxor	%xmm4, %xmm6, %xmm6
        # ghash_gfmul_red
        vpclmulqdq	$16, %xmm5, %xmm6, %xmm2
        vpclmulqdq	$0x01, %xmm5, %xmm6, %xmm1
        vpclmulqdq	$0x00, %xmm5, %xmm6, %xmm0
        vpxor	%xmm1, %xmm2, %xmm2
        vpslldq	$8, %xmm2, %xmm1
        vpsrldq	$8, %xmm2, %xmm2
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$0x11, %xmm5, %xmm6, %xmm6
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm0, %xmm1, %xmm1
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm1, %xmm0
        vpshufd	$0x4e, %xmm1, %xmm1
        vpxor	%xmm2, %xmm6, %xmm6
        vpxor	%xmm1, %xmm6, %xmm6
        vpxor	%xmm0, %xmm6, %xmm6
L_AES_GCM_decrypt_avx2_done_dec:
        # calc_tag
        shlq	$3, %r10
        vpinsrq	$0x00, %r10, %xmm0, %xmm0
        shlq	$3, %r11
        vpinsrq	$0x01, %r11, %xmm1, %xmm1
        vpblendd	$12, %xmm1, %xmm0, %xmm0
        vpxor	%xmm6, %xmm0, %xmm0
        # ghash_gfmul_red
        vpclmulqdq	$16, %xmm5, %xmm0, %xmm4
        vpclmulqdq	$0x01, %xmm5, %xmm0, %xmm3
        vpclmulqdq	$0x00, %xmm5, %xmm0, %xmm2
        vpxor	%xmm3, %xmm4, %xmm4
        vpslldq	$8, %xmm4, %xmm3
        vpsrldq	$8, %xmm4, %xmm4
        vpxor	%xmm2, %xmm3, %xmm3
        vpclmulqdq	$0x11, %xmm5, %xmm0, %xmm0
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm3, %xmm2
        vpshufd	$0x4e, %xmm3, %xmm3
        vpxor	%xmm2, %xmm3, %xmm3
        vpclmulqdq	$16, L_avx2_aes_gcm_mod2_128(%rip), %xmm3, %xmm2
        vpshufd	$0x4e, %xmm3, %xmm3
        vpxor	%xmm4, %xmm0, %xmm0
        vpxor	%xmm3, %xmm0, %xmm0
        vpxor	%xmm2, %xmm0, %xmm0
        vpshufb	L_avx2_aes_gcm_bswap_mask(%rip), %xmm0, %xmm0
        vpxor	%xmm15, %xmm0, %xmm0
        # cmp_tag
        cmpl	$16, %r15d
        je	L_AES_GCM_decrypt_avx2_cmp_tag_16
        xorq	%rdx, %rdx
        xorq	%rax, %rax
        vmovdqa	%xmm0, (%rsp)
L_AES_GCM_decrypt_avx2_cmp_tag_loop:
        movzbl	(%rsp,%rdx,1), %r13d
        xorb	(%r14,%rdx,1), %r13b
        orb	%r13b, %al
        incl	%edx
        cmpl	%r15d, %edx
        jne	L_AES_GCM_decrypt_avx2_cmp_tag_loop
        cmpb	$0x00, %al
        sete	%al
        jmp	L_AES_GCM_decrypt_avx2_cmp_tag_done
L_AES_GCM_decrypt_avx2_cmp_tag_16:
        vmovdqu	(%r14), %xmm1
        vpcmpeqb	%xmm1, %xmm0, %xmm0
        vpmovmskb	%xmm0, %rdx
        # %%edx == 0xFFFF then return 1 else => return 0
        xorl	%eax, %eax
        cmpl	$0xffff, %edx
        sete	%al
L_AES_GCM_decrypt_avx2_cmp_tag_done:
        movl	%eax, (%rbp)
        vzeroupper
        addq	$0xa8, %rsp
        popq	%rbp
        popq	%r15
        popq	%rbx
        popq	%r14
        popq	%r12
        popq	%r13
        repz retq
#ifndef __APPLE__
.size	AES_GCM_decrypt_avx2,.-AES_GCM_decrypt_avx2
#endif /* __APPLE__ */
#endif /* HAVE_INTEL_AVX2 */

#if defined(__linux__) && defined(__ELF__)
.section	.note.GNU-stack,"",%progbits
#endif
