/* aes_asm.s
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


/* See Intel® Advanced Encryption Standard (AES) Instructions Set White Paper
 * by Intel Mobility Group, Israel Development Center, Israel Shay Gueron
 */

/* This file is in at&t asm syntax, see .asm for intel syntax */


/*
AES_CBC_encrypt (const unsigned char *in,
	unsigned char *out,
	unsigned char ivec[16],
	unsigned long length,
	const unsigned char *KS,
	int nr)
*/
.globl AES_CBC_encrypt
AES_CBC_encrypt:
# parameter 1: %rdi
# parameter 2: %rsi
# parameter 3: %rdx
# parameter 4: %rcx
# parameter 5: %r8
# parameter 6: %r9d
movq	%rcx, %r10
shrq	$4, %rcx
shlq	$60, %r10
je	NO_PARTS
addq	$1, %rcx
NO_PARTS:
subq	$16, %rsi
movdqa	(%rdx), %xmm1
LOOP:
pxor	(%rdi), %xmm1
pxor	(%r8), %xmm1
addq	$16,%rsi
addq	$16,%rdi
cmpl	$12, %r9d
aesenc	16(%r8),%xmm1
aesenc	32(%r8),%xmm1
aesenc	48(%r8),%xmm1
aesenc	64(%r8),%xmm1
aesenc	80(%r8),%xmm1
aesenc	96(%r8),%xmm1
aesenc	112(%r8),%xmm1
aesenc	128(%r8),%xmm1
aesenc	144(%r8),%xmm1
movdqa	160(%r8),%xmm2
jb	LAST
cmpl	$14, %r9d

aesenc	160(%r8),%xmm1
aesenc	176(%r8),%xmm1
movdqa	192(%r8),%xmm2
jb	LAST
aesenc	192(%r8),%xmm1
aesenc	208(%r8),%xmm1
movdqa	224(%r8),%xmm2
LAST:
decq	%rcx
aesenclast %xmm2,%xmm1
movdqu	%xmm1,(%rsi)
jne	LOOP
ret




/*
AES_CBC_decrypt (const unsigned char *in,
  unsigned char *out,
  unsigned char ivec[16],
  unsigned long length,
  const unsigned char *KS,
  int nr)
*/
.globl AES_CBC_decrypt
AES_CBC_decrypt:
# parameter 1: %rdi
# parameter 2: %rsi
# parameter 3: %rdx
# parameter 4: %rcx
# parameter 5: %r8
# parameter 6: %r9d

movq    %rcx, %r10
shrq $4, %rcx
shlq   $60, %r10
je    DNO_PARTS_4
addq    $1, %rcx
DNO_PARTS_4:
movq   %rcx, %r10
shlq    $62, %r10
shrq  $62, %r10
shrq  $2, %rcx
movdqu (%rdx),%xmm5
je DREMAINDER_4
subq   $64, %rsi
DLOOP_4:
movdqu (%rdi), %xmm1
movdqu  16(%rdi), %xmm2
movdqu  32(%rdi), %xmm3
movdqu  48(%rdi), %xmm4
movdqa  %xmm1, %xmm6
movdqa %xmm2, %xmm7
movdqa %xmm3, %xmm8
movdqa %xmm4, %xmm15
movdqa    (%r8), %xmm9
movdqa 16(%r8), %xmm10
movdqa  32(%r8), %xmm11
movdqa  48(%r8), %xmm12
pxor    %xmm9, %xmm1
pxor   %xmm9, %xmm2
pxor   %xmm9, %xmm3

pxor    %xmm9, %xmm4
aesdec %xmm10, %xmm1
aesdec    %xmm10, %xmm2
aesdec    %xmm10, %xmm3
aesdec    %xmm10, %xmm4
aesdec    %xmm11, %xmm1
aesdec    %xmm11, %xmm2
aesdec    %xmm11, %xmm3
aesdec    %xmm11, %xmm4
aesdec    %xmm12, %xmm1
aesdec    %xmm12, %xmm2
aesdec    %xmm12, %xmm3
aesdec    %xmm12, %xmm4
movdqa    64(%r8), %xmm9
movdqa   80(%r8), %xmm10
movdqa  96(%r8), %xmm11
movdqa  112(%r8), %xmm12
aesdec %xmm9, %xmm1
aesdec %xmm9, %xmm2
aesdec %xmm9, %xmm3
aesdec %xmm9, %xmm4
aesdec %xmm10, %xmm1
aesdec    %xmm10, %xmm2
aesdec    %xmm10, %xmm3
aesdec    %xmm10, %xmm4
aesdec    %xmm11, %xmm1
aesdec    %xmm11, %xmm2
aesdec    %xmm11, %xmm3
aesdec    %xmm11, %xmm4
aesdec    %xmm12, %xmm1
aesdec    %xmm12, %xmm2
aesdec    %xmm12, %xmm3
aesdec    %xmm12, %xmm4
movdqa    128(%r8), %xmm9
movdqa  144(%r8), %xmm10
movdqa 160(%r8), %xmm11
cmpl   $12, %r9d
aesdec  %xmm9, %xmm1
aesdec %xmm9, %xmm2
aesdec %xmm9, %xmm3
aesdec %xmm9, %xmm4
aesdec %xmm10, %xmm1
aesdec    %xmm10, %xmm2
aesdec    %xmm10, %xmm3
aesdec    %xmm10, %xmm4
jb    DLAST_4
movdqa  160(%r8), %xmm9
movdqa  176(%r8), %xmm10
movdqa 192(%r8), %xmm11
cmpl   $14, %r9d
aesdec  %xmm9, %xmm1
aesdec %xmm9, %xmm2
aesdec %xmm9, %xmm3
aesdec %xmm9, %xmm4
aesdec %xmm10, %xmm1
aesdec    %xmm10, %xmm2
aesdec    %xmm10, %xmm3
aesdec    %xmm10, %xmm4
jb    DLAST_4

movdqa  192(%r8), %xmm9
movdqa  208(%r8), %xmm10
movdqa 224(%r8), %xmm11
aesdec %xmm9, %xmm1
aesdec %xmm9, %xmm2
aesdec %xmm9, %xmm3
aesdec %xmm9, %xmm4
aesdec %xmm10, %xmm1
aesdec    %xmm10, %xmm2
aesdec    %xmm10, %xmm3
aesdec    %xmm10, %xmm4
DLAST_4:
addq   $64, %rdi
addq    $64, %rsi
decq  %rcx
aesdeclast %xmm11, %xmm1
aesdeclast %xmm11, %xmm2
aesdeclast %xmm11, %xmm3
aesdeclast %xmm11, %xmm4
pxor   %xmm5 ,%xmm1
pxor    %xmm6 ,%xmm2
pxor   %xmm7 ,%xmm3
pxor   %xmm8 ,%xmm4
movdqu %xmm1, (%rsi)
movdqu    %xmm2, 16(%rsi)
movdqu  %xmm3, 32(%rsi)
movdqu  %xmm4, 48(%rsi)
movdqa  %xmm15,%xmm5
jne    DLOOP_4
addq    $64, %rsi
DREMAINDER_4:
cmpq    $0, %r10
je  DEND_4
DLOOP_4_2:
movdqu  (%rdi), %xmm1
movdqa    %xmm1 ,%xmm15
addq  $16, %rdi
pxor  (%r8), %xmm1
movdqu 160(%r8), %xmm2
cmpl    $12, %r9d
aesdec    16(%r8), %xmm1
aesdec   32(%r8), %xmm1
aesdec   48(%r8), %xmm1
aesdec   64(%r8), %xmm1
aesdec   80(%r8), %xmm1
aesdec   96(%r8), %xmm1
aesdec   112(%r8), %xmm1
aesdec  128(%r8), %xmm1
aesdec  144(%r8), %xmm1
jb  DLAST_4_2
movdqu    192(%r8), %xmm2
cmpl    $14, %r9d
aesdec    160(%r8), %xmm1
aesdec  176(%r8), %xmm1
jb  DLAST_4_2
movdqu    224(%r8), %xmm2
aesdec  192(%r8), %xmm1
aesdec  208(%r8), %xmm1
DLAST_4_2:
aesdeclast %xmm2, %xmm1
pxor    %xmm5, %xmm1
movdqa %xmm15, %xmm5
movdqu    %xmm1, (%rsi)

addq    $16, %rsi
decq    %r10
jne DLOOP_4_2
DEND_4:
ret


/*
AES_ECB_encrypt (const unsigned char *in,
	unsigned char *out,
	unsigned long length,
	const unsigned char *KS,
	int nr)
*/
.globl AES_ECB_encrypt
AES_ECB_encrypt:
# parameter 1: %rdi
# parameter 2: %rsi
# parameter 3: %rdx
# parameter 4: %rcx
# parameter 5: %r8d
        movq    %rdx, %r10
        shrq    $4, %rdx
        shlq    $60, %r10
        je      EECB_NO_PARTS_4
        addq    $1, %rdx
EECB_NO_PARTS_4:
        movq    %rdx, %r10
        shlq    $62, %r10
        shrq    $62, %r10
        shrq    $2, %rdx
        je      EECB_REMAINDER_4
        subq    $64, %rsi
EECB_LOOP_4:
        movdqu  (%rdi), %xmm1
        movdqu  16(%rdi), %xmm2
        movdqu  32(%rdi), %xmm3
        movdqu  48(%rdi), %xmm4
        movdqa  (%rcx), %xmm9
        movdqa  16(%rcx), %xmm10
        movdqa  32(%rcx), %xmm11
        movdqa  48(%rcx), %xmm12
        pxor    %xmm9, %xmm1
        pxor    %xmm9, %xmm2
        pxor    %xmm9, %xmm3
        pxor    %xmm9, %xmm4
        aesenc  %xmm10, %xmm1
        aesenc  %xmm10, %xmm2
        aesenc  %xmm10, %xmm3
        aesenc  %xmm10, %xmm4
        aesenc  %xmm11, %xmm1
        aesenc  %xmm11, %xmm2
        aesenc  %xmm11, %xmm3
        aesenc  %xmm11, %xmm4
        aesenc  %xmm12, %xmm1
        aesenc  %xmm12, %xmm2
        aesenc  %xmm12, %xmm3
        aesenc  %xmm12, %xmm4
        movdqa  64(%rcx), %xmm9
        movdqa  80(%rcx), %xmm10
        movdqa  96(%rcx), %xmm11
        movdqa  112(%rcx), %xmm12
        aesenc  %xmm9, %xmm1
        aesenc  %xmm9, %xmm2
        aesenc  %xmm9, %xmm3
        aesenc  %xmm9, %xmm4
        aesenc  %xmm10, %xmm1
        aesenc  %xmm10, %xmm2
        aesenc  %xmm10, %xmm3
        aesenc  %xmm10, %xmm4
        aesenc  %xmm11, %xmm1
        aesenc  %xmm11, %xmm2
        aesenc  %xmm11, %xmm3
        aesenc  %xmm11, %xmm4
        aesenc  %xmm12, %xmm1
        aesenc  %xmm12, %xmm2
        aesenc  %xmm12, %xmm3
        aesenc  %xmm12, %xmm4
        movdqa  128(%rcx), %xmm9
        movdqa  144(%rcx), %xmm10
        movdqa  160(%rcx), %xmm11
        cmpl    $12, %r8d
        aesenc  %xmm9, %xmm1
        aesenc  %xmm9, %xmm2
        aesenc  %xmm9, %xmm3
        aesenc  %xmm9, %xmm4
        aesenc  %xmm10, %xmm1
        aesenc  %xmm10, %xmm2
        aesenc  %xmm10, %xmm3
        aesenc  %xmm10, %xmm4
        jb      EECB_LAST_4
        movdqa  160(%rcx), %xmm9
        movdqa  176(%rcx), %xmm10
        movdqa  192(%rcx), %xmm11
        cmpl    $14, %r8d
        aesenc  %xmm9, %xmm1
        aesenc  %xmm9, %xmm2
        aesenc  %xmm9, %xmm3
        aesenc  %xmm9, %xmm4
        aesenc  %xmm10, %xmm1
        aesenc  %xmm10, %xmm2
        aesenc  %xmm10, %xmm3
        aesenc  %xmm10, %xmm4
        jb      EECB_LAST_4
        movdqa  192(%rcx), %xmm9
        movdqa  208(%rcx), %xmm10
        movdqa  224(%rcx), %xmm11
        aesenc  %xmm9, %xmm1
        aesenc  %xmm9, %xmm2
        aesenc  %xmm9, %xmm3
        aesenc  %xmm9, %xmm4
        aesenc  %xmm10, %xmm1
        aesenc  %xmm10, %xmm2
        aesenc  %xmm10, %xmm3
        aesenc  %xmm10, %xmm4
EECB_LAST_4:
        addq    $64, %rdi
        addq    $64, %rsi
        decq    %rdx
        aesenclast %xmm11, %xmm1
        aesenclast %xmm11, %xmm2
        aesenclast %xmm11, %xmm3
        aesenclast %xmm11, %xmm4
        movdqu  %xmm1, (%rsi)
        movdqu  %xmm2, 16(%rsi)
        movdqu  %xmm3, 32(%rsi)
        movdqu  %xmm4, 48(%rsi)
        jne     EECB_LOOP_4
        addq    $64, %rsi
EECB_REMAINDER_4:
        cmpq    $0, %r10
        je      EECB_END_4
EECB_LOOP_4_2:
        movdqu  (%rdi), %xmm1
        addq    $16, %rdi
        pxor    (%rcx), %xmm1
        movdqu  160(%rcx), %xmm2
        aesenc  16(%rcx), %xmm1
        aesenc  32(%rcx), %xmm1
        aesenc  48(%rcx), %xmm1
        aesenc  64(%rcx), %xmm1
        aesenc  80(%rcx), %xmm1
        aesenc  96(%rcx), %xmm1
        aesenc  112(%rcx), %xmm1
        aesenc  128(%rcx), %xmm1
        aesenc  144(%rcx), %xmm1
        cmpl    $12, %r8d
        jb      EECB_LAST_4_2
        movdqu  192(%rcx), %xmm2
        aesenc  160(%rcx), %xmm1
        aesenc  176(%rcx), %xmm1
        cmpl    $14, %r8d
        jb      EECB_LAST_4_2
        movdqu  224(%rcx), %xmm2
        aesenc  192(%rcx), %xmm1
        aesenc  208(%rcx), %xmm1
EECB_LAST_4_2:
        aesenclast %xmm2, %xmm1
        movdqu  %xmm1, (%rsi)
        addq    $16, %rsi
        decq    %r10
        jne     EECB_LOOP_4_2
EECB_END_4:
        ret


/*
AES_ECB_decrypt (const unsigned char *in,
  unsigned char *out,
  unsigned long length,
  const unsigned char *KS,
  int nr)
*/
.globl AES_ECB_decrypt
AES_ECB_decrypt:
# parameter 1: %rdi
# parameter 2: %rsi
# parameter 3: %rdx
# parameter 4: %rcx
# parameter 5: %r8d

        movq    %rdx, %r10
        shrq    $4, %rdx
        shlq    $60, %r10
        je      DECB_NO_PARTS_4
        addq    $1, %rdx
DECB_NO_PARTS_4:
        movq    %rdx, %r10
        shlq    $62, %r10
        shrq    $62, %r10
        shrq    $2, %rdx
        je      DECB_REMAINDER_4
        subq    $64, %rsi
DECB_LOOP_4:
        movdqu  (%rdi), %xmm1
        movdqu  16(%rdi), %xmm2
        movdqu  32(%rdi), %xmm3
        movdqu  48(%rdi), %xmm4
        movdqa  (%rcx), %xmm9
        movdqa  16(%rcx), %xmm10
        movdqa  32(%rcx), %xmm11
        movdqa  48(%rcx), %xmm12
        pxor    %xmm9, %xmm1
        pxor    %xmm9, %xmm2
        pxor    %xmm9, %xmm3
        pxor    %xmm9, %xmm4
        aesdec  %xmm10, %xmm1
        aesdec  %xmm10, %xmm2
        aesdec  %xmm10, %xmm3
        aesdec  %xmm10, %xmm4
        aesdec  %xmm11, %xmm1
        aesdec  %xmm11, %xmm2
        aesdec  %xmm11, %xmm3
        aesdec  %xmm11, %xmm4
        aesdec  %xmm12, %xmm1
        aesdec  %xmm12, %xmm2
        aesdec  %xmm12, %xmm3
        aesdec  %xmm12, %xmm4
        movdqa  64(%rcx), %xmm9
        movdqa  80(%rcx), %xmm10
        movdqa  96(%rcx), %xmm11
        movdqa  112(%rcx), %xmm12
        aesdec  %xmm9, %xmm1
        aesdec  %xmm9, %xmm2
        aesdec  %xmm9, %xmm3
        aesdec  %xmm9, %xmm4
        aesdec  %xmm10, %xmm1
        aesdec  %xmm10, %xmm2
        aesdec  %xmm10, %xmm3
        aesdec  %xmm10, %xmm4
        aesdec  %xmm11, %xmm1
        aesdec  %xmm11, %xmm2
        aesdec  %xmm11, %xmm3
        aesdec  %xmm11, %xmm4
        aesdec  %xmm12, %xmm1
        aesdec  %xmm12, %xmm2
        aesdec  %xmm12, %xmm3
        aesdec  %xmm12, %xmm4
        movdqa  128(%rcx), %xmm9
        movdqa  144(%rcx), %xmm10
        movdqa  160(%rcx), %xmm11
        cmpl    $12, %r8d
        aesdec  %xmm9, %xmm1
        aesdec  %xmm9, %xmm2
        aesdec  %xmm9, %xmm3
        aesdec  %xmm9, %xmm4
        aesdec  %xmm10, %xmm1
        aesdec  %xmm10, %xmm2
        aesdec  %xmm10, %xmm3
        aesdec  %xmm10, %xmm4
        jb      DECB_LAST_4
        movdqa  160(%rcx), %xmm9
        movdqa  176(%rcx), %xmm10
        movdqa  192(%rcx), %xmm11
        cmpl    $14, %r8d
        aesdec  %xmm9, %xmm1
        aesdec  %xmm9, %xmm2
        aesdec  %xmm9, %xmm3
        aesdec  %xmm9, %xmm4
        aesdec  %xmm10, %xmm1
        aesdec  %xmm10, %xmm2
        aesdec  %xmm10, %xmm3
        aesdec  %xmm10, %xmm4
        jb      DECB_LAST_4
        movdqa  192(%rcx), %xmm9
        movdqa  208(%rcx), %xmm10
        movdqa  224(%rcx), %xmm11
        aesdec  %xmm9, %xmm1
        aesdec  %xmm9, %xmm2
        aesdec  %xmm9, %xmm3
        aesdec  %xmm9, %xmm4
        aesdec  %xmm10, %xmm1
        aesdec  %xmm10, %xmm2
        aesdec  %xmm10, %xmm3
        aesdec  %xmm10, %xmm4
DECB_LAST_4:
        addq    $64, %rdi
        addq    $64, %rsi
        decq    %rdx
        aesdeclast %xmm11, %xmm1
        aesdeclast %xmm11, %xmm2
        aesdeclast %xmm11, %xmm3
        aesdeclast %xmm11, %xmm4
        movdqu  %xmm1, (%rsi)
        movdqu  %xmm2, 16(%rsi)
        movdqu  %xmm3, 32(%rsi)
        movdqu  %xmm4, 48(%rsi)
        jne     DECB_LOOP_4
        addq    $64, %rsi
DECB_REMAINDER_4:
        cmpq    $0, %r10
        je      DECB_END_4
DECB_LOOP_4_2:
        movdqu  (%rdi), %xmm1
        addq    $16, %rdi
        pxor    (%rcx), %xmm1
        movdqu  160(%rcx), %xmm2
        cmpl    $12, %r8d
        aesdec  16(%rcx), %xmm1
        aesdec  32(%rcx), %xmm1
        aesdec  48(%rcx), %xmm1
        aesdec  64(%rcx), %xmm1
        aesdec  80(%rcx), %xmm1
        aesdec  96(%rcx), %xmm1
        aesdec  112(%rcx), %xmm1
        aesdec  128(%rcx), %xmm1
        aesdec  144(%rcx), %xmm1
        jb      DECB_LAST_4_2
        cmpl    $14, %r8d
        movdqu  192(%rcx), %xmm2
        aesdec  160(%rcx), %xmm1
        aesdec  176(%rcx), %xmm1
        jb      DECB_LAST_4_2
        movdqu  224(%rcx), %xmm2
        aesdec  192(%rcx), %xmm1
        aesdec  208(%rcx), %xmm1
DECB_LAST_4_2:
        aesdeclast %xmm2, %xmm1
        movdqu  %xmm1, (%rsi)
        addq    $16, %rsi
        decq    %r10
        jne     DECB_LOOP_4_2
DECB_END_4:
        ret




/*
void AES_128_Key_Expansion(const unsigned char* userkey,
   unsigned char* key_schedule);
*/
.align  16,0x90
.globl AES_128_Key_Expansion
AES_128_Key_Expansion:
# parameter 1: %rdi
# parameter 2: %rsi
movl    $10, 240(%rsi)

movdqu  (%rdi), %xmm1
movdqa    %xmm1, (%rsi)


ASSISTS:
aeskeygenassist $1, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 16(%rsi)
aeskeygenassist $2, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 32(%rsi)
aeskeygenassist $4, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 48(%rsi)
aeskeygenassist $8, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 64(%rsi)
aeskeygenassist $16, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 80(%rsi)
aeskeygenassist $32, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 96(%rsi)
aeskeygenassist $64, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 112(%rsi)
aeskeygenassist $0x80, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 128(%rsi)
aeskeygenassist $0x1b, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 144(%rsi)
aeskeygenassist $0x36, %xmm1, %xmm2
call PREPARE_ROUNDKEY_128
movdqa %xmm1, 160(%rsi)
ret

PREPARE_ROUNDKEY_128:
pshufd $255, %xmm2, %xmm2
movdqa %xmm1, %xmm3
pslldq $4, %xmm3
pxor %xmm3, %xmm1
pslldq $4, %xmm3
pxor %xmm3, %xmm1
pslldq $4, %xmm3
pxor %xmm3, %xmm1
pxor %xmm2, %xmm1
ret


/*
void AES_192_Key_Expansion (const unsigned char *userkey,
  unsigned char *key)
*/
.globl AES_192_Key_Expansion
AES_192_Key_Expansion:
# parameter 1: %rdi
# parameter 2: %rsi

movdqu (%rdi), %xmm1
movdqu 16(%rdi), %xmm3
movdqa %xmm1, (%rsi)
movdqa %xmm3, %xmm5

aeskeygenassist $0x1, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
shufpd $0, %xmm1, %xmm5
movdqa %xmm5, 16(%rsi)
movdqa %xmm1, %xmm6
shufpd $1, %xmm3, %xmm6
movdqa %xmm6, 32(%rsi)

aeskeygenassist $0x2, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
movdqa %xmm1, 48(%rsi)
movdqa %xmm3, %xmm5

aeskeygenassist $0x4, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
shufpd $0, %xmm1, %xmm5
movdqa %xmm5, 64(%rsi)
movdqa %xmm1, %xmm6
shufpd $1, %xmm3, %xmm6
movdqa %xmm6, 80(%rsi)

aeskeygenassist $0x8, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
movdqa %xmm1, 96(%rsi)
movdqa %xmm3, %xmm5

aeskeygenassist $0x10, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
shufpd $0, %xmm1, %xmm5
movdqa %xmm5, 112(%rsi)
movdqa %xmm1, %xmm6
shufpd $1, %xmm3, %xmm6
movdqa %xmm6, 128(%rsi)

aeskeygenassist $0x20, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
movdqa %xmm1, 144(%rsi)
movdqa %xmm3, %xmm5

aeskeygenassist $0x40, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
shufpd $0, %xmm1, %xmm5
movdqa %xmm5, 160(%rsi)
movdqa %xmm1, %xmm6
shufpd $1, %xmm3, %xmm6
movdqa %xmm6, 176(%rsi)

aeskeygenassist $0x80, %xmm3, %xmm2
call PREPARE_ROUNDKEY_192
movdqa %xmm1, 192(%rsi)
movdqa %xmm3, 208(%rsi)
ret

PREPARE_ROUNDKEY_192:
pshufd $0x55, %xmm2, %xmm2
movdqu %xmm1, %xmm4
pslldq $4, %xmm4
pxor   %xmm4, %xmm1

pslldq $4, %xmm4
pxor   %xmm4, %xmm1
pslldq $4, %xmm4
pxor  %xmm4, %xmm1
pxor   %xmm2, %xmm1
pshufd $0xff, %xmm1, %xmm2
movdqu %xmm3, %xmm4
pslldq $4, %xmm4
pxor   %xmm4, %xmm3
pxor   %xmm2, %xmm3
ret
 

/*
void AES_256_Key_Expansion (const unsigned char *userkey,
  unsigned char *key)
*/
.globl AES_256_Key_Expansion
AES_256_Key_Expansion:
# parameter 1: %rdi
# parameter 2: %rsi

movdqu (%rdi), %xmm1
movdqu 16(%rdi), %xmm3
movdqa %xmm1, (%rsi)
movdqa %xmm3, 16(%rsi)

aeskeygenassist $0x1, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 32(%rsi)
aeskeygenassist $0x0, %xmm1, %xmm2
call MAKE_RK256_b
movdqa %xmm3, 48(%rsi)
aeskeygenassist $0x2, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 64(%rsi)
aeskeygenassist $0x0, %xmm1, %xmm2
call MAKE_RK256_b
movdqa %xmm3, 80(%rsi)
aeskeygenassist $0x4, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 96(%rsi)
aeskeygenassist $0x0, %xmm1, %xmm2
call MAKE_RK256_b
movdqa %xmm3, 112(%rsi)
aeskeygenassist $0x8, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 128(%rsi)
aeskeygenassist $0x0, %xmm1, %xmm2
call MAKE_RK256_b
movdqa %xmm3, 144(%rsi)
aeskeygenassist $0x10, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 160(%rsi)
aeskeygenassist $0x0, %xmm1, %xmm2
call MAKE_RK256_b
movdqa %xmm3, 176(%rsi)
aeskeygenassist $0x20, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 192(%rsi)

aeskeygenassist $0x0, %xmm1, %xmm2
call MAKE_RK256_b
movdqa %xmm3, 208(%rsi)
aeskeygenassist $0x40, %xmm3, %xmm2
call MAKE_RK256_a
movdqa %xmm1, 224(%rsi)

ret

MAKE_RK256_a:
pshufd $0xff, %xmm2, %xmm2
movdqa %xmm1, %xmm4
pslldq $4, %xmm4
pxor   %xmm4, %xmm1
pslldq $4, %xmm4
pxor  %xmm4, %xmm1
pslldq $4, %xmm4
pxor  %xmm4, %xmm1
pxor   %xmm2, %xmm1
ret

MAKE_RK256_b:
pshufd $0xaa, %xmm2, %xmm2
movdqa %xmm3, %xmm4
pslldq $4, %xmm4
pxor   %xmm4, %xmm3
pslldq $4, %xmm4
pxor  %xmm4, %xmm3
pslldq $4, %xmm4
pxor  %xmm4, %xmm3
pxor   %xmm2, %xmm3
ret

