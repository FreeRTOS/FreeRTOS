/**
 * \file iar.h
 *
 * \brief Assembler abstraction layer: IAR Assembler specifics
 *
 *
 * Copyright (C) 2016 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 *
 */

#ifndef ASSEMBLER_IAR_H_INCLUDED
#define ASSEMBLER_IAR_H_INCLUDED

/* clang-format off */

ld_addr MACRO   reg, sym
	mov     reg, LWRD sym
	orh     reg, HWRD sym
	ENDM

call    MACRO   sym
	rcall   sym
	ENDM

iar_begin_func  MACRO   name, sect, is_public, is_weak
	MODULE  name
	RSEG    CODE:CODE:NOROOT(1)
	IF      is_weak == 1
	PUBWEAK name
	ELSEIF  is_public
	PUBLIC  name
	ENDIF
name:
	ENDM

iar_begin_func_segm  MACRO   name, sect, is_public, is_weak, segment
	MODULE  name
	RSEG    segment:CODE:NOROOT(1)
	IF      is_weak == 1
	PUBWEAK name
	ELSEIF  is_public
	PUBLIC  name
	ENDIF
name:
	ENDM

iar_weak_alias  MACRO   name, strong_name
	PUBWEAK name
name:
	rjmp    strong_name
	ENDM

#define lo(x)   LWRD x
#define hi(x)   HWRD x

#define REPEAT(count)           REPT    count
#define END_REPEAT()            ENDR
#define SET_LOC(offset)         ORG     offset
#define END_FILE()              END

#define FILL_BYTES(count)       DS8     count

#define L(name)                 name
#define EXTERN_SYMBOL(name)             EXTERN  name
#define FUNCTION(name)          iar_begin_func name, text_##name, 0, 0
#define PUBLIC_FUNCTION(name)   iar_begin_func name, text_##name, 1, 0
#define PUBLIC_FUNCTION_SEGMENT(name, segment)          \
		iar_begin_func_segm name, text_##name, 1, 0, segment
#define WEAK_FUNCTION(name)     iar_begin_func name, text_##name, 1, 1
#define WEAK_FUNCTION_ALIAS(name, strong_name)          \
		iar_weak_alias  name, strong_name
#define END_FUNC(name)          ENDMOD

#define TEXT_SECTION(name)      RSEG    name:CODE:NOROOT
#define RODATA_SECTION(name)    RSEG    name:CONST:NOROOT
#define DATA_SECTION(name)      RSEG    name:DATA:NOROOT
#define BSS_SECTION(name)       RSEG    name:DATA:NOROOT

/* clang-format on */

#endif /* ASSEMBLER_IAR_H_INCLUDED */
