/**
 * \file gas.h
 *
 * \brief Assembler abstraction layer: GNU Assembler specifics
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
#ifndef ASSEMBLER_GAS_H_INCLUDED
#define ASSEMBLER_GAS_H_INCLUDED

#ifndef __DOXYGEN__

/* clang-format off */

        /* IAR doesn't accept dots in macro names */
        .macro  ld_addr, reg, sym
        lda.w   \reg, \sym
        .endm

        /* Define a function \a name that is either globally visible or only
         * file-local.
         */
        .macro gas_begin_func name, is_public
                .if \is_public
                .global \name
                .endif
                .section .text.\name, "ax", @progbits
                .type \name, @function
        \name :
        .endm

        /* Define a function \a name that is either globally visible or only
         * file-local in a given segment.
         */
        .macro gas_begin_func_segm name, is_public, segment
                .if \is_public
                .global \name
                .endif
                .section .\segment, "ax", @progbits
                .type \name, @function
        \name :
        .endm

        /* Define \a name as a weak alias for the function \a strong_name */
        .macro gas_weak_function_alias name, strong_name
        .global \name
        .weak   \name
        .type   \name, @function
        .set    \name, \strong_name
        .endm

        /* Define a weak function called \a name */
        .macro gas_weak_function name
        .weak   \name
        gas_begin_func \name 1
        .endm

#define REPEAT(count)           .rept   count
#define END_REPEAT()            .endr
#define FILL_BYTES(count)       .fill   count
#define SET_LOC(offset)         .org    offset
#define L(name)                 .L##name
#define EXTERN_SYMBOL(name)

#define TEXT_SECTION(name)                              \
        .section name, "ax", @progbits
#define RODATA_SECTION(name)                            \
        .section name, "a", @progbits
#define DATA_SECTION(name)                              \
        .section name, "aw", @progbits
#define BSS_SECTION(name)                               \
        .section name, "aw", @nobits

#define FUNCTION(name) gas_begin_func name 0
#define PUBLIC_FUNCTION(name)   gas_begin_func name 1
#define PUBLIC_FUNCTION_SEGMENT(name, segment)          \
        gas_begin_func_segm name 1 segment
#define WEAK_FUNCTION(name) gas_weak_function name
#define WEAK_FUNCTION_ALIAS(name, strong_name) \
        gas_weak_function_alias name strong_name
#define END_FUNC(name)                                  \
        .size   name, . - name

#define END_FILE()

/* clang-format on */

#endif /* __DOXYGEN__ */

#endif /* ASSEMBLER_GAS_H_INCLUDED */
