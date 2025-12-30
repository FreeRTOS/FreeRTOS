/* linker
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */

OUTPUT_FORMAT("elf64-x86-64")
OUTPUT_ARCH(i386:x86-64)
ENTRY(start)

SECTIONS
{
    . = 1M;

    .boot :
    {
        KEEP(*(.multiboot_header))
    }
    .note : 
    {
        KEEP(*(.note*))
        KEEP(*(.note.*))
    }
    .text ALIGN(4096) :
    {
	_text = .;
        *(.text*)
        *(.text.*)
    }
    privileged_functions ALIGN(4096) :
    {
        *(privileged_functions*)
    }
    privileged_data ALIGN(4096) :
    {
        *(privileged_data*)
    }
    .data ALIGN(4096) : {
        *(.data*)
        *(.data.*)
    }
    .rodata ALIGN(4096) : {
        __rodata_start = .;
        *(.rodata*)
        *(.rodata.*)
        __rodata_end = .;
    }
    .eh_frame ALIGN(4096) : {
        *(.eh_frame*)
        *(.eh_frame.*)
        __eh_frame = .;
    }
    .  = ALIGN(4096);
    .bss ALIGN(4096) : {
        *(.bss*)
        *(.bss.*)
    }
    .usercode ALIGN(4096) :
    {
        __usercode_start = .;
        *(.usercode)
        .  = ALIGN(4096);
        __usercode_end = .;
    }
    .userdata ALIGN(4096) :
    {
        __userdata_start = .;
        *(.userdata)
        .  = ALIGN(4096);
        __userdata_end = .;
    }
    freertos_system_calls ALIGN(4096) :
    {
        __system_calls_start = .;
        *(freertos_system_calls)
        .  = ALIGN(4096);
        __system_calls_end = .;
    }
    .application_apis ALIGN(4096) :
    {
        __apis_start = .;
        *(.application_apis)
        .  = ALIGN(4096);
        __apis_end = .;
    }
    .comment :
    {
        *(.comment)
    }

    . = ALIGN(4096);
    end = .;

}
