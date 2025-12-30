/* elf_ia32_efi 
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

OUTPUT_FORMAT("elf32-i386")
OUTPUT_ARCH(i386)
ENTRY(_start)

physbase = 0x00100000;

SECTIONS
{	
 	. = physbase;
	. = ALIGN(4096);
        .note :
        {
            *(.note*)
            *(.note.*)
        }
 	.text :
	{
	    __text_start =  ABSOLUTE(.);
	    *(.text.entry)
	    *(.text)
	    *(.text.last)
	    *(.text.*)
	    . = ALIGN(4);
		*(.rodata)
		*( .rodata.*)
		__rodata_end = .;
 	    __text_end =  ABSOLUTE(.);
  		. = ALIGN(4096);
	}

	
	/* Read-write data (initialised) */
 	.data :
	{
 		__data_start = ABSOLUTE(.);
  		__data_lma = LOADADDR(.data); 
  		__data_vma =  ABSOLUTE(.);
 		*(.data)
 		*(.data.*)
 		__data_end = ABSOLUTE(.);
 		. = ALIGN(4096);
 	}

	/* Read-write data (uninitialised) */
 	.bss :
	{
    	__bss_start =  ABSOLUTE(.);
    	*(.bss)
     	*(COMMON)
    	__bss_end =  ABSOLUTE(.);
   		. = ALIGN(1024);
 	}
	
	/* stack used before the scheduler starts */
 	.boot_stack :
	{
		/* 2K for the boot stack.  This could be avoided by using the same RAM
		as used by the FreeRTOS system/interrupt stack. */
		. += 2048;
    	__stack_for_main = ABSOLUTE( . );
   		. = ALIGN(1024);
 	}

	/*exception unwinding and source language information */
	.eh_frame : { KEEP (*(.eh_frame)) . = ALIGN(4); }

	/* function exports */
 	.drectve : { KEEP (*(.drectve)) }
  	
   	.comment 0 : { *(.comment) }

}
