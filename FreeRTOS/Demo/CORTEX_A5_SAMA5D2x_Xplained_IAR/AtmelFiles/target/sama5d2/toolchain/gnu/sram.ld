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

/*------------------------------------------------------------------------------
 *      Linker script for running in internal SRAM on the SAMA5D2
 *----------------------------------------------------------------------------*/

OUTPUT_FORMAT("elf32-littlearm", "elf32-littlearm", "elf32-littlearm")
OUTPUT_ARCH(arm)
ENTRY(entry)
SEARCH_DIR(.)

/* Memory Spaces Definitions */
MEMORY
{
	sram        (W!RX) : ORIGIN = 0x200000,   LENGTH = 128K /* sram */
	ddr         (W!RX) : ORIGIN = 0x20000000, LENGTH = 64M  /* ddr */
	ddr_nocache  (RWX) : ORIGIN = 0x24000000, LENGTH = 16M  /* ddr (non-cached) */
}

/* Sizes of the stacks used by the application. NOTE: you need to adjust */
C_STACK_SIZE   = 0x3000;
IRQ_STACK_SIZE = 0x60;
FIQ_STACK_SIZE = 0x60;
SYS_STACK_SIZE = 0x40;
ABT_STACK_SIZE = 0x40;
UND_STACK_SIZE = 0x40;
HEAP_SIZE      = 0x200;

/* Section Definitions */
SECTIONS
{
	.fixed0 :
	{
		. = ALIGN(4);
		_sfixed = .;
		KEEP(*(.vectors .vectors.*))
		*(.textEntry)
		*(.text .text.* .gnu.linkonce.t.*)
		*(.glue_7t) *(.glue_7)
		*(.cp15_*)
		*(.rodata .rodata* .gnu.linkonce.r.*)
		*(.ARM.extab* .gnu.linkonce.armextab.*)

		/* Support C constructors, and C destructors in both user code
		   and the C library. This also provides support for C++ code. */
		. = ALIGN(4);
		KEEP(*(.init))
		. = ALIGN(4);
		__preinit_array_start = .;
		KEEP (*(.preinit_array))
		__preinit_array_end = .;

		. = ALIGN(4);
		__init_array_start = .;
		KEEP (*(SORT(.init_array.*)))
		KEEP (*(.init_array))
		__init_array_end = .;

		. = ALIGN(0x4);
		KEEP (*crtbegin.o(.ctors))
		KEEP (*(EXCLUDE_FILE (*crtend.o) .ctors))
		KEEP (*(SORT(.ctors.*)))
		KEEP (*crtend.o(.ctors))

		. = ALIGN(4);
		KEEP(*(.fini))

		. = ALIGN(4);
		__fini_array_start = .;
		KEEP (*(.fini_array))
		KEEP (*(SORT(.fini_array.*)))
		__fini_array_end = .;

		KEEP (*crtbegin.o(.dtors))
		KEEP (*(EXCLUDE_FILE (*crtend.o) .dtors))
		KEEP (*(SORT(.dtors.*)))
		KEEP (*crtend.o(.dtors))
		*(.data .data.*);
		. = ALIGN(4);
		_efixed = .;            /* End of text section */

		/* no relocation when running from sram */
		_srelocate = .;
		_erelocate = .;
	} >sram

	/* .ARM.exidx is sorted, so has to go in its own output section.  */
	PROVIDE_HIDDEN (__exidx_start = .);
	.ARM.exidx :
	{
		*(.ARM.exidx* .gnu.linkonce.armexidx.*)
	} >sram
	PROVIDE_HIDDEN (__exidx_end = .);

	. = ALIGN(4);
	_etext = .;

	.region_sram (NOLOAD) :
	{
		. = ALIGN(4);
		*(.region_sram)
	} >sram

	.region_ddr (NOLOAD) :
	{
		. = ALIGN(4);
		*(.region_ddr)
	} >ddr

	.region_ddr_nocache (NOLOAD) :
	{
		. = ALIGN(4);
		*(.region_ddr_nocache)
	} >ddr_nocache

	/* .bss section which is used for uninitialized data */
	.bss (NOLOAD) :
	{
		. = ALIGN(4);
		_sbss = . ;
		_szero = .;
		*(.bss .bss.*)
		*(COMMON)
		. = ALIGN(4);
		_ebss = . ;
		_ezero = .;
	} >sram

	.stack (NOLOAD) :
	{
		__stack_start__ = . ;

		. += IRQ_STACK_SIZE;
		. = ALIGN (4);
		_irqstack = . ;

		. += FIQ_STACK_SIZE;
		. = ALIGN (4);
		_fiqstack = . ;

		. += ABT_STACK_SIZE;
		. = ALIGN (4);
		_abtstack = . ;

		. += UND_STACK_SIZE;
		. = ALIGN (4);
		_undstack = . ;

		. += SYS_STACK_SIZE;
		. = ALIGN (4);
		_sysstack = . ;

		. += C_STACK_SIZE;
		. = ALIGN (4);
		_cstack = . ;

		. += HEAP_SIZE;
		. = ALIGN (4);
		_heap = . ;

		__stack_end__ = .;
	} >sram

	_end = . ;
	__end = . ;
	PROVIDE(end = .);
}
