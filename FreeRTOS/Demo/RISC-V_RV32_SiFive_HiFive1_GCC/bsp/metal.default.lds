/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */
/* ----------------------------------- */
/* ----------------------------------- */

OUTPUT_ARCH("riscv")

ENTRY(_enter)

MEMORY
{
	ram (wxa!ri) : ORIGIN = 0x80000000, LENGTH = 0x4000
	flash (rxai!w) : ORIGIN = 0x20010000, LENGTH = 0x6a120
}

PHDRS
{
	flash PT_LOAD;
	ram_init PT_LOAD;
	itim_init PT_LOAD;
	ram PT_NULL;
	itim PT_NULL;
}

SECTIONS
{
	__stack_size = DEFINED(__stack_size) ? __stack_size : 0x400;
	PROVIDE(__stack_size = __stack_size);
	__heap_size = DEFINED(__heap_size) ? __heap_size : 0x4;
	PROVIDE(__metal_boot_hart = 0);
	PROVIDE(__metal_chicken_bit = 0);


	.init 		:
	{
		KEEP (*(.text.metal.init.enter))
		KEEP (*(SORT_NONE(.init)))
		KEEP (*(.text.libgloss.start))
	} >flash AT>flash :flash


	.text 		:
	{
		*(.text.unlikely .text.unlikely.*)
		*(.text.startup .text.startup.*)
		*(.text .text.*)
		*(.itim .itim.*)
		*(.gnu.linkonce.t.*)
	} >flash AT>flash :flash


	.fini 		:
	{
		KEEP (*(SORT_NONE(.fini)))
	} >flash AT>flash :flash


	PROVIDE (__etext = .);
	PROVIDE (_etext = .);
	PROVIDE (etext = .);


	.rodata 		:
	{
		*(.rdata)
		*(.rodata .rodata.*)
		*(.gnu.linkonce.r.*)
		. = ALIGN(8);
		*(.srodata.cst16)
		*(.srodata.cst8)
		*(.srodata.cst4)
		*(.srodata.cst2)
		*(.srodata .srodata.*)
	} >flash AT>flash :flash


	. = ALIGN(4);


	.preinit_array 		:
	{
		PROVIDE_HIDDEN (__preinit_array_start = .);
		KEEP (*(.preinit_array))
		PROVIDE_HIDDEN (__preinit_array_end = .);
	} >flash AT>flash :flash


	.init_array 		:
	{
		PROVIDE_HIDDEN (__init_array_start = .);
		KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*) SORT_BY_INIT_PRIORITY(.ctors.*)))
		KEEP (*(.init_array EXCLUDE_FILE (*crtbegin.o *crtbegin?.o *crtend.o *crtend?.o ) .ctors))
		PROVIDE_HIDDEN (__init_array_end = .);
	} >flash AT>flash :flash


	.fini_array 		:
	{
		PROVIDE_HIDDEN (__fini_array_start = .);
		KEEP (*(SORT_BY_INIT_PRIORITY(.fini_array.*) SORT_BY_INIT_PRIORITY(.dtors.*)))
		KEEP (*(.fini_array EXCLUDE_FILE (*crtbegin.o *crtbegin?.o *crtend.o *crtend?.o ) .dtors))
		PROVIDE_HIDDEN (__fini_array_end = .);
	} >flash AT>flash :flash


	.ctors 		:
	{
		/* gcc uses crtbegin.o to find the start of
		   the constructors, so we make sure it is
		   first.  Because this is a wildcard, it
		   doesn't matter if the user does not
		   actually link against crtbegin.o; the
		   linker won't look for a file to match a
		   wildcard.  The wildcard also means that it
		   doesn't matter which directory crtbegin.o
		   is in.  */
		KEEP (*crtbegin.o(.ctors))
		KEEP (*crtbegin?.o(.ctors))
		/* We don't want to include the .ctor section from
		   the crtend.o file until after the sorted ctors.
		   The .ctor section from the crtend file contains the
		   end of ctors marker and it must be last */
		KEEP (*(EXCLUDE_FILE (*crtend.o *crtend?.o ) .ctors))
		KEEP (*(SORT(.ctors.*)))
		KEEP (*(.ctors))
	} >flash AT>flash :flash


	.dtors 		:
	{
		KEEP (*crtbegin.o(.dtors))
		KEEP (*crtbegin?.o(.dtors))
		KEEP (*(EXCLUDE_FILE (*crtend.o *crtend?.o ) .dtors))
		KEEP (*(SORT(.dtors.*)))
		KEEP (*(.dtors))
	} >flash AT>flash :flash


	.litimalign 		:
	{
		. = ALIGN(4);
		PROVIDE( metal_segment_itim_source_start = . );
	} >flash AT>flash :flash


	.ditimalign 		:
	{
		. = ALIGN(4);
		PROVIDE( metal_segment_itim_target_start = . );
	} >ram AT>flash :ram_init


	.itim 		:
	{
		*(.itim .itim.*)
	} >flash AT>flash :flash


	. = ALIGN(8);
	PROVIDE( metal_segment_itim_target_end = . );


	.lalign 		:
	{
		. = ALIGN(4);
		PROVIDE( _data_lma = . );
		PROVIDE( metal_segment_data_source_start = . );
	} >flash AT>flash :flash


	.dalign 		:
	{
		. = ALIGN(4);
		PROVIDE( metal_segment_data_target_start = . );
	} >ram AT>flash :ram_init


	.data 		:
	{
		*(.data .data.*)
		*(.gnu.linkonce.d.*)
		. = ALIGN(8);
		PROVIDE( __global_pointer$ = . + 0x800 );
		*(.sdata .sdata.* .sdata2.*)
		*(.gnu.linkonce.s.*)
	} >ram AT>flash :ram_init


	. = ALIGN(4);
	PROVIDE( _edata = . );
	PROVIDE( edata = . );
	PROVIDE( metal_segment_data_target_end = . );
	PROVIDE( _fbss = . );
	PROVIDE( __bss_start = . );
	PROVIDE( metal_segment_bss_target_start = . );


	.bss 		:
	{
		*(.sbss*)
		*(.gnu.linkonce.sb.*)
		*(.bss .bss.*)
		*(.gnu.linkonce.b.*)
		*(COMMON)
		. = ALIGN(4);
	} >ram AT>ram :ram


	. = ALIGN(8);
	PROVIDE( _end = . );
	PROVIDE( end = . );
	PROVIDE( metal_segment_bss_target_end = . );

	.stack :
	{
		. = ALIGN(16);
		metal_segment_stack_begin = .;
		. += __stack_size;
		. = ALIGN(16);
		_sp = .;		
		PROVIDE(metal_segment_stack_end = .);
		__freertos_irq_stack_top = .;
	} >ram AT>ram :ram


	.heap :
	{
		PROVIDE( metal_segment_heap_target_start = . );
		. = __heap_size;
		PROVIDE( metal_segment_heap_target_end = . );
		PROVIDE( _heap_end = . );
	} >ram AT>ram :ram


}

