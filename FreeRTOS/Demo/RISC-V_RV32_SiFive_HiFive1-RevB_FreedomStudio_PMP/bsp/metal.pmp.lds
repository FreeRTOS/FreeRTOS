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
	itim (wx!rai) : ORIGIN = 0x8000000, LENGTH = 0x2000
}

/* Elf32_Phdr.p_type -- PT_LOAD  (a loadable segment). */
PHDRS
{
	flash PT_LOAD;
	ram_init PT_LOAD;
	itim_init PT_LOAD;
	ram PT_LOAD;
	itim PT_LOAD;
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

	/* FreeRTOS kernel function.
	   In v10.3.0, the size of this section is 0x4a2e bytes which rounds up to 0x8000. 
	   Thus, set forced output alignment to 0x8000 bytes. 
	   The start address of this section will be used in PMP initialization.
	   todo: M-mode R/X access, U-mode no access.
	*/
	.privileged_functions :		ALIGN(0x8000)
 	{
 		_privileged_function_start = .; 
		KEEP(*(.isr_vector)) /* Startup code. */
		. = ALIGN(4);
		*(privileged_functions)
		. = ALIGN(4);
		FILL(0xDEAD);
		/* Ensure that non-privileged code is placed after the region reserved for
		 * privileged kernel code. */
		. = ALIGN(0x8000);
	} >flash AT>flash :flash


	/* The 0x10000 alignment is to make .text region fit into a PMP address matching rule. 
	   The options here:
	   - use more than one PMP region, so that minimize flash fragmentation. 
	     Note that there are only 8 PMP regions on fe310-g002.
	   - use one PMP region, with the understanding that .privileged_functions and .text may not be contiguous. 
	     The in between flash addresses are not used.
	   In either case, every time software is modified, user needs to come back and reassess whetehr the configuration is still correct.
	*/
	.text 		:			ALIGN(0x10000)
	{
		*(.text.unlikely .text.unlikely.*)
		*(.text.startup .text.startup.*)
		*(.text .text.*)
		*(.itim .itim.*)
		*(.gnu.linkonce.t.*)
		. = ALIGN(0x10000);
	} >flash AT>flash :flash


	/* Address used for PMP configuration, use ADDR instead of LOADADDR! */	
	PROVIDE( _common_function_start = ADDR(.text) );


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

	.itim 		:
	{
		. = ALIGN(4);
		*(.itim .itim.*)
	} >itim AT>flash :itim_init

	PROVIDE( metal_segment_itim_source_start = LOADADDR(.itim) );
	PROVIDE( metal_segment_itim_target_start = ADDR(.itim) );
	PROVIDE( metal_segment_itim_target_end = ADDR(.itim) + SIZEOF(.itim) );


	/* FreeRTOS kernel data. 
	   In v10.3.0, the size of this section is 0x1a8 bytes which rounds up to 0x200.
	   Thus set forced output alignment to 0x200 bytes. 
	   The start address of this section will be used in PMP initialization.
	   todo: M-mode R/W access, U-mode no access.
	*/
	.privileged_data :		ALIGN(0x200)
	{ 
		*(privileged_data)
		. = ALIGN(8);
		FILL(0xDEAD);
		/* Ensure that non-privileged data is placed after the region reserved for
		 * privileged kernel data. */
		. = ALIGN(0x200);
	} >ram AT>flash :ram_init

	/* .data and .bss section HAVE TO be placed right after .privileged_data section.
	   In the PMP entry for .data and .bss R/W only, TOR address matching with be used.
	*/
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

	PROVIDE( metal_segment_data_source_start = LOADADDR(.privileged_data) );
	PROVIDE( metal_segment_data_target_start = ADDR(.privileged_data) );
	PROVIDE( metal_segment_data_target_end = ADDR(.privileged_data) + SIZEOF(.data) + SIZEOF(.privileged_data) );

	/* Address used for PMP configuration, use ADDR instead of LOADADDR! */
	PROVIDE( _privileged_data_start = ADDR(.privileged_data) );

	PROVIDE( _fbss = . );
	PROVIDE( __bss_start = . );

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
	PROVIDE( metal_segment_bss_target_start = ADDR(.bss) );
	PROVIDE( metal_segment_bss_target_end = ADDR(.bss) + SIZEOF(.bss) );

	/* Address used for PMP configuration, use ADDR instead of LOADADDR! */
	PROVIDE( _common_data_end = ADDR(.bss) + SIZEOF(.bss) );

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

