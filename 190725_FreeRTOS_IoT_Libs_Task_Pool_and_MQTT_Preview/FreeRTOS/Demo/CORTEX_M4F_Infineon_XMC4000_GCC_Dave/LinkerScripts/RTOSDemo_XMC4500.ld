/* Generated Linker Script file */
/*
 * Template Version 1.0 dated 11 Oct 2012
 */

OUTPUT_FORMAT("elf32-littlearm")
OUTPUT_ARCH(arm)
ENTRY(__Xmc4500_reset_cortex_m)
GROUP(-lxmclibcstubs)

MEMORY
{
	FLASH_1_cached(RX) : ORIGIN = 0x08000000, LENGTH = 0x100000
	FLASH_1_uncached(RX) : ORIGIN = 0x0C000000, LENGTH = 0x100000
	PSRAM_1(!RX) : ORIGIN = 0x10000000, LENGTH = 0x10000
	DSRAM_1_system(!RX) : ORIGIN = 0x20000000, LENGTH = 0x10000
	DSRAM_2_comm(!RX) : ORIGIN = 0x30000000, LENGTH = 0x8000
}

stack_size = 2048;

SECTIONS
{
	/* TEXT section */

	.text : AT(ORIGIN(FLASH_1_uncached))
	{
		sText = .;
		*(.Xmc4500.reset);
		*(.Xmc4500.postreset);
		*(.XmcStartup);
		*(.text .text.* .gnu.linkonce.t.*);

		/* ARM <->THUMB interworking */
		*(.glue*)
		*(.v4*)
		*(.vfp11_veneer)

		/* C++ Support */
		KEEP(*(.init))
		__preinit_array_start = .;
		KEEP (*(.preinit_array))
		__preinit_array_end = .;
		__init_array_start = .;
		KEEP (*(SORT(.init_array.*)))
		KEEP (*(.init_array))
		__init_array_end = .;
		KEEP (*crtbegin.o(.ctors))
		KEEP (*(EXCLUDE_FILE (*crtend.o) .ctors))
		KEEP (*(SORT(.ctors.*)))
		KEEP (*crtend.o(.ctors))
		KEEP(*(.fini))
		__fini_array_start = .;
		KEEP (*(.fini_array))
		KEEP (*(SORT(.fini_array.*)))
		__fini_array_end = .;

		KEEP (*crtbegin.o(.dtors))
		KEEP (*(EXCLUDE_FILE (*crtend.o) .dtors))
		KEEP (*(SORT(.dtors.*)))
		KEEP (*crtend.o(.dtors))

		/* Exception handling support */
		__extab_start = .;
		*(.ARM.extab* .gnu.linkonce.armextab.*)
		. = ALIGN(4);
		__extab_end = ABSOLUTE(.);
	} > FLASH_1_cached

	/* Exception handling, exidx needs a dedicated section */
	.ARM.exidx ABSOLUTE(__extab_end): AT(__extab_end | 0x04000000)
	{
		__exidx_start = .;
		*(.ARM.exidx* .gnu.linkonce.armexidx.*)
		. = ALIGN(4);
		__exidx_end = ABSOLUTE(.);
	} > FLASH_1_cached

	/* CONST data section */
	.rodata ABSOLUTE(__exidx_end): AT(__exidx_end | 0x04000000)
	{
		*(.rodata .rodata.*)
		*(.gnu.linkonce.r*)
	} > FLASH_1_cached

	. = ALIGN(16);

	/* End of RO-DATA and start of LOAD region for DATA */
	eROData = . | 0x04000000;

	/* DSRAM layout (Lowest to highest)*/
	/* Fully Descending Stack <-> BSS <-> DATA <-> HEAP */
	/* Dummy section for stack */
	Stack (NOLOAD) : 
	{
		. = . + stack_size;
		__Xmc4500_stack = .;
	} > DSRAM_1_system

	Communication_Buffers :
	{
		*DMA_Descriptors.o (COMMON);
	} > DSRAM_2_comm

	/* BSS section */
	.bss : 
	{
		__Xmc4500_sBSS = .;
		* (.bss);
		* (.bss*);
		* (EXCLUDE_FILE(*DMA_Descriptors.o) COMMON);
		*(.gnu.linkonce.b*)
		__Xmc4500_eBSS = ALIGN(4);
	} > DSRAM_1_system
	/* Yes, the size must be kept outside */
	__Xmc4500_BSS_Size = __Xmc4500_eBSS - __Xmc4500_sBSS;

	/* Standard DATA and user defined DATA/BSS/CONST sections */
	.data ABSOLUTE(ALIGN(16)): AT(eROData)
	{
		__Xmc4500_sData = .;
		* (.data);
		* (.data*);
		*(*.data);
		*(.gnu.linkonce.d*)
		__Xmc4500_eData = ALIGN(4);
	} > DSRAM_1_system
	/* Yes, the size must be kept outside */
	__Xmc4500_Data_Size = __Xmc4500_eData - __Xmc4500_sData;

	/* Heap - Bank1*/
	__Xmc4500_heap_start = ALIGN(8);
	__Xmc4500_heap_end = ORIGIN(DSRAM_1_system) + LENGTH (DSRAM_1_system);
	Heap_Bank1_Start = __Xmc4500_heap_start;
	Heap_Bank1_Size  = __Xmc4500_heap_end - __Xmc4500_heap_start;
	Heap_Bank1_End   = ABSOLUTE(__Xmc4500_heap_end);

	/* Heap - Bank2 */
	DSRAM2_Heap :
	{
		/* To host DATA in DSRAM2 above heap, please be sure to augment
		 * program loader code in the startup file */
		Heap_Bank2_Start = .;
	} > DSRAM_2_comm
	Heap_Bank2_Size = LENGTH(DSRAM_2_comm) - (Heap_Bank2_Start - ORIGIN(DSRAM_2_comm));

	/* Heap - Bank3 */
	PSRAM_Heap :
	{
		/* To host DATA in PSRAM above heap, please be sure to augment
		 * program loader code in the startup file */
		Heap_Bank3_Start = .;
	} > PSRAM_1
	Heap_Bank3_Size  =  LENGTH(PSRAM_1) - (Heap_Bank3_Start - ORIGIN(PSRAM_1));

	/DISCARD/ :
	{
		*(.comment)
	}

	.stab		0 (NOLOAD) : { *(.stab) }
	.stabstr	0 (NOLOAD) : { *(.stabstr) }

	/* DWARF 1 */
	.debug				0 : { *(.debug) }
	.line				0 : { *(.line) }

	/* GNU DWARF 1 extensions */
	.debug_srcinfo		0 : { *(.debug_srcinfo) }
	.debug_sfnames		0 : { *(.debug_sfnames) }

	/* DWARF 1.1 and DWARF 2 */
	.debug_aranges		0 : { *(.debug_aranges) }
	.debug_pubnames		0 : { *(.debug_pubnames) }
	.debug_pubtypes		0 : { *(.debug_pubtypes) }

	/* DWARF 2 */
	.debug_info			0 : { *(.debug_info .gnu.linkonce.wi.*) }
	.debug_abbrev		0 : { *(.debug_abbrev) }
	.debug_line			0 : { *(.debug_line) }
	.debug_frame		0 : { *(.debug_frame) }
	.debug_str			0 : { *(.debug_str) }
	.debug_loc			0 : { *(.debug_loc) }
	.debug_macinfo		0 : { *(.debug_macinfo) }

	/* DWARF 2.1 */
	.debug_ranges		0 : { *(.debug_ranges) }

	/* SGI/MIPS DWARF 2 extensions */
	.debug_weaknames	0 : { *(.debug_weaknames) }
	.debug_funcnames	0 : { *(.debug_funcnames) }
	.debug_typenames	0 : { *(.debug_typenames) }
	.debug_varnames		0 : { *(.debug_varnames) }

	/* Build attributes */
	.build_attributes	0 : { *(.ARM.attributes) }
}
