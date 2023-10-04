
/*
 * Name: iROM.ld 
 * 
 * Generated Linker Description File
 * Copyright (C) 2010 HighTec EDV-Systeme GmbH. 
 * (!Do not edit outsite of the protection areas!)
 *
 * Description: 
 * internal flash configuration
 */

/*
 * Define Entrypoint of Executable
 */
ENTRY(_start)

/*
 * Global
 */
/*Program Flash Memory (PFLASH)*/ 
__PMU_PFLASH_BEGIN = 0x80000000;
__PMU_PFLASH_SIZE = 2560K;
/*Data Flash Memory (DFLASH0)*/ 
__PMU_DFLASH0_BEGIN = 0xAFE00000;
__PMU_DFLASH0_SIZE = 64K;
/*Data Flash Memory (DFLASH1)*/ 
__PMU_DFLASH1_BEGIN = 0xAFE10000;
__PMU_DFLASH1_SIZE = 64K;
/*Boot ROM (BROM)*/ 
__BROM_BEGIN = 0xAFFFC000;
__BROM_SIZE = 16K;
/*Scratch-Pad RAM (SPRAM)*/ 
__PMI_SPRAM_BEGIN = 0xC0000000;
__PMI_SPRAM_SIZE = 40K;
/*Local Data RAM (LDRAM)*/ 
__DMI_LDRAM_BEGIN = 0xD0000000;
__DMI_LDRAM_SIZE = 128K;
/*PCP Code Memory (CMEM)*/ 
__PCP_CMEM_BEGIN = 0xF0060000;
__PCP_CMEM_SIZE = 32K;
/*PCP Data Memory (PRAM)*/ 
__PCP_PRAM_BEGIN = 0xF0050000;
__PCP_PRAM_SIZE = 16K;

__ISTACK_SIZE = DEFINED (__ISTACK_SIZE) ? __ISTACK_SIZE : 256;
__USTACK_SIZE = DEFINED (__USTACK_SIZE) ? __USTACK_SIZE : 1K;
__HEAP_SIZE = DEFINED (__HEAP_SIZE) ? __HEAP_SIZE : 4K ;
__CSA_SIZE = DEFINED (__CSA_SIZE) ? __CSA_SIZE : 16K ;

/**
 *	User defined global region
 */
/*PROTECTED REGION ID(Protection:iROM-Global) ENABLED START*/
/*Protection-Area for your own LDF-Code*/
/*PROTECTED REGION END*/

/*
 * internal flash configuration
 */
MEMORY
{
	PMU_PFLASH (rx!p):	org = 0x80000000, len = 2560K  /*Program Flash Memory (PFLASH)*/ 
	PMU_DFLASH0 (r!xp):	org = 0xAFE00000, len = 64K  /*Data Flash Memory (DFLASH0)*/ 
	PMU_DFLASH1 (r!xp):	org = 0xAFE10000, len = 64K  /*Data Flash Memory (DFLASH1)*/ 
	BROM (rx!p):	org = 0xAFFFC000, len = 16K  /*Boot ROM (BROM)*/ 
	PMI_SPRAM (wx!p):	org = 0xC0000000, len = 40K  /*Scratch-Pad RAM (SPRAM)*/ 
	DMI_LDRAM (w!xp):	org = 0xD0000000, len = 128K  /*Local Data RAM (LDRAM)*/ 
	PCP_CMEM (rxp):	org = 0xF0060000, len = 32K  /*PCP Code Memory (CMEM)*/ 
	PCP_PRAM (wp!x):	org = 0xF0050000, len = 16K  /*PCP Data Memory (PRAM)*/ 
	
}			

SECTIONS
{
	/*Code-Sections*/
	 
	 /*
	  * Startup code for TriCore
	  */
	 .startup_code  :
	 {
	 	PROVIDE(__startup_code_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .startup_code.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.startup_code) /*Startup code for TriCore*/ 
	 	*(.startup_code*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .startup_code) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__startup_code_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Code section
	  */
	 .text  :
	 {
	 	PROVIDE(__text_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .text.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.text) /*Code section*/ 
	 	*(.text*)
	 	*(.gnu.linkonce.t.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .text) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__text_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Code executed before calling main
	  */
	 .init  :
	 {
	 	PROVIDE(__init_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .init.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	KEEP(*(.init)) /*Code executed before calling main*/ 
	 	KEEP(*(.init*))
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .init) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__init_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Code executed before exiting program
	  */
	 .fini  :
	 {
	 	PROVIDE(__fini_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .fini.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	KEEP(*(.fini)) /*Code executed before exiting program*/ 
	 	KEEP(*(.fini*))
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .fini) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__fini_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Section for trap table
	  */
	 .traptab  :
	 {
	 	PROVIDE(__traptab_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .traptab.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.traptab) /*Section for trap table*/ 
	 	*(.traptab*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .traptab) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__traptab_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Section for interrupt table
	  */
	 .inttab  :
	 {
	 	PROVIDE(__inttab_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .inttab.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.inttab) /*Section for interrupt table*/ 
	 	*(.inttab*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .inttab) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__inttab_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Exception handling frame for C++ exceptions
	  */
	 .eh_frame  :
	 {
	 	PROVIDE(__eh_frame_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .eh_frame.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.eh_frame) /*Exception handling frame for C++ exceptions*/ 
	 	*(.eh_frame*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .eh_frame) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__eh_frame_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Section for constructors
	  */
	 .ctors  :
	 {
	 	PROVIDE(__ctors_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .ctors.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	KEEP(*(.ctors)) /*Section for constructors*/ 
	 	KEEP(*(.ctors*))
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .ctors) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__ctors_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Section for destructors
	  */
	 .dtors  :
	 {
	 	PROVIDE(__dtors_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .dtors.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	KEEP(*(.dtors)) /*Section for destructors*/ 
	 	KEEP(*(.dtors*))
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .dtors) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__dtors_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 

	/*Absolute Data-Sections*/
	 
	 /*
	  * Initialised data addressed as absolute
	  */
	 .zdata  :
	 {
	 	PROVIDE(__zdata_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .zdata.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.zdata) /*Initialised data addressed as absolute*/ 
	 	*(.zdata*)
	 	*(.gnu.linkonce.z.*)
	 	*(.gnu.linkonce.zr.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .zdata) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/

	 	PROVIDE(__zdata_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM AT > PMU_PFLASH /* DMI_LDRAM: Local Data RAM (LDRAM) */ /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Not initialised data addressed as absolute
	  */
	 .zbss (NOLOAD) :
	 {
	 	PROVIDE(__zbss_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .zbss.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.zbss) /*Not Initialised data addressed as absolute*/ 
	 	*(.zbss*)
	 	*(.gnu.linkonce.zb.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .zbss) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/

	 	PROVIDE(__zbss_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM /* DMI_LDRAM: Local Data RAM (LDRAM) */ 
	 
	 /*
	  * Not initialised bit data
	  */
	 .bbss (NOLOAD) :
	 {
	 	PROVIDE(__bbss_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .bbss.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.bbss) /*Not initialised bit data*/ 
	 	*(.bbss*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .bbss) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/

	 	PROVIDE(__bbss_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM /* DMI_LDRAM: Local Data RAM (LDRAM) */ 
	 
	 /*
	  * Bit variables
	  */
	 .bdata  :
	 {
	 	PROVIDE(__bdata_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .bdata.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.bdata) /*Bit variables*/ 
	 	*(.bdata*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .bdata) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/

	 	PROVIDE(__bdata_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM /* DMI_LDRAM: Local Data RAM (LDRAM) */ 
	 

	/*Small Data-Sections*/
	 
	 /*
	  * Storage of write-protected data addressed as small
	  */
	 .sdata2  :
	 {
	 	PROVIDE(__sdata2_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .sdata2.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.sdata.rodata) /*Storage of write-protected data addressed as small*/ 
	 	*(.sdata.rodata*)
	 	*(.gnu.linkonce.sr.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .sdata2) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__sdata2_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Section stores initialised data which is addressable by small data area pointer (%a0)
	  */
	 .sdata  :
	 {
	 	PROVIDE(__sdata_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .sdata.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.sdata) /*Section stores initialised data which is addressable by small data area pointer (%a0)*/ 
	 	*(.sdata*)
		 *(.gnu.linkonce.s.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .sdata) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__sdata_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM AT > PMU_PFLASH /* DMI_LDRAM: Local Data RAM (LDRAM) */ /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Not initialised data in section ’.sbss’, addressable by small data area pointer (%a0)
	  */
	 .sbss (NOLOAD) :
	 {
	 	PROVIDE(__sbss_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .sbss.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.sbss) /*Not initialised data in section ’.sbss’, addressable by small data area pointer (%a0)*/ 
	 	*(.sbss*)
	 	*(.gnu.linkonce.sb.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .sbss) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__sbss_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM /* DMI_LDRAM: Local Data RAM (LDRAM) */ 
	 

	/*Normal Data-Sections*/
	 
	 /*
	  * Storage of write-protected data
	  */
	 .rodata  :
	 {
	 	PROVIDE(__rodata_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .rodata.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.rodata) /*Storage of write-protected data*/ 
	 	*(.rodata*)
	 	*(.gnu.linkonce.r.*)
	 	*(.jcr.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .rodata) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__rodata_end = .);
	 	. = ALIGN(8);
	 	
	 } > PMU_PFLASH /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Initialised data
	  */
	 .data  :
	 {
	 	PROVIDE(__data_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .data.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.data) /*Initialised data*/ 
	 	*(.data*)
	 	*(.gnu.linkonce.d.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .data) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__data_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM AT > PMU_PFLASH /* DMI_LDRAM: Local Data RAM (LDRAM) */ /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * Not Initialised data
	  */
	 .bss (NOLOAD) :
	 {
	 	PROVIDE(__bss_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .bss.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	*(.bss) /*Not Initialised data*/ 
	 	*(.bss*)
	 	*(.gnu.linkonce.b.*)
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .bss) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__bss_end = .);
	 	. = ALIGN(8);
	 	
	 } > DMI_LDRAM /* DMI_LDRAM: Local Data RAM (LDRAM) */ 
	 
	

	/*PCP-Sections*/
	 
	 /*
	  * PCP Code Section
	  */
	 .pcptext  :
	 {
	 	PROVIDE(__pcptext_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .pcptext.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	KEEP(*(.pcptext)) /*PCP Code Section*/ 
	 	KEEP(*(.pcptext*))
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .pcptext) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__pcptext_end = .);
	 	. = ALIGN(8);
	 	
	 } > PCP_CMEM AT > PMU_PFLASH /* PCP_CMEM: PCP Code Memory (CMEM) */ /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 
	 /*
	  * PCP Data Section
	  */
	 .pcpdata  :
	 {
	 	PROVIDE(__pcpdata_start = .);
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .pcpdata.begin) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	KEEP(*(.pcpdata)) /*PCP Data Section*/ 
	 	KEEP(*(.pcpdata*))
	 	
	 	/*PROTECTED REGION ID(Protection: iROM .pcpdata) ENABLED START*/
	 		/*Protection-Area for your own LDF-Code*/
	 	/*PROTECTED REGION END*/
	 	
	 	PROVIDE(__pcpdata_end = .);
	 	. = ALIGN(8);
	 	
	 } > PCP_PRAM AT > PMU_PFLASH /* PCP_PRAM: PCP Data Memory (PRAM) */ /* PMU_PFLASH: Program Flash Memory (PFLASH) */ 
	 

	 
	 
	.clear_sec :
	{
		. = ALIGN(8);
		PROVIDE(__clear_table = .) ;
	
			LONG(0 + ADDR(.bss));	LONG(SIZEOF(.bss));
			LONG(0 + ADDR(.sbss));	LONG(SIZEOF(.sbss));
			LONG(0 + ADDR(.zbss));	LONG(SIZEOF(.zbss));
			LONG(0 + ADDR(.bbss));	LONG(SIZEOF(.bbss));
			/*PROTECTED REGION ID(Protection: iROM clear section) ENABLED START*/
		 		/*Protection-Area for your own LDF-Code*/
		 	/*PROTECTED REGION END*/
			LONG(-1);                 LONG(-1);
	
	} > PMU_PFLASH
	 
	
	.copy_sec :
	{
		. = ALIGN(8);
		PROVIDE(__copy_table = .) ;
	
			LONG(LOADADDR(.data));	LONG(0 + ADDR(.data));	LONG(SIZEOF(.data));
			LONG(LOADADDR(.sdata));	LONG(0 + ADDR(.sdata));	LONG(SIZEOF(.sdata));
			LONG(LOADADDR(.zdata));	LONG(0 + ADDR(.zdata));	LONG(SIZEOF(.zdata));
			LONG(LOADADDR(.pcptext));	LONG(0 + ADDR(.pcptext));	LONG(SIZEOF(.pcptext));
			LONG(LOADADDR(.pcpdata));	LONG(0 + ADDR(.pcpdata));	LONG(SIZEOF(.pcpdata));
	
			/*PROTECTED REGION ID(Protection: iROM copy section) ENABLED START*/
		 		/*Protection-Area for your own LDF-Code*/
		 	/*PROTECTED REGION END*/
			LONG(-1);                 LONG(-1);                  LONG(-1);
	} > PMU_PFLASH 
	
	.csa (NOLOAD) :
	{
		 . = ALIGN(64);
		 __CSA_BEGIN = . ;
		 . += __CSA_SIZE;
		 . = ALIGN(64);
		 __CSA_END = .;
	} > DMI_LDRAM
	
	.heap (NOLOAD) :
	{
		. =  ALIGN(8);
		__HEAP = .;
		. += __HEAP_SIZE;
		__HEAP_END = .;
	} > DMI_LDRAM
	
	.istack (NOLOAD) :
	{
		. =  ALIGN(8);
		. += __ISTACK_SIZE;
		__ISTACK = .;
	} > DMI_LDRAM
	
	.ustack (NOLOAD) :
	{
		. =  ALIGN(8);
		. += __USTACK_SIZE;
		__USTACK = .;
	} > DMI_LDRAM
	
	/*PROTECTED REGION ID(Protection:iROM-User-Sections) ENABLED START*/
	/*Protection-Area for your own LDF-Code*/
	/*PROTECTED REGION END*/
	
}

