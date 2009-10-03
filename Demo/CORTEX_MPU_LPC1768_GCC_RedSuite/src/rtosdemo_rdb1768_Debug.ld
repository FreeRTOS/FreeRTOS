/*
 * GENERATED FILE - DO NOT EDIT
 * (C) Code Red Technologies Ltd, 2008-9    
 * Generated C linker script file for LPC1768 
 * (created from nxp_lpc13_c.ld (v2.0.11 (200907061347)) on Thu Jul 09 12:44:31 BST 2009)
*/

GROUP(libgcc.a libc.a)

MEMORY
{
     FLASH (rx) : ORIGIN = 0x0 LENGTH = 0x80000
     SRAM (rwx) : ORIGIN = 0x10000000, LENGTH = 0x8000
	 AHBRAM0   : ORIGIN = 0x2007c000, LENGTH = 0x4000
	 AHBRAM1   : ORIGIN = 0x20080000, LENGTH = 0x4000
}

_vRamTop = 0x10000000 + 0x8000;

ENTRY(ResetISR)

SECTIONS
{
	__FLASH_segment_start__ = .;
	
	/* Privileged section at the start of the flash - vectors must be first
	whatever. */
	privileged_functions :
	{
		KEEP(*(.isr_vector))
		*(privileged_functions)
		__privileged_functions_end__ = .;
	} > FLASH
	
	.text :
	{
		/* Non privileged code kept out of the first 16K or flash. */
		. = 16K;
		
		*(.text*)
		*(.rodata*)

	} > FLASH


	/* for exception handling/unwind - some Newlib functions (in common with C++ and STDC++) use this. */
	
	.ARM.extab : 
	{
		*(.ARM.extab* .gnu.linkonce.armextab.*)
	} > FLASH

	__exidx_start = .;
	.ARM.exidx :
	{
		*(.ARM.exidx* .gnu.linkonce.armexidx.*)
	} > FLASH
	__exidx_end = .;

	_etext = .;
	
	__FLASH_segment_end__ = .;		

	/* zero initialized data */		
	privileged_data :
	{
		_bss = .;
		__privileged_data_start__ = .;
		__SRAM_segment_start__ = .;
		*(privileged_data)
		__privileged_data_end__ = .;
	} > SRAM	

	/* Non kernel data is kept out of the first 256 bytes of SRAM. */
	. = 0x10000000 + 256;

	.bss :
	{
		*(.bss*)
		*(COMMON)
		_ebss = .;
	} > SRAM
	
	.data : AT (__exidx_end)
	{
		_data = .;	
		*(vtable)
		*(.data*)
		_edata = .;
	} > SRAM


	/* Where we put the heap with cr_clib */
	.cr_heap :
	{
		end = .;
		_pvHeapStart = .;
		__SRAM_segment_end__ = .;
	} > SRAM

/*
	Note: (ref: M0000066)
	Moving the stack down by 16 is to work around a GDB bug.
	This space can be reclaimed for Production Builds.
*/	
	_vStackTop = _vRamTop - 16;
	
	.ETHRAM :
	{
	} > AHBRAM0
	
	.USBRAM :
	{
	} > AHBRAM1
}
