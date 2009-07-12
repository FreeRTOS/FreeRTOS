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
	 AHBSRAM0   : ORIGIN = 0x2007c000, LENGTH = 0x4000
	 AHBSRAM1   : ORIGIN = 0x20080000, LENGTH = 0x4000
}

_vRamTop = 0x10000000 + 0x8000;

ENTRY(ResetISR)

SECTIONS
{
	.text :
	{
		KEEP(*(.isr_vector))
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
		
	.data : AT (__exidx_end)
	{
		_data = .;
		*(vtable)
		*(.data*)
		_edata = .;
	} > SRAM

	/* zero initialized data */
	.bss :
	{
		_bss = .;
		*(.bss*)
		*(COMMON)
		_ebss = .;
	} > SRAM
	
	/* Where we put the heap with cr_clib */
	.cr_heap :
	{
		end = .;
		_pvHeapStart = .;
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
