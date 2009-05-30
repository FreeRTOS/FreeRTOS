/*
 * GENERATED FILE - DO NOT EDIT
 * (C) Code Red Technologies Ltd, 2008-9    
 * Generated C linker script file for LPC1766 
 * (created from nxp_cm3_c.ld (v2.0.0 (200903141830)) on Mon May 25 20:29:07 BST 2009)
*/

GROUP(libgcc.a libc.a)

MEMORY
{
     FLASH (rx) : ORIGIN = 0x0 LENGTH = 0x40000
     SRAM (rwx) : ORIGIN = 0x10000000, LENGTH = 0x8000
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


	__exidx_end = .;
	_etext = .;
		
	.data : AT (__exidx_end)
	{
		_data = .;
		*(.data*)
		_edata = .;
	} > SRAM

	/* zero initialized data */
	.bss :
	{
		_bss = .;
		*(.bss*)
		_ebss = .;
	} > SRAM
	

/*
	Note: (ref: M0000066)
	Moving the stack down by 16 is to work around a GDB bug.
	This space can be reclaimed for Production Builds.
*/	
	_vStackTop = _vRamTop - 16;
}
