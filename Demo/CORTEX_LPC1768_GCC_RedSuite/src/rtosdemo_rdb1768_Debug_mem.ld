/*
 * GENERATED FILE - DO NOT EDIT
 * (C) Code Red Technologies Ltd, 2008-9
 * Generated linker script include file for 
 * (created from LinkMemoryTemplate (v2.0.11 (200907061347)) on Thu Jul 09 12:44:31 BST 2009)
*/

MEMORY
{
     FLASH (rx) : ORIGIN = 0x0 LENGTH = 0x80000
     SRAM (rwx) : ORIGIN = 0x10000000, LENGTH = 0x8000
	 AHBSRAM0   : ORIGIN = 0x2007c000, LENGTH = 0x4000
	 AHBSRAM1   : ORIGIN = 0x20080000, LENGTH = 0x4000
}

_vRamTop = 0x10000000 + 0x8000;
