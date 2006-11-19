/*
Linker subscript for STR75xFx0 definitions
Copyright RAISONANCE 2005
You can use, modify and distribute thisfile freely, but without any waranty.
*/


/* Memory Spaces Definitions */

MEMORY
{
  FLASH (rx) : ORIGIN = 0x20000000, LENGTH = 128K
  FLASHB1 (rx) : ORIGIN = 0x200C0000, LENGTH = 16K
  RAM (xrw) : ORIGIN = 0x40000000, LENGTH = 16K
  EXTMEMB0 (rx) : ORIGIN = 0x60000000, LENGTH = 16M
  EXTMEMB1 (rx) : ORIGIN = 0x62000000, LENGTH = 16M
  EXTMEMB2 (rx) : ORIGIN = 0x64000000, LENGTH = 16M
  EXTMEMB3 (rx) : ORIGIN = 0x66000000, LENGTH = 16M
}

/* higher address of the user mode stack */
_estack = 0x40004000;

