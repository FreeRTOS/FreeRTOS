STARTUP(system/crt0.o)
INPUT(system/vector.o)
OUTPUT_ARCH(m68k)
SEARCH_DIR(.)
GROUP(-lc -lgcc)

__DYNAMIC  =  0;

MEMORY
{
  flash  (rwx) : ORIGIN = 0x00000000, LENGTH = 0x00200000
  sdram  (rwx) : ORIGIN = 0x01000000, LENGTH = 0x01000000
  sram   (rwx) : ORIGIN = 0x20000000, LENGTH = 0x00010000
  ipsbar (rwx) : ORIGIN = 0x40000000, LENGTH = 0x40000000
}

PROVIDE (__stack = 0x2000FFFC);

SECTIONS
{
  .sdram      : {} > sdram
  .ipsbar     : {} > ipsbar
  .sram (NOLOAD) : { *(.vector_ram); *(.nbuf) } > sram
  .flash      : {} > flash

  .text :
  {
    __text_start = . ;
    *(.vector_rom)
    . = ALIGN (0x100);
    *(.text)
    . = ALIGN (16);

    *(.eh_frame)
    . = ALIGN (16);

    *(.gnu.linkonce.t.*) 

    . = ALIGN(0x4);
     __CTOR_LIST__ = .;
    ___CTOR_LIST__ = .;
    LONG((__CTOR_END__ - __CTOR_LIST__) / 4 - 2)
    *(.ctors)
    LONG(0)
    __CTOR_END__ = .;
    __DTOR_LIST__ = .;
    ___DTOR_LIST__ = .;
    LONG((__DTOR_END__ - __DTOR_LIST__) / 4 - 2)
    *(.dtors)
     LONG(0)
    __DTOR_END__ = .;
    *(.rodata)
    *(.rodata.*)
    *(.gcc_except_table) 

    . = ALIGN(0x2);
    __INIT_SECTION__ = . ;
    LONG (0x4e560000)	/* linkw %fp,#0 */
    *(.init)
    SHORT (0x4e5e)	/* unlk %fp */
    SHORT (0x4e75)	/* rts */

    __FINI_SECTION__ = . ;
    LONG (0x4e560000)	/* linkw %fp,#0 */
    *(.fini)
    SHORT (0x4e5e)	/* unlk %fp */
    SHORT (0x4e75)	/* rts */

    *(.lit)
    . = ALIGN(16);
    _etext = .;
    etext = .;

  } > flash
  . = ALIGN(2);

  .data : AT (ADDR (.text) + SIZEOF (.text))
  {
    copy_start = .;
    *(.shdata)
    *(.data)
    *(.gnu.linkonce.d.*)
    . = ALIGN (16);
    _edata = .;
    copy_end = .;
  } > sdram
  __data_load_start = LOADADDR(.data);
  __data_load_end = __data_load_start + SIZEOF(.data);

  .bss :
  {
    . = ALIGN(0x4);
    __bss_start = . ;
    *(.shbss)
    *(.bss)
    *(COMMON)
    _end =  ALIGN (0x8);
    __end = _end;
  } > sdram

  .stab 0 (NOLOAD) :
  {
    *(.stab)
  }

  .stabstr 0 (NOLOAD) :
  {
    *(.stabstr)
  }
}

__IPSBAR            = ADDR(.ipsbar);

__SDRAM             = ADDR(.sdram);
__SDRAM_SIZE        = SIZEOF(.sdram);

__SRAM              = ADDR(.sram);
__SRAM_SIZE         = SIZEOF(.sram);

__FLASH             = ADDR(.flash);
__FLASH_SIZE        = SIZEOF(.flash);
