/*----------------------------------------------------------------------------*/
/* sys_link.ld                                                              */
/*                                                                            */
/* (c) Texas Instruments 2009-2014, All rights reserved.                      */
/*                                                                            */
/*----------------------------------------------------------------------------*/
/* Entry Point */
ENTRY(_c_int00)

/* Highest address of the stack */
_estack = 0x8080000;    /* end of 512K RAM */

/* Generate a link error if heap and stack don't fit into RAM */
_Min_Heap_Size = 0x400;      /* required amount of heap  */

/* Specify the memory areas */
MEMORY
{
  FLASH  (rx)     : ORIGIN = 0x00000000, LENGTH = 4M
  RAM (xrw)       : ORIGIN = 0x08000000, LENGTH = 512K
  MEMORY_B1 (rx)  : ORIGIN = 0x60000000, LENGTH = 0K
}

/** Common sizes
 * 0x0000 0001 == 1B
 * 0x0000 0002 == 2B
 * 0x0000 0004 == 4B
 * 0x0000 0008 == 8B
 * 0x0000 0010 == 16B
 * 0x0000 0020 == 32B
 * 0x0000 0040 == 64B
 * 0x0000 0080 == 128B
 * 0x0000 0100 == 256B
 * 0x0000 0200 == 512B
 * 0x0000 0400 == 1K
 * 0x0000 0800 == 2K
 * 0x0000 1000 == 4K
 * 0x0000 2000 == 8K
 * 0x0000 4000 == 16K
 * 0x0000 8000 == 32K
 * 0x0001 0000 == 64K
 * 0x0002 0000 == 128K
 * 0x0003 0000 == 192K
 * 0x0004 0000 == 256K
 * 0x0008 0000 == 512K
 * 0x0010 0000 == 1024K/1MB
 * 0x0014 0000 == 1280KB/1.25 MB
 * 0x0020 0000 == 2048K/2MB
 * 0x0040 0000 == 4096K/4MB
 * 0x0080 0000 == 8192K/8MB
 * 0x0100 0000 == 16MB
 * 0x0200 0000 == 32MB
 * 0x0400 0000 == 64MB
 * 0x0800 0000 == 128MB
*/

/* The first 2K of space in RAM is used for different processor mode stacks */
__interrupt_stack_region_size = 0x1000;

/* Define output sections */
SECTIONS
{
  /* The ISR vector goes first into RAM */
  .intvecs :
  {
    . = ALIGN(4);
    KEEP(*(.intvecs))
    . = ALIGN(4);
  } >FLASH

  /* The program code and other data goes into RAM */
  .text :
  {
    . = ALIGN(4);
    *(.text)           /* .text sections (code) */
    *(.text*)          /* .text* sections (code) */
    *(.glue_7)         /* glue arm to thumb code */
    *(.glue_7t)        /* glue thumb to arm code */
    *(.eh_frame)

    KEEP (*(.init))
    KEEP (*(.fini))

    . = ALIGN(4);
    _etext = .;        /* define a global symbols at end of code */
  } >FLASH

  /* Constant data goes into RAM */
  .rodata :
  {
    . = ALIGN(4);
    *(.rodata)         /* .rodata sections (constants, strings, etc.) */
    *(.rodata*)        /* .rodata* sections (constants, strings, etc.) */
    . = ALIGN(4);
  } >FLASH

  .ARM.extab   : {
    . = ALIGN(4);
    *(.ARM.extab* .gnu.linkonce.armextab.*)
    . = ALIGN(4);
  } >FLASH

    .ARM : {
    . = ALIGN(4);
    __exidx_start = .;
      *(.ARM.exidx*)
      __exidx_end = .;
    . = ALIGN(4);
    } >FLASH

  .preinit_array     :
  {
    PROVIDE_HIDDEN (__preinit_array_start = .);
    KEEP (*(.preinit_array*))
    PROVIDE_HIDDEN (__preinit_array_end = .);
  } >FLASH
  .init_array :
  {
    PROVIDE_HIDDEN (__init_array_start = .);
    KEEP (*(SORT(.init_array.*)))
    KEEP (*(.init_array*))
    PROVIDE_HIDDEN (__init_array_end = .);
  } >FLASH
  .fini_array :
  {
    PROVIDE_HIDDEN (__fini_array_start = .);
    KEEP (*(SORT(.fini_array.*)))
    KEEP (*(.fini_array*))
    PROVIDE_HIDDEN (__fini_array_end = .);
  } >FLASH

  /* Used by sys_startup.c to initialize data */
  _sidata = LOADADDR(.data);
  /* Initialized data sections goes into RAM, load LMA copy after code */
  .data :
  {
    . = ALIGN(4);
    . = __interrupt_stack_region_size;
    . = ALIGN(4);
    _sdata = .;        /* create a global symbol at data start */
    *(.data)           /* .data sections */
    *(.data*)          /* .data* sections */

    . = ALIGN(4);
    _edata = .;        /* define a global symbol at data end */
  } >RAM AT> FLASH

  /* Uninitialized data section */
  . = ALIGN(4);
  .bss :
  {
    /* This is used by the startup in order to initialize the .bss secion */
    _sbss = .;         /* define a global symbol at bss start */
    __bss_start__ = _sbss;
    *(.bss)
    *(.bss*)
    *(COMMON)

    . = ALIGN(4);
    _ebss = .;         /* define a global symbol at bss end */
    __bss_end__ = _ebss;
  } >RAM

  PROVIDE ( end = _ebss );
  PROVIDE ( _end = _ebss );

  /* MEMORY_bank1 section, code must be located here explicitly            */
  /* Example: extern int foo(void) __attribute__ ((section (".mb1text"))); */
  .memory_b1_text :
  {
    *(.mb1text)        /* .mb1text sections (code) */
    *(.mb1text*)       /* .mb1text* sections (code)  */
    *(.mb1rodata)      /* read-only data (constants) */
    *(.mb1rodata*)
  } >MEMORY_B1

  /* Remove information from the standard libraries */
  /DISCARD/ :
  {
    libc.a ( * )
    libm.a ( * )
    libgcc.a ( * )
  }

  .ARM.attributes 0 : { *(.ARM.attributes) }
}
