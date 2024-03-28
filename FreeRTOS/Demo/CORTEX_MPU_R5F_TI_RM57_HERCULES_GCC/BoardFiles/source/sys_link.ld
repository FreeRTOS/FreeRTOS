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

/* Variables used by FreeRTOS-MPU. */
/* Cover the entirety of flash */
__FLASH_segment_start__ = ORIGIN( FLASH );
__FLASH_segment_end__   = __FLASH_segment_start__ + LENGTH( FLASH );

/* Cover the all of System RAM */
__SRAM_segment_start__  = ORIGIN( RAM );
__SRAM_segment_end__    = __SRAM_segment_start__ + LENGTH( RAM );

/* All functions marked as "PRIVILEGED_FUNCTION" get placed in this section */
__privileged_functions_region_size__  = 64K;
__privileged_functions_start__        = ORIGIN( FLASH );
__privileged_functions_end__          = __privileged_functions_start__ + __privileged_functions_region_size__;

/* All variables marked as "PRIVILEGED_DATA" get placed in this section, including the heap */
__privileged_data_region_size__ = 32K;
__privileged_data_start__       = ORIGIN( RAM );
__privileged_data_end__         = ORIGIN( RAM ) + __privileged_data_region_size__;

/* A section of memory at the start of "PRIVILEGED_DATA" for different operating mode stacks */
__privileged_stacks_region_size__ = 2K;
__privileged_stacks_start__       = ORIGIN( RAM );
__privileged_stacks_end__         = ORIGIN( RAM ) + __privileged_stacks_region_size__;

/* Memory block for various dev kit peripherals */
__peripherals_start__   = 0xF0000000;
__peripherals_length__  = 256M;
__peripherals_end__     = __peripherals_start__ + __peripherals_length__;

/* Seperate memory block for privileged system */
__privileged_system_start__   = 0xFFF80000;
__privileged_system_length__  = 512K;
__privileged_system_end__     = __privileged_system_start__ + __privileged_system_length__;

/* The first 2K of space in RAM is used for different processor mode stacks */
__privileged_stack_region_size = 0x800;

/* Define output sections */
SECTIONS
{
  /* The ISR vector goes first into RAM */
  .privileged_functions :
  {
    . = ALIGN(4);
    KEEP(*(.intvecs))
    . = ALIGN(4);

    *(privileged_functions)
    . = ALIGN(4);
    /* Fill rest of the region with a known value */
    FILL(0xADDEADDE);
    /* Ensure that non-privileged code is placed after the region reserved for
     * privileged kernel code. This is done for MPU Region Alignment */
    /* Note that dot (.) actually refers to the byte offset from the start of
     * the current section (.privileged_functions in this case). As a result,
     * setting dot (.) to a value sets the size of the section. */
    . = __privileged_functions_region_size__;
  } >FLASH

  .freertos_system_calls :
  {
    . = ALIGN(4);
    /* Place the FreeRTOS System Calls first in the unprivileged region. */
    __syscalls_flash_start__ = .;
    *(freertos_system_calls)
    __syscalls_flash_end__ = .;
    . = ALIGN(4);

  } >FLASH

  /* This variable is used in portASM.S to determine if a FreeRTOS System Call
   * was raised from this specific section of flash */
  __syscalls_flash_length__ = __syscalls_flash_end__ - __syscalls_flash_start__;

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

  _siPrivData = LOADADDR(.privileged_data);
  /* FreeRTOS kernel data. */
  .privileged_data :
  {
    /* Leave a block of memory for different Processor mode stacks.
     * These are set in sys_core.S */
    . = ALIGN(4);
    /* Mark the start of the region for debugging purposes. */
    __start_privileged_stack_region = .;
    . = __privileged_stack_region_size;
    . = ALIGN(4);
    /* Mark the end of the region for debugging purposes. */
    __end_privileged_stack_region = .;

    __start_priv_data = .; /* Create a global symbol at privileged data start. */
    *(privileged_data)
    . = ALIGN(4);
    __end_priv_data = .; /* Create a global symbol at privileged data end. */
    FILL(0xADDE); /* Fill RAM with known value */
    /* Ensure that non-privileged data is placed after the region reserved for
     * privileged kernel data. */
    /* Note that dot (.) actually refers to the byte offset from the start of
     * the current section (.privileged_data in this case). As a result, setting
     * dot (.) to a value sets the size of the section. */
    . = __privileged_data_region_size__;
    . = ALIGN(4);
  } >RAM AT> FLASH

  /* Used by sys_startup.c to initialize data */
  _sidata = LOADADDR(.data);
  /* Initialized data sections goes into RAM, load LMA copy after code */
  .data :
  {
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
