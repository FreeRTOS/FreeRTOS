/*
** ###################################################################
**     Processors:          RV32M1_ri5cy
**                          RV32M1_ri5cy
**
**     Compiler:            GNU C Compiler
**     Reference manual:    RV32M1 Series Reference Manual, Rev. 1 , 8/10/2018
**     Version:             rev. 1.0, 2018-10-02
**     Build:               b171115
**
**     Abstract:
**         Linker file for the GNU C Compiler
**
**     Copyright 2016 Freescale Semiconductor, Inc.
**     Copyright 2016-2017 NXP
**     All rights reserved.
**     
**     SPDX-License-Identifier: BSD-3-Clause
**
**     http:                 www.nxp.com
**     mail:                 support@nxp.com
**
** ###################################################################
*/

/* Entry Point */
OUTPUT_ARCH( "riscv" )

HEAP_SIZE  = DEFINED(__heap_size__)  ? __heap_size__  : 0x0400;
STACK_SIZE = DEFINED(__stack_size__) ? __stack_size__ : 0x0800;

/* Specify the memory areas */
MEMORY
{
  m_vector              (RX)  : ORIGIN = 0x000FFF00, LENGTH = 0x00000100
  m_text                (RX)  : ORIGIN = 0x00000000, LENGTH = 0x000FFF00
  m_data                (RW)  : ORIGIN = 0x20000000, LENGTH = 0x00030000 - 0x1800
  rpmsg_sh_mem          (RW)  : ORIGIN = 0x2002E800, LENGTH = 0x1800
  m_usb_sram            (RW)  : ORIGIN = 0x48010000, LENGTH = 0x00000800
}

/* Define output sections */
SECTIONS
{
  /* NOINIT section for rpmsg_sh_mem */
  .noinit_rpmsg_sh_mem (NOLOAD) : ALIGN(4)
  {
     *(.noinit.$rpmsg_sh_mem*)
     . = ALIGN(4) ;
  } > rpmsg_sh_mem

  .vectors : ALIGN(4)
  {
    __VECTOR_TABLE = .;
    KEEP(*(.vectors))
  } > m_vector


  /* The program code and other data goes into internal flash */
  .text :
  {
    . = ALIGN(4);
    KEEP(*(.startup))
    . = ALIGN(4);
    __user_vector = .;
    KEEP(*(user_vectors))
    *(.text)                 /* .text sections (code) */
    *(.text*)                /* .text* sections (code) */
    *(.rodata)               /* .rodata sections (constants, strings, etc.) */
    *(.rodata*)              /* .rodata* sections (constants, strings, etc.) */
    *(.srodata .srodata.*)
    *(.glue_7)               /* glue arm to thumb code */
    *(.glue_7t)              /* glue thumb to arm code */
    *(.eh_frame)
    *(.init)
    *(.fini)
  } > m_text

  .preinit_array :
  {
    PROVIDE_HIDDEN (__preinit_array_start = .);
    KEEP (*(.preinit_array*))
    PROVIDE_HIDDEN (__preinit_array_end = .);
  } > m_text

  .init_array :
  {
    PROVIDE_HIDDEN (__init_array_start = .);
    KEEP (*(SORT(.init_array.*)))
    KEEP (*(.init_array*))
    PROVIDE_HIDDEN (__init_array_end = .);
  } > m_text

  .fini_array :
  {
    PROVIDE_HIDDEN (__fini_array_start = .);
    KEEP (*(SORT(.fini_array.*)))
    KEEP (*(.fini_array*))
    PROVIDE_HIDDEN (__fini_array_end = .);
  } > m_text

  __etext = .;    /* define a global symbol at end of code */
  __global_pointer = .;    /* define a global symbol at end of code */
  __DATA_ROM = .; /* Symbol is used by startup for data initialization */

  .data : AT(__DATA_ROM)
  {
    . = ALIGN(4);
    __DATA_RAM = .;
    __data_start__ = .;      /* create a global symbol at data start */
    *(.data)                 /* .data sections */
    *(.data*)                /* .data* sections */
    *(.sdata .sdata.*)
    *(.heapsram*)            /* This is only for the pulpino official test code. */
    __noncachedata_start__ = .;   /* create a global symbol at ncache data start */
	*(NonCacheable)
    __noncachedata_end__ = .;     /* define a global symbol at ncache data end */
    KEEP(*(.jcr*))
    . = ALIGN(4);
    __data_end__ = .;        /* define a global symbol at data end */
  } > m_data

  __DATA_END = __DATA_ROM + (__data_end__ - __data_start__);
  text_end = ORIGIN(m_text) + LENGTH(m_text);
  ASSERT(__DATA_END <= text_end, "region m_text overflowed with text and data")

  _edata = .;
  /* Uninitialized data section */
  .bss :
  {
    /* This is used by the startup in order to initialize the .bss section */
    . = ALIGN(4);
    __START_BSS = .;
    __bss_start__ = .;
    *(.bss)
    *(.bss*)
    *(.sbss)
    *(.sbss*)
    *(COMMON)
    . = ALIGN(4);
    __bss_end__ = .;
    __END_BSS = .;
  } > m_data

  /* End of uninitalized data segement */
  _end = .;
  PROVIDE(end = .);

  .heap :
  {
    . = ALIGN(8);
    __heap_start = .;
    . += HEAP_SIZE;
    __heap_end = .;
    _heap_end = __heap_end;
  } > m_data

  .stack :
  {
    . = ALIGN(8);
    __StackLimit = .;
    . += STACK_SIZE;
    __StackTop = .;
    __freertos_irq_stack_top = .;
  } > m_data

  m_usb_bdt (NOLOAD) :
  {
    . = ALIGN(512);
    *(m_usb_bdt)
  } > m_usb_sram

  m_usb_global (NOLOAD) :
  {
    *(m_usb_global)
  } > m_usb_sram

  /* Initializes stack on the end of block */
  PROVIDE(__stack = __StackTop);
}

