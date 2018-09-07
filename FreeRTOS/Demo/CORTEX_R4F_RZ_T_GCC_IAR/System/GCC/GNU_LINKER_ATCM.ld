/****************************************************************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
****************************************************************************************************************************************************************/
/***********************************************************************************************************************
* File Name     : GNU_LINKER_ATCM.ld
* Device(s)     : RZ/T1 (R7S910018)
* Tool-Chain    : GNUARM-NONEv14.02-EABI
* H/W Platform  : RSK+RZT1 CPU Board
* Description   : Linker file for projects that require to load and run from RAM (ATCM)
***********************************************************************************************************************/
/***********************************************************************************************************************
* History       : DD.MM.YYYY Version Description
*               : 21.05.2015 1.00
***********************************************************************************************************************/
OUTPUT_FORMAT("elf32-littlearm", "elf32-bigarm", "elf32-littlearm")
OUTPUT_ARCH(arm)
ENTRY(start)

/* Base Address RAM Memory Table 1 Mbyte on-chip RAM */
MEMORY
{
	/* Internal RAM address range H'2000_0000 to H'2001_FFFF is configured as data retention RAM */
	/* Write access to this address range has to be enabled by writing to registers SYSCR1 and SYSCR2 */
	ATCM       (rwx)   : ORIGIN = 0x00000000, LENGTH = 0x00080000  /* (512KB)  H'00000000 to H'0007FFFF */
	BTCM       (rwx)   : ORIGIN = 0x00800000, LENGTH = 0x00800000  /* (32KB)   H'00800000 to H'00807FFF */
	BUFFER_RAM (rwx)   : ORIGIN = 0x20200000, LENGTH = 0x00100000  /* (1024KB) H'08000000 to H'0FFFFFFF */
	DATA_RAM0  (rwx)   : ORIGIN = 0x24000000, LENGTH = 0x00080000  /* (512KB)  H'22000000 to H'2207FFFF */
	DATA_RAM1  (rwx)   : ORIGIN = 0x22000000, LENGTH = 0x00080000  /* (512KB)  H'24000000 to H'2407FFFF */

	SPIBSC (rw)    : ORIGIN = 0x30000000, LENGTH = 0x04000000  /* attached to H'30000000 to H'33FFFFFF */
	CS0    (rw)    : ORIGIN = 0x40000000, LENGTH = 0x04000000  /* attached to H'40000000 to H'43FFFFFF */
	CS1    (rw)    : ORIGIN = 0x44000000, LENGTH = 0x04000000  /* attached to H'44000000 to H'47FFFFFF */
	CS2    (rw)    : ORIGIN = 0x48000000, LENGTH = 0x04000000  /* attached to H'40000000 to H'4CFFFFFF */
	CS3    (rw)    : ORIGIN = 0x4C000000, LENGTH = 0x04000000  /* attached to H'4C000000 to H'4FFFFFFF */
	CS4    (rw)    : ORIGIN = 0x50000000, LENGTH = 0x04000000  /* attached to H'50000000 to H'53FFFFFF */
	CS5    (rw)    : ORIGIN = 0x54000000, LENGTH = 0x04000000  /* attached to H'54000000 to H'57FFFFFF */

	/* Mapped memory type */
	SPI_ROM    (rw)    : ORIGIN = 0x30000000, LENGTH = 0x04000000
	CS0_ROM    (rw)    : ORIGIN = 0x40000000, LENGTH = 0x04000000
	CS1_ROM    (rw)    : ORIGIN = 0x44000000, LENGTH = 0x04000000
	SDRAM0_EXT (rw)    : ORIGIN = 0x48000000, LENGTH = 0x04000000
	SDRAM1_EXT (rw)    : ORIGIN = 0x4C000000, LENGTH = 0x04000000
}

SYS_STACK_SIZE        = 0x200; 	    /* Application stack size            */
SVC_STACK_SIZE	      = 0x200;      /* SVC mode stack                    */
IRQ_STACK_SIZE	      = 0x200;      /* IRQ mode stack                    */
FIQ_STACK_SIZE	      = 0x200;      /* FRQ mode stack                    */
UND_STACK_SIZE	      = 0x200;      /* SVC mode stack                    */
ABT_STACK_SIZE	      = 0x200;      /* ABT mode stack                    */
HEAP_STACK_SIZE       = 0x1000; 	/* Heap stack size                   */

ATCM_BASE             = 0x00000000;  /* User application located here          */
BTCM_BASE             = 0x00800000;  /* BTCM base address                      */

USER_EXEC_BASE        = 0x00000000;  /* Application loads and runs from here   */

USER_RAM              = 0x20000000;	 /* Application's RAM base                 */

STACK_BASE            = 0x00807800;  /* Stacks located in BTCM                 */

SDRAM0_BASE           = 0x48000000;  /* SDRAM1 is attached to CS2 space        */
SDRAM1_BASE           = 0x4C000000;  /* SDRAM1 is attached to CS3 space        */

SECTIONS
{
	.reset USER_EXEC_BASE :
	{
		reset_start = .;
	    execute = .;
		_intvec_start = .;
	    *start.o (.text);
		.	= ALIGN(0x4);
		_intvec_end = .;
		end_reset = .;
	} > ATCM

	.text :
	{
		text_start = .;
		*(.text)
		*(.text.startup)
		text_end = .;
	} > ATCM

	.rodata :
	{
		_rodata_start = .;
		*(.rodata)
		*(.rodata.*)
		.	= ALIGN(0x8);
		_start_data_ROM = .;
	    *(.data)
		*(.data.*)
		_end_data_ROM = .;
		*(.got.plt)
		*(.got)
		.	= ALIGN(0x8);
		_rodata_end = .;
        PROVIDE(end = .);
	} > ATCM

    _ram_data_size = (_end_data_ROM - _start_data_ROM);

	.data USER_RAM :
	{
		_data_start = .;
		_start_data_RAM = .;
		. += _ram_data_size;
		_data_end = .;
	}

	.bss _data_end :
	{
         _bss = .;
         PROVIDE(__bss_start__ = .);
         *(.bss)
         *(.bss.**)
         *(COMMON)
         . = ALIGN(0x4);
         PROVIDE(__bss_end__ = .);
         _ebss = .;
         _end = .;
         PROVIDE(end = .);
	}

	.heap :
	{
	    heap_start = .;
		.	= ALIGN(0x8);
		*(.heap_stack)
		. += HEAP_STACK_SIZE;
		heap_end = .;
	} > ATCM

	.sys_stack STACK_BASE :
	{
	    sys_stack_start = .;
		.	= ALIGN(0x8);
		*(.sys_stack)
		. += SYS_STACK_SIZE;
	    sys_stack_end = .;
	} > BTCM

	.svc_stack sys_stack_end :
	{
	    svc_stack_start = .;
		.	= ALIGN(0x8);
		*(.svc_stack)
		. += SVC_STACK_SIZE;
	    svc_stack_end = .;
	} > BTCM

	.irq_stack svc_stack_end :
	{
	    irq_stack_start = .;
		.	= ALIGN(0x8);
		*(.irq_stack)
		. += IRQ_STACK_SIZE;
	    irq_stack_end = .;
	} > BTCM

	.fiq_stack irq_stack_end :
	{
	    fiq_stack_start = .;
		.	= ALIGN(0x8);
		*(.fiq_stack)
		. += FIQ_STACK_SIZE;
	    fiq_stack_end = .;
	} > BTCM

	.und_stack fiq_stack_end :
	{
	    und_stack_start = .;
		.	= ALIGN(0x8);
		*(.und_stack)
		. += UND_STACK_SIZE;
		und_stack_end = .;
	} > BTCM

	.abt_stack und_stack_end :
	{
	    abt_stack_start = .;
		.	= ALIGN(0x8);
		*(.abt_stack)
		. += ABT_STACK_SIZE;
		abt_stack_end = .;
	} > BTCM

	/* NOLOAD directs linker NOT to fill VRAMx_SECTION with 0.          */
	/* Usage of NOLOAD increases speed of linker and download to target */
	.sdram0_section SDRAM0_BASE (NOLOAD) : {} > SDRAM0_EXT
	.sdram1_section SDRAM1_BASE (NOLOAD) : {} > SDRAM1_EXT
}