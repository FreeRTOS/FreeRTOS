/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Set to 1 to enable functionality */
#define __SHOW_KERNEL_PARAMS__ 0

/* Local definitions boot loader */
#define MULTIBOOT_SIGNATURE		0x2BADB002
#define MULTIBOOT_BOOTINFO_MMAP	0x00000040

/* Local definitions for GD table */
#define	GDT_ENTRIES			8
#define	GDT_ENTRY_SIZE		8
#define	GDT_BYTES			(GDT_ENTRIES * GDT_ENTRY_SIZE)

 	/* Globals and externs */
	.global _mboot_hdr
	.global _start
	.global _restart

	.extern bootsign
	.extern bootinfo

	.extern __text_start
	.extern __text_end
	.extern __data_vma
	.extern __data_lma
	.extern __data_start
	.extern __data_end
	.extern __bss_start
	.extern __bss_end
	.extern __stack_for_main

	.global __text_start
	.global __text_end
	.global __data_vma
	.global __data_lma
	.global __data_start
	.global __data_end
	.global __bss_start
	.global __bss_end

	.extern setsegs
	.extern CRT_Init
	.extern kernel_load_check
	.extern main

 	/* Local constants for multiboot section */
  	.set ALIGN,    	1<<0             	/* align loaded modules on page boundaries */
	.set MEMINFO,  	1<<1             	/* provide memory map */
	.set MAGIC,    	0x1BADB002       	/* 'magic number' lets bootloader find the header */
	.set FLAGS, 	ALIGN|MEMINFO  		/* this is the multiboot 'flag' field */
	.set CHECKSUM, 	-(MAGIC + FLAGS) 	/* checksum of above */

	/* Set-up GDT */
	.section .data

	.align	16
	.globl	gdt
	gdt:	.space	GDT_BYTES
	gdtr:	.word	(GDT_BYTES-1)		/* sizeof _gdt -1 (in bytes) */
	.long	gdt							/* global pointer to the gdt */

	/* Start of application text */
	.section .text.entry

	/* Skip mb header */
	jmp _start

	.align 4
	/* Multiboot header */
	_mboot_hdr:
	.long MAGIC							/* offset = 0 */
	.long FLAGS							/* offset = 4 */
	.long CHECKSUM						/* offset = 8 */
 	.long _mboot_hdr					/* should be header address - offset = 12 */
	.long __text_start					/* load address (start of text) - offset = 16 */
	.long __bss_start					/* load end address (end of data) - offset = 20*/
	.long __bss_end 					/* bss end address - offset = 24*/
	.long _start						/* entry_addr - offset = 28*/

	/* Start of executable code */
	_start:

    /* Store boot arguments */
	movl	%eax, bootsign
	movl	%ebx, bootinfo

    /* Check to see if kernel is bootstrapped by grub */
	cmpl $MULTIBOOT_SIGNATURE, %eax
	jne _local_loop
	testb	$MULTIBOOT_BOOTINFO_MMAP, (%ebx)
	je	_local_loop

	_restart:

	/* Initialise the stack pointer */
	movl $__stack_for_main, %esp

    /* Reset EFLAGS. */
    pushl $0
    popf

 	/* Set up the global descriptor table */
	call	setsegs
	lgdt	gdtr
	ljmp	$0x8, $gdt1					/* CS descriptor 1 */
	gdt1:
	movl	$0x10, %eax					/* DS descriptor 2 */
	movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movl	$0x18, %eax					/* SS descriptor 3 */
	movw	%ax, %ss

    /* Clear interrupt flag */
	cli

    /* Initialise platform */
	call CRT_Init

    /* Show kernel parameters and call main, or just call main */
	#if (__SHOW_KERNEL_PARAMS__ == 1)
	    /*---------------------------------------------------------------------
	    	On successful OS load EAX should contain 0x2BADB002
	       	EBX should contain the physical address of multiboot info structure

	       	Push the pointers to the multiboot information structure
	       	and the magic number on the stack and check values returned
	    ----------------------------------------------------------------------*/
	    movl	bootsign, %eax
		movl	bootinfo, %ebx
	    pushl   %ebx		/* Multiboot information */
	    pushl   %eax 		/* Magic number */
	    call show_kernel_parameters
	#else
	    /*---------------------------------------------------------------------
	    	Call main() routine
	    ----------------------------------------------------------------------*/
	 	call main
    #endif

	/* Should not get here, but just in case - loop forever */
	cli
	_local_loop:
	hlt
	jmp _local_loop

	/*-------------------------------------------------------------------------
	                  GLOBAL ASSEMBLY LANGUAGE ROUTINES
	--------------------------------------------------------------------------*/

 	/* halt */
 	.globl	halt
	halt:
	jmp halt
	ret

	/* inb */
	.globl	inb
	inb:	movl	4(%esp), %edx
	xorl	%eax, %eax	# clr eax
	inb	%dx, %al
	ret

	/* inw */
	.globl	inw
	inw:	movl	4(%esp), %edx
	xorl	%eax, %eax	# clr eax
	inw		%dx, %ax
	ret

	/* inl */
	.globl  inl
	inl:	movl	4(%esp), %edx
	xorl	%eax, %eax
	inl		%dx, %eax
	ret

	/* outb */
	.globl	outb
	outb:	movl	4(%esp), %edx
	movl	8(%esp), %eax
	outb	%al, %dx
	ret

	/* outw */
	.globl	outw
	outw:	movl	4(%esp), %edx
	movl	8(%esp), %eax
	outw	%ax, %dx
	ret

	/* outl */
	.globl	outl
	outl:	movl	4(%esp), %edx
	movl	8(%esp), %eax
	outl	%eax, %dx
	ret

.end
