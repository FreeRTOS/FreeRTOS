/*
 * crt0.S
 * 1 define and initial the stack pointer
 * 2 exception handler table
 * 3 call SystemInit
 * 4 go to __main in entry.o
 *
 * Copyright (C) 2016~2017  Hangzhou C-SKY Microsystems Co., Ltd
 * Modify by Jiang Long  on 2016-09-14
 */
// <<< Use Configuration Wizard in Context Menu >>>

/*
 * For importing variable or functions from other c or assemble files.
 */
.import main

/*
 * default service routine
 */
.global Reset_Handler
.global Misaligned_Access_Handler
.global Access_Error_Handler
.global Divided_By_Zero_Handler
.global Illegal_Handler
.global Privlege_Violation_Handler
.global Trace_Exection_Handler
.global Breakpoint_Exception_Handler
.global Unrecoverable_Error_Handler
.global Idly4_Error_Handler
.global Auto_INT_Handler
.global Auto_FINT_Handler
.global Reserved_HAI_Handler
.global Reserved_FP_Handler
.global TLB_Ins_Empty_Handler
.global TLB_Data_Empty_Handler
.global Default_handler

.weak Reset_Handler
.weak Misaligned_Access_Handler
.weak Access_Error_Handler
.weak Divided_By_Zero_Handler
.weak Illegal_Handler
.weak Privlege_Violation_Handler
.weak Trace_Exection_Handler
.weak Breakpoint_Exception_Handler
.weak Unrecoverable_Error_Handler
.weak Idly4_Error_Handler
.weak Auto_INT_Handler
.weak Auto_FINT_Handler
.weak Reserved_HAI_Handler
.weak Reserved_FP_Handler
.weak TLB_Ins_Empty_Handler
.weak TLB_Data_Empty_Handler
.weak Default_handler


.export	ckcpu_vsr_table	/* Vector table base address. */
.section .exp_table,"ax",@progbits
/* Vector table space. */
$d:
.align 10
ckcpu_vsr_table:
	.long Reset_Handler
	.long Misaligned_Access_Handler
	.long Access_Error_Handler
	.long Divided_By_Zero_Handler
	.long Illegal_Handler
	.long Privlege_Violation_Handler
	.long Trace_Exection_Handler
	.long Breakpoint_Exception_Handler
	.long Unrecoverable_Error_Handler
	.long Idly4_Error_Handler
	.long Auto_INT_Handler
	.long Auto_FINT_Handler
	.long Reserved_HAI_Handler
	.long Reserved_FP_Handler
	.long TLB_Ins_Empty_Handler
	.long TLB_Data_Empty_Handler

.rept 32
	.long NOVIC_IRQ_Default_Handler
.endr
$t:
/* The ckcpu startup codes. */
.text
.align 2
	/*
	 * This is the codes first entry point. This is where it all begins...
	 */
Reset_Handler:
	/*
	 * Init psr value, enable exception, disable interrupt and fast interrupt.
	 * psr = 0x80000100
	 */
	bgeni	r7, 31
	bseti	r7, 30
	bseti	r7, 29
	bseti	r7, 8
	mtcr	r7, psr

	/*
	 * Setup initial vector base table for interrupts and exceptions
	 */
	lrw 	a3, ckcpu_vsr_table
	mtcr	a3, vbr
	
	/* Initialize the normal stack pointer from the linker definition. */
    lrw     r0, g_top_irqstack
    mov     sp, r0

/*
 *  The ranges of copy from/to are specified by following symbols
 *    __etext: LMA of start of the section to copy from. Usually end of text
 *    __data_start__: VMA of start of the section to copy to
 *    __data_end__: VMA of end of the section to copy to
 *
 *  All addresses must be aligned to 4 bytes boundary.
 */
    lrw     r1, __erodata
    lrw     r2, __data_start__
    lrw     r3, __data_end__

    subu    r3, r2
    cmpnei  r3, 0
    bf      .L_loop0_done

.L_loop0:
    ldw     r0, (r1, 0)
    stw     r0, (r2, 0)
    addi    r1, 4
    addi    r2, 4
    subi    r3, 4
    cmpnei  r3, 0
    bt      .L_loop0

.L_loop0_done:

/*
 *  The BSS section is specified by following symbols
 *    __bss_start__: start of the BSS section.
 *    __bss_end__: end of the BSS section.
 *
 *  Both addresses must be aligned to 4 bytes boundary.
 */
    lrw     r1, __bss_start__
    lrw     r2, __bss_end__

    movi    r0, 0

    subu    r2, r1
    cmpnei  r2, 0
    bf      .L_loop1_done

.L_loop1:
    stw     r0, (r1, 0)
    addi    r1, 4
    subi    r2, 4
    cmpnei  r2, 0
    bt      .L_loop1
.L_loop1_done:
	
	jbsr    main
	/* Should never get here. */
1:
	br 1b
Misaligned_Access_Handler:
Access_Error_Handler:
Divided_By_Zero_Handler:
Illegal_Handler:
Privlege_Violation_Handler:
Trace_Exection_Handler:
Breakpoint_Exception_Handler:
Unrecoverable_Error_Handler:
Idly4_Error_Handler:
Auto_INT_Handler:
Auto_FINT_Handler:
Reserved_HAI_Handler:
Reserved_FP_Handler:
TLB_Ins_Empty_Handler:
TLB_Data_Empty_Handler:
Default_handler:
	br Default_handler
	rte

.section .bss

    .align  2
    .global g_intstackalloc
    .global g_intstackbase
    .global g_top_irqstack
g_intstackalloc:
g_intstackbase:
    .space  4096
g_top_irqstack: