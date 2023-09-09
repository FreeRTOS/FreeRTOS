	/* Sample initialization file */

	.extern main
	.extern exit
	.extern AT91F_LowLevelInit

	.text
	.code 32


	.align  0

	.extern __stack_end__
	.extern __bss_beg__
	.extern __bss_end__
	.extern __data_beg__
	.extern __data_end__
	.extern __data+beg_src__

	.global start
	.global endless_loop

	/* Stack Sizes */
    .set  UND_STACK_SIZE, 0x00000004
    .set  ABT_STACK_SIZE, 0x00000004
    .set  FIQ_STACK_SIZE, 0x00000004
    .set  IRQ_STACK_SIZE, 0X00000400
    .set  SVC_STACK_SIZE, 0x00000400

	/* Standard definitions of Mode bits and Interrupt (I & F) flags in PSRs */
    .set  MODE_USR, 0x10            /* User Mode */
    .set  MODE_FIQ, 0x11            /* FIQ Mode */
    .set  MODE_IRQ, 0x12            /* IRQ Mode */
    .set  MODE_SVC, 0x13            /* Supervisor Mode */
    .set  MODE_ABT, 0x17            /* Abort Mode */
    .set  MODE_UND, 0x1B            /* Undefined Mode */
    .set  MODE_SYS, 0x1F            /* System Mode */

    .equ  I_BIT, 0x80               /* when I bit is set, IRQ is disabled */
    .equ  F_BIT, 0x40               /* when F bit is set, FIQ is disabled */


start:
_start:
_mainCRTStartup:

	/* Setup a stack for each mode - note that this only sets up a usable stack
	for system/user, SWI and IRQ modes.   Also each mode is setup with
	interrupts initially disabled. */
    ldr   r0, .LC6
    msr   CPSR_c, #MODE_UND|I_BIT|F_BIT /* Undefined Instruction Mode */
    mov   sp, r0
    sub   r0, r0, #UND_STACK_SIZE
    msr   CPSR_c, #MODE_ABT|I_BIT|F_BIT /* Abort Mode */
    mov   sp, r0
    sub   r0, r0, #ABT_STACK_SIZE
    msr   CPSR_c, #MODE_FIQ|I_BIT|F_BIT /* FIQ Mode */
    mov   sp, r0
    sub   r0, r0, #FIQ_STACK_SIZE
    msr   CPSR_c, #MODE_IRQ|I_BIT|F_BIT /* IRQ Mode */
    mov   sp, r0
    sub   r0, r0, #IRQ_STACK_SIZE
    msr   CPSR_c, #MODE_SVC|I_BIT|F_BIT /* Supervisor Mode */
    mov   sp, r0
    sub   r0, r0, #SVC_STACK_SIZE
    msr   CPSR_c, #MODE_SYS|I_BIT|F_BIT /* System Mode */
    mov   sp, r0

	/* We want to start in supervisor mode.  Operation will switch to system
	mode when the first task starts. */
	msr   CPSR_c, #MODE_SVC|I_BIT|F_BIT

    bl		AT91F_LowLevelInit

	/* Clear BSS. */

	mov     a2, #0			/* Fill value */
	mov		fp, a2			/* Null frame pointer */
	mov		r7, a2			/* Null frame pointer for Thumb */

	ldr		r1, .LC1		/* Start of memory block */
	ldr		r3, .LC2		/* End of memory block */
	subs	r3, r3, r1      /* Length of block */
	beq		.end_clear_loop
	mov		r2, #0

.clear_loop:
	strb	r2, [r1], #1
	subs	r3, r3, #1
	bgt		.clear_loop

.end_clear_loop:

	/* Initialise data. */

	ldr		r1, .LC3		/* Start of memory block */
	ldr		r2, .LC4		/* End of memory block */
	ldr		r3, .LC5
	subs	r3, r3, r1		/* Length of block */
	beq		.end_set_loop

.set_loop:
	ldrb	r4, [r2], #1
	strb	r4, [r1], #1
	subs	r3, r3, #1
	bgt		.set_loop

.end_set_loop:

	mov		r0, #0          /* no arguments  */
	mov		r1, #0          /* no argv either */

    ldr lr, =main	
	bx	lr

endless_loop:
	b               endless_loop


	.align 0

	.LC1:
	.word   __bss_beg__
	.LC2:
	.word   __bss_end__
	.LC3:
	.word   __data_beg__
	.LC4:
	.word   __data_beg_src__
	.LC5:
	.word   __data_end__
	.LC6:
	.word	__stack_end__


	/* Setup vector table.  Note that undf, pabt, dabt, fiq just execute
	a null loop. */

.section .startup,"ax"
         .code 32
         .align 0

	b     _start						/* reset - _start			*/
	ldr   pc, _undf						/* undefined - _undf		*/
	ldr   pc, _swi						/* SWI - _swi				*/
	ldr   pc, _pabt						/* program abort - _pabt	*/
	ldr   pc, _dabt						/* data abort - _dabt		*/
	nop									/* reserved					*/
	ldr   pc, [pc,#-0xF20]				/* IRQ - read the AIC		*/
	ldr   pc, _fiq						/* FIQ - _fiq				*/

_undf:  .word __undf                    /* undefined				*/
_swi:   .word swi_handler				/* SWI						*/
_pabt:  .word __pabt                    /* program abort			*/
_dabt:  .word __dabt                    /* data abort				*/
_fiq:   .word __fiq                     /* FIQ						*/

__undf: b     .                         /* undefined				*/
__pabt: b     .                         /* program abort			*/
__dabt: b     .                         /* data abort				*/
__fiq:  b     .                         /* FIQ						*/
