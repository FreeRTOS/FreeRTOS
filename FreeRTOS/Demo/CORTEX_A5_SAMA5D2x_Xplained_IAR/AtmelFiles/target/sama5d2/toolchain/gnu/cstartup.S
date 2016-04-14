/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */


//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

#define AIC         0xFC020000
#define SAIC        0xF803C000
#define AIC_IVR     0x10
#define AIC_EOICR   0x38

#define MODE_MSK         0x1F

#define ARM_MODE_FIQ     0x11
#define ARM_MODE_IRQ     0x12
#define ARM_MODE_SVC     0x13
#define ARM_MODE_ABT     0x17
#define ARM_MODE_UND     0x1B
#define ARM_MODE_SYS     0x1F

#define I_BIT            0x80
#define F_BIT            0x40

#define FPU_NON_SECURE_ACCESS_OFFSET 10
#define FPU_ACCESS_CONTROL_OFFSET    20
#define FPU_FPEXC_EN_BIT             0x40000000

//------------------------------------------------------------------------------
//         Startup routine
//------------------------------------------------------------------------------

	.align      4
	.arm

/* Exception vectors
 *******************/
	.section    .vectors, "a", %progbits

resetVector:
/* Reset */
	ldr     pc, =resetHandler
/* Undefined Instruction */
	ldr     pc, =undefined_instruction_irq_handler
/* Software Interrupt */
	ldr     pc, =software_interrupt_irq_handler
/* Prefetch Abort */
	ldr     pc, =prefetch_abort_irq_handler
/* Data Abort */
	ldr     pc, =data_abort_irq_handler
/* Reserved for future use */
1:
	b       1b
/* Interrupt */
	b       irqHandler
/* Fast interrupt */
	b       fiqHandler

//------------------------------------------------------------------------------
/// Handles a fast interrupt request by branching to the address defined in the
/// AIC.
//------------------------------------------------------------------------------
fiqHandler:
	sub     lr, lr, #4
	stmfd   sp!, {lr}
	//mrs     lr, SPSR
	stmfd   sp!, {r0}

	/* Write in the IVR to support Protect Mode */

	ldr     lr, =SAIC
	ldr     r0, [r14, #AIC_IVR]
	str     lr, [r14, #AIC_IVR]

	/* Branch to interrupt handler in Supervisor mode */

	msr     CPSR_c, #ARM_MODE_SVC
	stmfd   sp!, {r1-r3, r4, r12, lr}

	blx      r0

	ldmia   sp!, {r1-r3, r4, r12, lr}
	msr     CPSR_c, #ARM_MODE_FIQ | I_BIT | F_BIT

	/* Acknowledge interrupt */

	ldr     lr, =SAIC
	str     lr, [r14, #AIC_EOICR]

	/* Restore interrupt context and branch back to calling code */

	ldmia   sp!, {r0}
	//msr     SPSR_cxsf, lr
	ldmia   sp!, {pc}^

//------------------------------------------------------------------------------
/// Handles incoming interrupt requests by branching to the corresponding
/// handler, as defined in the AIC. Supports interrupt nesting.
//------------------------------------------------------------------------------
irqHandler:
	/* Save interrupt context on the stack to allow nesting */

	sub     lr, lr, #4
	stmfd   sp!, {lr}
	mrs     lr, SPSR
	stmfd   sp!, {r0, lr}

	/* Write in the IVR to support Protect Mode */

	ldr     lr, =AIC
	ldr     r0, [r14, #AIC_IVR]
	str     lr, [r14, #AIC_IVR]

	/* Branch to interrupt handler in Supervisor mode */

	msr     CPSR_c, #ARM_MODE_SVC
	stmfd   sp!, {r1-r3, r4, r12, lr}

	/* Check for 8-byte alignment and save lr plus a */
	/* word to indicate the stack adjustment used (0 or 4) */

	and     r1, sp, #4
	sub     sp, sp, r1
	stmfd   sp!, {r1, lr}

	blx     r0

	ldmia   sp!, {r1, lr}
	add     sp, sp, r1

	ldmia   sp!, {r1-r3, r4, r12, lr}
	msr     CPSR_c, #ARM_MODE_IRQ | I_BIT | F_BIT

	/* Acknowledge interrupt */

	ldr     lr, =AIC
	str     lr, [r14, #AIC_EOICR]

	/* Restore interrupt context and branch back to calling code */

	ldmia   sp!, {r0, lr}
	msr     SPSR_cxsf, lr
	ldmia   sp!, {pc}^


//------------------------------------------------------------------------------
/// Initializes the chip and branches to the main() function.
//------------------------------------------------------------------------------
	.section    .textEntry
	.global     entry

entry:
resetHandler:

	cpsie   a

/* Useless instruction for referencing the .vectors section */

	ldr     r0, =resetVector

/* Set pc to actual code location (i.e. not in remap zone) */

	ldr     pc, =1f
1:

/* Relocate */
	ldr     r0, =_etext
	ldr     r1, =_srelocate
	ldr     r2, =_erelocate
1:
	cmp     r1, r2
	ldrcc   r3, [r0], #4
	strcc   r3, [r1], #4
	bcc     1b

/* Set up the fast interrupt stack pointer */

	mrs     r0, CPSR
	bic     r0, r0, #MODE_MSK
	orr     r0, r0, #ARM_MODE_FIQ
	msr     CPSR_c, r0
	ldr     sp, =_fiqstack
	bic     sp, sp, #0x7

/* Set up the normal interrupt stack pointer */

	bic     r0, r0, #MODE_MSK
	orr     r0, r0, #ARM_MODE_IRQ
	msr     CPSR_c, r0
	ldr     sp, =_irqstack
	bic     sp, sp, #0x7

/* Set up the abort mode stack pointer */

	bic     r0, r0, #MODE_MSK
	orr     r0, r0, #ARM_MODE_ABT
	msr     CPSR_c, r0
	ldr     sp, =_abtstack
	bic     sp, sp, #0x7

/* Set up the undefined mode stack pointer */

	bic     r0, r0, #MODE_MSK
	orr     r0, r0, #ARM_MODE_UND
	msr     CPSR_c, r0
	ldr     sp, =_undstack
	bic     sp, sp, #0x7

/* Set up the system mode stack pointer */

	bic     r0, r0, #MODE_MSK
	orr     r0, r0, #ARM_MODE_SYS
	msr     CPSR_c, r0
	ldr     sp, =_sysstack
	bic     sp, sp, #0x7

/* Set up the supervisor mode stack pointer */

	bic     r0, r0, #MODE_MSK
	orr     r0, r0, #ARM_MODE_SVC
	msr     CPSR_c, r0
	ldr     sp, =_cstack
	bic     sp, sp, #0x7

/* Perform low-level initialization of the chip using low_level_init() */

	ldr     r0, =low_level_init
	blx     r0

/* Clear the zero segment */
	ldr     r0, =_szero
	ldr     r1, =_ezero
	mov     r2, #0
1:
	cmp     r0, r1
	strcc   r2, [r0], #4
	bcc     1b

/* Enable fpu */
	/* Grant non secure access for CP10 and CP11 */
	mrc	p15, 0, r0, c1, c1, 2
	orr     r0, r0, #3 << FPU_NON_SECURE_ACCESS_OFFSET
	mcr	p15, 0, r0, c1, c1, 2
	/* Set CP10 and CP11 access permission (Privileged and User mode) */
	ldr	r0, =(0xF << FPU_ACCESS_CONTROL_OFFSET)
	mcr	p15, 0, r0, c1, c0, 2
	/* Set the FPEXC EN bit to enable the FPU (and NEON instructions) */
	mov	r1, #FPU_FPEXC_EN_BIT
	vmsr	FPEXC, r1

/* Initialize the C library */

	ldr     r0, =__libc_init_array
	blx     r0

/* Branch to main() */

	ldr     r0, =main
	blx     r0

/* Loop indefinitely when program is finished */

1:
	b       1b
