/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

#include "ISR_Support.h"

/*
     IAR startup file for AT91SAM9XE microcontrollers.
 */

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(2)
        SECTION CSTACK:DATA:NOROOT(3)

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#define __ASSEMBLY__
#include "board.h"

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

#define ARM_MODE_ABT     0x17
#define ARM_MODE_FIQ     0x11
#define ARM_MODE_IRQ     0x12
#define ARM_MODE_SVC     0x13
#define ARM_MODE_SYS     0x1F

#define I_BIT            0x80
#define F_BIT            0x40

//------------------------------------------------------------------------------
//         Startup routine
//------------------------------------------------------------------------------

/*
   Exception vectors
 */
        SECTION .vectors:CODE:NOROOT(2)

        PUBLIC  resetVector
        PUBLIC  irqHandler

        EXTERN  Undefined_Handler
        EXTERN  vPortYieldProcessor
        EXTERN  Prefetch_Handler
        EXTERN  Abort_Handler
        EXTERN  FIQ_Handler

        ARM

__iar_init$$done:               ; The interrupt vector is not needed
                                ; until after copy initialization is done

resetVector:
        ; All default exception handlers (except reset) are
        ; defined as weak symbol definitions.
        ; If a handler is defined by the application it will take precedence.
        LDR     pc, =resetHandler        ; Reset
        LDR     pc, Undefined_Addr       ; Undefined instructions
        LDR     pc, SWI_Addr             ; Software interrupt (SWI/SVC)
        LDR     pc, Prefetch_Addr        ; Prefetch abort
        LDR     pc, Abort_Addr           ; Data abort
        B       .                        ; RESERVED
        LDR     pc, =irqHandler          ; IRQ
        LDR     pc, FIQ_Addr             ; FIQ

Undefined_Addr: DCD   Undefined_Handler
SWI_Addr:       DCD   vPortYieldProcessor
Prefetch_Addr:  DCD   Prefetch_Handler
Abort_Addr:     DCD   Abort_Handler
FIQ_Addr:       DCD   FIQ_Handler
	
/*
   Handles incoming interrupt requests by branching to the corresponding
   handler, as defined in the AIC. Supports interrupt nesting.
 */
irqHandler:
		portSAVE_CONTEXT

        /* Write in the IVR to support Protect Mode */
        LDR     lr, =AT91C_BASE_AIC
        LDR     r0, [r14, #AIC_IVR]
        STR     lr, [r14, #AIC_IVR]

        /* Branch to interrupt handler in Supervisor mode */
        MSR     CPSR_c, #ARM_MODE_SVC
        STMFD   sp!, {r1-r3, r12, lr}
        MOV     lr, pc
        BX      r0
        LDMIA   sp!, {r1-r3, r12, lr}
        MSR     CPSR_c, #ARM_MODE_IRQ | I_BIT

        /* Acknowledge interrupt */
        LDR     lr, =AT91C_BASE_AIC
        STR     lr, [r14, #AIC_EOICR]

		portRESTORE_CONTEXT

		/* Won't progress to here. */

		/* Save interrupt context on the stack to allow nesting */
        SUB     lr, lr, #4
        STMFD   sp!, {lr}
        MRS     lr, SPSR
        STMFD   sp!, {r0, lr}

        /* Write in the IVR to support Protect Mode */
        LDR     lr, =AT91C_BASE_AIC
        LDR     r0, [r14, #AIC_IVR]
        STR     lr, [r14, #AIC_IVR]

        /* Branch to interrupt handler in Supervisor mode */
        MSR     CPSR_c, #ARM_MODE_SVC
        STMFD   sp!, {r1-r3, r12, lr}
        MOV     lr, pc
        BX      r0
        LDMIA   sp!, {r1-r3, r12, lr}
        MSR     CPSR_c, #ARM_MODE_IRQ | I_BIT

        /* Acknowledge interrupt */
        LDR     lr, =AT91C_BASE_AIC
        STR     lr, [r14, #AIC_EOICR]

        /* Restore interrupt context and branch back to calling code */
        LDMIA   sp!, {r0, lr}
        MSR     SPSR_cxsf, lr
        LDMIA   sp!, {pc}^


/*
   After a reset, execution starts here, the mode is ARM, supervisor
   with interrupts disabled.
   Initializes the chip and branches to the main() function.
 */
        SECTION .cstartup:CODE:NOROOT(2)

        PUBLIC  resetHandler
        EXTERN  LowLevelInit
        EXTERN  ?main
        REQUIRE resetVector
        ARM

resetHandler:

        /* Set pc to actual code location (i.e. not in remap zone) */
	    LDR     pc, =label

        /* Perform low-level initialization of the chip using LowLevelInit() */
label:
	    LDR     r0, =LowLevelInit
        LDR     r4, =SFE(CSTACK)
        MOV     sp, r4
        MOV     lr, pc
        BX      r0

        /* Set up the interrupt stack pointer. */
        MSR     cpsr_c, #ARM_MODE_IRQ | I_BIT | F_BIT      ; Change the mode
        LDR     sp, =SFE(IRQ_STACK)

        /* Set up the SVC stack pointer. */
        MSR     cpsr_c, #ARM_MODE_SVC | F_BIT              ; Change the mode
        LDR     sp, =SFE(CSTACK)

        /* Branch to main() */
        LDR     r0, =?main
        MOV     lr, pc
        BX      r0

        /* Loop indefinitely when program is finished */
loop4:
        B       loop4

        END
