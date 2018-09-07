/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/*
     IAR startup file for AT91SAMA5D3X microcontrollers.
 */

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(2)
        SECTION CSTACK:DATA:NOROOT(3)

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

//#define __ASSEMBLY__
//#include "board.h"

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

        EXTERN  FreeRTOS_IRQ_Handler
        EXTERN  Undefined_Handler
        EXTERN  FreeRTOS_SWI_Handler
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
        LDR     pc, SWI_Addr             ; Software interrupt (SWI/SYS)
        LDR     pc, Prefetch_Addr        ; Prefetch abort
        LDR     pc, Abort_Addr           ; Data abort
        B       .                        ; RESERVED
        LDR     pc, IRQ_Addr             ; IRQ
        LDR     pc, FIQ_Addr             ; FIQ

IRQ_Addr:       DCD   FreeRTOS_IRQ_Handler
Undefined_Addr: DCD   Undefined_Handler
SWI_Addr:       DCD   FreeRTOS_SWI_Handler
Prefetch_Addr:  DCD   Prefetch_Handler
Abort_Addr:     DCD   Abort_Handler
FIQ_Addr:       DCD   FIQ_Handler


/*
   After a reset, execution starts here, the mode is ARM, supervisor
   with interrupts disabled.
   Initializes the chip and branches to the main() function.
 */
        SECTION .cstartup:CODE:NOROOT(2)

        PUBLIC  resetHandler
        EXTERN  low_level_init
        EXTERN  ?main
        REQUIRE resetVector
        ARM

resetHandler:
       CPSIE   A
        /* Enable VFP */
        /* - Enable access to CP10 and CP11 in CP15.CACR */
        mrc     p15, 0, r0, c1, c0, 2
        orr     r0, r0, #0xf00000
        mcr     p15, 0, r0, c1, c0, 2
        /* - Enable access to CP10 and CP11 in CP15.NSACR */
        /* - Set FPEXC.EN (B30) */
        fmrx    r0, fpexc
        orr     r0, r0, #0x40000000
        fmxr    fpexc, r0
        /* Set pc to actual code location (i.e. not in remap zone) */
        LDR     pc, =label

        /* Perform low-level initialization of the chip using LowLevelInit() */
label:
		/* Sets up Supervisor stack before running LowLevelInit.  The supervisor
		stack is reused by interrupts, which switch from IRQ mode to SVC mode. */
        LDR     r0, =low_level_init
        LDR     r4, =SFE(CSTACK)
        MOV     sp, r4
        BLX     r0

        /* Set up the interrupt stack pointer. */
        MSR     cpsr_c, #ARM_MODE_IRQ | I_BIT | F_BIT      ; Change the mode
        LDR     sp, =SFE(IRQ_STACK)

		/* No need to set up stacks for any other mode as that stack used by
		tasks is allocated by FreeRTOS. */

		/* Back to Supervisor mode bfore calling main().  The schduduler should
		be started from Supervisor mode. */
        MSR     cpsr_c, #ARM_MODE_SVC | F_BIT              ; Change the mode

        /* Branch to main() */
        LDR     r0, =?main
        BLX     r0

        /* Loop indefinitely when program is finished */
loop4:
        B       loop4
        END
