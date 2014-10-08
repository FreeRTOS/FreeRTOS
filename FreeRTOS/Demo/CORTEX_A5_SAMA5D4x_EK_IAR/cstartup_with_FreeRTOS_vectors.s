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

/*
     IAR startup file for SAMA5D4X microcontrollers.
 */

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(2)
        SECTION FIQ_STACK:DATA:NOROOT(2)
        SECTION UND_STACK:DATA:NOROOT(2)
        SECTION ABT_STACK:DATA:NOROOT(2)
        SECTION CSTACK:DATA:NOROOT(3)

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#define __ASSEMBLY__

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

#define AIC         0xFC06E000
#define AIC_IVR     0x10
#define AIC_EOICR   0x38
#define L2CC_CR     0x00A00100

#define REG_SFR_AICREDIR        0xF8028054
#define REG_SFR_UID             0xF8028050
#define AICREDIR_KEY            0x5F67B102


MODE_MSK DEFINE 0x1F            ; Bit mask for mode bits in CPSR
#define ARM_MODE_ABT     0x17
#define ARM_MODE_FIQ     0x11
#define ARM_MODE_IRQ     0x12
#define ARM_MODE_SVC     0x13
#define ARM_MODE_SYS     0x1F
#define ARM_MODE_UND     0x1B
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
        PUBLIC  IRQ_Handler
        EXTERN  FreeRTOS_IRQ_Handler
        EXTERN  Undefined_C_Handler
        EXTERN  FreeRTOS_SWI_Handler
        EXTERN  Prefetch_C_Handler
        EXTERN  Abort_C_Handler
        PUBLIC  FIQ_Handler

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
        LDR     PC,IRQ_Addr              ; 0x18 IRQ
        LDR     PC,FIQ_Addr              ; 0x1c FIQ

IRQ_Addr:       DCD   FreeRTOS_IRQ_Handler
Undefined_Addr: DCD   Undefined_C_Handler
SWI_Addr:       DCD   FreeRTOS_SWI_Handler
Abort_Addr:     DCD   Abort_C_Handler
Prefetch_Addr:  DCD   Prefetch_C_Handler
;IRQ_Addr:       DCD   IRQ_Handler
FIQ_Addr:       DCD   FIQ_Handler
/*
   Handles incoming interrupt requests by branching to the corresponding
   handler, as defined in the AIC. Supports interrupt nesting.
 */
IRQ_Handler:
        /* Save interrupt context on the stack to allow nesting */
        SUB     lr, lr, #4
        STMFD   sp!, {lr}
        MRS     lr, SPSR
        STMFD   sp!, {r0, lr}

        /* Write in the IVR to support Protect Mode */
        LDR     lr, =AIC
        LDR     r0, [r14, #AIC_IVR]
        STR     lr, [r14, #AIC_IVR]

        /* Branch to interrupt handler in Supervisor mode */
        MSR     CPSR_c, #ARM_MODE_SVC
        STMFD   sp!, {r1-r3, r4, r12, lr}

        /* Check for 8-byte alignment and save lr plus a */
        /* word to indicate the stack adjustment used (0 or 4) */
        AND     r1, sp, #4
        SUB     sp, sp, r1
        STMFD   sp!, {r1, lr}

        BLX     r0

        LDMIA   sp!, {r1, lr}
        ADD     sp, sp, r1

        LDMIA   sp!, {r1-r3, r4, r12, lr}
        MSR     CPSR_c, #ARM_MODE_IRQ | I_BIT | F_BIT

        /* Acknowledge interrupt */
        LDR     lr, =AIC
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
        EXTERN  CP15_InvalidateBTB
        EXTERN  CP15_InvalidateTranslationTable
        EXTERN  CP15_InvalidateIcache
        EXTERN  CP15_InvalidateDcacheBySetWay
        ARM

resetHandler:

        LDR     r4, =SFE(CSTACK)     ; End of SVC stack
        BIC     r4,r4,#0x7           ; Make sure SP is 8 aligned
        MOV     sp, r4


        ;; Set up the normal interrupt stack pointer.

        MSR     CPSR_c, #(ARM_MODE_IRQ | F_BIT | I_BIT)
        LDR     sp, =SFE(IRQ_STACK)     ; End of IRQ_STACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned


        ;; Set up the fast interrupt stack pointer.

        MSR     CPSR_c, #(ARM_MODE_FIQ | F_BIT | I_BIT)
        LDR     sp, =SFE(FIQ_STACK)     ; End of FIQ_STACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned

        MSR     CPSR_c, #(ARM_MODE_ABT | F_BIT | I_BIT)
        LDR     sp, =SFE(ABT_STACK)     ; End of ABT_STACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned

        MSR     CPSR_c, #(ARM_MODE_UND | F_BIT | I_BIT)
        LDR     sp, =SFE(UND_STACK)     ; End of UND_STACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned

        MSR     CPSR_c, #(ARM_MODE_SYS | F_BIT | I_BIT)
        LDR     sp, =SFE(CSTACK-0x3000) ; 0x1000 bytes of SYS stack
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned


        MSR     CPSR_c, #(ARM_MODE_SVC | F_BIT | I_BIT)

        CPSIE   A

        /* Enable VFP */
        /* - Enable access to CP10 and CP11 in CP15.CACR */
        MRC     p15, 0, r0, c1, c0, 2
        ORR     r0, r0, #0xf00000
        MCR     p15, 0, r0, c1, c0, 2
        /* - Enable access to CP10 and CP11 in CP15.NSACR */
        /* - Set FPEXC.EN (B30) */
#ifdef __ARMVFP__
        MOV     r3, #0x40000000
        VMSR    FPEXC, r3
#endif

         // Redirect FIQ to IRQ
        LDR  r0,  =AICREDIR_KEY
        LDR  r1, = REG_SFR_UID
        LDR  r2, = REG_SFR_AICREDIR
        LDR  r3,[r1]
        EORS r0, r0, r3
        ORRS r0, r0, #0x01
        STR  r0, [r2]

         /* Perform low-level initialization of the chip using LowLevelInit() */
        LDR     r0, =LowLevelInit
        BLX     r0


        MRC     p15, 0, r0, c1, c0, 0       ; Read CP15 Control Regsiter into r0
        TST     r0, #0x1                    ; Is the MMU enabled?
        BICNE   r0, r0, #0x1                ; Clear bit 0
        TST     r0, #0x4                    ; Is the Dcache enabled?
        BICNE   r0, r0, #0x4                ; Clear bit 2
        MCRNE   p15, 0, r0, c1, c0, 0       ; Write value back

        // Disbale L2 cache
        LDR r1,=L2CC_CR
        MOV r2,#0
        STR r2, [r1]

        DMB
        BL      CP15_InvalidateTranslationTable
        BL      CP15_InvalidateBTB
        BL      CP15_InvalidateIcache
        BL      CP15_InvalidateDcacheBySetWay
        DMB
        ISB


        /* Branch to main() */
        LDR     r0, =?main
        BLX     r0

        /* Loop indefinitely when program is finished */
loop4:
        B       loop4



;------------------------------------------------------------------------------
;- Function             : FIQ_Handler
;- Treatments           : FIQ Controller Interrupt Handler.
;- Called Functions     : AIC_IVR[interrupt]
;------------------------------------------------------------------------------
SAIC   DEFINE   0xFC068400
AIC_FVR           DEFINE   0x14

        SECTION .text:CODE:NOROOT(2)
        ARM
FIQ_Handler:
  /* Save interrupt context on the stack to allow nesting */
        SUB     lr, lr, #4
        STMFD   sp!, {lr}
        /* MRS     lr, SPSR */
        STMFD   sp!, {r0}

        /* Write in the IVR to support Protect Mode */
        LDR     lr, =SAIC
        LDR     r0, [r14, #AIC_IVR]
        STR     lr, [r14, #AIC_IVR]

        /* Branch to interrupt handler in Supervisor mode */
        MSR     CPSR_c, #ARM_MODE_SVC
        STMFD   sp!, {r1-r3, r4, r12, lr}

        MOV     r14, pc
        BX      r0

        LDMIA   sp!, {r1-r3, r4, r12, lr}
        MSR     CPSR_c, #ARM_MODE_FIQ | I_BIT | F_BIT

        /* Acknowledge interrupt */
        LDR     lr, =SAIC
        STR     lr, [r14, #AIC_EOICR]

        /* Restore interrupt context and branch back to calling code */
        LDMIA   sp!, {r0}
        /* MSR     SPSR_cxsf, lr */
        LDMIA   sp!, {pc}^


 END
