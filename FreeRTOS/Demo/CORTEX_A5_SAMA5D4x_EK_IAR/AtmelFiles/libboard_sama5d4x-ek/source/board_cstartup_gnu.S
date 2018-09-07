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


#define AIC         0xFC06E000
#define AIC_IVR     0x10
#define AIC_EOICR   0x38
#define SAIC        0xFC068400
#define AIC_FVR     0x14

#define IRQ_STACK_SIZE   8*3*4
#define FIQ_STACK_SIZE   8*3*4

#define MODE_MSK         0x1F
#define ARM_MODE_ABT     0x17
#define ARM_MODE_FIQ     0x11
#define ARM_MODE_IRQ     0x12
#define ARM_MODE_SVC     0x13
#define ARM_MODE_SYS     0x1F

#define I_BIT            0x80
#define F_BIT            0x40

#define REG_SFR_AICREDIR        0xF8028054
#define REG_SFR_UID             0xF8028050   
#define AICREDIR_KEY            0x5F67B102

//------------------------------------------------------------------------------
//         Startup routine
//------------------------------------------------------------------------------

            .align      4
            .arm
        
/* Exception vectors
 *******************/
            .section    .vectors, "a", %progbits

resetVector:
        ldr     pc, =resetHandler       /* Reset */
undefVector:
        b       undefVector             /* Undefined instruction */
swiVector:
        b       swiVector               /* Software interrupt */
prefetchAbortVector:
        b       prefetchAbortVector     /* Prefetch abort */
dataAbortVector:
        b       dataAbortVector         /* Data abort */
reservedVector:
        b       reservedVector          /* Reserved for future use */
irqVector:
        b       irqHandler              /* Interrupt */
fiqVector:
        b       fiqHandler              /* Fast interrupt */
//------------------------------------------------------------------------------
/// Handles a fast interrupt request by branching to the address defined in the
/// AIC.
//------------------------------------------------------------------------------
fiqHandler:
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
        /* MSR     SPSR_cxsf, lr*/
        LDMIA   sp!, {pc}^


//------------------------------------------------------------------------------
/// Handles incoming interrupt requests by branching to the corresponding
/// handler, as defined in the AIC. Supports interrupt nesting.
//------------------------------------------------------------------------------
irqHandler:
 /* Save interrupt context on the stack to allow nesting */
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


//------------------------------------------------------------------------------
/// Initializes the chip and branches to the main() function.
//------------------------------------------------------------------------------
            .section    .textEntry
            .global     entry

entry:
resetHandler:
        
        CPSIE   A 

/* Enable VFP */
        /* - Enable access to CP10 and CP11 in CP15.CACR */
        //mrc     p15, 0, r0, c1, c0, 2
        //orr     r0, r0, #0xf00000
        //mcr     p15, 0, r0, c1, c0, 2
/* - Enable access to CP10 and CP11 in CP15.NSACR */
/* - Set FPEXC.EN (B30) */
        //fmrx    r0, fpexc
        //orr     r0, r0, #0x40000000
        //fmxr    fpexc, r0

/* Useless instruction for referencing the .vectors section */
        ldr     r0, =resetVector

/* Set pc to actual code location (i.e. not in remap zone) */
        ldr     pc, =1f

/* Initialize the prerelocate segment */
1:
        ldr     r0, =_efixed
        ldr     r1, =_sprerelocate
        ldr     r2, =_eprerelocate
1:
        cmp     r1, r2
        ldrcc   r3, [r0], #4
        strcc   r3, [r1], #4
        bcc     1b

/* Perform low-level initialization of the chip using LowLevelInit() */
        ldr     sp, =_cstack
        stmfd   sp!, {r0}
        ldr     r0, =LowLevelInit
        blx     r0

/* Initialize the postrelocate segment */

        ldmfd   sp!, {r0}
        ldr     r1, =_spostrelocate
        ldr     r2, =_epostrelocate
1:
        cmp     r1, r2
        ldrcc   r3, [r0], #4
        strcc   r3, [r1], #4
        bcc     1b

/* Clear the zero segment */
        ldr     r0, =_szero
        ldr     r1, =_ezero
        mov     r2, #0
1:
        cmp     r0, r1
        strcc   r2, [r0], #4
        bcc     1b
        
        MRS     r0, cpsr                
/* Set up the fast interrupt stack pointer.*/
        bic     r0, r0, #MODE_MSK       
        orr     r0, r0, #ARM_MODE_FIQ   
        msr     cpsr_c, r0              
        ldr     sp, =_fiqstack     
        bic     sp,sp,#0x7       

/* Set up the normal interrupt stack pointer.*/

        bic     r0, r0, #MODE_MSK       
        orr     r0, r0, #ARM_MODE_IRQ  
        msr     cpsr_c, r0             
        ldr     sp, =_irqstack          
        bic     sp,sp,#0x7             

/* Set up the stack pointer.*/

        bic     r0 ,r0, #MODE_MSK      
        orr     r0 ,r0, #ARM_MODE_SYS  
        msr     cpsr_c, r0             
        ldr     sp, =_sysstack
        bic     sp,sp,#0x7              

        bic     r0 ,r0, #MODE_MSK      
        orr     r0 ,r0, #ARM_MODE_SVC
        msr     cpsr_c, r0             
        ldr     sp, =_cstack
        bic     sp,sp,#0x7    

		// Redirect FIQ to IRQ
        LDR  r0,  =AICREDIR_KEY 
        LDR  r1, = REG_SFR_UID
        LDR  r2, = REG_SFR_AICREDIR
        LDR  r3,[r1]
        EORS r0, r0, r3
        ORRS r0, r0, #0x01
        STR  r0, [r2]

/*Initialize the C library  */
       ldr     r3, =__libc_init_array
       mov     lr, pc
       bx      r3

/* Branch to main()
 ******************/
       ldr     r0, =main
       blx     r0

/* Loop indefinitely when program is finished */
1:
        b       1b

