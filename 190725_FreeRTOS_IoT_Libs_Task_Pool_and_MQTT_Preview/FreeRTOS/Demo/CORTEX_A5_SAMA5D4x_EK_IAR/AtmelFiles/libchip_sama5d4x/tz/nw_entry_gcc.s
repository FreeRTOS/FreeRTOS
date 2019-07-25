
#define AIC         0xFC06E000
#define AIC_IVR     0x10
#define AIC_EOICR   0x38


/*
   Exception vectors
 */
        SECTION .ns_vectors:CODE:NOROOT(2)

        PUBLIC  NWVector
        EXTERN  TZ_FIQ_Handler
        EXTERN  TZ_Undefined_Handler
        EXTERN  TZ_SWI_Handler
        EXTERN  Prefetch_C_Handler
        EXTERN  Abort_C_Handler

        ARM

__iar_init$$done:               ; The interrupt vector is not needed
                                ; until after copy initialization is done

NWVector:
        ; All default exception handlers (except reset) are
        ; defined as weak symbol definitions.
        ; If a handler is defined by the application it will take precedence.
        LDR     pc, =nw_start      ; Reset
        LDR     pc, Undefined_Addr       ; Undefined instructions
        B       .                        ; Software interrupt (SWI/SYS)
        LDR     pc, Prefetch_Addr        ; Prefetch abort
        LDR     pc, Abort_Addr           ; Data abort
        B       .                        ; RESERVED
        LDR     PC,IRQ_Addr              ; 0x18 IRQ
        LDR     PC,FIQ_Addr              ; 0x1c FIQ

Undefined_Addr: DCD   TZ_Undefined_Handler
Prefetch_Addr:  DCD   Prefetch_C_Handler
Abort_Addr:     DCD   Abort_C_Handler
IRQ_Addr:       DCD   TZ_IRQ_Handler
FIQ_Addr:       DCD   TZ_FIQ_Handler




        SECTION .cstartup:CODE:NOROOT(2)
        SECTION IRQ_STACK:DATA:NOROOT(2)        
        SECTION NW_CSTACK:DATA:NOROOT(3)
        
        PUBLIC  nw_start
        PUBLIC  TZ_IRQ_Handler
        EXTERN  main_nw
        EXTERN  LowLevelInit
        ARM


MODE_MSK DEFINE 0x1F            ; Bit mask for mode bits in CPSR

ARM_MODE_USR  DEFINE   0x10
ARM_MODE_FIQ  DEFINE   0x11
ARM_MODE_IRQ  DEFINE   0x12
ARM_MODE_SVC  DEFINE   0x13
ARM_MODE_MON  DEFINE   0x16
ARM_MODE_ABT  DEFINE   0x17
ARM_MODE_UND  DEFINE   0x1B
ARM_MODE_SYS  DEFINE   0x1F

#define I_BIT            0x80
#define F_BIT            0x40


nw_start:
        
        ;- Keep IRQ disable, Keep FIQ(F) disable and switch back in SVC mode        
        MSR     CPSR_c, #ARM_MODE_SVC | I_BIT
        LDR     sp, =SFE(NW_CSTACK)        ; End of CSTACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned
              
        MRS     r0, cpsr                ; Original PSR value
         ;; Set up the sys stack pointer.

        BIC     r0 ,r0, #MODE_MSK       ; Clear the mode bits
        ORR     r0 ,r0, #ARM_MODE_SYS   ; Set System mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(NW_CSTACK-0x1900); End of CSTACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned
        
         ;; Set up the sys stack pointer.

        BIC     r0 ,r0, #MODE_MSK       ; Clear the mode bits
        ORR     r0 ,r0, #ARM_MODE_IRQ   ; Set System mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(IRQ_STACK); End of CSTACK
        BIC     sp,sp,#0x7              ; Make sure SP is 8 aligned
               
       ;; Set up the normal stack pointer.

        BIC     r0 ,r0, #MODE_MSK       ; Clear the mode bits
        ORR     r0 ,r0, #ARM_MODE_SVC   ; Set System mode bits
        MSR     cpsr_c, r0              ; Change the mode
        CPSIE   I
        
                /* Branch to main() */
        LDR     r0, =main_nw
        BLX     r0
       
       


/*
   Handles incoming interrupt requests by branching to the corresponding
   handler, as defined in the AIC. Supports interrupt nesting.
 */
TZ_IRQ_Handler:
        
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
        
        ;- Keep IRQ disable, Keep FIQ(F) disable and switch back in IRQ mode        
        MSR     CPSR_c, #ARM_MODE_IRQ | I_BIT

        /* Acknowledge interrupt */
        LDR     lr, =AIC
        STR     lr, [r14, #AIC_EOICR]

        /* Restore interrupt context and branch back to calling code */
        LDMIA   sp!, {r0, lr}
        MSR     SPSR_cxsf, lr
        LDMIA   sp!, {pc}^
       
  END