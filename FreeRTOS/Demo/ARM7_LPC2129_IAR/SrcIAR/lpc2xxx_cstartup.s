;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Part one of the system initialization code,
;; contains low-level
;; initialization.
;;
;; Copyright 2006 IAR Systems. All rights reserved.
;;
;; $Revision: 10608 $
;;

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(3)
        SECTION ABT_STACK:DATA:NOROOT(3)
        SECTION SVC_STACK:DATA:NOROOT(3)
        SECTION UND_STACK:DATA:NOROOT(3)
        SECTION FIQ_STACK:DATA:NOROOT(3)
        SECTION CSTACK:DATA:NOROOT(3)

;
; The module in this file are included in the libraries, and may be
; replaced by any user-defined modules that define the PUBLIC symbol
; __iar_program_start or a user defined start symbol.
;
; To override the cstartup defined in the library, simply add your
; modified version to the workbench project.

        SECTION .intvec:CODE:NOROOT(2)

        PUBLIC  __vector
        PUBLIC  __vector_0x14
        PUBLIC  __iar_program_start
		EXTERN	vPortYieldProcessor

        ARM
__vector:
        ;;
        ldr   pc,[pc,#+24]              ;; Reset
        ldr   pc,[pc,#+24]              ;; Undefined instructions
;;        ldr   pc,[pc,#+24]              ;; Software interrupt (SWI/SVC)
		b vPortYieldProcessor
        ldr   pc,[pc,#+24]              ;; Prefetch abort
        ldr   pc,[pc,#+24]              ;; Data abort
__vector_0x14
        DC32  0                         ;; RESERVED
        ldr   pc, [PC, #-0xFF0]         ;; IRQ
        ldr   pc,[pc,#+24]              ;; FIQ

        DC32  __iar_program_start       ;; Reset
        DC32  undef_handler             ;; Undefined instructions
        DC32  0       ;; Software interrupt (SWI/SVC)
        DC32  prefetch_handler          ;; Prefetch abort
        DC32  data_handler              ;; Data abort
        DC32  0                         ;; RESERVED
        DC32  0               			;; IRQ
        DC32  fiq_handler               ;; FIQ

undef_handler
    b         undef_handler
	
prefetch_handler
    b         prefetch_handler

data_handler
    b         data_handler

fiq_handler
    b         fiq_handler
; --------------------------------------------------
; ?cstartup -- low-level system initialization code.
;
; After a reser execution starts here, the mode is ARM, supervisor
; with interrupts disabled.
;



        SECTION .text:CODE:NOROOT(2)

;        PUBLIC  ?cstartup
        EXTERN  ?main
        REQUIRE __vector

        ARM

__iar_program_start:
?cstartup:

;
; Add initialization needed before setup of stackpointers here.
;

; Errata  MAM.1Incorrect read of data from SRAM after Reset and MAM
; is not enabled or partially enabled.
; Work-around: User code should enable the MAM after Reset and before
; any RAM accesses
MAMCR    DEFINE  0xE01FC000     ; MAM Control Register
MAMTIM   DEFINE  0xE01FC004     ; MAM Timing register

        ldr     r0,=MAMCR
        ldr     r1,=MAMTIM
        ldr     r2,=0
        str     r2,[r0]
        ldr     r2,=3     ; 1 < 20 MHz; 20 MHz < 2 < 40 MHz; 40MHz > 3
        str     r2,[r1]
        ldr     r2,=2
        str     r2,[r0]

; Initialize the stack pointers.
; The pattern below can be used for any of the exception stacks:
; FIQ, IRQ, SVC, ABT, UND, SYS.
; The USR mode uses the same stack as SYS.
; The stack segments must be defined in the linker command file,
; and be declared above.
;
; --------------------
; Mode, correspords to bits 0-5 in CPSR
MODE_BITS DEFINE  0x1F    ; Bit mask for mode bits in CPSR
USR_MODE  DEFINE  0x10    ; User mode
FIQ_MODE  DEFINE  0x11    ; Fast Interrupt Request mode
IRQ_MODE  DEFINE  0x12    ; Interrupt Request mode
SVC_MODE  DEFINE  0x13    ; Supervisor mode
ABT_MODE  DEFINE  0x17    ; Abort mode
UND_MODE  DEFINE  0x1B    ; Undefined Instruction mode
SYS_MODE  DEFINE  0x1F    ; System mode

        MRS     r0, cpsr                ; Original PSR value

        BIC     r0, r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0, r0, #ABT_MODE       ; Set ABT mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(ABT_STACK)     ; End of ABT_STACK

        BIC     r0, r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0, r0, #SVC_MODE       ; Set SVC mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(SVC_STACK)     ; End of SVC_STACK

        BIC     r0, r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0, r0, #UND_MODE       ; Set UND mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(UND_STACK)     ; End of UND_STACK

        BIC     r0, r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0, r0, #FIQ_MODE       ; Set FIQ mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(FIQ_STACK)     ; End of FIQ_STACK

        BIC     r0, r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0, r0, #IRQ_MODE       ; Set IRQ mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(IRQ_STACK)     ; End of IRQ_STACK

        BIC     r0 ,r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0 ,r0, #SYS_MODE       ; Set System mode bits
        MSR     cpsr_c, r0              ; Change the mode
        LDR     sp, =SFE(CSTACK)        ; End of CSTACK

#ifdef __ARMVFP__
        ;; Enable the VFP coprocessor.

        MOV     r0, #0x40000000         ; Set EN bit in VFP
        FMXR    fpexc, r0               ; FPEXC, clear others.

;
; Disable underflow exceptions by setting flush to zero mode.
; For full IEEE 754 underflow compliance this code should be removed
; and the appropriate exception handler installed.
;

        MOV     r0, #0x01000000         ; Set FZ bit in VFP
        FMXR    fpscr, r0               ; FPSCR, clear others.
#endif

;
; Add more initialization here
;
        BIC     r0, r0, #MODE_BITS      ; Clear the mode bits
        ORR     r0, r0, #SVC_MODE       ; Set SVC mode bits
        MSR     cpsr_c, r0              ; Change the mode
		
; Continue to ?main for C-level initialization.

        LDR     r0, =?main
        BX      r0

        END
