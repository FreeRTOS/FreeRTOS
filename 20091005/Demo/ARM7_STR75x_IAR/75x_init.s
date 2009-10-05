;******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
;* File Name          : 75x_init.s
;* Author             : MCD Application Team
;* Date First Issued  : 03/10/2006
;* Description        : This module performs:
;*                      - Memory remapping (if required),
;*                      - Stack pointer initialisation for each mode ,
;*                      - Interrupt Controller Initialisation
;*                      - Branches to ?main in the C library (which eventually
;*                        calls main()).
;*			On reset, the ARM core starts up in Supervisor (SVC) mode,
;*			in ARM state,with IRQ and FIQ disabled.
;*******************************************************************************
; History:
; 07/17/2006 : V1.0
; 03/10/2006 : V0.1
;*******************************************************************************
; THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
; WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
; AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
; INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
; CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
; INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;*******************************************************************************

        IMPORT  WAKUP_Addr                 ; imported from 75x_vect.s




  ; Depending on Your Application, Disable or Enable the following Defines
  ; ----------------------------------------------------------------------------
  ;                      SMI Bank0 configuration
  ; ----------------------------------------------------------------------------
      ; If you need to accees the SMI Bank0
      ; uncomment next line
        ;#define SMI_Bank0_EN

  ; ----------------------------------------------------------------------------
  ;                      Memory remapping
  ; ----------------------------------------------------------------------------
        ;#define Remap_SRAM    ; remap SRAM at address 0x00

  ; ----------------------------------------------------------------------------
  ;                      EIC initialization
  ; ----------------------------------------------------------------------------
        #define EIC_INIT         ; Configure and Initialize EIC

; Standard definitions of mode bits and interrupt (I & F) flags in PSRs
Mode_USR    EQU    0x10
Mode_FIQ    EQU    0x11
Mode_IRQ    EQU    0x12
Mode_SVC    EQU    0x13
Mode_ABT    EQU    0x17
Mode_UND    EQU    0x1B
Mode_SYS    EQU    0x1F

I_Bit       EQU    0x80  ; when I bit is set, IRQ is disabled
F_Bit       EQU    0x40  ; when F bit is set, FIQ is disabled


; MRCC Register
MRCC_PCLKEN_Addr    EQU    0x60000030  ; Peripheral Clock Enable register base address

; CFG Register
CFG_GLCONF_Addr     EQU    0x60000010  ; Global Configuration register base address
SRAM_mask           EQU    0x0002      ; to remap RAM at 0x0

; GPIO Register
GPIOREMAP0R_Addr    EQU    0xFFFFE420
SMI_EN_Mask         EQU    0x00000001

; SMI Register
SMI_CR1_Addr        EQU    0x90000000

; EIC Registers offsets
EIC_Base_addr    EQU    0xFFFFF800  ; EIC base address
ICR_off_addr     EQU    0x00        ; Interrupt Control register offset
CIPR_off_addr    EQU    0x08        ; Current Interrupt Priority Register offset
IVR_off_addr     EQU    0x18        ; Interrupt Vector Register offset
FIR_off_addr     EQU    0x1C        ; Fast Interrupt Register offset
IER_off_addr     EQU    0x20        ; Interrupt Enable Register offset
IPR_off_addr     EQU    0x40        ; Interrupt Pending Bit Register offset
SIR0_off_addr    EQU    0x60        ; Source Interrupt Register 0


;---------------------------------------------------------------
; ?program_start
;---------------------------------------------------------------
		MODULE	?program_start
		SECTION	IRQ_STACK:DATA:NOROOT(3)
		SECTION	FIQ_STACK:DATA:NOROOT(3)
		SECTION	UND_STACK:DATA:NOROOT(3)
		SECTION	ABT_STACK:DATA:NOROOT(3)	
		SECTION	SVC_STACK:DATA:NOROOT(3)
		SECTION	CSTACK:DATA:NOROOT(3)
		SECTION	.text:CODE(2)
		PUBLIC	__iar_program_start
		EXTERN	?main
                CODE32


__iar_program_start:
        LDR     pc, =NextInst

NextInst
; Reset all Peripheral Clocks
; This is usefull only when using debugger to Reset\Run the application

     #ifdef SMI_Bank0_EN
        LDR     r0, =0x01000000          ; Disable peripherals clock (except GPIO)
     #else
        LDR     r0, =0x00000000          ; Disable peripherals clock
     #endif
        LDR     r1, =MRCC_PCLKEN_Addr
        STR     r0, [r1]

     #ifdef SMI_Bank0_EN
        LDR     r0, =0x1875623F          ; Peripherals kept under reset (except GPIO)
     #else
        LDR     r0, =0x1975623F          ; Peripherals kept under reset
     #endif

        STR     r0, [r1,#4]
        MOV     r0, #0
        NOP                              ; Wait
        NOP
        NOP
        NOP
        STR     r0, [r1,#4]              ; Disable peripherals reset

; Initialize stack pointer registers
; Enter each mode in turn and set up the stack pointer


        MSR     CPSR_c, #Mode_FIQ|I_Bit|F_Bit    ; No interrupts
        ldr      sp,=SFE(FIQ_STACK)              ; End of FIQ_STACK

        MSR     CPSR_c, #Mode_IRQ|I_Bit|F_Bit    ; No interrupts
        ldr     sp,=SFE(IRQ_STACK)               ; End of IRQ_STACK

        MSR     CPSR_c, #Mode_ABT|I_Bit|F_Bit    ; No interrupts
        ldr     sp,=SFE(ABT_STACK)               ; End of ABT_STACK

        MSR     CPSR_c, #Mode_UND|I_Bit|F_Bit    ; No interrupts
        ldr     sp,=SFE(UND_STACK)               ; End of UND_STACK

        MSR     CPSR_c, #Mode_SVC|I_Bit|F_Bit    ; No interrupts
        ldr     sp,=SFE(SVC_STACK)               ; End of SVC_STACK

; ------------------------------------------------------------------------------
; Description  :  Enable SMI Bank0: enable GPIOs clock in MRCC_PCLKEN register,
;                 enable SMI alternate function in GPIO_REMAP register and enable
;                 Bank0 in SMI_CR1 register.
; ------------------------------------------------------------------------------
  #ifdef SMI_Bank0_EN
        MOV     r0, #0x01000000
        LDR     r1, =MRCC_PCLKEN_Addr
        STR     r0, [r1]                 ; Enable GPIOs clock

        LDR     r1, =GPIOREMAP0R_Addr
        MOV     r0, #SMI_EN_Mask
        LDR     r2, [r1]
        ORR     r2, r2, r0
        STR     r2, [r1]                 ; Enable SMI alternate function

        LDR     r0, =0x251               ; SMI Bank0 enabled, Prescaler = 2, Deselect Time = 5
        LDR     r1, =SMI_CR1_Addr
        STR     r0, [r1]                 ; Configure CR1 register
        LDR     r0, =0x00
        STR     r0, [r1,#4]              ; Reset CR2 register
  #endif

; ------------------------------------------------------------------------------
; Description  :  Remapping SRAM at address 0x00 after the application has
;                 started executing.
; ------------------------------------------------------------------------------
 #ifdef  Remap_SRAM
        MOV     r0, #SRAM_mask
        LDR     r1, =CFG_GLCONF_Addr
        LDR     r2, [r1]                  ; Read GLCONF Register
        BIC     r2, r2, #0x03             ; Reset the SW_BOOT bits
        ORR     r2, r2, r0                ; Change the SW_BOOT bits
        STR     r2, [r1]                  ; Write GLCONF Register
  #endif

;-------------------------------------------------------------------------------
;Description  : Initialize the EIC as following :
;              - IRQ disabled
;              - FIQ disabled
;              - IVR contains the load PC opcode
;              - All channels are disabled
;              - All channels priority equal to 0
;              - All SIR registers contains offset to the related IRQ table entry
;-------------------------------------------------------------------------------
  #ifdef EIC_INIT
        LDR     r3, =EIC_Base_addr
        LDR     r4, =0x00000000
        STR     r4, [r3, #ICR_off_addr]   ; Disable FIQ and IRQ
        STR     r4, [r3, #IER_off_addr]   ; Disable all interrupts channels

        LDR     r4, =0xFFFFFFFF
        STR     r4, [r3, #IPR_off_addr]   ; Clear all IRQ pending bits

        LDR     r4, =0x18
        STR     r4, [r3, #FIR_off_addr]   ; Disable FIQ channels and clear FIQ pending bits

        LDR     r4, =0x00000000
        STR     r4, [r3, #CIPR_off_addr]  ; Reset the current priority register

        LDR     r4, =0xE59F0000           ; Write the LDR pc,pc,#offset..
        STR     r4, [r3, #IVR_off_addr]   ; ..instruction code in IVR[31:16]


        LDR     r2,= 32                   ; 32 Channel to initialize
        LDR     r0, =WAKUP_Addr           ; Read the address of the IRQs address table
        LDR     r1, =0x00000FFF
        AND     r0,r0,r1
        LDR     r5,=SIR0_off_addr         ; Read SIR0 address
        SUB     r4,r0,#8                  ; subtract 8 for prefetch
        LDR     r1, =0xF7E8               ; add the offset to the 0x00 address..
                                          ; ..(IVR address + 7E8 = 0x00)
                                          ; 0xF7E8 used to complete the LDR pc,offset opcode
        ADD     r1,r4,r1                  ; compute the jump offset
EIC_INI
        MOV     r4, r1, LSL #16           ; Left shift the result
        STR     r4, [r3, r5]              ; Store the result in SIRx register
        ADD     r1, r1, #4                ; Next IRQ address
        ADD     r5, r5, #4                ; Next SIR
        SUBS    r2, r2, #1                ; Decrement the number of SIR registers to initialize
        BNE     EIC_INI                   ; If more then continue

 #endif


; --- Branch to C Library entry point

    IMPORT  ?main

    B       ?main   ; use B not BL, because an application will never return this way




        LTORG


        END
;******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE*****
