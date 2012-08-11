;******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
;* File Name          : 91x_init.s
;* Author             : MCD Application Team
;* Date First Issued  : 05/18/2006 : Version 1.0
;* Description        : This module performs:
;*                      - FLASH/RAM initialization,
;*                      - Stack pointer initialization for each mode ,
;*                      - Branches to ?main in the C library (which eventually
;*                        calls main()).
;*
;*		      On reset, the ARM core starts up in Supervisor (SVC) mode,
;*		      in ARM state,with IRQ and FIQ disabled.
;*******************************************************************************
;* History:
;* 05/22/2007 : Version 1.2
;* 05/24/2006 : Version 1.1
;* 05/18/2006 : Version 1.0
;*******************************************************************************
;* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
;* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
;* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
;* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
;* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
;* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;******************************************************************************/

; At power up, the CPU defaults to run on the oscillator clock, so Depending
; of your Application, Disable or Enable the following Define

  #define  PLL_Clock   ; Use PLL as the default clock source @ 96 MHz only with
                        ; Bank 0 @ 0x0 and Bank 1 @ 0x80000
;   #define  RTC_Clock  ; Use RTC as the default clock source
;   #define  OSC_Clock  ; Use OSC as the default clock source


; --- Standard definitions of mode bits and interrupt (I & F) flags in PSRs

Mode_USR           EQU     0x10
Mode_FIQ           EQU     0x11
Mode_IRQ           EQU     0x12
Mode_SVC           EQU     0x13
Mode_ABT           EQU     0x17
Mode_UND           EQU     0x1B
Mode_SYS           EQU     0x1F ; available on ARM Arch 4 and later

I_Bit              EQU     0x80 ; when I bit is set, IRQ is disabled
F_Bit              EQU     0x40 ; when F bit is set, FIQ is disabled



; --- STR9X SCU specific definitions

SCU_BASE_Address    EQU     0x5C002000 ; SCU Base Address
SCU_CLKCNTR_OFST    EQU     0x00000000 ; Clock Control register Offset
SCU_PLLCONF_OFST    EQU     0x00000004 ; PLL Configuration register Offset
SCU_SYSSTATUS_OFST  EQU     0x00000008 ; System Status Register Offset
SCU_SCR0_OFST       EQU     0x00000034 ; System Configuration Register 0 Offset

; --- STR9X FMI specific definitions

FMI_BASE_Address    EQU     0x54000000 ; FMI Base Address
FMI_BBSR_OFST       EQU     0x00000000 ; Boot Bank Size Register
FMI_NBBSR_OFST      EQU     0x00000004 ; Non-boot Bank Size Register
FMI_BBADR_OFST      EQU     0x0000000C ; Boot Bank Base Address Register
FMI_NBBADR_OFST     EQU     0x00000010 ; Non-boot Bank Base Address Register
FMI_CR_OFST         EQU     0x00000018 ; Control Register

;---------------------------------------------------------------
; ?program_start
;---------------------------------------------------------------
       MODULE  ?program_start

       SECTION	   IRQ_STACK:DATA:NOROOT(3)
       SECTION	   FIQ_STACK:DATA:NOROOT(3)
       SECTION	   UND_STACK:DATA:NOROOT(3)
       SECTION	   ABT_STACK:DATA:NOROOT(3)		
       SECTION	   SVC_STACK:DATA:NOROOT(3)
       SECTION	   CSTACK:DATA:NOROOT(3)
       SECTION .icode:CODE:NOROOT(2)
       PUBLIC __iar_program_start
       EXTERN  ?main
       CODE32

__iar_program_start:
        LDR     pc, =NextInst


NextInst


        NOP   ; execute some instructions to access CPU registers after wake
        NOP   ; up from Reset, while waiting for OSC stabilization
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP


; BUFFERED_Mode
; ------------------------------------------------------------------------------
; Description  :  Enable the Buffered mode.
;                 Just enable the buffered define on the 91x_conf.h
; http://www.arm.com/pdfs/DDI0164A_966E_S.pdf
; ------------------------------------------------------------------------------

       MRC     p15, 0, r0, c1, c0, 0   ; Read CP15 register 1 into r0
       ORR     r0, r0, #0x8          ; Enable Write Buffer on AHB
       MCR     p15, 0, r0, c1, c0, 0   ; Write CP15 register 1



; --- Remap Flash Bank 0 at address 0x0 and Bank 1 at address 0x80000,
;     when the bank 0 is the boot bank, then enable the Bank 1.

        LDR     R6, =FMI_BASE_Address

        LDR     R7, = 0x4                     ; BOOT BANK Size = 512KB
        STR     R7, [R6, #FMI_BBSR_OFST]      ; (2^4) * 32 = 512KB

        LDR     R7, = 0x2                     ; NON BOOT BANK Size = 32KB
        STR     R7, [R6, #FMI_NBBSR_OFST]     ; (2^2) * 8 = 32KB

        LDR     R7, = 0x0                     ; BOOT BANK Address = 0x0
        STR     R7, [R6, #FMI_BBADR_OFST]

        LDR     R7, = 0x20000                 ; NON BOOT BANK Address = 0x80000
        STR     R7, [R6, #FMI_NBBADR_OFST]    ; need to put 0x20000 because FMI
                                              ; bus on A[25:2] of CPU bus

        LDR     R7, = 0x18                    ; Enable CS on both banks
        STR     R7, [R6, #FMI_CR_OFST]        ; LDR     R7, = 0x19 ;in RevD
                                              ; to enable 8 words PFQ deepth

; --- Enable 96K RAM, PFQBC enabled, DTCM & AHB wait-states disabled
        LDR     R0, = SCU_BASE_Address
        LDR     R1, = 0x0191
        STR     R1, [R0, #SCU_SCR0_OFST]

; ------------------------------------------------------------------------------
; --- System clock configuration
; ------------------------------------------------------------------------------

#ifdef PLL_Clock  ; Use 96 MHZ PLL clock as the default frequency

; --- wait states Flash confguration

        LDR     R6, = 0x00080000            ;Write a Write Flash Configuration
        LDR     R7, =0x60                   ;Register command (60h) to any word
        STRH    R7, [R6]                    ;address in Bank 1.

        LDR     R6, = 0x00083040            ;Write a Write Flash Configuration
        LDR     R7, = 0x3                   ;Register Confirm command (03h)
        STRH    R7, [R6]                    ;2Wstaites in read,PWD,LVD enabled,
                                            ;High BUSCFG.
; --- PLL configuration
        LDR     R1, = 0x00020002              ;Set OSC as clock source
        STR     R1, [R0, #SCU_CLKCNTR_OFST ]


        NOP     ; Wait for OSC stabilization
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP


		
		
        LDR     R1, = 0x000ac019               ;Set PLL ENABLE, to 96Mhz
        STR     R1, [R0, #SCU_PLLCONF_OFST]

Wait_Loop
        LDR     R1,[R0, #SCU_SYSSTATUS_OFST]   ;Wait until PLL is Locked
        ANDS    R1, R1, #0x01
        BEQ     Wait_Loop

        LDR     R1, = 0x00020080             ;Set PLL as clock source after pll
        STR     R1, [R0, #SCU_CLKCNTR_OFST ] ;is locked and  FMICLK=RCLK,
                                             ;PCLK=RCLK/2
#endif

#ifdef  RTC_Clock   ;Use RTC  as the default clock source
        LDR     R1, = 0x00020001              ;Set RTC as clock source and
        STR     R1, [R0, #SCU_CLKCNTR_OFST ]  ;FMICLK=RCLK, PCLK=RCLK
#endif

#ifdef OSC_Clock  ;Use Osc as the default clock source
        LDR     R1, = 0x00020002              ;Set OSC as clock source  and
        STR     R1, [R0, #SCU_CLKCNTR_OFST ]  ;FMICLK=RCLK, PCLK=RCLK
#endif


; --- Initialize Stack pointer registers

; Enter each mode in turn and set up the stack pointer

       MSR     CPSR_c, #Mode_FIQ|I_Bit|F_Bit    ; No interrupts
       LDR     SP, =SFE(FIQ_STACK)

       MSR     CPSR_c, #Mode_IRQ|I_Bit|F_Bit    ; No interrupts
       LDR     SP, = SFE(IRQ_STACK)

       MSR     CPSR_c, #Mode_ABT|I_Bit|F_Bit    ; No interrupts
       LDR     SP, = SFE(ABT_STACK)
	
       MSR     CPSR_c, #Mode_UND|I_Bit|F_Bit    ; No interrupts
       LDR     SP, = SFE(UND_STACK)

        MSR     CPSR_c, #Mode_SYS               ; IRQs & FIQs are now enabled
        LDR     SP, = SFE(CSTACK)

       MSR     CPSR_c, #Mode_SVC|I_Bit|F_Bit    ; No interrupts
       LDR     SP, = SFE(SVC_STACK)

; --- Set bits 17-18(DTCM/ITCM order bits)of the Core Configuration Control
;     Register
       MOV     r0, #0x60000
       MCR     p15,0x1,r0,c15,c1,0

; --- Now enter the C code
        B       ?main   ; Note : use B not BL, because an application will
                         ; never return this way

        LTORG


        END
;******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****




