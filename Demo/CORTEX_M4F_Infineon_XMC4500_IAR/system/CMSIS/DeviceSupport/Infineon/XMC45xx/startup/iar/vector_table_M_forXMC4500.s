;*************************************************
;*
;* Part one of the system initialization code, contains low-level
;* initialization, plain thumb variant.
;*
;* Copyright 2008 IAR Systems. All rights reserved.
;*
;* $Revision: 50748 $
;*
;*************************************************

;
; The modules in this file are included in the libraries, and may be replaced
; by any user-defined modules that define the PUBLIC symbol _program_start or
; a user defined start symbol.
; To override the cstartup defined in the library, simply add your modified
; version to the workbench project.
;
; The vector table is normally located at address 0.
; When debugging in RAM, it can be located in RAM, aligned to at least 2^6.
; The name "__vector_table" has special meaning for C-SPY:
; it is where the SP start value is found, and the NVIC vector
; table register (VTOR) is initialized to this address if != 0.
;
; Cortex-M version with interrupt handler for XMC4500 from Infineon
;

        MODULE  ?vector_table

        AAPCS INTERWORK, VFP_COMPATIBLE, RWPI_COMPATIBLE
        PRESERVE8


        ;; Forward declaration of sections.
        SECTION CSTACK:DATA:NOROOT(3)

        SECTION .intvec:CODE:NOROOT(2)

        EXTERN  __iar_program_start
        PUBLIC  __vector_table

        DATA

__iar_init$$done:               ; The vector table is not needed
                                ; until after copy initialization is done

__vector_table
        DCD     sfe(CSTACK)
        DCD     Reset_Handler

        DCD     NMI_Handler
        DCD     HardFault_Handler
        DCD     MemManage_Handler
        DCD     BusFault_Handler
        DCD     UsageFault_Handler
        DCD     0
        DCD     0
        DCD     0
        DCD     0
        DCD     SVC_Handler
        DCD     DebugMon_Handler
        DCD     0
        DCD     PendSV_Handler
        DCD     SysTick_Handler

    ; Interrupt Handlers for Service Requests (SR) from XMC4500 Peripherals
	    DCD   SCU_0_IRQHandler            ; Handler name for SR SCU_0
	    DCD   ERU0_0_IRQHandler           ; Handler name for SR ERU0_0
	    DCD   ERU0_1_IRQHandler           ; Handler name for SR ERU0_1
	    DCD   ERU0_2_IRQHandler           ; Handler name for SR ERU0_2
	    DCD   ERU0_3_IRQHandler           ; Handler name for SR ERU0_3
	    DCD   ERU1_0_IRQHandler           ; Handler name for SR ERU1_0
	    DCD   ERU1_1_IRQHandler           ; Handler name for SR ERU1_1
	    DCD   ERU1_2_IRQHandler           ; Handler name for SR ERU1_2
	    DCD   ERU1_3_IRQHandler           ; Handler name for SR ERU1_3
	    DCD   0                           ; Not Available
	    DCD   0                           ; Not Available
	    DCD   0                           ; Not Available
	    DCD   PMU0_0_IRQHandler           ; Handler name for SR PMU0_0
	    DCD   0                           ; Not Available
	    DCD   VADC0_C0_0_IRQHandler       ; Handler name for SR VADC0_C0_0
	    DCD   VADC0_C0_1_IRQHandler       ; Handler name for SR VADC0_C0_1
	    DCD   VADC0_C0_2_IRQHandler       ; Handler name for SR VADC0_C0_1
	    DCD   VADC0_C0_3_IRQHandler       ; Handler name for SR VADC0_C0_3
	    DCD   VADC0_G0_0_IRQHandler       ; Handler name for SR VADC0_G0_0
	    DCD   VADC0_G0_1_IRQHandler       ; Handler name for SR VADC0_G0_1
	    DCD   VADC0_G0_2_IRQHandler       ; Handler name for SR VADC0_G0_2
	    DCD   VADC0_G0_3_IRQHandler       ; Handler name for SR VADC0_G0_3
	    DCD   VADC0_G1_0_IRQHandler       ; Handler name for SR VADC0_G1_0
	    DCD   VADC0_G1_1_IRQHandler       ; Handler name for SR VADC0_G1_1
	    DCD   VADC0_G1_2_IRQHandler       ; Handler name for SR VADC0_G1_2
	    DCD   VADC0_G1_3_IRQHandler       ; Handler name for SR VADC0_G1_3
	    DCD   VADC0_G2_0_IRQHandler       ; Handler name for SR VADC0_G2_0
	    DCD   VADC0_G2_1_IRQHandler       ; Handler name for SR VADC0_G2_1
	    DCD   VADC0_G2_2_IRQHandler       ; Handler name for SR VADC0_G2_2
	    DCD   VADC0_G2_3_IRQHandler       ; Handler name for SR VADC0_G2_3
	    DCD   VADC0_G3_0_IRQHandler       ; Handler name for SR VADC0_G3_0
	    DCD   VADC0_G3_1_IRQHandler       ; Handler name for SR VADC0_G3_1
	    DCD   VADC0_G3_2_IRQHandler       ; Handler name for SR VADC0_G3_2
	    DCD   VADC0_G3_3_IRQHandler       ; Handler name for SR VADC0_G3_3
	    DCD   DSD0_0_IRQHandler           ; Handler name for SR DSD0_0
	    DCD   DSD0_1_IRQHandler           ; Handler name for SR DSD0_1
	    DCD   DSD0_2_IRQHandler           ; Handler name for SR DSD0_2
	    DCD   DSD0_3_IRQHandler           ; Handler name for SR DSD0_3
	    DCD   DSD0_4_IRQHandler           ; Handler name for SR DSD0_4
	    DCD   DSD0_5_IRQHandler           ; Handler name for SR DSD0_5
	    DCD   DSD0_6_IRQHandler           ; Handler name for SR DSD0_6
	    DCD   DSD0_7_IRQHandler           ; Handler name for SR DSD0_7
	    DCD   DAC0_0_IRQHandler           ; Handler name for SR DAC0_0
	    DCD   DAC0_1_IRQHandler           ; Handler name for SR DAC0_0
	    DCD   CCU40_0_IRQHandler          ; Handler name for SR CCU40_0
	    DCD   CCU40_1_IRQHandler          ; Handler name for SR CCU40_1
	    DCD   CCU40_2_IRQHandler          ; Handler name for SR CCU40_2
	    DCD   CCU40_3_IRQHandler          ; Handler name for SR CCU40_3
	    DCD   CCU41_0_IRQHandler          ; Handler name for SR CCU41_0
	    DCD   CCU41_1_IRQHandler          ; Handler name for SR CCU41_1
	    DCD   CCU41_2_IRQHandler          ; Handler name for SR CCU41_2
	    DCD   CCU41_3_IRQHandler          ; Handler name for SR CCU41_3
	    DCD   CCU42_0_IRQHandler          ; Handler name for SR CCU42_0
	    DCD   CCU42_1_IRQHandler          ; Handler name for SR CCU42_1
	    DCD   CCU42_2_IRQHandler          ; Handler name for SR CCU42_2
	    DCD   CCU42_3_IRQHandler          ; Handler name for SR CCU42_3
	    DCD   CCU43_0_IRQHandler          ; Handler name for SR CCU43_0
	    DCD   CCU43_1_IRQHandler          ; Handler name for SR CCU43_1
	    DCD   CCU43_2_IRQHandler          ; Handler name for SR CCU43_2
	    DCD   CCU43_3_IRQHandler          ; Handler name for SR CCU43_3
	    DCD   CCU80_0_IRQHandler          ; Handler name for SR CCU80_0
	    DCD   CCU80_1_IRQHandler          ; Handler name for SR CCU80_1
	    DCD   CCU80_2_IRQHandler          ; Handler name for SR CCU80_2
	    DCD   CCU80_3_IRQHandler          ; Handler name for SR CCU80_3
	    DCD   CCU81_0_IRQHandler          ; Handler name for SR CCU81_0
	    DCD   CCU81_1_IRQHandler          ; Handler name for SR CCU81_1
	    DCD   CCU81_2_IRQHandler          ; Handler name for SR CCU81_2
	    DCD   CCU81_3_IRQHandler          ; Handler name for SR CCU81_3
	    DCD   POSIF0_0_IRQHandler         ; Handler name for SR POSIF0_0
	    DCD   POSIF0_1_IRQHandler         ; Handler name for SR POSIF0_1
	    DCD   POSIF1_0_IRQHandler         ; Handler name for SR POSIF1_0
	    DCD   POSIF1_1_IRQHandler         ; Handler name for SR POSIF1_1
	    DCD   0                           ; Not Available
	    DCD   0                           ; Not Available
	    DCD   0                           ; Not Available
	    DCD   0                           ; Not Available
	    DCD   CAN0_0_IRQHandler           ; Handler name for SR CAN0_0
	    DCD   CAN0_1_IRQHandler           ; Handler name for SR CAN0_1
	    DCD   CAN0_2_IRQHandler           ; Handler name for SR CAN0_2
	    DCD   CAN0_3_IRQHandler           ; Handler name for SR CAN0_3
	    DCD   CAN0_4_IRQHandler           ; Handler name for SR CAN0_4
	    DCD   CAN0_5_IRQHandler           ; Handler name for SR CAN0_5
	    DCD   CAN0_6_IRQHandler           ; Handler name for SR CAN0_6
	    DCD   CAN0_7_IRQHandler           ; Handler name for SR CAN0_7
	    DCD   USIC0_0_IRQHandler          ; Handler name for SR USIC0_0
	    DCD   USIC0_1_IRQHandler          ; Handler name for SR USIC0_1
	    DCD   USIC0_2_IRQHandler          ; Handler name for SR USIC0_2
	    DCD   USIC0_3_IRQHandler          ; Handler name for SR USIC0_3
	    DCD   USIC0_4_IRQHandler          ; Handler name for SR USIC0_4
	    DCD   USIC0_5_IRQHandler          ; Handler name for SR USIC0_5
	    DCD   USIC1_0_IRQHandler          ; Handler name for SR USIC1_0
	    DCD   USIC1_1_IRQHandler          ; Handler name for SR USIC1_1
	    DCD   USIC1_2_IRQHandler          ; Handler name for SR USIC1_2
	    DCD   USIC1_3_IRQHandler          ; Handler name for SR USIC1_3
	    DCD   USIC1_4_IRQHandler          ; Handler name for SR USIC1_4
	    DCD   USIC1_5_IRQHandler          ; Handler name for SR USIC1_5
	    DCD   USIC2_0_IRQHandler          ; Handler name for SR USIC2_0
	    DCD   USIC2_1_IRQHandler          ; Handler name for SR USIC2_1
	    DCD   USIC2_2_IRQHandler          ; Handler name for SR USIC2_2
	    DCD   USIC2_3_IRQHandler          ; Handler name for SR USIC2_3
	    DCD   USIC2_4_IRQHandler          ; Handler name for SR USIC2_4
	    DCD   USIC2_5_IRQHandler          ; Handler name for SR USIC2_5
	    DCD   LEDTS0_0_IRQHandler         ; Handler name for SR LEDTS0_0
	    DCD   0                           ; Not Available
	    DCD   FCE0_0_IRQHandler           ; Handler name for SR FCE0_0
	    DCD   GPDMA0_0_IRQHandler         ; Handler name for SR GPDMA0_0
	    DCD   SDMMC0_0_IRQHandler         ; Handler name for SR SDMMC0_0
	    DCD   USB0_0_IRQHandler           ; Handler name for SR USB0_0
	    DCD   ETH0_0_IRQHandler           ; Handler name for SR ETH0_0
	    DCD   0                           ; Not Available
	    DCD   GPDMA1_0_IRQHandler         ; Handler name for SR GPDMA1_0
	    DCD   0                           ; Not Available




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Default interrupt handlers.
;;

        PUBWEAK NMI_Handler
        PUBWEAK HardFault_Handler
        PUBWEAK MemManage_Handler
        PUBWEAK BusFault_Handler
        PUBWEAK UsageFault_Handler
        PUBWEAK SVC_Handler
        PUBWEAK DebugMon_Handler
        PUBWEAK PendSV_Handler
        PUBWEAK SysTick_Handler
;; XMC4500 interrupt handlers
      PUBWEAK   SCU_0_IRQHandler
	    PUBWEAK   ERU0_0_IRQHandler
	    PUBWEAK   ERU0_1_IRQHandler
	    PUBWEAK   ERU0_2_IRQHandler
	    PUBWEAK   ERU0_3_IRQHandler
	    PUBWEAK   ERU1_0_IRQHandler
	    PUBWEAK   ERU1_1_IRQHandler
	    PUBWEAK   ERU1_2_IRQHandler
	    PUBWEAK   ERU1_3_IRQHandler
	    PUBWEAK   PMU0_0_IRQHandler
	    PUBWEAK   PMU0_1_IRQHandler
	    PUBWEAK   VADC0_C0_0_IRQHandler
	    PUBWEAK   VADC0_C0_1_IRQHandler
	    PUBWEAK   VADC0_C0_2_IRQHandler
	    PUBWEAK   VADC0_C0_3_IRQHandler
	    PUBWEAK   VADC0_G0_0_IRQHandler
	    PUBWEAK   VADC0_G0_1_IRQHandler
	    PUBWEAK   VADC0_G0_2_IRQHandler
	    PUBWEAK   VADC0_G0_3_IRQHandler
	    PUBWEAK   VADC0_G1_0_IRQHandler
	    PUBWEAK   VADC0_G1_1_IRQHandler
	    PUBWEAK   VADC0_G1_2_IRQHandler
	    PUBWEAK   VADC0_G1_3_IRQHandler
	    PUBWEAK   VADC0_G2_0_IRQHandler
	    PUBWEAK   VADC0_G2_1_IRQHandler
	    PUBWEAK   VADC0_G2_2_IRQHandler
	    PUBWEAK   VADC0_G2_3_IRQHandler
	    PUBWEAK   VADC0_G3_0_IRQHandler
	    PUBWEAK   VADC0_G3_1_IRQHandler
	    PUBWEAK   VADC0_G3_2_IRQHandler
	    PUBWEAK   VADC0_G3_3_IRQHandler
	    PUBWEAK   DSD0_0_IRQHandler
	    PUBWEAK   DSD0_1_IRQHandler
	    PUBWEAK   DSD0_2_IRQHandler
	    PUBWEAK   DSD0_3_IRQHandler
	    PUBWEAK   DSD0_4_IRQHandler
	    PUBWEAK   DSD0_5_IRQHandler
	    PUBWEAK   DSD0_6_IRQHandler
	    PUBWEAK   DSD0_7_IRQHandler
	    PUBWEAK   DAC0_0_IRQHandler
	    PUBWEAK   DAC0_1_IRQHandler
	    PUBWEAK   CCU40_0_IRQHandler
	    PUBWEAK   CCU40_1_IRQHandler
	    PUBWEAK   CCU40_2_IRQHandler
	    PUBWEAK   CCU40_3_IRQHandler
	    PUBWEAK   CCU41_0_IRQHandler
	    PUBWEAK   CCU41_1_IRQHandler
	    PUBWEAK   CCU41_2_IRQHandler
	    PUBWEAK   CCU41_3_IRQHandler
	    PUBWEAK   CCU42_0_IRQHandler
	    PUBWEAK   CCU42_1_IRQHandler
	    PUBWEAK   CCU42_2_IRQHandler
	    PUBWEAK   CCU42_3_IRQHandler
	    PUBWEAK   CCU43_0_IRQHandler
	    PUBWEAK   CCU43_1_IRQHandler
	    PUBWEAK   CCU43_2_IRQHandler
	    PUBWEAK   CCU43_3_IRQHandler
	    PUBWEAK   CCU80_0_IRQHandler
	    PUBWEAK   CCU80_1_IRQHandler
	    PUBWEAK   CCU80_2_IRQHandler
	    PUBWEAK   CCU80_3_IRQHandler
	    PUBWEAK   CCU81_0_IRQHandler
	    PUBWEAK   CCU81_1_IRQHandler
	    PUBWEAK   CCU81_2_IRQHandler
	    PUBWEAK   CCU81_3_IRQHandler
	    PUBWEAK   POSIF0_0_IRQHandler
	    PUBWEAK   POSIF0_1_IRQHandler
	    PUBWEAK   POSIF1_0_IRQHandler
	    PUBWEAK   POSIF1_1_IRQHandler
	    PUBWEAK   CAN0_0_IRQHandler
	    PUBWEAK   CAN0_1_IRQHandler
	    PUBWEAK   CAN0_2_IRQHandler
	    PUBWEAK   CAN0_3_IRQHandler
	    PUBWEAK   CAN0_4_IRQHandler
	    PUBWEAK   CAN0_5_IRQHandler
	    PUBWEAK   CAN0_6_IRQHandler
	    PUBWEAK   CAN0_7_IRQHandler
	    PUBWEAK   USIC0_0_IRQHandler
	    PUBWEAK   USIC0_1_IRQHandler
	    PUBWEAK   USIC0_2_IRQHandler
	    PUBWEAK   USIC0_3_IRQHandler
	    PUBWEAK   USIC0_4_IRQHandler
	    PUBWEAK   USIC0_5_IRQHandler
	    PUBWEAK   USIC1_0_IRQHandler
	    PUBWEAK   USIC1_1_IRQHandler
	    PUBWEAK   USIC1_2_IRQHandler
	    PUBWEAK   USIC1_3_IRQHandler
	    PUBWEAK   USIC1_4_IRQHandler
	    PUBWEAK   USIC1_5_IRQHandler
	    PUBWEAK   USIC2_0_IRQHandler
	    PUBWEAK   USIC2_1_IRQHandler
	    PUBWEAK   USIC2_2_IRQHandler
	    PUBWEAK   USIC2_3_IRQHandler
	    PUBWEAK   USIC2_4_IRQHandler
	    PUBWEAK   USIC2_5_IRQHandler
	    PUBWEAK   LEDTS0_0_IRQHandler
	    PUBWEAK   FCE0_0_IRQHandler
	    PUBWEAK   GPDMA0_0_IRQHandler
	    PUBWEAK   SDMMC0_0_IRQHandler
	    PUBWEAK   USB0_0_IRQHandler
	    PUBWEAK   ETH0_0_IRQHandler
	    PUBWEAK   GPDMA1_0_IRQHandler

        SECTION .text:CODE:REORDER(2)
        THUMB

NMI_Handler
HardFault_Handler
MemManage_Handler
BusFault_Handler
UsageFault_Handler
SVC_Handler
DebugMon_Handler
PendSV_Handler
SysTick_Handler

SCU_0_IRQHandler
ERU0_0_IRQHandler
ERU0_1_IRQHandler
ERU0_2_IRQHandler
ERU0_3_IRQHandler
ERU1_0_IRQHandler
ERU1_1_IRQHandler
ERU1_2_IRQHandler
ERU1_3_IRQHandler
PMU0_0_IRQHandler
PMU0_1_IRQHandler
VADC0_C0_0_IRQHandler
VADC0_C0_1_IRQHandler
VADC0_C0_2_IRQHandler
VADC0_C0_3_IRQHandler
VADC0_G0_0_IRQHandler
VADC0_G0_1_IRQHandler
VADC0_G0_2_IRQHandler
VADC0_G0_3_IRQHandler
VADC0_G1_0_IRQHandler
VADC0_G1_1_IRQHandler
VADC0_G1_2_IRQHandler
VADC0_G1_3_IRQHandler
VADC0_G2_0_IRQHandler
VADC0_G2_1_IRQHandler
VADC0_G2_2_IRQHandler
VADC0_G2_3_IRQHandler
VADC0_G3_0_IRQHandler
VADC0_G3_1_IRQHandler
VADC0_G3_2_IRQHandler
VADC0_G3_3_IRQHandler
DSD0_0_IRQHandler
DSD0_1_IRQHandler
DSD0_2_IRQHandler
DSD0_3_IRQHandler
DSD0_4_IRQHandler
DSD0_5_IRQHandler
DSD0_6_IRQHandler
DSD0_7_IRQHandler
DAC0_0_IRQHandler
DAC0_1_IRQHandler
CCU40_0_IRQHandler
CCU40_1_IRQHandler
CCU40_2_IRQHandler
CCU40_3_IRQHandler
CCU41_0_IRQHandler
CCU41_1_IRQHandler
CCU41_2_IRQHandler
CCU41_3_IRQHandler
CCU42_0_IRQHandler
CCU42_1_IRQHandler
CCU42_2_IRQHandler
CCU42_3_IRQHandler
CCU43_0_IRQHandler
CCU43_1_IRQHandler
CCU43_2_IRQHandler
CCU43_3_IRQHandler
CCU80_0_IRQHandler
CCU80_1_IRQHandler
CCU80_2_IRQHandler
CCU80_3_IRQHandler
CCU81_0_IRQHandler
CCU81_1_IRQHandler
CCU81_2_IRQHandler
CCU81_3_IRQHandler
POSIF0_0_IRQHandler
POSIF0_1_IRQHandler
POSIF1_0_IRQHandler
POSIF1_1_IRQHandler
CAN0_0_IRQHandler
CAN0_1_IRQHandler
CAN0_2_IRQHandler
CAN0_3_IRQHandler
CAN0_4_IRQHandler
CAN0_5_IRQHandler
CAN0_6_IRQHandler
CAN0_7_IRQHandler
USIC0_0_IRQHandler
USIC0_1_IRQHandler
USIC0_2_IRQHandler
USIC0_3_IRQHandler
USIC0_4_IRQHandler
USIC0_5_IRQHandler
USIC1_0_IRQHandler
USIC1_1_IRQHandler
USIC1_2_IRQHandler
USIC1_3_IRQHandler
USIC1_4_IRQHandler
USIC1_5_IRQHandler
USIC2_0_IRQHandler
USIC2_1_IRQHandler
USIC2_2_IRQHandler
USIC2_3_IRQHandler
USIC2_4_IRQHandler
USIC2_5_IRQHandler
LEDTS0_0_IRQHandler
FCE0_0_IRQHandler
GPDMA0_0_IRQHandler
SDMMC0_0_IRQHandler
USB0_0_IRQHandler
ETH0_0_IRQHandler
GPDMA1_0_IRQHandler

Default_Handler
        NOCALL Default_Handler
        B Default_Handler

PREF_PCON       EQU 0x58004000
SCU_GCU_PEEN    EQU 0x5000413C
SCU_GCU_PEFLAG  EQU 0x50004150

        SECTION .text:CODE:REORDER(2)
        THUMB
Reset_Handler:
        ; A11 workaround for branch prediction and parity
        LDR R0,=PREF_PCON        /* switch off branch prediction required in A11 step to use cached memory*/
        LDR R1,[R0]
        ORR R1,R1,#0x00010000
        STR R1,[R0]

        /* Clear existing parity errors if any required in A11 step */
        LDR R0,=SCU_GCU_PEFLAG
        MOV R1,#0xFFFFFFFF
        STR R1,[R0]

        /* Disable parity  required in A11 step*/
        LDR R0,=SCU_GCU_PEEN
        MOV R1,#0
        STR R1,[R0]
        B __iar_program_start
        
        END
