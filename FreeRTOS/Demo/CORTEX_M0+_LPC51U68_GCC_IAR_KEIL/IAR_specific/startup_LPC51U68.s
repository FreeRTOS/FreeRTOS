;/*****************************************************************************
; * @file:    startup_LPC51U68.s
; * @purpose: CMSIS Cortex-M0 Core Device Startup File
; *           LPC51U68
; * @version: 1.0
; * @date:    2017-12-15
; *----------------------------------------------------------------------------
; *
; Copyright 1997-2016 Freescale Semiconductor, Inc.
; Copyright 2016-2018 NXP
;
; SPDX-License-Identifier: BSD-3-Clause
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
; Cortex-M version
;

        MODULE  ?cstartup

        ;; Forward declaration of sections.
        SECTION CSTACK:DATA:NOROOT(3)

        SECTION .intvec:CODE:NOROOT(2)

        EXTERN  __iar_program_start
        EXTERN  SystemInit
        PUBLIC  __vector_table
        PUBLIC  __vector_table_0x1c
        PUBLIC  __Vectors
        PUBLIC  __Vectors_End
        PUBLIC  __Vectors_Size

        DATA

__vector_table
        DCD     sfe(CSTACK)
        DCD     Reset_Handler

        DCD     NMI_Handler
        DCD     HardFault_Handler
        DCD     0
        DCD     0
        DCD     0
__vector_table_0x1c
        DCD     0
        DCD     0
        DCD     0
        DCD     0
        DCD     SVC_Handler
        DCD     0
        DCD     0
        DCD     PendSV_Handler
        DCD     SysTick_Handler

        ; External Interrupts
        DCD     WDT_BOD_IRQHandler  ; Windowed watchdog timer, Brownout detect
        DCD     DMA0_IRQHandler  ; DMA controller
        DCD     GINT0_IRQHandler  ; GPIO group 0
        DCD     GINT1_IRQHandler  ; GPIO group 1
        DCD     PIN_INT0_IRQHandler  ; Pin interrupt 0 or pattern match engine slice 0
        DCD     PIN_INT1_IRQHandler  ; Pin interrupt 1or pattern match engine slice 1
        DCD     PIN_INT2_IRQHandler  ; Pin interrupt 2 or pattern match engine slice 2
        DCD     PIN_INT3_IRQHandler  ; Pin interrupt 3 or pattern match engine slice 3
        DCD     UTICK0_IRQHandler  ; Micro-tick Timer
        DCD     MRT0_IRQHandler  ; Multi-rate timer
        DCD     CTIMER0_IRQHandler  ; Standard counter/timer CTIMER0
        DCD     CTIMER1_IRQHandler  ; Standard counter/timer CTIMER1
        DCD     SCT0_IRQHandler  ; SCTimer/PWM
        DCD     CTIMER3_IRQHandler  ; Standard counter/timer CTIMER3
        DCD     FLEXCOMM0_IRQHandler  ; Flexcomm Interface 0 (USART, SPI, I2C)
        DCD     FLEXCOMM1_IRQHandler  ; Flexcomm Interface 1 (USART, SPI, I2C)
        DCD     FLEXCOMM2_IRQHandler  ; Flexcomm Interface 2 (USART, SPI, I2C)
        DCD     FLEXCOMM3_IRQHandler  ; Flexcomm Interface 3 (USART, SPI, I2C)
        DCD     FLEXCOMM4_IRQHandler  ; Flexcomm Interface 4 (USART, SPI, I2C)
        DCD     FLEXCOMM5_IRQHandler  ; Flexcomm Interface 5 (USART, SPI, I2C)
        DCD     FLEXCOMM6_IRQHandler  ; Flexcomm Interface 6 (USART, SPI, I2C, I2S)
        DCD     FLEXCOMM7_IRQHandler  ; Flexcomm Interface 7 (USART, SPI, I2C, I2S)
        DCD     ADC0_SEQA_IRQHandler  ; ADC0 sequence A completion.
        DCD     ADC0_SEQB_IRQHandler  ; ADC0 sequence B completion.
        DCD     ADC0_THCMP_IRQHandler  ; ADC0 threshold compare and error.
        DCD     Reserved41_IRQHandler  ; Reserved interrupt
        DCD     Reserved42_IRQHandler  ; Reserved interrupt
        DCD     USB0_NEEDCLK_IRQHandler  ; USB Activity Wake-up Interrupt
        DCD     USB0_IRQHandler  ; USB device
        DCD     RTC_IRQHandler  ; RTC alarm and wake-up interrupts
        DCD     Reserved46_IRQHandler  ; Reserved interrupt
        DCD     Reserved47_IRQHandler  ; Reserved interrupt
__Vectors_End

; Code Read Protection Level (CRP)
;    <0xFFFFFFFF=> Disabled
;    <0x4E697370=> NO_ISP
;    <0x12345678=> CRP1
;    <0x87654321=> CRP2
;    <0x43218765=> CRP3

#if !defined NO_CRP
        SECTION .crp:CODE
__CRP
      	DCD	0xFFFFFFFF
__CRP_End
#endif

__Vectors       EQU   __vector_table
__Vectors_Size 	EQU 	__Vectors_End - __Vectors


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Default interrupt handlers.
;;
        THUMB

        PUBWEAK Reset_Handler
        SECTION .text:CODE:REORDER:NOROOT(2)
Reset_Handler
        LDR     r0, =SystemInit
        BLX     r0
        LDR     r0, =__iar_program_start
        BX      r0

        PUBWEAK NMI_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
NMI_Handler
        B .

        PUBWEAK HardFault_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
HardFault_Handler
        B .

        PUBWEAK SVC_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
SVC_Handler
        B .

        PUBWEAK PendSV_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
PendSV_Handler
        B .

        PUBWEAK SysTick_Handler
        SECTION .text:CODE:REORDER:NOROOT(1)
SysTick_Handler
        B .

        PUBWEAK WDT_BOD_IRQHandler
        PUBWEAK WDT_BOD_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
WDT_BOD_IRQHandler
        LDR     R0, =WDT_BOD_DriverIRQHandler
        BX      R0
        PUBWEAK DMA0_IRQHandler
        PUBWEAK DMA0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
DMA0_IRQHandler
        LDR     R0, =DMA0_DriverIRQHandler
        BX      R0
        PUBWEAK GINT0_IRQHandler
        PUBWEAK GINT0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
GINT0_IRQHandler
        LDR     R0, =GINT0_DriverIRQHandler
        BX      R0
        PUBWEAK GINT1_IRQHandler
        PUBWEAK GINT1_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
GINT1_IRQHandler
        LDR     R0, =GINT1_DriverIRQHandler
        BX      R0
        PUBWEAK PIN_INT0_IRQHandler
        PUBWEAK PIN_INT0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
PIN_INT0_IRQHandler
        LDR     R0, =PIN_INT0_DriverIRQHandler
        BX      R0
        PUBWEAK PIN_INT1_IRQHandler
        PUBWEAK PIN_INT1_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
PIN_INT1_IRQHandler
        LDR     R0, =PIN_INT1_DriverIRQHandler
        BX      R0
        PUBWEAK PIN_INT2_IRQHandler
        PUBWEAK PIN_INT2_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
PIN_INT2_IRQHandler
        LDR     R0, =PIN_INT2_DriverIRQHandler
        BX      R0
        PUBWEAK PIN_INT3_IRQHandler
        PUBWEAK PIN_INT3_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
PIN_INT3_IRQHandler
        LDR     R0, =PIN_INT3_DriverIRQHandler
        BX      R0
        PUBWEAK UTICK0_IRQHandler
        PUBWEAK UTICK0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
UTICK0_IRQHandler
        LDR     R0, =UTICK0_DriverIRQHandler
        BX      R0
        PUBWEAK MRT0_IRQHandler
        PUBWEAK MRT0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
MRT0_IRQHandler
        LDR     R0, =MRT0_DriverIRQHandler
        BX      R0
        PUBWEAK CTIMER0_IRQHandler
        PUBWEAK CTIMER0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
CTIMER0_IRQHandler
        LDR     R0, =CTIMER0_DriverIRQHandler
        BX      R0
        PUBWEAK CTIMER1_IRQHandler
        PUBWEAK CTIMER1_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
CTIMER1_IRQHandler
        LDR     R0, =CTIMER1_DriverIRQHandler
        BX      R0
        PUBWEAK SCT0_IRQHandler
        PUBWEAK SCT0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
SCT0_IRQHandler
        LDR     R0, =SCT0_DriverIRQHandler
        BX      R0
        PUBWEAK CTIMER3_IRQHandler
        PUBWEAK CTIMER3_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
CTIMER3_IRQHandler
        LDR     R0, =CTIMER3_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM0_IRQHandler
        PUBWEAK FLEXCOMM0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM0_IRQHandler
        LDR     R0, =FLEXCOMM0_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM1_IRQHandler
        PUBWEAK FLEXCOMM1_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM1_IRQHandler
        LDR     R0, =FLEXCOMM1_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM2_IRQHandler
        PUBWEAK FLEXCOMM2_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM2_IRQHandler
        LDR     R0, =FLEXCOMM2_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM3_IRQHandler
        PUBWEAK FLEXCOMM3_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM3_IRQHandler
        LDR     R0, =FLEXCOMM3_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM4_IRQHandler
        PUBWEAK FLEXCOMM4_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM4_IRQHandler
        LDR     R0, =FLEXCOMM4_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM5_IRQHandler
        PUBWEAK FLEXCOMM5_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM5_IRQHandler
        LDR     R0, =FLEXCOMM5_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM6_IRQHandler
        PUBWEAK FLEXCOMM6_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM6_IRQHandler
        LDR     R0, =FLEXCOMM6_DriverIRQHandler
        BX      R0
        PUBWEAK FLEXCOMM7_IRQHandler
        PUBWEAK FLEXCOMM7_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
FLEXCOMM7_IRQHandler
        LDR     R0, =FLEXCOMM7_DriverIRQHandler
        BX      R0
        PUBWEAK ADC0_SEQA_IRQHandler
        PUBWEAK ADC0_SEQA_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
ADC0_SEQA_IRQHandler
        LDR     R0, =ADC0_SEQA_DriverIRQHandler
        BX      R0
        PUBWEAK ADC0_SEQB_IRQHandler
        PUBWEAK ADC0_SEQB_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
ADC0_SEQB_IRQHandler
        LDR     R0, =ADC0_SEQB_DriverIRQHandler
        BX      R0
        PUBWEAK ADC0_THCMP_IRQHandler
        PUBWEAK ADC0_THCMP_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
ADC0_THCMP_IRQHandler
        LDR     R0, =ADC0_THCMP_DriverIRQHandler
        BX      R0
        PUBWEAK Reserved41_IRQHandler
        PUBWEAK Reserved41_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
Reserved41_IRQHandler
        LDR     R0, =Reserved41_DriverIRQHandler
        BX      R0
        PUBWEAK Reserved42_IRQHandler
        PUBWEAK Reserved42_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
Reserved42_IRQHandler
        LDR     R0, =Reserved42_DriverIRQHandler
        BX      R0
        PUBWEAK USB0_NEEDCLK_IRQHandler
        PUBWEAK USB0_NEEDCLK_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
USB0_NEEDCLK_IRQHandler
        LDR     R0, =USB0_NEEDCLK_DriverIRQHandler
        BX      R0
        PUBWEAK USB0_IRQHandler
        PUBWEAK USB0_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
USB0_IRQHandler
        LDR     R0, =USB0_DriverIRQHandler
        BX      R0
        PUBWEAK RTC_IRQHandler
        PUBWEAK RTC_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
RTC_IRQHandler
        LDR     R0, =RTC_DriverIRQHandler
        BX      R0
        PUBWEAK Reserved46_IRQHandler
        PUBWEAK Reserved46_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
Reserved46_IRQHandler
        LDR     R0, =Reserved46_DriverIRQHandler
        BX      R0
        PUBWEAK Reserved47_IRQHandler
        PUBWEAK Reserved47_DriverIRQHandler
        SECTION .text:CODE:REORDER:NOROOT(2)
Reserved47_IRQHandler
        LDR     R0, =Reserved47_DriverIRQHandler
        BX      R0
WDT_BOD_DriverIRQHandler
DMA0_DriverIRQHandler
GINT0_DriverIRQHandler
GINT1_DriverIRQHandler
PIN_INT0_DriverIRQHandler
PIN_INT1_DriverIRQHandler
PIN_INT2_DriverIRQHandler
PIN_INT3_DriverIRQHandler
UTICK0_DriverIRQHandler
MRT0_DriverIRQHandler
CTIMER0_DriverIRQHandler
CTIMER1_DriverIRQHandler
SCT0_DriverIRQHandler
CTIMER3_DriverIRQHandler
FLEXCOMM0_DriverIRQHandler
FLEXCOMM1_DriverIRQHandler
FLEXCOMM2_DriverIRQHandler
FLEXCOMM3_DriverIRQHandler
FLEXCOMM4_DriverIRQHandler
FLEXCOMM5_DriverIRQHandler
FLEXCOMM6_DriverIRQHandler
FLEXCOMM7_DriverIRQHandler
ADC0_SEQA_DriverIRQHandler
ADC0_SEQB_DriverIRQHandler
ADC0_THCMP_DriverIRQHandler
Reserved41_DriverIRQHandler
Reserved42_DriverIRQHandler
USB0_NEEDCLK_DriverIRQHandler
USB0_DriverIRQHandler
RTC_DriverIRQHandler
Reserved46_DriverIRQHandler
Reserved47_DriverIRQHandler
DefaultISR
        B .

        END
