#include "FreeRTOSConfig.h"
;******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
;* File Name          : 71x_vect.s
;* Author             : MCD Application Team
;* Date First Issued  : 16/05/2003
;* Description        : This file used to initialize the exception and IRQ
;*                      vectors, and to enter/return to/from exceptions handlers.
;*******************************************************************************
;* History:
;*  13/01/2006 : V3.1
;*  24/05/2005 : V3.0
;*  30/11/2004 : V2.0
;*  14/07/2004 : V1.3
;*  01/01/2004 : V1.2
;*******************************************************************************
; THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
; CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
; AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
; OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
; OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
; CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;*******************************************************************************/

            	MODULE	?RESET
		SECTION	.intvec:CODE(2)				
		CODE32	

EIC_base_addr        EQU    0xFFFFF800; EIC base address.
CICR_off_addr        EQU    0x04      ; Current Interrupt Channel Register.
IVR_off_addr         EQU    0x18      ; Interrupt Vector Register.
IPR_off_addr         EQU    0x40      ; Interrupt Pending Register.


;*******************************************************************************
;              Import  the __iar_program_start address from 71x_init.s
;*******************************************************************************

        IMPORT  __iar_program_start

;*******************************************************************************
;                      Import exception handlers
;*******************************************************************************

        IMPORT  Undefined_Handler
        IMPORT  Prefetch_Handler
        IMPORT  Abort_Handler
        IMPORT  FIQ_Handler

;*******************************************************************************
;                   Import IRQ handlers from 71x_it.c
;*******************************************************************************

        IMPORT  Default_Handler
		IMPORT 	vPortYieldProcessor
		IMPORT	vSerialISREntry
		IMPORT	vPortPreemptiveTickISR
		IMPORT	vPortNonPreemptiveTick

;*******************************************************************************
;            Export Peripherals IRQ handlers table address
;*******************************************************************************

        EXPORT  T0TIMI_Addr

;*******************************************************************************
;                        Exception vectors
;*******************************************************************************
IVR_ADDR		 DEFINE    0xFFFFF818

		LDR     PC, Reset_Addr
        LDR     PC, Undefined_Addr
        LDR     PC, SWI_Addr
        LDR     PC, Prefetch_Addr
        LDR     PC, Abort_Addr
        NOP                             ; Reserved vector
        LDR     PC, =IVR_ADDR
        LDR     PC, FIQ_Addr

;*******************************************************************************
;               Exception handlers address table
;*******************************************************************************

Reset_Addr      DCD     __iar_program_start
Undefined_Addr  DCD     UndefinedHandler
SWI_Addr        DCD     vPortYieldProcessor
Prefetch_Addr   DCD     PrefetchAbortHandler
Abort_Addr      DCD     DataAbortHandler
                DCD     0               ; Reserved vector
IRQ_Addr        DCD     0			    ; Direct vectors are used.  See the STR75x demo for an alternative implementation
FIQ_Addr        DCD     FIQHandler

;*******************************************************************************
;              Peripherals IRQ handlers address table
;*******************************************************************************

T0TIMI_Addr     DCD  Default_Handler
FLASH_Addr      DCD  Default_Handler
RCCU_Addr       DCD  Default_Handler
RTC_Addr        DCD  Default_Handler
#if configUSE_PREEMPTION == 0
WDG_Addr        DCD  vPortNonPreemptiveTick	; Tick ISR if the cooperative scheduler is used.
#else
WDG_Addr		DCD  vPortPreemptiveTickISR	; Tick ISR if the preemptive scheduler is used.
#endif
XTI_Addr        DCD  Default_Handler
USBHP_Addr      DCD  Default_Handler
I2C0ITERR_Addr  DCD  Default_Handler
I2C1ITERR_ADDR  DCD  Default_Handler
UART0_Addr      DCD  vSerialISREntry
UART1_Addr      DCD  Default_Handler
UART2_ADDR      DCD  Default_Handler
UART3_ADDR      DCD  Default_Handler
BSPI0_ADDR      DCD  Default_Handler
BSPI1_Addr      DCD  Default_Handler
I2C0_Addr       DCD  Default_Handler
I2C1_Addr       DCD  Default_Handler
CAN_Addr        DCD  Default_Handler
ADC12_Addr      DCD  Default_Handler
T1TIMI_Addr     DCD  Default_Handler
T2TIMI_Addr     DCD  Default_Handler
T3TIMI_Addr     DCD  Default_Handler
                DCD  0                  ; reserved
                DCD  0                  ; reserved
                DCD  0                  ; reserved
HDLC_Addr       DCD  Default_Handler
USBLP_Addr      DCD  Default_Handler
                DCD  0                  ; reserved
                DCD  0                  ; reserved
T0TOI_Addr      DCD  Default_Handler
T0OC1_Addr      DCD  Default_Handler
T0OC2_Addr      DCD  Default_Handler


;*******************************************************************************
;                         Exception Handlers
;*******************************************************************************

;*******************************************************************************
;* Macro Name     : SaveContext
;* Description    : This macro used to save the context before entering
;                   an exception handler.
;* Input          : The range of registers to store.
;* Output         : none
;*******************************************************************************

SaveContext MACRO reg1,reg2

        STMFD  sp!,{reg1-reg2,lr} ; Save The workspace plus the current return
                              ; address lr_ mode into the stack.
        MRS    r1,spsr        ; Save the spsr_mode into r1.
        STMFD  sp!,{r1}       ; Save spsr.
        ENDM

;*******************************************************************************
;* Macro Name     : RestoreContext
;* Description    : This macro used to restore the context to return from
;                   an exception handler and continue the program execution.
;* Input          : The range of registers to restore.
;* Output         : none
;*******************************************************************************

RestoreContext MACRO reg1,reg2

        LDMFD   sp!,{r1}        ; Restore the saved spsr_mode into r1.
        MSR     spsr_cxsf,r1    ; Restore spsr_mode.
        LDMFD   sp!,{reg1-reg2,pc}^; Return to the instruction following...
                                ; ...the exception interrupt.
        ENDM

;*******************************************************************************
;* Function Name  : UndefinedHandler
;* Description    : This function called when undefined instruction
;                   exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
UndefinedHandler
        SaveContext r0,r12           ; Save the workspace plus the current
                                     ; return address lr_ und and spsr_und.
        ldr r0,=Undefined_Handler
        ldr lr,=Undefined_Handler_end
        bx r0                        ; Branch to Undefined_Handler
Undefined_Handler_end:
        RestoreContext r0,r12        ; Return to the instruction following...
                                     ; ...the undefined instruction.


;*******************************************************************************
;* Function Name  : PrefetchAbortHandler
;* Description    : This function called when Prefetch Abort
;                   exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************

PrefetchAbortHandler
        SUB    lr,lr,#4       ; Update the link register.
        SaveContext r0,r12    ; Save the workspace plus the current
                              ; return address lr_abt and spsr_abt.
        ldr r0,=Prefetch_Handler
        ldr lr,=Prefetch_Handler_end

        bx r0                 ; Branch to Prefetch_Handler.
Prefetch_Handler_end:
        RestoreContext r0,r12 ; Return to the instruction following that...
                              ; ...has generated the prefetch abort exception.

;*******************************************************************************
;* Function Name  : DataAbortHandler
;* Description    : This function is called when Data Abort
;                   exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************

DataAbortHandler
        SUB    lr,lr,#8       ; Update the link register.
        SaveContext r0,r12    ; Save the workspace plus the current
                              ; return address lr_ abt and spsr_abt.
        ldr r0,=Abort_Handler
        ldr lr,=Abort_Handler_end

        bx r0                 ; Branch to Abort_Handler.
Abort_Handler_end:
        RestoreContext r0,r12 ; Return to the instruction following that...
                              ; ...has generated the data abort exception.

;*******************************************************************************
;* Function Name  : FIQHandler
;* Description    : This function is called when FIQ
;                   exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************

FIQHandler
        SUB    lr,lr,#4       ; Update the link register.
        SaveContext r0,r7     ; Save the workspace plus the current
                              ; return address lr_ fiq and spsr_fiq.
        ldr r0,=FIQ_Handler
        ldr lr,=FIQ_Handler_end

        bx r0                 ; Branch to FIQ_Handler.
FIQ_Handler_end:
        RestoreContext r0,r7  ; Restore the context and return to the...
                              ; ...program execution.


		
		LTORG

  END
;******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****