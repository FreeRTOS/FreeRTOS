;******************** (C) COPYRIGHT 2005 STMicroelectronics ********************
;* File Name          : 91x_vect.s
;* Author             : MCD Application Team
;* Date First Issued  : 10/25/2005 :  Beta Version V0.1
;* Description        : This File used to initialize the exception and IRQ
;*                      vectors, and to enter/return to/from exceptions
;*                      handlers.
;*******************************************************************************
; History:
; 10/25/2005 :  Beta Version V0.1
;*******************************************************************************
; THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
; CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
; A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
; OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
; OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
; CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;******************************************************************************/

#include "FreeRTOSConfig.h"
#include "ISR_Support.h"

    MODULE	?RESET
	COMMON	INTVEC:CODE(2)			
	CODE32
    EXPORT LINK

VectorAddress			EQU    0xFFFFF030  ; VIC Vector address register address.
VectorAddressDaisy		EQU    0xFC000030  ; Daisy VIC Vector address register
                                          ; address.
LINK					EQU    0x0

I_Bit					EQU    0x80 ; when I bit is set, IRQ is disabled
F_Bit					EQU    0x40 ; when F bit is set, FIQ is disabled

;*******************************************************************************
;                                  MACRO
;*******************************************************************************

;*******************************************************************************
;            Import  the __program_start address from 91x_init.s
;*******************************************************************************

       	IMPORT  __program_start

;*******************************************************************************
;                      Import exception handlers
;*******************************************************************************

		IMPORT  vPortYieldProcessor		; FreeRTOS SWI handler

;*******************************************************************************
;            Export Peripherals IRQ handlers table address
;*******************************************************************************

;*******************************************************************************
;                        Exception vectors
;*******************************************************************************

        LDR     PC, Reset_Addr
        LDR     PC, Undefined_Addr
        LDR     PC, SWI_Addr
        LDR     PC, Prefetch_Addr
        LDR     PC, Abort_Addr
        NOP                             ; Reserved vector
        LDR    	PC, IRQ_Addr
        LDR     PC, FIQ_Addr

;*******************************************************************************
;               Exception handlers address table
;*******************************************************************************

Reset_Addr      DCD     __program_start
Undefined_Addr  DCD     UndefinedHandler
SWI_Addr        DCD     vPortYieldProcessor
Prefetch_Addr   DCD     PrefetchAbortHandler
Abort_Addr      DCD     DataAbortHandler
                DCD     0               ; Reserved vector
IRQ_Addr        DCD     IRQHandler
FIQ_Addr        DCD     FIQHandler


;*******************************************************************************
;                         Exception Handlers
;*******************************************************************************

; - NOTE -
; The IRQ and SWI handlers are the only managed exception.

UndefinedHandler
		b	UndefinedHandler

PrefetchAbortHandler
		b	PrefetchAbortHandler

DataAbortHandler
		b	DataAbortHandler

FIQHandler
		b	FIQHandler

DefaultISR
		b	DefaultISR


;*******************************************************************************
;* Function Name  : IRQHandler
;* Description    : This function called when IRQ exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************

IRQHandler
	portSAVE_CONTEXT					; Save the context of the current task.

	LDR    r0, = VectorAddress
	LDR    r0, [r0]						; Read the routine address
	LDR    r1, = VectorAddressDaisy
	LDR    r1, [r1]
	MOV	   lr, pc
	bx	   r0
	LDR    r0, = VectorAddress			; Write to the VectorAddress to clear the
	STR    r0, [r0]						; respective interrupt in the internal interrupt
	LDR    r1, = VectorAddressDaisy		; Write to the VectorAddressDaisy to clear the
	STR    r1,[r1]						; respective interrupt in the internal interrupt
	
	portRESTORE_CONTEXT					; Restore the context of the selected task.

	
	LTORG
	
	END

;******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****
