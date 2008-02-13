;******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
;* File Name          : 91x_vect.s
;* Author             : MCD Application Team
;* Date First Issued  :  05/18/2006 : Version 1.0
;* Description        : This File used to initialize the exception and IRQ
;*                      vectors, and to enter/return to/from exceptions
;*                      handlers.
;*******************************************************************************
* History:
* 05/22/2007 : Version 1.2
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
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

    SECTION .intvec:CODE:ROOT(2)		
    CODE32


VectorAddress          EQU    0xFFFFF030  ; VIC Vector address register address.
VectorAddressDaisy     EQU    0xFC000030  ; Daisy VIC Vector address register
I_Bit                  EQU    0x80 ; when I bit is set, IRQ is disabled
F_Bit                  EQU    0x40 ; when F bit is set, FIQ is disabled




;*******************************************************************************
;              Import  the __iar_program_start address from 91x_init.s
;*******************************************************************************

       IMPORT  __iar_program_start

;*******************************************************************************
;                      Import exception handlers
;*******************************************************************************

        IMPORT  Undefined_Handler
        IMPORT  vPortYieldProcessor		; FreeRTOS SWI handler
        IMPORT  Prefetch_Handler
        IMPORT  Abort_Handler
        IMPORT  FIQ_Handler


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
        LDR     PC, IRQ_Addr

;*******************************************************************************
;* Function Name  : FIQHandler
;* Description    : This function is called when FIQ exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
FIQHandler
       SUB    lr,lr,#4        ; Update the link register.
       STMFD  sp!,{r0-r7,lr}  ; Save The workspace plus the current return
                             ; address lr_fiq into the FIQ stack.
       ldr r0,=FIQ_Handler
       ldr lr,=FIQ_Handler_end
       bx r0                 ;Branch to FIQ_Handler.
FIQ_Handler_end:

      LDMFD   sp!,{r0-r7,pc}^; Return to the instruction following...
                              ; ...the exception interrupt.


;*******************************************************************************
;               Exception handlers address table
;*******************************************************************************

Reset_Addr      DCD     __iar_program_start
Undefined_Addr  DCD     UndefinedHandler
SWI_Addr        DCD     vPortYieldProcessor
Prefetch_Addr   DCD     PrefetchAbortHandler
Abort_Addr      DCD     DataAbortHandler
                DCD     0               ; Reserved vector
IRQ_Addr        DCD     IRQHandler


;*******************************************************************************
;                                  MACRO
;*******************************************************************************
;*******************************************************************************
;* Macro Name     : SaveContext
;* Description    : This macro is used to save the context before entering
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
;* Description    : This macro is used to restore the context to return from
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
;                         Exception Handlers
;*******************************************************************************


;*******************************************************************************
;* Function Name  : UndefinedHandler
;* Description    : This function is called when undefined instruction
;                   exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************

UndefinedHandler
        SaveContext r0,r12    ; Save the workspace plus the current
                              ; return address lr_ und and spsr_und.

       ldr r0,=Undefined_Handler
       ldr lr,=Undefined_Handler_end
       bx r0                 ; Branch to Undefined_Handler.

Undefined_Handler_end:
        RestoreContext r0,r12 ; Return to the instruction following...
                              ; ...the undefined instruction.

;*******************************************************************************
;* Function Name  : PrefetchAbortHandler
;* Description    : This function is called when Prefetch Abort
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
;* Function Name  : IRQHandler
;* Description    : This function is called when IRQ exception is entered.
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
;******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****
