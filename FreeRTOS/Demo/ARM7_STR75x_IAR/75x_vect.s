;******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
;* File Name          : 75x_vect.c
;* Author             : MCD Application Team
;* Date First Issued  : 03/10/2006
;* Description        : This file used to initialize the exception and IRQ
;*                      vectors, and to enter/return to/from exceptions handlers.
;*******************************************************************************
; History:
; 07/17/2006 : V1.0
; 03/10/2006 : V0.1
;*******************************************************************************
;* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
;* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
;* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
;* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
;* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
;* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;*******************************************************************************

#include "FreeRTOSConfig.h"
#include "ISR_Support.h"


                PROGRAM	?RESET
		SECTION	.intvec:CODE(2)			
		CODE32

EIC_base_addr         EQU    0xFFFFF800 ; EIC base address
CICR_off_addr         EQU    0x04       ; Current Interrupt Channel Register
IVR_off_addr          EQU    0x18       ; Interrupt Vector Register
IPR_off_addr          EQU    0x40       ; Interrupt Pending Register


;*******************************************************************************
;              Import  the __program_start address from 75x_init.s
;*******************************************************************************

        IMPORT  __iar_program_start



;*******************************************************************************
;                      Import exception handlers
;*******************************************************************************

        IMPORT  Undefined_Handler
        IMPORT  SWI_Handler
        IMPORT  Prefetch_Handler
        IMPORT  Abort_Handler
        IMPORT  FIQ_Handler

;*******************************************************************************
;                   Import IRQ handlers from 75x_it.c
;*******************************************************************************

        IMPORT WAKUP_IRQHandler
        IMPORT TIM2_OC2_IRQHandler
        IMPORT TIM2_OC1_IRQHandler
        IMPORT TIM2_IC12_IRQHandler
        IMPORT TIM2_UP_IRQHandler
        IMPORT TIM1_OC2_IRQHandler
        IMPORT TIM1_OC1_IRQHandler
        IMPORT TIM1_IC12_IRQHandler
        IMPORT TIM1_UP_IRQHandler
        IMPORT TIM0_OC2_IRQHandler
        IMPORT TIM0_OC1_IRQHandler
        IMPORT TIM0_IC12_IRQHandler
        IMPORT TIM0_UP_IRQHandler
        IMPORT PWM_OC123_IRQHandler
        IMPORT PWM_EM_IRQHandler
        IMPORT PWM_UP_IRQHandler
        IMPORT I2C_IRQHandler
        IMPORT SSP1_IRQHandler
        IMPORT SSP0_IRQHandler
        IMPORT UART2_IRQHandler
        IMPORT UART1_IRQHandler
        IMPORT vSerialISR
        IMPORT CAN_IRQHandler
        IMPORT USB_LP_IRQHandler
        IMPORT USB_HP_IRQHandler
        IMPORT ADC_IRQHandler
        IMPORT DMA_IRQHandler
        IMPORT EXTIT_IRQHandler
        IMPORT MRCC_IRQHandler
        IMPORT FLASHSMI_IRQHandler
        IMPORT RTC_IRQHandler
        IMPORT TB_IRQHandler
		IMPORT vPortPreemptiveTick
		IMPORT vPortYieldProcessor
		IMPORT UART0_IRQHandler

;*******************************************************************************
;            Export Peripherals IRQ handlers table address
;*******************************************************************************

        EXPORT  WAKUP_Addr

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
IRQ_Addr        DCD     IRQHandler
FIQ_Addr        DCD     FIQHandler

;*******************************************************************************
;              Peripherals IRQ handlers address table
;*******************************************************************************

WAKUP_Addr         DCD	WAKUPIRQHandler
TIM2_OC2_Addr      DCD	TIM2_OC2IRQHandler
TIM2_OC1_Addr      DCD	TIM2_OC1IRQHandler
TIM2_IC12_Addr     DCD	TIM2_IC12IRQHandler
TIM2_UP_Addr       DCD	TIM2_UPIRQHandler
TIM1_OC2_Addr      DCD	TIM1_OC2IRQHandler
TIM1_OC1_Addr      DCD	TIM1_OC1IRQHandler
TIM1_IC12_Addr     DCD	TIM1_IC12IRQHandler
TIM1_UP_Addr       DCD	TIM1_UPIRQHandler
TIM0_OC2_Addr      DCD	TIM0_OC2IRQHandler
TIM0_OC1_Addr      DCD	TIM0_OC1IRQHandler
TIM0_IC12_Addr     DCD	TIM0_IC12IRQHandler
TIM0_UP_Addr       DCD	TIM0_UPIRQHandler
PWM_OC123_Addr     DCD	PWM_OC123IRQHandler
PWM_EM_Addr        DCD	PWM_EMIRQHandler
PWM_UP_Addr        DCD	PWM_UPIRQHandler
I2C_Addr           DCD	I2CIRQHandler
SSP1_Addr          DCD	SSP1IRQHandler
SSP0_Addr          DCD	SSP0IRQHandler
UART2_Addr         DCD	UART2IRQHandler
UART1_Addr         DCD	UART1IRQHandler
UART0_Addr         DCD	vSerialISR
CAN_Addr           DCD	CANIRQHandler
USB_LP_Addr        DCD	USB_LPIRQHandler
USB_HP_Addr        DCD	USB_HPIRQHandler
ADC_Addr           DCD	ADCIRQHandler
DMA_Addr           DCD	DMAIRQHandler
EXTIT_Addr         DCD	EXTITIRQHandler
MRCC_Addr          DCD	MRCCIRQHandler
FLASHSMI_Addr      DCD	FLASHSMIIRQHandler
RTC_Addr           DCD	RTCIRQHandler
TB_Addr            DCD	vPortPreemptiveTick

;*******************************************************************************
;                         Exception Handlers
;*******************************************************************************

;*******************************************************************************
;* Macro Name     : SaveContext
;* Description    : This macro used to save the context before entering
;*                  an exception handler.
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
;*                  an exception handler and continue the program execution.
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
;* Description    : This function called when undefined instruction exception
;*                  is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
UndefinedHandler
        SaveContext r0,r12         ; Save the workspace plus the current
                                   ; return address lr_ und and spsr_und.
        ldr r0,=Undefined_Handler
        ldr lr,=Undefined_Handler_end
        bx r0                       ;Branch to Undefined_Handler
Undefined_Handler_end:
        RestoreContext r0,r12      ; Return to the instruction following...
                                    ; ...the undefined instruction.

;*******************************************************************************
;* Function Name  : SWIHandler
;* Description    : This function called when SWI instruction executed.
;* Input          : none
;* Output         : none
;*******************************************************************************
SWIHandler
        SaveContext r0,r12         ; Save the workspace plus the current
                                   ; return address lr_ svc and spsr_svc.
        ldr r0,= SWI_Handler
        ldr lr,= SWI_Handler_end
        bx r0                       ;Branch to  SWI_Handler
SWI_Handler_end:
        RestoreContext r0,r12     ; Return to the instruction following...
                                  ; ...the SWI instruction.

;*******************************************************************************
;* Function Name  : IRQHandler
;* Description    : This function called when IRQ exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
IRQHandler
	portSAVE_CONTEXT					; Save the context of the current task.

	LDR    r0, =EIC_base_addr
	LDR    r1, =IVR_off_addr
	LDR    lr, =ReturnAddress			; Load the return address.	
	ADD    pc,r0,r1						; Branch to the IRQ handler.
ReturnAddress
	LDR    r0, =EIC_base_addr
	LDR    r2, [r0, #CICR_off_addr]		; Get the IRQ channel number
	MOV    r3,#1
	MOV    r3,r3,LSL r2
	STR    r3,[r0, #IPR_off_addr]		; Clear the corresponding IPR bit.
	
	portRESTORE_CONTEXT					; Restore the context of the selected task.

	
;*******************************************************************************
;* Function Name  : PrefetchAbortHandler
;* Description    : This function called when Prefetch Abort exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
PrefetchAbortHandler
        SUB    lr,lr,#4        ; Update the link register.
        SaveContext r0,r7      ; Save the workspace plus the current
                               ; return address lr_abt and spsr_abt.
        ldr r0,= Prefetch_Handler
        ldr lr,= Prefetch_Handler_end
        bx r0                       ;Branch to  Prefetch_Handler
Prefetch_Handler_end:
        RestoreContext r0,r7   ; Return to the instruction following that...
                               ; ...has generated the prefetch abort exception.

;*******************************************************************************
;* Function Name  : DataAbortHandler
;* Description    : This function is called when Data Abort exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
DataAbortHandler
        SUB    lr,lr,#8            ; Update the link register.
        SaveContext r0,r12         ; Save the workspace plus the current
                                   ; return address lr_ abt and spsr_abt.
        ldr r0,= Abort_Handler
        ldr lr,= Abort_Handler_end
        bx r0                       ;Branch to  Abort_Handler
Abort_Handler_end:
        RestoreContext r0,r12       ; Return to the instruction following that...
                                    ; ...has generated the data abort exception.

;*******************************************************************************
;* Function Name  : FIQHandler
;* Description    : This function is called when FIQ exception is entered.
;* Input          : none
;* Output         : none
;*******************************************************************************
FIQHandler
        SUB    lr,lr,#4            ; Update the link register.
        SaveContext r0,r7          ; Save the workspace plus the current
                                   ; return address lr_ fiq and spsr_fiq.
        ldr r0,= FIQ_Handler
        ldr lr,= FIQ_Handler_end
        bx r0                       ;Branch to  FIQ_Handler
FIQ_Handler_end:
        RestoreContext r0,r7        ; Restore the context and return to the...
                                    ; ...program execution.

;*******************************************************************************
;* Macro Name     : IRQ_to_SYS
;* Description    : This macro used to switch form IRQ mode to SYS mode.
;* Input          : none.
;* Output         : none
;*******************************************************************************
IRQ_to_SYS MACRO
        MSR    cpsr_c,#0x1F
        STMFD  sp!,{lr}
       ENDM

;*******************************************************************************
;* Macro Name     : SYS_to_IRQ
;* Description    : This macro used to switch from SYS mode to IRQ mode.
;* Input          : none.
;* Output         : none
;*******************************************************************************
SYS_to_IRQ MACRO
        LDMFD  sp!,{lr}
        MSR    cpsr_c,#0xD2
        MOV    pc,lr
       ENDM

;*******************************************************************************
;* Function Name  : WAKUPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the WAKUP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the WAKUP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
WAKUPIRQHandler
        IRQ_to_SYS
        ldr r0,=WAKUP_IRQHandler
        ldr lr,=WAKUP_IRQHandler_end
        bx r0
WAKUP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM2_OC2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_OC2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM2_OC2_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM2_OC2IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM2_OC2_IRQHandler
        ldr lr,=TIM2_OC2_IRQHandler_end
        bx r0
TIM2_OC2_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM2_OC1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_OC1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM2_OC1_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM2_OC1IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM2_OC1_IRQHandler
        ldr lr,=TIM2_OC1_IRQHandler_end
        bx r0
TIM2_OC1_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM2_IC12IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_IC12_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM2_IC12_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM2_IC12IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM2_IC12_IRQHandler
        ldr lr,=TIM2_IC12_IRQHandler_end
        bx r0
TIM2_IC12_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM2_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM2_UP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM2_UPIRQHandler
        IRQ_to_SYS
        ldr r0,=TIM2_UP_IRQHandler
        ldr lr,=TIM2_UP_IRQHandler_end
        bx r0
TIM2_UP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM1_OC2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_OC2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM1_OC2_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM1_OC2IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM1_OC2_IRQHandler
        ldr lr,=TIM1_OC2_IRQHandler_end
        bx r0
TIM1_OC2_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM1_OC1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_OC1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM1_OC1_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM1_OC1IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM1_OC1_IRQHandler
        ldr lr,=TIM1_OC1_IRQHandler_end
        bx r0
TIM1_OC1_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM1_IC12IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_IC12_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM1_IC12_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM1_IC12IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM1_IC12_IRQHandler
        ldr lr,=TIM1_IC12_IRQHandler_end
        bx r0
TIM1_IC12_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM1_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM1_UP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM1_UPIRQHandler
        IRQ_to_SYS
        ldr r0,=TIM1_UP_IRQHandler
        ldr lr,=TIM1_UP_IRQHandler_end
        bx r0
TIM1_UP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM0_OC2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_OC2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM0_OC2_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM0_OC2IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM0_OC2_IRQHandler
        ldr lr,=TIM0_OC2_IRQHandler_end
        bx r0
TIM0_OC2_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM0_OC1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_OC1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM0_OC1_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM0_OC1IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM0_OC1_IRQHandler
        ldr lr,=TIM0_OC1_IRQHandler_end
        bx r0
TIM0_OC1_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM0_IC12IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_IC12_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM0_IC12_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM0_IC12IRQHandler
        IRQ_to_SYS
        ldr r0,=TIM0_IC12_IRQHandler
        ldr lr,=TIM0_IC12_IRQHandler_end
        bx r0
TIM0_IC12_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TIM0_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TIM0_UP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TIM0_UPIRQHandler
        IRQ_to_SYS
        ldr r0,=TIM0_UP_IRQHandler
        ldr lr,=TIM0_UP_IRQHandler_end
        bx r0
TIM0_UP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : PWM_OC123IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the PWM_OC123_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the PWM_OC123_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
PWM_OC123IRQHandler
        IRQ_to_SYS
        ldr r0,=PWM_OC123_IRQHandler
        ldr lr,=PWM_OC123_IRQHandler_end
        bx r0
PWM_OC123_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : PWM_EMIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the PWM_EM_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the PWM_EM_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
PWM_EMIRQHandler
        IRQ_to_SYS
        ldr r0,=PWM_EM_IRQHandler
        ldr lr,=PWM_EM_IRQHandler_end
        bx r0
PWM_EM_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : PWM_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the PWM_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the PWM_UP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
PWM_UPIRQHandler
        IRQ_to_SYS
        ldr r0,=PWM_UP_IRQHandler
        ldr lr,=PWM_UP_IRQHandler_end
        bx r0
PWM_UP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : I2CIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the I2C_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the I2C_IRQHandler function
;*                  termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
I2CIRQHandler
        IRQ_to_SYS
        ldr r0,=I2C_IRQHandler
        ldr lr,=I2C_IRQHandler_end
        bx r0
I2C_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : SSP1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the SSP1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the SSP1_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
SSP1IRQHandler
        IRQ_to_SYS
        ldr r0,=SSP1_IRQHandler
        ldr lr,=SSP1_IRQHandler_end
        bx r0
SSP1_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : SSP0IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the SSP0_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the SSP0_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
SSP0IRQHandler
        IRQ_to_SYS
        ldr r0,=SSP0_IRQHandler
        ldr lr,=SSP0_IRQHandler_end
        bx r0
SSP0_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : UART2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the UART2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the UART2_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
UART2IRQHandler
        IRQ_to_SYS
        ldr r0,=UART2_IRQHandler
        ldr lr,=UART2_IRQHandler_end
        bx r0
UART2_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : UART1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the UART1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the UART1_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
UART1IRQHandler
        IRQ_to_SYS
        ldr r0,=UART1_IRQHandler
        ldr lr,=UART1_IRQHandler_end
        bx r0
UART1_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : UART0IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the UART0_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the UART0_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
UART0IRQHandler
        IRQ_to_SYS
        ldr r0,=UART0_IRQHandler
        ldr lr,=UART0_IRQHandler_end
        bx r0
UART0_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : CANIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the CAN_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the CAN_IRQHandler function
;*                  termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
CANIRQHandler
        IRQ_to_SYS
        ldr r0,=CAN_IRQHandler
        ldr lr,=CAN_IRQHandler_end
        bx r0
CAN_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : USB_LPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the USB_LP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the USB_LP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
USB_LPIRQHandler
        IRQ_to_SYS
        ldr r0,=USB_LP_IRQHandler
        ldr lr,=USB_LP_IRQHandler_end
        bx r0
USB_LP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : USB_HPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the USB_HP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the USB_HP_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
USB_HPIRQHandler
        IRQ_to_SYS
        ldr r0,=USB_HP_IRQHandler
        ldr lr,=USB_HP_IRQHandler_end
        bx r0
USB_HP_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : ADCIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the ADC_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the ADC_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
ADCIRQHandler
        IRQ_to_SYS
        ldr r0,=ADC_IRQHandler
        ldr lr,=ADC_IRQHandler_end
        bx r0
ADC_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : DMAIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the DMA_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the DMA_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
DMAIRQHandler
        IRQ_to_SYS
        ldr r0,=DMA_IRQHandler
        ldr lr,=DMA_IRQHandler_end
        bx r0
DMA_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : EXTITIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the EXTIT_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the EXTIT_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
EXTITIRQHandler
        IRQ_to_SYS
        ldr r0,=EXTIT_IRQHandler
        ldr lr,=EXTIT_IRQHandler_end
        bx r0
EXTIT_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : MRCCIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the MRCC_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the MRCC_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
MRCCIRQHandler
        IRQ_to_SYS
        ldr r0,=MRCC_IRQHandler
        ldr lr,=MRCC_IRQHandler_end
        bx r0
MRCC_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : FLASHSMIIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the FLASHSMI_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the FLASHSMI_IRQHandler
;*                  function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
FLASHSMIIRQHandler
        IRQ_to_SYS
        ldr r0,=FLASHSMI_IRQHandler
        ldr lr,=FLASHSMI_IRQHandler_end
        bx r0
FLASHSMI_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : RTCIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the RTC_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the RTC_IRQHandler function
;*                  termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
RTCIRQHandler
        IRQ_to_SYS
        ldr r0,=RTC_IRQHandler
        ldr lr,=RTC_IRQHandler_end
        bx r0
RTC_IRQHandler_end:
        SYS_to_IRQ

;*******************************************************************************
;* Function Name  : TBIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TB_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the TB_IRQHandler function
;*                  termination.
;* Input          : none
;* Output         : none
;*******************************************************************************
TBIRQHandler
        IRQ_to_SYS
        ldr r0,=TB_IRQHandler
        ldr lr,=TB_IRQHandler_end
        bx r0
TB_IRQHandler_end:
        SYS_to_IRQ

       LTORG

        END
;******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE*****











