/*
This is the default Startup for STR75x devices for the GNU toolchain

It has been designed by ST Microelectronics and modified by Raisonance
and FreeRTOS.org.

You can use it, modify it, distribute it freely but without any waranty.

*/
.extern main

	   

/*; Depending on Your Application, Disable or Enable the following Defines*/
  /*; --------------------------------------------------------------------------
  ;                      SMI Bank0 configuration
; ----------------------------------------------------------------------------*/
.set SMI_Bank0_EN, 0 /*; enable access the SMI Bank0 if 1*/

/*; ----------------------------------------------------------------------------
  ;                      Memory remapping
; ----------------------------------------------------------------------------*/
.set Remap_SRAM, 0   /* remap SRAM at address 0x00 if 1 */
 
/*  ; ----------------------------------------------------------------------------
  ;                      EIC initialization
  ; ----------------------------------------------------------------------------*/
.set EIC_INIT, 1     /*; Configure and Initialize EIC if 1*/


;/* the following are useful for initializing the .data section */
.extern _sidata ;/* start address for the initialization values of the .data section. defined in linker script */
.extern _sdata ;/* start address for the .data section. defined in linker script */
.extern _edata ;/* end address for the .data section. defined in linker script */

;/* the following are useful for initializing the .bss section */
.extern _sbss ;/* start address for the .bss section. defined in linker script */
.extern _ebss ;/* end address for the .bss section. defined in linker script */

;/* Standard definitions of Mode bits and Interrupt (I & F) flags in PSRs */
.set  Mode_USR, 0x10            ;/* User Mode */
.set  Mode_FIQ, 0x11            ;/* FIQ Mode */
.set  Mode_IRQ, 0x12            ;/* IRQ Mode */
.set  Mode_SVC, 0x13            ;/* Supervisor Mode */
.set  Mode_ABT, 0x17            ;/* Abort Mode */
.set  Mode_UNDEF, 0x1B          ;/* Undefined Mode */
.set  Mode_SYS, 0x1F            ;/* System Mode */

.equ  I_Bit, 0x80               ;/* when I bit is set, IRQ is disabled */
.equ  F_Bit, 0x40               ;/* when F bit is set, FIQ is disabled */

/*; --- System memory locations */

;/* init value for the stack pointer. defined in linker script */
.extern _estack

;/* Stack Sizes. The default values are in the linker script, but they can be overriden. */
.extern _UND_Stack_Init
.extern _SVC_Stack_Init
.extern _ABT_Stack_Init
.extern _FIQ_Stack_Init
.extern _IRQ_Stack_Init
.extern _USR_Stack_Init

.extern _UND_Stack_Size
.extern _SVC_Stack_Size
.extern _ABT_Stack_Size
.extern _FIQ_Stack_Size
.extern _IRQ_Stack_Size
.extern _USR_Stack_Size
.extern vTaskSwitchContext
.extern ulCriticalNesting

SVC_Stack           =     _SVC_Stack_Init /*_estack*/           /*; 32 byte SVC stack at*/
                                              /*; top of memory */
                                              
IRQ_Stack           =     _IRQ_Stack_Init /*SVC_Stack - 32*/     /*; followed by IRQ stack */
USR_Stack           =     _USR_Stack_Init /*IRQ_Stack-256*/    /*; followed by USR stack */
FIQ_Stack           =     _FIQ_Stack_Init /*USR_Stack-256*/    /*; followed by FIQ stack*/
ABT_Stack           =     _ABT_Stack_Init /*FIQ_Stack-64*/     /*; followed by ABT stack */
UNDEF_Stack         =     _UND_Stack_Init /*ABT_Stack-0*/     /*; followed by UNDEF stack */

/*; --- System memory locations*/

/*; MRCC Register*/
MRCC_PCLKEN_Addr    =    0x60000030  /*; Peripheral Clock Enable register base address*/

/*; CFG Register*/
CFG_GLCONF_Addr     =    0x60000010  /*; Global Configuration register base address*/
SRAM_mask           =    0x0002      /*; to remap RAM at 0x0*/

/*; GPIO Register*/
GPIOREMAP0R_Addr    =    0xFFFFE420
SMI_EN_Mask         =    0x00000001

/*; SMI Register*/
SMI_CR1_Addr        =    0x90000000

/*; --- Stack Addres for each ARM mode*/
/*; add FIQ_Stack, ABT_Stack, UNDEF_Stack here if you need them*/


/*; --- EIC Registers offsets*/
EIC_base_addr       =    0xFFFFF800         /*; EIC base address*/
ICR_off_addr        =    0x00               /*; Interrupt Control register offset*/
CICR_off_addr       =    0x04               /*; Current Interrupt Channel Register*/
CIPR_off_addr       =    0x08               /*; Current Interrupt Priority Register offset*/
IVR_off_addr        =    0x18               /*; Interrupt Vector Register offset*/
FIR_off_addr        =    0x1C               /*; Fast Interrupt Register offset*/
IER_off_addr        =    0x20               /*; Interrupt Enable Register offset*/
IPR_off_addr        =    0x40               /*; Interrupt Pending Bit Register offset*/
SIR0_off_addr       =    0x60               /*; Source Interrupt Register 0*/

/***************************************************************************************/


.globl _start
.globl _startup

.text
_startup:
_start:
        LDR     PC, Reset_Addr
        LDR     PC, Undefined_Addr
        LDR     PC, SWI_Addr
        LDR     PC, Prefetch_Addr
        LDR     PC, Abort_Addr
        NOP                          /*; Reserved vector*/
        LDR     PC, IRQ_Addr
        LDR     PC, FIQ_Addr





Reset_Addr      : .long     Reset_Handler
Undefined_Addr  : .long     UndefinedHandler
SWI_Addr        : .long     SWIHandler
Prefetch_Addr   : .long     PrefetchAbortHandler
Abort_Addr      : .long     DataAbortHandler
                  .long 0      /*; Reserved vector*/
IRQ_Addr        : .long     IRQHandler
FIQ_Addr        : .long     FIQHandler

.text
/*;*******************************************************************************
;              Peripherals IRQ handlers address table
;********************************************************************************/

/* execution goes there when an interrupt occurs and there is no associated ISR */
.globl __wrongvector
__wrongvector:
	ldr     PC, __wrongvector_Addr	
__wrongvector_Addr:
	.long 0

WAKUP_Addr         :.long	WAKUPIRQHandler
TIM2_OC2_Addr      :.long	TIM2_OC2IRQHandler
TIM2_OC1_Addr      :.long	TIM2_OC1IRQHandler
TIM2_IC12_Addr     :.long	TIM2_IC12IRQHandler
TIM2_UP_Addr       :.long	TIM2_UPIRQHandler
TIM1_OC2_Addr      :.long	TIM1_OC2IRQHandler
TIM1_OC1_Addr      :.long	TIM1_OC1IRQHandler
TIM1_IC12_Addr     :.long	TIM1_IC12IRQHandler
TIM1_UP_Addr       :.long	TIM1_UPIRQHandler
TIM0_OC2_Addr      :.long	TIM0_OC2IRQHandler
TIM0_OC1_Addr      :.long	TIM0_OC1IRQHandler
TIM0_IC12_Addr     :.long	TIM0_IC12IRQHandler
TIM0_UP_Addr       :.long	TIM0_UPIRQHandler
PWM_OC123_Addr     :.long	PWM_OC123IRQHandler
PWM_EM_Addr        :.long	PWM_EMIRQHandler
PWM_UP_Addr        :.long	PWM_UPIRQHandler
I2C_Addr           :.long	I2CIRQHandler
SSP1_Addr          :.long	SSP1IRQHandler
SSP0_Addr          :.long	SSP0IRQHandler
UART2_Addr         :.long	UART2IRQHandler
UART1_Addr         :.long	UART1IRQHandler
UART0_Addr         :.long	vSerialISR
CAN_Addr           :.long	CANIRQHandler
USB_LP_Addr        :.long	USB_LPIRQHandler
USB_HP_Addr        :.long	USB_HPIRQHandler
ADC_Addr           :.long	ADCIRQHandler
DMA_Addr           :.long	DMAIRQHandler
EXTIT_Addr         :.long	EXTITIRQHandler
MRCC_Addr          :.long	MRCCIRQHandler
FLASHSMI_Addr      :.long	FLASHSMIIRQHandler
RTC_Addr           :.long	RTCIRQHandler
TB_Addr            :.long	vPortTickISR

/*;*******************************************************************************
;                         Exception Handlers
;********************************************************************************/


/*;*******************************************************************************
;* FreeRTOS.org macros for saving and restoring a task context
;*******************************************************************************/

	.macro portSAVE_CONTEXT MACRO

	/* ; Push R0 as we are going to use the register. */
	STMDB	SP!, {R0}

	/* ; Set R0 to point to the task stack pointer. */
	STMDB	SP, {SP}^
	NOP
	SUB		SP, SP, #4
	LDMIA	SP!, {R0}

	/* ; Push the return address onto the stack. 	*/
	STMDB	R0!, {LR}

	/* ; Now we have saved LR we can use it instead of R0. 	*/
	MOV		LR, R0

	/* ; Pop R0 so we can save it onto the system mode stack. */
	LDMIA	SP!, {R0}

	/* ; Push all the system mode registers onto the task stack. */
	STMDB	LR, {R0-LR}^
	NOP
	SUB		LR, LR, #60

	/* ; Push the SPSR onto the task stack.  */
	MRS		R0, SPSR
	STMDB	LR!, {R0}

	LDR		R0, =ulCriticalNesting 
	LDR		R0, [R0]
	STMDB	LR!, {R0}

	/* ; Store the new top of stack for the task. 	*/
	LDR		R1, =pxCurrentTCB
	LDR		R0, [R1]
	STR		LR, [R0]

	.endm


	.macro portRESTORE_CONTEXT MACRO

	/* ; Set the LR to the task stack. 	*/
	LDR		R1, =pxCurrentTCB
	LDR		R0, [R1]
	LDR		LR, [R0]

	/* ; The critical nesting depth is the first item on the stack. 	
	; Load it into the ulCriticalNesting variable. 	*/
	LDR		R0, =ulCriticalNesting
	LDMFD	LR!, {R1}
	STR		R1, [R0]

	/* ; Get the SPSR from the stack. 	*/
	LDMFD	LR!, {R0}
	MSR		SPSR_cxsf, R0

	/* ; Restore all system mode registers for the task. */
	LDMFD	LR, {R0-R14}^
	NOP

	/* ; Restore the return address. */
	LDR		LR, [LR, #+60]

	/* ; And return - correcting the offset in the LR to obtain the 	
	; correct address. 	*/
	SUBS	PC, LR, #4
	
	.endm



/*;*******************************************************************************
;* Macro Name     : SaveContext
;* Description    : This macro used to save the context before entering
;                   an exception handler.
;* Input          : The range of registers to store.
;* Output         : none
;********************************************************************************/

       .macro SaveContext $r0,$r12
        STMFD  sp!,{r0-r12,lr} /*; Save The workspace plus the current return*/
                               /*; address lr_ mode into the stack.*/
        MRS    r1,spsr         /*; Save the spsr_mode into r1.*/
        STMFD  sp!,{r1}        /*; Save spsr.*/
        .endm

/*;*******************************************************************************
;* Macro Name     : RestoreContext
;* Description    : This macro used to restore the context to return from
;                   an exception handler and continue the program execution.
;* Input          : The range of registers to restore.
;* Output         : none
;********************************************************************************/

        .macro RestoreContext $r0,$r12
        LDMFD   sp!,{r1}        /*; Restore the saved spsr_mode into r1.*/
        MSR     spsr_cxsf,r1    /*; Restore spsr_mode.*/
        LDMFD   sp!,{r0-r12,pc}^/*; Return to the instruction following...*/
                                /*; ...the exception interrupt.*/
        .endm



/*;*******************************************************************************
;* Function Name  : UndefinedHandler
;* Description    : This function called when undefined instruction
;                   exception is entered.
;* Input          : none
;* Output         : none
;*********************************************************************************/

UndefinedHandler:
        SaveContext r0,r12    /*; Save the workspace plus the current*/
                              /*; return address lr_ und and spsr_und.*/
        BL      Undefined_Handler/*; Branch to Undefined_Handler*/
        RestoreContext r0,r12 /*; Return to the instruction following...*/
                              /*; ...the undefined instruction.*/

/*;*******************************************************************************
;* Function Name  : SWIHandler
;* Description    : This function called when SWI instruction executed.
;* Input          : none
;* Output         : none
;********************************************************************************/

SWIHandler:
		ADD	LR, LR, #4
        portSAVE_CONTEXT        
        LDR R0, =vTaskSwitchContext
        MOV LR, PC
        BX R0
        portRESTORE_CONTEXT 


/*;*******************************************************************************
;* Function Name  : IRQHandler
;* Description    : This function called when IRQ exception is entered.
;* Input          : none
;* Output         : none
;********************************************************************************/


IRQHandler:

	portSAVE_CONTEXT					/*; Save the context of the current task. */

	LDR    r0, =EIC_base_addr
	LDR    r1, =IVR_off_addr
	LDR    lr, =ReturnAddress			/*; Load the return address. */
	ADD    pc,r0,r1						/*; Branch to the IRQ handler. */
ReturnAddress:
	LDR    r0, =EIC_base_addr
	LDR    r2, [r0, #CICR_off_addr]		/*; Get the IRQ channel number. */
	MOV    r3,#1
	MOV    r3,r3,LSL r2
	STR    r3,[r0, #IPR_off_addr]		/*; Clear the corresponding IPR bit. */
	
	portRESTORE_CONTEXT					/*; Restore the context of the selected task. */

/*;*******************************************************************************
;* Function Name  : PrefetchAbortHandler
;* Description    : This function called when Prefetch Abort
;                   exception is entered.
;* Input          : none
;* Output         : none
;*********************************************************************************/

PrefetchAbortHandler:
		NOP
		B PrefetchAbortHandler

/*;*******************************************************************************
;* Function Name  : DataAbortHandler
;* Description    : This function is called when Data Abort
;                   exception is entered.
;* Input          : none
;* Output         : none
;********************************************************************************/

DataAbortHandler:
		NOP
		NOP
		B DataAbortHandler
                              /*; ...has generated the data abort exception.*/

/*;*******************************************************************************
;* Function Name  : FIQHandler
;* Description    : This function is called when FIQ
;*                  exception is entered.
;* Input          : none
;* Output         : none
;********************************************************************************/

FIQHandler:
        SUB    lr,lr,#4       /*; Update the link register.*/
        SaveContext r0,r7     /*; Save the workspace plus the current*/
                              /*; return address lr_ fiq and spsr_fiq.*/
        BL      FIQ_Handler   /*; Branch to FIQ_Handler.*/
        RestoreContext r0,r7  /*; Restore the context and return to the...*/
                              /*; ...program execution.*/

/*;*******************************************************************************
;* Macro Name     : IRQ_to_SYS
;* Description    : This macro used to switch form IRQ mode to SYS mode
;* Input          : none.
;* Output         : none
;*******************************************************************************/
       .macro IRQ_to_SYS

        MSR    cpsr_c,#0x1F
        STMFD  sp!,{lr}
       .endm
/*;*******************************************************************************
;* Macro Name     : SYS_to_IRQ
;* Description    : This macro used to switch from SYS mode to IRQ mode
;                   then to return to IRQHnadler routine.
;* Input          : none.
;* Output         : none.
;*******************************************************************************/
      .macro SYS_to_IRQ
       LDMFD  sp!,{lr}      /*; Restore the link register. */
        MSR    cpsr_c,#0xD2  /*; Switch to IRQ mode.*/
        MOV    pc,lr         /*; Return to IRQHandler routine to clear the*/
                             /*; pending bit.*/
       .endm

/*;*******************************************************************************
;* Function Name  : WAKUPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the WAKUP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  WAKUP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
WAKUPIRQHandler:
        IRQ_to_SYS
        BL     WAKUP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM2_OC2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM3_OC2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM2_OC2_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM2_OC2IRQHandler:
        IRQ_to_SYS
        BL     TIM2_OC2_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM2_OC1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_OC1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM2_OC1_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM2_OC1IRQHandler:
        IRQ_to_SYS
        BL     TIM2_OC1_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM2_IC12IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_IC12_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM2_IC12_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM2_IC12IRQHandler:
        IRQ_to_SYS
        BL     TIM2_IC12_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM2_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM2_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM3_UP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM2_UPIRQHandler:
        IRQ_to_SYS
        BL     TIM2_UP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM1_OC2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_OC2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM1_OC2_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM1_OC2IRQHandler:
        IRQ_to_SYS
        BL     TIM1_OC2_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM1_OC1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_OC1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM1_OC1_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM1_OC1IRQHandler:
        IRQ_to_SYS
        BL     TIM1_OC1_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM1_IC12IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_IC12_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM1_IC12_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM1_IC12IRQHandler:
        IRQ_to_SYS
        BL     TIM1_IC12_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM1_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM1_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM1_UP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM1_UPIRQHandler:
        IRQ_to_SYS
        BL     TIM1_UP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM0_OC2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_OC2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM0_OC2_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM0_OC2IRQHandler:
        IRQ_to_SYS
        BL     TIM0_OC2_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM0_OC1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_OC1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM0_OC1_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
TIM0_OC1IRQHandler:
        IRQ_to_SYS
        BL     TIM0_OC1_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM0_IC12IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_IC12_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM0_IC12_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
TIM0_IC12IRQHandler:
        IRQ_to_SYS
        BL     TIM0_IC12_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TIM0_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TIM0_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TIM0_UP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
TIM0_UPIRQHandler:
        IRQ_to_SYS
        BL     TIM0_UP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : PWM_OC123IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the PWM_OC123_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                    PWM_OC123_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
PWM_OC123IRQHandler:
        IRQ_to_SYS
        BL     PWM_OC123_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : PWM_EMIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the PWM_EM_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  PWM_EM_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
PWM_EMIRQHandler:
        IRQ_to_SYS
        BL     PWM_EM_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : PWM_UPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the PWM_UP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  PWM_UP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
PWM_UPIRQHandler:
        IRQ_to_SYS
        BL     PWM_UP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : I2CIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the I2C_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  I2C_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
I2CIRQHandler:
        IRQ_to_SYS
        BL     I2C_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : SSP1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the SSP1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  SSP1_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
SSP1IRQHandler:
        IRQ_to_SYS
        BL     SSP1_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : SSP0IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the SSP0_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  SSP0_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
SSP0IRQHandler:
        IRQ_to_SYS
        BL     SSP0_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : UART2IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the UART2_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  UART2_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
UART2IRQHandler:
        IRQ_to_SYS
        BL     UART2_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : UART1IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the UART1_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  UART1_IRQHandler function termination.
;* Input          : none
;* Output         : none
;*******************************************************************************/
UART1IRQHandler:
        IRQ_to_SYS
        BL     UART1_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : UART0IRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the UART0_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  UART0_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
UART0IRQHandler:
        IRQ_to_SYS
        BL     UART0_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : CANIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the CAN_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  CAN_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
CANIRQHandler:
        IRQ_to_SYS
        BL     CAN_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : USB_LPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the USB_LP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  USB_LP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
USB_LPIRQHandler:
        IRQ_to_SYS
        BL     USB_LP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : USB_HPIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the USB_HP_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  USB_HP_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
USB_HPIRQHandler:
        IRQ_to_SYS
        BL     USB_HP_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : ADCIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the ADC_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  ADC_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
ADCIRQHandler:
        IRQ_to_SYS
        BL     ADC_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : DMAIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the DMA_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  DMA_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
DMAIRQHandler:
        IRQ_to_SYS
        BL     DMA_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : EXTITIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the EXTIT_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  EXTIT_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
EXTITIRQHandler:
        IRQ_to_SYS
        BL     EXTIT_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : MRCCIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the MRCC_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  MRCC_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
MRCCIRQHandler:
        IRQ_to_SYS
        BL     MRCC_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : FLASHSMIIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the FLASHSMI_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  FLASHSMI_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
FLASHSMIIRQHandler:
        IRQ_to_SYS
        BL     FLASHSMI_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : RTCIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the RTC_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  RTC_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
RTCIRQHandler:
        IRQ_to_SYS
        BL     RTC_IRQHandler
        SYS_to_IRQ

/*;*******************************************************************************
;* Function Name  : TBIRQHandler
;* Description    : This function used to switch to SYS mode before entering
;*                  the TB_IRQHandler function located in 75x_it.c.
;*                  Then to return to IRQ mode after the
;*                  TB_IRQHandler function termination.
;* Input          : none
;* Output         : none
;********************************************************************************/
TBIRQHandler:
        IRQ_to_SYS
        BL     TB_IRQHandler
        SYS_to_IRQ
/*;**********************************************************************************/

Reset_Handler:
        LDR     pc, =NextInst

NextInst:
/*; Reset all Peripheral Clocks*/
/*; This is usefull only when using debugger to Reset\Run the application*/

     .if SMI_Bank0_EN
        LDR     r0, =0x01000000          /*; Disable peripherals clock (except GPIO)*/
     .else
        LDR     r0, =0x00000000          /*; Disable peripherals clock*/
     .endif
        LDR     r1, =MRCC_PCLKEN_Addr
        STR     r0, [r1]

     .if SMI_Bank0_EN
        LDR     r0, =0x1875623F          /*; Peripherals kept under reset (except GPIO)*/
     .else
        LDR     r0, =0x1975623F          /*; Peripherals kept under reset*/
     .endif     
           
        STR     r0, [r1,#4]              
        MOV     r0, #0
        NOP                              /*; Wait*/
        NOP
        NOP
        NOP
        STR     r0, [r1,#4]              /*; Disable peripherals reset*/

/*; Initialize stack pointer registers
  ; Enter each mode in turn and set up the stack pointer*/



        MSR     CPSR_c, #Mode_FIQ|I_Bit|F_Bit /*; No interrupts*/
        ldr     sp, =FIQ_Stack

        MSR     CPSR_c, #Mode_IRQ|I_Bit|F_Bit /*; No interrupts*/
        ldr     sp, =IRQ_Stack

        MSR     CPSR_c, #Mode_ABT|I_Bit|F_Bit /*; No interrupts*/
        ldr     sp, =ABT_Stack

        MSR     CPSR_c, #Mode_UNDEF|I_Bit|F_Bit /*; No interrupts*/
        ldr     sp,  =UNDEF_Stack

        MSR     CPSR_c, #Mode_SVC|I_Bit|F_Bit /*; No interrupts*/
        ldr     sp, =_estack

/*; ------------------------------------------------------------------------------
; Description  :  Enable SMI Bank0: enable GPIOs clock in MRCC_PCLKEN register, 
;                 enable SMI alternate function in GPIO_REMAP register and enable 
;                 Bank0 in SMI_CR1 register.
; ------------------------------------------------------------------------------*/
  .if SMI_Bank0_EN
        MOV     r0, #0x01000000
        LDR     r1, =MRCC_PCLKEN_Addr
        STR     r0, [r1]                 /*; Enable GPIOs clock*/

        LDR     r1, =GPIOREMAP0R_Addr
        MOV     r0, #SMI_EN_Mask
        LDR     r2, [r1]
        ORR     r2, r2, r0
        STR     r2, [r1]                 /*; Enable SMI alternate function  */

        LDR     r0, =0x251               /*; SMI Bank0 enabled, Prescaler = 2, Deselect Time = 5*/
        LDR     r1, =SMI_CR1_Addr
        STR     r0, [r1]                 /*; Configure CR1 register */
        LDR     r0, =0x00
        STR     r0, [r1,#4]              /*; Reset CR2 register */
  .endif

/*; ----------------------------------------------------------------------------
; Description  :  Remapping SRAM at address 0x00 after the application has 
;                 started executing. 
; ----------------------------------------------------------------------------*/
 .if  Remap_SRAM
        MOV     r0, #SRAM_mask
        LDR     r1, =CFG_GLCONF_Addr
        LDR     r2, [r1]                  /*; Read GLCONF Register*/
        BIC     r2, r2, #0x03             /*; Reset the SW_BOOT bits*/
        ORR     r2, r2, r0                /*; Change the SW_BOOT bits*/
        STR     r2, [r1]                  /*; Write GLCONF Register*/
  .endif

/*;-------------------------------------------------------------------------------
;Description  : Initialize the EIC as following :
;              - IRQ disabled
;              - FIQ disabled
;              - IVR contains the load PC opcode
;              - All channels are disabled
;              - All channels priority equal to 0
;              - All SIR registers contains offset to the related IRQ table entry
;-------------------------------------------------------------------------------*/
  .if EIC_INIT
        LDR     r3, =EIC_base_addr
        LDR     r4, =0x00000000
        STR     r4, [r3, #ICR_off_addr]   /*; Disable FIQ and IRQ*/
        STR     r4, [r3, #IER_off_addr]   /*; Disable all interrupts channels*/

        LDR     r4, =0xFFFFFFFF
        STR     r4, [r3, #IPR_off_addr]   /*; Clear all IRQ pending bits*/

        LDR     r4, =0x18
        STR     r4, [r3, #FIR_off_addr]   /*; Disable FIQ channels and clear FIQ pending bits*/

        LDR     r4, =0x00000000
        STR     r4, [r3, #CIPR_off_addr]  /*; Reset the current priority register*/

        LDR     r4, =0xE59F0000           /*; Write the LDR pc,pc,#offset..*/
        STR     r4, [r3, #IVR_off_addr]   /*; ..instruction code in IVR[31:16]*/


        LDR     r2,= 32                   /*; 32 Channel to initialize*/
        LDR     r0, =WAKUP_Addr           /*; Read the address of the IRQs address table*/
        LDR     r1, =0x00000FFF
        AND     r0,r0,r1
        LDR     r5,=SIR0_off_addr         /*; Read SIR0 address*/
        SUB     r4,r0,#8                  /*; subtract 8 for prefetch*/
        LDR     r1, =0xF7E8               /*; add the offset to the 0x00 address..*/
                                          /*; ..(IVR address + 7E8 = 0x00)*/
                                          /*; 0xF7E8 used to complete the LDR pc,offset opcode*/
        ADD     r1,r4,r1                  /*; compute the jump offset*/
EIC_INI:
        MOV     r4, r1, LSL #16           /*; Left shift the result*/
        STR     r4, [r3, r5]              /*; Store the result in SIRx register*/
        ADD     r1, r1, #4                /*; Next IRQ address*/
        ADD     r5, r5, #4                /*; Next SIR*/
        SUBS    r2, r2, #1                /*; Decrement the number of SIR registers to initialize*/
        BNE     EIC_INI                   /*; If more then continue*/

 .endif





  /* ;copy the initial values for .data section from FLASH to RAM */
	ldr	R1, =_sidata
	ldr	R2, =_sdata
	ldr	R3, =_edata
_reset_inidata_loop:
	cmp	R2, R3
	ldrlO	R0, [R1], #4
	strlO	R0, [R2], #4
	blO	_reset_inidata_loop

	;/* Clear the .bss section */
	mov   r0,#0						;/* get a zero */
	ldr   r1,=_sbss				;/* point to bss start */
	ldr   r2,=_ebss				;/* point to bss end */
_reset_inibss_loop:
	cmp   r1,r2						;/* check if some data remains to clear */
	strlo r0,[r1],#4				;/* clear 4 bytes */
	blo   _reset_inibss_loop	;/* loop until done */

/************************************************************************************************/

/*; --- Now enter the C code */
        B       main   /*; Note : use B not BL, because an application will*/
                         /*; never return this way*/























