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
; History:
; 05/24/2006 : Version 1.1
; 05/18/2006 : Version 1.0
;*******************************************************************************
;* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
;* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
;* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
;* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
;* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
;* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;******************************************************************************/

; Depending in Your Application, Disable or Enable the following Define

;	  #define  BUFFERED_Mode       ; Work on Buffered mode, when enabling this define
                               ; just enable the Buffered define on 91x_conf.h

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

;--- BASE ADDRESSES
; System memory locations

SRAM_Base       	EQU     0x04000000
SRAM_Limit      	EQU     0x04018000			; at the top of 96 KB SRAM

SVC_Stack           DEFINE     SRAM_Limit       ; 512 byte SVC stack at
	                                             	 ; top of memory - used by kernel.
IRQ_Stack           DEFINE     SVC_Stack-512    ; followed by IRQ stack
USR_Stack           DEFINE     IRQ_Stack-512   	; followed by USR stack.  Tasks run in
                                                ; system mode but task stacks are allocated
                                                ; when the task is created.
FIQ_Stack           DEFINE     USR_Stack-8      ; followed by FIQ stack
ABT_Stack           DEFINE     FIQ_Stack-8      ; followed by ABT stack
UND_Stack         	DEFINE     ABT_Stack-8      ; followed by UNDEF stack

					EXTERN main

; STR9X register specific definition

FMI_BBSR_AHB_UB			EQU			0x54000000
FMI_BBADR_AHB_UB		EQU			0x5400000C
FMI_NBBSR_AHB_UB		EQU			0x54000004
FMI_NBBADR_AHB_UB		EQU			0x54000010

SCU_SCRO_APB1_UB		EQU			0x4C002034
SCRO_AHB_UNB    EQU     0x5C002034



;---------------------------------------------------------------
; ?program_start
;---------------------------------------------------------------
		MODULE	?program_start
		RSEG	ICODE:CODE(2)
		IMPORT    LINK
		PUBLIC	__program_start
		EXTERN	?main
                CODE32
                

__program_start:
        LDR     pc, =NextInst


NextInst


        NOP   ; execute some instructions to access CPU registers after wake
        NOP  ; up from Reset, while waiting for OSC stabilization
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
        NOP
		ldr r0,=LINK	; to include the vector table inside the final executable.



; --- Remap Flash Bank 0 at address 0x0 and Bank 1 at address 0x80000, 
;     when the bank 0 is the boot bank, then enable the Bank 1.

        LDR R6, =0x54000000
        LDR R7, =0x4
        STR R7, [R6]

        LDR R6, =0x54000004
        LDR R7, =0x3
        STR R7, [R6]

        LDR R6, =0x5400000C
        LDR R7, =0x0
        STR R7, [R6]

        LDR R6, =0x54000010
        LDR R7, =0x20000
        STR R7, [R6]

        LDR R6, =0x54000018
        LDR R7, =0x18
        STR R7, [R6]
        
; --- Enable 96K RAM
        LDR     R0, = SCRO_AHB_UNB
        LDR     R1, = 0x0196
        STR     R1, [R0]


	/* Setup a stack for each mode - note that this only sets up a usable stack
	for system/user, SWI and IRQ modes.   Also each mode is setup with
	interrupts initially disabled. */

	MSR     CPSR_c, #Mode_FIQ|I_Bit|F_Bit   ; No interrupts
	LDR   	SP, =FIQ_Stack

	MSR     CPSR_c, #Mode_IRQ|I_Bit|F_Bit   ; No interrupts
	LDR   	SP, =IRQ_Stack

	MSR     CPSR_c, #Mode_ABT|I_Bit|F_Bit   ; No interrupts
	LDR   	SP, =ABT_Stack

	MSR     CPSR_c, #Mode_UND|I_Bit|F_Bit   ; No interrupts
	LDR   	SP, =UND_Stack

	MSR     CPSR_c, #Mode_SVC|I_Bit|F_Bit   ; No interrupts
	LDR   	SP, =SVC_Stack

	MSR   	CPSR_c, #Mode_SYS|I_Bit|F_Bit   ; No interrupts
	LDR   	SP, =USR_Stack

	/* We want to start in supervisor mode.  Operation will switch to system
	mode when the first task starts. */
	MSR   CPSR_c, #Mode_SVC|I_Bit|F_Bit


; --- Set bits 17-18 of the Core Configuration Control Register
 
	MOV     r0, #0x60000             
	MCR     p15,0x1,r0,c15,c1,0
      

; --- Now enter the C code
	B       ?main   ; Note : use B not BL, because an application will
                         ; never return this way

	LTORG

	END
;******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****

