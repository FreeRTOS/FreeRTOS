; <<< Use Configuration Wizard in Context Menu >>>
;******************************************************************************
;
; startup_rvmdk.S - Startup code for Stellaris.
;
; Copyright (c) 2006 Luminary Micro, Inc.  All rights reserved.
;
; Software License Agreement
;
; Luminary Micro, Inc. (LMI) is supplying this software for use solely and
; exclusively on LMI's Stellaris Family of microcontroller products.
;
; The software is owned by LMI and/or its suppliers, and is protected under
; applicable copyright laws.  All rights are reserved.  Any use in violation of
; the foregoing restrictions may subject the user to criminal sanctions under
; applicable laws, as well as to civil liability for the breach of the terms
; and conditions of this license.
;
; THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
; OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
; MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
; LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
; CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
;
; This is part of revision 816 of the Stellaris Driver Library.
;
;******************************************************************************

;******************************************************************************
;
; <h> Stack Configuration
;   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>
;
;******************************************************************************
Stack   EQU     0x00000100

;******************************************************************************
;
; <h> Heap Configuration
;   <o> Heap Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>
;
;******************************************************************************
Heap    EQU     0x00000000

;******************************************************************************
;
; Allocate space for the stack.
;
;******************************************************************************
        AREA    STACK, NOINIT, READWRITE, ALIGN=3
StackMem
        SPACE   Stack

;******************************************************************************
;
; Allocate space for the heap.
;
;******************************************************************************
        AREA    HEAP, NOINIT, READWRITE, ALIGN=3
HeapMem
        SPACE   Heap

;******************************************************************************
;
; Indicate that the code in this file preserves 8-byte alignment of the stack.
;
;******************************************************************************
        PRESERVE8

;******************************************************************************
;
; Place code into the reset code section.
;
;******************************************************************************
        AREA    RESET, CODE, READONLY
        THUMB

;******************************************************************************
;
; The vector table.
;
;******************************************************************************
		EXPORT __Vectors
__Vectors
        DCD     StackMem + Stack            ; Top of Stack
        DCD     Reset_Handler               ; Reset Handler
        DCD     NmiSR                       ; NMI Handler
        DCD     FaultISR                    ; Hard Fault Handler
        DCD     IntDefaultHandler           ; MPU Fault Handler
        DCD     IntDefaultHandler           ; Bus Fault Handler
        DCD     IntDefaultHandler           ; Usage Fault Handler
        DCD     0                           ; Reserved
        DCD     0                           ; Reserved
        DCD     0                           ; Reserved
        DCD     0                           ; Reserved
        DCD     vPortSVCHandler             ; SVCall Handler
        DCD     IntDefaultHandler           ; Debug Monitor Handler
        DCD     0                           ; Reserved
        DCD     xPortPendSVHandler      	; PendSV Handler
        DCD     xPortSysTickHandler     	; SysTick Handler
        DCD     IntDefaultHandler           ; GPIO Port A
        DCD     IntDefaultHandler           ; GPIO Port B
        DCD     vGPIO_ISR           	; GPIO Port C
        DCD     IntDefaultHandler           ; GPIO Port D
        DCD     IntDefaultHandler           ; GPIO Port E
        DCD     vUART_ISR           		; UART0
        DCD     IntDefaultHandler           ; UART1
        DCD     IntDefaultHandler           ; SSI
        DCD     IntDefaultHandler           ; I2C
        DCD     IntDefaultHandler           ; PWM Fault
        DCD     IntDefaultHandler           ; PWM Generator 0
        DCD     IntDefaultHandler           ; PWM Generator 1
        DCD     IntDefaultHandler           ; PWM Generator 2
        DCD     IntDefaultHandler           ; Quadrature Encoder
        DCD     IntDefaultHandler           ; ADC Sequence 0
        DCD     IntDefaultHandler           ; ADC Sequence 1
        DCD     IntDefaultHandler           ; ADC Sequence 2
        DCD     IntDefaultHandler           ; ADC Sequence 3
        DCD     IntDefaultHandler           ; Watchdog
        DCD     IntDefaultHandler           ; Timer 0A
        DCD     IntDefaultHandler           ; Timer 0B
        DCD     IntDefaultHandler           ; Timer 1A
        DCD     IntDefaultHandler           ; Timer 1B
        DCD     IntDefaultHandler           ; Timer 2A
        DCD     IntDefaultHandler           ; Timer 2B
        DCD     IntDefaultHandler           ; Comp 0
        DCD     IntDefaultHandler           ; Comp 1
        DCD     IntDefaultHandler           ; Comp 2
        DCD     IntDefaultHandler           ; System Control
        DCD     IntDefaultHandler           ; Flash Control

;******************************************************************************
;
; This is the code that gets called when the processor first starts execution
; following a reset event.
;
;******************************************************************************
        EXPORT  Reset_Handler
Reset_Handler
        ;
        ; Call __main() in the C library, which will call the application
        ; supplied main().
        ;
        IMPORT  __main
		IMPORT	vGPIO_ISR
		IMPORT  vUART_ISR
		IMPORT	xPortPendSVHandler
		IMPORT 	xPortSysTickHandler
		IMPORT 	vPortSVCHandler

        LDR     R0, =__main
        BX      R0

;******************************************************************************
;
; This is the code that gets called when the processor receives a NMI.  This
; simply enters an infinite loop, preserving the system state for examination
; by a debugger.
;
;******************************************************************************
NmiSR
        B       NmiSR

;******************************************************************************
;
; This is the code that gets called when the processor receives a fault
; interrupt.  This simply enters an infinite loop, preserving the system state
; for examination by a debugger.
;
;******************************************************************************
FaultISR
        B       FaultISR

;******************************************************************************
;
; This is the code that gets called when the processor receives an unexpected
; interrupt.  This simply enters an infinite loop, preserving the system state
; for examination by a debugger.
;
;******************************************************************************
IntDefaultHandler
        B       IntDefaultHandler

;******************************************************************************
;
; Make sure the end of this section is aligned.
;
;******************************************************************************
        ALIGN

;******************************************************************************
;
; Some code in the normal code section for initializing the heap and stack.
;
;******************************************************************************
        AREA    |.text|, CODE, READONLY

;******************************************************************************
;
; The function expected of the C library startup code for defining the stack
; and heap memory locations.
;
;******************************************************************************
        IMPORT  __use_two_region_memory
        EXPORT  __user_initial_stackheap
__user_initial_stackheap
        LDR     R0, =HeapMem
        LDR     R1, =(StackMem + Stack)
        LDR     R2, =(HeapMem + Heap)
        LDR     R3, =StackMem
        BX      LR

;******************************************************************************
;
; Make sure the end of this section is aligned.
;
;******************************************************************************
        ALIGN

; Note: 
; Using READWRITE places Section .RTOSHeap in Region ER_RW.
; Using NOINIT places Section .RTOSHeap in Region ER_ZI,which means
; "ZEROINITIALIZE" (sic), and which is the last region in memory. Then
; we need to make this section the last section, which is somewhat tricky,
; because we cannot use the sectionname, but need to use a defined symbol:
; Linker option: "--last xHeap"

		EXPORT xHeap

                AREA    RTOSHeap, DATA, NOINIT
xHeap

;******************************************************************************
;
; Tell the assembler that we're done.
;
;******************************************************************************
        END
