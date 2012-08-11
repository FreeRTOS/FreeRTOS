;/*****************************************************************************/
;/* STARTUP.S: Startup file for Luminary Micro LM3Sxxx                        */
;/*****************************************************************************/
;/* <<< Use Configuration Wizard in Context Menu >>>                          */ 
;/*****************************************************************************/
;/* This file is part of the uVision/ARM development tools.                   */
;/* Copyright (c) 2005-2006 Keil Software. All rights reserved.               */
;/* This software may only be used under the terms of a valid, current,       */
;/* end user licence from KEIL for a compatible version of KEIL software      */
;/* development tools. Nothing else gives you the right to use this software. */
;/*****************************************************************************/


;/*
; *  The STARTUP.S code is executed after CPU Reset. 
; */


;// <h> Stack Configuration
;//   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
;// </h>

Stack_Size      EQU     51

                AREA    STACK, NOINIT, READWRITE, ALIGN=3
Stack_Mem       SPACE   Stack_Size


;// <h> Heap Configuration
;//   <o>  Heap Size (in Bytes) <0x0-0xFFFFFFFF:8>
;// </h>

Heap_Size       EQU     0x00000000

                AREA    HEAP, NOINIT, READWRITE, ALIGN=3
Heap_Mem        SPACE   Heap_Size


; System Control Register Addresses
SYSCTL_BASE     EQU     0x400FE000      ; System Control Base Address
PBORCTL_OFS     EQU     0x0030          ; Power-On & Brown-Out Reset Control
LDOPC_OFS       EQU     0x0034          ; LDO Power
SRCR0_OFS       EQU     0x0040          ; Software Reset Control 0
SRCR1_OFS       EQU     0x0044          ; Software Reset Control 1
SRCR2_OFS       EQU     0x0048          ; Software Reset Control 2
RCC_OFS         EQU     0x0060          ; Run-Mode Clock Control
RCGC0_OFS       EQU     0x0100          ; Run-Mode Clock Gating Control 0
RCGC1_OFS       EQU     0x0104          ; Run-Mode Clock Gating Control 1
RCGC2_OFS       EQU     0x0108          ; Run-Mode Clock Gating Control 2
SCGC0_OFS       EQU     0x0110          ; Sleep-Mode Clock Gating Control 0
SCGC1_OFS       EQU     0x0114          ; Sleep-Mode Clock Gating Control 1
SCGC2_OFS       EQU     0x0118          ; Sleep-Mode Clock Gating Control 2
DCGC0_OFS       EQU     0x0120          ; Deep-Sleep-Mode Clock Gating Control 0
DCGC1_OFS       EQU     0x0124          ; Deep-Sleep-Mode Clock Gating Control 1
DCGC2_OFS       EQU     0x0128          ; Deep-Sleep-Mode Clock Gating Control 2


                PRESERVE8
                

; Area Definition and Entry Point
;  Startup Code must be linked first at Address 0.

                AREA    RESET, CODE, READONLY
                THUMB

				IMPORT	xPortPendSVHandler
				IMPORT 	xPortSysTickHandler
				IMPORT	vUART_ISR
				IMPORT	vPortSVCHandler

; Vector Table
				EXPORT __Vectors
__Vectors       DCD     Stack_Mem + Stack_Size  ; Top of Stack
                DCD     Reset_Handler      		; Reset Handler
                DCD     NmiSR            		; NMI Handler
                DCD     DefaultISR       		; Hard Fault Handler
                DCD     DefaultISR         		; MPU Fault Handler
                DCD     DefaultISR         		; Bus Fault Handler
                DCD     DefaultISR         		; Usage Fault Handler
                DCD     0                       ; Reserved
                DCD     0                       ; Reserved
                DCD     0                       ; Reserved
                DCD     0                       ; Reserved
                DCD     vPortSVCHandler      	; SVCall Handler
                DCD     DefaultISR         		; Debug Monitor Handler
                DCD     0                       ; Reserved
                DCD     xPortPendSVHandler      ; PendSV Handler
                DCD     xPortSysTickHandler     ; SysTick Handler
                DCD     DefaultISR         	; GPIO Port A Handler
                DCD     DefaultISR         	; GPIO Port B Handler
                DCD     DefaultISR         	; GPIO Port C Handler
                DCD     DefaultISR         	; GPIO Port D Handler
                DCD     DefaultISR         	; GPIO Port E Handler
                DCD     vUART_ISR			; UART0 Rx/Tx Handler
                DCD     DefaultISR         	; UART1 Rx/Tx Handler
                DCD     DefaultISR         	; SSI Rx/Tx Handler
                DCD     DefaultISR         	; I2C Master/Slave Handler
                DCD     DefaultISR         ; PWM Fault Handler
                DCD     DefaultISR         ; PWM Generator 0 Handler
                DCD     DefaultISR         ; PWM Generator 1 Handler
                DCD     DefaultISR         ; PWM Generator 2 Handler
                DCD     DefaultISR         ; Quadrature Encoder Handler
                DCD     DefaultISR         ; ADC Sequence 0 Handler
                DCD     DefaultISR         ; ADC Sequence 1 Handler
                DCD     DefaultISR         ; ADC Sequence 2 Handler
                DCD     DefaultISR         ; ADC Sequence 3 Handler
                DCD     DefaultISR         ; Watchdog Timer Handler
                DCD     DefaultISR         ; Timer 0 Subtimer A Handler
                DCD     DefaultISR         ; Timer 0 Subtimer B Handler
                DCD     DefaultISR         ; Timer 1 Subtimer A Handler
                DCD     DefaultISR         ; Timer 1 Subtimer B Handler
                DCD     DefaultISR         ; Timer 2 Subtimer A Handler
                DCD     DefaultISR         ; Timer 2 Subtimer B Handler
                DCD     DefaultISR         ; Analog Comparator 0 Handler
                DCD     DefaultISR         ; Analog Comparator 1 Handler
                DCD     DefaultISR         ; Analog Comparator 2 Handler
                DCD     DefaultISR         ; System Control Handler
                DCD     DefaultISR         ; Flash Control Handler

; Dummy Handlers are implemented as infinite loops which can be modified.

NmiSR			B       NmiSR
FaultISR		B		FaultISR
				EXPORT FaultISR
DefaultISR		B       DefaultISR


; Reset Handler

                EXPORT  Reset_Handler
Reset_Handler   

; Enable Clock Gating for Peripherals
;                LDR     R0, =SYSCTL_BASE        ; System Control Base Address
;                MVN     R1, #0                  ; Value 0xFFFFFFFF
;                STR     R1, [R0,#RCGC0_OFS]     ; Run-Mode Clock Gating Ctrl 0
;                STR     R1, [R0,#RCGC1_OFS]     ; Run-Mode Clock Gating Ctrl 1
;                STR     R1, [R0,#RCGC2_OFS]     ; Run-Mode Clock Gating Ctrl 2

; Enter the C code

                IMPORT  __main
                LDR     R0, =__main
                BX      R0


; User Initial Stack & Heap
                AREA    |.text|, CODE, READONLY

                IMPORT  __use_two_region_memory
                EXPORT  __user_initial_stackheap
__user_initial_stackheap

                LDR     R0, =  Heap_Mem
                LDR     R1, =(Stack_Mem + Stack_Size)
                LDR     R2, = (Heap_Mem +  Heap_Size)
                LDR     R3, = Stack_Mem
                BX      LR

                ALIGN


                END
