;/*****************************************************************************/
;/* STM32F10x.s: Startup file for ST STM32F10x device series                  */
;/*****************************************************************************/
;/* <<< Use Configuration Wizard in Context Menu >>>                          */
;/*****************************************************************************/
;/* This file is part of the uVision/ARM development tools.                   */
;/* Copyright (c) 2005-2007 Keil Software. All rights reserved.               */
;/* This software may only be used under the terms of a valid, current,       */
;/* end user licence from KEIL for a compatible version of KEIL software      */
;/* development tools. Nothing else gives you the right to use this software. */
;/*****************************************************************************/


;// <h> Stack Configuration
;//   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
;// </h>

Stack_Size      EQU     0x00000200

                AREA    STACK, NOINIT, READWRITE, ALIGN=3
Stack_Mem       SPACE   Stack_Size
__initial_sp


;// <h> Heap Configuration
;//   <o>  Heap Size (in Bytes) <0x0-0xFFFFFFFF:8>
;// </h>

Heap_Size       EQU     0x00000000

                AREA    HEAP, NOINIT, READWRITE, ALIGN=3
__heap_base
Heap_Mem        SPACE   Heap_Size
__heap_limit

				IMPORT xPortPendSVHandler
				IMPORT xPortSysTickHandler
				IMPORT vPortSVCHandler
				IMPORT vUARTInterruptHandler
				IMPORT vTimer2IntHandler

                PRESERVE8
                THUMB


; Vector Table Mapped to Address 0 at Reset

                AREA    RESET, DATA, READONLY
                EXPORT  __Vectors

__Vectors       DCD     __initial_sp              ; Top of Stack
                DCD     Reset_Handler             ; Reset Handler
                DCD     NMI_Handler               ; NMI Handler
                DCD     HardFault_Handler         ; Hard Fault Handler
                DCD     MemManage_Handler         ; MPU Fault Handler
                DCD     BusFault_Handler          ; Bus Fault Handler
                DCD     UsageFault_Handler        ; Usage Fault Handler
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     0                         ; Reserved
                DCD     vPortSVCHandler           ; SVCall Handler
                DCD     DebugMon_Handler          ; Debug Monitor Handler
                DCD     0                         ; Reserved
                DCD     xPortPendSVHandler        ; PendSV Handler
                DCD     xPortSysTickHandler       ; SysTick Handler

                ; External Interrupts
                DCD     WWDG_IRQHandler           ; Window Watchdog
                DCD     PVD_IRQHandler            ; PVD through EXTI Line detect
                DCD     TAMPER_IRQHandler         ; Tamper
                DCD     RTC_IRQHandler            ; RTC
                DCD     FLASH_IRQHandler          ; Flash
                DCD     RCC_IRQHandler            ; RCC
                DCD     EXTI0_IRQHandler          ; EXTI Line 0
                DCD     EXTI1_IRQHandler          ; EXTI Line 1
                DCD     EXTI2_IRQHandler          ; EXTI Line 2
                DCD     EXTI3_IRQHandler          ; EXTI Line 3
                DCD     EXTI4_IRQHandler          ; EXTI Line 4
                DCD     DMAChannel1_IRQHandler    ; DMA Channel 1
                DCD     DMAChannel2_IRQHandler    ; DMA Channel 2
                DCD     DMAChannel3_IRQHandler    ; DMA Channel 3
                DCD     DMAChannel4_IRQHandler    ; DMA Channel 4
                DCD     DMAChannel5_IRQHandler    ; DMA Channel 5
                DCD     DMAChannel6_IRQHandler    ; DMA Channel 6
                DCD     DMAChannel7_IRQHandler    ; DMA Channel 7
                DCD     ADC_IRQHandler            ; ADC
                DCD     USB_HP_CAN_TX_IRQHandler  ; USB High Priority or CAN TX
                DCD     USB_LP_CAN_RX0_IRQHandler ; USB Low  Priority or CAN RX0
                DCD     CAN_RX1_IRQHandler        ; CAN RX1
                DCD     CAN_SCE_IRQHandler        ; CAN SCE
                DCD     EXTI9_5_IRQHandler        ; EXTI Line 9..5
                DCD     TIM1_BRK_IRQHandler       ; TIM1 Break
                DCD     TIM1_UP_IRQHandler        ; TIM1 Update
                DCD     TIM1_TRG_COM_IRQHandler   ; TIM1 Trigger and Commutation
                DCD     TIM1_CC_IRQHandler        ; TIM1 Capture Compare
                DCD     vTimer2IntHandler         ; TIM2
                DCD     TIM3_IRQHandler           ; TIM3
                DCD     TIM4_IRQHandler           ; TIM4
                DCD     I2C1_EV_IRQHandler        ; I2C1 Event
                DCD     I2C1_ER_IRQHandler        ; I2C1 Error
                DCD     I2C2_EV_IRQHandler        ; I2C2 Event
                DCD     I2C2_ER_IRQHandler        ; I2C2 Error
                DCD     SPI1_IRQHandler           ; SPI1
                DCD     SPI2_IRQHandler           ; SPI2
                DCD     vUARTInterruptHandler     ; USART1
                DCD     USART2_IRQHandler         ; USART2
                DCD     USART3_IRQHandler         ; USART3
                DCD     EXTI15_10_IRQHandler      ; EXTI Line 15..10
                DCD     RTCAlarm_IRQHandler       ; RTC Alarm through EXTI Line
                DCD     USBWakeUp_IRQHandler      ; USB Wakeup from suspend


                AREA    |.text|, CODE, READONLY


; Reset Handler

Reset_Handler   PROC
                EXPORT  Reset_Handler             [WEAK]
                IMPORT  __main
                LDR     R0, =__main
                BX      R0
                ENDP


; Dummy Exception Handlers (infinite loops which can be modified)                

NMI_Handler     PROC
                EXPORT  NMI_Handler               [WEAK]
                B       .
                ENDP
HardFault_Handler\
                PROC
                EXPORT  HardFault_Handler         [WEAK]
                B       .
                ENDP
MemManage_Handler\
                PROC
                EXPORT  MemManage_Handler         [WEAK]
                B       .
                ENDP
BusFault_Handler\
                PROC
                EXPORT  BusFault_Handler          [WEAK]
                B       .
                ENDP
UsageFault_Handler\
                PROC
                EXPORT  UsageFault_Handler        [WEAK]
                B       .
                ENDP
SVC_Handler     PROC
                EXPORT  SVC_Handler               [WEAK]
                B       .
                ENDP
DebugMon_Handler\
                PROC
                EXPORT  DebugMon_Handler          [WEAK]
                B       .
                ENDP
PendSV_Handler  PROC
                EXPORT  PendSV_Handler            [WEAK]
                B       .
                ENDP
SysTick_Handler PROC
                EXPORT  SysTick_Handler           [WEAK]
                B       .
                ENDP

Default_Handler PROC

                EXPORT  WWDG_IRQHandler           [WEAK]
                EXPORT  PVD_IRQHandler            [WEAK]
                EXPORT  TAMPER_IRQHandler         [WEAK]
                EXPORT  RTC_IRQHandler            [WEAK]
                EXPORT  FLASH_IRQHandler          [WEAK]
                EXPORT  RCC_IRQHandler            [WEAK]
                EXPORT  EXTI0_IRQHandler          [WEAK]
                EXPORT  EXTI1_IRQHandler          [WEAK]
                EXPORT  EXTI2_IRQHandler          [WEAK]
                EXPORT  EXTI3_IRQHandler          [WEAK]
                EXPORT  EXTI4_IRQHandler          [WEAK]
                EXPORT  DMAChannel1_IRQHandler    [WEAK]
                EXPORT  DMAChannel2_IRQHandler    [WEAK]
                EXPORT  DMAChannel3_IRQHandler    [WEAK]
                EXPORT  DMAChannel4_IRQHandler    [WEAK]
                EXPORT  DMAChannel5_IRQHandler    [WEAK]
                EXPORT  DMAChannel6_IRQHandler    [WEAK]
                EXPORT  DMAChannel7_IRQHandler    [WEAK]
                EXPORT  ADC_IRQHandler            [WEAK]
                EXPORT  USB_HP_CAN_TX_IRQHandler  [WEAK]
                EXPORT  USB_LP_CAN_RX0_IRQHandler [WEAK]
                EXPORT  CAN_RX1_IRQHandler        [WEAK]
                EXPORT  CAN_SCE_IRQHandler        [WEAK]
                EXPORT  EXTI9_5_IRQHandler        [WEAK]
                EXPORT  TIM1_BRK_IRQHandler       [WEAK]
                EXPORT  TIM1_UP_IRQHandler        [WEAK]
                EXPORT  TIM1_TRG_COM_IRQHandler   [WEAK]
                EXPORT  TIM1_CC_IRQHandler        [WEAK]
                EXPORT  TIM2_IRQHandler           [WEAK]
                EXPORT  TIM3_IRQHandler           [WEAK]
                EXPORT  TIM4_IRQHandler           [WEAK]
                EXPORT  I2C1_EV_IRQHandler        [WEAK]
                EXPORT  I2C1_ER_IRQHandler        [WEAK]
                EXPORT  I2C2_EV_IRQHandler        [WEAK]
                EXPORT  I2C2_ER_IRQHandler        [WEAK]
                EXPORT  SPI1_IRQHandler           [WEAK]
                EXPORT  SPI2_IRQHandler           [WEAK]
                EXPORT  USART1_IRQHandler         [WEAK]
                EXPORT  USART2_IRQHandler         [WEAK]
                EXPORT  USART3_IRQHandler         [WEAK]
                EXPORT  EXTI15_10_IRQHandler      [WEAK]
                EXPORT  RTCAlarm_IRQHandler       [WEAK]
                EXPORT  USBWakeUp_IRQHandler      [WEAK]

WWDG_IRQHandler
PVD_IRQHandler
TAMPER_IRQHandler
RTC_IRQHandler
FLASH_IRQHandler
RCC_IRQHandler
EXTI0_IRQHandler
EXTI1_IRQHandler
EXTI2_IRQHandler
EXTI3_IRQHandler
EXTI4_IRQHandler
DMAChannel1_IRQHandler
DMAChannel2_IRQHandler
DMAChannel3_IRQHandler
DMAChannel4_IRQHandler
DMAChannel5_IRQHandler
DMAChannel6_IRQHandler
DMAChannel7_IRQHandler
ADC_IRQHandler
USB_HP_CAN_TX_IRQHandler
USB_LP_CAN_RX0_IRQHandler
CAN_RX1_IRQHandler
CAN_SCE_IRQHandler
EXTI9_5_IRQHandler
TIM1_BRK_IRQHandler
TIM1_UP_IRQHandler
TIM1_TRG_COM_IRQHandler
TIM1_CC_IRQHandler
TIM2_IRQHandler
TIM3_IRQHandler
TIM4_IRQHandler
I2C1_EV_IRQHandler
I2C1_ER_IRQHandler
I2C2_EV_IRQHandler
I2C2_ER_IRQHandler
SPI1_IRQHandler
SPI2_IRQHandler
USART1_IRQHandler
USART2_IRQHandler
USART3_IRQHandler
EXTI15_10_IRQHandler
RTCAlarm_IRQHandler
USBWakeUp_IRQHandler

                B       .

                ENDP


                ALIGN


; User Initial Stack & Heap

                IF      :DEF:__MICROLIB
                
                EXPORT  __initial_sp
                EXPORT  __heap_base
                EXPORT  __heap_limit
                
                ELSE
                
                IMPORT  __use_two_region_memory
                EXPORT  __user_initial_stackheap
__user_initial_stackheap

                LDR     R0, =  Heap_Mem
                LDR     R1, =(Stack_Mem + Stack_Size)
                LDR     R2, = (Heap_Mem +  Heap_Size)
                LDR     R3, = Stack_Mem
                BX      LR

                ALIGN

                ENDIF


                END
