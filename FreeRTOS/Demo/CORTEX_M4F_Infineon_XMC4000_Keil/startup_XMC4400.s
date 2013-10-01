;*****************************************************************************/
; * @file     startup_XMC4400.s
; * @brief    CMSIS Cortex-M4 Core Device Startup File for
; *           Infineon XMC4400 Device Series
; * @version  V1.00
; * @date     05. February 2013
; *
; * @note
; * Copyright (C) 2009-2013 ARM Limited. All rights reserved.
; *
; * @par
; * ARM Limited (ARM) is supplying this software for use with Cortex-M
; * processor based microcontrollers.  This file can be freely distributed
; * within development tools that are supporting such ARM based processors.
; *
; * @par
; * THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
; * OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
; * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
; * ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
; * CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
; *
; ******************************************************************************/

;/* ********************* Version History *********************************** */
;/* ***************************************************************************
; V0.2 , August 2012, First version
; V1.0 , February 2013, FIX for CPU prefetch bug implemented
;**************************************************************************** */


;*  <<< Use Configuration Wizard in Context Menu >>>

; Amount of memory (in bytes) allocated for Stack
; Tailor this value to your application needs
; <h> Stack Configuration
;   <o> Stack Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>

Stack_Size      EQU     0x00000400

                AREA    STACK, NOINIT, READWRITE, ALIGN=3
Stack_Mem       SPACE   Stack_Size
__initial_sp


; <h> Heap Configuration
;   <o>  Heap Size (in Bytes) <0x0-0xFFFFFFFF:8>
; </h>

Heap_Size       EQU     0x00000200

                AREA    HEAP, NOINIT, READWRITE, ALIGN=3
__heap_base
Heap_Mem        SPACE   Heap_Size
__heap_limit

                PRESERVE8
                THUMB


;/* ===========START : MACRO DEFINITION MACRO DEFINITION ================== */
;/*
; * STEP_AB and below have the prefetch functional deviation (Errata id: PMU_CM.001).
; * A veneer defined below will first
; * be executed which in turn branches to the final exception handler.
; *
; * In addition to defining the veneers, the vector table must for these buggy
; * devices contain the veneers.
; */

;set WORKAROUND_PMU_CM001 under Options for target - Asm - Define
;or use define below
              GBLL WORKAROUND_PMU_CM001

;/* A macro to setup a vector table entry based on STEP ID */
              IF    :DEF:WORKAROUND_PMU_CM001
                MACRO
                ExcpVector $Handler
                  DCD   $Handler._Veneer
                MEND
              ELSE
                MACRO
                ExcpVector $Handler
                  DCD   $Handler
                MEND
              ENDIF

;/* A macro to ease definition of the various handlers based on STEP ID */
              IF     :DEF:WORKAROUND_PMU_CM001

                ;/* First define the final exception handler */
                MACRO
                ExcpHandler $Handler_Func
$Handler_Func\
                  PROC
                  EXPORT  $Handler_Func            [WEAK]
                  B       .
                  ENDP

                ;/* And then define a veneer that will branch to the final excp handler */
$Handler_Func._Veneer\
                  PROC
                  EXPORT  $Handler_Func._Veneer    [WEAK]
                  LDR     R0, =$Handler_Func
                  PUSH    {LR}
                  BLX     R0
                  POP     {PC}
                  ALIGN
                  LTORG
                  ENDP
                MEND

              ELSE

                ;/* No prefetch bug, hence define only the final exception handler */
                MACRO
                ExcpHandler $Handler_Func
$Handler_Func\
                  PROC
                  EXPORT  $Handler_Func            [WEAK]
                  B       .
                  ENDP
                MEND

              ENDIF
;/* ============= END OF MACRO DEFINITION MACRO DEFINITION ================== */


;* ================== START OF VECTOR TABLE DEFINITION ====================== */
;* Vector Table - This gets programed into VTOR register */
                AREA    RESET, DATA, READONLY
                EXPORT  __Vectors
                EXPORT  __Vectors_End
                EXPORT  __Vectors_Size



__Vectors
    DCD          __initial_sp               ; Top of Stack
    DCD          Reset_Handler              ; Reset Handler

    ExcpVector   NMI_Handler                ; NMI Handler
    ExcpVector   HardFault_Handler          ; Hard Fault Handler
    ExcpVector   MemManage_Handler          ; MPU Fault Handler
    ExcpVector   BusFault_Handler           ; Bus Fault Handler
    ExcpVector   UsageFault_Handler         ; Usage Fault Handler
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    ExcpVector   SVC_Handler                ; SVCall Handler
    ExcpVector   DebugMon_Handler           ; Debug Monitor Handler
    DCD          0                          ; Reserved
    ExcpVector   PendSV_Handler             ; PendSV Handler
    ExcpVector   SysTick_Handler            ; SysTick Handler

    ; Interrupt Handlers for Service Requests (SR) from XMC4400 Peripherals
    ExcpVector   SCU_0_IRQHandler           ; Handler name for SR SCU_0
    ExcpVector   ERU0_0_IRQHandler          ; Handler name for SR ERU0_0
    ExcpVector   ERU0_1_IRQHandler          ; Handler name for SR ERU0_1
    ExcpVector   ERU0_2_IRQHandler          ; Handler name for SR ERU0_2
    ExcpVector   ERU0_3_IRQHandler          ; Handler name for SR ERU0_3
    ExcpVector   ERU1_0_IRQHandler          ; Handler name for SR ERU1_0
    ExcpVector   ERU1_1_IRQHandler          ; Handler name for SR ERU1_1
    ExcpVector   ERU1_2_IRQHandler          ; Handler name for SR ERU1_2
    ExcpVector   ERU1_3_IRQHandler          ; Handler name for SR ERU1_3
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    ExcpVector   PMU0_0_IRQHandler          ; Handler name for SR PMU0_0
    DCD          0                          ; Reserved
    ExcpVector   VADC0_C0_0_IRQHandler      ; Handler name for SR VADC0_C0_0
    ExcpVector   VADC0_C0_1_IRQHandler      ; Handler name for SR VADC0_C0_1
    ExcpVector   VADC0_C0_2_IRQHandler      ; Handler name for SR VADC0_C0_1
    ExcpVector   VADC0_C0_3_IRQHandler      ; Handler name for SR VADC0_C0_3
    ExcpVector   VADC0_G0_0_IRQHandler      ; Handler name for SR VADC0_G0_0
    ExcpVector   VADC0_G0_1_IRQHandler      ; Handler name for SR VADC0_G0_1
    ExcpVector   VADC0_G0_2_IRQHandler      ; Handler name for SR VADC0_G0_2
    ExcpVector   VADC0_G0_3_IRQHandler      ; Handler name for SR VADC0_G0_3
    ExcpVector   VADC0_G1_0_IRQHandler      ; Handler name for SR VADC0_G1_0
    ExcpVector   VADC0_G1_1_IRQHandler      ; Handler name for SR VADC0_G1_1
    ExcpVector   VADC0_G1_2_IRQHandler      ; Handler name for SR VADC0_G1_2
    ExcpVector   VADC0_G1_3_IRQHandler      ; Handler name for SR VADC0_G1_3
    ExcpVector   VADC0_G2_0_IRQHandler      ; Handler name for SR VADC0_G2_0
    ExcpVector   VADC0_G2_1_IRQHandler      ; Handler name for SR VADC0_G2_1
    ExcpVector   VADC0_G2_2_IRQHandler      ; Handler name for SR VADC0_G2_2
    ExcpVector   VADC0_G2_3_IRQHandler      ; Handler name for SR VADC0_G2_3
    ExcpVector   VADC0_G3_0_IRQHandler      ; Handler name for SR VADC0_G3_0
    ExcpVector   VADC0_G3_1_IRQHandler      ; Handler name for SR VADC0_G3_1
    ExcpVector   VADC0_G3_2_IRQHandler      ; Handler name for SR VADC0_G3_2
    ExcpVector   VADC0_G3_3_IRQHandler      ; Handler name for SR VADC0_G3_3
    ExcpVector   DSD0_0_IRQHandler          ; Handler name for SR DSD0_0
    ExcpVector   DSD0_1_IRQHandler          ; Handler name for SR DSD0_1
    ExcpVector   DSD0_2_IRQHandler          ; Handler name for SR DSD0_2
    ExcpVector   DSD0_3_IRQHandler          ; Handler name for SR DSD0_3
    ExcpVector   DSD0_4_IRQHandler          ; Handler name for SR DSD0_4
    ExcpVector   DSD0_5_IRQHandler          ; Handler name for SR DSD0_5
    ExcpVector   DSD0_6_IRQHandler          ; Handler name for SR DSD0_6
    ExcpVector   DSD0_7_IRQHandler          ; Handler name for SR DSD0_7
    ExcpVector   DAC0_0_IRQHandler          ; Handler name for SR DAC0_0
    ExcpVector   DAC0_1_IRQHandler          ; Handler name for SR DAC0_1
    ExcpVector   CCU40_0_IRQHandler         ; Handler name for SR CCU40_0
    ExcpVector   CCU40_1_IRQHandler         ; Handler name for SR CCU40_1
    ExcpVector   CCU40_2_IRQHandler         ; Handler name for SR CCU40_2
    ExcpVector   CCU40_3_IRQHandler         ; Handler name for SR CCU40_3
    ExcpVector   CCU41_0_IRQHandler         ; Handler name for SR CCU41_0
    ExcpVector   CCU41_1_IRQHandler         ; Handler name for SR CCU41_1
    ExcpVector   CCU41_2_IRQHandler         ; Handler name for SR CCU41_2
    ExcpVector   CCU41_3_IRQHandler         ; Handler name for SR CCU41_3
    ExcpVector   CCU42_0_IRQHandler         ; Handler name for SR CCU42_0
    ExcpVector   CCU42_1_IRQHandler         ; Handler name for SR CCU42_1
    ExcpVector   CCU42_2_IRQHandler         ; Handler name for SR CCU42_2
    ExcpVector   CCU42_3_IRQHandler         ; Handler name for SR CCU42_3
    ExcpVector   CCU43_0_IRQHandler         ; Handler name for SR CCU43_0
    ExcpVector   CCU43_1_IRQHandler         ; Handler name for SR CCU43_1
    ExcpVector   CCU43_2_IRQHandler         ; Handler name for SR CCU43_2
    ExcpVector   CCU43_3_IRQHandler         ; Handler name for SR CCU43_3
    ExcpVector   CCU80_0_IRQHandler         ; Handler name for SR CCU80_0
    ExcpVector   CCU80_1_IRQHandler         ; Handler name for SR CCU80_1
    ExcpVector   CCU80_2_IRQHandler         ; Handler name for SR CCU80_2
    ExcpVector   CCU80_3_IRQHandler         ; Handler name for SR CCU80_3
    ExcpVector   CCU81_0_IRQHandler         ; Handler name for SR CCU81_0
    ExcpVector   CCU81_1_IRQHandler         ; Handler name for SR CCU81_1
    ExcpVector   CCU81_2_IRQHandler         ; Handler name for SR CCU81_2
    ExcpVector   CCU81_3_IRQHandler         ; Handler name for SR CCU81_3
    ExcpVector   POSIF0_0_IRQHandler        ; Handler name for SR POSIF0_0
    ExcpVector   POSIF0_1_IRQHandler        ; Handler name for SR POSIF0_1
    ExcpVector   POSIF1_0_IRQHandler        ; Handler name for SR POSIF1_0
    ExcpVector   POSIF1_1_IRQHandler        ; Handler name for SR POSIF1_1
    ExcpVector   HRPWM_0_IRQHandler         ; Handler name for SR HRPWM_0
    ExcpVector   HRPWM_1_IRQHandler         ; Handler name for SR HRPWM_1
    ExcpVector   HRPWM_2_IRQHandler         ; Handler name for SR HRPWM_2
    ExcpVector   HRPWM_3_IRQHandler         ; Handler name for SR HRPWM_3
    ExcpVector   CAN0_0_IRQHandler          ; Handler name for SR CAN0_0
    ExcpVector   CAN0_1_IRQHandler          ; Handler name for SR CAN0_1
    ExcpVector   CAN0_2_IRQHandler          ; Handler name for SR CAN0_2
    ExcpVector   CAN0_3_IRQHandler          ; Handler name for SR CAN0_3
    ExcpVector   CAN0_4_IRQHandler          ; Handler name for SR CAN0_4
    ExcpVector   CAN0_5_IRQHandler          ; Handler name for SR CAN0_5
    ExcpVector   CAN0_6_IRQHandler          ; Handler name for SR CAN0_6
    ExcpVector   CAN0_7_IRQHandler          ; Handler name for SR CAN0_7
    ExcpVector   USIC0_0_IRQHandler         ; Handler name for SR USIC0_0
    ExcpVector   USIC0_1_IRQHandler         ; Handler name for SR USIC0_1
    ExcpVector   USIC0_2_IRQHandler         ; Handler name for SR USIC0_2
    ExcpVector   USIC0_3_IRQHandler         ; Handler name for SR USIC0_3
    ExcpVector   USIC0_4_IRQHandler         ; Handler name for SR USIC0_4
    ExcpVector   USIC0_5_IRQHandler         ; Handler name for SR USIC0_5
    ExcpVector   USIC1_0_IRQHandler         ; Handler name for SR USIC1_0
    ExcpVector   USIC1_1_IRQHandler         ; Handler name for SR USIC1_1
    ExcpVector   USIC1_2_IRQHandler         ; Handler name for SR USIC1_2
    ExcpVector   USIC1_3_IRQHandler         ; Handler name for SR USIC1_3
    ExcpVector   USIC1_4_IRQHandler         ; Handler name for SR USIC1_4
    ExcpVector   USIC1_5_IRQHandler         ; Handler name for SR USIC1_5
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    ExcpVector   LEDTS0_0_IRQHandler        ; Handler name for SR LEDTS0_0
    DCD          0                          ; Reserved
    ExcpVector   FCE0_0_IRQHandler          ; Handler name for SR FCE0_0
    ExcpVector   GPDMA0_0_IRQHandler        ; Handler name for SR GPDMA0_0
    DCD          0                          ; Reserved
    ExcpVector   USB0_0_IRQHandler          ; Handler name for SR USB0_0
    ExcpVector   ETH0_0_IRQHandler          ; Handler name for SR ETH0_0
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
    DCD          0                          ; Reserved
__Vectors_End

__Vectors_Size  EQU  __Vectors_End - __Vectors

;* ================== END OF VECTOR TABLE DEFINITION ======================= */

;* ================== START OF VECTOR ROUTINES ============================= */

                AREA    |.text|, CODE, READONLY

;* Reset Handler */
Reset_Handler    PROC
                 EXPORT  Reset_Handler             [WEAK]
        IMPORT  SystemInit
        IMPORT  __main

        ; Remap vector table
        LDR     R0, =__Vectors
        LDR     R1, =0xE000ED08 ;*VTOR register
        STR     R0,[R1]

        ;* C routines are likely to be called. Setup the stack now
        LDR     SP,=__initial_sp

        LDR     R0, = SystemInit
        BLX     R0

        ;SystemInit_DAVE3() is provided by DAVE3 code generation engine. It is
        ;weakly defined here though for a potential override.

        LDR     R0, = SystemInit_DAVE3
        BLX     R0

        ;* Reset stack pointer before zipping off to user application
        LDR     SP,=__initial_sp

        LDR     R0, =__main
        BX      R0

        ALIGN
        ENDP




;* ========== START OF EXCEPTION HANDLER DEFINITION ======================== */



;/* Default exception Handlers - Users may override this default functionality by
;   defining handlers of the same name in their C code */

    ExcpHandler   NMI_Handler
    ExcpHandler   HardFault_Handler
    ExcpHandler   MemManage_Handler
    ExcpHandler   BusFault_Handler
    ExcpHandler   UsageFault_Handler
    ExcpHandler   SVC_Handler
    ExcpHandler   DebugMon_Handler
    ExcpHandler   PendSV_Handler
    ExcpHandler   SysTick_Handler

;* ============= END OF EXCEPTION HANDLER DEFINITION ======================== */

;* ============= START OF INTERRUPT HANDLER DEFINITION ====================== */

;* IRQ Handlers */
    ExcpHandler   SCU_0_IRQHandler
    ExcpHandler   ERU0_0_IRQHandler
    ExcpHandler   ERU0_1_IRQHandler
    ExcpHandler   ERU0_2_IRQHandler
    ExcpHandler   ERU0_3_IRQHandler
    ExcpHandler   ERU1_0_IRQHandler
    ExcpHandler   ERU1_1_IRQHandler
    ExcpHandler   ERU1_2_IRQHandler
    ExcpHandler   ERU1_3_IRQHandler
    ExcpHandler   PMU0_0_IRQHandler
    ExcpHandler   VADC0_C0_0_IRQHandler
    ExcpHandler   VADC0_C0_1_IRQHandler
    ExcpHandler   VADC0_C0_2_IRQHandler
    ExcpHandler   VADC0_C0_3_IRQHandler
    ExcpHandler   VADC0_G0_0_IRQHandler
    ExcpHandler   VADC0_G0_1_IRQHandler
    ExcpHandler   VADC0_G0_2_IRQHandler
    ExcpHandler   VADC0_G0_3_IRQHandler
    ExcpHandler   VADC0_G1_0_IRQHandler
    ExcpHandler   VADC0_G1_1_IRQHandler
    ExcpHandler   VADC0_G1_2_IRQHandler
    ExcpHandler   VADC0_G1_3_IRQHandler
    ExcpHandler   VADC0_G2_0_IRQHandler
    ExcpHandler   VADC0_G2_1_IRQHandler
    ExcpHandler   VADC0_G2_2_IRQHandler
    ExcpHandler   VADC0_G2_3_IRQHandler
    ExcpHandler   VADC0_G3_0_IRQHandler
    ExcpHandler   VADC0_G3_1_IRQHandler
    ExcpHandler   VADC0_G3_2_IRQHandler
    ExcpHandler   VADC0_G3_3_IRQHandler
    ExcpHandler   DSD0_0_IRQHandler
    ExcpHandler   DSD0_1_IRQHandler
    ExcpHandler   DSD0_2_IRQHandler
    ExcpHandler   DSD0_3_IRQHandler
    ExcpHandler   DSD0_4_IRQHandler
    ExcpHandler   DSD0_5_IRQHandler
    ExcpHandler   DSD0_6_IRQHandler
    ExcpHandler   DSD0_7_IRQHandler
    ExcpHandler   DAC0_0_IRQHandler
    ExcpHandler   DAC0_1_IRQHandler
    ExcpHandler   CCU40_0_IRQHandler
    ExcpHandler   CCU40_1_IRQHandler
    ExcpHandler   CCU40_2_IRQHandler
    ExcpHandler   CCU40_3_IRQHandler
    ExcpHandler   CCU41_0_IRQHandler
    ExcpHandler   CCU41_1_IRQHandler
    ExcpHandler   CCU41_2_IRQHandler
    ExcpHandler   CCU41_3_IRQHandler
    ExcpHandler   CCU42_0_IRQHandler
    ExcpHandler   CCU42_1_IRQHandler
    ExcpHandler   CCU42_2_IRQHandler
    ExcpHandler   CCU42_3_IRQHandler
    ExcpHandler   CCU43_0_IRQHandler
    ExcpHandler   CCU43_1_IRQHandler
    ExcpHandler   CCU43_2_IRQHandler
    ExcpHandler   CCU43_3_IRQHandler
    ExcpHandler   CCU80_0_IRQHandler
    ExcpHandler   CCU80_1_IRQHandler
    ExcpHandler   CCU80_2_IRQHandler
    ExcpHandler   CCU80_3_IRQHandler
    ExcpHandler   CCU81_0_IRQHandler
    ExcpHandler   CCU81_1_IRQHandler
    ExcpHandler   CCU81_2_IRQHandler
    ExcpHandler   CCU81_3_IRQHandler
    ExcpHandler   POSIF0_0_IRQHandler
    ExcpHandler   POSIF0_1_IRQHandler
    ExcpHandler   POSIF1_0_IRQHandler
    ExcpHandler   POSIF1_1_IRQHandler
    ExcpHandler   HRPWM_0_IRQHandler
    ExcpHandler   HRPWM_1_IRQHandler
    ExcpHandler   HRPWM_2_IRQHandler
    ExcpHandler   HRPWM_3_IRQHandler
    ExcpHandler   CAN0_0_IRQHandler
    ExcpHandler   CAN0_1_IRQHandler
    ExcpHandler   CAN0_2_IRQHandler
    ExcpHandler   CAN0_3_IRQHandler
    ExcpHandler   CAN0_4_IRQHandler
    ExcpHandler   CAN0_5_IRQHandler
    ExcpHandler   CAN0_6_IRQHandler
    ExcpHandler   CAN0_7_IRQHandler
    ExcpHandler   USIC0_0_IRQHandler
    ExcpHandler   USIC0_1_IRQHandler
    ExcpHandler   USIC0_2_IRQHandler
    ExcpHandler   USIC0_3_IRQHandler
    ExcpHandler   USIC0_4_IRQHandler
    ExcpHandler   USIC0_5_IRQHandler
    ExcpHandler   USIC1_0_IRQHandler
    ExcpHandler   USIC1_1_IRQHandler
    ExcpHandler   USIC1_2_IRQHandler
    ExcpHandler   USIC1_3_IRQHandler
    ExcpHandler   USIC1_4_IRQHandler
    ExcpHandler   USIC1_5_IRQHandler
    ExcpHandler   LEDTS0_0_IRQHandler
    ExcpHandler   FCE0_0_IRQHandler
    ExcpHandler   GPDMA0_0_IRQHandler
    ExcpHandler   USB0_0_IRQHandler
    ExcpHandler   ETH0_0_IRQHandler

;* ============= END OF INTERRUPT HANDLER DEFINITION ======================== */

;*  Definition of the default weak SystemInit_DAVE3 function.
;*  This function will be called by the CMSIS SystemInit function.
;*  If DAVE3 requires an extended SystemInit it will create its own SystemInit_DAVE3
;*  which will overule this weak definition
SystemInit_DAVE3  PROC
                  EXPORT  SystemInit_DAVE3             [WEAK]
                  NOP
                  BX     LR
                  ENDP

;*  Definition of the default weak DAVE3 function for clock App usage.
;* AllowPLLInitByStartup Handler */
AllowPLLInitByStartup    PROC
                  EXPORT  AllowPLLInitByStartup        [WEAK]
                  MOV    R0,#1
                  BX     LR
                  ENDP

                  ALIGN

;*******************************************************************************
; User Stack and Heap initialization
;*******************************************************************************
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

;******************* Copyright (C) 2009-2013 ARM Limited *****END OF FILE*****
