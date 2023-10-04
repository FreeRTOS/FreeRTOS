;*****************************************************************************/
; * @file     startup_XMC1300.s
; * @brief    CMSIS Cortex-M4 Core Device Startup File for
; *           Infineon XMC1300 Device Series
; * @version  V1.00
; * @date     21. Jan. 2013
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

Heap_Size       EQU     0x00000000

                AREA    HEAP, NOINIT, READWRITE, ALIGN=3
__heap_base
Heap_Mem        SPACE   Heap_Size
__heap_limit

; <h> Clock system handling by SSW
;   <h> CLK_VAL1 Configuration
;     <o0.0..7>    FDIV Fractional Divider Selection
;     <o0.8..15>   IDIV Divider Selection
;                     <0=> Divider is bypassed
;                     <1=> MCLK = 32 MHz
;                     <2=> MCLK = 16 MHz
;                     <3=> MCLK = 10.67 MHz
;                     <4=> MCLK = 8 MHz
;                     <254=> MCLK = 126 kHz
;                     <255=> MCLK = 125.5 kHz
;     <o0.16>      PCLKSEL PCLK Clock Select
;                     <0=> PCLK = MCLK
;                     <1=> PCLK = 2 x MCLK
;     <o0.17..19>  RTCCLKSEL RTC Clock Select
;                     <0=> 32.768kHz standby clock
;                     <1=> 32.768kHz external clock from ERU0.IOUT0
;                     <2=> 32.768kHz external clock from ACMP0.OUT
;                     <3=> 32.768kHz external clock from ACMP1.OUT
;                     <4=> 32.768kHz external clock from ACMP2.OUT
;                     <5=> Reserved
;                     <6=> Reserved
;                     <7=> Reserved
;     <o0.31>      do not move CLK_VAL1 to SCU_CLKCR[0..19]
;   </h>
CLK_VAL1_Val    EQU     0x00000100      ; 0xF0000000

;   <h> CLK_VAL2 Configuration
;     <o0.0>    disable VADC and SHS Gating
;     <o0.1>    disable CCU80 Gating
;     <o0.2>    disable CCU40 Gating
;     <o0.3>    disable USIC0 Gating
;     <o0.4>    disable BCCU0 Gating
;     <o0.5>    disable LEDTS0 Gating
;     <o0.6>    disable LEDTS1 Gating
;     <o0.7>    disable POSIF0 Gating
;     <o0.8>    disable MATH Gating
;     <o0.9>    disable WDT Gating
;     <o0.10>   disable RTC Gating
;     <o0.31>   do not move CLK_VAL2 to SCU_CGATCLR0[0..10]
;   </h>
CLK_VAL2_Val    EQU     0x00000000      ; 0xF0000000
; </h>

                PRESERVE8
                THUMB

;* ================== START OF VECTOR TABLE DEFINITION ====================== */
;* Vector Table Mapped to Address 0 at Reset
                AREA    RESET, DATA, READONLY
                EXPORT  __Vectors
                EXPORT  __Vectors_End
                EXPORT  __Vectors_Size



__Vectors
    DCD   __initial_sp                ;* Top of Stack
    DCD   Reset_Handler               ;* Reset Handler
    DCD   0                           ;* Not used
    DCD   0                           ;* Not Used
    DCD   CLK_VAL1_Val                ;* CLK_VAL1
    DCD   CLK_VAL2_Val                ;* CLK_VAL2
__Vectors_End

__Vectors_Size  EQU  __Vectors_End - __Vectors

;* ================== END OF VECTOR TABLE DEFINITION ======================== */


;* ================== START OF VECTOR ROUTINES ============================== */
                AREA    |.text|, CODE, READONLY

;* Reset Handler
Reset_Handler    PROC
                 EXPORT  Reset_Handler             [WEAK]
        IMPORT  __main
        IMPORT  SystemInit

        ;* C routines are likely to be called. Setup the stack now
        LDR     R0, =__initial_sp
        MOV     SP, R0

       ; Following code initializes the Veneers at address 0x20000000 with a "branch to itself"
       ; The real veneers will be copied later from the scatter loader before reaching main.
       ; This init code should handle an exception before the real veneers are copied.
SRAM_BASE            EQU     0x20000000
VENEER_INIT_CODE     EQU     0xE7FEBF00             ; NOP, B .

        LDR     R1, =SRAM_BASE
        LDR     R2, =VENEER_INIT_CODE                
        MOVS    R0, #48                     ; Veneer 0..47
Init_Veneers
        STR     R2, [R1]
        ADDS    R1, #4
        SUBS    R0, R0, #1
        BNE     Init_Veneers


        LDR     R0, =SystemInit
        BLX     R0


        ; SystemInit_DAVE3() is provided by DAVE3 code generation engine. It is
        ; weakly defined here though for a potential override.

        LDR     R0, = SystemInit_DAVE3
        BLX     R0


        LDR     R0, =__main
        BX      R0


        ALIGN
        ENDP

;* ========================================================================== */



;* ========== START OF EXCEPTION HANDLER DEFINITION ========================= */
;* Default exception Handlers - Users may override this default functionality

NMI_Handler     PROC
                EXPORT  NMI_Handler                   [WEAK]
                B       .
                ENDP
HardFault_Handler\
                PROC
                EXPORT  HardFault_Handler             [WEAK]
                B       .
                ENDP
SVC_Handler\
                PROC
                EXPORT  SVC_Handler                   [WEAK]
                B       .
                ENDP
PendSV_Handler\
                PROC
                EXPORT  PendSV_Handler                [WEAK]
                B       .
                ENDP
SysTick_Handler\
                PROC
                EXPORT  SysTick_Handler               [WEAK]
                B       .
                ENDP

;* ============= END OF EXCEPTION HANDLER DEFINITION ======================== */


;* ============= START OF INTERRUPT HANDLER DEFINITION ====================== */
;* IRQ Handlers

Default_Handler PROC
               EXPORT     SCU_0_IRQHandler            [WEAK]
               EXPORT     SCU_1_IRQHandler            [WEAK]
               EXPORT     SCU_2_IRQHandler            [WEAK]
               EXPORT     ERU0_0_IRQHandler           [WEAK]
               EXPORT     ERU0_1_IRQHandler           [WEAK]
               EXPORT     ERU0_2_IRQHandler           [WEAK]
               EXPORT     ERU0_3_IRQHandler           [WEAK]
               EXPORT     MATH0_0_IRQHandler          [WEAK]
               EXPORT     USIC0_0_IRQHandler          [WEAK]
               EXPORT     USIC0_1_IRQHandler          [WEAK]
               EXPORT     USIC0_2_IRQHandler          [WEAK]
               EXPORT     USIC0_3_IRQHandler          [WEAK]
               EXPORT     USIC0_4_IRQHandler          [WEAK]
               EXPORT     USIC0_5_IRQHandler          [WEAK]
               EXPORT     VADC0_C0_0_IRQHandler       [WEAK]
               EXPORT     VADC0_C0_1_IRQHandler       [WEAK]
               EXPORT     VADC0_G0_0_IRQHandler       [WEAK]
               EXPORT     VADC0_G0_1_IRQHandler       [WEAK]
               EXPORT     VADC0_G1_0_IRQHandler       [WEAK]
               EXPORT     VADC0_G1_1_IRQHandler       [WEAK]
               EXPORT     CCU40_0_IRQHandler          [WEAK]
               EXPORT     CCU40_1_IRQHandler          [WEAK]
               EXPORT     CCU40_2_IRQHandler          [WEAK]
               EXPORT     CCU40_3_IRQHandler          [WEAK]
               EXPORT     CCU80_0_IRQHandler          [WEAK]
               EXPORT     CCU80_1_IRQHandler          [WEAK]
               EXPORT     POSIF0_0_IRQHandler         [WEAK]
               EXPORT     POSIF0_1_IRQHandler         [WEAK]
               EXPORT     LEDTS0_0_IRQHandler         [WEAK]
               EXPORT     LEDTS1_0_IRQHandler         [WEAK]
               EXPORT     BCCU0_0_IRQHandler          [WEAK]

SCU_0_IRQHandler
SCU_1_IRQHandler
SCU_2_IRQHandler
ERU0_0_IRQHandler
ERU0_1_IRQHandler
ERU0_2_IRQHandler
ERU0_3_IRQHandler
MATH0_0_IRQHandler
USIC0_0_IRQHandler
USIC0_1_IRQHandler
USIC0_2_IRQHandler
USIC0_3_IRQHandler
USIC0_4_IRQHandler
USIC0_5_IRQHandler
VADC0_C0_0_IRQHandler
VADC0_C0_1_IRQHandler
VADC0_G0_0_IRQHandler
VADC0_G0_1_IRQHandler
VADC0_G1_0_IRQHandler
VADC0_G1_1_IRQHandler
CCU40_0_IRQHandler
CCU40_1_IRQHandler
CCU40_2_IRQHandler
CCU40_3_IRQHandler
CCU80_0_IRQHandler
CCU80_1_IRQHandler
POSIF0_0_IRQHandler
POSIF0_1_IRQHandler
LEDTS0_0_IRQHandler
LEDTS1_0_IRQHandler
BCCU0_0_IRQHandler

                B       .

                ENDP

                ALIGN

;* ============= END OF INTERRUPT HANDLER DEFINITION ======================== */

;*  Definition of the default weak SystemInit_DAVE3 function.
;*  This function will be called by the CMSIS SystemInit function.
;*  If DAVE3 requires an extended SystemInit it will create its own SystemInit_DAVE3
;*  which will overule this weak definition
SystemInit_DAVE3    PROC
                  EXPORT  SystemInit_DAVE3             [WEAK]
                  NOP
                  BX LR
        ENDP

;*  Definition of the default weak DAVE3 function for clock App usage.
;*  AllowClkInitByStartup Handler */
AllowClkInitByStartup    PROC
                  EXPORT  AllowClkInitByStartup        [WEAK]
                  MOVS R0,#1
                  BX LR
        ENDP


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


;* ================== START OF INTERRUPT HANDLER VENEERS ==================== */
; Veneers are located to fix SRAM Address 0x2000'0000
                AREA    |.ARM.__at_0x20000000|, CODE, READWRITE

; Each Veneer has exactly a lengs of 4 Byte

                MACRO
                STAYHERE $IrqNumber
                LDR  R0, =$IrqNumber
                B    .
                MEND

                MACRO
                JUMPTO $Handler
                LDR  R0, =$Handler
                BX   R0
                MEND

                STAYHERE 0x0                          ;* Reserved
                STAYHERE 0x1                          ;* Reserved 
                STAYHERE 0x2                          ;* Reserved 
                JUMPTO   HardFault_Handler            ;* HardFault Veneer  
                STAYHERE 0x4                          ;* Reserved 
                STAYHERE 0x5                          ;* Reserved 
                STAYHERE 0x6                          ;* Reserved 
                STAYHERE 0x7                          ;* Reserved 
                STAYHERE 0x8                          ;* Reserved 
                STAYHERE 0x9                          ;* Reserved 
                STAYHERE 0xA                          ;* Reserved
                JUMPTO   SVC_Handler                  ;* SVC Veneer        
                STAYHERE 0xC                          ;* Reserved
                STAYHERE 0xD                          ;* Reserved
                JUMPTO   PendSV_Handler               ;* PendSV Veneer     
                JUMPTO   SysTick_Handler              ;* SysTick Veneer    
                JUMPTO   SCU_0_IRQHandler             ;* SCU_0 Veneer      
                JUMPTO   SCU_1_IRQHandler             ;* SCU_1 Veneer      
                JUMPTO   SCU_2_IRQHandler             ;* SCU_2 Veneer      
                JUMPTO   ERU0_0_IRQHandler            ;* SCU_3 Veneer      
                JUMPTO   ERU0_1_IRQHandler            ;* SCU_4 Veneer      
                JUMPTO   ERU0_2_IRQHandler            ;* SCU_5 Veneer      
                JUMPTO   ERU0_3_IRQHandler            ;* SCU_6 Veneer      
                JUMPTO   MATH0_0_IRQHandler           ;* SCU_7 Veneer      
                STAYHERE 0x18                         ;* Reserved
                JUMPTO   USIC0_0_IRQHandler           ;* USIC0_0 Veneer    
                JUMPTO   USIC0_1_IRQHandler           ;* USIC0_1 Veneer    
                JUMPTO   USIC0_2_IRQHandler           ;* USIC0_2 Veneer    
                JUMPTO   USIC0_3_IRQHandler           ;* USIC0_3 Veneer    
                JUMPTO   USIC0_4_IRQHandler           ;* USIC0_4 Veneer    
                JUMPTO   LEDTS0_0_IRQHandler          ;* USIC0_5 Veneer    
                JUMPTO   VADC0_C0_0_IRQHandler        ;* VADC0_C0_0 Veneer 
                JUMPTO   VADC0_C0_1_IRQHandler        ;* VADC0_C0_1 Veneer 
                JUMPTO   VADC0_G0_0_IRQHandler        ;* VADC0_G0_0 Veneer 
                JUMPTO   VADC0_G0_1_IRQHandler        ;* VADC0_G0_1 Veneer 
                JUMPTO   VADC0_G1_0_IRQHandler        ;* VADC0_G1_0 Veneer 
                JUMPTO   VADC0_G1_1_IRQHandler        ;* VADC0_G1_1 Veneer 
                JUMPTO   CCU40_0_IRQHandler           ;* CCU40_0 Veneer    
                JUMPTO   CCU40_1_IRQHandler           ;* CCU40_1 Veneer    
                JUMPTO   CCU40_2_IRQHandler           ;* CCU40_2 Veneer    
                JUMPTO   CCU40_3_IRQHandler           ;* CCU40_3 Veneer    
                JUMPTO   CCU80_0_IRQHandler           ;* CCU80_0 Veneer    
                JUMPTO   CCU80_1_IRQHandler           ;* CCU80_1 Veneer    
                JUMPTO   POSIF0_0_IRQHandler          ;* POSIF0_0 Veneer   
                JUMPTO   POSIF0_1_IRQHandler          ;* POSIF0_1 Veneer   
                JUMPTO   LEDTS0_0_IRQHandler          ;* LEDTS0_0 Veneer   
                JUMPTO   LEDTS1_0_IRQHandler          ;* LEDTS1_0 Veneer   
                JUMPTO   BCCU0_0_IRQHandler           ;* BCCU0_0 Veneer    

                ALIGN

;* ================== END OF INTERRUPT HANDLER VENEERS ====================== */

                END
