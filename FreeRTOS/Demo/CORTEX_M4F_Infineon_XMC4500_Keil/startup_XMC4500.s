;*****************************************************************************/
; * @file     startup_XMC4500.s
; * @brief    CMSIS Cortex-M4 Core Device Startup File for
; *           Infineon XMC4500 Device Series
; * @version  V1.03
; * @date     16. Jan. 2012
; *
; * @note
; * Copyright (C) 2009-2011 ARM Limited. All rights reserved.
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

Heap_Size       EQU     0x00000200

                AREA    HEAP, NOINIT, READWRITE, ALIGN=3
__heap_base
Heap_Mem        SPACE   Heap_Size
__heap_limit

                PRESERVE8
                THUMB


;* ================== START OF VECTOR TABLE DEFINITION ====================== */
;* Vector Table - This gets programed into VTOR register */
                AREA    RESET, DATA, READONLY
                EXPORT  __Vectors
                EXPORT  __Vectors_End
                EXPORT  __Vectors_Size



__Vectors
    DCD   __initial_sp                ;* Top of Stack                 */
    DCD   Reset_Handler               ;* Reset Handler                */
    DCD   NMI_Handler                 ;* NMI Handler                  */
    DCD   HardFault_Handler           ;* Hard Fault Handler           */
    DCD   MemManage_Handler           ;* MPU Fault Handler            */
    DCD   BusFault_Handler            ;* Bus Fault Handler            */
    DCD   UsageFault_Handler          ;* Usage Fault Handler          */
    DCD   0                           ;* Reserved                     */
    DCD   0                           ;* Reserved                     */
    DCD   0                           ;* Reserved                     */
    DCD   0                           ;* Reserved                     */
    DCD   SVC_Handler                 ;* SVCall Handler               */
    DCD   DebugMon_Handler            ;* Debug Monitor Handler        */
    DCD   0                           ;* Reserved                     */
    DCD   PendSV_Handler              ;* PendSV Handler               */
    DCD   SysTick_Handler             ;* SysTick Handler              */

    ;* Interrupt Handlers for Service Requests (SR) from XMC4500 Peripherals */
    DCD   SCU_0_IRQHandler            ;* Handler name for SR SCU_0     */
    DCD   ERU0_0_IRQHandler           ;* Handler name for SR ERU0_0    */
    DCD   ERU0_1_IRQHandler           ;* Handler name for SR ERU0_1    */
    DCD   ERU0_2_IRQHandler           ;* Handler name for SR ERU0_2    */
    DCD   ERU0_3_IRQHandler           ;* Handler name for SR ERU0_3    */ 
    DCD   ERU1_0_IRQHandler           ;* Handler name for SR ERU1_0    */
    DCD   ERU1_1_IRQHandler           ;* Handler name for SR ERU1_1    */
    DCD   ERU1_2_IRQHandler           ;* Handler name for SR ERU1_2    */
    DCD   ERU1_3_IRQHandler           ;* Handler name for SR ERU1_3    */
    DCD   0                           ;* Not Available                 */
    DCD   0                           ;* Not Available                 */
    DCD   0                           ;* Not Available                 */
    DCD   PMU0_0_IRQHandler           ;* Handler name for SR PMU0_0    */
    DCD   0                           ;* Not Available                 */
    DCD   VADC0_C0_0_IRQHandler       ;* Handler name for SR VADC0_C0_0  */
    DCD   VADC0_C0_1_IRQHandler       ;* Handler name for SR VADC0_C0_1  */
    DCD   VADC0_C0_2_IRQHandler       ;* Handler name for SR VADC0_C0_1  */
    DCD   VADC0_C0_3_IRQHandler       ;* Handler name for SR VADC0_C0_3  */
    DCD   VADC0_G0_0_IRQHandler       ;* Handler name for SR VADC0_G0_0  */
    DCD   VADC0_G0_1_IRQHandler       ;* Handler name for SR VADC0_G0_1  */
    DCD   VADC0_G0_2_IRQHandler       ;* Handler name for SR VADC0_G0_2  */
    DCD   VADC0_G0_3_IRQHandler       ;* Handler name for SR VADC0_G0_3  */
    DCD   VADC0_G1_0_IRQHandler       ;* Handler name for SR VADC0_G1_0  */
    DCD   VADC0_G1_1_IRQHandler       ;* Handler name for SR VADC0_G1_1  */
    DCD   VADC0_G1_2_IRQHandler       ;* Handler name for SR VADC0_G1_2  */
    DCD   VADC0_G1_3_IRQHandler       ;* Handler name for SR VADC0_G1_3  */
    DCD   VADC0_G2_0_IRQHandler       ;* Handler name for SR VADC0_G2_0  */
    DCD   VADC0_G2_1_IRQHandler       ;* Handler name for SR VADC0_G2_1  */
    DCD   VADC0_G2_2_IRQHandler       ;* Handler name for SR VADC0_G2_2  */
    DCD   VADC0_G2_3_IRQHandler       ;* Handler name for SR VADC0_G2_3  */
    DCD   VADC0_G3_0_IRQHandler       ;* Handler name for SR VADC0_G3_0  */
    DCD   VADC0_G3_1_IRQHandler       ;* Handler name for SR VADC0_G3_1  */
    DCD   VADC0_G3_2_IRQHandler       ;* Handler name for SR VADC0_G3_2  */
    DCD   VADC0_G3_3_IRQHandler       ;* Handler name for SR VADC0_G3_3  */
    DCD   DSD0_0_IRQHandler           ;* Handler name for SR DSD0_0    */
    DCD   DSD0_1_IRQHandler           ;* Handler name for SR DSD0_1    */
    DCD   DSD0_2_IRQHandler           ;* Handler name for SR DSD0_2    */
    DCD   DSD0_3_IRQHandler           ;* Handler name for SR DSD0_3    */
    DCD   DSD0_4_IRQHandler           ;* Handler name for SR DSD0_4    */
    DCD   DSD0_5_IRQHandler           ;* Handler name for SR DSD0_5    */
    DCD   DSD0_6_IRQHandler           ;* Handler name for SR DSD0_6    */
    DCD   DSD0_7_IRQHandler           ;* Handler name for SR DSD0_7    */
    DCD   DAC0_0_IRQHandler           ;* Handler name for SR DAC0_0    */
    DCD   DAC0_1_IRQHandler           ;* Handler name for SR DAC0_0    */
    DCD   CCU40_0_IRQHandler          ;* Handler name for SR CCU40_0   */
    DCD   CCU40_1_IRQHandler          ;* Handler name for SR CCU40_1   */
    DCD   CCU40_2_IRQHandler          ;* Handler name for SR CCU40_2   */
    DCD   CCU40_3_IRQHandler          ;* Handler name for SR CCU40_3   */
    DCD   CCU41_0_IRQHandler          ;* Handler name for SR CCU41_0   */
    DCD   CCU41_1_IRQHandler          ;* Handler name for SR CCU41_1   */
    DCD   CCU41_2_IRQHandler          ;* Handler name for SR CCU41_2   */
    DCD   CCU41_3_IRQHandler          ;* Handler name for SR CCU41_3   */
    DCD   CCU42_0_IRQHandler          ;* Handler name for SR CCU42_0   */
    DCD   CCU42_1_IRQHandler          ;* Handler name for SR CCU42_1   */
    DCD   CCU42_2_IRQHandler          ;* Handler name for SR CCU42_2   */
    DCD   CCU42_3_IRQHandler          ;* Handler name for SR CCU42_3   */
    DCD   CCU43_0_IRQHandler          ;* Handler name for SR CCU43_0   */
    DCD   CCU43_1_IRQHandler          ;* Handler name for SR CCU43_1   */
    DCD   CCU43_2_IRQHandler          ;* Handler name for SR CCU43_2   */
    DCD   CCU43_3_IRQHandler          ;* Handler name for SR CCU43_3   */
    DCD   CCU80_0_IRQHandler          ;* Handler name for SR CCU80_0   */
    DCD   CCU80_1_IRQHandler          ;* Handler name for SR CCU80_1   */
    DCD   CCU80_2_IRQHandler          ;* Handler name for SR CCU80_2   */
    DCD   CCU80_3_IRQHandler          ;* Handler name for SR CCU80_3   */
    DCD   CCU81_0_IRQHandler          ;* Handler name for SR CCU81_0   */
    DCD   CCU81_1_IRQHandler          ;* Handler name for SR CCU81_1   */
    DCD   CCU81_2_IRQHandler          ;* Handler name for SR CCU81_2   */
    DCD   CCU81_3_IRQHandler          ;* Handler name for SR CCU81_3   */
    DCD   POSIF0_0_IRQHandler         ;* Handler name for SR POSIF0_0  */
    DCD   POSIF0_1_IRQHandler         ;* Handler name for SR POSIF0_1  */
    DCD   POSIF1_0_IRQHandler         ;* Handler name for SR POSIF1_0  */
    DCD   POSIF1_1_IRQHandler         ;* Handler name for SR POSIF1_1  */
    DCD   0                           ;* Not Available                 */
    DCD   0                           ;* Not Available                 */
    DCD   0                           ;* Not Available                 */
    DCD   0                           ;* Not Available                 */
    DCD   CAN0_0_IRQHandler           ;* Handler name for SR CAN0_0    */
    DCD   CAN0_1_IRQHandler           ;* Handler name for SR CAN0_1    */
    DCD   CAN0_2_IRQHandler           ;* Handler name for SR CAN0_2    */
    DCD   CAN0_3_IRQHandler           ;* Handler name for SR CAN0_3    */
    DCD   CAN0_4_IRQHandler           ;* Handler name for SR CAN0_4    */
    DCD   CAN0_5_IRQHandler           ;* Handler name for SR CAN0_5    */
    DCD   CAN0_6_IRQHandler           ;* Handler name for SR CAN0_6    */
    DCD   CAN0_7_IRQHandler           ;* Handler name for SR CAN0_7    */
    DCD   USIC0_0_IRQHandler          ;* Handler name for SR USIC0_0   */
    DCD   USIC0_1_IRQHandler          ;* Handler name for SR USIC0_1   */
    DCD   USIC0_2_IRQHandler          ;* Handler name for SR USIC0_2   */
    DCD   USIC0_3_IRQHandler          ;* Handler name for SR USIC0_3   */
    DCD   USIC0_4_IRQHandler          ;* Handler name for SR USIC0_4   */
    DCD   USIC0_5_IRQHandler          ;* Handler name for SR USIC0_5   */
    DCD   USIC1_0_IRQHandler          ;* Handler name for SR USIC1_0   */
    DCD   USIC1_1_IRQHandler          ;* Handler name for SR USIC1_1   */
    DCD   USIC1_2_IRQHandler          ;* Handler name for SR USIC1_2   */
    DCD   USIC1_3_IRQHandler          ;* Handler name for SR USIC1_3   */
    DCD   USIC1_4_IRQHandler          ;* Handler name for SR USIC1_4   */
    DCD   USIC1_5_IRQHandler          ;* Handler name for SR USIC1_5   */
    DCD   USIC2_0_IRQHandler          ;* Handler name for SR USIC2_0   */
    DCD   USIC2_1_IRQHandler          ;* Handler name for SR USIC2_1   */
    DCD   USIC2_2_IRQHandler          ;* Handler name for SR USIC2_2   */
    DCD   USIC2_3_IRQHandler          ;* Handler name for SR USIC2_3   */
    DCD   USIC2_4_IRQHandler          ;* Handler name for SR USIC2_4   */
    DCD   USIC2_5_IRQHandler          ;* Handler name for SR USIC2_5   */
    DCD   LEDTS0_0_IRQHandler         ;* Handler name for SR LEDTS0_0  */
    DCD   0                           ;* Not Available                 */
    DCD   FCE0_0_IRQHandler           ;* Handler name for SR FCE0_0    */
    DCD   GPDMA0_0_IRQHandler         ;* Handler name for SR GPDMA0_0  */
    DCD   SDMMC0_0_IRQHandler         ;* Handler name for SR SDMMC0_0  */
    DCD   USB0_0_IRQHandler           ;* Handler name for SR USB0_0    */
    DCD   ETH0_0_IRQHandler           ;* Handler name for SR ETH0_0    */
    DCD   0                           ;* Not Available                 */
    DCD   GPDMA1_0_IRQHandler         ;* Handler name for SR GPDMA1_0  */
    DCD   0                           ;* Not Available                 */
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

				; switch off branch prediction required in A11 step to use cached memory
        LDR R0,=0x58004000  ;PREF_PCON         
				LDR R1,[R0]
				ORR R1,R1,#0x00010000
				STR R1,[R0]

        ; Clear existing parity errors if any required in A11 step 
				LDR R0,=0x50004150  ;SCU_GCU_PEFLAG
				LDR R1,=0xFFFFFFFF
				STR R1,[R0]

				; Disable parity  required in A11 step
				LDR R0,=0x5000413C ; SCU_GCU_PEEN
				MOV R1,#0
				STR R1,[R0]

        ;enable un-aligned memory access 
        LDR     R1, =0xE000ED14 
        LDR.W   R0,[R1,#0x0]
        BIC     R0,R0,#0x8
        STR.W   R0,[R1,#0x0]


        ;* C routines are likely to be called. Setup the stack now 
        LDR     SP,=__initial_sp


        LDR     R0, = SystemInit 
        BLX     R0
   
 
        ;* Reset stack pointer before zipping off to user application 
        LDR     SP,=__initial_sp

        LDR     R0, =__main 
        BX      R0

        ENDP


;* ========== START OF EXCEPTION HANDLER DEFINITION ======================== */

;* Default exception Handlers - Users may override this default functionality by

NMI_Handler     PROC
                EXPORT  NMI_Handler                [WEAK]
                B       .
                ENDP
HardFault_Handler\
                PROC
                EXPORT  HardFault_Handler          [WEAK]
                B       .
                ENDP
MemManage_Handler\
                PROC
                EXPORT  MemManage_Handler          [WEAK]
                B       .
                ENDP
BusFault_Handler\
                PROC
                EXPORT  BusFault_Handler           [WEAK]
                B       .
                ENDP
UsageFault_Handler\
                PROC
                EXPORT  UsageFault_Handler         [WEAK]
                B       .
                ENDP
SVC_Handler     PROC
                EXPORT  SVC_Handler                [WEAK]
                B       .
                ENDP
DebugMon_Handler\
                PROC
                EXPORT  DebugMon_Handler           [WEAK]
                B       .
                ENDP
PendSV_Handler  PROC
                EXPORT  PendSV_Handler             [WEAK]
                B       .
                ENDP
SysTick_Handler PROC
                EXPORT  SysTick_Handler            [WEAK]
                B       .
                ENDP

;* ============= END OF EXCEPTION HANDLER DEFINITION ======================== */

;* ============= START OF INTERRUPT HANDLER DEFINITION ====================== */

;* IRQ Handlers */
               EXPORT   SCU_0_IRQHandler           [WEAK]
               EXPORT   ERU0_0_IRQHandler          [WEAK]
               EXPORT   ERU0_1_IRQHandler          [WEAK]
               EXPORT   ERU0_2_IRQHandler          [WEAK]
               EXPORT   ERU0_3_IRQHandler          [WEAK]
               EXPORT   ERU1_0_IRQHandler          [WEAK]
               EXPORT   ERU1_1_IRQHandler          [WEAK]
               EXPORT   ERU1_2_IRQHandler          [WEAK]
               EXPORT   ERU1_3_IRQHandler          [WEAK]
               EXPORT   PMU0_0_IRQHandler          [WEAK]
               EXPORT   VADC0_C0_0_IRQHandler      [WEAK]
               EXPORT   VADC0_C0_1_IRQHandler      [WEAK]
               EXPORT   VADC0_C0_2_IRQHandler      [WEAK]
               EXPORT   VADC0_C0_3_IRQHandler      [WEAK]
               EXPORT   VADC0_G0_0_IRQHandler      [WEAK]
               EXPORT   VADC0_G0_1_IRQHandler      [WEAK]
               EXPORT   VADC0_G0_2_IRQHandler      [WEAK]
               EXPORT   VADC0_G0_3_IRQHandler      [WEAK]
               EXPORT   VADC0_G1_0_IRQHandler      [WEAK]
               EXPORT   VADC0_G1_1_IRQHandler      [WEAK]
               EXPORT   VADC0_G1_2_IRQHandler      [WEAK]
               EXPORT   VADC0_G1_3_IRQHandler      [WEAK]
               EXPORT   VADC0_G2_0_IRQHandler      [WEAK]
               EXPORT   VADC0_G2_1_IRQHandler      [WEAK]
               EXPORT   VADC0_G2_2_IRQHandler      [WEAK]
               EXPORT   VADC0_G2_3_IRQHandler      [WEAK]
               EXPORT   VADC0_G3_0_IRQHandler      [WEAK]
               EXPORT   VADC0_G3_1_IRQHandler      [WEAK]
               EXPORT   VADC0_G3_2_IRQHandler      [WEAK]
               EXPORT   VADC0_G3_3_IRQHandler      [WEAK]
               EXPORT   DSD0_0_IRQHandler          [WEAK]
               EXPORT   DSD0_1_IRQHandler          [WEAK]
               EXPORT   DSD0_2_IRQHandler          [WEAK]
               EXPORT   DSD0_3_IRQHandler          [WEAK]
               EXPORT   DSD0_4_IRQHandler          [WEAK]
               EXPORT   DSD0_5_IRQHandler          [WEAK]
               EXPORT   DSD0_6_IRQHandler          [WEAK]
               EXPORT   DSD0_7_IRQHandler          [WEAK]
               EXPORT   DAC0_0_IRQHandler          [WEAK]
               EXPORT   DAC0_1_IRQHandler          [WEAK]
               EXPORT   CCU40_0_IRQHandler         [WEAK]
               EXPORT   CCU40_1_IRQHandler         [WEAK]
               EXPORT   CCU40_2_IRQHandler         [WEAK]
               EXPORT   CCU40_3_IRQHandler         [WEAK]
               EXPORT   CCU41_0_IRQHandler         [WEAK]
               EXPORT   CCU41_1_IRQHandler         [WEAK]
               EXPORT   CCU41_2_IRQHandler         [WEAK]
               EXPORT   CCU41_3_IRQHandler         [WEAK]
               EXPORT   CCU42_0_IRQHandler         [WEAK]
               EXPORT   CCU42_1_IRQHandler         [WEAK]
               EXPORT   CCU42_2_IRQHandler         [WEAK]
               EXPORT   CCU42_3_IRQHandler         [WEAK]
               EXPORT   CCU43_0_IRQHandler         [WEAK]
               EXPORT   CCU43_1_IRQHandler         [WEAK]
               EXPORT   CCU43_2_IRQHandler         [WEAK]
               EXPORT   CCU43_3_IRQHandler         [WEAK]
               EXPORT   CCU80_0_IRQHandler         [WEAK]
               EXPORT   CCU80_1_IRQHandler         [WEAK]
               EXPORT   CCU80_2_IRQHandler         [WEAK]
               EXPORT   CCU80_3_IRQHandler         [WEAK]
               EXPORT   CCU81_0_IRQHandler         [WEAK]
               EXPORT   CCU81_1_IRQHandler         [WEAK]
               EXPORT   CCU81_2_IRQHandler         [WEAK]
               EXPORT   CCU81_3_IRQHandler         [WEAK]
               EXPORT   POSIF0_0_IRQHandler        [WEAK]
               EXPORT   POSIF0_1_IRQHandler        [WEAK]
               EXPORT   POSIF1_0_IRQHandler        [WEAK]
               EXPORT   POSIF1_1_IRQHandler        [WEAK]
               EXPORT   CAN0_0_IRQHandler          [WEAK]
               EXPORT   CAN0_1_IRQHandler          [WEAK]
               EXPORT   CAN0_2_IRQHandler          [WEAK]
               EXPORT   CAN0_3_IRQHandler          [WEAK]
               EXPORT   CAN0_4_IRQHandler          [WEAK]
               EXPORT   CAN0_5_IRQHandler          [WEAK]
               EXPORT   CAN0_6_IRQHandler          [WEAK]
               EXPORT   CAN0_7_IRQHandler          [WEAK]
               EXPORT   USIC0_0_IRQHandler         [WEAK]
               EXPORT   USIC0_1_IRQHandler         [WEAK]
               EXPORT   USIC0_2_IRQHandler         [WEAK]
               EXPORT   USIC0_3_IRQHandler         [WEAK]
               EXPORT   USIC0_4_IRQHandler         [WEAK]
               EXPORT   USIC0_5_IRQHandler         [WEAK]
               EXPORT   USIC1_0_IRQHandler         [WEAK]
               EXPORT   USIC1_1_IRQHandler         [WEAK]
               EXPORT   USIC1_2_IRQHandler         [WEAK]
               EXPORT   USIC1_3_IRQHandler         [WEAK]
               EXPORT   USIC1_4_IRQHandler         [WEAK]
               EXPORT   USIC1_5_IRQHandler         [WEAK]
               EXPORT   USIC2_0_IRQHandler         [WEAK]
               EXPORT   USIC2_1_IRQHandler         [WEAK]
               EXPORT   USIC2_2_IRQHandler         [WEAK]
               EXPORT   USIC2_3_IRQHandler         [WEAK]
               EXPORT   USIC2_4_IRQHandler         [WEAK]
               EXPORT   USIC2_5_IRQHandler         [WEAK]
               EXPORT   LEDTS0_0_IRQHandler        [WEAK]
               EXPORT   FCE0_0_IRQHandler          [WEAK]
               EXPORT   GPDMA0_0_IRQHandler        [WEAK]
               EXPORT   SDMMC0_0_IRQHandler        [WEAK]
               EXPORT   USB0_0_IRQHandler          [WEAK]
               EXPORT   ETH0_0_IRQHandler          [WEAK]
               EXPORT   GPDMA1_0_IRQHandler        [WEAK]


SCU_0_IRQHandler     
ERU0_0_IRQHandler     
ERU0_1_IRQHandler     
ERU0_2_IRQHandler     
ERU0_3_IRQHandler     
ERU1_0_IRQHandler     
ERU1_1_IRQHandler     
ERU1_2_IRQHandler     
ERU1_3_IRQHandler     
PMU0_0_IRQHandler     
VADC0_C0_0_IRQHandler     
VADC0_C0_1_IRQHandler     
VADC0_C0_2_IRQHandler     
VADC0_C0_3_IRQHandler     
VADC0_G0_0_IRQHandler     
VADC0_G0_1_IRQHandler     
VADC0_G0_2_IRQHandler     
VADC0_G0_3_IRQHandler     
VADC0_G1_0_IRQHandler     
VADC0_G1_1_IRQHandler     
VADC0_G1_2_IRQHandler     
VADC0_G1_3_IRQHandler     
VADC0_G2_0_IRQHandler     
VADC0_G2_1_IRQHandler     
VADC0_G2_2_IRQHandler     
VADC0_G2_3_IRQHandler     
VADC0_G3_0_IRQHandler     
VADC0_G3_1_IRQHandler     
VADC0_G3_2_IRQHandler     
VADC0_G3_3_IRQHandler     
DSD0_0_IRQHandler     
DSD0_1_IRQHandler     
DSD0_2_IRQHandler     
DSD0_3_IRQHandler     
DSD0_4_IRQHandler     
DSD0_5_IRQHandler     
DSD0_6_IRQHandler     
DSD0_7_IRQHandler     
DAC0_0_IRQHandler     
DAC0_1_IRQHandler     
CCU40_0_IRQHandler     
CCU40_1_IRQHandler     
CCU40_2_IRQHandler     
CCU40_3_IRQHandler     
CCU41_0_IRQHandler     
CCU41_1_IRQHandler     
CCU41_2_IRQHandler     
CCU41_3_IRQHandler     
CCU42_0_IRQHandler     
CCU42_1_IRQHandler     
CCU42_2_IRQHandler     
CCU42_3_IRQHandler     
CCU43_0_IRQHandler     
CCU43_1_IRQHandler     
CCU43_2_IRQHandler     
CCU43_3_IRQHandler     
CCU80_0_IRQHandler     
CCU80_1_IRQHandler     
CCU80_2_IRQHandler     
CCU80_3_IRQHandler     
CCU81_0_IRQHandler     
CCU81_1_IRQHandler     
CCU81_2_IRQHandler     
CCU81_3_IRQHandler     
POSIF0_0_IRQHandler     
POSIF0_1_IRQHandler     
POSIF1_0_IRQHandler     
POSIF1_1_IRQHandler     
CAN0_0_IRQHandler     
CAN0_1_IRQHandler     
CAN0_2_IRQHandler     
CAN0_3_IRQHandler     
CAN0_4_IRQHandler     
CAN0_5_IRQHandler     
CAN0_6_IRQHandler     
CAN0_7_IRQHandler     
USIC0_0_IRQHandler     
USIC0_1_IRQHandler     
USIC0_2_IRQHandler     
USIC0_3_IRQHandler     
USIC0_4_IRQHandler     
USIC0_5_IRQHandler     
USIC1_0_IRQHandler     
USIC1_1_IRQHandler     
USIC1_2_IRQHandler     
USIC1_3_IRQHandler     
USIC1_4_IRQHandler     
USIC1_5_IRQHandler     
USIC2_0_IRQHandler     
USIC2_1_IRQHandler     
USIC2_2_IRQHandler     
USIC2_3_IRQHandler     
USIC2_4_IRQHandler     
USIC2_5_IRQHandler     
LEDTS0_0_IRQHandler     
FCE0_0_IRQHandler     
GPDMA0_0_IRQHandler     
SDMMC0_0_IRQHandler     
USB0_0_IRQHandler     
ETH0_0_IRQHandler     
GPDMA1_0_IRQHandler     


;* ============= END OF INTERRUPT HANDLER DEFINITION ======================== */

;*  Definition of the default weak SystemInit_DAVE3 function.
;*  This function will be called by the CMSIS SystemInit function. 
;*  If DAVE3 requires an extended SystemInit it will create its own SystemInit_DAVE3
;*  which will overule this weak definition

;*SystemInit_DAVE3
;*  NOP
;*  BX LR

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


                 ENDIF

				 ALIGN
                 END

;******************* (C) COPYRIGHT 2011 Infineon Techonlogies *****END OF FILE*****


