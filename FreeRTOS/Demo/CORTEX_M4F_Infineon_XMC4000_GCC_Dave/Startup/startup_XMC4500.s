/*****************************************************************************/
/* Startup_XMC4500.s: Startup file for XMC4500 device series                 */
/*****************************************************************************/

/* ********************* Version History *********************************** */
/* ***************************************************************************
V1.0 , July 2011, First version for XIP profile
V1.1 , Oct  2011, Program loading code included (GH: b to main changed)
V1.2 , Nov, 01, 2011 GH :Removed second definition of section .Xmc4500.reset
                         at line 186. 
V1.3 , Nov, 16, 2011 GH :Removed PMU0_1_IRQHandler and respective weak function
                         declaration.
V1.4 , Dec, 16, 2011 PKB:Jump to __Xmc4500_start_c reinstated for RTOS integration
V1.5 , Jan, 10, 2012 PKB:Migrated to GCC from ARM
V1.6 , Jan, 16, 2012 PKB:Branch prediction turned off, Parity errors cleared.
V1.7 , Apr, 17, 2012 PKB:Added decision function for PLL initialization  
V1.8 , Apr, 20, 2012 PKB:Handshake with DAVE code engine added  
V1.9 , Jun, 14, 2012 PKB:Removed the handshake protocol towards simplification  
V1.10, Aug, 13, 2012 PKB:Flash Wait states handling  
V1.11, Oct, 11, 2012 PKB:C++ support. Call to global constructors  
V1.12, Jan, 23, 2013 PKB:XMC4 Prefetch bug workaround  
**************************************************************************** */
/**
* @file     Startup_XMC4500.s
*           XMC4000 Device Series
* @version  V1.12
* @date     Jan 2013
*
Copyright (C) 2013 Infineon Technologies AG. All rights reserved.
*
*
* @par
* Infineon Technologies AG (Infineon) is supplying this software for use with 
* Infineon's microcontrollers.  This file can be freely distributed
* within development tools that are supporting such microcontrollers.
*
* @par
* THIS SOFTWARE IS PROVIDED AS IS.  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
* ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
* CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
*
******************************************************************************/
#include <uc_id.inc>

/* ===========START : MACRO DEFINITION MACRO DEFINITION ================== */
/*
 * STEP_AB and below have the prefetch bug. A veneer defined below will first
 * be executed which in turn branches to the final exception handler.
 * 
 * In addition to defining the veneers, the vector table must for these buggy
 * devices contain the veneers. 
 */
 
/* A macro to setup a vector table entry based on STEP ID */ 
.macro Entry Handler
 #if (UC_STEP > STEP_AB)
   .long \Handler
 #else
   .long \Handler\()_Veneer
 #endif
.endm

/* A macro to ease definition of the various handlers based on STEP ID */
#if (UC_STEP <= STEP_AB)
 /* First define the final exception handler */
 .macro Insert_ExceptionHandler Handler_Func 
  .weak \Handler_Func
  .type \Handler_Func, %function
  \Handler_Func:
  B .
  .size \Handler_Func, . - \Handler_Func

  /* And then define a veneer that will branch to the final excp handler */
  .weak \Handler_Func\()_Veneer
  .type \Handler_Func\()_Veneer, %function
  \Handler_Func\()_Veneer:
  LDR     R0, =\Handler_Func
  PUSH    {LR}
  BLX     R0
  POP     {PC}
  .size \Handler_Func\()_Veneer, . - \Handler_Func\()_Veneer
 .endm
#else
 /* No prefetch bug, hence define only the final exception handler */
 .macro Insert_ExceptionHandler Handler_Func 
  .weak \Handler_Func
  .type \Handler_Func, %function
  \Handler_Func:
  B .
  .size \Handler_Func, . - \Handler_Func
 .endm
#endif 
/* =============END : MACRO DEFINITION MACRO DEFINITION ================== */

/* ================== START OF VECTOR TABLE DEFINITION ====================== */
/* Vector Table - This gets programed into VTOR register by onchip BootROM */
    .syntax unified

    .section ".Xmc4500.reset"
    .globl  __Xmc4500_interrupt_vector_cortex_m
    .type   __Xmc4500_interrupt_vector_cortex_m, %object

__Xmc4500_interrupt_vector_cortex_m:
    .long   __Xmc4500_stack             /* Top of Stack                 */
    .long   __Xmc4500_reset_cortex_m    /* Reset Handler                */

    Entry   NMI_Handler                 /* NMI Handler                  */
    Entry   HardFault_Handler           /* Hard Fault Handler           */
    Entry   MemManage_Handler           /* MPU Fault Handler            */
    Entry   BusFault_Handler            /* Bus Fault Handler            */
    Entry   UsageFault_Handler          /* Usage Fault Handler          */
    .long   0                           /* Reserved                     */
    .long   0                           /* Reserved                     */
    .long   0                           /* Reserved                     */
    .long   0                           /* Reserved                     */
    Entry   SVC_Handler                 /* SVCall Handler               */
    Entry   DebugMon_Handler            /* Debug Monitor Handler        */
    .long   0                           /* Reserved                     */
    Entry   PendSV_Handler              /* PendSV Handler               */
    Entry   SysTick_Handler             /* SysTick Handler              */

    /* Interrupt Handlers for Service Requests (SR) from XMC4500 Peripherals */
    Entry   SCU_0_IRQHandler            /* Handler name for SR SCU_0     */
    Entry   ERU0_0_IRQHandler           /* Handler name for SR ERU0_0    */
    Entry   ERU0_1_IRQHandler           /* Handler name for SR ERU0_1    */
    Entry   ERU0_2_IRQHandler           /* Handler name for SR ERU0_2    */
    Entry   ERU0_3_IRQHandler           /* Handler name for SR ERU0_3    */ 
    Entry   ERU1_0_IRQHandler           /* Handler name for SR ERU1_0    */
    Entry   ERU1_1_IRQHandler           /* Handler name for SR ERU1_1    */
    Entry   ERU1_2_IRQHandler           /* Handler name for SR ERU1_2    */
    Entry   ERU1_3_IRQHandler           /* Handler name for SR ERU1_3    */
    .long   0                           /* Not Available                 */
    .long   0                           /* Not Available                 */
    .long   0                           /* Not Available                 */
    Entry   PMU0_0_IRQHandler           /* Handler name for SR PMU0_0    */
    .long   0                           /* Not Available                 */
    Entry   VADC0_C0_0_IRQHandler       /* Handler name for SR VADC0_C0_0  */
    Entry   VADC0_C0_1_IRQHandler       /* Handler name for SR VADC0_C0_1  */
    Entry   VADC0_C0_2_IRQHandler       /* Handler name for SR VADC0_C0_1  */
    Entry   VADC0_C0_3_IRQHandler       /* Handler name for SR VADC0_C0_3  */
    Entry   VADC0_G0_0_IRQHandler       /* Handler name for SR VADC0_G0_0  */
    Entry   VADC0_G0_1_IRQHandler       /* Handler name for SR VADC0_G0_1  */
    Entry   VADC0_G0_2_IRQHandler       /* Handler name for SR VADC0_G0_2  */
    Entry   VADC0_G0_3_IRQHandler       /* Handler name for SR VADC0_G0_3  */
    Entry   VADC0_G1_0_IRQHandler       /* Handler name for SR VADC0_G1_0  */
    Entry   VADC0_G1_1_IRQHandler       /* Handler name for SR VADC0_G1_1  */
    Entry   VADC0_G1_2_IRQHandler       /* Handler name for SR VADC0_G1_2  */
    Entry   VADC0_G1_3_IRQHandler       /* Handler name for SR VADC0_G1_3  */
    Entry   VADC0_G2_0_IRQHandler       /* Handler name for SR VADC0_G2_0  */
    Entry   VADC0_G2_1_IRQHandler       /* Handler name for SR VADC0_G2_1  */
    Entry   VADC0_G2_2_IRQHandler       /* Handler name for SR VADC0_G2_2  */
    Entry   VADC0_G2_3_IRQHandler       /* Handler name for SR VADC0_G2_3  */
    Entry   VADC0_G3_0_IRQHandler       /* Handler name for SR VADC0_G3_0  */
    Entry   VADC0_G3_1_IRQHandler       /* Handler name for SR VADC0_G3_1  */
    Entry   VADC0_G3_2_IRQHandler       /* Handler name for SR VADC0_G3_2  */
    Entry   VADC0_G3_3_IRQHandler       /* Handler name for SR VADC0_G3_3  */
    Entry   DSD0_0_IRQHandler           /* Handler name for SR DSD0_0    */
    Entry   DSD0_1_IRQHandler           /* Handler name for SR DSD0_1    */
    Entry   DSD0_2_IRQHandler           /* Handler name for SR DSD0_2    */
    Entry   DSD0_3_IRQHandler           /* Handler name for SR DSD0_3    */
    Entry   DSD0_4_IRQHandler           /* Handler name for SR DSD0_4    */
    Entry   DSD0_5_IRQHandler           /* Handler name for SR DSD0_5    */
    Entry   DSD0_6_IRQHandler           /* Handler name for SR DSD0_6    */
    Entry   DSD0_7_IRQHandler           /* Handler name for SR DSD0_7    */
    Entry   DAC0_0_IRQHandler           /* Handler name for SR DAC0_0    */
    Entry   DAC0_1_IRQHandler           /* Handler name for SR DAC0_0    */
    Entry   CCU40_0_IRQHandler          /* Handler name for SR CCU40_0   */
    Entry   CCU40_1_IRQHandler          /* Handler name for SR CCU40_1   */
    Entry   CCU40_2_IRQHandler          /* Handler name for SR CCU40_2   */
    Entry   CCU40_3_IRQHandler          /* Handler name for SR CCU40_3   */
    Entry   CCU41_0_IRQHandler          /* Handler name for SR CCU41_0   */
    Entry   CCU41_1_IRQHandler          /* Handler name for SR CCU41_1   */
    Entry   CCU41_2_IRQHandler          /* Handler name for SR CCU41_2   */
    Entry   CCU41_3_IRQHandler          /* Handler name for SR CCU41_3   */
    Entry   CCU42_0_IRQHandler          /* Handler name for SR CCU42_0   */
    Entry   CCU42_1_IRQHandler          /* Handler name for SR CCU42_1   */
    Entry   CCU42_2_IRQHandler          /* Handler name for SR CCU42_2   */
    Entry   CCU42_3_IRQHandler          /* Handler name for SR CCU42_3   */
    Entry   CCU43_0_IRQHandler          /* Handler name for SR CCU43_0   */
    Entry   CCU43_1_IRQHandler          /* Handler name for SR CCU43_1   */
    Entry   CCU43_2_IRQHandler          /* Handler name for SR CCU43_2   */
    Entry   CCU43_3_IRQHandler          /* Handler name for SR CCU43_3   */
    Entry   CCU80_0_IRQHandler          /* Handler name for SR CCU80_0   */
    Entry   CCU80_1_IRQHandler          /* Handler name for SR CCU80_1   */
    Entry   CCU80_2_IRQHandler          /* Handler name for SR CCU80_2   */
    Entry   CCU80_3_IRQHandler          /* Handler name for SR CCU80_3   */
    Entry   CCU81_0_IRQHandler          /* Handler name for SR CCU81_0   */
    Entry   CCU81_1_IRQHandler          /* Handler name for SR CCU81_1   */
    Entry   CCU81_2_IRQHandler          /* Handler name for SR CCU81_2   */
    Entry   CCU81_3_IRQHandler          /* Handler name for SR CCU81_3   */
    Entry   POSIF0_0_IRQHandler         /* Handler name for SR POSIF0_0  */
    Entry   POSIF0_1_IRQHandler         /* Handler name for SR POSIF0_1  */
    Entry   POSIF1_0_IRQHandler         /* Handler name for SR POSIF1_0  */
    Entry   POSIF1_1_IRQHandler         /* Handler name for SR POSIF1_1  */
    .long   0                           /* Not Available                 */
    .long   0                           /* Not Available                 */
    .long   0                           /* Not Available                 */
    .long   0                           /* Not Available                 */
    Entry   CAN0_0_IRQHandler           /* Handler name for SR CAN0_0    */
    Entry   CAN0_1_IRQHandler           /* Handler name for SR CAN0_1    */
    Entry   CAN0_2_IRQHandler           /* Handler name for SR CAN0_2    */
    Entry   CAN0_3_IRQHandler           /* Handler name for SR CAN0_3    */
    Entry   CAN0_4_IRQHandler           /* Handler name for SR CAN0_4    */
    Entry   CAN0_5_IRQHandler           /* Handler name for SR CAN0_5    */
    Entry   CAN0_6_IRQHandler           /* Handler name for SR CAN0_6    */
    Entry   CAN0_7_IRQHandler           /* Handler name for SR CAN0_7    */
    Entry   USIC0_0_IRQHandler          /* Handler name for SR USIC0_0   */
    Entry   USIC0_1_IRQHandler          /* Handler name for SR USIC0_1   */
    Entry   USIC0_2_IRQHandler          /* Handler name for SR USIC0_2   */
    Entry   USIC0_3_IRQHandler          /* Handler name for SR USIC0_3   */
    Entry   USIC0_4_IRQHandler          /* Handler name for SR USIC0_4   */
    Entry   USIC0_5_IRQHandler          /* Handler name for SR USIC0_5   */
    Entry   USIC1_0_IRQHandler          /* Handler name for SR USIC1_0   */
    Entry   USIC1_1_IRQHandler          /* Handler name for SR USIC1_1   */
    Entry   USIC1_2_IRQHandler          /* Handler name for SR USIC1_2   */
    Entry   USIC1_3_IRQHandler          /* Handler name for SR USIC1_3   */
    Entry   USIC1_4_IRQHandler          /* Handler name for SR USIC1_4   */
    Entry   USIC1_5_IRQHandler          /* Handler name for SR USIC1_5   */
    Entry   USIC2_0_IRQHandler          /* Handler name for SR USIC2_0   */
    Entry   USIC2_1_IRQHandler          /* Handler name for SR USIC2_1   */
    Entry   USIC2_2_IRQHandler          /* Handler name for SR USIC2_2   */
    Entry   USIC2_3_IRQHandler          /* Handler name for SR USIC2_3   */
    Entry   USIC2_4_IRQHandler          /* Handler name for SR USIC2_4   */
    Entry   USIC2_5_IRQHandler          /* Handler name for SR USIC2_5   */
    Entry   LEDTS0_0_IRQHandler         /* Handler name for SR LEDTS0_0  */
    .long   0                           /* Not Available                 */
    Entry   FCE0_0_IRQHandler           /* Handler name for SR FCE0_0    */
    Entry   GPDMA0_0_IRQHandler         /* Handler name for SR GPDMA0_0  */
    Entry   SDMMC0_0_IRQHandler         /* Handler name for SR SDMMC0_0  */
    Entry   USB0_0_IRQHandler           /* Handler name for SR USB0_0    */
    Entry   ETH0_0_IRQHandler           /* Handler name for SR ETH0_0    */
    .long   0                           /* Not Available                 */
    Entry   GPDMA1_0_IRQHandler         /* Handler name for SR GPDMA1_0  */
    .long   0                           /* Not Available                 */

    .size  __Xmc4500_interrupt_vector_cortex_m, . - __Xmc4500_interrupt_vector_cortex_m
/* ================== END OF VECTOR TABLE DEFINITION ======================= */

/* ================== START OF VECTOR ROUTINES ============================= */
    .thumb
/* ======================================================================== */
/* Reset Handler */

    .thumb_func
    .globl  __Xmc4500_reset_cortex_m
    .type   __Xmc4500_reset_cortex_m, %function
__Xmc4500_reset_cortex_m:
    .fnstart

    /* C routines are likely to be called. Setup the stack now */
    /* This is already setup by BootROM,hence this step is optional */ 
    LDR SP,=__Xmc4500_stack

    /* Clock tree, External memory setup etc may be done here */    
    LDR     R0, =SystemInit
    BLX     R0

/* 
   SystemInit_DAVE3() is provided by DAVE3 code generation engine. It is  
   weakly defined here though for a potential override.
*/
    LDR     R0, =SystemInit_DAVE3     
    BLX     R0

    B       __Xmc4500_Program_Loader 
    
    .pool
    .cantunwind
    .fnend
    .size   __Xmc4500_reset_cortex_m,.-__Xmc4500_reset_cortex_m
/* ======================================================================== */
/* __Xmc4500_reset must yield control to __Xmc4500_Program_Loader before control
   to C land is given */
   .section .Xmc4500.postreset,"x",%progbits
   __Xmc4500_Program_Loader:
   .fnstart
   /* Memories are accessible now*/
   
   /* DATA COPY */
   /* R0 = Start address, R1 = Destination address, R2 = Size */
   LDR R0, =eROData
   LDR R1, =__Xmc4500_sData
   LDR R2, =__Xmc4500_Data_Size

   /* Is there anything to be copied? */
   CMP R2,#0
   BEQ SKIPCOPY
   
   /* For bytecount less than 4, at least 1 word must be copied */
   CMP R2,#4
   BCS STARTCOPY
   
   /* Byte count < 4 ; so bump it up */
   MOV R2,#4

STARTCOPY:
   /* 
      R2 contains byte count. Change it to word count. It is ensured in the 
      linker script that the length is always word aligned.
   */
   LSR R2,R2,#2 /* Divide by 4 to obtain word count */

   /* The proverbial loop from the schooldays */
COPYLOOP:
   LDR R3,[R0]
   STR R3,[R1]
   SUBS R2,#1
   BEQ SKIPCOPY
   ADD R0,#4
   ADD R1,#4
   B COPYLOOP
    
SKIPCOPY:
   /* BSS CLEAR */
   LDR R0, =__Xmc4500_sBSS     /* Start of BSS */
   LDR R1, =__Xmc4500_BSS_Size /* BSS size in bytes */

   /* Find out if there are items assigned to BSS */   
   CMP R1,#0 
   BEQ SKIPCLEAR

   /* At least 1 word must be copied */
   CMP R1,#4
   BCS STARTCLEAR
   
   /* Byte count < 4 ; so bump it up to a word*/
   MOV R1,#4

STARTCLEAR:
   LSR R1,R1,#2            /* BSS size in words */
   
   MOV R2,#0
CLEARLOOP:
   STR R2,[R0]
   SUBS R1,#1
   BEQ SKIPCLEAR
   ADD R0,#4
   B CLEARLOOP
    
SKIPCLEAR:
   /* Remap vector table */
   /* This is already setup by BootROM,hence this step is optional */ 
   LDR R0, =__Xmc4500_interrupt_vector_cortex_m 
   LDR R1, =SCB_VTOR
   STR R0,[R1]
   
   /* Update System Clock */
   LDR R0,=SystemCoreClockUpdate
   BLX R0
 
   /* C++ : Call global constructors */
   LDR R0,=__libc_init_array
   BLX R0

   /* Reset stack pointer before zipping off to user application, Optional */
   LDR SP,=__Xmc4500_stack 
   MOV R0,#0
   MOV R1,#0
   LDR PC, =main
   .pool
   .cantunwind
   .fnend
   .size   __Xmc4500_Program_Loader,.-__Xmc4500_Program_Loader
/* ======================================================================== */
/* ========== START OF EXCEPTION HANDLER DEFINITION ======================== */


/* Default exception Handlers - Users may override this default functionality by
   defining handlers of the same name in their C code */
    .thumb
    .text

     Insert_ExceptionHandler NMI_Handler
/* ======================================================================== */
     Insert_ExceptionHandler HardFault_Handler
/* ======================================================================== */
     Insert_ExceptionHandler MemManage_Handler
/* ======================================================================== */
     Insert_ExceptionHandler BusFault_Handler
/* ======================================================================== */
     Insert_ExceptionHandler UsageFault_Handler
/* ======================================================================== */
     Insert_ExceptionHandler SVC_Handler
/* ======================================================================== */
     Insert_ExceptionHandler DebugMon_Handler
/* ======================================================================== */
     Insert_ExceptionHandler PendSV_Handler
/* ======================================================================== */
     Insert_ExceptionHandler SysTick_Handler

/* ============= END OF EXCEPTION HANDLER DEFINITION ======================== */

/* ============= START OF INTERRUPT HANDLER DEFINITION ====================== */

/* IRQ Handlers */
     Insert_ExceptionHandler SCU_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU0_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU0_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU1_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU1_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU1_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ERU1_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler PMU0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_C0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_C0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_C0_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_C0_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G0_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G0_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G1_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G1_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G1_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G1_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G2_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G2_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G2_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G2_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G3_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G3_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G3_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler VADC0_G3_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_4_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_5_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_6_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DSD0_7_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DAC0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler DAC0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU40_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU40_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU40_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU40_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU41_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU41_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU41_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU41_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU42_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU42_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU42_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU42_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU43_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU43_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU43_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU43_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU80_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU80_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU80_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU80_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU81_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU81_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU81_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CCU81_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler POSIF0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler POSIF0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler POSIF1_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler POSIF1_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_4_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_5_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_6_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler CAN0_7_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC0_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC0_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC0_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC0_4_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC0_5_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC1_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC1_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC1_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC1_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC1_4_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC1_5_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC2_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC2_1_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC2_2_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC2_3_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC2_4_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USIC2_5_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler LEDTS0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler FCE0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler GPDMA0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler SDMMC0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler USB0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler ETH0_0_IRQHandler
/* ======================================================================== */
     Insert_ExceptionHandler GPDMA1_0_IRQHandler
/* ======================================================================== */
/* ======================================================================== */

/* ============= END OF INTERRUPT HANDLER DEFINITION ====================== */

/* ======== Decision function queried by CMSIS startup for PLL setup ====== */
/* In the absence of DAVE code engine, CMSIS SystemInit() must perform clock 
   tree setup. 
   
   This decision routine defined here will always return TRUE.
   
   When overridden by a definition defined in DAVE code engine, this routine
   returns FALSE indicating that the code engine has performed the clock setup
*/   
    .weak   AllowPLLInitByStartup
    .type   AllowPLLInitByStartup, %function
AllowPLLInitByStartup:
    MOV R0,#1
    BX LR
    .size   AllowPLLInitByStartup, . - AllowPLLInitByStartup

/* ======  Definition of the default weak SystemInit_DAVE3 function =========
If DAVE3 requires an extended SystemInit it will create its own version of
SystemInit_DAVE3 which overrides this weak definition. Example includes
setting up of external memory interfaces.
*/
     .section ".XmcStartup"
     .weak SystemInit_DAVE3
     .type SystemInit_DAVE3, %function
SystemInit_DAVE3:
     NOP
     BX LR
     .size SystemInit_DAVE3, . - SystemInit_DAVE3
/* ======================================================================== */
/* ======================================================================== */

/* ======================== Data references =============================== */
.equ  SCB_VTOR,       0xE000ED08
.equ  PREF_PCON,      0x58004000
.equ  SCU_GCU_PEEN,   0x5000413C
.equ  SCU_GCU_PEFLAG, 0x50004150
.equ  FLASH_FCON,     0x58002014

    .end
