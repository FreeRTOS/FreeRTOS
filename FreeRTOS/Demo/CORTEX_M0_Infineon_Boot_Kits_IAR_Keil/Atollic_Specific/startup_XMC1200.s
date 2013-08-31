/**
*****************************************************************************
**
**  File        : startup_XMC1200.s
**
**  Abstract    : This assembler file contains interrupt vector and
**                startup code for ARM.
**
**  Functions   : Reset_Handler
**                Default_Handler
**                XMCVeneer code
**
**  Target      : Infineon $(DEVICE) Device 
**
**  Environment : Atollic TrueSTUDIO(R)
**
**  Distribution: The file is distributed “as is,” without any warranty
**                of any kind.
**
**  (c)Copyright Atollic AB.
**  You may use this file as-is or modify it according to the needs of your
**  project. This file may only be built (assembled or compiled and linked)
**  using the Atollic TrueSTUDIO(R) product. The use of this file together
**  with other tools than Atollic TrueSTUDIO(R) is not permitted.
**
*****************************************************************************
*/

#ifdef DAVE_CE
#include <Device_Data.h>
#else
#define CLKVAL1_SSW 0x80000000
#define CLKVAL2_SSW 0x80000000
#endif

  .syntax unified
  .cpu cortex-m0
  .fpu softvfp
  .thumb

.global Reset_Handler
.global InterruptVector
.global Default_Handler

/* Linker script definitions */
/* start address for the initialization values of the .data section */
.word _sidata
/* start address for the .data section */
.word _sdata
/* end address for the .data section */
.word _edata
/* start address for the .bss section */
.word _sbss
/* end address for the .bss section */
.word _ebss

.word VeneerLoadAddr
.word VeneerStart
.word VeneerSize


/**
**===========================================================================
**  Program - Reset_Handler
**  Abstract: This code gets called after reset.
**===========================================================================
*/
  .section  .text.Reset_Handler,"ax", %progbits
  .type Reset_Handler, %function
Reset_Handler:
  /* Set stack pointer */
  ldr   r0, =_estack
  mov   sp, r0

  /* Branch to SystemInit function */
  bl SystemInit

  /* Copy data initialization values */
  ldr r1,=_sidata
  ldr r2,=_sdata
  ldr r3,=_edata
  b cmpdata
CopyLoop:
  ldr r0, [r1]
  str r0, [r2]
  adds r1, r1, #4
  adds r2, r2, #4
cmpdata:
  cmp r2, r3
  blt CopyLoop

  /* Clear BSS section */
  movs r0, #0
  ldr r2,=_sbss
  ldr r3,=_ebss
  b cmpbss
ClearLoop:
  str r0, [r2]
  adds r2, r2, #4
cmpbss:
  cmp r2, r3
  blt ClearLoop

  /* VENEER COPY */
  /* R0 = Start address, R1 = Destination address, R2 = Size */
  ldr r0, =VeneerLoadAddr
  ldr r1, =VeneerStart
  ldr r2, =VeneerSize

STARTVENEERCOPY:
  /* R2 contains byte count. Change it to word count. It is ensured in the
     linker script that the length is always word aligned.
  */
  lsrs r2,r2,#2 /* Divide by 4 to obtain word count */
  beq SKIPVENEERCOPY

  /* The proverbial loop from the schooldays */
VENEERCOPYLOOP:
  ldr r3,[R0]
  str r3,[R1]
  subs r2,#1
  beq SKIPVENEERCOPY
  adds r0,#4
  adds r1,#4
  b VENEERCOPYLOOP

SKIPVENEERCOPY:
  /* Update System Clock */
  ldr r0,=SystemCoreClockUpdate
  blx r0

  /* Call static constructors */
  bl __libc_init_array

  /* Branch to main */
  bl main

  /* If main returns, branch to Default_Handler. */
  b Default_Handler

  .size  Reset_Handler, .-Reset_Handler

/**
**===========================================================================
**  Program - Default_Handler
**  Abstract: This code gets called when the processor receives an
**    unexpected interrupt.
**===========================================================================
*/
  .section  .text.Default_Handler,"ax", %progbits
Default_Handler:
  b  Default_Handler

  .size  Default_Handler, .-Default_Handler

/**
**===========================================================================
**  Interrupt vector table
**===========================================================================
*/
  .section .isr_vector,"a", %progbits
  .globl  InterruptVector
  .type   InterruptVector, %object

InterruptVector:
  .word _estack                   /* 0 - Stack pointer */
  .word Reset_Handler             /* 1 - Reset */
  .word NMI_Handler               /* 2 - NMI  */
  .word HardFault_Handler         /* 3 - Hard fault */
  .word CLKVAL1_SSW               /* Clock configuration value  */
  .word CLKVAL2_SSW               /* Clock gating configuration */

  .size  InterruptVector, . - InterruptVector

/**
**===========================================================================
**  Weak interrupt handlers redirected to Default_Handler. These can be
**  overridden in user code.
**===========================================================================
*/
  .weak NMI_Handler
  .thumb_set NMI_Handler, Default_Handler

  .weak HardFault_Handler
  .thumb_set HardFault_Handler, Default_Handler

  .weak SVC_Handler
  .thumb_set SVC_Handler, Default_Handler

  .weak PendSV_Handler
  .thumb_set PendSV_Handler, Default_Handler

  .weak SysTick_Handler
  .thumb_set SysTick_Handler, Default_Handler

/* ============= START OF INTERRUPT HANDLER DEFINITION ====================== */

/* IRQ Handlers */
    .weak   SCU_0_IRQHandler
    .type   SCU_0_IRQHandler, %function
SCU_0_IRQHandler:
    B       .
    .size   SCU_0_IRQHandler, . - SCU_0_IRQHandler
/* ======================================================================== */
    .weak   SCU_1_IRQHandler
    .type   SCU_1_IRQHandler, %function
SCU_1_IRQHandler:
    B       .
    .size   SCU_1_IRQHandler, . - SCU_1_IRQHandler
/* ======================================================================== */
    .weak   SCU_2_IRQHandler
    .type   SCU_2_IRQHandler, %function
SCU_2_IRQHandler:
    B       .
    .size   SCU_2_IRQHandler, . - SCU_2_IRQHandler
/* ======================================================================== */
    .weak   ERU0_0_IRQHandler
    .type   ERU0_0_IRQHandler, %function
ERU0_0_IRQHandler:
    B       .
    .size   ERU0_0_IRQHandler, . - ERU0_0_IRQHandler
/* ======================================================================== */
    .weak   ERU0_1_IRQHandler
    .type   ERU0_1_IRQHandler, %function
ERU0_1_IRQHandler:
    B       .
    .size   ERU0_1_IRQHandler, . - ERU0_1_IRQHandler
/* ======================================================================== */
    .weak   ERU0_2_IRQHandler
    .type   ERU0_2_IRQHandler, %function
ERU0_2_IRQHandler:
    B       .
    .size   ERU0_2_IRQHandler, . - ERU0_2_IRQHandler
/* ======================================================================== */
    .weak   ERU0_3_IRQHandler
    .type   ERU0_3_IRQHandler, %function
ERU0_3_IRQHandler:
    B       .
    .size   ERU0_3_IRQHandler, . - ERU0_3_IRQHandler
/* ======================================================================== */
    .weak   MATH0_0_IRQHandler
    .type   MATH0_0_IRQHandler, %function
MATH0_0_IRQHandler:
    B       .
    .size   MATH0_0_IRQHandler, . - MATH0_0_IRQHandler
/* ======================================================================== */
    .weak   VADC0_C0_0_IRQHandler
    .type   VADC0_C0_0_IRQHandler , %function
VADC0_C0_0_IRQHandler:
    B       .
    .size   VADC0_C0_0_IRQHandler , . - VADC0_C0_0_IRQHandler
/* ======================================================================== */
    .weak   VADC0_C0_1_IRQHandler
    .type   VADC0_C0_1_IRQHandler , %function
VADC0_C0_1_IRQHandler:
    B       .
    .size   VADC0_C0_1_IRQHandler , . - VADC0_C0_1_IRQHandler
/* ======================================================================== */
    .weak   VADC0_G0_0_IRQHandler
    .type   VADC0_G0_0_IRQHandler, %function
VADC0_G0_0_IRQHandler:
    B       .
    .size   VADC0_G0_0_IRQHandler, . - VADC0_G0_0_IRQHandler
/* ======================================================================== */
    .weak   VADC0_G0_1_IRQHandler
    .type   VADC0_G0_1_IRQHandler, %function
VADC0_G0_1_IRQHandler:
    B       .
    .size   VADC0_G0_1_IRQHandler, . - VADC0_G0_1_IRQHandler
/* ======================================================================== */
    .weak   VADC0_G1_0_IRQHandler
    .type   VADC0_G1_0_IRQHandler, %function
VADC0_G1_0_IRQHandler:
    B       .
    .size   VADC0_G1_0_IRQHandler, . - VADC0_G1_0_IRQHandler
/* ======================================================================== */
    .weak   VADC0_G1_1_IRQHandler
    .type   VADC0_G1_1_IRQHandler, %function
VADC0_G1_1_IRQHandler:
    B       .
    .size   VADC0_G1_1_IRQHandler, . - VADC0_G1_1_IRQHandler
/* ======================================================================== */
    .weak   CCU40_0_IRQHandler
    .type   CCU40_0_IRQHandler, %function
CCU40_0_IRQHandler:
    B       .
    .size   CCU40_0_IRQHandler, . - CCU40_0_IRQHandler
/* ======================================================================== */
    .weak   CCU40_1_IRQHandler
    .type   CCU40_1_IRQHandler, %function

CCU40_1_IRQHandler:
    B       .
    .size   CCU40_1_IRQHandler, . - CCU40_1_IRQHandler
/* ======================================================================== */
    .weak   CCU40_2_IRQHandler
    .type   CCU40_2_IRQHandler, %function
CCU40_2_IRQHandler:
    B       .
    .size   CCU40_2_IRQHandler, . - CCU40_2_IRQHandler
/* ======================================================================== */
    .weak   CCU40_3_IRQHandler
    .type   CCU40_3_IRQHandler, %function
CCU40_3_IRQHandler:
    B       .
    .size   CCU40_3_IRQHandler, . - CCU40_3_IRQHandler
/* ======================================================================== */
    .weak   CCU80_0_IRQHandler
    .type   CCU80_0_IRQHandler, %function
CCU80_0_IRQHandler:
    B       .
    .size   CCU80_0_IRQHandler, . - CCU80_0_IRQHandler
/* ======================================================================== */
    .weak   CCU80_1_IRQHandler
    .type   CCU80_1_IRQHandler, %function
CCU80_1_IRQHandler:
    B       .
    .size   CCU80_1_IRQHandler, . - CCU80_1_IRQHandler
/* ======================================================================== */
    .weak   POSIF0_0_IRQHandler
    .type   POSIF0_0_IRQHandler, %function

POSIF0_0_IRQHandler:
    B       .
    .size   POSIF0_0_IRQHandler, . - POSIF0_0_IRQHandler
/* ======================================================================== */
    .weak   POSIF0_1_IRQHandler
    .type   POSIF0_1_IRQHandler, %function
POSIF0_1_IRQHandler:
    B       .
    .size   POSIF0_1_IRQHandler, . - POSIF0_1_IRQHandler
/* ======================================================================== */
    .weak   USIC0_0_IRQHandler
    .type   USIC0_0_IRQHandler, %function
USIC0_0_IRQHandler:
    B       .
    .size   USIC0_0_IRQHandler, . - USIC0_0_IRQHandler
/* ======================================================================== */
    .weak   USIC0_1_IRQHandler
    .type   USIC0_1_IRQHandler, %function
USIC0_1_IRQHandler:
    B       .
    .size   USIC0_1_IRQHandler, . - USIC0_1_IRQHandler
/* ======================================================================== */
    .weak   USIC0_2_IRQHandler
    .type   USIC0_2_IRQHandler, %function
USIC0_2_IRQHandler:
    B       .
    .size   USIC0_2_IRQHandler, . - USIC0_2_IRQHandler
/* ======================================================================== */
    .weak   USIC0_3_IRQHandler
    .type   USIC0_3_IRQHandler, %function
USIC0_3_IRQHandler:
    B       .
    .size   USIC0_3_IRQHandler, . - USIC0_3_IRQHandler
/* ======================================================================== */
    .weak   USIC0_4_IRQHandler
    .type   USIC0_4_IRQHandler, %function
USIC0_4_IRQHandler:
    B       .
    .size   USIC0_4_IRQHandler, . - USIC0_4_IRQHandler
/* ======================================================================== */
    .weak   USIC0_5_IRQHandler
    .type   USIC0_5_IRQHandler, %function
USIC0_5_IRQHandler:
    B       .
    .size   USIC0_5_IRQHandler, . - USIC0_5_IRQHandler
/* ======================================================================== */
    .weak   LEDTS0_0_IRQHandler
    .type   LEDTS0_0_IRQHandler, %function
LEDTS0_0_IRQHandler:
    B       .
    .size   LEDTS0_0_IRQHandler, . - LEDTS0_0_IRQHandler
/* ======================================================================== */
    .weak   LEDTS1_0_IRQHandler
    .type   LEDTS1_0_IRQHandler, %function
LEDTS1_0_IRQHandler:
    B       .
    .size   LEDTS1_0_IRQHandler, . - LEDTS1_0_IRQHandler
/* ======================================================================== */
    .weak   BCCU0_0_IRQHandler
    .type   BCCU0_0_IRQHandler, %function
BCCU0_0_IRQHandler:
    B       .
    .size   BCCU0_0_IRQHandler, . - BCCU0_0_IRQHandler
/* ======================================================================== */
/* ======================================================================== */

/* ==================VENEERS VENEERS VENEERS VENEERS VENEERS=============== */
    .section ".XmcVeneerCode","ax",%progbits
.globl HardFault_Veneer
HardFault_Veneer:
    LDR R0, =HardFault_Handler
    MOV PC,R0
    .long 0
    .long 0
    .long 0
    .long 0
    .long 0
    .long 0
    .long 0

/* ======================================================================== */
.globl SVC_Veneer
SVC_Veneer:
    LDR R0, =SVC_Handler
    MOV PC,R0
    .long 0
    .long 0
/* ======================================================================== */
.globl PendSV_Veneer
PendSV_Veneer:
    LDR R0, =PendSV_Handler
    MOV PC,R0
/* ======================================================================== */
.globl SysTick_Veneer
SysTick_Veneer:
    LDR R0, =SysTick_Handler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_0_Veneer
SCU_0_Veneer:
    LDR R0, =SCU_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_1_Veneer
SCU_1_Veneer:
    LDR R0, =SCU_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_2_Veneer
SCU_2_Veneer:
    LDR R0, =SCU_2_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_3_Veneer
SCU_3_Veneer:
    LDR R0, =ERU0_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_4_Veneer
SCU_4_Veneer:
    LDR R0, =ERU0_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_5_Veneer
SCU_5_Veneer:
    LDR R0, =ERU0_2_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_6_Veneer
SCU_6_Veneer:
    LDR R0, =ERU0_3_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl SCU_7_Veneer
SCU_7_Veneer:
    LDR R0, =MATH0_0_IRQHandler
    MOV PC,R0
    .long 0
/* ======================================================================== */
.globl VADC0_C0_0_Veneer
VADC0_C0_0_Veneer:
    LDR R0, =VADC0_C0_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl VADC0_C0_1_Veneer
VADC0_C0_1_Veneer:
    LDR R0, =VADC0_C0_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl VADC0_G0_0_Veneer
VADC0_G0_0_Veneer:
    LDR R0, =VADC0_G0_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl VADC0_G0_1_Veneer
VADC0_G0_1_Veneer:
    LDR R0, =VADC0_G0_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl VADC0_G1_0_Veneer
VADC0_G1_0_Veneer:
    LDR R0, =VADC0_G1_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl VADC0_G1_1_Veneer
VADC0_G1_1_Veneer:
    LDR R0, =VADC0_G1_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl CCU40_0_Veneer
CCU40_0_Veneer:
    LDR R0, =CCU40_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl CCU40_1_Veneer
CCU40_1_Veneer:
    LDR R0, =CCU40_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl CCU40_2_Veneer
CCU40_2_Veneer:
    LDR R0, =CCU40_2_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl CCU40_3_Veneer
CCU40_3_Veneer:
    LDR R0, =CCU40_3_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl CCU80_0_Veneer
CCU80_0_Veneer:
    LDR R0, =CCU80_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl CCU80_1_Veneer
CCU80_1_Veneer:
    LDR R0, =CCU80_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl POSIF0_0_Veneer
POSIF0_0_Veneer:
    LDR R0, =POSIF0_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl POSIF0_1_Veneer
POSIF0_1_Veneer:
    LDR R0, =POSIF0_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl USIC0_0_Veneer
USIC0_0_Veneer:
    LDR R0, =USIC0_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl USIC0_1_Veneer
USIC0_1_Veneer:
    LDR R0, =USIC0_1_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl USIC0_2_Veneer
USIC0_2_Veneer:
    LDR R0, =USIC0_2_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl USIC0_3_Veneer
USIC0_3_Veneer:
    LDR R0, =USIC0_3_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl USIC0_4_Veneer
USIC0_4_Veneer:
    LDR R0, =USIC0_4_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl USIC0_5_Veneer
USIC0_5_Veneer:
    LDR R0, =USIC0_5_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl LEDTS0_0_Veneer
LEDTS0_0_Veneer:
    LDR R0, =LEDTS0_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
.globl LEDTS1_0_Veneer
LEDTS1_0_Veneer:
    LDR R0, =LEDTS1_0_IRQHandler
    MOV PC,R0
/* ======================================================================== */
    .globl BCCU0_0_Veneer
BCCU0_0_Veneer:
    LDR R0, =BCCU0_0_IRQHandler
    MOV PC,R0

/* ======================================================================== */

/* ===== Decision function queried by CMSIS startup for Clock tree setup === */
/* In the absence of DAVE code engine, CMSIS SystemInit() must perform clock
   tree setup.

   This decision routine defined here will always return TRUE.

   When overridden by a definition defined in DAVE code engine, this routine
   returns FALSE indicating that the code engine has performed the clock setup
*/
     .section ".XmcStartup"
    .weak   AllowClkInitByStartup
    .type   AllowClkInitByStartup, %function
AllowClkInitByStartup:
    MOVS R0,#1
    BX LR
    .size   AllowClkInitByStartup, . - AllowClkInitByStartup

/* ======  Definition of the default weak SystemInit_DAVE3 function =========
If DAVE3 requires an extended SystemInit it will create its own version of
SystemInit_DAVE3 which overrides this weak definition. Example includes
setting up of external memory interfaces.
*/
     .weak SystemInit_DAVE3
     .type SystemInit_DAVE3, %function
SystemInit_DAVE3:
     NOP
     BX LR
     .size SystemInit_DAVE3, . - SystemInit_DAVE3

  .end
