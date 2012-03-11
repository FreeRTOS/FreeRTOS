/**
*****************************************************************************
**
**  File        : startup_XMC4500.s
**
**  Abstract    : This assembler file contains interrupt vector and
**                startup code for Infineon XMC4500.
**
**  Functions   : Reset_Handler
**                Default_Handler
**
**  Target      : ARM Cortex-M4
**
**  Environment : Atollic TrueSTUDIO(R)
**
**  Distribution: The file is distributed “as is,” without any warranty
**                of any kind.
**
**  (c)Copyright Atollic AB.
**  You may use this file as-is or modify it according to the needs of your
**  project. Distribution of this file (unmodified or modified) is not
**  permitted. Atollic AB permit registered Atollic TrueSTUDIO(R) users the
**  rights to distribute the assembled, compiled & linked contents of this
**  file as part of an application binary file, provided that it is built
**  using the Atollic TrueSTUDIO(R) toolchain.
**
*****************************************************************************
*/

/**
**===========================================================================
**  Revisions
**===========================================================================
**       Date        Modification
**       2011-12-30  First issue.
**===========================================================================
*/

/**
**===========================================================================
**  Definitions
**===========================================================================
*/
    .syntax unified
    .cpu cortex-m4
    .fpu softvfp
    .thumb

.global	g_pfnVectors
.global	Default_Handler

/* Linker script definitions */
/* start address for the initialization values of the .data section */
.word	_sidata
/* start address for the .data section */
.word	_sdata
/* end address for the .data section */
.word	_edata
/* start address for the .bss section */
.word	_sbss
/* end address for the .bss section */
.word	_ebss

.equ  PREF_PCON,      0x58004000
.equ  SCU_GCU_PEEN,   0x5000413C
.equ  SCU_GCU_PEFLAG, 0x50004150

/**
**===========================================================================
**  Program - Reset_Handler
**  Abstract: This code gets called after a reset event.
**    1. Copy .data section from ROM to RAM
**    2. Clear .bss section (Zero init)
**    3. Call system initialzation routine
**    4. Run static constructors
**    5. Enter main
**    6. Loop forever if returning from main
**===========================================================================
*/
  .section	.text.Reset_Handler
  .weak	Reset_Handler
  .type	Reset_Handler, %function
Reset_Handler:

  /* Remap vector table - added by RB. */
  ldr r0, =g_pfnVectors
  ldr r1, =0xE000ED08 /* VTOR register */
  str r0,[r1]

  /* Disable Branch prediction */
  ldr r0,=PREF_PCON
  ldr r1,[r0]
  orr r1,r1,#0x00010000
  str r1,[r0]

  /* Clear existing parity errors if any */
  ldr r0,=SCU_GCU_PEFLAG
  ldr r1,=0xFFFFFFFF
  str r1,[r0]

  /* Disable parity */
  ldr r0,=SCU_GCU_PEEN
  mov r1,#0
  str r1,[R0]

  /* Enable un-aligned memory access - added by RB. */
  ldr r1, =0xE000ED14
  ldr.w r0,[R1,#0x0]
  bic r0,r0,#0x8
  str.w r0,[r1,#0x0]


  ldr sp, =_estack    /* set stack pointer */

  /* 1. copy .data section (Copy from ROM to RAM) */
  movs r1, #0
  b LoopCopyDataInit

CopyDataInit:
  ldr r3, =_sidata
  ldr r3, [r3, r1]
  str r3, [r0, r1]
  adds r1, r1, #4

LoopCopyDataInit:
  ldr r0, =_sdata
  ldr r3, =_edata
  adds r2, r0, r1
  cmp r2, r3
  bcc CopyDataInit
  ldr r2, =_sbss
  b LoopFillZerobss

  /* 2. Clear .bss section (Zero init) */
FillZerobss:
  movs r3, #0
  str r3, [r2], #4

LoopFillZerobss:
  ldr r3, = _ebss
  cmp r2, r3
  bcc FillZerobss

  /* 3. Call system initialzation routine */
  bl SystemInit

  /* 4. Run static constructors  */
  bl __libc_init_array

  /* 5. Enter main  */
  bl main

  /* 6. Loop forever if returning from main */
LoopForever:
  b LoopForever


.size	Reset_Handler, .-Reset_Handler

/**
**===========================================================================
**  Program - Default_Handler
**  Abstract: This code gets called when the processor receives an
**    unexpected interrupt.
**===========================================================================
*/
  .section	.text.Default_Handler,"ax",%progbits
Default_Handler:
InfiniteLoop:
  b	InfiniteLoop
  .size	Default_Handler, .-Default_Handler

/**
**===========================================================================
**  Reset, Exception, and Interrupt vectors
**===========================================================================
*/
  .section	.isr_vector,"a",%progbits
  .type	g_pfnVectors, %object
  .size	g_pfnVectors, .-g_pfnVectors


g_pfnVectors:
  /* Processor exception vectors */
  .word	_estack
  .word	Reset_Handler
  .word	NMI_Handler
  .word	HardFault_Handler
  .word	MemManage_Handler
  .word	BusFault_Handler
  .word	UsageFault_Handler
  .word	0
  .word	0
  .word	0
  .word	0
  .word	SVC_Handler
  .word	DebugMon_Handler
  .word	0
  .word	PendSV_Handler
  .word	SysTick_Handler

  /* Interrupt Handlers for XMC4500 Peripherals */
  .word SCU_0_IRQHandler            /* Handler name for SR SCU_0     */
  .word ERU0_0_IRQHandler           /* Handler name for SR ERU0_0    */
  .word ERU0_1_IRQHandler           /* Handler name for SR ERU0_1    */
  .word ERU0_2_IRQHandler           /* Handler name for SR ERU0_2    */
  .word ERU0_3_IRQHandler           /* Handler name for SR ERU0_3    */
  .word ERU1_0_IRQHandler           /* Handler name for SR ERU1_0    */
  .word ERU1_1_IRQHandler           /* Handler name for SR ERU1_1    */
  .word ERU1_2_IRQHandler           /* Handler name for SR ERU1_2    */
  .word ERU1_3_IRQHandler           /* Handler name for SR ERU1_3    */
  .word 0                           /* Not Available                 */
  .word 0                           /* Not Available                 */
  .word 0                           /* Not Available                 */
  .word PMU0_0_IRQHandler           /* Handler name for SR PMU0_0    */
  .word 0                           /* Not Available                 */
  .word VADC0_C0_0_IRQHandler       /* Handler name for SR VADC0_C0_0  */
  .word VADC0_C0_1_IRQHandler       /* Handler name for SR VADC0_C0_1  */
  .word VADC0_C0_2_IRQHandler       /* Handler name for SR VADC0_C0_1  */
  .word VADC0_C0_3_IRQHandler       /* Handler name for SR VADC0_C0_3  */
  .word VADC0_G0_0_IRQHandler       /* Handler name for SR VADC0_G0_0  */
  .word VADC0_G0_1_IRQHandler       /* Handler name for SR VADC0_G0_1  */
  .word VADC0_G0_2_IRQHandler       /* Handler name for SR VADC0_G0_2  */
  .word VADC0_G0_3_IRQHandler       /* Handler name for SR VADC0_G0_3  */
  .word VADC0_G1_0_IRQHandler       /* Handler name for SR VADC0_G1_0  */
  .word VADC0_G1_1_IRQHandler       /* Handler name for SR VADC0_G1_1  */
  .word VADC0_G1_2_IRQHandler       /* Handler name for SR VADC0_G1_2  */
  .word VADC0_G1_3_IRQHandler       /* Handler name for SR VADC0_G1_3  */
  .word VADC0_G2_0_IRQHandler       /* Handler name for SR VADC0_G2_0  */
  .word VADC0_G2_1_IRQHandler       /* Handler name for SR VADC0_G2_1  */
  .word VADC0_G2_2_IRQHandler       /* Handler name for SR VADC0_G2_2  */
  .word VADC0_G2_3_IRQHandler       /* Handler name for SR VADC0_G2_3  */
  .word VADC0_G3_0_IRQHandler       /* Handler name for SR VADC0_G3_0  */
  .word VADC0_G3_1_IRQHandler       /* Handler name for SR VADC0_G3_1  */
  .word VADC0_G3_2_IRQHandler       /* Handler name for SR VADC0_G3_2  */
  .word VADC0_G3_3_IRQHandler       /* Handler name for SR VADC0_G3_3  */
  .word DSD0_0_IRQHandler           /* Handler name for SR DSD0_0    */
  .word DSD0_1_IRQHandler           /* Handler name for SR DSD0_1    */
  .word DSD0_2_IRQHandler           /* Handler name for SR DSD0_2    */
  .word DSD0_3_IRQHandler           /* Handler name for SR DSD0_3    */
  .word DSD0_4_IRQHandler           /* Handler name for SR DSD0_4    */
  .word DSD0_5_IRQHandler           /* Handler name for SR DSD0_5    */
  .word DSD0_6_IRQHandler           /* Handler name for SR DSD0_6    */
  .word DSD0_7_IRQHandler           /* Handler name for SR DSD0_7    */
  .word DAC0_0_IRQHandler           /* Handler name for SR DAC0_0    */
  .word DAC0_1_IRQHandler           /* Handler name for SR DAC0_0    */
  .word CCU40_0_IRQHandler          /* Handler name for SR CCU40_0   */
  .word CCU40_1_IRQHandler          /* Handler name for SR CCU40_1   */
  .word CCU40_2_IRQHandler          /* Handler name for SR CCU40_2   */
  .word CCU40_3_IRQHandler          /* Handler name for SR CCU40_3   */
  .word CCU41_0_IRQHandler          /* Handler name for SR CCU41_0   */
  .word CCU41_1_IRQHandler          /* Handler name for SR CCU41_1   */
  .word CCU41_2_IRQHandler          /* Handler name for SR CCU41_2   */
  .word CCU41_3_IRQHandler          /* Handler name for SR CCU41_3   */
  .word CCU42_0_IRQHandler          /* Handler name for SR CCU42_0   */
  .word CCU42_1_IRQHandler          /* Handler name for SR CCU42_1   */
  .word CCU42_2_IRQHandler          /* Handler name for SR CCU42_2   */
  .word CCU42_3_IRQHandler          /* Handler name for SR CCU42_3   */
  .word CCU43_0_IRQHandler          /* Handler name for SR CCU43_0   */
  .word CCU43_1_IRQHandler          /* Handler name for SR CCU43_1   */
  .word CCU43_2_IRQHandler          /* Handler name for SR CCU43_2   */
  .word CCU43_3_IRQHandler          /* Handler name for SR CCU43_3   */
  .word CCU80_0_IRQHandler          /* Handler name for SR CCU80_0   */
  .word CCU80_1_IRQHandler          /* Handler name for SR CCU80_1   */
  .word CCU80_2_IRQHandler          /* Handler name for SR CCU80_2   */
  .word CCU80_3_IRQHandler          /* Handler name for SR CCU80_3   */
  .word CCU81_0_IRQHandler          /* Handler name for SR CCU81_0   */
  .word CCU81_1_IRQHandler          /* Handler name for SR CCU81_1   */
  .word CCU81_2_IRQHandler          /* Handler name for SR CCU81_2   */
  .word CCU81_3_IRQHandler          /* Handler name for SR CCU81_3   */
  .word POSIF0_0_IRQHandler         /* Handler name for SR POSIF0_0  */
  .word POSIF0_1_IRQHandler         /* Handler name for SR POSIF0_1  */
  .word POSIF1_0_IRQHandler         /* Handler name for SR POSIF1_0  */
  .word POSIF1_1_IRQHandler         /* Handler name for SR POSIF1_1  */
  .word 0                           /* Not Available                 */
  .word 0                           /* Not Available                 */
  .word 0                           /* Not Available                 */
  .word 0                           /* Not Available                 */
  .word CAN0_0_IRQHandler           /* Handler name for SR CAN0_0    */
  .word CAN0_1_IRQHandler           /* Handler name for SR CAN0_1    */
  .word CAN0_2_IRQHandler           /* Handler name for SR CAN0_2    */
  .word CAN0_3_IRQHandler           /* Handler name for SR CAN0_3    */
  .word CAN0_4_IRQHandler           /* Handler name for SR CAN0_4    */
  .word CAN0_5_IRQHandler           /* Handler name for SR CAN0_5    */
  .word CAN0_6_IRQHandler           /* Handler name for SR CAN0_6    */
  .word CAN0_7_IRQHandler           /* Handler name for SR CAN0_7    */
  .word USIC0_0_IRQHandler          /* Handler name for SR USIC0_0   */
  .word USIC0_1_IRQHandler          /* Handler name for SR USIC0_1   */
  .word USIC0_2_IRQHandler          /* Handler name for SR USIC0_2   */
  .word USIC0_3_IRQHandler          /* Handler name for SR USIC0_3   */
  .word USIC0_4_IRQHandler          /* Handler name for SR USIC0_4   */
  .word USIC0_5_IRQHandler          /* Handler name for SR USIC0_5   */
  .word USIC1_0_IRQHandler          /* Handler name for SR USIC1_0   */
  .word USIC1_1_IRQHandler          /* Handler name for SR USIC1_1   */
  .word USIC1_2_IRQHandler          /* Handler name for SR USIC1_2   */
  .word USIC1_3_IRQHandler          /* Handler name for SR USIC1_3   */
  .word USIC1_4_IRQHandler          /* Handler name for SR USIC1_4   */
  .word USIC1_5_IRQHandler          /* Handler name for SR USIC1_5   */
  .word USIC2_0_IRQHandler          /* Handler name for SR USIC2_0   */
  .word USIC2_1_IRQHandler          /* Handler name for SR USIC2_1   */
  .word USIC2_2_IRQHandler          /* Handler name for SR USIC2_2   */
  .word USIC2_3_IRQHandler          /* Handler name for SR USIC2_3   */
  .word USIC2_4_IRQHandler          /* Handler name for SR USIC2_4   */
  .word USIC2_5_IRQHandler          /* Handler name for SR USIC2_5   */
  .word LEDTS0_0_IRQHandler         /* Handler name for SR LEDTS0_0  */
  .word 0                           /* Not Available                 */
  .word FCE0_0_IRQHandler           /* Handler name for SR FCE0_0    */
  .word GPDMA0_0_IRQHandler         /* Handler name for SR GPDMA0_0  */
  .word SDMMC0_0_IRQHandler         /* Handler name for SR SDMMC0_0  */
  .word USB0_0_IRQHandler           /* Handler name for SR USB0_0    */
  .word ETH0_0_IRQHandler           /* Handler name for SR ETH0_0    */
  .word 0                           /* Not Available                 */
  .word GPDMA1_0_IRQHandler         /* Handler name for SR GPDMA1_0  */
  .word 0                           /* Not Available                 */


/**
**===========================================================================
** Provide weak aliases for each Exception handler to the Default_Handler.
**===========================================================================
*/
  .weak  NMI_Handler
  .thumb_set NMI_Handler,Default_Handler
  
  .weak  HardFault_Handler
  .thumb_set HardFault_Handler,Default_Handler
  
  .weak  MemManage_Handler
  .thumb_set MemManage_Handler,Default_Handler
  
  .weak  BusFault_Handler
  .thumb_set BusFault_Handler,Default_Handler

  .weak  UsageFault_Handler
  .thumb_set UsageFault_Handler,Default_Handler

  .weak  SVC_Handler
  .thumb_set SVC_Handler,Default_Handler

  .weak  DebugMon_Handler
  .thumb_set DebugMon_Handler,Default_Handler

  .weak  PendSV_Handler
  .thumb_set PendSV_Handler,Default_Handler

  .weak  SysTick_Handler
  .thumb_set SysTick_Handler,Default_Handler

  .weak  SCU_0_IRQHandler
  .thumb_set SCU_0_IRQHandler,Default_Handler

  .weak  ERU0_0_IRQHandler
  .thumb_set ERU0_0_IRQHandler,Default_Handler

  .weak  ERU0_1_IRQHandler
  .thumb_set ERU0_1_IRQHandler,Default_Handler

  .weak  ERU0_2_IRQHandler
  .thumb_set ERU0_2_IRQHandler,Default_Handler

  .weak  ERU0_3_IRQHandler
  .thumb_set ERU0_3_IRQHandler,Default_Handler

  .weak  ERU1_0_IRQHandler
  .thumb_set ERU1_0_IRQHandler,Default_Handler

  .weak  ERU1_1_IRQHandler
  .thumb_set ERU1_1_IRQHandler,Default_Handler

  .weak  ERU1_2_IRQHandler
  .thumb_set ERU1_2_IRQHandler,Default_Handler

  .weak  ERU1_3_IRQHandler
  .thumb_set ERU1_3_IRQHandler,Default_Handler

  .weak  PMU0_0_IRQHandler
  .thumb_set PMU0_0_IRQHandler,Default_Handler

  .weak  VADC0_C0_0_IRQHandler
  .thumb_set VADC0_C0_0_IRQHandler,Default_Handler

  .weak  VADC0_C0_1_IRQHandler
  .thumb_set VADC0_C0_1_IRQHandler,Default_Handler

  .weak  VADC0_C0_2_IRQHandler
  .thumb_set VADC0_C0_2_IRQHandler,Default_Handler

  .weak  VADC0_C0_3_IRQHandler
  .thumb_set VADC0_C0_3_IRQHandler,Default_Handler

  .weak  VADC0_G0_0_IRQHandler
  .thumb_set VADC0_G0_0_IRQHandler,Default_Handler

  .weak  VADC0_G0_1_IRQHandler
  .thumb_set VADC0_G0_1_IRQHandler,Default_Handler

  .weak  VADC0_G0_2_IRQHandler
  .thumb_set VADC0_G0_2_IRQHandler,Default_Handler

  .weak  VADC0_G0_3_IRQHandler
  .thumb_set VADC0_G0_3_IRQHandler,Default_Handler

  .weak  VADC0_G1_0_IRQHandler
  .thumb_set VADC0_G1_0_IRQHandler,Default_Handler

  .weak  VADC0_G1_1_IRQHandler
  .thumb_set VADC0_G1_1_IRQHandler,Default_Handler

  .weak  VADC0_G1_2_IRQHandler
  .thumb_set VADC0_G1_2_IRQHandler,Default_Handler

  .weak  VADC0_G1_3_IRQHandler
  .thumb_set VADC0_G1_3_IRQHandler,Default_Handler

  .weak  VADC0_G2_0_IRQHandler
  .thumb_set VADC0_G2_0_IRQHandler,Default_Handler

  .weak  VADC0_G2_1_IRQHandler
  .thumb_set VADC0_G2_1_IRQHandler,Default_Handler

  .weak  VADC0_G2_2_IRQHandler
  .thumb_set VADC0_G2_2_IRQHandler,Default_Handler

  .weak  VADC0_G2_3_IRQHandler
  .thumb_set VADC0_G2_3_IRQHandler,Default_Handler

  .weak  VADC0_G3_0_IRQHandler
  .thumb_set VADC0_G3_0_IRQHandler,Default_Handler

  .weak  VADC0_G3_1_IRQHandler
  .thumb_set VADC0_G3_1_IRQHandler,Default_Handler

  .weak  VADC0_G3_2_IRQHandler
  .thumb_set VADC0_G3_2_IRQHandler,Default_Handler

  .weak  VADC0_G3_3_IRQHandler
  .thumb_set VADC0_G3_3_IRQHandler,Default_Handler

  .weak  DSD0_0_IRQHandler
  .thumb_set DSD0_0_IRQHandler,Default_Handler

  .weak  DSD0_1_IRQHandler
  .thumb_set DSD0_1_IRQHandler,Default_Handler

  .weak  DSD0_2_IRQHandler
  .thumb_set DSD0_2_IRQHandler,Default_Handler

  .weak  DSD0_3_IRQHandler
  .thumb_set DSD0_3_IRQHandler,Default_Handler

  .weak  DSD0_4_IRQHandler
  .thumb_set DSD0_4_IRQHandler,Default_Handler

  .weak  DSD0_5_IRQHandler
  .thumb_set DSD0_5_IRQHandler,Default_Handler

  .weak  DSD0_6_IRQHandler
  .thumb_set DSD0_6_IRQHandler,Default_Handler

  .weak  DSD0_7_IRQHandler
  .thumb_set DSD0_7_IRQHandler,Default_Handler

  .weak  DAC0_0_IRQHandler
  .thumb_set DAC0_0_IRQHandler,Default_Handler

  .weak  DAC0_1_IRQHandler
  .thumb_set DAC0_1_IRQHandler,Default_Handler

  .weak  CCU40_0_IRQHandler
  .thumb_set CCU40_0_IRQHandler,Default_Handler

  .weak  CCU40_1_IRQHandler
  .thumb_set CCU40_1_IRQHandler,Default_Handler

  .weak  CCU40_2_IRQHandler
  .thumb_set CCU40_2_IRQHandler,Default_Handler

  .weak  CCU40_3_IRQHandler
  .thumb_set CCU40_3_IRQHandler,Default_Handler

  .weak  CCU41_0_IRQHandler
  .thumb_set CCU41_0_IRQHandler,Default_Handler

  .weak  CCU41_1_IRQHandler
  .thumb_set CCU41_1_IRQHandler,Default_Handler

  .weak  CCU41_2_IRQHandler
  .thumb_set CCU41_2_IRQHandler,Default_Handler

  .weak  CCU41_3_IRQHandler
  .thumb_set CCU41_3_IRQHandler,Default_Handler

  .weak  CCU42_0_IRQHandler
  .thumb_set CCU42_0_IRQHandler,Default_Handler

  .weak  CCU42_1_IRQHandler
  .thumb_set CCU42_1_IRQHandler,Default_Handler

  .weak  CCU42_2_IRQHandler
  .thumb_set CCU42_2_IRQHandler,Default_Handler

  .weak  CCU42_3_IRQHandler
  .thumb_set CCU42_3_IRQHandler,Default_Handler

  .weak  CCU43_0_IRQHandler
  .thumb_set CCU43_0_IRQHandler,Default_Handler

  .weak  CCU43_1_IRQHandler
  .thumb_set CCU43_1_IRQHandler,Default_Handler

  .weak  CCU43_2_IRQHandler
  .thumb_set CCU43_2_IRQHandler,Default_Handler

  .weak  CCU43_3_IRQHandler
  .thumb_set CCU43_3_IRQHandler,Default_Handler

  .weak  CCU80_0_IRQHandler
  .thumb_set CCU80_0_IRQHandler,Default_Handler

  .weak  CCU80_1_IRQHandler
  .thumb_set CCU80_1_IRQHandler,Default_Handler

  .weak  CCU80_2_IRQHandler
  .thumb_set CCU80_2_IRQHandler,Default_Handler

  .weak  CCU80_3_IRQHandler
  .thumb_set CCU80_3_IRQHandler,Default_Handler

  .weak  CCU81_0_IRQHandler
  .thumb_set CCU81_0_IRQHandler,Default_Handler

  .weak  CCU81_1_IRQHandler
  .thumb_set CCU81_1_IRQHandler,Default_Handler

  .weak  CCU81_2_IRQHandler
  .thumb_set CCU81_2_IRQHandler,Default_Handler

  .weak  CCU81_3_IRQHandler
  .thumb_set CCU81_3_IRQHandler,Default_Handler

  .weak  POSIF0_0_IRQHandler
  .thumb_set POSIF0_0_IRQHandler,Default_Handler

  .weak  POSIF0_1_IRQHandler
  .thumb_set POSIF0_1_IRQHandler,Default_Handler

  .weak  POSIF1_0_IRQHandler
  .thumb_set POSIF1_0_IRQHandler,Default_Handler

  .weak  POSIF1_1_IRQHandler
  .thumb_set POSIF1_1_IRQHandler,Default_Handler

  .weak  CAN0_0_IRQHandler
  .thumb_set CAN0_0_IRQHandler,Default_Handler

  .weak  CAN0_1_IRQHandler
  .thumb_set CAN0_1_IRQHandler,Default_Handler

  .weak  CAN0_2_IRQHandler
  .thumb_set CAN0_2_IRQHandler,Default_Handler

  .weak  CAN0_3_IRQHandler
  .thumb_set CAN0_3_IRQHandler,Default_Handler

  .weak  CAN0_4_IRQHandler
  .thumb_set CAN0_4_IRQHandler,Default_Handler

  .weak  CAN0_5_IRQHandler
  .thumb_set CAN0_5_IRQHandler,Default_Handler

  .weak  CAN0_6_IRQHandler
  .thumb_set CAN0_6_IRQHandler,Default_Handler

  .weak  CAN0_7_IRQHandler
  .thumb_set CAN0_7_IRQHandler,Default_Handler

  .weak  USIC0_0_IRQHandler
  .thumb_set USIC0_0_IRQHandler,Default_Handler

  .weak  USIC0_1_IRQHandler
  .thumb_set USIC0_1_IRQHandler,Default_Handler

  .weak  USIC0_2_IRQHandler
  .thumb_set USIC0_2_IRQHandler,Default_Handler

  .weak  USIC0_3_IRQHandler
  .thumb_set USIC0_3_IRQHandler,Default_Handler

  .weak  USIC0_4_IRQHandler
  .thumb_set USIC0_4_IRQHandler,Default_Handler

  .weak  USIC0_5_IRQHandler
  .thumb_set USIC0_5_IRQHandler,Default_Handler

  .weak  USIC1_0_IRQHandler
  .thumb_set USIC1_0_IRQHandler,Default_Handler

  .weak  USIC1_1_IRQHandler
  .thumb_set USIC1_1_IRQHandler,Default_Handler

  .weak  USIC1_2_IRQHandler
  .thumb_set USIC1_2_IRQHandler,Default_Handler

  .weak  USIC1_3_IRQHandler
  .thumb_set USIC1_3_IRQHandler,Default_Handler

  .weak  USIC1_4_IRQHandler
  .thumb_set USIC1_4_IRQHandler,Default_Handler

  .weak  USIC1_5_IRQHandler
  .thumb_set USIC1_5_IRQHandler,Default_Handler

  .weak  USIC2_0_IRQHandler
  .thumb_set USIC2_0_IRQHandler,Default_Handler

  .weak  USIC2_1_IRQHandler
  .thumb_set USIC2_1_IRQHandler,Default_Handler

  .weak  USIC2_2_IRQHandler
  .thumb_set USIC2_2_IRQHandler,Default_Handler

  .weak  USIC2_3_IRQHandler
  .thumb_set USIC2_3_IRQHandler,Default_Handler

  .weak  USIC2_4_IRQHandler
  .thumb_set USIC2_4_IRQHandler,Default_Handler

  .weak  USIC2_5_IRQHandler
  .thumb_set USIC2_5_IRQHandler,Default_Handler

  .weak  LEDTS0_0_IRQHandler
  .thumb_set LEDTS0_0_IRQHandler,Default_Handler

  .weak  FCE0_0_IRQHandler
  .thumb_set FCE0_0_IRQHandler,Default_Handler

  .weak  GPDMA0_0_IRQHandler
  .thumb_set GPDMA0_0_IRQHandler,Default_Handler

  .weak  SDMMC0_0_IRQHandler
  .thumb_set SDMMC0_0_IRQHandler,Default_Handler

  .weak  USB0_0_IRQHandler
  .thumb_set USB0_0_IRQHandler,Default_Handler

  .weak  ETH0_0_IRQHandler
  .thumb_set ETH0_0_IRQHandler,Default_Handler

  .weak  GPDMA1_0_IRQHandler
  .thumb_set GPDMA1_0_IRQHandler,Default_Handler

.end
