/*****************************************************************************
 * Copyright (c) 2009 Rowley Associates Limited.                             *
 *                                                                           *
 * This file may be distributed under the terms of the License Agreement     *
 * provided with this software.                                              *
 *                                                                           *
 * THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE   *
 * WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. *
 *****************************************************************************/

/*****************************************************************************
 *                           Preprocessor Definitions
 *                           ------------------------
 *
 * STARTUP_FROM_RESET
 *
 *   If defined, the program will startup from power-on/reset. If not defined
 *   the program will just loop endlessly from power-on/reset.
 *
 *   This definition is not defined by default on this target because the
 *   debugger is unable to reset this target and maintain control of it over the
 *   JTAG interface. The advantage of doing this is that it allows the debugger
 *   to reset the CPU and run programs from a known reset CPU state on each run.
 *   It also acts as a safety net if you accidently download a program in FLASH
 *   that crashes and prevents the debugger from taking control over JTAG
 *   rendering the target unusable over JTAG. The obvious disadvantage of doing
 *   this is that your application will not startup without the debugger.
 *
 *   We advise that on this target you keep STARTUP_FROM_RESET undefined whilst
 *   you are developing and only define STARTUP_FROM_RESET when development is
 *   complete.A
 *
 *
 * CONFIGURE_USB
 *
 *   If defined, the USB clock will be configured.
 *
 *****************************************************************************/

#include <LPC1000.h>

#if OSCILLATOR_CLOCK_FREQUENCY==12000000

#ifdef FULL_SPEED

/* Fosc = 12Mhz, Fcco = 400Mhz, cclk = 100Mhz */
#ifndef PLL0CFG_VAL
#define PLL0CFG_VAL ((49 << PLL0CFG_MSEL0_BIT) | (2 << PLL0CFG_NSEL0_BIT))
#endif

#ifndef CCLKCFG_VAL
#define CCLKCFG_VAL 3
#endif

#ifndef FLASHCFG_VAL
#define FLASHCFG_VAL 0x0000403A
#endif

#else

/* Fosc = 12Mhz, Fcco = 288Mhz, cclk = 72Mhz */
#ifndef PLL0CFG_VAL
#define PLL0CFG_VAL ((11 << PLL0CFG_MSEL0_BIT) | (0 << PLL0CFG_NSEL0_BIT))
#endif

#ifndef CCLKCFG_VAL
#define CCLKCFG_VAL 3
#endif

#ifndef FLASHCFG_VAL
#define FLASHCFG_VAL 0x0000303A
#endif

#endif

/* Fosc = 12Mhz, Fcco = 192Mhz, usbclk = 48Mhz */
#ifndef PLL1CFG_VAL
#define PLL1CFG_VAL ((3 << PLL1CFG_MSEL1_BIT) | (1 << PLL1CFG_PSEL1_BIT))
#endif

#endif

  .global reset_handler

  .syntax unified

  .section .vectors, "ax"
  .code 16
  .align 0
  .global _vectors

.macro DEFAULT_ISR_HANDLER name=
  .thumb_func
  .weak \name
\name:
1: b 1b /* endless loop */
.endm

.extern xPortPendSVHandler
.extern xPortSysTickHandler
.extern vPortSVCHandler
.extern vEMAC_ISR;

_vectors:
  .word __stack_end__
#ifdef STARTUP_FROM_RESET
  .word reset_handler
#else
  .word reset_wait
#endif /* STARTUP_FROM_RESET */
  .word NMI_Handler
  .word HardFault_Handler
  .word MemManage_Handler
  .word BusFault_Handler
  .word UsageFault_Handler
  .word 0 // Reserved
  .word 0 // Reserved
  .word 0 // Reserved
  .word 0 // Reserved
  .word vPortSVCHandler
  .word DebugMon_Handler
  .word 0 // Reserved
  .word xPortPendSVHandler
  .word xPortSysTickHandler
  .word WDT_IRQHandler
  .word TIMER0_IRQHandler
  .word TIMER1_IRQHandler
  .word TIMER2_IRQHandler
  .word TIMER3_IRQHandler
  .word UART0_IRQHandler
  .word UART1_IRQHandler
  .word UART2_IRQHandler
  .word UART3_IRQHandler
  .word PWM1_IRQHandler
  .word I2C0_IRQHandler
  .word I2C1_IRQHandler
  .word I2C2_IRQHandler
  .word SPI_IRQHandler
  .word SSP0_IRQHandler
  .word SSP1_IRQHandler
  .word PLL0_IRQHandler
  .word RTC_IRQHandler
  .word EINT0_IRQHandler
  .word EINT1_IRQHandler
  .word EINT2_IRQHandler
  .word EINT3_IRQHandler
  .word ADC_IRQHandler
  .word BOD_IRQHandler
  .word USB_IRQHandler
  .word CAN_IRQHandler
  .word GPDMA_IRQHandler
  .word I2S_IRQHandler
  .word vEMAC_ISR
  .word RIT_IRQHandler
  .word MCPWM_IRQHandler
  .word QEI_IRQHandler
  .word PLL1_IRQHandler
  .word USBACT_IRQHandler
  .word CANACT_IRQHandler

  .section .init, "ax"
  .thumb_func

  reset_handler:
#ifndef __FLASH_BUILD
  /* If this is a RAM build, configure vector table offset register to point
     to the RAM vector table. */
  ldr r0, =0xE000ED08
  ldr r1, =_vectors
  str r1, [r0]
#endif

  ldr r0, =SC_BASE_ADDRESS

  /* Configure PLL0 Multiplier/Divider */
  ldr r1, [r0, #PLL0STAT_OFFSET]
  tst r1, #PLL0STAT_PLLC0_STAT
  beq 1f

  /* Disconnect PLL0 */
  ldr r1, =PLL0CON_PLLE0
  str r1, [r0, #PLL0CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL0FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL0FEED_OFFSET]
1:
  /* Disable PLL0 */
  ldr r1, =0
  str r1, [r0, #PLL0CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL0FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL0FEED_OFFSET]

  /* Enable main oscillator */
  ldr r1, [r0, #SCS_OFFSET]
  orr r1, r1, #SCS_OSCEN
  str r1, [r0, #SCS_OFFSET]
1:
  ldr r1, [r0, #SCS_OFFSET]
  tst r1, #SCS_OSCSTAT
  beq 1b

  /* Select main oscillator as the PLL0 clock source */
  ldr r1, =1
  str r1, [r0, #CLKSRCSEL_OFFSET]

  /* Set PLL0CFG */
  ldr r1, =PLL0CFG_VAL
  str r1, [r0, #PLL0CFG_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL0FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL0FEED_OFFSET]

  /* Enable PLL0 */
  ldr r1, =PLL0CON_PLLE0
  str r1, [r0, #PLL0CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL0FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL0FEED_OFFSET]

#ifdef CCLKCFG_VAL
  /* Set the CPU clock divider */
  ldr r1, =CCLKCFG_VAL
  str r1, [r0, #CCLKCFG_OFFSET]
#endif

#ifdef FLASHCFG_VAL
  /* Configure the FLASH accelerator */
  ldr r1, =FLASHCFG_VAL
  str r1, [r0, #FLASHCFG_OFFSET]
#endif

  /* Wait for PLL0 to lock */
1:
  ldr r1, [r0, #PLL0STAT_OFFSET]
  tst r1, #PLL0STAT_PLOCK0
  beq 1b

  /* PLL0 Locked, connect PLL as clock source */
  mov r1, #(PLL0CON_PLLE0 | PLL0CON_PLLC0)
  str r1, [r0, #PLL0CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL0FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL0FEED_OFFSET]
  /* Wait for PLL0 to connect */
1:
  ldr r1, [r0, #PLL0STAT_OFFSET]
  tst r1, #PLL0STAT_PLLC0_STAT
  beq 1b

#ifdef CONFIGURE_USB
  /* Configure PLL1 Multiplier/Divider */
  ldr r1, [r0, #PLL1STAT_OFFSET]
  tst r1, #PLL1STAT_PLLC1_STAT
  beq 1f

  /* Disconnect PLL1 */
  ldr r1, =PLL1CON_PLLE1
  str r1, [r0, #PLL1CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL1FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL1FEED_OFFSET]
1:
  /* Disable PLL1 */
  ldr r1, =0
  str r1, [r0, #PLL1CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL1FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL1FEED_OFFSET]

  /* Set PLL1CFG */
  ldr r1, =PLL1CFG_VAL
  str r1, [r0, #PLL1CFG_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL1FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL1FEED_OFFSET]

  /* Enable PLL1 */
  ldr r1, =PLL1CON_PLLE1
  str r1, [r0, #PLL1CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL1FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL1FEED_OFFSET]

  /* Wait for PLL1 to lock */
1:
  ldr r1, [r0, #PLL1STAT_OFFSET]
  tst r1, #PLL1STAT_PLOCK1
  beq 1b

  /* PLL1 Locked, connect PLL as clock source */
  mov r1, #(PLL1CON_PLLE1 | PLL1CON_PLLC1)
  str r1, [r0, #PLL1CON_OFFSET]
  mov r1, #0xAA
  str r1, [r0, #PLL1FEED_OFFSET]
  mov r1, #0x55
  str r1, [r0, #PLL1FEED_OFFSET]
  /* Wait for PLL1 to connect */
1:
  ldr r1, [r0, #PLL1STAT_OFFSET]
  tst r1, #PLL1STAT_PLLC1_STAT
  beq 1b
#endif

  b _start

DEFAULT_ISR_HANDLER NMI_Handler
DEFAULT_ISR_HANDLER HardFault_Handler
DEFAULT_ISR_HANDLER MemManage_Handler
DEFAULT_ISR_HANDLER BusFault_Handler
DEFAULT_ISR_HANDLER UsageFault_Handler
DEFAULT_ISR_HANDLER SVC_Handler
DEFAULT_ISR_HANDLER DebugMon_Handler
DEFAULT_ISR_HANDLER PendSV_Handler
DEFAULT_ISR_HANDLER SysTick_Handler
DEFAULT_ISR_HANDLER WDT_IRQHandler
DEFAULT_ISR_HANDLER TIMER0_IRQHandler
DEFAULT_ISR_HANDLER TIMER1_IRQHandler
DEFAULT_ISR_HANDLER TIMER2_IRQHandler
DEFAULT_ISR_HANDLER TIMER3_IRQHandler
DEFAULT_ISR_HANDLER UART0_IRQHandler
DEFAULT_ISR_HANDLER UART1_IRQHandler
DEFAULT_ISR_HANDLER UART2_IRQHandler
DEFAULT_ISR_HANDLER UART3_IRQHandler
DEFAULT_ISR_HANDLER PWM1_IRQHandler
DEFAULT_ISR_HANDLER I2C0_IRQHandler
DEFAULT_ISR_HANDLER I2C1_IRQHandler
DEFAULT_ISR_HANDLER I2C2_IRQHandler
DEFAULT_ISR_HANDLER SPI_IRQHandler
DEFAULT_ISR_HANDLER SSP0_IRQHandler
DEFAULT_ISR_HANDLER SSP1_IRQHandler
DEFAULT_ISR_HANDLER PLL0_IRQHandler
DEFAULT_ISR_HANDLER RTC_IRQHandler
DEFAULT_ISR_HANDLER EINT0_IRQHandler
DEFAULT_ISR_HANDLER EINT1_IRQHandler
DEFAULT_ISR_HANDLER EINT2_IRQHandler
DEFAULT_ISR_HANDLER EINT3_IRQHandler
DEFAULT_ISR_HANDLER ADC_IRQHandler
DEFAULT_ISR_HANDLER BOD_IRQHandler
DEFAULT_ISR_HANDLER USB_IRQHandler
DEFAULT_ISR_HANDLER CAN_IRQHandler
DEFAULT_ISR_HANDLER GPDMA_IRQHandler
DEFAULT_ISR_HANDLER I2S_IRQHandler
DEFAULT_ISR_HANDLER ENET_IRQHandler
DEFAULT_ISR_HANDLER RIT_IRQHandler
DEFAULT_ISR_HANDLER MCPWM_IRQHandler
DEFAULT_ISR_HANDLER QEI_IRQHandler
DEFAULT_ISR_HANDLER PLL1_IRQHandler
DEFAULT_ISR_HANDLER USBACT_IRQHandler
DEFAULT_ISR_HANDLER CANACT_IRQHandler

#ifndef STARTUP_FROM_RESET
DEFAULT_ISR_HANDLER reset_wait
#endif /* STARTUP_FROM_RESET */

