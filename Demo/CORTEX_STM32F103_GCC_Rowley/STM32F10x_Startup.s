/*****************************************************************************
 * Copyright (c) 2007 Rowley Associates Limited.                             *
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
 *   complete.
 *
 *****************************************************************************/

.extern xPortPendSVHandler
.extern xPortSysTickHandler
.extern vPortSVCHandler

  .global reset_handler

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

_vectors:
  .word __stack_end__
#ifdef STARTUP_FROM_RESET
  .word reset_handler
#else
  .word reset_wait
#endif /* STARTUP_FROM_RESET */
  .word NMIException
  .word HardFaultException
  .word MemManageException 
  .word BusFaultException
  .word UsageFaultException
  .word 0 // Reserved
  .word 0 // Reserved
  .word 0 // Reserved
  .word 0 // Reserved
  .word vPortSVCHandler
  .word DebugMonitor
  .word 0 // Reserved
  .word xPortPendSVHandler
  .word xPortSysTickHandler
  .word WWDG_IRQHandler
  .word PVD_IRQHandler
  .word TAMPER_IRQHandler
  .word RTC_IRQHandler
  .word FLASH_IRQHandler
  .word RCC_IRQHandler
  .word EXTI0_IRQHandler
  .word EXTI1_IRQHandler
  .word EXTI2_IRQHandler
  .word EXTI3_IRQHandler
  .word EXTI4_IRQHandler
  .word DMAChannel1_IRQHandler
  .word DMAChannel2_IRQHandler
  .word DMAChannel3_IRQHandler
  .word DMAChannel4_IRQHandler
  .word DMAChannel5_IRQHandler
  .word DMAChannel6_IRQHandler
  .word DMAChannel7_IRQHandler
  .word ADC_IRQHandler
  .word USB_HP_CAN_TX_IRQHandler
  .word USB_LP_CAN_RX0_IRQHandler
  .word CAN_RX1_IRQHandler
  .word CAN_SCE_IRQHandler
  .word EXTI9_5_IRQHandler
  .word TIM1_BRK_IRQHandler
  .word TIM1_UP_IRQHandler
  .word TIM1_TRG_COM_IRQHandler
  .word TIM1_CC_IRQHandler
  .word TIM2_IRQHandler
  .word TIM3_IRQHandler
  .word TIM4_IRQHandler  
  .word I2C1_EV_IRQHandler
  .word I2C1_ER_IRQHandler
  .word I2C2_EV_IRQHandler
  .word I2C2_ER_IRQHandler
  .word SPI1_IRQHandler
  .word SPI2_IRQHandler
  .word USART1_IRQHandler
  .word USART2_IRQHandler
  .word USART3_IRQHandler
  .word EXTI15_10_IRQHandler
  .word RTCAlarm_IRQHandler
  .word USBWakeUp_IRQHandler
  .word TIM8_BRK_IRQHandler
  .word TIM8_UP_IRQHandler
  .word TIM8_TRG_COM_IRQHandler
  .word TIM8_CC_IRQHandler
  .word ADC3_IRQHandler
  .word FSMC_IRQHandler
  .word SDIO_IRQHandler
  .word TIM5_IRQHandler
  .word SPI3_IRQHandler
  .word UART4_IRQHandler
  .word UART5_IRQHandler
  .word TIM6_IRQHandler
  .word TIM7_IRQHandler
  .word DMA2_Channel1_IRQHandler
  .word DMA2_Channel2_IRQHandler
  .word DMA2_Channel3_IRQHandler
  .word DMA2_Channel4_5_IRQHandler

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
  b _start

DEFAULT_ISR_HANDLER NMIException
DEFAULT_ISR_HANDLER HardFaultException 
DEFAULT_ISR_HANDLER MemManageException 
DEFAULT_ISR_HANDLER BusFaultException 
DEFAULT_ISR_HANDLER UsageFaultException 
DEFAULT_ISR_HANDLER SVCHandler 
DEFAULT_ISR_HANDLER DebugMonitor  
DEFAULT_ISR_HANDLER PendSV 
DEFAULT_ISR_HANDLER SysTickHandler 
DEFAULT_ISR_HANDLER WWDG_IRQHandler 
DEFAULT_ISR_HANDLER PVD_IRQHandler 
DEFAULT_ISR_HANDLER TAMPER_IRQHandler 
DEFAULT_ISR_HANDLER RTC_IRQHandler 
DEFAULT_ISR_HANDLER FLASH_IRQHandler 
DEFAULT_ISR_HANDLER RCC_IRQHandler 
DEFAULT_ISR_HANDLER EXTI0_IRQHandler 
DEFAULT_ISR_HANDLER EXTI1_IRQHandler 
DEFAULT_ISR_HANDLER EXTI2_IRQHandler 
DEFAULT_ISR_HANDLER EXTI3_IRQHandler 
DEFAULT_ISR_HANDLER EXTI4_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel1_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel2_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel3_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel4_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel5_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel6_IRQHandler 
DEFAULT_ISR_HANDLER DMAChannel7_IRQHandler 
DEFAULT_ISR_HANDLER ADC_IRQHandler 
DEFAULT_ISR_HANDLER USB_HP_CAN_TX_IRQHandler 
DEFAULT_ISR_HANDLER USB_LP_CAN_RX0_IRQHandler 
DEFAULT_ISR_HANDLER CAN_RX1_IRQHandler 
DEFAULT_ISR_HANDLER CAN_SCE_IRQHandler 
DEFAULT_ISR_HANDLER EXTI9_5_IRQHandler 
DEFAULT_ISR_HANDLER TIM1_BRK_IRQHandler 
DEFAULT_ISR_HANDLER TIM1_UP_IRQHandler 
DEFAULT_ISR_HANDLER TIM1_TRG_COM_IRQHandler 
DEFAULT_ISR_HANDLER TIM1_CC_IRQHandler 
DEFAULT_ISR_HANDLER TIM2_IRQHandler 
DEFAULT_ISR_HANDLER TIM3_IRQHandler 
DEFAULT_ISR_HANDLER TIM4_IRQHandler 
DEFAULT_ISR_HANDLER I2C1_EV_IRQHandler 
DEFAULT_ISR_HANDLER I2C1_ER_IRQHandler 
DEFAULT_ISR_HANDLER I2C2_EV_IRQHandler 
DEFAULT_ISR_HANDLER I2C2_ER_IRQHandler 
DEFAULT_ISR_HANDLER SPI1_IRQHandler 
DEFAULT_ISR_HANDLER SPI2_IRQHandler 
DEFAULT_ISR_HANDLER USART1_IRQHandler 
DEFAULT_ISR_HANDLER USART2_IRQHandler 
DEFAULT_ISR_HANDLER USART3_IRQHandler 
DEFAULT_ISR_HANDLER EXTI15_10_IRQHandler 
DEFAULT_ISR_HANDLER RTCAlarm_IRQHandler 
DEFAULT_ISR_HANDLER USBWakeUp_IRQHandler 
DEFAULT_ISR_HANDLER TIM8_BRK_IRQHandler
DEFAULT_ISR_HANDLER TIM8_UP_IRQHandler
DEFAULT_ISR_HANDLER TIM8_TRG_COM_IRQHandler
DEFAULT_ISR_HANDLER TIM8_CC_IRQHandler
DEFAULT_ISR_HANDLER ADC3_IRQHandler
DEFAULT_ISR_HANDLER FSMC_IRQHandler
DEFAULT_ISR_HANDLER SDIO_IRQHandler
DEFAULT_ISR_HANDLER TIM5_IRQHandler
DEFAULT_ISR_HANDLER SPI3_IRQHandler
DEFAULT_ISR_HANDLER UART4_IRQHandler
DEFAULT_ISR_HANDLER UART5_IRQHandler
DEFAULT_ISR_HANDLER TIM6_IRQHandler
DEFAULT_ISR_HANDLER TIM7_IRQHandler
DEFAULT_ISR_HANDLER DMA2_Channel1_IRQHandler
DEFAULT_ISR_HANDLER DMA2_Channel2_IRQHandler
DEFAULT_ISR_HANDLER DMA2_Channel3_IRQHandler
DEFAULT_ISR_HANDLER DMA2_Channel4_5_IRQHandler

#ifndef STARTUP_FROM_RESET
DEFAULT_ISR_HANDLER reset_wait
#endif /* STARTUP_FROM_RESET */

  // STM32 library requires these
  .global __WFI
  .global __WFE
  .global __SEV
  .global __ISB
  .global __DSB
  .global __DMB
  .global __SVC
  .global __MRS_CONTROL
  .global __MSR_CONTROL
  .global __MRS_PSP
  .global __MSR_PSP
  .global __MRS_MSP
  .global __MSR_MSP   
  .global __SETPRIMASK
  .global __RESETPRIMASK
  .global __SETFAULTMASK
  .global __RESETFAULTMASK
  .global __BASEPRICONFIG
  .global __GetBASEPRI
  .global __REV_HalfWord
  .global __REV_Word

.thumb_func
__WFI: 
  wfi
  bx r14
.thumb_func
__WFE:
  wfe
  bx r14
.thumb_func
__SEV:
  sev
  bx r14
.thumb_func
__ISB:
  isb
  bx r14
.thumb_func
__DSB:
  dsb
  bx r14
.thumb_func
__DMB:
  dmb
  bx r14
.thumb_func
__SVC:
  svc 0x01
  bx r14
.thumb_func
__MRS_CONTROL:
  mrs r0, control
  bx r14
.thumb_func
__MSR_CONTROL:
  msr control, r0
  isb
  bx r14
.thumb_func
__MRS_PSP:
  mrs r0, psp
  bx r14
.thumb_func
__MSR_PSP: 
  msr psp, r0
  bx r14
.thumb_func
__MRS_MSP:
  mrs r0, msp
  bx r14
.thumb_func
__MSR_MSP: 
  msr msp, r0
  bx r14
.thumb_func
__SETPRIMASK:
  cpsid i
  bx r14
.thumb_func
__RESETPRIMASK:
  cpsie i
  bx r14
.thumb_func
__SETFAULTMASK:
  cpsid f
  bx r14
.thumb_func
__RESETFAULTMASK:
  cpsie f
  bx r14
.thumb_func
__BASEPRICONFIG:
  msr basepri, r0
  bx r14
.thumb_func
__GetBASEPRI:
  mrs r0, basepri_max
  bx r14
.thumb_func
__REV_HalfWord:
  rev16 r0, r0
  bx r14
.thumb_func
__REV_Word:  
  rev r0, r0
  bx r14
      





