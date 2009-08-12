/*****************************************************************************
 * Copyright (c) 2006 Rowley Associates Limited.                             *
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
.extern Timer0IntHandler
.extern vT2InterruptHandler
.extern vT3InterruptHandler
.extern vEMAC_ISR


.global reset_handler

.macro DEFAULT_ISR_HANDLER name=
  .thumb_func
  .weak \name
\name:
1: b 1b /* endless loop */
.endm

  .section .vectors, "ax"
  .code 16
  .align 0
  .global _vectors

_vectors:
  .word __stack_end__
#ifdef STARTUP_FROM_RESET
  .word reset_handler
#else
  .word reset_wait
#endif /* STARTUP_FROM_RESET */
  .word Nmi_ISR
  .word Fault_ISR
  .word MPU_Fault_ISR
  .word 0  /* Populate if using Bus fault */
  .word 0  /* Populate if using Usage fault */
  .word 0  /* Reserved */
  .word 0  /* Reserved */
  .word 0  /* Reserved */
  .word 0  /* Reserved */
  .word vPortSVCHandler
  .word 0  /* Populate if using a debug monitor */
  .word 0  /* Reserved */
  .word xPortPendSVHandler
  .word xPortSysTickHandler
  .word GPIO_Port_A_ISR
  .word GPIO_Port_B_ISR
  .word GPIO_Port_C_ISR
  .word GPIO_Port_D_ISR
  .word GPIO_Port_E_ISR
  .word UART0_ISR
  .word UART1_ISR
  .word SSI_ISR
  .word I2C_ISR
  .word PWM_Fault_ISR
  .word PWM_Generator_0_ISR
  .word PWM_Generator_1_ISR
  .word PWM_Generator_2_ISR
  .word QEI_ISR
  .word ADC_Sequence_0_ISR
  .word ADC_Sequence_1_ISR
  .word ADC_Sequence_2_ISR
  .word ADC_Sequence_3_ISR
  .word Watchdog_Timer_ISR
  .word Timer0IntHandler
  .word Timer0B_ISR
  .word Timer1A_ISR
  .word Timer1B_ISR
  .word vT2InterruptHandler
  .word Timer2B_ISR
  .word Analog_Comparator_0_ISR
  .word Analog_Comparator_1_ISR
  .word Analog_Comparator_2_ISR
  .word System_Control_ISR
  .word FLASH_Control_ISR
  .word GPIO_Port_F_ISR
  .word GPIO_Port_G_ISR
  .word GPIO_Port_H_ISR
  .word UART2_ISR
  .word SSI1_ISR
  .word vT3InterruptHandler
  .word Timer3B_ISR
  .word I2C1_ISR
  .word QEI1_ISR
  .word CAN0_ISR
  .word CAN1_ISR
  .word CAN2_ISR
  .word vEMAC_ISR
  .word HIBERNATE_ISR
  .word USB0_ISR
  .word PWM_Generator_3_ISR
  .word uDMA_Software_Transfer_ISR
  .word uDMA_Error_ISR
_vectors_end:

  .section .init, "ax"
  .thumb_func

reset_handler:
#ifdef __RAM_BUILD
  /* If this is a RAM build, configure vector table offset register to point
     to the RAM vector table. */
  ldr r0, =0xE000ED08
  ldr r1, =_vectors
  str r1, [r0]
#endif
  b _start

DEFAULT_ISR_HANDLER Nmi_ISR
DEFAULT_ISR_HANDLER Fault_ISR
DEFAULT_ISR_HANDLER MPU_Fault_ISR
DEFAULT_ISR_HANDLER SVCall_ISR
DEFAULT_ISR_HANDLER SysTick_ISR
DEFAULT_ISR_HANDLER PendSV_ISR
DEFAULT_ISR_HANDLER GPIO_Port_A_ISR
DEFAULT_ISR_HANDLER GPIO_Port_B_ISR
DEFAULT_ISR_HANDLER GPIO_Port_C_ISR
DEFAULT_ISR_HANDLER GPIO_Port_D_ISR
DEFAULT_ISR_HANDLER GPIO_Port_E_ISR
DEFAULT_ISR_HANDLER UART0_ISR
DEFAULT_ISR_HANDLER UART1_ISR
DEFAULT_ISR_HANDLER SSI_ISR
DEFAULT_ISR_HANDLER I2C_ISR
DEFAULT_ISR_HANDLER PWM_Fault_ISR
DEFAULT_ISR_HANDLER PWM_Generator_0_ISR
DEFAULT_ISR_HANDLER PWM_Generator_1_ISR
DEFAULT_ISR_HANDLER PWM_Generator_2_ISR
DEFAULT_ISR_HANDLER QEI_ISR
DEFAULT_ISR_HANDLER ADC_Sequence_0_ISR
DEFAULT_ISR_HANDLER ADC_Sequence_1_ISR
DEFAULT_ISR_HANDLER ADC_Sequence_2_ISR
DEFAULT_ISR_HANDLER ADC_Sequence_3_ISR
DEFAULT_ISR_HANDLER Watchdog_Timer_ISR
DEFAULT_ISR_HANDLER Timer0A_ISR
DEFAULT_ISR_HANDLER Timer0B_ISR
DEFAULT_ISR_HANDLER Timer1A_ISR
DEFAULT_ISR_HANDLER Timer1B_ISR
DEFAULT_ISR_HANDLER Timer2A_ISR
DEFAULT_ISR_HANDLER Timer2B_ISR
DEFAULT_ISR_HANDLER Analog_Comparator_0_ISR
DEFAULT_ISR_HANDLER Analog_Comparator_1_ISR
DEFAULT_ISR_HANDLER Analog_Comparator_2_ISR
DEFAULT_ISR_HANDLER System_Control_ISR
DEFAULT_ISR_HANDLER FLASH_Control_ISR
DEFAULT_ISR_HANDLER GPIO_Port_F_ISR
DEFAULT_ISR_HANDLER GPIO_Port_G_ISR
DEFAULT_ISR_HANDLER GPIO_Port_H_ISR
DEFAULT_ISR_HANDLER UART2_ISR
DEFAULT_ISR_HANDLER SSI1_ISR
DEFAULT_ISR_HANDLER Timer3A_ISR
DEFAULT_ISR_HANDLER Timer3B_ISR
DEFAULT_ISR_HANDLER I2C1_ISR
DEFAULT_ISR_HANDLER QEI1_ISR
DEFAULT_ISR_HANDLER CAN0_ISR
DEFAULT_ISR_HANDLER CAN1_ISR
DEFAULT_ISR_HANDLER CAN2_ISR
DEFAULT_ISR_HANDLER ETHERNET_ISR
DEFAULT_ISR_HANDLER HIBERNATE_ISR
DEFAULT_ISR_HANDLER USB0_ISR
DEFAULT_ISR_HANDLER PWM_Generator_3_ISR
DEFAULT_ISR_HANDLER uDMA_Software_Transfer_ISR
DEFAULT_ISR_HANDLER uDMA_Error_ISR

#ifndef STARTUP_FROM_RESET
DEFAULT_ISR_HANDLER reset_wait
#endif /* STARTUP_FROM_RESET */
