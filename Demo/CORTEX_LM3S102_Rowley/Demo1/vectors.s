/*****************************************************************************
 * Copyright (c) 2006 Rowley Associates Limited.                             *
 *                                                                           *
 * This file may be distributed under the terms of the License Agreement     *
 * provided with this software.                                              *
 *                                                                           *
 * THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE   *
 * WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. *
 *****************************************************************************/
  .section .vectors, "ax"
  .code 16
  .align 0
  .global _vectors

  .extern xPortPendSVHandler
  .extern xPortSysTickHandler
  .extern vUART_ISR
  .extern vPortSVCHandler

.macro DEFAULT_ISR_HANDLER name=
  .thumb_func
  .weak \name
\name:
1: b 1b /* endless loop */
.endm

_vectors:
  .word __stack_end__
#ifdef STARTUP_FROM_RESET
  .word _start
#else
  .word reset_wait
#endif /* STARTUP_FROM_RESET */
  .word NmiISR
  .word FaultISR
  .word 0 // Populate if using MemManage (MPU)
  .word 0 // Populate if using Bus fault
  .word 0 // Populate if using Usage fault
  .word 0 // Reserved
  .word 0 // Reserved
  .word 0 // Reserved
  .word 0 // Reserved
  .word vPortSVCHandler
  .word 0 // Populate if using a debug monitor
  .word 0 // Reserved
  .word xPortPendSVHandler // Populate if using pendable service request
  .word xPortSysTickHandler
  // External interrupts start her 
  .word GPIO_Port_A_ISR
  .word GPIO_Port_B_ISR
  .word GPIO_Port_C_ISR
  .word GPIO_Port_D_ISR
  .word GPIO_Port_E_ISR
  .word vUART_ISR
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
  .word Watchdog_timer_ISR
  .word Timer0a_ISR
  .word Timer0b_ISR
  .word Timer1a_ISR
  .word Timer1b_ISR
  .word Timer2a_ISR
  .word Timer2b_ISR
  .word Analog_Comparator_0_ISR
  .word Analog_Comparator_1_ISR
  .word Analog_Comparator_2_ISR
  .word System_Control_ISR
  .word FLASH_Control_ISR

  .section .init, "ax"
  .thumb_func

DEFAULT_ISR_HANDLER NmiISR
DEFAULT_ISR_HANDLER FaultISR
DEFAULT_ISR_HANDLER SVCallISR
DEFAULT_ISR_HANDLER SysTickISR
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
DEFAULT_ISR_HANDLER Watchdog_timer_ISR
DEFAULT_ISR_HANDLER Timer0a_ISR
DEFAULT_ISR_HANDLER Timer0b_ISR
DEFAULT_ISR_HANDLER Timer1a_ISR
DEFAULT_ISR_HANDLER Timer1b_ISR
DEFAULT_ISR_HANDLER Timer2a_ISR
DEFAULT_ISR_HANDLER Timer2b_ISR
DEFAULT_ISR_HANDLER Analog_Comparator_0_ISR
DEFAULT_ISR_HANDLER Analog_Comparator_1_ISR
DEFAULT_ISR_HANDLER Analog_Comparator_2_ISR
DEFAULT_ISR_HANDLER System_Control_ISR
DEFAULT_ISR_HANDLER FLASH_Control_ISR

#ifndef STARTUP_FROM_RESET
DEFAULT_ISR_HANDLER reset_wait
#endif /* STARTUP_FROM_RESET */
