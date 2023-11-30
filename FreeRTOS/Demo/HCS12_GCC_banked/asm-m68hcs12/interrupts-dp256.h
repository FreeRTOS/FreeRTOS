/* Interrupt Vectors defined
   Copyright (C) 2004 Robotronics, Inc.
   Author Jefferson Smith, Robotronics

This file is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 2, or (at your option) any
later version.

In addition to the permissions in the GNU General Public License, the
Free Software Foundation gives you unlimited permission to link the
compiled version of this file with other programs, and to distribute
those programs without any restriction coming from the use of this
file.  (The General Public License restrictions do apply in other
respects; for example, they cover modification of the file, and
distribution when not linked into another program.)

This file is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; see the file COPYING.  If not, write to
the Free Software Foundation, 59 Temple Place - Suite 330,
Boston, MA 02111-1307, USA.  */

#ifndef _M68HC12_ASM_INTERRUPTS_DP256_H
#define _M68HC12_ASM_INTERRUPTS_DP256_H

/** Interrupt vectors as a struct.  */
struct interrupt_vectors
{
  interrupt_t res0_handler;        /* 0x80 */
  interrupt_t res1_handler;        /* 0x82 */
  interrupt_t res2_handler;        /* 0x84 */
  interrupt_t res3_handler;        /* 0x86 */
  interrupt_t res4_handler;        /* 0x88 */
  interrupt_t res5_handler;        /* 0x8a */
  interrupt_t pwm_shutdown_handler; /* 0x8c */
  interrupt_t ptpif_handler;
  
  /** Controller Area Networking */
  interrupt_t can4_tx_handler;
  interrupt_t can4_rx_handler;
  interrupt_t can4_err_handler;
  interrupt_t can4_wake_handler;
  interrupt_t can3_tx_handler;
  interrupt_t can3_rx_handler;
  interrupt_t can3_err_handler;
  interrupt_t can3_wake_handler;
  interrupt_t can2_tx_handler;
  interrupt_t can2_rx_handler;
  interrupt_t can2_err_handler;
  interrupt_t can2_wake_handler;
  interrupt_t can1_tx_handler;
  interrupt_t can1_rx_handler;
  interrupt_t can1_err_handler;
  interrupt_t can1_wake_handler;
  interrupt_t can0_tx_handler;
  interrupt_t can0_rx_handler;
  interrupt_t can0_err_handler;
  interrupt_t can0_wake_handler;
  
  interrupt_t flash_handler;
  interrupt_t eeprom_handler;
  interrupt_t spi2_handler;
  interrupt_t spi1_handler;
  interrupt_t iic_handler;
  interrupt_t bdlc_handler;
  interrupt_t selfclk_mode_handler;
  interrupt_t pll_lock_handler;
  interrupt_t accb_overflow_handler;
  interrupt_t mccnt_underflow_handler;
  interrupt_t pthif_handler;
  interrupt_t ptjif_handler;
  interrupt_t atd1_handler;
  interrupt_t atd0_handler;
  interrupt_t sci1_handler;
  interrupt_t sci0_handler;
  interrupt_t spi0_handler;
  
  /** Timer and Accumulator */
  interrupt_t acca_input_handler;
  interrupt_t acca_overflow_handler;
  interrupt_t timer_overflow_handler;
  
  /** Input capture / Output compare Timers */
  interrupt_t tc7_handler;
  interrupt_t tc6_handler;
  interrupt_t tc5_handler;
  interrupt_t tc4_handler;
  interrupt_t tc3_handler;
  interrupt_t tc2_handler;
  interrupt_t tc1_handler;
  interrupt_t tc0_handler;
  
  /** External Interrupts */
  interrupt_t rtii_handler;
  interrupt_t irq_handler;
  interrupt_t xirq_handler;

  /** Software Interrupt  */
  interrupt_t swi_handler;

  /** Illegal Instruction Reset  */
  interrupt_t illegal_handler;

  /** COP Timeout Reset  */
  interrupt_t cop_fail_handler;

  /** Clock Monitor Fail Reset  */
  interrupt_t cop_clock_handler;

  /** Start or Reset vector  */
  interrupt_t reset_handler;
};
typedef struct interrupt_vectors interrupt_vectors_t;

/** Interrupt vector id. */
enum interrupt_vector_id
{
  RES0_VECTOR = 0,
  RES1_VECTOR,
  RES2_VECTOR,
  RES3_VECTOR,
  RES4_VECTOR,
  RES5_VECTOR,
  PWM_SHUTDOWN_VECTOR,
  PTPIF_VECTOR,
  CAN4_TX_VECTOR,
  CAN4_RX_VECTOR,
  CAN4_ERR_VECTOR,
  CAN4_WAKE_VECTOR,
  CAN3_TX_VECTOR,
  CAN3_RX_VECTOR,
  CAN3_ERR_VECTOR,
  CAN3_WAKE_VECTOR,
  CAN2_TX_VECTOR,
  CAN2_RX_VECTOR,
  CAN2_ERR_VECTOR,
  CAN2_WAKE_VECTOR,
  CAN1_TX_VECTOR,
  CAN1_RX_VECTOR,
  CAN1_ERR_VECTOR,
  CAN1_WAKE_VECTOR,
  CAN0_TX_VECTOR,
  CAN0_RX_VECTOR,
  CAN0_ERR_VECTOR,
  CAN0_WAKE_VECTOR,
  FLASH_VECTOR,
  EEPROM_VECTOR,
  SPI2_VECTOR,
  SPI1_VECTOR,
  IIC_VECTOR,
  BDLC_VECTOR,
  SELFCLK_MODE_VECTOR,
  PLL_LOCK_VECTOR,
  ACCB_OVERFLOW_VECTOR,
  MCCNT_UNDERFLOW_VECTOR,
  PTHIF_VECTOR,
  PTJIF_VECTOR,
  ATD1_VECTOR,
  ATD0_VECTOR,
  SCI1_VECTOR,
  SCI0_VECTOR,
  SPI0_VECTOR,
  ACCA_INPUT_VECTOR,
  ACCA_OVERFLOW_VECTOR,
  TIMER_OVERFLOW_VECTOR,
  TC7_VECTOR,
  TC6_VECTOR,
  TC5_VECTOR,
  TC4_VECTOR,
  TC3_VECTOR,
  TC2_VECTOR,
  TC1_VECTOR,
  TC0_VECTOR,
  RTI_VECTOR,
  IRQ_VECTOR,
  XIRQ_VECTOR,
  SWI_VECTOR,
  ILLEGAL_OPCODE_VECTOR,
  COP_FAIL_VECTOR,
  COP_CLOCK_VECTOR,
  RESET_VECTOR,
  MAX_VECTORS
};
typedef enum interrupt_vector_id interrupt_vector_id;

/** some backwards-compatible equivalents from HC11 */
#define SCI_VECTOR           SCI0_VECTOR
#define SPI_VECTOR           SPI0_VECTOR
#define ACC_INPUT_VECTOR     ACCA_INPUT_VECTOR
#define ACC_OVERFLOW_VECTOR  ACCA_OVERFLOW_VECTOR

#endif  /* _M68HC12_ASM_INTERRUPTS_DP256_H */
