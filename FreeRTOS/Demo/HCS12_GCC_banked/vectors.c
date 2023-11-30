/* modrx.c -- wireless controller receiver for robots
   Copyright 2004 Robotronics, Inc.
   Author Jefferson Smith

   This file is part of the Modular Robot Design.
*/

#include "cpu.h"
#include <sys/ports.h>
#include <sys/interrupts.h>

void fatal_interrupt ()
{
  /* Infinite loop for debugging
     Returning would not help as it's necessary to clear the interrupt flag.
     */
  for (;;) cop_optional_reset();
}

#ifdef USE_INTERRUPT_TABLE

/* NOTE: these ISR must be in non-banked memory (near) */

/* Manual context switch function.  This is the SWI ISR. */
void ATTR_INT ATTR_NEAR vPortYield( void );

/* Tick context switch function.  This is the timer ISR. */
void ATTR_INT ATTR_NEAR vPortTickInterrupt( void );

void ATTR_INT ATTR_NEAR vCOM_ISR( void );

/* Interrupt vectors table.

   Note: the `XXX_handler: foo' notation is a GNU extension which is
   used here to ensure correct association of the handler in the struct.
   This is why the order of handlers declared below does not follow
   the MCU order.  */
const struct interrupt_vectors __attribute__((section(".vectors"))) vectors = 
{
  pwm_shutdown_handler:	fatal_interrupt,
  ptpif_handler:		fatal_interrupt,
  can4_tx_handler:		fatal_interrupt,
  can4_rx_handler:		fatal_interrupt,
  can4_err_handler:		fatal_interrupt,
  can4_wake_handler:	fatal_interrupt,
  can3_tx_handler:		fatal_interrupt,
  can3_rx_handler:		fatal_interrupt,
  can3_err_handler:		fatal_interrupt,
  can3_wake_handler:	fatal_interrupt,
  can2_tx_handler:		fatal_interrupt,
  can2_rx_handler:		fatal_interrupt,
  can2_err_handler:		fatal_interrupt,
  can2_wake_handler:	fatal_interrupt,
  can1_tx_handler:		fatal_interrupt,
  can1_rx_handler:		fatal_interrupt,
  can1_err_handler:		fatal_interrupt,
  can1_wake_handler:	fatal_interrupt,
  can0_tx_handler:		fatal_interrupt,
  can0_rx_handler:		fatal_interrupt,
  can0_err_handler:		fatal_interrupt,
  can0_wake_handler:	fatal_interrupt,
  flash_handler:		fatal_interrupt,
  eeprom_handler:		fatal_interrupt,
  spi2_handler:			fatal_interrupt,
  spi1_handler:			fatal_interrupt,
  iic_handler:			fatal_interrupt,
  bdlc_handler:			fatal_interrupt,
  selfclk_mode_handler:	fatal_interrupt,
  pll_lock_handler:		fatal_interrupt,
  accb_overflow_handler: fatal_interrupt,
  mccnt_underflow_handler: fatal_interrupt,
  pthif_handler:		fatal_interrupt,
  ptjif_handler:		fatal_interrupt,
  atd1_handler:			fatal_interrupt,
  atd0_handler:			fatal_interrupt,
  sci1_handler:			fatal_interrupt,
  sci0_handler:			fatal_interrupt,
  spi0_handler:			fatal_interrupt,

  /** Timer and Accumulator */
  acca_input_handler:	fatal_interrupt,
  acca_overflow_handler: fatal_interrupt,
  timer_overflow_handler: fatal_interrupt,
  
  /** Input capture / Output compare Timers */
  tc7_handler:			fatal_interrupt,
  tc6_handler:			fatal_interrupt,
  tc5_handler:			fatal_interrupt,
  tc4_handler:			fatal_interrupt,
  tc3_handler:			fatal_interrupt,
  tc2_handler:			fatal_interrupt,
  tc1_handler:			fatal_interrupt,
  tc0_handler:			fatal_interrupt,

  /** External Interrupts */
  rtii_handler:			fatal_interrupt,
  irq_handler:			fatal_interrupt,
  xirq_handler:			fatal_interrupt,

  illegal_handler:		fatal_interrupt,
  cop_fail_handler:		fatal_interrupt,
  cop_clock_handler:	fatal_interrupt,

  /** Vectors in use */
  swi_handler:			vPortYield,
  rtii_handler:			vPortTickInterrupt,
#if M6812_DEF_SCI==1
  sci1_handler:			vCOM_ISR,
#else
  sci0_handler:			vCOM_ISR,
#endif
  reset_handler:		_start
};
#endif

