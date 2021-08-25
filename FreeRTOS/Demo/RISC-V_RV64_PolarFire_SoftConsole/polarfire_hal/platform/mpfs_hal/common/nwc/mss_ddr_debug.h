/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_ddr_debug.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief mss_ddr_debug related defines
 *
 */

/*=========================================================================*//**
  @page DDR setup and monitoring
  ==============================================================================
  @section intro_sec Introduction
  ==============================================================================
  DDR debug helper functions

  ==============================================================================
  @section Items located in the north west corner
  ==============================================================================
  -

  ==============================================================================
  @section Overview of DDR related hardware
  ==============================================================================

 *//*=========================================================================*/

#include <stddef.h>
#include <stdint.h>


#ifndef __MSS_DDr_DEBUG_H_
#define __MSS_DDr_DEBUG_H_ 1

#ifdef DEBUG_DDR_INIT
#include "drivers/mss/mss_mmuart/mss_uart.h"
#endif

#ifdef __cplusplus
extern "C" {
#endif

#ifndef TEST_64BIT_ACCESS
#define TEST_64BIT_ACCESS 1
#endif

#ifndef TEST_32BIT_ACCESS
#define TEST_32BIT_ACCESS 1
#endif

typedef enum DDR_ACCESS_SIZE_
{
    DDR_8_BIT,
    DDR_16_BIT,
    DDR_32_BIT,
    DDR_64_BIT
} DDR_ACCESS_SIZE;


/***************************************************************************//**
 The ddr_read_write_fn function is used to write/read test patterns to the DDR

  @return
    This function returns 0 if successful, number of errors if not.

  Example:
  @code

    if (ddr_read_write_fn() != 0U)
    {
        .. warn the user, increment error count , wait for watchdog reset
    }

  @endcode
 */
uint32_t
ddr_read_write_fn
(
uint64_t* DDR_word_ptr,
uint32_t no_access,
uint32_t pattern
);

#ifdef DEBUG_DDR_INIT
/***************************************************************************//**
  The uprint32() function is used to print to the designated debug port

  Example:
  @code

  (void)uprint32(g_debug_uart, "\n\r DDR_TRAINING_FAIL: ", error);

  @endcode
 */
void
uprint32
(
mss_uart_instance_t * uart,
const char* msg,
uint32_t d
);

/***************************************************************************//**
  The uprint64() function is used to print to the designated debug port

  Example:
  @code

  (void)uprint64(g_debug_uart, "\n\r DDR_TRAINING_FAIL: ", error);

  @endcode
 */
void
uprint64
(
mss_uart_instance_t * uart,
const char* msg,
uint64_t d
);

/***************************************************************************//**
  The error_status() function is used to print to the designated debug port

  Example:
  @code

  (void)error_status(g_debug_uart, "\n\r DDR_TRAINING_FAIL: ", error);

  @endcode
 */
uint32_t error_status(mss_uart_instance_t *g_mss_uart_debug_pt, uint32_t error);

/***************************************************************************//**
  The wrcalib_status() function is used to print to the designated debug port

  Example:
  @code

  (void)wrcalib_status(mss_uart_instance_t *g_mss_uart_debug_pt);

  @endcode
 */
uint32_t wrcalib_status(mss_uart_instance_t *g_mss_uart_debug_pt);

/***************************************************************************//**
  The tip_register_status() function is used to print ddr TIP status to the
  designated debug port

  Example:
  @code

  (void)tip_register_status(mss_uart_instance_t *g_mss_uart_debug_pt);

  @endcode
 */
uint32_t tip_register_status (mss_uart_instance_t *g_mss_uart_debug_pt);

/***************************************************************************//**
  The setup_ddr_debug_port() function is used to setup a serial port dedicated
  to printing information on the DDR start-up.

  @return
    This function returns 0 if successful

  Example:
  @code

    if (ddr_setup() != 0U)
    {
        .. warn the user, increment error count , wait for watchdog reset
    }

  @endcode
 */
uint32_t
setup_ddr_debug_port
(
mss_uart_instance_t * uart
);

/***************************************************************************//**
 *
 */
void
sweep_status
(
mss_uart_instance_t *g_mss_uart_debug_pt
);

/***************************************************************************//**
 *
 */
void
print_reg_array
(
mss_uart_instance_t * uart,
uint32_t *reg_pointer,
uint32_t no_of_regs
);
#endif

/***************************************************************************//**
 *
 */
void
load_ddr_pattern
(
uint64_t base,
uint32_t size,
uint8_t pattern_offset
);

/***************************************************************************//**
 *
 */
uint32_t
test_ddr
(
uint32_t no_of_iterations,
uint32_t size
);




#ifdef __cplusplus
}
#endif

#endif /* __MSS_DDRC_H_ */


