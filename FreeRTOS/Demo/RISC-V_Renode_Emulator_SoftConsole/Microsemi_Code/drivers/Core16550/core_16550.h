/*******************************************************************************
 * (c) Copyright 2007-2015 Microsemi SoC Products Group. All rights reserved.
 *
 * This file contains the application programming interface for the Core16550
 * bare metal driver.
 *
 * SVN $Revision: 7963 $
 * SVN $Date: 2015-10-09 17:58:21 +0530 (Fri, 09 Oct 2015) $
 */
/*=========================================================================*//**
  @mainpage Core16550 Bare Metal Driver.

  @section intro_sec Introduction
  The Core16550 is an implementation of the Universal Asynchronous
  Receiver/Transmitter aimed at complete compliance to standard 16550 UART.
  The Core16550 bare metal software driver is designed for use in systems
  with no operating system.

  The Core16550 driver provides functions for polled and interrupt driven
  transmitting and receiving. It also provides functions for reading the
  values from different status registers, enabling and disabling interrupts
  at Core16550 level. The Core16550 driver is provided as C source code.

  @section driver_configuration Driver Configuration
  Your application software should configure the Core16550 driver through
  calls to the UART_16550_init() function for each Core16550 instance in
  the hardware design. The configuration parameters include the Core16550
  hardware instance base address and other runtime parameters, such as baud
  value, bit width, and parity.

  No Core16550 hardware configuration parameters are needed by the driver,
  apart from the Core16550 hardware instance base address. Hence, no
  additional configuration files are required to use the driver.

  @section theory_op Theory of Operation
  The Core16550 software driver is designed to allow the control of multiple
  instances of Core16550. Each instance of Core16550 in the hardware design
  is associated with a single instance of the uart_16550_instance_t structure
  in the software. You need to allocate memory for one unique
  uart_16550_instance_t structure instance for each Core16550 hardware instance.
  The contents of these data structures are initialized during calls to
  function UART_16550_init(). A pointer to the structure is passed to
  subsequent driver functions in order to identify the Core16550 hardware
  instance you wish to perform the requested operation on.

  Note:     Do not attempt to directly manipulate the content of
  uart_16550_instance_t structures. This structure is only intended to be
  modified by the driver function.

  Initialization
  The Core16550 driver is initialized through a call to the UART_16550_init()
  function. This function takes the UART’s configuration as parameters.
  The UART_16550_init() function must be called before any other Core16550
  driver functions can be called.

  Polled Transmission and Reception
  The driver can be used to transmit and receive data once initialized. Polled
  operations where the driver constantly polls the state of the UART registers
  in order to control data transmit or data receive are performed using these
  functions:
         •  UART_16550_polled_tx()
         •  UART_16550_polled_tx_string
         •  UART_16550_fill_tx_fifo()
         •  UART_16550_get_rx()

  Data is transmitted using the UART_16550_polled_tx() function. This function
  is blocking, meaning that it will only return once the data passed to the
  function has been sent to the Core16550 hardware. Data received by the
  Core16550 hardware can be read by the UART_16550_get_rx() function.

  The UART_16550_polled_tx_string() function is provided to transmit a NULL (‘\0’)
  terminated string in polled mode. This function is blocking, meaning that it
  will only return once the data passed to the function has been sent to the
  Core16550 hardware.

  The UART_16550_fill_tx_fifo() function fills the Core16550 hardware transmit
  FIFO with data from a buffer passed as a parameter and returns the number of
  bytes transferred to the FIFO. If the transmit FIFO is not empty when the
  UART_16550_fill_tx_fifo() function is called it returns immediately without
  transferring any data to the FIFO.

  Interrupt Driven Operations
  The driver can also transmit or receive data under interrupt control, freeing
  your application to perform other tasks until an interrupt occurs indicating
  that the driver’s attention is required. Interrupt controlled UART operations
  are performed using these functions:
        •   UART_16550_isr()
        •   UART_16550_irq_tx()
        •   UART_16550_tx_complete()
        •   UART_16550_set_tx_handler()
        •   UART_16550_set_rx_handler()
        •   UART_16550_set_rxstatus_handler()
        •   UART_16550_set_modemstatus_handler()
        •   UART_16550_enable_irq()
        •   UART_16550_disable_irq()

  Interrupt Handlers
  The UART_16550_isr() function is the top level interrupt handler function for
  the Core16550 driver. You must call it from the system level
  (CoreInterrupt and NVIC level) interrupt service routine (ISR) assigned to the
  interrupt triggered by the Core16550 INTR signal. The UART_16550_isr() function
  identifies the source of the Core16550 interrupt and calls the corresponding
  handler function previously registered with the driver through calls to the
  UART_16550_set_rx_handler(), UART_16550_set_tx_handler(),
  UART_16550_set_rxstatus_handler(), and UART_16550_set_modemstatus_handler()
  functions. You are responsible for creating these lower level interrupt handlers
  as part of your application program and registering them with the driver.
  The UART_16550_enable_irq() and UART_16550_disable_irq() functions are used to
  enable or disable the received line status, received data available/character
  timeout, transmit holding register empty and modem status interrupts at the
  Core16550 level.

  Transmitting Data
  Interrupt-driven transmit is initiated by a call to UART_16550_irq_tx(),
  specifying the block of data to transmit. Your application is then free to
  perform other tasks and inquire later whether transmit has completed by calling
  the UART_16550_tx_complete() function. The UART_16550_irq_tx() function enables
  the UART’s transmit holding register empty (THRE) interrupt and then, when the
  interrupt goes active, the driver’s default THRE interrupt handler transfers
  the data block to the UART until the entire block is transmitted.

  Note:     You can use the UART_16550_set_tx_handler() function to assign an
  alternative handler to the THRE interrupt. In this case, you must not use the
  UART_16550_irq_tx() function to initiate the transmit, as this will re-assign
  the driver’s default THRE interrupt handler to the THRE interrupt. Instead,
  your alternative THRE interrupt handler must include a call to the
  UART_16550_fill_tx_fifo() function to transfer the data to the UART.

  Receiving Data
  Interrupt-driven receive is performed by first calling UART_16550_set_rx_handler()
  to register a receive handler function that will be called by the driver whenever
  receive data is available. You must provide this receive handler function which
  must include a call to the UART_16550_get_rx() function to actually read the
  received data.

  UART Status
  The function UART_16550_get_rx_status() is used to read the receiver error status.
  This function returns the overrun, parity, framing, break, and FIFO error status
  of the receiver.
  The function UART_16550_get_tx_status() is used to read the transmitter status.
  This function returns the transmit empty (TEMT) and transmit holding register
  empty (THRE) status of the transmitter.
  The function UART_16550_get_modem_status() is used to read the modem status flags.
  This function returns the current value of the modem status register.

  Loopback
  The function UART_16550_set_loopback() is used to enable or disable loopback
  between Tx and Rx lines internal to Core16550.
*//*=========================================================================*/
#ifndef __CORE_16550_H
#define __CORE_16550_H 1

#include "cpu_types.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * Receiver Error Status
 * The following defines are used to determine the UART receiver error type.
 * These bit mask constants are used with the return value of the
 * UART_16550_get_rx_status() function to find out if any errors occurred
 * while receiving data.
 */
#define UART_16550_NO_ERROR         ( (uint8_t) 0x00 )
#define UART_16550_OVERRUN_ERROR    ( (uint8_t) 0x02 )
#define UART_16550_PARITY_ERROR     ( (uint8_t) 0x04 )
#define UART_16550_FRAMING_ERROR    ( (uint8_t) 0x08 )
#define UART_16550_BREAK_ERROR      ( (uint8_t) 0x10 )
#define UART_16550_FIFO_ERROR       ( (uint8_t) 0x80 )
#define UART_16550_INVALID_PARAM    ( (uint8_t) 0xFF )

/***************************************************************************//**
 * Modem Status
 * The following defines are used to determine the modem status. These bit
 * mask constants are used with the return value of the
 * UART_16550_get_modem_status() function to find out the modem status of
 * the UART.
 */
#define UART_16550_DCTS             ( (uint8_t) 0x01 )
#define UART_16550_DDSR             ( (uint8_t) 0x02 )
#define UART_16550_TERI             ( (uint8_t) 0x04 )
#define UART_16550_DDCD             ( (uint8_t) 0x08 )
#define UART_16550_CTS              ( (uint8_t) 0x10 )
#define UART_16550_DSR              ( (uint8_t) 0x20 )
#define UART_16550_RI               ( (uint8_t) 0x40 )
#define UART_16550_DCD              ( (uint8_t) 0x80 )

/***************************************************************************//**
 * Transmitter Status
 * The following definitions are used to determine the UART transmitter status.
 * These bit mask constants are used with the return value of the
 * UART_16550_get_tx_status() function to find out the status of the
 * transmitter.
 */
#define UART_16550_TX_BUSY          ( (uint8_t) 0x00 )
#define UART_16550_THRE             ( (uint8_t) 0x20 )
#define UART_16550_TEMT             ( (uint8_t) 0x40 )

/***************************************************************************//**
 * Core16550 Interrupts
 * The following defines are used to enable and disable Core16550 interrupts.
 * They are used to build the value of the irq_mask parameter for the
 * UART_16550_enable_irq() and UART_16550_disable_irq() functions. A bitwise
 * OR of these constants is used to enable or disable multiple interrupts.
 */
#define UART_16550_RBF_IRQ          ( (uint8_t) 0x01 )
#define UART_16550_TBE_IRQ          ( (uint8_t) 0x02 )
#define UART_16550_LS_IRQ           ( (uint8_t) 0x04 )
#define UART_16550_MS_IRQ           ( (uint8_t) 0x08 )

/***************************************************************************//**
 * Data Width
 * The following defines are used to build the value of the UART_16550_init()
 * function line_config parameter.
 */
#define UART_16550_DATA_5_BITS      ( (uint8_t) 0x00 )
#define UART_16550_DATA_6_BITS      ( (uint8_t) 0x01 )
#define UART_16550_DATA_7_BITS      ( (uint8_t) 0x02 )
#define UART_16550_DATA_8_BITS      ( (uint8_t) 0x03 )

/***************************************************************************//**
 * Parity Control
 * The following defines are used to build the value of the UART_16550_init()
 * function line_config parameter.
 */
#define UART_16550_NO_PARITY            ( (uint8_t) 0x00 )
#define UART_16550_ODD_PARITY           ( (uint8_t) 0x08 )
#define UART_16550_EVEN_PARITY          ( (uint8_t) 0x18 )
#define UART_16550_STICK_PARITY_1       ( (uint8_t) 0x28 )
#define UART_16550_STICK_PARITY_0       ( (uint8_t) 0x38 )

/***************************************************************************//**
 * Number of Stop Bits
 * The following defines are used to build the value of the UART_16550_init()
 * function line_config parameter.
 */
#define UART_16550_ONE_STOP_BIT     ( (uint8_t) 0x00 )
/*only when data bits is 5*/
#define UART_16550_ONEHALF_STOP_BIT ( (uint8_t) 0x04 )
/*only when data bits is not 5*/
#define UART_16550_TWO_STOP_BITS    ( (uint8_t) 0x04 )

/***************************************************************************//**
  This enumeration specifies the receiver FIFO trigger level. This is the number
  of bytes that must be received before the UART generates a receive data
  available interrupt. It provides the allowed values for the
  UART_16550_set_rx_handler() function’s trigger_level parameter.
 */
typedef enum {
    UART_16550_FIFO_SINGLE_BYTE    = 0,
    UART_16550_FIFO_FOUR_BYTES     = 1,
    UART_16550_FIFO_EIGHT_BYTES    = 2,
    UART_16550_FIFO_FOURTEEN_BYTES = 3,
    UART_16550_FIFO_INVALID_TRIG_LEVEL
} uart_16550_rx_trig_level_t;

/***************************************************************************//**
  This enumeration specifies the Loopback configuration of the UART. It provides
  the allowed values for the UART_16550_set_loopback() function’s loopback
  parameter.
 */
typedef enum {
    UART_16550_LOOPBACK_OFF   = 0,
    UART_16550_LOOPBACK_ON    = 1,
    UART_16550_INVALID_LOOPBACK
} uart_16550_loopback_t;

/***************************************************************************//**
  This is type definition for Core16550 instance. You need to create and
  maintain a record of this type. This holds all data regarding the Core16550
  instance.
 */
typedef struct uart_16550_instance uart_16550_instance_t;

/***************************************************************************//**
  This typedef specifies the function prototype for Core16550 interrupt handlers.
  All interrupt handlers registered with the Core16550 driver must be of this
  type. The interrupt handlers are registered with the driver through the
  UART_16550_set_rx_handler(), UART_16550_set_tx_handler(),
  UART_16550_set_rxstatus_handler(), and UART_16550_set_modemstatus_handler()
  functions.

  The this_uart parameter is a pointer to a uart_16550_instance_t structure that
  holds all data regarding this instance of the Core16550.
 */
typedef void (*uart_16550_irq_handler_t)(uart_16550_instance_t * this_uart);

/***************************************************************************//**
  uart_16550_instance.
  This structure is used to identify the various Core16550 hardware instances
  in your system. Your application software should declare one instance of this
  structure for each instance of Core16550 in your system. The function
  UART_16550_init() initializes this structure. A pointer to an initialized
  instance of the structure should be passed as the first parameter to the
  Core16550 driver functions, to identify which Core16550 hardware instance
  should perform the requested operation.
 */
struct uart_16550_instance{
    /* Core16550 instance base address: */
    addr_t      base_address;
    /* Accumulated status: */
    uint8_t     status;

    /* transmit related info: */
    const uint8_t*  tx_buffer;
    uint32_t        tx_buff_size;
    uint32_t        tx_idx;

    /* line status (OE, PE, FE & BI) interrupt handler:*/
    uart_16550_irq_handler_t linests_handler;
    /* receive interrupt handler:*/
    uart_16550_irq_handler_t rx_handler;
    /* transmitter holding register interrupt handler:*/
    uart_16550_irq_handler_t tx_handler;
    /* modem status interrupt handler:*/
    uart_16550_irq_handler_t modemsts_handler;
};

/***************************************************************************//**
 * The UART_16550_init() function initializes the driver’s data structures and
 * the Core16550 hardware with the configuration passed as parameters.. The
 * configuration parameters are the baud_value used to generate the baud rate,
 * and the line_config used to specify the line configuration (bit length,
 * stop bits and parity).
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550. This pointer
 *                      is used to identify the target Core16550 hardware
 *                      instance in subsequent calls to the Core16550 driver
 *                      functions.
 * @param base_addr     The base_address parameter is the base address in the
 *                      processor's memory map for the registers of the
 *                      Core16550 instance being initialized.
 * @param baud_value    The baud_value parameter is used to select the baud rate
 *                      for the UART. The baud value is calculated from the
 *                      frequency of the system clock in Hertz and the desired
 *                      baud rate using the following equation:
 *
 *                      baud_value = (clock /(baud_rate * 16))
 *
 *                      The baud_value parameter must be a value in the range 0
 *                      to 65535 (or 0x0000 to 0xFFFF).
 * @param line_config   This parameter is the line configuration specifying the
 *                      bit length, number of stop bits and parity settings. This
 *                      is a bitwise OR of one value from each of the following
 *                      groups of allowed values:
 *                      •   Data lengths:
 *                          UART_16550_DATA_5_BITS
 *                          UART_16550_DATA_6_BITS
 *                          UART_16550_DATA_7_BITS
 *                          UART_16550_DATA_8_BITS
 *                      •   Parity types:
 *                          UART_16550_NO_PARITY
 *                          UART_16550_EVEN_PARITY
 *                          UART_16550_ODD_PARITY
 *                          UART_16550_STICK_PARITY_0
 *                          UART_16550_STICK_PARITY_1
 *                      •   Number of stop bits:
 *                          UART_16550_ONE_STOP_BIT
 *                          UART_16550_ONEHALF_STOP_BIT
 *                          UART_16550_TWO_STOP_BITS
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 * #define UART_16550_BASE_ADDR   0x2A000000
 * #define BAUD_VALUE_57600    26
 *
 * uart_16550_instance_t g_uart;
 *
 * UART_16550_init( &g_uart, UART_16550_BASE_ADDR, BAUD_VALUE_57600,
 *                  (UART_16550_DATA_8_BITS |
 *                   UART_16550_EVEN_PARITY |
 *                   UART_16550_ONE_STOP_BIT) );
 * @endcode
 */
void
UART_16550_init
(
    uart_16550_instance_t* this_uart,
    addr_t base_addr,
    uint16_t baud_value,
    uint8_t line_config
);

/***************************************************************************//**
 * The UART_16550_polled_tx() function is used to transmit data. It transfers
 * the contents of the transmitter data buffer, passed as a function parameter,
 * into the UART's hardware transmitter FIFO. It returns when the full content
 * of the transmitter data buffer has been transferred to the UART's transmitter
 * FIFO. It is safe to release or reuse the memory used as the transmitter data
 * buffer once this function returns.
 *
 * Note:    This function reads the UART’s line status register (LSR) to poll
 * for the active state of the transmitter holding register empty (THRE) bit
 * before transferring data from the data buffer to the transmitter FIFO. It
 * transfers data to the transmitter FIFO in blocks of 16 bytes or less and
 * allows the FIFO to empty before transferring the next block of data.
 *
 * Note:    The actual transmission over the serial connection will still be in
 * progress when this function returns. Use the UART_16550_get_tx_status()
 * function if you need to know when the transmitter is empty.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all
 *                      data regarding this instance of the Core16550.
 * @param pbuff         The pbuff parameter is a pointer to a buffer containing
 *                      the data to be transmitted.
 * @param tx_size       The tx_size parameter is the size, in bytes, of the
 *                      data to be transmitted.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   uint8_t testmsg1[] = {"\n\r\n\r\n\rUART_16550_polled_tx() test message 1"};
 *   UART_16550_polled_tx(&g_uart,(const uint8_t *)testmsg1,sizeof(testmsg1));
 * @endcode
 */
void
UART_16550_polled_tx
(
    uart_16550_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
);
/***************************************************************************//**
 * The UART_16550_polled_tx_string() function is used to transmit a NULL ('\0')
 * terminated string. It transfers the text string, from the buffer starting at
 * the address pointed to by p_sz_string, into the UART’s hardware transmitter
 * FIFO. It returns when the complete string has been transferred to the UART's
 * transmit FIFO. It is safe to release or reuse the memory used as the string
 * buffer once this function returns.
 *
 * Note:    This function reads the UART’s line status register (LSR) to poll
 * for the active state of the transmitter holding register empty (THRE) bit
 * before transferring data from the data buffer to the transmitter FIFO. It
 * transfers data to the transmitter FIFO in blocks of 16 bytes or less and
 * allows the FIFO to empty before transferring the next block of data.
 *
 * Note:    The actual transmission over the serial connection will still be
 * in progress when this function returns. Use the UART_16550_get_tx_status()
 * function if you need to know when the transmitter is empty.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param p_sz_string   The p_sz_string parameter is a pointer to a buffer
 *                      containing the NULL ('\0') terminated string to be
 *                      transmitted.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   uint8_t testmsg1[] = {"\r\n\r\nUART_16550_polled_tx_string() test message 1\0"};
 *   UART_16550_polled_tx_string(&g_uart,(const uint8_t *)testmsg1);
 * @endcode
 */
void
UART_16550_polled_tx_string
(
    uart_16550_instance_t * this_uart,
    const uint8_t * p_sz_string
);

/***************************************************************************//**
 * The UART_16550_irq_tx() function is used to initiate an interrupt driven
 * transmit. It returns immediately after making a note of the transmit buffer
 * location and enabling the transmitter holding register empty (THRE) interrupt
 * at the Core16550 level. This function takes a pointer via the pbuff parameter
 * to a memory buffer containing the data to transmit. The memory buffer
 * specified through this pointer must remain allocated and contain the data to
 * transmit until the transmit completion has been detected through calls to
 * function UART_16550_tx_complete().The actual transmission over the serial
 * connection is still in progress until calls to the UART_16550_tx_complete()
 * function indicate transmit completion.
 *
 * Note:    It is your responsibility to call UART_16550_isr(), the driver’s
 * top level interrupt handler function, from the system level (CoreInterrupt
 * and NVIC level) interrupt handler assigned to the interrupt triggered by the
 * Core16550 INTR signal. You must do this before using the UART_16550_irq_tx()
 * function.
 *
 * Note:    It is also your responsibility to enable the system level
 * (CoreInterrupt and NVIC level) interrupt connected to the Core16550 INTR
 * interrupt signal.
 *
 * Note:    The UART_16550_irq_tx() function assigns an internal default transmit
 * interrupt handler function to the UART’s THRE interrupt. This interrupt handler
 * overrides any custom interrupt handler that you may have previously registered
 * using the UART_16550_set_tx_handler() function.
 *
 * Note:    The UART_16550_irq_tx() function’s default transmit interrupt handler
 * disables the UART’s THRE interrupt when all of the data has been transferred
 * to the UART's transmit FIFO.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param pbuff         The pbuff parameter is a pointer to a buffer containing
 *                      the data to be transmitted.
 * @param tx_size       The tx_size parameter specifies the size, in bytes, of
 *                      the data to be transmitted.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 * uint8_t tx_buff[10] = "abcdefghi";
 *
 * UART_16550_irq_tx( &g_uart, tx_buff, sizeof(tx_buff));
 * while ( 0 == UART_16550_tx_complete( &g_uart ) )
 * { ; }
 * @endcode
 */
void
UART_16550_irq_tx
(
    uart_16550_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
);

/***************************************************************************//**
 * The UART_16550_tx_complete() function is used to find out if the interrupt
 * driven transmit previously initiated through a call to UART_16550_irq_tx()
 * is complete. This function is typically used to find out when it is safe
 * to reuse or release the memory buffer holding the transmit data.
 *
 * Note:    The transfer of all of the data from the memory buffer to the UART’s
 * transmit FIFO and the actual transmission over the serial connection are both
 * complete when a call to the UART_16550_tx_complete() function indicate
 * transmit completion.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @return              This function returns a non-zero value if transmit has
 *                      completed, otherwise it returns zero.
 *  Example:
 *   See the UART_16550_irq_tx() function for an example that uses the
 *   UART_16550_tx_complete() function.
 */
int8_t
UART_16550_tx_complete
(
   uart_16550_instance_t * this_uart
);

/***************************************************************************//**
 * The UART_16550_get_rx() function reads the content of the Core16550
 * receiver’s FIFO and stores it in the receive buffer that is passed via the
 * rx_buff function parameter. It copies either the full contents of the FIFO
 * into the receive buffer, or just enough data from the FIFO to fill the receive
 * buffer, dependent upon the size of the receive buffer passed by the buff_size
 * parameter. The UART_16550_get_rx() function returns the number of bytes copied
 * into the receive buffer .This function is non-blocking and will return 0
 * immediately if no data has been received.
 *
 * Note:    The UART_16550_get_rx() function reads and accumulates the receiver
 * status of the Core16550 instance before reading each byte from the receiver's
 * data register/FIFO. This allows the driver to maintain a sticky record of any
 * receiver errors that occur as the UART receives each data byte; receiver errors
 * would otherwise be lost after each read from the receiver's data register. A call
 * to the UART_16550_get_rx_status() function returns any receiver errors accumulated
 * during the execution of the UART_16550_get_rx() function.
 *
 * Note:    If you need to read the error status for each byte received, set the
 * buff_size to 1 and read the receive line error status for each byte using the
 * UART_16550_get_rx_status() function.
 * The UART_16550_get_rx() function can be used in polled mode, where it is called
 * at regular intervals to find out if any data has been received, or in interrupt
 * driven-mode, where it is called as part of a receive handler that is called by
 * the driver as a result of data being received.
 *
 * Note:    In interrupt driven mode you should call the UART_16550_get_rx()
 * function as part of the receive handler function that you register with the
 * Core16550 driver through a call to UART_16550_set_rx_handler().
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param rx_buff       The rx_buff parameter is a pointer to a memory buffer
 *                      where the received data is copied.
 * @param buff_size     The buff_size parameter is the size of the receive
 *                      buffer in bytes.
 * @return              This function returns the number of bytes copied into
 *                      the receive buffer.
 * Example:
 * @code
 *   #define MAX_RX_DATA_SIZE    256
 *
 *   uint8_t rx_data[MAX_RX_DATA_SIZE];
 *   uint8_t rx_size = 0;
 *
 *   rx_size = UART_16550_get_rx( &g_uart, rx_data, sizeof(rx_data) );
 * @endcode
 */
size_t
UART_16550_get_rx
(
   uart_16550_instance_t * this_uart,
   uint8_t * rx_buff,
   size_t buff_size
);

/***************************************************************************//**
 * The UART_16550_isr() function is the top level interrupt handler function for
 * the Core16550 driver. You must call UART_16550_isr() from the system level
 * (CoreInterrupt and NVIC level) interrupt handler assigned to the interrupt
 * triggered by the Core16550 INTR signal. Your system level interrupt handler
 * must also clear the system level interrupt triggered by the Core16550 INTR
 * signal before returning, to prevent a re-assertion of the same interrupt.
 *
 * Note:    This function supports all types of interrupt triggered by Core16550.
 * It is not a complete interrupt handler by itself; rather, it is a top level
 * wrapper that abstracts Core16550 interrupt handling by calling lower level
 * handler functions specific to each type of Core16550 interrupt. You must
 * create the lower level handler functions to suit your application and
 * register them with the driver through calls to the UART_16550_set_rx_handler(),
 * UART_16550_set_tx_handler(), UART_16550_set_rxstatus_handler() and
 * UART_16550_set_modemstatus_handler() functions.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 *
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   void CIC_irq1_handler(void)
 *   {
 *      UART_16550_isr( &g_uart );
 *   }
 * @endcode
 */
void
UART_16550_isr
(
   uart_16550_instance_t * this_uart
);

/***************************************************************************//**
 * The UART_16550_set_rx_handler() function is used to register a receive handler
 * function that is called by the driver when a UART receive data available (RDA)
 * interrupt occurs. The UART_16550_set_rx_handler() function also enables the
 * RDA interrupt at the Core16550 level. You must create and register the receive
 * handler function to suit your application and it must include a call to the
 * UART_16550_get_rx() function to actually read the received data.
 *
 * Note:    The driver’s top level interrupt handler function UART_16550_isr()
 * will call your receive handler function in response to an RDA interrupt from
 * the Core16550.
 *
 * Note:    You can disable the RDA interrupt once the data is received by calling
 * the UART_16550_disable_irq() function. This is your choice and is dependent
 * upon your application.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param handler       The handler parameter is a pointer to a receive interrupt
 *                      handler function provided by your application that will be
 *                      called as a result of a UART RDA interrupt. This handler
 *                      function must be of type uart_16550_irq_handler_t.
 * @param trigger_level The trigger_level parameter is the receive FIFO
 *                      trigger level. This specifies the number of bytes that
 *                      must be received before the UART triggers an RDA
 *                      interrupt.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 * #include "core_16550.h"
 *
 * #define RX_BUFF_SIZE    64
 * #define UART_57600_BAUD 26
 *
 * uint8_t g_rx_buff[RX_BUFF_SIZE];
 * uart_16550_instance_t g_uart;
 * void uart_rx_handler( uart_16550_instance_t * this_uart )
 * {
 *     UART_16550_get_rx( this_uart, g_rx_buff, RX_BUFF_SIZE );
 * }
 *
 * int main(void)
 * {
 *     UART_16550_init( &g_uart, UART_57600_BAUD,
 *                       ( UART_16550_DATA_8_BITS | UART_16550_NO_PARITY ) );
 *     UART_16550_set_rx_handler( &g_uart, uart_rx_handler,
 *                                UART_16550_FIFO_SINGLE_BYTE);
 *     while ( 1 )
 *     {
 *         ;
 *     }
 *     return(0);
 * }
 * @endcode
 */
void
UART_16550_set_rx_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler,
    uart_16550_rx_trig_level_t trigger_level
);

/***************************************************************************//**
 * The UART_16550_set_loopback() function is used to locally loopback the Tx
 * and Rx lines of a Core16550 UART.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param loopback      The loopback parameter indicates whether or not the
 *                      UART's transmit and receive lines should be looped back.
 *                      Allowed values are as follows:
 *                      •   UART_16550_LOOPBACK_ON
 *                      •   UART_16550_LOOPBACK_OFF
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 * #include "core_16550.h"
 *
 * #define UART_57600_BAUD 26
 * #define DATA_SIZE 4
 *
 * uart_16550_instance_t g_uart;
 *
 * int main(void)
 * {
 *      uint8_t txbuf[DATA_SIZE] = "abc";
 *      uint8_t rxbuf[DATA_SIZE];
 *      UART_16550_init( &g_uart, UART_57600_BAUD,
 *                        ( UART_16550_DATA_8_BITS | UART_16550_NO_PARITY |
 *                                               UART_16550_ONE_STOP_BIT) );
 *      UART_16550_set_loopback( &g_uart, UART_16550_LOOPBACK_ON );
 *
 *      while(1)
 *      {
 *          UART_16550_polled_tx( &g_uart, txbuf, DATA_SIZE);
 *          delay(100);
 *          UART_16550_get_rx( &g_uart, rxbuf, DATA_SIZE);
 *      }
 * }
 * @endcode
 */
void
UART_16550_set_loopback
(
    uart_16550_instance_t * this_uart,
    uart_16550_loopback_t loopback
);

/***************************************************************************//**
 * The UART_16550_get_rx_status() function returns the receiver error status of
 * the Core16550 instance. It reads both the current error status of the receiver
 * from the UART’s line status register (LSR) and the accumulated error status
 * from preceding calls to the UART_16550_get_rx() function, and it combines
 * them using a bitwise OR. It returns the cumulative overrun, parity, framing,
 * break and FIFO error status of the receiver, since the previous call to
 * UART_16550_get_rx_status(), as an 8-bit encoded value.
 *
 * Note:    The UART_16550_get_rx() function reads and accumulates the receiver
 * status of the Core16550 instance before reading each byte from the receiver’s
 * data register/FIFO. The driver maintains a sticky record of the cumulative
 * receiver error status, which persists after the UART_16550_get_rx() function
 * returns. The UART_16550_get_rx_status() function clears the driver’s sticky
 * receiver error record before returning.
 *
 * Note:    The driver’s transmit functions also read the line status register
 * (LSR) as part of their implementation. When the driver reads the LSR, the
 * UART clears any active receiver error bits in the LSR. This could result in
 * the driver losing receiver errors. To avoid any loss of receiver errors, the
 * transmit functions also update the driver’s sticky record of the cumulative
 * receiver error status whenever they read the LSR.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @return              This function returns the UART’s receiver error status
 *                      as an 8-bit unsigned integer. The returned value is 0
 *                      if no receiver errors occurred. The driver provides a
 *                      set of bit mask constants that should be compared with
 *                      and/or used to mask the returned value to determine the
 *                      receiver error status.
 *                      When the return value is compared to the following bit
 *                      masks, a non-zero result indicates that the
 *                      corresponding error occurred:
 *                      •   UART_16550_OVERRUN_ERROR    (bit mask = 0x02)
 *                      •   UART_16550_PARITY_ERROR     (bit mask = 0x04)
 *                      •   UART_16550_FRAMING_ERROR    (bit mask = 0x08)
 *                      •   UART_16550_BREAK_ERROR      (bit mask = 0x10)
 *                      •   UART_16550_FIFO_ERROR       (bit mask = 0x80)
 *                      When the return value is compared to the following bit
 *                      mask, a non-zero result indicates that no error occurred:
 *                      •   UART_16550_NO_ERROR         (bit mask = 0x00)
 *                      Upon unsuccessful execution, this function returns:
 *                      •   UART_16550_INVALID_PARAM    (bit mask = 0xFF)
 *
 * Example:
 * @code
 *   uart_16550_instance_t g_uart;
 *   uint8_t rx_data[MAX_RX_DATA_SIZE];
 *   uint8_t err_status;
 *
 *   err_status = UART_16550_get_rx_status(&g_uart);
 *   if(UART_16550_NO_ERROR == err_status )
 *   {
 *        rx_size = UART_16550_get_rx( &g_uart, rx_data, MAX_RX_DATA_SIZE );
 *   }
 * @endcode
 */
uint8_t
UART_16550_get_rx_status
(
    uart_16550_instance_t * this_uart
);
/***************************************************************************//**
 * The UART_16550_enable_irq() function enables the Core16550 interrupts
 * specified by the irq_mask parameter. The irq_mask parameter identifies the
 * Core16550 interrupts by bit position, as defined in the interrupt enable
 * register (IER) of Core16550. The Core16550 interrupts and their identifying
 * irq_mask bit positions are as follows:
 *      •   Receive data available interrupt (RDA)      (irq_mask bit 0)
 *      •   Transmit holding register empty interrupt (THRE)    (irq_mask bit 1)
 *      •   Receiver line status interrupt (LS)         (irq_mask bit 2)
 *      •   Modem status interrupt (MS)         (irq_mask bit 3)
 * When an irq_mask bit position is set to 1, this function enables the
 * corresponding Core16550 interrupt in the IER register. When an irq_mask
 * bit position is set to 0, the corresponding interrupt’s state remains
 * unchanged in the IER register.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param irq_mask      The irq_mask parameter is used to select which of the
 *                      Core16550’s interrupts you want to enable. The allowed
 *                      value for the irq_mask parameter is one of the
 *                      following constants or a bitwise OR of more than one:
 *                      •   UART_16550_RBF_IRQ      (bit mask = 0x01)
 *                      •   UART_16550_TBE_IRQ      (bit mask = 0x02)
 *                      •   UART_16550_LS_IRQ       (bit mask = 0x04)
 *                      •   UART_16550_MS_IRQ       (bit mask = 0x08)
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   UART_16550_enable_irq( &g_uart,( UART_16550_RBF_IRQ | UART_16550_TBE_IRQ ) );
 * @endcode
 */
void
UART_16550_enable_irq
(
    uart_16550_instance_t * this_uart,
    uint8_t irq_mask
);

/***************************************************************************//**
 * The UART_16550_disable_irq() function disables the Core16550 interrupts
 * specified by the irq_mask parameter. The irq_mask parameter identifies the
 * Core16550 interrupts by bit position, as defined in the interrupt enable
 * register (IER) of Core16550. The Core16550 interrupts and their identifying
 * bit positions are as follows:
 *      •   Receive data available interrupt (RDA)              (irq_mask bit 0)
 *      •   Transmit holding register empty interrupt (THRE)    (irq_mask bit 1)
 *      •   Receiver line status interrupt (LS)                 (irq_mask bit 2)
 *      •   Modem status interrupt (MS)                         (irq_mask bit 3)
 * When an irq_mask bit position is set to 1, this function disables the
 * corresponding Core16550 interrupt in the IER register. When an irq_mask bit
 * position is set to 0, the corresponding interrupt’s state remains unchanged
 * in the IER register.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param irq_mask      The irq_mask parameter is used to select which of the
 *                      Core16550’s interrupts you want to disable. The allowed
 *                      value for the irq_mask parameter is one of the
 *                      following constants or a bitwise OR of more than one:
 *                      •   UART_16550_RBF_IRQ      (bit mask = 0x01)
 *                      •   UART_16550_TBE_IRQ      (bit mask = 0x02)
 *                      •   UART_16550_LS_IRQ       (bit mask = 0x04)
 *                      •   UART_16550_MS_IRQ       (bit mask = 0x08)
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   UART_16550_disable_irq( &g_uart, ( UART_16550_RBF_IRQ | UART_16550_TBE_IRQ ) );
 * @endcode
 */
void
UART_16550_disable_irq
(
    uart_16550_instance_t * this_uart,
    uint8_t irq_mask
);

/***************************************************************************//**
 * The UART_16550_get_modem_status() function returns the modem status of the
 * Core16550 instance. It reads the modem status register (MSR) and returns the
 * 8 bit value. The bit encoding of the returned value is exactly the same as
 * the definition of the bits in the MSR.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @return              This function returns current state of the UART's MSR
 *                      as an 8 bit unsigned integer. The driver provides the
 *                      following set of bit mask constants that should be
 *                      compared with and/or used to mask the returned value
 *                      to determine the modem status:
 *                      •   UART_16550_DCTS (bit mask = 0x01)
 *                      •   UART_16550_DDSR (bit mask = 0x02)
 *                      •   UART_16550_TERI (bit mask = 0x04)
 *                      •   UART_16550_DDCD (bit mask = 0x08)
 *                      •   UART_16550_CTS  (bit mask = 0x10)
 *                      •   UART_16550_DSR  (bit mask = 0x20)
 *                      •   UART_16550_RI   (bit mask = 0x40)
 *                      •   UART_16550_DCD  (bit mask = 0x80)
 * Example:
 * @code
 *   void uart_modem_status_isr(uart_16550_instance_t * this_uart)
 *   {
 *      uint8_t status;
 *      status = UART_16550_get_modem_status( this_uart );
 *      if( status & UART_16550_DCTS )
 *      {
 *          uart_dcts_handler();
 *      }
 *      if( status & UART_16550_CTS )
 *      {
 *          uart_cts_handler();
 *      }
 *   }
 * @endcode
 */
uint8_t
UART_16550_get_modem_status
(
    uart_16550_instance_t * this_uart
);

/***************************************************************************//**
 * The UART_16550_set_rxstatus_handler() function is used to register a receiver
 * status handler function that is called by the driver when a UART receiver
 * line status (RLS) interrupt occurs. The UART_16550_set_rxstatus_handler()
 * function also enables the RLS interrupt at the Core16550 level. You must
 * create and register the receiver status handler function to suit your
 * application.
 *
 * Note:    The driver’s top level interrupt handler function UART_16550_isr()
 * will call your receive status handler function in response to an RLS
 * interrupt from the Core16550.
 *
 * Note:    You can disable the RLS interrupt when required by calling the
 * UART_16550_disable_irq() function. This is your choice and is dependent
 * upon your application.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param handler       The handler parameter is a pointer to a receiver line
 *                      status interrupt handler function provided by your
 *                      application that will be called as a result of a
 *                      UART RLS interrupt. This handler function must be
 *                      of type uart_16550_irq_handler_t.
 * Example:
 * @code
 * #include "core_16550.h"
 *
 * #define UART_57600_BAUD 26
 *
 * uart_16550_instance_t g_uart;
 *
 * void uart_rxsts_handler( uart_16550_instance_t * this_uart )
 * {
 *      uint8_t status;
 *      status = UART_16550_get_rx_status( this_uart );
 *      if( status & UART_16550_OVERUN_ERROR )
 *      {
 *          discard_rx_data();
 *      }
 * }
 *
 * int main(void)
 * {
 *     UART_16550_init( &g_uart, UART_57600_BAUD,
 *                      UART_16550_DATA_8_BITS | UART_16550_NO_PARITY |
 *                                             UART_16550_ONE_STOP_BIT );
 *     UART_16550_set_rxstatus_handler( &g_uart, uart_rxsts_handler );
 *
 *     while ( 1 )
 *     {
 *         ;
 *     }
 *     return(0);
 * }
 * @endcode
 */
void
UART_16550_set_rxstatus_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler
);

/***************************************************************************//**
 * The UART_16550_set_tx_handler() function is used to register a transmit
 * handler function that is called by the driver when a UART transmit holding
 * register empty (THRE) interrupt occurs. The UART_16550_set_tx_handler()
 * function also enables the THRE interrupt at the Core16550 level. You must
 * create and register the transmit handler function to suit your application.
 * You can use the UART_16550_fill_tx_fifo() function in your transmit handler
 * function to write data to the transmitter.
 *
 * Note:    The driver’s top level interrupt handler function UART_16550_isr()
 * will call your transmit handler function in response to an THRE interrupt
 * from the Core16550.
 *
 * Note:    You can disable the THRE interrupt when required by calling the
 * UART_16550_disable_irq() function. This is your choice and is dependent
 * upon your application.
 *
 * Note:    The UART_16550_irq_tx() function does not use the transmit handler
 * function that you register with the UART_16550_set_tx_handler() function.
 * It uses its own internal THRE interrupt handler function that overrides any
 * custom interrupt handler that you register using the
 * UART_16550_set_tx_handler() function.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param handler       The handler parameter is a pointer to a transmitter
 *                      interrupt handler function provided by your application,
 *                      which will be called as a result of a UART THRE interrupt.
 *                      This handler is of uart_16550_irq_handler_t type.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 * #include "core_16550.h"
 *
 * #define UART_57600_BAUD 26
 *
 * uart_16550_instance_t g_uart;
 *
 * uint8_t * g_tx_buffer;
 * size_t g_tx_size = 0;
 *
 * void uart_tx_handler( uart_16550_instance_t * this_uart )
 * {
 *      size_t size_in_fifo;
 *
 *      size_in_fifo = UART_16550_fill_tx_fifo( this_uart,
 *                                              (const uint8_t *)g_tx_buffer,
 *                                              g_tx_size );
 *
 *      if(size_in_fifo == g_tx_size)
 *      {
 *         g_tx_size = 0;
 *         UART_16550_disable_irq( this_uart, UART_16550_TBE_IRQ );
 *      }
 *      else
 *      {
 *         g_tx_buffer = &g_tx_buffer[size_in_fifo];
 *         g_tx_size = g_tx_size - size_in_fifo;
 *      }
 *  }
 *
 *  int main(void)
 *  {
 *      uint8_t message[12] = "Hello world";
 *
 *      UART_16550_init( &g_uart, UART_57600_BAUD,
 *                       UART_16550_DATA_8_BITS | UART_16550_NO_PARITY |
 *                                            UART_16550_ONE_STOP_BIT );
 *
 *      g_tx_buffer = message;
 *      g_tx_size = sizeof(message);
 *
 *      UART_16550_set_tx_handler( &g_uart, uart_tx_handler);
 *
 *      while ( 1 )
 *      {
 *          ;
 *      }
 *      return(0);
 *  }
 *
 * @endcode
 */
void
UART_16550_set_tx_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler
);

/***************************************************************************//**
 * The UART_16550_set_modemstatus_handler() function is used to register a
 * modem status handler function that is called by the driver when a UART modem
 * status (MS) interrupt occurs. The UART_16550_set_modemstatus_handler()
 * function also enables the MS interrupt at the Core16550 level. You must
 * create and register the modem status handler function to suit your
 * application.
 *
 * Note:    The driver’s top level interrupt handler function UART_16550_isr()
 * will call your receive status handler function in response to an MS interrupt
 * from the Core16550.
 *
 * Note:    You can disable the MS interrupt when required by calling the
 * UART_16550_disable_irq() function. This is your choice and is dependent
 * upon your application.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param handler       The handler parameter is a pointer to a modem status
 *                      interrupt handler function provided by your application
 *                      that will be called as a result of a UART MS interrupt.
 *                      This handler function must be of type
 *                      uart_16550_irq_handler_t.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 * #include "core_16550.h"
 *
 * #define UART_57600_BAUD 26
 *
 * uart_16550_instance_t g_uart;
 *
 * void uart_modem_handler( uart_16550_instance_t * this_uart )
 * {
 *      uint8_t status;
 *      status = UART_16550_get_modem_status( this_uart );
 *      if( status & UART_16550_CTS )
 *      {
 *          uart_cts_handler();
 *      }
 * }
 *
 * int main(void)
 * {
 *     UART_16550_init( &g_uart, UART_57600_BAUD,
 *                      UART_16550_DATA_8_BITS | UART_16550_NO_PARITY |
                                              UART_16550_ONE_STOP_BIT);
 *     UART_16550_set_modemstatus_handler( &g_uart, uart_modem_handler);
 *
 *     while ( 1 )
 *     {
 *         ;
 *     }
 *     return(0);
 * }
 * @endcode
 */
void
UART_16550_set_modemstatus_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler
);

/***************************************************************************//**
 * The UART_16550_fill_tx_fifo() function fills the UART's hardware transmitter
 * FIFO with the data found in the transmitter buffer that is passed via the
 * tx_buffer function parameter. If the transmitter FIFO is not empty when the
 * function is called, the function returns immediately without transferring
 * any data to the FIFO; otherwise, the function transfers data from the
 * transmitter buffer to the FIFO until it is full or until the complete
 * contents of the transmitter buffer have been copied into the FIFO. The
 * function returns the number of bytes copied into the UART's transmitter FIFO.
 *
 * Note:    This function reads the UART’s line status register (LSR) to check
 * for the active state of the transmitter holding register empty (THRE) bit
 * before transferring data from the data buffer to the transmitter FIFO. If
 * THRE is 0, the function returns immediately, without transferring any data
 * to the FIFO. If THRE is 1, the function transfers up to 16 bytes of data to
 * the FIFO and then returns.
 *
 * Note:    The actual transmission over the serial connection will still be in
 * progress when this function returns. Use the UART_16550_get_tx_status()
 * function if you need to know when the transmitter is empty.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @param tx_buffer     The tx_buffer parameter is a pointer to a buffer
 *                      containing the data to be transmitted.
 * @param tx_size       The tx_size parameter is the size in bytes, of the data
 *                      to be transmitted.
 * @return              This function returns the number of bytes copied
 *                      into the UART's transmitter FIFO.
 *
 * Example:
 * @code
 *   void send_using_interrupt(uint8_t * pbuff, size_t tx_size)
 *   {
 *       size_t size_in_fifo;
 *       size_in_fifo = UART_16550_fill_tx_fifo( &g_uart, pbuff, tx_size );
 *   }
 * @endcode
 */
size_t
UART_16550_fill_tx_fifo
(
    uart_16550_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
);

/***************************************************************************//**
 * The UART_16550_get_tx_status() function returns the transmitter status of
 * the Core16550 instance. It reads both the UART’s line status register (LSR)
 * and returns the status of the transmit holding register empty (THRE) and
 * transmitter empty (TEMT) bits.
 *
 * @param this_uart     The this_uart parameter is a pointer to a
 *                      uart_16550_instance_t structure that holds all data
 *                      regarding this instance of the Core16550.
 * @return              This function returns the UART’s transmitter status
 *                      as an 8-bit unsigned integer. The returned value is 0
 *                      if the transmitter status bits are not set or the
 *                      function execution failed. The driver provides a set
 *                      of bit mask constants that should be compared with
 *                      and/or used to mask the returned value to determine
 *                      the transmitter status.
 *                      When the return value is compared to the following
 *                      bitmasks, a non-zero result indicates that the
 *                      corresponding transmitter status bit is set:
 *                      •   UART_16550_THRE     (bit mask = 0x20)
 *                      •   UART_16550_TEMT     (bit mask = 0x40)
 *                      When the return value is compared to the following
 *                      bit mask, a non-zero result indicates that the
 *                      transmitter is busy or the function execution failed.
 *                      •   UART_16550_TX_BUSY      (bit mask = 0x00)
 * Example:
 * @code
 *   uint8_t tx_buff[10] = "abcdefghi";
 *
 *   UART_16550_polled_tx( &g_uart, tx_buff, sizeof(tx_buff));
 *
 *   while ( ! (UART_16550_TEMT & UART_16550_get_tx_status( &g_uart ) )  )
 *   {
 *      ;
 *   }
 * @endcode
 */
uint8_t
UART_16550_get_tx_status
(
    uart_16550_instance_t * this_uart
);

#ifdef __cplusplus
}
#endif

#endif /* __CORE_16550_H */
