/*******************************************************************************
 * (c) Copyright 2007-2017 Microsemi SoC Products Group. All rights reserved.
 * 
 * This file contains the application programming interface for the CoreUARTapb
 * bare metal driver.
 * 
 * SVN $Revision: 9082 $
 * SVN $Date: 2017-04-28 11:51:36 +0530 (Fri, 28 Apr 2017) $
 */
/*=========================================================================*//**
  @mainpage CoreUARTapb Bare Metal Driver.

  @section intro_sec Introduction
  CoreUARTapb is an implementation of the Universal Asynchronous 
  Receiver/Transmitter aimed at a minimal FPGA tile usage within an Microsemi
  FPGA. The CoreUARTapb bare metal software driver is designed for use in 
  systems with no operating system.

  The CoreUARTapb driver provides functions for basic polled transmitting and 
  receiving operations. It also provides functions allowing use of the 
  CoreUARTapb in interrupt-driven mode, but leaves the management of interrupts 
  to the calling application, as interrupt enabling and disabling cannot be 
  controlled through the CoreUARTapb registers. The CoreUARTapb driver is 
  provided as C source code.

  @section driver_configuration Driver Configuration
  Your application software should configure the CoreUARTapb driver, through 
  calls to the UART_init() function for each CoreUARTapb instance in the 
  hardware design. The configuration parameters include the CoreUARTapb 
  hardware instance base address and other runtime parameters, such as baud 
  rate, bit width, and parity. No CoreUARTapb hardware configuration parameters 
  are needed by the driver, apart from the CoreUARTapb hardware instance base 
  address. Hence, no additional configuration files are required to use the driver.

  A CoreUARTapb hardware instance can be generated with fixed baud value, 
  character size and parity configuration settings as part of the hardware flow. 
  The baud_value and line_config parameter values passed to the UART_init() 
  function will not have any effect if fixed values were selected for the 
  baud value, character size and parity in the hardware configuration of 
  CoreUARTapb. When fixed values are selected for these hardware configuration 
  parameters, the driver cannot overwrite the fixed values in the CoreUARTapb 
  control registers, CTRL1 and CTRL2.

  @section theory_op Theory of Operation
  The CoreUARTapb software driver is designed to allow the control of multiple 
  instances of CoreUARTapb. Each instance of CoreUARTapb in the hardware design 
  is associated with a single instance of the UART_instance_t structure in the 
  software. You need to allocate memory for one unique UART_instance_t  
  structure instance for each CoreUARTapb hardware instance. The contents of 
  these data structures are initialized during calls to function UART_init(). 
  A pointer to the structure is passed to subsequent driver functions in order
  to identify the CoreUARTapb hardware instance you wish to perform the 
  requested operation on.
  
  Note: Do not attempt to directly manipulate the content of UART_instance_t 
  structures. This structure is only intended to be modified by the driver 
  function.

  The driver can be used to transmit and receive data once initialized. 
  Transmit can be performed using the UART_send() function. This function
  is blocking, meaning that it will only return once the data passed to 
  the function has been sent to the CoreUARTapb hardware. Data received 
  by the CoreUARTapb hardware can be read by the user application using 
  the UART_get_rx() function.

  The function UART_fill_tx_fifo() is also provided to be used as part of 
  interrupt-driven transmit. This function fills the CoreUARTapb hardware 
  transmit FIFO with the content of a data buffer passed as a parameter before 
  returning. The control of the interrupts must be implemented outside the 
  driver as the CoreUARTapb hardware does not provide the ability to enable 
  or disable its interrupt sources.

  The function UART_polled_tx_string() is provided to transmit a NULL 
  terminated string in polled mode. This function is blocking, meaning that it 
  will only return once the data passed to the function has been sent to the 
  CoreUARTapb hardware.

  The function UART_get_rx_status() returns the error status of the CoreUARTapb
  receiver. This can be used by applications to take appropriate action in case
  of receiver errors.
*//*=========================================================================*/
#ifndef __CORE_UART_APB_H
#define __CORE_UART_APB_H 1

#include "cpu_types.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * Data bits length defines:
 */
#define DATA_7_BITS     0x00u
#define DATA_8_BITS     0x01u

/***************************************************************************//**
 * Parity defines:
 */
#define NO_PARITY       0x00u
#define EVEN_PARITY     0x02u
#define ODD_PARITY      0x06u

/***************************************************************************//**
 * Error Status definitions:
 */
#define UART_APB_PARITY_ERROR    0x01u
#define UART_APB_OVERFLOW_ERROR  0x02u
#define UART_APB_FRAMING_ERROR   0x04u
#define UART_APB_NO_ERROR        0x00u
#define UART_APB_INVALID_PARAM   0xFFu

/***************************************************************************//**
 * UART_instance_t
 * 
 * There should be one instance of this structure for each instance of CoreUARTapb
 * in your system. This structure instance is used to identify the various UARTs
 * in a system and should be passed as first parameter to UART functions to 
 * identify which UART should perform the requested operation. The 'status' 
 * element in the structure is used to provide sticky status information. 
 */
typedef struct
{
    addr_t      base_address;
    uint8_t     status;
} UART_instance_t;

/***************************************************************************//**
 * The function UART_init() initializes the UART with the configuration passed 
 * as parameters. The configuration parameters are the baud_value used to 
 * generate the baud rate and the line configuration (bit length and parity).
 *
 * @param this_uart   The this_uart parameter is a pointer to a UART_instance_t
 *                    structure which holds all data regarding this instance of
 *                    the CoreUARTapb. This pointer will be used to identify 
 *                    the target CoreUARTapb hardware instance in subsequent 
 *                    calls to the CoreUARTapb functions.
 * @param base_addr   The base_address parameter is the base address in the 
 *                    processor's memory map for the registers of the 
 *                    CoreUARTapb instance being initialized.
 * @param baud_value  The baud_value parameter is used to select the baud rate 
 *                    for the UART. The baud value is calculated from the 
 *                    frequency of the system clock in hertz and the desired 
 *                    baud rate using the following equation: 
 *                    
 *                    baud_value = (clock /(baud_rate * 16)) - 1.
 * 
 *                    The baud_value parameter must be a value in the range 0 
 *                    to 8191 (or 0x0000 to 0x1FFF).
 * @param line_config This parameter is the line configuration specifying the 
 *                    bit length and parity settings. This is a logical OR of:
 *                      - DATA_7_BITS
 *                    - DATA_8_BITS
 *                    - NO_PARITY
 *                    - EVEN_PARITY
 *                    - ODD_PARITY
 *                    For example, 8 bits even parity would be specified as 
 *                    (DATA_8_BITS | EVEN_PARITY). 
 * @return            This function does not return a value.
 * Example:
 * @code
 *   #define BAUD_VALUE_57600    25
 *   
 *   #define COREUARTAPB0_BASE_ADDR      0xC3000000UL
 *   
 *   UART_instance_t g_uart;
 *   int main()
 *   {
 *      UART_init(&g_uart, COREUARTAPB0_BASE_ADDR, 
                  BAUD_VALUE_57600, (DATA_8_BITS | EVEN_PARITY));
 *   }
 * @endcode
 */
void
UART_init
(
    UART_instance_t * this_uart,
    addr_t base_addr,
    uint16_t baud_value,
    uint8_t line_config
);

/***************************************************************************//**
 * The function UART_send() is used to transmit data. It transfers the contents
 * of the transmitter data buffer, passed as a function parameter, into the 
 * UART's hardware transmitter FIFO. It returns when the full content of the 
 * transmitter data buffer has been transferred to the UART's transmitter FIFO. 
 *
 * Note: you cannot assume that the data you are sending using this function has
 * been received at the other end by the time this function returns. The actual
 * transmit over the serial connection will still be taking place at the time of
 * the function return. It is safe to release or reuse the memory used as the
 * transmit buffer once this function returns.
 *
 * @param this_uart     The this_uart parameter is a pointer to a 
 *                      UART_instance_t structure which holds all data regarding 
 *                      this instance of the CoreUARTapbUART.
 * @param tx_buffer     The tx_buffer parameter is a pointer to a buffer 
 *                      containing the data to be transmitted.
 * @param tx_size       The tx_size parameter is the size, in bytes, of 
 *                      the data to be transmitted.
 *
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   uint8_t testmsg1[] = {"\n\r\n\r\n\rUART_send() test message 1"};
 *   UART_send(&g_uart,(const uint8_t *)&testmsg1,sizeof(testmsg1));
 * @endcode
 */
void
UART_send
(
    UART_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
);

/***************************************************************************//**
 * The function UART_fill_tx_fifo() fills the UART's transmitter hardware FIFO 
 * with the data found in the transmitter buffer that is passed in as a 
 * function parameter. The function returns either when the FIFO is full or 
 * when the complete contents of the transmitter buffer have been copied into 
 * the FIFO. It returns the number of bytes copied into the UART's transmitter
 * hardware FIFO. This function is intended to be used as part of 
 * interrupt-driven transmission.
 *
 * Note:    You cannot assume that the data you transmit using this function has 
 *          been received at the other end by the time this function returns. 
 *          The actual transmission over the serial connection will still be 
 *          taking place at the time of the function return. 
 *
 * @param this_uart     The this_uart parameter is a pointer to a UART_instance_t
 *                      structure which holds all data regarding this instance of
 *                      the UART.
 * @param tx_buffer     The tx_buffer parameter is a pointer to a buffer 
 *                      containing the data to be transmitted.
 * @param tx_size       The tx_size parameter is the size in bytes, of the data 
 *                      to be transmitted.
 * @return              This function returns the number of bytes copied 
 *                      into the UART's transmitter hardware FIFO. 
 *
 * Example:
 * @code
 *   void send_using_interrupt
 *   (
 *       uint8_t * pbuff,
 *       size_t tx_size
 *   )
 *   {
 *       size_t size_in_fifo;
 *       size_in_fifo = UART_fill_tx_fifo( &g_uart, pbuff, tx_size );
 *   }
 * @endcode
 */
size_t
UART_fill_tx_fifo
(
    UART_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
);

/***************************************************************************//**
 * The function UART_get_rx() reads the content of the UART's receiver hardware 
 * FIFO and stores it in the receiver buffer that is passed in as a function 
 * parameter. It copies either the full contents of the FIFO into the receiver 
 * buffer, or just enough data from the FIFO to fill the receiver buffer, 
 * dependent upon the size of the receiver buffer.  The size of the receiver 
 * buffer is passed in as a function parameter. UART_get_rx() returns the number
 * of bytes copied into the receiver buffer. If no data was received at the time
 * the function is called, the function returns 0.
 *
 * Note:    This function reads and accumulates the receiver status of the 
 *          CoreUARTapb instance before reading each byte from the receiver's 
 *          data register/FIFO. This allows the driver to maintain a sticky 
 *          record of any receiver errors that occur as the UART receives each 
 *          data byte; receiver errors would otherwise be lost after each read 
 *          from the receiver's data register. A call to the UART_get_rx_status()
 *          function returns any receiver errors accumulated during the execution
 *          of the UART_get_rx() function.
 * Note:    When FIFO mode is disabled in the CoreUARTapb hardware configuration,
 *          the driver accumulates a sticky record of any parity errors, framing 
 *          errors or overflow errors. When FIFO mode is enabled, the driver 
 *          accumulates a sticky record of overflow errors only; in this case 
 *          interrupts must be used to handle parity errors or framing errors.
 *
 * @param this_uart     The this_uart parameter is a pointer to a UART_instance_t 
 *                      structure which holds all data regarding this instance of 
 *                      the UART.
 * @param rx_buffer     The rx_buffer parameter is a pointer to a buffer where the 
 *                      received data will be copied.
 * @param buff_size     The buff_size parameter is the size of the receive buffer 
 *                      in bytes.
 * @return              This function returns the number of bytes copied into the 
 *                      receive buffer.
 *
 * Example:
 * @code
 *   #define MAX_RX_DATA_SIZE    256
 *   
 *   uint8_t rx_data[MAX_RX_DATA_SIZE];
 *   uint8_t rx_size = 0;
 *           
 *   rx_size = UART_get_rx( &g_uart, rx_data, sizeof(rx_data) );
 * @endcode
 */
size_t
UART_get_rx
(
    UART_instance_t * this_uart,
    uint8_t * rx_buffer,
    size_t buff_size
);

/***************************************************************************//**
 * The function UART_polled_tx_string() is used to transmit a NULL ('\0') 
 * terminated string. Internally, it polls for the transmit ready status and
 * transfers the text starting at the address pointed to by p_sz_string into
 * the UART's hardware transmitter FIFO. It is a blocking function and returns
 * only when the complete string has been transferred to the UART's transmit 
 * FIFO.
 *
 * Note:    You cannot assume that the data you transmit using this function 
 *          has been received at the other end by the time this function 
 *          returns. The actual transmission over the serial connection will
 *          still be taking place at the time of the function return.
 *
 * @param this_uart     The this_uart parameter is a pointer to a 
 *                      UART_instance_t structure which holds
 *                      all data regarding this instance of the UART.
 * @param p_sz_string   The p_sz_string parameter is a pointer to a buffer
 *                      containing the NULL ('\0') terminated string to be 
 *                      transmitted.
 * @return              This function does not return a value.
 *
 * Example:
 * @code
 *   uint8_t testmsg1[] = {"\r\n\r\nUART_polled_tx_string() test message 1\0"};
 *   UART_polled_tx_string(&g_uart,(const uint8_t *)&testmsg1);
 * @endcode
 */
void 
UART_polled_tx_string
( 
    UART_instance_t * this_uart, 
    const uint8_t * p_sz_string
);

/***************************************************************************//**
 * The UART_get_rx_status() function returns the receiver error status of the 
 * CoreUARTapb instance. It reads both the current error status of the receiver
 * and the accumulated error status from preceding calls to the UART_get_rx() 
 * function and combines them using a bitwise OR. It returns the cumulative 
 * parity, framing and overflow error status of the receiver, since the 
 * previous call to UART_get_rx_status(), as an 8-bit encoded value.
 *
 * Note:    The UART_get_rx() function reads and accumulates the receiver status 
 *          of the CoreUARTapb instance before reading each byte from the 
 *          receiver's data register/FIFO. The driver maintains a sticky record 
 *          of the cumulative error status, which persists after the 
 *          UART_get_rx() function returns. The UART_get_rx_status() function 
 *          clears this accumulated record of receiver errors before returning.
 * 
 * @param this_uart     The this_uart parameter is a pointer to a UART_instance_t
 *                      structure which holds all data regarding this instance 
 *                      of the UART.
 * @return              This function returns the UART receiver error status as 
 *                      an 8-bit encoded value. The returned value is 0 if no 
 *                      receiver errors occurred. The driver provides a set of 
 *                      bit mask constants which should be compared with and/or
 *                      used to mask the returned value to determine the 
 *                      receiver error status. 
 *                      When the return value is compared to the following bit 
 *                      masks, a non-zero result indicates that the 
 *                      corresponding error occurred:
 *                      UART_APB_PARITY_ERROR    (bit mask = 0x01)
 *                      UART_APB_OVERFLOW_ERROR  (bit mask = 0x02)
 *                      UART_APB_FRAMING_ERROR   (bit mask = 0x04)
 *                      When the return value is compared to the following bit 
 *                      mask, a non-zero result indicates that no error occurred:
 *                      UART_APB_NO_ERROR        (0x00)
 *
 * Example:
 * @code
 *   UART_instance_t g_uart;
 *   uint8_t rx_data[MAX_RX_DATA_SIZE];
 *   uint8_t err_status;
 *   err_status = UART_get_err_status(&g_uart);
 *   
 *   if(UART_APB_NO_ERROR == err_status )
 *   {
 *        rx_size = UART_get_rx( &g_uart, rx_data, MAX_RX_DATA_SIZE );
 *   }
 * @endcode
 */
uint8_t
UART_get_rx_status
(
    UART_instance_t * this_uart
);

#ifdef __cplusplus
}
#endif

#endif /* __CORE_UART_APB_H */
