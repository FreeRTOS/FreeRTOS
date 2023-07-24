/*******************************************************************************
 * Copyright (c) 2020 Thales.
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 *
 *
 */
// Additional contributions by:
//         Sebastien Jacq - sjthales on github.com
//         Anjali Gedam - anjaliigedam on github.com
//
// Description: Driver header for UART Ip of the CVA6 platform
//
// =========================================================================== //
// Revisions  :
// Date        Version  Author       Description
// 2020-10-06  0.1      S.Jacq       modification of the Test for CVA6 softcore
// 2021-07-12  0.2      Anjali G     modification for the CVA6 FPGA
// =========================================================================== //

#ifndef __UART1_H_
#define __UART1_H_ 1

#include <stddef.h>
#include <stdint.h>


/***************************************************************************//**
  Baud rates
  ==========
  The following definitions are used to specify standard baud rates as a
  parameter to the UART_init() function.
  
  | Constant             | Description      |
  |----------------------|------------------|
  | UART_110_BAUD    |    110 baud rate |
  | UART_300_BAUD    |    300 baud rate |
  | UART_600_BAUD    |    600 baud rate |
  | UART_1200_BAUD   |   1200 baud rate |
  | UART_2400_BAUD   |   2400 baud rate |
  | UART_4800_BAUD   |   4800 baud rate |
  | UART_9600_BAUD   |   9600 baud rate |
  | UART_19200_BAUD  |  19200 baud rate |
  | UART_38400_BAUD  |  38400 baud rate |
  | UART_57600_BAUD  |  57600 baud rate |
  | UART_115200_BAUD | 115200 baud rate |
  | UART_230400_BAUD | 230400 baud rate |
  | UART_460800_BAUD | 460800 baud rate |
  | UART_921600_BAUD | 921600 baud rate |
  
 */
#define UART_110_BAUD       110U
#define UART_300_BAUD       300U
#define UART_600_BAUD       600U
#define UART_1200_BAUD      1200U
#define UART_2400_BAUD      2400U
#define UART_4800_BAUD      4800U
#define UART_9600_BAUD      9600U
#define UART_19200_BAUD     19200U
#define UART_38400_BAUD     38400U
#define UART_57600_BAUD     57600U
#define UART_115200_BAUD    115200U
#define UART_230400_BAUD    230400U
#define UART_460800_BAUD    460800U
#define UART_921600_BAUD    921600U

/***************************************************************************//**
  Data Bits Length
  ================
  The following defines are used to build the value of the UART_init()
  function line_config parameter.
  
  | Constant             | Description                |
  |----------------------|----------------------------|
  | UART_DATA_5_BITS | 5 bits of data transmitted |
  | UART_DATA_6_BITS | 6 bits of data transmitted |
  | UART_DATA_7_BITS | 7 bits of data transmitted |
  | UART_DATA_8_BITS | 8 bits of data transmitted |
  
 */
#define UART_DATA_5_BITS     ((uint8_t) 0x00)
#define UART_DATA_6_BITS     ((uint8_t) 0x01)
#define UART_DATA_7_BITS     ((uint8_t) 0x02)
#define UART_DATA_8_BITS     ((uint8_t) 0x03)

/***************************************************************************//**
  Parity
  ======
  The following defines are used to build the value of the UART_init()
  function line_config parameter.
  
  | Constant                | Description              |
  |-------------------------|--------------------------|
  | UART_NO_PARITY      | No parity                |
  | UART_ODD_PARITY     | Odd Parity               |
  | UART_EVEN_PARITY    | Even parity              |
  | UART_STICK_PARITY_0 | Stick parity bit to zero |
  | UART_STICK_PARITY_1 | Stick parity bit to one  |
 */
#define UART_NO_PARITY           ((uint8_t) 0x00)
#define UART_ODD_PARITY          ((uint8_t) 0x08)
#define UART_EVEN_PARITY         ((uint8_t) 0x18)
#define UART_STICK_PARITY_0      ((uint8_t) 0x38)
#define UART_STICK_PARITY_1      ((uint8_t) 0x28)

/***************************************************************************//**
  Number of Stop Bits
  ===================
  The following defines are used to build the value of the UART_init()
  function line_config parameter.
  
  | Constant                  | Description              |
  |---------------------------|--------------------------|
  | UART_ONE_STOP_BIT     | One stop bit             |
  | UART_ONEHALF_STOP_BIT | One and a half stop bits |
  | UART_TWO_STOP_BITS    | Two stop bits            |
  
 */
#define UART_ONE_STOP_BIT        ((uint8_t) 0x00)
#define UART_ONEHALF_STOP_BIT    ((uint8_t) 0x04)
#define UART_TWO_STOP_BITS       ((uint8_t) 0x04)

/***************************************************************************//**
  Receiver Error Status
  =====================
  The following defines are used to determine the UART receiver error type.
  These bit mask constants are used with the return value of the
  UART_get_rx_status() function to find out if any errors occurred while
  receiving data.
  
  
  | Constant               | Description                                |
  |------------------------|--------------------------------------------|
  | UART_NO_ERROR      | No error bit mask (0x00)                   |
  | UART_OVERUN_ERROR  | Overrun error bit mask (0x02)              |
  | UART_PARITY_ERROR  | Parity error bit mask (0x04)               |
  | UART_FRAMING_ERROR | Framing error bit mask (0x08)              |
  | UART_BREAK_ERROR   | Break error bit mask (0x10)                |
  | UART_FIFO_ERROR    | FIFO error bit mask (0x80)                 |
  | UART_INVALID_PARAM | Invalid function parameter bit mask (0xFF) |
 */
#define UART_INVALID_PARAM    ((uint8_t)0xFF)
#define UART_NO_ERROR         ((uint8_t)0x00 )
#define UART_OVERUN_ERROR     ((uint8_t)0x02)
#define UART_PARITY_ERROR     ((uint8_t)0x04)
#define UART_FRAMING_ERROR    ((uint8_t)0x08)
#define UART_BREAK_ERROR      ((uint8_t)0x10)
#define UART_FIFO_ERROR       ((uint8_t)0x80)


/*******************************************************************************
 * Receiver error status mask.
 */
#define STATUS_ERROR_MASK    ( UART_OVERUN_ERROR   | UART_PARITY_ERROR | \
                               UART_FRAMING_ERROR  | UART_BREAK_ERROR  | \
                               UART_FIFO_ERROR)

/***************************************************************************//**
  Transmitter Status
  ==================
  The following definitions are used to determine the UART transmitter status.
  These bit mask constants are used with the return value of the
  UART_get_tx_status() function to find out the status of the transmitter.
    
  | Constant         | Description                                        |
  |------------------|----------------------------------------------------|
  | UART_TX_BUSY | Transmitter busy (0x00)                            |
  | UART_THRE    | Transmitter holding register empty bit mask (0x20) |
  | UART_TEMT    | Transmitter empty bit mask (0x40)                  |
  
 */
#define UART_TX_BUSY          ((uint8_t) 0x00)
#define UART_THRE             ((uint8_t) 0x20)
#define UART_TEMT             ((uint8_t) 0x40)

/***************************************************************************//**
  Modem Status
  ============
  The following defines are used to determine the modem status. These bit
  mask constants are used with the return value of the
  UART_get_modem_status() function to find out the modem status of
  the UART.
  
  | Constant      | Description                                     |
  |---------------|-------------------------------------------------|
  | UART_DCTS | Delta clear to send bit mask (0x01)             |
  | UART_DDSR | Delta data set ready bit mask (0x02)            |
  | UART_TERI | Trailing edge of ring indicator bit mask (0x04) |
  | UART_DDCD | Delta data carrier detect bit mask (0x08)       |
  | UART_CTS  | Clear to send bit mask (0x10)                   |
  | UART_DSR  | Data set ready bit mask (0x20)                  |
  | UART_RI   | Ring indicator bit mask (0x40)                  |
  | UART_DCD  | Data carrier detect bit mask (0x80)             |
 */
#define UART_DCTS             ((uint8_t) 0x01)
#define UART_DDSR             ((uint8_t) 0x02)
#define UART_TERI             ((uint8_t) 0x04)
#define UART_DDCD             ((uint8_t) 0x08)
#define UART_CTS              ((uint8_t) 0x10)
#define UART_DSR              ((uint8_t) 0x20)
#define UART_RI               ((uint8_t) 0x40)
#define UART_DCD              ((uint8_t) 0x80)

/***************************************************************************//**
  This typedef specifies the irq_mask parameter for the UART_enable_irq()
  and UART_disable_irq() functions. The driver defines a set of bit masks
  that are used to build the value of the irq_mask parameter. A bitwise OR of
  these bit masks is used to enable or disable multipleUART interrupts.
 */
typedef uint16_t uart_irq_t;

/***************************************************************************//**
  UART Interrupts
  =====================
  The following defines specify the interrupt masks to enable and disable
  UART interrupts. They are used to build the value of the irq_mask parameter
  for the UART_enable_irq() and UART_disable_irq() functions. A bitwise
  OR of these constants is used to enable or disable multiple interrupts.
  
  
  | Constant           | Description                                                   |
  |--------------------|---------------------------------------------------------------|
  | UART_RBF_IRQ   | Receive Data Available Interrupt bit mask (0x001)             |
  | UART_TBE_IRQ   | Transmitter Holding Register Empty interrupt bit mask (0x002) |
  | UART_LS_IRQ    | Receiver Line Status interrupt bit mask (0x004)               |
  | UART_MS_IRQ    | Modem Status interrupt bit mask (0x008)                       |

 */
#define UART_RBF_IRQ        0x001
#define UART_TBE_IRQ        0x002
#define UART_LS_IRQ         0x004
#define UART_MS_IRQ         0x008
//#define UART_RTO_IRQ        0x010
//#define UART_NACK_IRQ       0x020
//#define UART_PIDPE_IRQ      0x040
//#define UART_LINB_IRQ       0x080
//#define UART_LINS_IRQ       0x100
#define UART_INVALID_IRQ    UINT16_MAX

/***************************************************************************//**
  This enumeration specifies the receiver FIFO trigger level. This is the number
  of bytes that must be received before the UART generates a receive data
  available interrupt. It provides the allowed values for the
  UART_set_rx_handler() function trigger_level parameter.
 */
typedef enum {
    UART_FIFO_SINGLE_BYTE    = 0x00,
    UART_FIFO_FOUR_BYTES     = 0x40,
    UART_FIFO_EIGHT_BYTES    = 0x80,
    UART_FIFO_FOURTEEN_BYTES = 0xC0,
    UART_FIFO_INVALID_TRIG_LEVEL

} uart_rx_trig_level_t;




/***************************************************************************//**
  UART instance type.
  This is type definition for UART instance. You need to create and
  maintain a record of this type. This holds all data regarding the UART
  instance
 */
typedef struct  uart_instance uart_instance_t;

/***************************************************************************//**
  Interrupt handler prototype.
  This typedef specifies the function prototype for UART interrupt handlers.
  All interrupt handlers registered with the UART driver must be of this type.
  The interrupt handlers are registered with the driver through the
  UART_set_rx_handler(), UART_set_tx_handler(),
  UART_set_rxstatus_handler(), and UART_set_modemstatus_handler()
  functions.
  The this_uart parameter is a pointer to either g_uart0 or g_uart1 to
  identify the UART to associate with the handler function.
 */
typedef void (*uart_irq_handler_t)( uart_instance_t * this_uart );


/*******************************************************************************
 Register Bit definitions
 */

/* Line Control register bit definitions */
#define SB                          6u                  /* Set break */
#define DLAB                        7u                  /* Divisor latch access bit */

/* Line Control register bit masks */
#define SB_MASK                     (0x01u << SB)        /* Set break */
#define DLAB_MASK                   (0x01u << DLAB)      /* Divisor latch access bit */

/* FIFO Control register bit definitions */
#define ENABLE_FIFO                 0u                  /* Enable FIFO */
#define CLEAR_RX_FIFO               1u                  /* Clear receiver FIFO */
#define CLEAR_TX_FIFO               2u                  /* Clear transmitter FIFO */
#define DMA_MODE                    3u                  /* DMA mode */
#define FIFO64_ENABLE               5u                  /* FIFO64 enable */
#define RDYMODE                     3u                  /* Mode 0 or Mode 1 for TXRDY and RXRDY */
#define FIFO_RX_TRIGGER             6u                  /* FIFO RX trigger */

/* FIFO Control register bit MASKS */
#define RXRDY_TXRDYN_EN_MASK           (0x01u << 0u)      /* Enable TXRDY and RXRDY signals */
#define CLEAR_RX_FIFO_MASK             (0x01u << 1u)      /* Clear receiver FIFO */
#define CLEAR_TX_FIFO_MASK             (0x01u << 2u)      /* Clear transmitter FIFO */
#define DMA_MODE_MASK                  (0x01u << 3u)      /* DMA mode */
#define FIFO64_ENABLE_MASK             (0x01u << 5u)      /* FIFO64 enable */
#define RDYMODE_MASK                 (0x01u << 3u)      /* Mode 0 or Mode 1 for TXRDY and RXRDY */

#define FIFO_RX_TRIGGER_LEVEL_4_MASK   (0x01u << 6u)
#define FIFO_RX_TRIGGER_LEVEL_8_MASK   (0x02u << 6u)
#define FIFO_RX_TRIGGER_LEVEL_14_MASK   (0x03u << 6u)

#define FIFO64_RX_TRIGGER_LEVEL_16_MASK   (0x01u << 6u)
#define FIFO64_RX_TRIGGER_LEVEL_32_MASK   (0x02u << 6u)
#define FIFO64_RX_TRIGGER_LEVEL_56_MASK   (0x03u << 6u)

/* Modem Control register bit definitions */
//#define LOOP                        4u                  /* Local loopback */
//#define RLOOP                       5u                  /* Remote loopback */
//#define ECHO                        6u                  /* Automatic echo */

/* Modem Control register bit MASKS */
//#define LOOP_MASK                   (0x01u << 4u)        /* Local loopback */
//#define RLOOP_MASK                  (0x01u << 5u)        /* Remote loopback & Automatic echo*/
//#define ECHO_MASK                   (0x01u << 6u)        /* Automatic echo */

/* Line Status register bit definitions   */
#define DR                          0u                  /* Data ready */
#define THRE                        5u                  /* Transmitter holding register empty */
#define TEMT                        6u                  /* Transmitter empty */

/* Line Status register bit MASKS   */
#define DR_MASK                     (0x01u << 0u)        /* Data ready */
#define THRE_MASK                   (0x01u << 5u)        /* Transmitter holding register empty */
#define TEMT_MASK                   (0x01u << 6u)        /* Transmitter empty */

/* Interrupt Enable register bit definitions */
#define ERBFI                       0u                  /* Enable receiver buffer full interrupt */
#define ETBEI                       1u                  /* Enable transmitter buffer empty interrupt */
#define ELSI                        2u                  /* Enable line status interrupt */
#define EDSSI                       3u                  /* Enable modem status interrupt */

/* Interrupt Enable register bit MASKS */
#define ERBFI_MASK                  (0x01u << 0u)      /* Enable receiver buffer full interrupt */
#define ETBEI_MASK                  (0x01u << 1u)      /* Enable transmitter buffer empty interrupt */
#define ELSI_MASK                   (0x01u << 2u)      /* Enable line status interrupt */
#define EDSSI_MASK                  (0x01u << 3u)      /* Enable modem status interrupt */

/* Multimode register 0 bit definitions */
#define ELIN                        3u                  /* Enable LIN header detection */
#define ETTG                        5u                  /* Enable transmitter time guard */
#define ERTO                        6u                  /* Enable receiver time-out */
#define EFBR                        7u                  /* Enable fractional baud rate mode */

/* Multimode register 0 bit MASKS */
#define ELIN_MASK                   (0x01u << 3u)      /* Enable LIN header detection */
#define ETTG_MASK                   (0x01u << 5u)      /* Enable transmitter time guard */
#define ERTO_MASK                   (0x01u << 6u)      /* Enable receiver time-out */
#define EFBR_MASK                   (0x01u << 7u)      /* Enable fractional baud rate mode */

/* Multimode register 1 bit definitions */
#define E_MSB_RX                    0u                  /* MSB / LSB first for receiver */
#define E_MSB_TX                    1u                  /* MSB / LSB first for transmitter */
#define EIRD                        2u                  /* Enable IrDA modem */
#define EIRX                        3u                  /* Input polarity for IrDA modem */
#define EITX                        4u                  /* Output polarity for IrDA modem */
#define EITP                        5u                  /* Output pulse width for IrDA modem */

/* Multimode register 1 bit MASKS */
#define E_MSB_RX_MASK               (0x01u << 0u)      /* MSB / LSB first for receiver */
#define E_MSB_TX_MASK               (0x01u << 1u)      /* MSB / LSB first for transmitter */
#define EIRD_MASK                   (0x01u << 2u)      /* Enable IrDA modem */
#define EIRX_MASK                   (0x01u << 3u)      /* Input polarity for IrDA modem */
#define EITX_MASK                   (0x01u << 4u)      /* Output polarity for IrDA modem */
#define EITP_MASK                   (0x01u << 5u)      /* Output pulse width for IrDA modem */

/* Multimode register 2 bit definitions */
//#define EERR                        0u                  /* Enable ERR / NACK during stop time */
//#define EAFM                        1u                  /* Enable 9-bit address flag mode */
//#define EAFC                        2u                  /* Enable address flag clear */
//#define ESWM                        3u                  /* Enable single wire half-duplex mode */

/* Multimode register 2 bit MASKS */
//#define EERR_MASK                   (0x01u << 0u)      /* Enable ERR / NACK during stop time */
//#define EAFM_MASK                   (0x01u << 1u)      /* Enable 9-bit address flag mode */
//#define EAFC_MASK                   (0x01u << 2u)      /* Enable address flag clear */
//#define ESWM_MASK                   (0x01u << 3u)      /* Enable single wire half-duplex mode */

/* Multimode Interrupt Enable register and
   Multimode Interrupt Identification register definitions */
//#define ERTOI                       0u                  /* Enable receiver timeout interrupt */
//#define ENACKI                      1u                  /* Enable NACK / ERR interrupt */
//#define EPID_PEI                    2u                  /* Enable PID parity error interrupt */
//#define ELINBI                      3u                  /* Enable LIN break interrupt */
//#define ELINSI                      4u                  /* Enable LIN sync detection interrupt */

/* Multimode Interrupt Enable register and
   Multimode Interrupt Identification register MASKS */
//#define ERTOI_MASK                  (0x01u << 0u)      /* Enable receiver timeout interrupt */
//#define ENACKI_MASK                 (0x01u << 1u)      /* Enable NACK / ERR interrupt */
//#define EPID_PEI_MASK               (0x01u << 2u)      /* Enable PID parity error interrupt */
//#define ELINBI_MASK                 (0x01u << 3u)      /* Enable LIN break interrupt */
//#define ELINSI_MASK                 (0x01u << 4u)      /* Enable LIN sync detection interrupt */

typedef struct
{
    union
    {
        volatile const  uint8_t    RBR;
        volatile uint8_t    THR;
        volatile uint8_t    DLL;
             uint32_t   RESERVED0;
    };

    union
    {
        volatile uint8_t  DLM;
        volatile uint8_t  IER;
             uint32_t RESERVED1;
    };

    union
    {
        volatile uint8_t  IIR;
        volatile uint8_t  FCR;
             uint32_t RESERVED2;
    };

    volatile uint8_t  LCR;
         uint8_t  RESERVED3[3];

    volatile uint8_t  MCR;
         uint8_t  RESERVED4[3];

    volatile const  uint8_t  LSR;
         uint8_t  RESERVED5[3];

    volatile const  uint8_t  MSR;
         uint8_t  RESERVED6[3];

    volatile uint8_t  SR;
         uint8_t  RESERVED7[7];

} UART_TypeDef;


/***************************************************************************//**
  uart_instance.
  There is one instance of this structure for each instance of the
  microprocessor subsystem's UARTs. Instances of this structure are used to
  identify a specific UART. A pointer to an initialized instance of the
  uart_instance_t structure is passed as the first parameter to
  UART driver functions to identify which UART should perform the
  requested operation.
 */
struct uart_instance{
    /* CMSIS related defines identifying the UART hardware. */
    UART_TypeDef *      hw_reg;     /*!< Pointer to UART registers. */
    uint32_t            baudrate;   /*!< Operating baud rate. */
    uint8_t             lineconfig; /*!< Line configuration parameters. */
    uint8_t             status;     /*!< Sticky line status. */

    /* transmit related info (used with interrupt driven transmit): */
    const uint8_t * tx_buffer;          /*!< Pointer to transmit buffer. */
    uint32_t        tx_buff_size;       /*!< Transmit buffer size. */
    uint32_t        tx_idx;             /*!< Index within transmit buffer of next byte to transmit.*/

    /* line status interrupt handler:*/
    uart_irq_handler_t linests_handler;   /*!< Pointer to user registered line status handler. */
    /* receive interrupt handler:*/
    uart_irq_handler_t rx_handler;        /*!< Pointer to user registered receiver handler. */
    /* transmit interrupt handler:*/
    uart_irq_handler_t tx_handler;        /*!< Pointer to user registered transmit handler. */
    /* modem status interrupt handler:*/
    uart_irq_handler_t modemsts_handler;  /*!< Pointer to user registered modem status handler. */



};

extern uart_instance_t g_uart_0;

static void default_tx_handler(uart_instance_t * this_uart);
static void enable_irq(const uart_instance_t * this_uart);

static void disable_irq(const uart_instance_t * this_uart);

static void config_baud_divisors
(
    uart_instance_t * this_uart,
    uint32_t baudrate    
);

/***************************************************************************//**
  The UART_init() function initializes and configures the
  UART with the configuration passed as a parameter. The configuration
  parameters are the baud_rate which is used to generate the baud value and the
  line_config which is used to specify the line configuration (bit length,
  stop bits and parity).
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function.
  @param baud_rate
    The baud_rate parameter specifies the baud rate. It can be specified for
    common baud rates using the following defines:
    - UART_110_BAUD
    - UART_300_BAUD
    - UART_600_BAUD
    - UART_1200_BAUD
    - UART_2400_BAUD
    - UART_4800_BAUD
    - UART_9600_BAUD
    - UART_19200_BAUD
    - UART_38400_BAUD
    - UART_57600_BAUD
    - UART_115200_BAUD
    - UART_230400_BAUD
    - UART_460800_BAUD
    - UART_921600_BAUD
    
    Alternatively, any nonstandard baud rate can be specified by simply passing
    the actual required baud rate as the value for this parameter.
  @param line_config
    The line_config parameter is the line configuration specifying the bit length,
    number of stop bits and parity settings.
    
    This is a bitwise OR of one value from each of the following groups of
    allowed values:
    
    One of the following to specify the transmit/receive data bit length:
     - UART_DATA_5_BITS
     - UART_DATA_6_BITS,
     - UART_DATA_7_BITS
     - UART_DATA_8_BITS
     
    One of the following to specify the parity setting:
     - UART_NO_PARITY
     - UART_EVEN_PARITY
     - UART_ODD_PARITY
     - UART_STICK_PARITY_0
     - UART_STICK_PARITY_1
        
    One of the following to specify the number of stop bits:
     - UART_ONE_STOP_BIT
     - UART_ONEHALF_STOP_BIT
     - UART_TWO_STOP_BITS
  @return
    This function does not return a value.
  Example:
  @code
  #include "uart.h"
  int main(void)
  {
    UART_init(&g_uart0_lo,
             UART_57600_BAUD,
             UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                   
     return(0);
  }
  @endcode
 */
void
UART_init
(
    uart_instance_t* this_uart,
    uint32_t baud_rate,
    uint8_t line_config
);

/***************************************************************************//**
  The function UART_polled_tx() is used to transmit data. It transfers the
  contents of the transmitter data buffer, passed as a function parameter, into
  the UART's hardware transmitter FIFO. It returns when the full content of the
  transmit data buffer has been transferred to the UART's transmit FIFO. It is
  safe to release or reuse the memory used as the transmitter data buffer once
  this function returns.
  Note:     This function reads the UART's line status register (LSR) to poll
  for the active state of the transmitter holding register empty (THRE) bit
  before transferring data from the data buffer to the transmitter FIFO. It
  transfers data to the transmitter FIFO in blocks of 16 bytes or less and
  allows the FIFO to empty before transferring the next block of data.
  Note:     The actual transmission over the serial connection will still be
  in progress when this function returns. Use the UART_get_tx_status()
  function if you need to know when the transmitter is empty.
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function. 
  @param pbuff
    The pbuff parameter is a pointer to a buffer containing the data to
    be transmitted.
  @param tx_size
    The tx_size parameter specifies the size, in bytes, of the data to
    be transmitted.
  @return
    This function does not return a value.
  Example:
  @code
  #include "uart.h"
  int main(void)
  {
     uint8_t message[12] = "Hello World";
     UART_init(&g_uart0_lo,
              UART_57600_BAUD,
              SS_UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
     UART_polled_tx(&g_uart0_lo, message, sizeof(message));
     
     return(0);
  }
  @endcode
 */
void
UART_polled_tx
(
    uart_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
);

/***************************************************************************//**
  The function UART_polled_tx_string() is used to transmit a NULL ('\0')
  terminated string. It transfers the text string, from the buffer starting at
  the address pointed to by p_sz_string into the UART's hardware transmitter
  FIFO. It returns when the complete string has been transferred to the UART's
  transmit FIFO. It is safe to release or reuse the memory used as the string
  buffer once this function returns.
  Note:     This function reads the UART's line status register (LSR) to poll
  for the active state of the transmitter holding register empty (THRE) bit
  before transferring data from the data buffer to the transmitter FIFO. It
  transfers data to the transmitter FIFO in blocks of 16 bytes or less and
  allows the FIFO to empty before transferring the next block of data.
  Note:     The actual transmission over the serial connection will still be
  in progress when this function returns. Use the UART_get_tx_status()
  function if you need to know when the transmitter is empty.
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function.
  @param p_sz_string
    The p_sz_string parameter is a pointer to a buffer containing the NULL
    ('\0') terminated string to be transmitted.
  @return
    This function does not return a value.
  Example:
  @code
  #include "uart.h"
  int main(void)
  {
     uint8_t message[12] = "Hello World";
     UART_init(&g_uart0_lo,
             UART_57600_BAUD,
             UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                   
     UART_polled_tx_string(&g_uart0_lo, message);
     
     return(0);
  }
  @endcode
 */
void
UART_polled_tx_string
(
    uart_instance_t * this_uart,
    const uint8_t * p_sz_string
);

/***************************************************************************//**
  The function UART_irq_tx() is used to initiate an interrupt-driven
  transmit. It returns immediately after making a note of the transmit buffer
  location and enabling transmit interrupts both at the UART and the PolarFire
  SoC Core Complex PLIC level. This function takes a pointer via the pbuff
  parameter to a memory buffer containing the data to transmit. The memory
  buffer specified through this pointer must remain allocated and contain the
  data to transmit until the transmit completion has been detected through calls
  to function UART_tx_complete(). The actual transmission over the serial 
  connection is still in progress until calls to the UART_tx_complete() 
  function indicate transmit completion.
  Note:     The UART_irq_tx() function enables both the transmit holding
  register empty (THRE) interrupt in the UART and the UART instance
  interrupt in the PolarFire SoC Core Complex PLIC as part of its implementation.
  Note:     The UART_irq_tx() function assigns an internal default transmit
  interrupt handler function to the UART's THRE interrupt. This interrupt
  handler overrides any custom interrupt handler that you may have previously
  registered using the UART_set_tx_handler() function.
  Note:     The UART_irq_tx() function's default transmit interrupt
  handler disables the UART's THRE interrupt when all of the data has
  been transferred to the UART's transmit FIFO.
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function.
  @param pbuff
    The pbuff parameter is a pointer to a buffer containing the data
    to be transmitted.
  @param tx_size
    The tx_size parameter specifies the size, in bytes, of the data
    to be transmitted.
  @return
    This function does not return a value.
  Example:
  @code
  #include "uart.h"
  int main(void)
  {
     uint8_t tx_buff[10] = "abcdefghi";
     
     UART_init(&g_uart0_lo,
              UART_57600_BAUD,
              UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                   
     UART_irq_tx(&g_uart0_lo, tx_buff, sizeof(tx_buff));
     
     while(0 == UART_tx_complete(&g_uart0_lo))
     {
         ;
     }
     return(0);
  }
  @endcode
 */
void
UART_irq_tx
(
    uart_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
);

/***************************************************************************//**
  The UART_tx_complete() function is used to find out if the
  interrupt-driven transmit previously initiated through a call to
  UART_irq_tx() is complete. This is typically used to find out when it is
  safe to reuse or release the memory buffer holding transmit data.
  Note:     The transfer of all of the data from the memory buffer to the UART's
  transmit FIFO and the actual transmission over the serial connection are both
  complete when a call to the UART_tx_complete() function indicates transmit
  completion.
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function.
  @return
    This function return a non-zero value if transmit has completed, otherwise
    it returns zero.
  Example:
    See the UART_irq_tx() function for an example that uses the
    UART_tx_complete() function.
 */
int8_t
UART_tx_complete
(
   uart_instance_t * this_uart
);

/***************************************************************************//**
  The UART_get_rx() function reads the content of the UART receiver's FIFO
  and stores it in the receive buffer that is passed via the rx_buff function
  parameter. It copies either the full contents of the FIFO into the receive
  buffer, or just enough data from the FIFO to fill the receive buffer,
  dependent upon the size of the receive buffer passed by the buff_size
  parameter. The UART_get_rx() function returns the number of bytes copied
  into the receive buffer .This function is non-blocking and will return 0
  immediately if no data has been received.
  Note:     The UART_get_rx() function reads and accumulates the receiver
  status of the UART instance before reading each byte from the receiver's
  data register/FIFO. This allows the driver to maintain a sticky record of any
  receiver errors that occur as the UART receives each data byte; receiver
  errors would otherwise be lost after each read from the receiver's data
  register. A call to the UART_get_rx_status() function returns any receiver
  errors accumulated during the execution of the UART_get_rx() function.
  Note:     If you need to read the error status for each byte received, set
  the buff_size to 1 and read the receive line error status for each byte
  using the UART_get_rx_status() function.
  The UART_get_rx() function can be used in polled mode, where it is called
  at regular intervals to find out if any data has been received, or in
  interrupt driven-mode, where it is called as part of a receive handler that is
  called by the driver as a result of data being received.
  Note:     In interrupt driven mode you should call the UART_get_rx()
  function as part of the receive handler function that you register with
  the UART driver through a call to UART_set_rx_handler().
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function.
  @param rx_buff
    The rx_buff parameter is a pointer to a buffer where the received
    data is copied.
  @param buff_size
    The buff_size parameter specifies the size of the receive buffer in bytes.
  @return
    This function returns the number of bytes that were copied into the
    rx_buff buffer. It returns 0 if no data has been received.
  Polled mode example:
  @code
   int main( void )
   {
      uint8_t rx_buff[RX_BUFF_SIZE];
      uint32_t rx_idx  = 0;
      UART_init(&g_uart0_lo,
             UART_57600_BAUD,
             UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                    
      while(1)
      {
          rx_size = UART_get_rx(&g_uart0_lo, rx_buff, sizeof(rx_buff));
          if(rx_size > 0)
          {
              process_rx_data(rx_buff, rx_size);
          }
          task_a();
          task_b();
      }
      return 0;
   }
  @endcode
  Interrupt driven example:
  @code
   int main( void )
   {
      UART_init(&g_uart1,
              UART_57600_BAUD,
              UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                    
      UART_set_rx_handler(&g_uart1,
                              uart1_rx_handler,
                              UART_FIFO_SINGLE_BYTE);
      
      while(1)
      {
          task_a();
          task_b();
      }
      return 0;
   }
   void uart1_rx_handler(uart_instance_t * this_uart)
   {
      uint8_t rx_buff[RX_BUFF_SIZE];
      uint32_t rx_idx  = 0;
      rx_size = UART_get_rx(this_uart, rx_buff, sizeof(rx_buff));
      process_rx_data(rx_buff, rx_size);
   }
  @endcode
 */
size_t
UART_get_rx
(
   uart_instance_t * this_uart,
   uint8_t * rx_buff,
   size_t buff_size
);

/***************************************************************************//**
  The UART_set_rx_handler() function is used to register a receive handler
  function that is called by the driver when a UART receive data available (RDA)
  interrupt occurs. You must create and register the receive handler function
  to suit your application and it must include a call to the UART_get_rx()
  function to actually read the received data.
  Note:     The UART_set_rx_handler() function enables both the RDA
  interrupt in the UART instance. It also enables the corresponding 
  UART instance interrupt in the PolarFire SoC Core Complex PLIC  as part
  of its implementation.
  Note:     You can disable the RDA interrupt when required by calling the 
  UART_disable_irq() function. This is your choice and is dependent upon
  your application.
  
  @param this_uart
    The this_uart parameter is a pointer to an uart_instance_t
    structure identifying the UART hardware block that will perform
    the requested function.
  @param handler
    The handler parameter is a pointer to a receive interrupt handler function
    provided by your application that will be called as a result of a UART RDA
    interrupt. This handler function must be of type uart_irq_handler_t.
  @param trigger_level
    The trigger_level parameter is the receive FIFO trigger level. This
    specifies the number of bytes that must be received before the UART
    triggers an RDA interrupt.
  @return
    This function does not return a value.
  Example:
  @code
  #include "uart.h"
  #define RX_BUFF_SIZE    64
  uint8_t g_rx_buff[RX_BUFF_SIZE];
  void uart0_rx_handler(uart_instance_t * this_uart)
  {
      UART_get_rx(this_uart, &g_rx_buff[g_rx_idx], sizeof(g_rx_buff));
  }
  int main(void)
  {
      UART_init(&g_uart0_lo,
             UART_57600_BAUD,
             UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                    
      UART_set_rx_handler(&g_uart0_lo,
                              uart0_rx_handler,
                              UART_FIFO_SINGLE_BYTE);
                              
      while(1)
      {
         ;
      }
      return(0);
   }
  @endcode
 */
void
UART_set_rx_handler
(
    uart_instance_t *       this_uart,
    uart_irq_handler_t          handler,
    uart_rx_trig_level_t    trigger_level
);


#endif /*__UART_H_*/

