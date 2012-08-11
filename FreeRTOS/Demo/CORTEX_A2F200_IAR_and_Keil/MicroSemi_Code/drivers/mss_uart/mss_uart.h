/*******************************************************************************
 * (c) Copyright 2007 Actel Corporation.  All rights reserved.
 *
 * SmartFusion Microcontroller Subsystem UART bare metal software driver public API.
 *
 * SVN $Revision: 1942 $
 * SVN $Date: 2009-12-22 17:48:07 +0000 (Tue, 22 Dec 2009) $
 */
/*=========================================================================*//**
  @mainpage SmartFusion MSS UART Bare Metal Driver.

  @section intro_sec Introduction
  The SmartFusion MicroController Subsystem (MSS) includes two UART peripherals
  for serial communications.
  This driver provides a set of functions for controlling the MSS UARTs as part
  of a bare metal system where no operating system is available. These drivers
  can be adapted for use as part of an operating system but the implementation
  of the adaptation layer between this driver and the operating system's driver
  model is outside the scope of this driver.
  
  @section hw_dependencies Hardware Flow Dependencies
  The configuration of all features of the MSS UARTs is covered by this driver
  with the exception of the SmartFusion IOMUX configuration. SmartFusion allows
  multiple non-concurrent uses of some external pins through IOMUX configuration.
  This feature allows optimization of external pin usage by assigning external
  pins for use by either the microcontroller subsystem or the FPGA fabric. The
  MSS UARTs serial signals are routed through IOMUXes to the SmartFusion device
  external pins. These IOMUXes are configured automatically by the MSS
  configurator tool in the hardware flow correctly when the MSS UARTs are enabled
  in that tool. You must ensure that the MSS UARTs are enabled by the MSS
  configurator tool in the hardware flow; otherwise the serial inputs and outputs
  will not be connected to the chip's external pins. For more information on
  IOMUX, refer to the IOMUX section of the SmartFusion Datasheet.
  The base address, register addresses and interrupt number assignment for the MSS
  UART blocks are defined as constants in the SmartFusion CMSIS-PAL You must ensure
  that the SmartFusion CMSIS-PAL is either included in the software tool chain used
  to build your project or is included in your project.

  
  @section theory_op Theory of Operation
  The MSS UART driver uses the SmartFusion "Cortex Microcontroler Software
  Interface Standard - Peripheral Access Layer" (CMSIS-PAL) to access hadware
  registers. You must ensure that the SmartFusion CMSIS-PAL is either included
  in the software toolchain used to build your project or is included in your
  project. The most up to date SmartFusion CMSIS-PAL files can be obtained using
  the Actel Firmware Catalog.
  
  The MSS UART driver functions are logically grouped into three groups:
    - Initialization functions
    - Polled transmit and receive functions
    - Interrupt driven transmit and receive functions
  
  The MSS UART driver is initialized through a call to the UART_init() function.
  This function takes the UART's configuration as parameters. The UART_init()
  function must be called before any other UART driver functions can be called.
  The first parameter of the UART_init() function is a pointer to one of two
  global data structures used to store state information for each UART driver.
  A pointer to these data structures is also used as first parameter to any of
  the driver functions to identify which UART will be used by the called
  function. The name of these two data structures are g_mss_uart0 and
  g_mss_uart1. Therefore any call to a MSS UART function should be of the form
  UART_function_name( &g_mss_uart0, ... ) or UART_function_name( &g_mss_uart1, ... ).
  The two SmartFusion MSS UARTs can also be configured to loop back to each
  other using the MSS_set_loopback() function for debugging purposes.
  
  Polled operations where the processor constantly poll the UART registers state
  in order to control data transmit or data receive is performed using functions:
    - MSS_UART_polled_tx()
    - MSS_UART_get_rx()
  
  Interrupt driven operations where the processor sets up transmit or receive
  then returns to performing some other operation until an interrupts occurs
  indicating that its attention is required is performed using functions:
    - MSS_UART_irq_tx()
    - MSS_UART_tx_complete()
    - MSS_UART_set_rx_handler()
    - MSS_UART_get_rx()
  Interrupt driven transmit is initiated by a call to MSS_UART_irq_tx() specifying
  the block of data to transmit. The processor can then perform some other
  operation and later inquire whether transmit has completed by calling the
  MSS_UART_tx_complete() function.
  Interrupt driven receive is performed by first registering a receive handler
  function that will be called by the driver whenever receive data is available.
  This receive handler function in turns calls the MSS_UART_get_rx() function to
  actually read the received data.
  
 *//*=========================================================================*/
#ifndef __MSS_UART_H_
#define __MSS_UART_H_ 1

#include "../../CMSIS/a2fxxxm3.h"
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif 

/***************************************************************************//**
  Baud rates.
  The following definitions are used to specify standard baud rates as a
  parameter to the MSS_UART_init() function.
 */
#define MSS_UART_110_BAUD       110
#define MSS_UART_300_BAUD       300
#define MSS_UART_1200_BAUD      1200
#define MSS_UART_2400_BAUD      2400
#define MSS_UART_4800_BAUD      4800
#define MSS_UART_9600_BAUD      9600
#define MSS_UART_19200_BAUD     19200
#define MSS_UART_38400_BAUD     38400
#define MSS_UART_57600_BAUD     57600
#define MSS_UART_115200_BAUD    115200
#define MSS_UART_230400_BAUD    230400
#define MSS_UART_460800_BAUD    460800
#define MSS_UART_921600_BAUD    921600

/***************************************************************************//**
  Data bits length values.
 
  The following defines are used to build the value of the MSS_UART_init()
  function line_config parameter.
 */
#define MSS_UART_DATA_5_BITS     0x00
#define MSS_UART_DATA_6_BITS     0x01
#define MSS_UART_DATA_7_BITS     0x02
#define MSS_UART_DATA_8_BITS     0x03

/***************************************************************************//**
  Parity values
  The following defines are used to build the value of the MSS_UART_init()
  function line_config parameter.
 */
#define MSS_UART_NO_PARITY           0x00
#define MSS_UART_ODD_PARITY          0x08
#define MSS_UART_EVEN_PARITY         0x18
#define MSS_UART_STICK_PARITY_0      0x38
#define MSS_UART_STICK_PARITY_1      0x28

/***************************************************************************//**
  Stop bit values
  The following defines are used to build the value of the MSS_UART_init()
  function line_config parameter.
 */
#define MSS_UART_ONE_STOP_BIT        0x00
#define MSS_UART_ONEHALF_STOP_BIT    0x04
#define MSS_UART_TWO_STOP_BITS       0x04

/***************************************************************************//**
  FIFO trigger sizes
  This enumeration specifies the number of bytes that must be received before a
  receive interrupt is generated. This enumeration provides the allowed values for
  the MSS_UART_set_rx_handler() function trigger_level parameter.
 */
typedef enum __mss_uart_rx_trig_level_t {
    MSS_UART_FIFO_SINGLE_BYTE    = 0x00,
    MSS_UART_FIFO_FOUR_BYTES     = 0x40,
    MSS_UART_FIFO_EIGHT_BYTES    = 0x80,
    MSS_UART_FIFO_FOURTEEN_BYTES = 0xC0
} mss_uart_rx_trig_level_t;

/***************************************************************************//**
  Loopback.
  This enumeration is used as parameter to function MSS_UART_set_loopback(). It
  specifies the loopback configuration of the UARTs. Using MSS_UART_LOOPBACK_ON
  as parameter to function MSS_UART_set_loopback() will set up the UART to locally
  loopback its Tx and Rx lines.
 */
typedef enum __mss_uart_loopback_t {
    MSS_UART_LOOPBACK_OFF   = 0,
    MSS_UART_LOOPBACK_ON    = 1
} mss_uart_loopback_t;

/***************************************************************************//**
  Receive handler prototype.
  This typedef specifies the prototype of functions that can be registered with
  this driver as receive handler functions.
 */
typedef void (*mss_uart_rx_handler_t)(void);

/***************************************************************************//**
  mss_uart_instance_t.
 
  There is one instance of this structure for each instance of the Microcontroller
  Subsystem's UARTs. Instances of this structure are used to identify a specific
  UART. A pointer to an instance of the mss_uart_instance_t structure is passed
  as the first parameter to MSS UART driver functions to identify which UART
  should perform the requested operation.
 */
typedef struct {
    /* CMSIS related defines identifying the UART hardware. */
    UART_TypeDef *          hw_reg;     /*!< Pointer to UART registers. */
    UART_BitBand_TypeDef *  hw_reg_bit; /*!< Pointer to UART registers bit band area. */
    IRQn_Type               irqn;       /*!< UART's Cortex-M3 NVIC interrupt number. */
    
	/* transmit related info (used with interrupt driven trnasmit): */
	const uint8_t * tx_buffer;          /*!< Pointer to transmit buffer. */
	uint32_t        tx_buff_size;       /*!< Transmit buffer size. */
	uint32_t        tx_idx;             /*!< Index within trnamit buffer of next byte to transmit.*/
	
    /* receive interrupt handler:*/
    mss_uart_rx_handler_t rx_handler;   /*!< Pointer to user registered received handler. */
} mss_uart_instance_t;

/***************************************************************************//**
  This instance of mss_uart_instance_t holds all data related to the operations
  performed by UART0. A pointer to g_mss_uart0 is passed as the first parameter
  to MSS UART driver functions to indicate that UART0 should perform the requested
  operation.
 */
extern mss_uart_instance_t g_mss_uart0;

/***************************************************************************//**
  This instance of mss_uart_instance_t holds all data related to the operations
  performed by UART1. A pointer to g_mss_uart1 is passed as the first parameter
  to MSS UART driver functions to indicate that UART1 should perform the requested
  operation.
 */
extern mss_uart_instance_t g_mss_uart1;

/***************************************************************************//**
  The MSS_UART_init() function initializes and configures one of the SmartFusion
  MSS UARTs with the configuration passed as a parameter. The configuration
  parameters are the baud_rate which is used to generate the baud value and the
  line_config which is used to specify the line configuration (bit length, stop
  bits and parity).
 
  Example:
  @code
  #include "mss_uart.h"
 
  int main(void)
  {
      MSS_UART_init
        (
            &g_mss_uart0,
            MSS_UART_57600_BAUD,
            MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT
        );
      return(0);
  }
  @endcode
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block to be initialized. There are two
    such data structures, g_mss_uart0 and g_mss_uart1, associated with MSS UART0
    and MSS UART1 respectively. This parameter must point to either the
    g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
    
 
  @param baud_rate
    The baud_rate parameter specifies the baud rate. It can be specified for
    common baud rates' using the following defines:
        - MSS_UART_110_BAUD
        - MSS_UART_300_BAUD
        - MSS_UART_1200_BAUD
        - MSS_UART_2400_BAUD
        - MSS_UART_4800_BAUD
        - MSS_UART_9600_BAUD
        - MSS_UART_19200_BAUD
        - MSS_UART_38400_BAUD
        - MSS_UART_57600_BAUD
        - MSS_UART_115200_BAUD
        - MSS_UART_230400_BAUD
        - MSS_UART_460800_BAUD
        - MSS_UART_921600_BAUD 
    Alternatively, any non standard baud rate can be specified by simply passing
    the actual required baud rate as value for this parameter.
 
  @param line_config
    The line_config parameter is the line configuration specifying the bit length,
    number of stop bits and parity settings. This is a logical OR of one of the
    following to specify the transmit/receive data bit length: 
       - MSS_UART_DATA_5_BITS
       - MSS_UART_DATA_6_BITS,
       - MSS_UART_DATA_7_BITS
       - MSS_UART_DATA_8_BITS
    with one of the following to specify the parity setting:
       - MSS_UART_NO_PARITY
       - MSS_UART_EVEN_PARITY
       - MSS_UART_ODD_PARITY
       - MSS_UART_STICK_PARITY_0
       - MSS_UART_STICK_PARITY_1
    with one of the following to specify the number of stop bits:
       - MSS_UART_ONE_STOP_BIT
       - MSS_UART_ONEHALF_STOP_BIT
       - MSS_UART_TWO_STOP_BITS
 
  @return
    This function does not return a value.
 */
void
MSS_UART_init
(
	mss_uart_instance_t* this_uart,
    uint32_t baud_rate,
    uint8_t line_config
);

/***************************************************************************//**
  The function MSS_UART_polled_tx() is used to transmit data. It transfers the
  contents of the transmitter data buffer, passed as a function parameter, into
  the UART's hardware transmitter FIFO. It returns when the full content of the
  transmit data buffer has been transferred to the UART's transmit FIFO. 
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @param pbuff
    The pbuff parameter is a pointer to a buffer containing the data to be
    transmitted.
 
  @param tx_size
    The tx_size parameter specifies the size, in bytes, of the data to be
    transmitted.
 
  @return				This function does not return a value.
 */
void 
MSS_UART_polled_tx
( 
	mss_uart_instance_t * this_uart, 
	const uint8_t * pbuff,
	uint32_t tx_size
);

/***************************************************************************//**
  The function MSS_UART_polled_tx_string() is used to transmit a zero-terminated
  string. It transfers the text found starting at the address pointed to by
  p_sz_string into the UART's hardware transmitter FIFO. It returns when the
  complete string has been transferred to the UART's transmit FIFO. 
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @param p_sz_string
    The p_sz_string parameter is a pointer to a buffer containing the
    zero-terminated string to be transmitted.
 
  @return				This function does not return a value.
 */
void 
MSS_UART_polled_tx_string
( 
	mss_uart_instance_t * this_uart, 
	const uint8_t * p_sz_string
);


/***************************************************************************//**
  The function MSS_UART_irq_tx() is used to initiate interrupt driven transmit. It
  returns immediately after making a note of the transmit buffer location and
  enabling transmit interrupts both at the UART and Cortex-M3 NVIC level.
  This function takes a pointer to a memory buffer containing the data to
  transmit as parameter. The memory buffer specified through this pointer
  should remain allocated and contain the data to transmit until the transmit
  completion has been detected through calls to function MSS_UART_tx_complete().
  NOTE: The MSS_UART_irq_tx() function also enables the Transmitter Holding
  Register Empty (THRE) interrupt and the UART instance interrupt in the
  Cortex-M3 NVIC as part of its implementation.
  
  Example:
  @code
  #include "mss_uart.h"
 
  int main(void)
  {
      uint8_t tx_buff[10] = "abcdefghi";
      MSS_UART_init( &g_mss_uart0, MSS_UART_57600_BAUD, MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT );
      MSS_UART_irq_tx( &g_mss_uart0, tx_buff, sizeof(tx_buff));
      while ( 0 == MSS_UART_tx_complete( &g_mss_uart0 ) )
      {
          ;
      }
      return(0);
  }
  @endcode
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @param pbuff
    The pbuff parameter is a pointer to a buffer containing the data to be
    transmitted.
 
  @param tx_size
    The tx_size parameter specifies the size, in bytes, of the data to be
    transmitted.
 
  @return
    This function does not return a value.
 */
void 
MSS_UART_irq_tx
( 
	mss_uart_instance_t * this_uart, 
	const uint8_t * pbuff,
	uint32_t tx_size
);

/***************************************************************************//**
  The MSS_UART_tx_complete() function is used to find out if interrupt driven
  transmit previously initiated through a call to MSS_UART_irq_tx() is complete.
  This is typically used to find out when it is safe to reuse or release the
  memory buffer holding transmit data.
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @return
    This function return a non-zero value if transmit has completed, otherwise
    it returns zero.
 
  Example:
    See the MSS_UART_irq_tx() function for an example that uses the
    MSS_UART_tx_complete() function.
 */
int8_t
MSS_UART_tx_complete
(
   mss_uart_instance_t * this_uart
);

/***************************************************************************//**
  The MSS_UART_get_rx() function is used to read the content of a UART's receive
  FIFO. It can be used in polled mode where it is called at regular interval
  to find out if any data has been received or in interrupt driven mode where
  it is called as part of a receive handler called by the driver as a result of
  data being received. This function is non-blocking and will return 0
  immediately if no data has been received.
  NOTE: In interrupt driven mode you should call the MSS_UART_get_rx() function
  as part of the receive handler function that you register with the MSS UART
  driver through a call to MSS_UART_set_rx_handler().
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @param rx_buff
    The rx_buff parameter is a pointer to a buffer where the received data will
    be copied.
 
  @param buff_size
    The buff_size parameter specifies the size of the receive buffer in bytes.
 
  @return
    This function return the number of bytes that were copied into the rx_buff
    buffer. It returns 0 if no data has been received.
 
  Polled mode example:
  @code
   int main( void )
   {
      	uint8_t rx_buff[RX_BUFF_SIZE];
      	uint32_t rx_idx  = 0;
  
      	MSS_UART_init( &g_mss_uart0, MSS_UART_57600_BAUD, MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT );
  
      	while( 1 )
      	{
           rx_size = MSS_UART_get_rx( &g_mss_uart0, rx_buff, sizeof(rx_buff) );
           if (rx_size > 0)
           {
               process_rx_data( rx_buff, rx_size );
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
      	MSS_UART_init( &g_mss_uart1, MSS_UART_57600_BAUD, MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT );
       MSS_UART_set_rx_handler( &g_mss_uart1, uart1_rx_handler, MSS_UART_FIFO_SINGLE_BYTE );
  
      	while( 1 )
      	{
           task_a();
           task_b();
       }
       return 0;
   }
 
   void uart1_rx_handler( void )
   {
      	uint8_t rx_buff[RX_BUFF_SIZE];
       uint32_t rx_idx  = 0;
       rx_size = MSS_UART_get_rx( &g_mss_uart1, rx_buff, sizeof(rx_buff) );
       process_rx_data( rx_buff, rx_size );
   }
  @endcode
 */
size_t
MSS_UART_get_rx
(
   mss_uart_instance_t * this_uart,
   uint8_t * rx_buff,
   size_t buff_size
);

/***************************************************************************//**
  The MSS_UART_set_rx_handler() function is used to register a receive handler
  function which will be called by the driver when a UART Received Data Available
  (RDA) interrupt occurs. You must create and register the handler function to
  suit your application. The MSS_UART_set_rx_handler() function also enables the UART
  Received Data Available interrupt and the UART instance interrupt in the
  Cortex-M3 NVIC as part of its implementation.
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @param handler
    The handler parameter is a pointer to a receive handler function provided
    by your application which will be called as a result of a UART Received
    Data Available interrupt.
 
  @param trigger_level
    The trigger_level parameter is the receive FIFO trigger level. This specifies
    the number of bytes that must be received before the UART triggers a Received
    Data Available interrupt. 
                       
  @return
    This function does not return a value.
    
  Example:
  @code
  #include "mss_uart.h"
 
  #define RX_BUFF_SIZE    64
 
  uint8_t g_rx_buff[RX_BUFF_SIZE];
 
  void uart0_rx_handler( void )
  {
      MSS_UART_get_rx( &g_mss_uart, &g_rx_buff[g_rx_idx], sizeof(g_rx_buff) );
  }
 
  int main(void)
  {
      MSS_UART_init( &g_mss_uart0, MSS_UART_57600_BAUD, MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT );
      MSS_UART_set_rx_handler( &g_mss_uart0, uart0_rx_handler, MSS_UART_FIFO_SINGLE_BYTE );
 
      while ( 1 )
      {
          ;
      }
      return(0);
  }
  @endcode
 */
void
MSS_UART_set_rx_handler
(
	mss_uart_instance_t *       this_uart,
    mss_uart_rx_handler_t       handler,
    mss_uart_rx_trig_level_t    trigger_level
);

/***************************************************************************//**
  The MSS_UART_set_loopback() function is used to locally loopback the Tx and Rx
  lines of a UART.
  This is not to be confused with the loopback of UART0 to UART1 which can be
  achieved through the microcontroller subsystem's system registers
 
  @param this_uart
    The this_uart parameter is a pointer to an mss_uart_instance_t structure
    identifying the MSS UART hardware block that will perform the requested
    function. There are two such data structures, g_mss_uart0 and g_mss_uart1,
    associated with MSS UART0 and MSS UART1. This parameter must point to either
    the g_mss_uart0 or g_mss_uart1 global data structure defined within the UART
    driver.
 
  @param loopback
    The loopback parameter indicates whether or not the UART's transmit and receive lines
    should be looped back. Allowed values are:
       - MSS_UART_LOOPBACK_ON
       - MSS_UART_LOOPBACK_OFF
  @return
    This function does not return a value.
 */
void
MSS_UART_set_loopback
(
	mss_uart_instance_t *   this_uart,
	mss_uart_loopback_t     loopback
);

#ifdef __cplusplus
}
#endif

#endif /* __MSS_UART_H_ */
