/*******************************************************************************
 * (c) Copyright 2008 Actel Corporation.  All rights reserved.
 * 
 * SmartFusion microcontroller subsystem Peripheral DMA bare metal software
 * driver public API.
 *
 * SVN $Revision: 2110 $
 * SVN $Date: 2010-02-05 15:24:19 +0000 (Fri, 05 Feb 2010) $
 */
/*=========================================================================*//**
  @mainpage SmartFusion MSS GPIO Bare Metal Driver.

  @section intro_sec Introduction
  The SmartFusion Microcontroller Subsystem (MSS) includes an 8 channel
  Peripheral DMA (PDMA) controller.
  This software driver provides a set of functions for controlling the MSS PDMA
  controller as part of a bare metal system where no operating system is available.
  This driver can be adapted for use as part of an operating system but the
  implementation of the adaptation layer between this driver and the operating
  system's driver model is outside the scope of this driver.
  
  @section theory_op Theory of Operation
  The MSS PDMA driver uses the SmartFusion "Cortex Microcontroler Software
  Interface Standard - Peripheral Access Layer" (CMSIS-PAL) to access MSS hardware
  registers. You must ensure that the SmartFusion CMSIS-PAL is either included
  in the software toolchain used to build your project or is included in your
  project. The most up-to-date SmartFusion CMSIS-PAL files can be obtained using
  the Actel Firmware Catalog.
  
  The MSS PDMA driver functions are grouped into the following categories:
    - Initialization
    - Configuration
    - DMA transfer control
    - Interrupt control
  
  The MSS PDMA driver is initialized through a call to the PDMA_init() function.
  The PDMA_init() function must be called before any other PDMA driver functions
  can be called.
  
  Each PDMA channel is individually configured through a call to the PDMA_configure()
  function. Configuration includes:
    - channel priority
    - transfer size
    - source and/or destination address increment
    - source or destination of the DMA transfer
  PDMA channels can be divided into high and low priority channels. High priority
  channels are given more opportunities to perform transfers than low priority
  channels when there are continuous high priority channels requests. The ratio
  of high priority to low priority PDMA transfers is configurable through the
  PDMA_set_priority() function.
  PDMA channels can be configured to perform byte (8 bits), half-word (16 bits)
  or word (32 bits) transfers.
  The source and destination address of a PDMA channel’s transfers can be
  independently configured to increment by 0, 1, 2 or 4 bytes. For example, the
  content of a byte buffer located in RAM can be transferred into a peripheral’s
  transmit register by configuring the source address increment to one byte and
  no increment of the destination address.
  The source or destination of a PDMA channel’s transfers can be configured to
  be one of the MSS peripherals. This allows the PDMA controller to use some
  hardware flow control signaling with the peripheral to avoid overrunning the
  peripheral’s data buffer when the peripheral is the destination of the DMA
  transfer, or attempting to read data from the peripheral while it is not ready
  when the peripheral is the source of the transfer.
  A PDMA channel can also be configured to transfer data between two memory
  mapped locations (memory to memory). No hardware flow control is used by the
  PDMA controller for data transfer in this configuration.
  
  A DMA transfer can be initiated by a call to the PDMA_start() function after a
  PDMA channel has been configured. Once started, further data can be pushed
  through the PDMA channel by calling the PDMA_load_next_buffer() function. The
  PDMA_load_next_buffer() function can be called every time a call to the
  PDMA_status() function indicates that the PDMA channel used for the transfer
  has a free buffer or it can be called as a result of a PDMA interrupt.
  
  A DMA transfer can be paused and resumed through calls to functions PDMA_pause()
  and PDMA_resume().
  
  Your application can manage DMA transfers using interrupts through the use of
  the following functions:
    - PDMA_set_irq_handler()
    - PDMA_enable_irq()
    - PDMA_clear_irq()
    - PDMA_disable_irq()
  The PDMA_set_irq_handler() function is used to register PDMA channel interrupt
  handler functions with the driver. You must create and register an interrupt
  handler function for each interrupt driven PDMA channel used by the application.
  Use the PDMA_enable_irq() function to enable interrupts for the PDMA channels. 
  Every time a PDMA channel completes the transfer of a buffer it causes a PDMA
  interrupt to occur and the PDMA driver will call the interrupt handler
  registered by the application for that PDMA channel.
  
 *//*=========================================================================*/
#ifndef __MSS_PERIPHERAL_DMA_H_
#define __MSS_PERIPHERAL_DMA_H_

#ifdef __cplusplus
extern "C" {
#endif 

#include "../../CMSIS/a2fxxxm3.h"

/***************************************************************************//**
  The pdma_channel_id_t enumeration is used to identify peripheral DMA channels.
  It is used as function parameter to specify the PDMA channel used.
 */
typedef enum __pdma_channel_id
{
    PDMA_CHANNEL_0 = 0,
    PDMA_CHANNEL_1,
    PDMA_CHANNEL_2,
    PDMA_CHANNEL_3,
    PDMA_CHANNEL_4,
    PDMA_CHANNEL_5,
    PDMA_CHANNEL_6,
    PDMA_CHANNEL_7
} pdma_channel_id_t;

/***************************************************************************//**
  The pdma_src_dest_t enumeration is used to specify the source or destination
  of transfers on a PDMA channel. It specifies which hardware peripheral will be
  the source or destination of DMA transfers. This allows the PDMA controller
  to use hardware flow control signals to avoid overrunning a
  destination peripheral with data it is not ready to receive, or attempting to
  transfer data from a peripheral while it has no data ready to transfer.
  The pdma_src_dest_t enumeration can also be used to specify that a PDMA channel
  is configured to transfer data between two memory mapped locations
  (memory to memory). No hardware data flow control is used by the PDMA
  controller in this configuration.
  This enumeration is used as parameter to function PDMA_configure().
 */
typedef enum __pdma_src_dest
{
    PDMA_FROM_UART_0 = 0,
    PDMA_TO_UART_0,
    PDMA_FROM_UART_1,
    PDMA_TO_UART_1,
    PDMA_FROM_SPI_0,
    PDMA_TO_SPI_0,
    PDMA_FROM_SPI_1,
    PDMA_TO_SPI_1,
    PDMA_FROM_FPGA_1,
    PDMA_TO_FPGA_1,
    PDMA_FROM_FPGA_0,
    PDMA_TO_FPGA_0,
    PDMA_TO_ACE,
    PDMA_FROM_ACE,
    PDMA_MEM_TO_MEM
} pdma_src_dest_t;

/***************************************************************************//**
  The pdma_priority_ratio_t enumeration is used to configure the ratio of high
  priority to low priority PDMA channels.  This ratio specifies how many DMA
  transfer opportunities will be given to high priority channels before a DMA
  transfer opportunity is given to a low priority channel when there are
  continuous requests from high priority channels. This enumeration is used as
  parameter to function PDMA_set_priority_ratio().
 */
typedef enum __pdma_priority_ratio_t
{
    PDMA_ROUND_ROBIN = 0,
    PDMA_RATIO_HIGH_LOW_1_TO_1 = 1,
    PDMA_RATIO_HIGH_LOW_3_TO_1 = 3,
    PDMA_RATIO_HIGH_LOW_7_TO_1 = 7,
    PDMA_RATIO_HIGH_LOW_15_TO_1 = 15,
    PDMA_RATIO_HIGH_LOW_31_TO_1 = 31,
    PDMA_RATIO_HIGH_LOW_63_TO_1 = 63,
    PDMA_RATIO_HIGH_LOW_127_TO_1 = 127,
    PDMA_RATIO_HIGH_LOW_255_TO_1 = 255
} pdma_priority_ratio_t;


/***************************************************************************//**
  The pdma_channel_isr_t type is a pointer to a PDMA channel interrupt handler
  function. It specifies the function prototype of functions that can be
  registered as PDMA channel interrupt handlers. It is used as parameter to
  function PDMA_set_irq_handler().
 */
typedef void (*pdma_channel_isr_t)( void );
/***************************************************************************//**
  These constants are used to build the channel_cfg parameter of the
  PDMA_configure() function. They specify whether a channel is a high or low
  priority channel.
 */
#define PDMA_LOW_PRIORITY    0x0000
#define PDMA_HIGH_PRIORITY   0x0200

/***************************************************************************//**
  These constants are used to build the channel_cfg parameter of the
  PDMA_configure() function. They specify the data width of the transfers
  performed by a PDMA channel.
 */
#define PDMA_BYTE_TRANSFER       0x0000     /* Byte transfers (8 bits) */
#define PDMA_HALFWORD_TRANSFER   0x0004     /* Half-word transfers (16 bits) */
#define PDMA_WORD_TRANSFER       0x0008     /* Word transfers (32 bits) */

/***************************************************************************//**
  These constants are used to build the channel_cfg parameter of the
  PDMA_configure() function. They specify the PDMA channel’s source and
  destination address increment.
 */
#define PDMA_NO_INC  0
#define PDMA_INC_SRC_ONE_BYTE    0x0400
#define PDMA_INC_SRC_TWO_BYTES   0x0800
#define PDMA_INC_SRC_FOUR_BYTES  0x0C00
#define PDMA_INC_DEST_ONE_BYTE   0x1000
#define PDMA_INC_DEST_TWO_BYTES  0x2000
#define PDMA_INC_DEST_FOUR_BYTES 0x3000

/***************************************************************************//**
 * Mask for various control register bits.
 */
#define PDMA_IRQ_ENABLE_MASK    (uint32_t)0x00000040
#define PDMA_PAUSE_MASK         (uint32_t)0x00000010

/***************************************************************************//**
  These constants are used to specify the src_addr parameter to the PDMA_start()
  and PDMA_load_next_buffer() functions. They specify the receive register
  address of peripherals that can be the source of a DMA transfer. 
  When a PDMA channel is configured for DMA transfers from a peripheral to memory,
  the constant specifying that peripheral’s receive register address must be used
  as the src_addr parameter.
 */
#define PDMA_SPI0_RX_REGISTER       0x40001010uL
#define PDMA_SPI1_RX_REGISTER       0x40011010uL
#define PDMA_UART0_RX_REGISTER      0x40000000uL
#define PDMA_UART1_RX_REGISTER      0x40010000uL
#define PDMA_ACE_PPE_DATAOUT        0x40021308uL

/***************************************************************************//**
  These constants are used to specify the dest_addr parameter to the PDMA_start()
  and PDMA_load_next_buffer() functions. They specify the transmit register
  address of peripherals that can be the destination of a DMA transfer. 
  When a PDMA channel is configured for DMA transfers from memory to a peripheral,
  the constant specifying that peripheral’s transmit register address must be used
  as the dest_addr parameter.
 */
#define PDMA_SPI0_TX_REGISTER       0x40001014uL
#define PDMA_SPI1_TX_REGISTER       0x40011014uL
#define PDMA_UART0_TX_REGISTER      0x40000000uL
#define PDMA_UART1_TX_REGISTER      0x40010000uL
#define PDMA_ACE_SSE_DATAIN         0x40020700uL

/***************************************************************************//**
  The PDMA_DEFAULT_WRITE_ADJ constant provides a suitable default value for the
  PDMA_configure() function write_adjust parameter.
 */
#define PDMA_DEFAULT_WRITE_ADJ      10u

/***************************************************************************//**
  The PDMA_init() function initializes the peripheral DMA hardware and driver
  internal data. It resets the PDMA and it also clears any pending PDMA
  interrupts in the Cortex-M3 interrupt controller. When the function exits, it
  takes the PDMA block out of reset.
 */
void PDMA_init( void );

/***************************************************************************//**
  The PDMA_configure() function configures a PDMA channel.
  It specifies:
   - The peripheral which will be the source or destination of the DMA transfer.
   - Whether the DMA channel will be a high or low priority channel
   - The source and destination address increment that will take place after
     each transfer.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 
  @param src_dest
    The src_dest parameter specifies the source or destination of the DMA
    transfers that will be performed. It can be one of the following:
        - PDMA_FROM_UART_0
        - PDMA_TO_UART_0
        - PDMA_FROM_UART_1
        - PDMA_TO_UART_1
        - PDMA_FROM_SPI_0
        - PDMA_TO_SPI_0
        - PDMA_FROM_SPI_1
        - PDMA_TO_SPI_1
        - PDMA_FROM_FPGA_1
        - PDMA_TO_FPGA_1
        - PDMA_FROM_FPGA_0
        - PDMA_TO_FPGA_0
        - PDMA_TO_ACE
        - PDMA_FROM_ACE
        - PDMA_MEM_TO_MEM
 
  @param channel_cfg
    The channel_cfg parameter specifies the configuration of the PDMA channel.
    The configuration includes:
        - channel priority
        - transfer size
        - source and/or destination address increment
    The channel_cfg parameter value is a logical OR of:
        One of the following to specify the channel priority:
           - PDMA_LOW_PRIORITY
           - PDMA_HIGH_PRIORITY
        One of the following to specify the transfer size:
           - PDMA_BYTE_TRANSFER
           - PDMA_HALFWORD_TRANSFER
           - PDMA_WORD_TRANSFER
        One or two of the following to specify the source and/or destination address
        increment:
           - PDMA_NO_INC
           - PDMA_INC_SRC_ONE_BYTE
           - PDMA_INC_SRC_TWO_BYTES
           - PDMA_INC_SRC_FOUR_BYTES
           - PDMA_INC_DEST_ONE_BYTE
           - PDMA_INC_DEST_TWO_BYTES
           - PDMA_INC_DEST_FOUR_BYTES
  
  @param write_adjust
    The write_adjust parameter specifies the number of Cortex-M3 clock cycles
    the PDMA controller will wait before attempting another transfer cycle. This
    delay is necessary when peripherals are used as destination of a DMA transfer
    to ensure the DMA controller interprets the state of the peripheral’s ready
    signal only after data has actually been written to the peripheral. This delay
    accounts for posted writes (dump and run) for write accesses to peripherals. 
    The effect of posted writes is that if the PDMA performs a write operation to
    a peripheral, the data is not actually written into the peripheral until
    sometime after the PDMA controller thinks it is written.
    A suitable value for write_adjust depends on the target of the DMA transfer.
    Guidelines for choosing this value are as follows:
        • The PDMA_DEFAULT_WRITE_ADJ constant provides a suitable default value
          for the write_adjust parameter when the PDMA channel is configured for
          transfers with MSS peripherals.
        • The PDMA_DEFAULT_WRITE_ADJ constant can also be used for DMA transfers
          with FPGA fabric implemented peripherals making use of the DMAREADY0 or
          DMAREADY1fabric interface signal to indicate that the peripheral is
          ready for another DMA transfer.
        • The write_adjust parameter can be set to zero to achieve maximum transfer
          speed for genuine memory to memory transfers. 
        • The internal latency of FPGA implemented peripherals will decide the
          write_adjust value for fabric peripherals that do not use the DMAREADY0
          or DMAREADY1 fabric interface signals. You need to check the fabric
          peripheral documentation for the value to use.
    
  Example:
  @code
   PDMA_configure
   (
       PDMA_CHANNEL_0,
       PDMA_TO_SPI_1,
       PDMA_LOW_PRIORITY | PDMA_BYTE_TRANSFER | PDMA_INC_SRC_ONE_BYTE,
       PDMA_DEFAULT_WRITE_ADJ
   );
  @endcode
 */
void PDMA_configure
(
    pdma_channel_id_t channel_id,
    pdma_src_dest_t src_dest,
    uint32_t channel_cfg,
    uint8_t write_adjust
);


/***************************************************************************//**
  The PDMA_set_priority_ratio() function sets the ratio of high priority to low
  priority DMA access opportunities. This ratio is used by the PDMA controller
  arbiter to decide which PDMA channel will be given the opportunity to perform
  a transfer when multiple PDMA channels are requesting to transfer data at the
  same time. The priority ratio specifies how many DMA transfer opportunities
  will be given to high priority channels before a DMA transfer opportunity is
  given to a low priority channel when there are continuous requests from high
  priority channels.
 
  @param priority_ratio
    The priority_ratio parameter specifies the ratio of DMA access opportunities
    given to high priority channels versus low priority channels.
    Allowed values for this parameter are:
       - PDMA_ROUND_ROBIN
       - PDMA_RATIO_HIGH_LOW_1_TO_1
       - PDMA_RATIO_HIGH_LOW_3_TO_1
       - PDMA_RATIO_HIGH_LOW_7_TO_1
       - PDMA_RATIO_HIGH_LOW_15_TO_1
       - PDMA_RATIO_HIGH_LOW_31_TO_1
       - PDMA_RATIO_HIGH_LOW_63_TO_1
       - PDMA_RATIO_HIGH_LOW_127_TO_1
       - PDMA_RATIO_HIGH_LOW_255_TO_1
 
  Example:
  @code
   PDMA_set_priority_ratio( PDMA_ROUND_ROBIN );
  @endcode
 */
static __INLINE void PDMA_set_priority_ratio
(
    pdma_priority_ratio_t priority_ratio
)
{
    PDMA->RATIO_HIGH_LOW = (uint32_t)priority_ratio;
}

/***************************************************************************//**
  The PDMA_start() function  initiates a DMA transfer. It specifies the source
  and destination address of the transfer as well as the number of transfers
  that must take place. The source and destination addresses can be the address
  of peripheral registers.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 
  @param src_addr
    The src_addr parameter specifies the address location of the data to be
    transferred. You must ensure that this source address is consistent with the
    DMA source configured for the selected channel using the PDMA_configure()
    function.
    For DMA transfers from MSS peripheral to memory, the following src_addr
    parameter values are allowed:
        • PDMA_SPI0_RX_REGISTER
        • PDMA_SPI1_RX_REGISTER
        • PDMA_UART0_RX_REGISTER
        • PDMA_UART1_RX_REGISTER
        • PDMA_ACE_PPE_DATAOUT
    For DMA transfers from FPGA fabric peripheral to memory, the following
    src_addr parameter values are allowed:
        • An address in the FPGA fabric address space (0x40050000-0x400FFFFF)
    For DMA transfers from memory to MSS peripheral, or from memory to FPGA
    fabric peripheral, or from memory to memory, the following src_addr
    parameter values are allowed:
        • Any memory mapped address.

  @param dest_addr
    The dest_addr parameter specifies the destination address of the PDMA
    transfer. You must ensure that this matches with the DMA destination
    configured for the selected channel.
    For DMA transfers from memory to MSS peripheral, the following dest_addr parameter values are allowed:
        • PDMA_SPI0_TX_REGISTER
        • PDMA_SPI1_TX_REGISTER
        • PDMA_UART0_TX_REGISTER
        • PDMA_UART1_TX_REGISTER
        • PDMA_ACE_SSE_DATAIN
    For DMA transfers from memory to FPGA fabric peripheral, the following
    dest_addr parameter values are allowed:
        • An address in the FPGA fabric address space (0x40050000-0x400FFFFF)
    For DMA transfers from MSS peripheral to memory, or from FPGA fabric
    peripheral to memory, or from memory to memory, the following dest_addr
    parameter values are allowed:
        • Any memory mapped address.

  @param transfer_count
    The transfer_count parameter specifies the number of transfers to be
    performed. It is the number of bytes to transfer if the PDMA channel is
    configured for byte transfer, the number of half-words to transfer if the
    PDMA channel is configured for half-word transfer, or the number of words
    to transfer if the PDMA channel is configured for word transfer.
 
  Example:
  @code
    PDMA_start
      (
          PDMA_CHANNEL_3,
          PDMA_SPI1_RX_REGISTER,
          (uint32_t)slave_rx_buffer,
          sizeof(slave_rx_buffer)
      ); 
  @endcode
 */
void PDMA_start
(
    pdma_channel_id_t channel_id,
    uint32_t src_addr,
    uint32_t dest_addr,
    uint16_t transfer_count
);

/***************************************************************************//**
  The PDMA_load_next_buffer() function sets the next buffer to be transferred.
  This function is called after a transfer has been initiated using the
  PDMA_start() function. Its purpose is to keep feeding a PDMA channel with data
  buffers.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 
  @param src_addr
    The src_addr parameter specifies the address location of the data to be
    transferred. You must ensure that this source address is consistent with the
    DMA source configured for the selected channel using the PDMA_configure()
    function.
    For DMA transfers from MSS peripheral to memory, the following src_addr parameter values are allowed:
        • PDMA_SPI0_RX_REGISTER
        • PDMA_SPI1_RX_REGISTER
        • PDMA_UART0_RX_REGISTER
        • PDMA_UART1_RX_REGISTER
        • PDMA_ACE_PPE_DATAOUT
    For DMA transfers from FPGA fabric peripheral to memory, the following src_addr parameter values are allowed:
        • An address in the FPGA fabric address space (0x40050000-0x400FFFFF)
    For DMA transfers from memory to MSS peripheral, or from memory to FPGA fabric peripheral, or from memory to memory, the following src_addr parameter values are allowed:
        • Any memory mapped address.

  @param dest_addr
    The dest_addr parameter specifies the destination address of the PDMA
    transfer. You must ensure that this matches with the DMA destination
    configured for the selected channel.
    For DMA transfers from memory to MSS peripheral, the following dest_addr parameter values are allowed:
        • PDMA_SPI0_TX_REGISTER
        • PDMA_SPI1_TX_REGISTER
        • PDMA_UART0_TX_REGISTER
        • PDMA_UART1_TX_REGISTER
        • PDMA_ACE_SSE_DATAIN
    For DMA transfers from memory to FPGA fabric peripheral, the following dest_addr parameter values are allowed:
        • An address in the FPGA fabric address space (0x40050000-0x400FFFFF)
    For DMA transfers from MSS peripheral to memory, or from FPGA fabric peripheral to memory, or from memory to memory, the following dest_addr parameter values are allowed:
        • Any memory mapped address.
 
  @param transfer_count
    The transfer_count parameter specifies the number of transfers to be
    performed. It is the number of bytes to transfer if the PDMA channel is
    configured for byte transfer, the number of half-words to transfer if the
    PDMA channel is configured for half-word transfer or the number of words to
    transfer if the PDMA channel is configured for word transfer.
    
  Example:
  @code
  void write_cmd_data
  (
      mss_spi_instance_t * this_spi,
      const uint8_t * cmd_buffer,
      uint16_t cmd_byte_size,
      uint8_t * data_buffer,
      uint16_t data_byte_size
  )
  {
      uint32_t transfer_size;
      
      transfer_size = cmd_byte_size + data_byte_size;
  
      MSS_SPI_disable( this_spi );
      MSS_SPI_set_transfer_byte_count( this_spi, transfer_size );
  
      PDMA_start
          (
              PDMA_CHANNEL_0,
              (uint32_t)cmd_buffer,
              PDMA_SPI1_TX_REGISTER,
              cmd_byte_size
          );
      
      PDMA_load_next_buffer
          (
              PDMA_CHANNEL_0,
              (uint32_t)data_buffer,
              PDMA_SPI1_TX_REGISTER,
              data_byte_size
          );
      
      MSS_SPI_enable( this_spi );
      
      while ( !MSS_SPI_tx_done(this_spi) )
      {
          ;
      }
  }
  @endcode
 */
void PDMA_load_next_buffer
(
    pdma_channel_id_t channel_id,
    uint32_t src_addr,
    uint32_t dest_addr,
    uint16_t transfer_count
);

/***************************************************************************//**
  The PDMA_status() function returns the status of a DMA channel.
  The returned value indicates if transfers have been completed using buffer A
  or buffer B of the PDMA hardware block.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 
  @return
    bit 0 of the return value indicates if buffer A has been trasnfered. It is
    set to 1 if the transfer has completed.
    bit 1 of the return value indicates if buffer B has been transfered. It is
    set to 1 if the transfer has completed.
 */
uint32_t PDMA_status
(
    pdma_channel_id_t  channel_id
);

/***************************************************************************//**
  The PDMA_pause() function temporarily pauses a PDMA transfer taking place on
  the specified PDMA channel. The transfer can later be resumed by using the
  PDMA_resume() function.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 */
static __INLINE void PDMA_pause( pdma_channel_id_t channel_id )
{
    PDMA->CHANNEL[channel_id].CRTL |= PDMA_PAUSE_MASK;
}

/***************************************************************************//**
  The PDMA_resume() function resumes a transfer previously paused using the
  PDMA_pause() function.
 
  @param channel_id    The channel_id parameter identifies the PDMA channel
                       used by the function.
 */
static __INLINE void PDMA_resume( pdma_channel_id_t channel_id )
{
    PDMA->CHANNEL[channel_id].CRTL &= ~PDMA_PAUSE_MASK;
}

/***************************************************************************//**
  The PDMA_enable_irq() enables the PDMA hardware to generate an interrupt when
  a DMA transfer completes on the specified PDMA channel. This function also
  enables the PDMA interrupt in the Cortex-M3 interrupt controller.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 */
void PDMA_enable_irq( pdma_channel_id_t channel_id );

/***************************************************************************//**
  The PDMA_disable_irq() disables interrupts for a specific PDMA channel.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 */
static __INLINE void PDMA_disable_irq( pdma_channel_id_t channel_id )
{
    PDMA->CHANNEL[channel_id].CRTL &= ~PDMA_IRQ_ENABLE_MASK;
}

/***************************************************************************//**
  The PDMA_set_irq_handler() function registers a handler function for
  interrupts generated on the completion of a transfer on a specific PDMA
  channel. This function also enables the PDMA interrupt both in the PDMA
  controller and in the Cortex-M3 interrupt controller.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
    
  @param handler
    The handler parameter is a pointer to the function that will be called when
    a transfer completes on the PDMA channel identified by channel_id and the
    interrupt is enabled for that channel.
    
  Example:
  @code
  void slave_dma_irq_handler( void )
  {
      if ( g_spi1_rx_buffer[2] == 0x99 )
      {
          PDMA_load_next_buffer
          (
              PDMA_CHANNEL_0,
              (uint32_t)g_spi1_tx_buffer_b,
              PDMA_SPI1_TX_REGISTER,
              sizeof(g_spi1_tx_buffer_b)
          );      
      }
      PDMA_disable_irq( PDMA_CHANNEL_3 );
  }
  
  void setup_dma( void )
  {
      PDMA_init();
      PDMA_configure
      (
           PDMA_CHANNEL_0, 
           PDMA_TO_SPI_1, 
           PDMA_LOW_PRIORITY | PDMA_BYTE_TRANSFER | PDMA_INC_SRC_ONE_BYTE
      );
      PDMA_configure
      ( 
           PDMA_CHANNEL_3,
           PDMA_FROM_SPI_1,
           PDMA_HIGH_PRIORITY | PDMA_BYTE_TRANSFER | PDMA_INC_DEST_ONE_BYTE
      );
      PDMA_set_irq_handler( PDMA_CHANNEL_3, slave_dma_irq_handler );
      PDMA_start( PDMA_CHANNEL_3, PDMA_SPI1_RX_REGISTER, (uint32_t)g_spi1_rx_buffer, 3 ); 
  }
  @endcode
 */
void PDMA_set_irq_handler
(
    pdma_channel_id_t channel_id,
    pdma_channel_isr_t handler
);

/***************************************************************************//**
  The PDMA_clear_irq() function clears interrupts for a specific PDMA channel.
  This function also clears the PDMA interrupt in the Cortex-M3 NVIC.
 
  @param channel_id
    The channel_id parameter identifies the PDMA channel used by the function.
 */
void PDMA_clear_irq
(
    pdma_channel_id_t channel_id
);

#ifdef __cplusplus
}
#endif

#endif  /* __MSS_PERIPHERAL_DMA_H_ */
