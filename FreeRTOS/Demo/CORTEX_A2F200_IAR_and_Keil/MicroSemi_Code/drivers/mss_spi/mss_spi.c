/*******************************************************************************
 * (c) Copyright 2008 Actel Corporation.  All rights reserved.
 * 
 * SmartFusion microcontroller subsystem SPI bare metal software driver
 * implementation.
 *
 * SVN $Revision: 2176 $
 * SVN $Date: 2010-02-15 21:04:22 +0000 (Mon, 15 Feb 2010) $
 */
#include "mss_spi.h"
#include "../../CMSIS/mss_assert.h"

#ifdef __cplusplus
extern "C" {
#endif 

/***************************************************************************//**
  MSS SPI can operate as master or slave.
 */
#define MSS_SPI_MODE_SLAVE      (uint32_t)0
#define MSS_SPI_MODE_MASTER     (uint32_t)1

/***************************************************************************//**
 * Mask of transfer protocol and SPO, SPH bits within control register.
 */
#define PROTOCOL_MODE_MASK  (uint32_t)0x030000C0

/***************************************************************************//**
 * Mask of theframe count bits within the SPI control register.
 */
#define TXRXDFCOUNT_MASK    (uint32_t)0x00FFFF00
#define TXRXDFCOUNT_SHIFT   (uint32_t)8

/***************************************************************************//**
 * SPI hardware FIFO depth.
 */
#define RX_FIFO_SIZE    4u

/***************************************************************************//**
  Marker used to detect that the configuration has not been selected for a
  specific slave when operating as a master.
 */
#define NOT_CONFIGURED  0xFFFFFFFF

/***************************************************************************//**
 * SPI instance data structures for SPI0 and SPI1. A pointer to these data
 * structures must be used as first parameter to any of the SPI driver functions
 * to identify the SPI hardware block that will perform the requested operation.
 */
mss_spi_instance_t g_mss_spi0;
mss_spi_instance_t g_mss_spi1;

/***************************************************************************//**
  SPI0 interrupt service routine
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void SPI0_IRQHandler( void );
#else
void SPI0_IRQHandler( void );
#endif

/***************************************************************************//**
  SPI1 interrupt service routine
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void SPI1_IRQHandler( void );
#else
void SPI1_IRQHandler( void );
#endif

/***************************************************************************//**
 * MSS_SPI_init()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_init
(
	mss_spi_instance_t * this_spi
)
{
    uint16_t i;
    
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    if (this_spi == &g_mss_spi0)
    {
        this_spi->hw_reg = SPI0;
        this_spi->hw_reg_bit = SPI0_BITBAND;
        this_spi->irqn = SPI0_IRQn;

        /* reset SPI0 */
        SYSREG->SOFT_RST_CR |= SYSREG_SPI0_SOFTRESET_MASK;
        /* Clear any previously pended SPI0 interrupt */
        NVIC_ClearPendingIRQ( SPI0_IRQn );
        /* Take SPI0 out of reset. */
        SYSREG->SOFT_RST_CR &= ~SYSREG_SPI0_SOFTRESET_MASK;
    }
    else
    {
        this_spi->hw_reg = SPI1;
        this_spi->hw_reg_bit = SPI1_BITBAND;
        this_spi->irqn = SPI1_IRQn;
        
        /* reset SPI1 */
        SYSREG->SOFT_RST_CR |= SYSREG_SPI1_SOFTRESET_MASK;
        /* Clear any previously pended SPI1 interrupt */
        NVIC_ClearPendingIRQ( SPI1_IRQn );
        /* Take SPI1 out of reset. */
        SYSREG->SOFT_RST_CR &= ~SYSREG_SPI1_SOFTRESET_MASK;
    }
    
    this_spi->frame_rx_handler = 0U;
    this_spi->slave_tx_frame = 0U;
    
    this_spi->block_rx_handler = 0U;
    
    this_spi->slave_tx_buffer = 0U;
    this_spi->slave_tx_size = 0U;
    this_spi->slave_tx_idx = 0U;
    
    for ( i = 0u; i < (uint16_t)MSS_SPI_MAX_NB_OF_SLAVES; ++i )
    {
        this_spi->slaves_cfg[i].ctrl_reg = NOT_CONFIGURED;
    }
}

/***************************************************************************//**
 * MSS_SPI_configure_slave_mode()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_configure_slave_mode
(
	mss_spi_instance_t * this_spi,
    mss_spi_protocol_mode_t protocol_mode,
    mss_spi_pclk_div_t clk_rate,
    uint8_t frame_bit_length
)
{
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    ASSERT( frame_bit_length <= 32 );
    
	/* Set the mode. */
    this_spi->hw_reg_bit->CTRL_MASTER = MSS_SPI_MODE_SLAVE;

    /* Set the clock rate. */
    this_spi->hw_reg_bit->CTRL_ENABLE = 0U;
    this_spi->hw_reg->CONTROL = (this_spi->hw_reg->CONTROL & ~PROTOCOL_MODE_MASK) | (uint32_t)protocol_mode;
    this_spi->hw_reg->CLK_GEN = (uint32_t)clk_rate;
    
    /* Set default frame size to byte size and number of data frames to 1. */
    this_spi->hw_reg->CONTROL = (this_spi->hw_reg->CONTROL & ~TXRXDFCOUNT_MASK) | ((uint32_t)1 << TXRXDFCOUNT_SHIFT);
    this_spi->hw_reg->TXRXDF_SIZE = frame_bit_length;
    this_spi->hw_reg_bit->CTRL_ENABLE = 1U;
}

/***************************************************************************//**
 * MSS_SPI_configure_master_mode()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_configure_master_mode
(
	mss_spi_instance_t *    this_spi,
	mss_spi_slave_t         slave,
    mss_spi_protocol_mode_t protocol_mode,
    mss_spi_pclk_div_t      clk_rate,
    uint8_t                 frame_bit_length
)
{
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    ASSERT( slave < MSS_SPI_MAX_NB_OF_SLAVES );
    ASSERT( frame_bit_length <= 32 );
    
	/* Set the mode. */
    this_spi->hw_reg_bit->CTRL_ENABLE = 0U;
    this_spi->hw_reg_bit->CTRL_MASTER = MSS_SPI_MODE_MASTER;
    this_spi->hw_reg_bit->CTRL_ENABLE = 1U;

    /*
     * Keep track of the required register configuration for this slave. These
     * values will be used by the MSS_SPI_set_slave_select() function to configure
     * the master to match the slave being selected.
     */
    if ( slave < MSS_SPI_MAX_NB_OF_SLAVES )     
    {
        this_spi->slaves_cfg[slave].ctrl_reg = 0x00000002uL | (uint32_t)protocol_mode | ((uint32_t)1 << TXRXDFCOUNT_SHIFT);
        this_spi->slaves_cfg[slave].txrxdf_size_reg = frame_bit_length;
        this_spi->slaves_cfg[slave].clk_gen = (uint8_t)clk_rate;
    }
}

/***************************************************************************//**
 * MSS_SPI_set_slave_select()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_set_slave_select
(
	mss_spi_instance_t * this_spi,
	mss_spi_slave_t slave
)
{
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    /* This function is only intended to be used with an SPI master. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_MASTER );
    ASSERT( this_spi->slaves_cfg[slave].ctrl_reg != NOT_CONFIGURED );

    /* Set the clock rate. */
    this_spi->hw_reg_bit->CTRL_ENABLE = 0U;
    this_spi->hw_reg->CONTROL = this_spi->slaves_cfg[slave].ctrl_reg;
    this_spi->hw_reg->CLK_GEN = this_spi->slaves_cfg[slave].clk_gen;
    this_spi->hw_reg->TXRXDF_SIZE = this_spi->slaves_cfg[slave].txrxdf_size_reg;
    this_spi->hw_reg_bit->CTRL_ENABLE = 1U;
    
    /* Set slave select */
    this_spi->hw_reg->SLAVE_SELECT |= ((uint32_t)1 << (uint32_t)slave);
}

/***************************************************************************//**
 * MSS_SPI_clear_slave_select()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_clear_slave_select
(
	mss_spi_instance_t * this_spi,
	mss_spi_slave_t slave
)
{
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    /* This function is only intended to be used with an SPI master. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_MASTER );

    this_spi->hw_reg->SLAVE_SELECT &= ~((uint32_t)1 << (uint32_t)slave);
}

/***************************************************************************//**
 * MSS_SPI_transfer_frame()
 * See "mss_spi.h" for details of how to use this function.
 */
uint32_t MSS_SPI_transfer_frame
(
    mss_spi_instance_t * this_spi,
    uint32_t tx_bits
)
{
    volatile uint32_t dummy;
    
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    /* This function is only intended to be used with an SPI master. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_MASTER );
    
    /* Flush Rx FIFO. */
    while ( this_spi->hw_reg_bit->STATUS_RX_RDY == 1U )
    {
        dummy = this_spi->hw_reg->RX_DATA;
        dummy = dummy;  /* Prevent Lint warning. */
    }
    
    /* Send frame. */
    this_spi->hw_reg->TX_DATA = tx_bits;
    
    /* Wait for frame Tx to complete. */
    while ( this_spi->hw_reg_bit->STATUS_TX_DONE == 0U )
    {
        ;
    }
    
    /* Read received frame. */
    /* Wait for Rx complete. */
    while ( this_spi->hw_reg_bit->STATUS_RX_RDY == 0U )
    {
        ;
    }
    /* Return Rx data. */
    return( this_spi->hw_reg->RX_DATA );
}


/***************************************************************************//**
 * MSS_SPI_transfer_block()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_transfer_block
(
    mss_spi_instance_t * this_spi,
    const uint8_t * cmd_buffer,
    uint16_t cmd_byte_size,
    uint8_t * rd_buffer,
    uint16_t rd_byte_size
)
{
    uint16_t transfer_idx = 0U;
    uint16_t tx_idx;
    uint16_t rx_idx;
    uint32_t frame_count;
    volatile uint32_t rx_raw;
    uint16_t transit = 0U;
    
    uint16_t transfer_size;     /* Total number of bytes transfered. */
    
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    /* This function is only intended to be used with an SPI master. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_MASTER );
    
    /* Compute number of bytes to transfer. */
    transfer_size = cmd_byte_size + rd_byte_size;
    
    /* Adjust to 1 byte transfer to cater for DMA transfers. */
    if ( transfer_size == 0U )
    {
        frame_count = 1U;
    }
    else
    {
        frame_count = transfer_size;
    }
    
    /* Set frame size to 8 bits and the frame count to the tansfer size. */
    this_spi->hw_reg_bit->CTRL_ENABLE = 0U;
    this_spi->hw_reg->CONTROL = (this_spi->hw_reg->CONTROL & ~TXRXDFCOUNT_MASK) | ( (frame_count << TXRXDFCOUNT_SHIFT) & TXRXDFCOUNT_MASK);
    this_spi->hw_reg->TXRXDF_SIZE = 8U;
    this_spi->hw_reg_bit->CTRL_ENABLE = 1U;

    /* Flush the receive FIFO. */
    while ( !this_spi->hw_reg_bit->STATUS_RX_FIFO_EMPTY )
    {
        rx_raw = this_spi->hw_reg->RX_DATA;
    }
    
    tx_idx = 0u;
    rx_idx = 0u;
    if ( tx_idx < cmd_byte_size )
    {
        this_spi->hw_reg->TX_DATA = cmd_buffer[tx_idx];
        ++tx_idx;
        ++transit;
    }
    else
    {
        if ( tx_idx < transfer_size )
        {
            this_spi->hw_reg->TX_DATA = 0x00U;
            ++tx_idx;
            ++transit;
        }
    }
    /* Perform the remainder of the transfer by sending a byte every time a byte
     * has been received. This should ensure that no Rx overflow can happen in
     * case of an interrupt occurs during this function. */
    while ( transfer_idx < transfer_size )
    {
        if ( !this_spi->hw_reg_bit->STATUS_RX_FIFO_EMPTY )
        {
            /* Process received byte. */
            rx_raw = this_spi->hw_reg->RX_DATA;
            if ( transfer_idx >= cmd_byte_size )
            {
                if ( rx_idx < rd_byte_size )
                {
                    rd_buffer[rx_idx] = (uint8_t)rx_raw;   
                }
                ++rx_idx;
            }
            ++transfer_idx;
            --transit;
        }

        if ( !this_spi->hw_reg_bit->STATUS_TX_FIFO_FULL )
        {
            if (transit < RX_FIFO_SIZE)
            {
                /* Send another byte. */
                if ( tx_idx < cmd_byte_size )
                {
                    this_spi->hw_reg->TX_DATA = cmd_buffer[tx_idx];
                    ++tx_idx;
                    ++transit;
                }
                else
                {
                    if ( tx_idx < transfer_size )
                    {
                        this_spi->hw_reg->TX_DATA = 0x00U;
                        ++tx_idx;
                        ++transit;
                    }
                }
            }
        }
    }
}

/***************************************************************************//**
 * MSS_SPI_set_frame_rx_handler()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_set_frame_rx_handler
(
    mss_spi_instance_t * this_spi,
    mss_spi_frame_rx_handler_t rx_handler
)
{
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    /* This function is only intended to be used with an SPI slave. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_SLAVE );
    
    /* Disable block Rx handler as they are mutually exclusive. */
    this_spi->block_rx_handler = 0U;
    
    /* Keep a copy of the pointer to the rx hnadler function. */
    this_spi->frame_rx_handler = rx_handler;
    
    /* Enable Rx interrupt. */
    this_spi->hw_reg_bit->CTRL_RX_INT_EN = 1U;
    NVIC_EnableIRQ( this_spi->irqn );
}

/***************************************************************************//**
 * MSS_SPI_set_slave_tx_frame()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_set_slave_tx_frame
(
    mss_spi_instance_t * this_spi,
    uint32_t frame_value
)
{
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );

    /* This function is only intended to be used with an SPI slave. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_SLAVE );
    
    /* Disable slave block tx buffer as it is mutually exclusive with frame
     * level handling. */    
    this_spi->slave_tx_buffer = 0U;
    this_spi->slave_tx_size = 0U;
    this_spi->slave_tx_idx = 0U;
    
    /* Keep a copy of the slave tx frame value. */
    this_spi->slave_tx_frame = frame_value;
    
    /* Load frame into Tx data register. */
    this_spi->hw_reg->TX_DATA = this_spi->slave_tx_frame;
    
    /* Enable Tx Done interrupt in order to reload the slave Tx frame after each
     * time it has been sent. */
    this_spi->hw_reg_bit->CTRL_TX_INT_EN = 1U;
    NVIC_EnableIRQ( this_spi->irqn );
}

/***************************************************************************//**
 * MSS_SPI_set_slave_block_buffers()
 * See "mss_spi.h" for details of how to use this function.
 */
void MSS_SPI_set_slave_block_buffers
(
    mss_spi_instance_t * this_spi,
    const uint8_t * tx_buffer,
    uint32_t tx_buff_size,
    uint8_t * rx_buffer,
    uint32_t rx_buff_size,
    mss_spi_block_rx_handler_t block_rx_handler
)
{
    uint32_t frame_count;
    
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    /* This function is only intended to be used with an SPI slave. */
    ASSERT( this_spi->hw_reg_bit->CTRL_MASTER == MSS_SPI_MODE_SLAVE );
    
    /* Disable Rx frame handler as it is mutually exclusive with block rx handler. */
    this_spi->frame_rx_handler = 0U;
    
    /* Keep a copy of the pointer to the block rx handler function. */
    this_spi->block_rx_handler = block_rx_handler;
    
    this_spi->slave_rx_buffer = rx_buffer;
    this_spi->slave_rx_size = rx_buff_size;
    this_spi->slave_rx_idx = 0U;
    
    /**/
    this_spi->slave_tx_buffer = tx_buffer;
    this_spi->slave_tx_size = tx_buff_size;
    this_spi->slave_tx_idx = 0U;

    frame_count = rx_buff_size;
    
    /**/
    this_spi->hw_reg_bit->CTRL_ENABLE = 0U;
    this_spi->hw_reg->CONTROL = (this_spi->hw_reg->CONTROL & ~TXRXDFCOUNT_MASK) | (frame_count << TXRXDFCOUNT_SHIFT);
    this_spi->hw_reg->TXRXDF_SIZE = 8U;
    this_spi->hw_reg_bit->CTRL_ENABLE = 1U;
    
    /* Load the transmit FIFO. */
    while ( !(this_spi->hw_reg_bit->STATUS_TX_FIFO_FULL) && ( this_spi->slave_tx_idx < this_spi->slave_tx_size ) )
    {
        this_spi->hw_reg->TX_DATA = this_spi->slave_tx_buffer[this_spi->slave_tx_idx];
        ++this_spi->slave_tx_idx;
    }
    
    /* Enable Rx interrupt. */
    this_spi->hw_reg_bit->CTRL_RX_INT_EN = 1U;
    NVIC_EnableIRQ( this_spi->irqn );
}

/***************************************************************************//**
 * SPI interrupt service routine.
 */
static void mss_spi_isr
(
    mss_spi_instance_t * this_spi
)
{
    uint32_t rx_frame;
    
    ASSERT( (this_spi == &g_mss_spi0) || (this_spi == &g_mss_spi1) );
    
    if ( this_spi->hw_reg_bit->MIS_RX_RDY )
    {
        while( !this_spi->hw_reg_bit->STATUS_RX_FIFO_EMPTY )
        {
            rx_frame = this_spi->hw_reg->RX_DATA;
            if ( this_spi->frame_rx_handler != 0U )
            {
                /* Single frame handling mode. */
                this_spi->frame_rx_handler( rx_frame );
            }
            else 
            {
                if ( this_spi->block_rx_handler != 0U )
                {
                    /* Block handling mode. */
                    if ( this_spi->slave_rx_idx < this_spi->slave_rx_size )
                    {
                        this_spi->slave_rx_buffer[this_spi->slave_rx_idx] = (uint8_t)rx_frame;
                        ++this_spi->slave_rx_idx;
                        if ( this_spi->slave_rx_idx == this_spi->slave_rx_size )
                        {
                            (*this_spi->block_rx_handler)( this_spi->slave_rx_buffer, this_spi->slave_rx_size );
                        }
                    }
                }
            }
            
            /* Feed transmit FIFO. */
            if ( !(this_spi->hw_reg_bit->STATUS_TX_FIFO_FULL) && ( this_spi->slave_tx_idx < this_spi->slave_tx_size ) )
            {
                this_spi->hw_reg->TX_DATA = this_spi->slave_tx_buffer[this_spi->slave_tx_idx];
                ++this_spi->slave_tx_idx;
            }
        }
        this_spi->hw_reg_bit->INT_CLEAR_RX_RDY = 1U;
    }
    
    if ( this_spi->hw_reg_bit->MIS_TX_DONE )
    {
        if ( this_spi->slave_tx_buffer != 0U )
        {
            this_spi->hw_reg->TX_DATA = this_spi->slave_tx_buffer[this_spi->slave_tx_idx];
            ++this_spi->slave_tx_idx;
            if ( this_spi->slave_tx_idx >= this_spi->slave_tx_size )
            {
                this_spi->slave_tx_idx = 0U;
            }
        }
        else
        {
            /* Reload slave tx frame into Tx data register. */
            this_spi->hw_reg->TX_DATA = this_spi->slave_tx_frame;
        }
    }
}

/***************************************************************************//**
 * SPIO interrupt service routine.
 * Please note that the name of this ISR is defined as part of the SmartFusion
 * CMSIS startup code.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void SPI0_IRQHandler( void )
#else
void SPI0_IRQHandler( void )
#endif
{
    mss_spi_isr( &g_mss_spi0 );
    NVIC_ClearPendingIRQ( SPI0_IRQn );
}

/***************************************************************************//**
 * SPI1 interrupt service routine.
 * Please note that the name of this ISR is defined as part of the SmartFusion
 * CMSIS startup code.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void SPI1_IRQHandler( void )
#else
void SPI1_IRQHandler( void )
#endif
{
    mss_spi_isr( &g_mss_spi1 );
    NVIC_ClearPendingIRQ( SPI1_IRQn );
}

#ifdef __cplusplus
}
#endif

