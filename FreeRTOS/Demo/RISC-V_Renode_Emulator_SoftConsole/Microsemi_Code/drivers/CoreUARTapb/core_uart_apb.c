/*******************************************************************************
 * (c) Copyright 2007-2017 Microsemi SoC Products Group. All rights reserved.
 * 
 * CoreUARTapb driver implementation. See file "core_uart_apb.h" for a
 * description of the functions implemented in this file.
 * 
 * SVN $Revision: 9082 $
 * SVN $Date: 2017-04-28 11:51:36 +0530 (Fri, 28 Apr 2017) $
 */
#include "hal.h"
#include "coreuartapb_regs.h"
#include "core_uart_apb.h"
#include "hal_assert.h"

#ifdef __cplusplus
extern "C" {
#endif

#define NULL_INSTANCE ( ( UART_instance_t* ) 0 )
#define NULL_BUFFER   ( ( uint8_t* ) 0 )

#define MAX_LINE_CONFIG     ( ( uint8_t )( DATA_8_BITS | ODD_PARITY ) )
#define MAX_BAUD_VALUE      ( ( uint16_t )( 0x1FFF ) )
#define STATUS_ERROR_MASK   ( ( uint8_t )( STATUS_PARITYERR_MASK | \
                                           STATUS_OVERFLOW_MASK  | \
                                           STATUS_FRAMERR_MASK ) )
#define BAUDVALUE_LSB ( (uint16_t) (0x00FF) )
#define BAUDVALUE_MSB ( (uint16_t) (0xFF00) )
#define BAUDVALUE_SHIFT ( (uint8_t) (5) )

#define STATUS_ERROR_OFFSET STATUS_PARITYERR_SHIFT 

/***************************************************************************//**
 * UART_init()
 * See "core_uart_apb.h" for details of how to use this function.
 */
void
UART_init
(
    UART_instance_t * this_uart,
    addr_t base_addr,
    uint16_t baud_value,
    uint8_t line_config
)
{
    uint8_t rx_full;
    
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( line_config <= MAX_LINE_CONFIG )
    HAL_ASSERT( baud_value <= MAX_BAUD_VALUE )

    if( ( this_uart != NULL_INSTANCE ) &&
        ( line_config <= MAX_LINE_CONFIG ) &&
        ( baud_value <= MAX_BAUD_VALUE ) )
    {
        /*
         * Store lower 8-bits of baud value in CTRL1.
         */
        HAL_set_8bit_reg( base_addr, CTRL1, (uint_fast8_t)(baud_value &
                                                       BAUDVALUE_LSB ) );
    
        /*
         * Extract higher 5-bits of baud value and store in higher 5-bits 
         * of CTRL2, along with line configuration in lower 3 three bits.
         */
        HAL_set_8bit_reg( base_addr, CTRL2, (uint_fast8_t)line_config | 
                                           (uint_fast8_t)((baud_value &
                                   BAUDVALUE_MSB) >> BAUDVALUE_SHIFT ) );
    
        this_uart->base_address = base_addr;
#ifndef NDEBUG
        {
            uint8_t  config;
            uint8_t  temp;
            uint16_t baud_val;
            baud_val = HAL_get_8bit_reg( this_uart->base_address, CTRL1 );
            config =  HAL_get_8bit_reg( this_uart->base_address, CTRL2 );
            /*
             * To resolve operator precedence between & and <<
             */
            temp =  ( config  &  (uint8_t)(CTRL2_BAUDVALUE_MASK ) );
            baud_val |= (uint16_t)( (uint16_t)(temp) << BAUDVALUE_SHIFT );
            config &= (uint8_t)(~CTRL2_BAUDVALUE_MASK);
            HAL_ASSERT( baud_val == baud_value );
            HAL_ASSERT( config == line_config );
        }        
#endif
        
        /*
         * Flush the receive FIFO of data that may have been received before the
         * driver was initialized.
         */
        rx_full = HAL_get_8bit_reg( this_uart->base_address, STATUS ) &
                                                    STATUS_RXFULL_MASK;
        while ( rx_full )
        {
            HAL_get_8bit_reg( this_uart->base_address, RXDATA );
            rx_full = HAL_get_8bit_reg( this_uart->base_address, STATUS ) &
                                                        STATUS_RXFULL_MASK;
        }

        /*
         * Clear status of the UART instance.
         */
        this_uart->status = (uint8_t)0;
    }
}

/***************************************************************************//**
 * UART_send()
 * See "core_uart_apb.h" for details of how to use this function.
 */
void
UART_send
(
    UART_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
)
{
    size_t char_idx;
    uint8_t tx_ready;

    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( tx_buffer != NULL_BUFFER )
    HAL_ASSERT( tx_size > 0 )
      
    if( (this_uart != NULL_INSTANCE) &&
        (tx_buffer != NULL_BUFFER)   &&
        (tx_size > (size_t)0) )
    {
        for ( char_idx = (size_t)0; char_idx < tx_size; char_idx++ )
        {
            /* Wait for UART to become ready to transmit. */
            do {
                tx_ready = HAL_get_8bit_reg( this_uart->base_address, STATUS ) &
                                                              STATUS_TXRDY_MASK;
            } while ( !tx_ready );
            /* Send next character in the buffer. */
            HAL_set_8bit_reg( this_uart->base_address, TXDATA,
                              (uint_fast8_t)tx_buffer[char_idx] );
        }
    }
}

/***************************************************************************//**
 * UART_fill_tx_fifo()
 * See "core_uart_apb.h" for details of how to use this function.
 */
size_t
UART_fill_tx_fifo
(
    UART_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
)
{
    uint8_t tx_ready;
    size_t size_sent = 0u;
    
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( tx_buffer != NULL_BUFFER )
    HAL_ASSERT( tx_size > 0 )
      
    /* Fill the UART's Tx FIFO until the FIFO is full or the complete input 
     * buffer has been written. */
    if( (this_uart != NULL_INSTANCE) &&
        (tx_buffer != NULL_BUFFER)   &&
        (tx_size > 0u) )
    {
        tx_ready = HAL_get_8bit_reg( this_uart->base_address, STATUS ) &
                                                      STATUS_TXRDY_MASK;
        if ( tx_ready )
        {
            do {
                HAL_set_8bit_reg( this_uart->base_address, TXDATA,
                                  (uint_fast8_t)tx_buffer[size_sent] );
                size_sent++;
                tx_ready = HAL_get_8bit_reg( this_uart->base_address, STATUS ) &
                                                              STATUS_TXRDY_MASK;
            } while ( (tx_ready) && ( size_sent < tx_size ) );
        }
    }    
    return size_sent;
}

/***************************************************************************//**
 * UART_get_rx()
 * See "core_uart_apb.h" for details of how to use this function.
 */
size_t
UART_get_rx
(
    UART_instance_t * this_uart,
    uint8_t * rx_buffer,
    size_t buff_size
)
{
    uint8_t new_status;
    uint8_t rx_full;
    size_t rx_idx = 0u;
    
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( rx_buffer != NULL_BUFFER )
    HAL_ASSERT( buff_size > 0 )
      
    if( (this_uart != NULL_INSTANCE) &&
        (rx_buffer != NULL_BUFFER)   &&
        (buff_size > 0u) )
    {
        rx_idx = 0u;
        new_status = HAL_get_8bit_reg( this_uart->base_address, STATUS );
        this_uart->status |= new_status;
        rx_full = new_status & STATUS_RXFULL_MASK;
        while ( ( rx_full ) && ( rx_idx < buff_size ) )
        {
            rx_buffer[rx_idx] = HAL_get_8bit_reg( this_uart->base_address,
                                                  RXDATA );
            rx_idx++;
            new_status = HAL_get_8bit_reg( this_uart->base_address, STATUS );
            this_uart->status |= new_status;
            rx_full = new_status & STATUS_RXFULL_MASK;
        }
    }
    return rx_idx;
}

/***************************************************************************//**
 * UART_polled_tx_string()
 * See "core_uart_apb.h" for details of how to use this function.
 */
void 
UART_polled_tx_string
( 
    UART_instance_t * this_uart, 
    const uint8_t * p_sz_string
)
{
    uint32_t char_idx;
    uint8_t tx_ready;

    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( p_sz_string != NULL_BUFFER )
    
    if( ( this_uart != NULL_INSTANCE ) && ( p_sz_string != NULL_BUFFER ) )
    {
        char_idx = 0U;
        while( 0U != p_sz_string[char_idx] )
        {
            /* Wait for UART to become ready to transmit. */
            do {
                tx_ready = HAL_get_8bit_reg( this_uart->base_address, STATUS ) &
                                                              STATUS_TXRDY_MASK;
            } while ( !tx_ready );
            /* Send next character in the buffer. */
            HAL_set_8bit_reg( this_uart->base_address, TXDATA,
                              (uint_fast8_t)p_sz_string[char_idx] );
            char_idx++;
        }
    }
}

/***************************************************************************//**
 * UART_get_rx_status()
 * See "core_uart_apb.h" for details of how to use this function.
 */
uint8_t
UART_get_rx_status
(
    UART_instance_t * this_uart
)
{
    uint8_t status = UART_APB_INVALID_PARAM;

    HAL_ASSERT( this_uart != NULL_INSTANCE )
    /*
     * Extract UART error status and place in lower bits of "status".
     * Bit 0 - Parity error status
     * Bit 1 - Overflow error status
     * Bit 2 - Frame error status
     */
    if( this_uart != NULL_INSTANCE )
    {
        status = ( ( this_uart->status & STATUS_ERROR_MASK ) >> 
                                          STATUS_ERROR_OFFSET );
        /*
         * Clear the sticky status for this instance.
         */
        this_uart->status = (uint8_t)0;
    }
    return status;
}

#ifdef __cplusplus
}
#endif
