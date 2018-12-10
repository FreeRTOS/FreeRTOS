/*******************************************************************************
 * (c) Copyright 2007-2015 Microsemi SoC Products Group. All rights reserved.
 *
 * Core16550 driver implementation. See file "core_16550.h" for a
 * description of the functions implemented in this file.
 *
 * SVN $Revision: 7963 $
 * SVN $Date: 2015-10-09 17:58:21 +0530 (Fri, 09 Oct 2015) $
 */
#include "hal.h"
#include "core_16550.h"
#include "core16550_regs.h"
#include "hal_assert.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * Definitions for transmitter states
 */
#define TX_COMPLETE     0x00U

/*******************************************************************************
 * Definition for transmitter FIFO size
 */
#define TX_FIFO_SIZE    16U

/*******************************************************************************
 * Default receive interrupt trigger level
 */
#define DEFAULT_RX_TRIG_LEVEL  ((uint8_t)UART_16550_FIFO_SINGLE_BYTE)

/*******************************************************************************
 * Receiver error status mask and shift offset
 */
#define STATUS_ERROR_MASK   ( LSR_OE_MASK | LSR_PE_MASK |  \
                              LSR_FE_MASK | LSR_BI_MASK | LSR_FIER_MASK)

/*******************************************************************************
 * Definitions for invalid parameters with proper type
 */
#define INVALID_INTERRUPT   0U
#define INVALID_IRQ_HANDLER ( (uart_16550_irq_handler_t) 0 )

/*******************************************************************************
 * Possible values for Interrupt Identification Register Field.
 */
#define IIRF_MODEM_STATUS       0x00U
#define IIRF_THRE               0x02U
#define IIRF_RX_DATA            0x04U
#define IIRF_RX_LINE_STATUS     0x06U
#define IIRF_DATA_TIMEOUT       0x0CU

/*******************************************************************************
 * Null parameters with appropriate type definitions
 */
#define NULL_ADDR       ( ( addr_t ) 0 )
#define NULL_INSTANCE   ( ( uart_16550_instance_t * ) 0 )
#define NULL_BUFF       ( ( uint8_t * ) 0 )

/*******************************************************************************
 * Possible states for different register bit fields
 */
enum {
    DISABLE = 0U,
    ENABLE  = 1U
};

/*******************************************************************************
 * Static function declarations
 */
static void default_tx_handler(uart_16550_instance_t * this_uart);

/*******************************************************************************
 * Public function definitions
 */

/***************************************************************************//**
 * UART_16550_init.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_init
(
    uart_16550_instance_t* this_uart,
    addr_t base_addr,
    uint16_t baud_value,
    uint8_t line_config
)
{
#ifndef NDEBUG
    uint8_t dbg1;
    uint8_t dbg2;
#endif
    uint8_t fifo_config;
    uint8_t temp;

    HAL_ASSERT( base_addr != NULL_ADDR );
    HAL_ASSERT( this_uart != NULL_INSTANCE );

    if( ( base_addr != NULL_ADDR ) && ( this_uart != NULL_INSTANCE ) )
    {
        /* disable interrupts */
        HAL_set_8bit_reg(base_addr, IER, DISABLE);

        /* reset divisor latch */
        HAL_set_8bit_reg_field(base_addr, LCR_DLAB, ENABLE);
#ifndef NDEBUG
        dbg1 =  HAL_get_8bit_reg_field(base_addr, LCR_DLAB );
        HAL_ASSERT( dbg1 == ENABLE );
#endif
        /* MSB of baud value */
        temp = (uint8_t)(baud_value >> 8);
        HAL_set_8bit_reg(base_addr, DMR, temp );
        /* LSB of baud value */
        HAL_set_8bit_reg(base_addr, DLR, ( (uint8_t)baud_value ) );
#ifndef NDEBUG
        dbg1 =  HAL_get_8bit_reg(base_addr, DMR );
        dbg2 =  HAL_get_8bit_reg(base_addr, DLR );
        HAL_ASSERT( ( ( ( (uint16_t) dbg1 ) << 8 ) | dbg2 ) == baud_value );
#endif
        /* reset divisor latch */
        HAL_set_8bit_reg_field(base_addr, LCR_DLAB, DISABLE);
#ifndef NDEBUG
        dbg1 =  HAL_get_8bit_reg_field(base_addr, LCR_DLAB );
        HAL_ASSERT( dbg1 == DISABLE );
#endif
        /* set the line control register (bit length, stop bits, parity) */
        HAL_set_8bit_reg( base_addr, LCR, line_config );
#ifndef NDEBUG
        dbg1 =  HAL_get_8bit_reg(base_addr, LCR );
        HAL_ASSERT( dbg1 == line_config)
#endif
        /* Enable and configure the RX and TX FIFOs. */
        fifo_config = ((uint8_t)(DEFAULT_RX_TRIG_LEVEL << FCR_TRIG_LEVEL_SHIFT) |
                                 FCR_RDYN_EN_MASK | FCR_CLEAR_RX_MASK |
                                 FCR_CLEAR_TX_MASK | FCR_ENABLE_MASK );
        HAL_set_8bit_reg( base_addr, FCR, fifo_config );

        /* disable loopback */
        HAL_set_8bit_reg_field( base_addr, MCR_LOOP, DISABLE );
#ifndef NDEBUG
        dbg1 =  HAL_get_8bit_reg_field(base_addr, MCR_LOOP);
        HAL_ASSERT( dbg1 == DISABLE );
#endif

        /* Instance setup */
        this_uart->base_address = base_addr;
        this_uart->tx_buffer    = NULL_BUFF;
        this_uart->tx_buff_size = TX_COMPLETE;
        this_uart->tx_idx       = 0U;
        this_uart->tx_handler   = default_tx_handler;

        this_uart->rx_handler  = ( (uart_16550_irq_handler_t) 0 );
        this_uart->linests_handler  = ( (uart_16550_irq_handler_t) 0 );
        this_uart->modemsts_handler = ( (uart_16550_irq_handler_t) 0 );
        this_uart->status = 0U;
    }
}

/***************************************************************************//**
 * UART_16550_polled_tx.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_polled_tx
(
    uart_16550_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
)
{
    uint32_t char_idx = 0U;
    uint32_t size_sent;
    uint8_t status;

    HAL_ASSERT( this_uart != NULL_INSTANCE );
    HAL_ASSERT( pbuff != NULL_BUFF );
    HAL_ASSERT( tx_size > 0U );

    if( ( this_uart != NULL_INSTANCE ) &&
        ( pbuff != NULL_BUFF ) &&
        ( tx_size > 0U ) )
    {
        /* Remain in this loop until the entire input buffer
         * has been transferred to the UART.
         */
        do {
            /* Read the Line Status Register and update the sticky record */
            status = HAL_get_8bit_reg( this_uart->base_address, LSR );
            this_uart->status |= status;

            /* Check if TX FIFO is empty. */
            if( status & LSR_THRE_MASK )
            {
                uint32_t fill_size = TX_FIFO_SIZE;

                /* Calculate the number of bytes to transmit. */
                if ( tx_size < TX_FIFO_SIZE )
                {
                    fill_size = tx_size;
                }

                /* Fill the TX FIFO with the calculated the number of bytes. */
                for ( size_sent = 0U; size_sent < fill_size; ++size_sent )
                {
                    /* Send next character in the buffer. */
                    HAL_set_8bit_reg( this_uart->base_address, THR,
                                      (uint_fast8_t)pbuff[char_idx++]);
                }

                /* Calculate the number of untransmitted bytes remaining. */
                tx_size -= size_sent;
            }
        } while ( tx_size );
    }
}

/***************************************************************************//**
 * UART_16550_polled_tx_string.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_polled_tx_string
(
    uart_16550_instance_t * this_uart,
    const uint8_t * p_sz_string
)
{
    uint32_t char_idx = 0U;
    uint32_t fill_size;
    uint_fast8_t data_byte;
    uint8_t status;

    HAL_ASSERT( this_uart != NULL_INSTANCE );
    HAL_ASSERT( p_sz_string != NULL_BUFF );

    if( ( this_uart != NULL_INSTANCE ) && ( p_sz_string != NULL_BUFF ) )
    {
        char_idx = 0U;

        /* Get the first data byte from the input buffer */
        data_byte = (uint_fast8_t)p_sz_string[char_idx];

        /* First check for the NULL terminator byte.
         * Then remain in this loop until the entire string in the input buffer
         * has been transferred to the UART.
         */
        while ( 0U != data_byte )
        {
            /* Wait until TX FIFO is empty. */
            do {
                status = HAL_get_8bit_reg( this_uart->base_address,LSR);
                this_uart->status |= status;
            } while ( !( status & LSR_THRE_MASK ) );

            /* Send bytes from the input buffer until the TX FIFO is full
             * or we reach the NULL terminator byte.
             */
            fill_size = 0U;
            while ( (0U != data_byte) && (fill_size < TX_FIFO_SIZE) )
            {
                /* Send the data byte */
                HAL_set_8bit_reg( this_uart->base_address, THR, data_byte );
                ++fill_size;
                char_idx++;
                /* Get the next data byte from the input buffer */
                data_byte = (uint_fast8_t)p_sz_string[char_idx];
            }
        }
    }
}


/***************************************************************************//**
 * UART_16550_irq_tx.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_irq_tx
(
    uart_16550_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( pbuff != NULL_BUFF )
    HAL_ASSERT( tx_size > 0U )

    if( ( this_uart != NULL_INSTANCE ) &&
        ( pbuff != NULL_BUFF ) &&
        ( tx_size > 0U ) )
    {
        /*Initialize the UART instance with
          parameters required for transmission.*/
        this_uart->tx_buffer = pbuff;
        this_uart->tx_buff_size = tx_size;
        /* char_idx; */
        this_uart->tx_idx = 0U;
        /* assign handler for default data transmission */
        this_uart->tx_handler = default_tx_handler;

        /* enables TX interrupt */
        HAL_set_8bit_reg_field(this_uart->base_address, IER_ETBEI, ENABLE);
    }
}

/***************************************************************************//**
 * UART_16550_tx_complete.
 * See core_16550.h for details of how to use this function.
 */
int8_t
UART_16550_tx_complete
(
    uart_16550_instance_t * this_uart
)
{
    int8_t returnvalue = 0;
    uint8_t status = 0U;

    HAL_ASSERT( this_uart != NULL_INSTANCE )

    if( this_uart != NULL_INSTANCE )
    {
        status = HAL_get_8bit_reg(this_uart->base_address,LSR);
        this_uart->status |= status;

        if( ( this_uart->tx_buff_size == TX_COMPLETE ) &&
                             ( status & LSR_TEMT_MASK ) )
        {
            returnvalue = (int8_t)1;
        }
    }
    return returnvalue;
}


/***************************************************************************//**
 * UART_16550_get_rx.
 * See core_16550.h for details of how to use this function.
 */
size_t
UART_16550_get_rx
(
    uart_16550_instance_t * this_uart,
    uint8_t * rx_buff,
    size_t buff_size
)
{
    uint8_t status;
    size_t rx_size = 0U;

    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( rx_buff != (uint8_t *)0 )
    HAL_ASSERT( buff_size > 0U )

    if( ( this_uart != NULL_INSTANCE ) &&
        ( rx_buff != (uint8_t *)0 ) &&
        ( buff_size > 0U ) )
    {
        status = HAL_get_8bit_reg( this_uart->base_address, LSR );
        this_uart->status |= status;
        while ( ((status & LSR_DR_MASK) != 0U) && ( rx_size < buff_size ) )
        {
            rx_buff[rx_size] = HAL_get_8bit_reg( this_uart->base_address, RBR );
            rx_size++;
            status = HAL_get_8bit_reg( this_uart->base_address, LSR );
            this_uart->status |= status;
        }
    }
    return rx_size;
}

/***************************************************************************//**
 * UART_16550_isr.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_isr
(
    uart_16550_instance_t * this_uart
)
{
    uint8_t iirf;

    HAL_ASSERT( this_uart != NULL_INSTANCE )

    if(this_uart != NULL_INSTANCE )
    {
        iirf = HAL_get_8bit_reg_field( this_uart->base_address, IIR_IIR );

        switch ( iirf )
        {
            /* Modem status interrupt */
            case IIRF_MODEM_STATUS:
            {
                if( INVALID_IRQ_HANDLER != this_uart->modemsts_handler  )
                {
                    HAL_ASSERT( INVALID_IRQ_HANDLER != this_uart->modemsts_handler );
                    if( INVALID_IRQ_HANDLER != this_uart->modemsts_handler )
                    {
                        (*(this_uart->modemsts_handler))(this_uart);
                    }
                }
            }
            break;
            /* Transmitter Holding Register Empty interrupt */
            case IIRF_THRE:
            {
                HAL_ASSERT( INVALID_IRQ_HANDLER != this_uart->tx_handler );
                if ( INVALID_IRQ_HANDLER != this_uart->tx_handler )
                {
                    (*(this_uart->tx_handler))(this_uart);
                }
            }
            break;
            /* Received Data Available interrupt */
            case IIRF_RX_DATA:
            case IIRF_DATA_TIMEOUT:
            {
                HAL_ASSERT( INVALID_IRQ_HANDLER != this_uart->rx_handler );
                if ( INVALID_IRQ_HANDLER != this_uart->rx_handler )
                {
                    (*(this_uart->rx_handler))(this_uart);
                }
            }
            break;
            /* Line status interrupt */
            case IIRF_RX_LINE_STATUS:
            {
                HAL_ASSERT( INVALID_IRQ_HANDLER != this_uart->linests_handler );
                if ( INVALID_IRQ_HANDLER != this_uart->linests_handler )
                {
                    (*(this_uart->linests_handler))(this_uart);
                }
            }
            break;
            /* Unidentified interrupt */
            default:
            {
                HAL_ASSERT( INVALID_INTERRUPT )
            }
        }
    }
}

/***************************************************************************//**
 * UART_16550_set_rx_handler.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_set_rx_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler,
    uart_16550_rx_trig_level_t trigger_level
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( handler != INVALID_IRQ_HANDLER)
    HAL_ASSERT( trigger_level < UART_16550_FIFO_INVALID_TRIG_LEVEL)

    if( ( this_uart != NULL_INSTANCE ) &&
        ( handler != INVALID_IRQ_HANDLER) &&
        ( trigger_level < UART_16550_FIFO_INVALID_TRIG_LEVEL) )
    {
        this_uart->rx_handler = handler;

        /* Set the receive interrupt trigger level. */
        HAL_set_8bit_reg_field( this_uart->base_address,
                            FCR_TRIG_LEVEL, trigger_level );

        /* Enable receive interrupt. */
        HAL_set_8bit_reg_field( this_uart->base_address, IER_ERBFI, ENABLE );
    }
}

/***************************************************************************//**
 * UART_16550_set_loopback.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_set_loopback
(
    uart_16550_instance_t * this_uart,
    uart_16550_loopback_t loopback
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE );
    HAL_ASSERT( loopback < UART_16550_INVALID_LOOPBACK );

    if( ( this_uart != NULL_INSTANCE ) &&
        ( loopback < UART_16550_INVALID_LOOPBACK ) )
    {
        if ( loopback == UART_16550_LOOPBACK_OFF )
        {
            HAL_set_8bit_reg_field( this_uart->base_address,
                                    MCR_LOOP,
                                    DISABLE );
        }
        else
        {
            HAL_set_8bit_reg_field( this_uart->base_address,
                                    MCR_LOOP,
                                    ENABLE );
        }
    }
}

/***************************************************************************//**
 * UART_16550_get_rx_status.
 * See core_16550.h for details of how to use this function.
 */
uint8_t
UART_16550_get_rx_status
(
    uart_16550_instance_t * this_uart
)
{
    uint8_t status = UART_16550_INVALID_PARAM;
    HAL_ASSERT( this_uart != NULL_INSTANCE );

    if( ( this_uart != NULL_INSTANCE ) )
    {
        /*
         * Bit 1 - Overflow error status
         * Bit 2 - Parity error status
         * Bit 3 - Frame error status
         * Bit 4 - Break interrupt indicator
         * Bit 7 - FIFO data error status
         */
        this_uart->status |= HAL_get_8bit_reg( this_uart->base_address, LSR );
        status = ( this_uart->status & STATUS_ERROR_MASK );
        /*
         * Clear the sticky status for this instance.
         */
        this_uart->status = (uint8_t)0;
    }
    return status;
}

/***************************************************************************//**
 * UART_16550_get_modem_status.
 * See core_16550.h for details of how to use this function.
 */
uint8_t
UART_16550_get_modem_status
(
    uart_16550_instance_t * this_uart
)
{
    uint8_t status = UART_16550_NO_ERROR;
    HAL_ASSERT( this_uart != NULL_INSTANCE )

    if( ( this_uart != NULL_INSTANCE ) )
    {
        /*
         * Extract UART error status and place in lower bits of "status".
         * Bit 0 - Delta Clear to Send Indicator
         * Bit 1 - Delta Clear to Receive Indicator
         * Bit 2 - Trailing edge of Ring Indicator detector
         * Bit 3 - Delta Data Carrier Detect indicator
         * Bit 4 - Clear To Send
         * Bit 5 - Data Set Ready
         * Bit 6 - Ring Indicator
         * Bit 7 - Data Carrier Detect
         */
        status = HAL_get_8bit_reg( this_uart->base_address, MSR );
    }
    return status;
}

/***************************************************************************//**
 * Default TX interrupt handler to automatically transmit data from
 * user assgined TX buffer.
 */
static void
default_tx_handler
(
    uart_16550_instance_t * this_uart
)
{
    uint8_t status;

    HAL_ASSERT( NULL_INSTANCE != this_uart )

    if ( this_uart != NULL_INSTANCE )
    {
        HAL_ASSERT( NULL_BUFF != this_uart->tx_buffer )
        HAL_ASSERT( 0U != this_uart->tx_buff_size )

        if ( ( this_uart->tx_buffer != NULL_BUFF ) &&
             ( 0U != this_uart->tx_buff_size ) )
        {
            /* Read the Line Status Register and update the sticky record. */
            status = HAL_get_8bit_reg( this_uart->base_address,LSR);
            this_uart->status |= status;
    
            /*
             * This function should only be called as a result of a THRE interrupt.
             * Verify that this is true before proceeding to transmit data.
             */
            if ( status & LSR_THRE_MASK )
            {
                uint32_t size_sent = 0U;
                uint32_t fill_size = TX_FIFO_SIZE;
                uint32_t tx_remain = this_uart->tx_buff_size - this_uart->tx_idx;
    
                /* Calculate the number of bytes to transmit. */
                if ( tx_remain < TX_FIFO_SIZE )
                {
                    fill_size = tx_remain;
                }
    
                /* Fill the TX FIFO with the calculated the number of bytes. */
                for ( size_sent = 0U; size_sent < fill_size; ++size_sent )
                {
                    /* Send next character in the buffer. */
                    HAL_set_8bit_reg( this_uart->base_address, THR,
                            (uint_fast8_t)this_uart->tx_buffer[this_uart->tx_idx]);
                    ++this_uart->tx_idx;
                }
            }
    
            /* Flag Tx as complete if all data has been pushed into the Tx FIFO. */
            if ( this_uart->tx_idx == this_uart->tx_buff_size )
            {
                this_uart->tx_buff_size = TX_COMPLETE;
                /* disables TX interrupt */
                HAL_set_8bit_reg_field( this_uart->base_address,
                                        IER_ETBEI, DISABLE);
            }
        }
    }
}

/***************************************************************************//**
 * UART_16550_enable_irq.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_enable_irq
(
    uart_16550_instance_t * this_uart,
    uint8_t irq_mask
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )

    if( this_uart != NULL_INSTANCE )
    {
        /* irq_mask encoding: 1- enable
         * bit 0 - Receive Data Available Interrupt
         * bit 1 - Transmitter Holding  Register Empty Interrupt
         * bit 2 - Receiver Line Status Interrupt
         * bit 3 - Modem Status Interrupt
         */
        /* read present interrupts for enabled ones*/
        irq_mask |= HAL_get_8bit_reg( this_uart->base_address, IER );
        /* Enable interrupts */
        HAL_set_8bit_reg( this_uart->base_address, IER, irq_mask );
    }
}

/***************************************************************************//**
 * UART_16550_disable_irq.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_disable_irq
(
    uart_16550_instance_t * this_uart,
    uint8_t irq_mask
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )

    if( this_uart != NULL_INSTANCE )
    {
        /* irq_mask encoding:  1 - disable
         * bit 0 - Receive Data Available Interrupt
         * bit 1 - Transmitter Holding  Register Empty Interrupt
         * bit 2 - Receiver Line Status Interrupt
         * bit 3 - Modem Status Interrupt
         */
        /* read present interrupts for enabled ones */
        irq_mask = (( (uint8_t)~irq_mask ) & 
                    HAL_get_8bit_reg( this_uart->base_address, IER ));
        /* Disable interrupts */
        HAL_set_8bit_reg( this_uart->base_address, IER, irq_mask );
    }
}

/***************************************************************************//**
 * UART_16550_set_rxstatus_handler.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_set_rxstatus_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( handler != INVALID_IRQ_HANDLER)

    if( ( this_uart != NULL_INSTANCE ) &&
        ( handler != INVALID_IRQ_HANDLER) )
    {
        this_uart->linests_handler = handler;
        /* Enable receiver line status interrupt. */
        HAL_set_8bit_reg_field( this_uart->base_address, IER_ELSI, ENABLE );
    }
}

/***************************************************************************//**
 * UART_16550_set_tx_handler.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_set_tx_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( handler != INVALID_IRQ_HANDLER)

    if( ( this_uart != NULL_INSTANCE ) &&
        ( handler != INVALID_IRQ_HANDLER) )
    {
        this_uart->tx_handler = handler;

        /* Make TX buffer info invalid */
        this_uart->tx_buffer = NULL_BUFF;
        this_uart->tx_buff_size = 0U;

        /* Enable transmitter holding register Empty interrupt. */
        HAL_set_8bit_reg_field( this_uart->base_address, IER_ETBEI, ENABLE );
    }
}

/***************************************************************************//**
 * UART_16550_set_modemstatus_handler.
 * See core_16550.h for details of how to use this function.
 */
void
UART_16550_set_modemstatus_handler
(
    uart_16550_instance_t * this_uart,
    uart_16550_irq_handler_t handler
)
{
    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( handler != INVALID_IRQ_HANDLER)

    if( ( this_uart != NULL_INSTANCE ) &&
        ( handler != INVALID_IRQ_HANDLER) )
    {
        this_uart->modemsts_handler = handler;
        /* Enable modem status interrupt. */
        HAL_set_8bit_reg_field( this_uart->base_address, IER_EDSSI, ENABLE );
    }
}

/***************************************************************************//**
 * UART_16550_fill_tx_fifo.
 * See core_16550.h for details of how to use this function.
 */
size_t
UART_16550_fill_tx_fifo
(
    uart_16550_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
)
{
    uint8_t status;
    size_t size_sent = 0U;

    HAL_ASSERT( this_uart != NULL_INSTANCE )
    HAL_ASSERT( tx_buffer != NULL_BUFF )
    HAL_ASSERT( tx_size > 0U )

    /* Fill the UART's Tx FIFO until the FIFO is full or the complete input
     * buffer has been written. */
    if( (this_uart != NULL_INSTANCE) &&
        (tx_buffer != NULL_BUFF)   &&
        (tx_size > 0U) )
    {
        /* Read the Line Status Register and update the sticky record. */
        status = HAL_get_8bit_reg( this_uart->base_address, LSR );
        this_uart->status |= status;

        /* Check if TX FIFO is empty. */
        if( status & LSR_THRE_MASK )
        {
            uint32_t fill_size = TX_FIFO_SIZE;

            /* Calculate the number of bytes to transmit. */
            if ( tx_size < TX_FIFO_SIZE )
            {
                fill_size = tx_size;
            }

            /* Fill the TX FIFO with the calculated the number of bytes. */
            for ( size_sent = 0U; size_sent < fill_size; ++size_sent )
            {
                /* Send next character in the buffer. */
                HAL_set_8bit_reg( this_uart->base_address, THR,
                                  (uint_fast8_t)tx_buffer[size_sent]);
            }
        }
    }
    return size_sent;
}

/***************************************************************************//**
 * UART_16550_get_tx_status.
 * See core_16550.h for details of how to use this function.
 */
uint8_t
UART_16550_get_tx_status
(
    uart_16550_instance_t * this_uart
)
{
    uint8_t status = UART_16550_TX_BUSY;
    HAL_ASSERT( this_uart != NULL_INSTANCE );

    if( ( this_uart != NULL_INSTANCE ) )
    {
        /* Read the Line Status Register and update the sticky record. */
        status = HAL_get_8bit_reg( this_uart->base_address, LSR );
        this_uart->status |= status;
        /*
         * Extract the transmit status bits from the UART's Line Status Register.
         * Bit 5 - Transmitter Holding Register/FIFO Empty (THRE) status. (If = 1, TX FIFO is empty)
         * Bit 6 - Transmitter Empty (TEMT) status. (If = 1, both TX FIFO and shift register are empty)
         */
        status &= ( LSR_THRE_MASK | LSR_TEMT_MASK );
    }
    return status;
}


#ifdef __cplusplus
}
#endif












