/*******************************************************************************
 * (c) Copyright 2007 Actel Corporation.  All rights reserved.
 *
 * SmartFusion Microcontroller Subsystem UART bare metal software driver
 * implementation.
 *
 * SVN $Revision: 1898 $
 * SVN $Date: 2009-12-21 17:27:57 +0000 (Mon, 21 Dec 2009) $
 */
#include "mss_uart.h"
#include "../../CMSIS/mss_assert.h"

#ifdef __cplusplus
extern "C" {
#endif 

/*******************************************************************************
 * defines
 */
#define TX_READY	    0x01U
#define TX_COMPLETE		0U

#define TX_FIFO_SIZE	16U

#define FCR_TRIG_LEVEL_MASK     0xC0U

#define IIRF_MASK   0x0FU

/*******************************************************************************
 * Possible values for Interrupt Identification Register Field.
 */
#define IIRF_MODEM_STATUS   0x00U    
#define IIRF_THRE           0x02U
#define IIRF_RX_DATA        0x04U
#define IIRF_RX_LINE_STATUS 0x06U
#define IIRF_DATA_TIMEOUT   0x0CU

/*******************************************************************************
 * Cortex-M3 interrupt handler functions implemented as part of the MSS UART
 * driver.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void UART0_IRQHandler( void );
#else
void UART0_IRQHandler( void );
#endif

#if defined(__GNUC__)
__attribute__((__interrupt__)) void UART1_IRQHandler( void );
#else
void UART1_IRQHandler( void );
#endif

/*******************************************************************************
 * Local functions.
 */
static void MSS_UART_isr( mss_uart_instance_t * this_uart );

/*******************************************************************************
 *
 */
mss_uart_instance_t g_mss_uart0;
mss_uart_instance_t g_mss_uart1;

/***************************************************************************//**
 * UART_init.
 * Initialises the UART with default configuration.
 */
void 
MSS_UART_init
(
	mss_uart_instance_t* this_uart, 
    uint32_t baud_rate,
    uint8_t line_config
)
{
    uint16_t baud_value;
    uint32_t pclk_freq;

    /* The driver expects g_mss_uart0 and g_mss_uart1 to be the only 
     * mss_uart_instance_t instances used to identfy UART0 and UART1. */
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );
    
    /* Force the value of the CMSIS global variables holding the various system
     * clock frequencies to be updated. */
    SystemCoreClockUpdate();
    
    if ( this_uart == &g_mss_uart0 )
    {
        this_uart->hw_reg = UART0;
        this_uart->hw_reg_bit = UART0_BITBAND;
        this_uart->irqn = UART0_IRQn;

        pclk_freq = g_FrequencyPCLK0;
        
        /* reset UART0 */
        SYSREG->SOFT_RST_CR |= SYSREG_UART0_SOFTRESET_MASK;
        /* Clear any previously pended UART0 interrupt */
        NVIC_ClearPendingIRQ( UART0_IRQn );
        /* Take UART0 out of reset. */
        SYSREG->SOFT_RST_CR &= ~SYSREG_UART0_SOFTRESET_MASK;
    }
    else
    {
        this_uart->hw_reg = UART1;
        this_uart->hw_reg_bit = UART1_BITBAND;
        this_uart->irqn = UART1_IRQn;

        pclk_freq = g_FrequencyPCLK1;
        
        /* Reset UART1 */
        SYSREG->SOFT_RST_CR |= SYSREG_UART1_SOFTRESET_MASK;
        /* Clear any previously pended UART1 interrupt */
        NVIC_ClearPendingIRQ( UART1_IRQn );
        /* Take UART1 out of reset. */
        SYSREG->SOFT_RST_CR &= ~SYSREG_UART1_SOFTRESET_MASK;
    }
    
    /* disable interrupts */
    this_uart->hw_reg->IER = 0U;

    /*
     * Compute baud value based on requested baud rate and PCLK frequency.
     * The baud value is computed using the following equation:
     *      baud_value = PCLK_Frequency / (baud_rate * 16)
     * The baud value is rounded up or down depending on what would be the remainder
     * of the divide by 16 operation.
     */
    baud_value = (uint16_t)(pclk_freq / baud_rate);
    if ( baud_value & 0x00000008U )
    {
        /* remainder above 0.5 */
        baud_value = (baud_value >> 4U) + 1U;
    }
    else
    {
        /* remainder below 0.5 */
        baud_value = (baud_value >> 4U);
    }

    /* set divisor latch */
    this_uart->hw_reg_bit->LCR_DLAB = (uint32_t)1;

    /* msb of baud value */
    this_uart->hw_reg->DMR = (uint8_t)(baud_value >> 8);
    /* lsb of baud value */
    this_uart->hw_reg->DLR = (uint8_t)baud_value;

    /* reset divisor latch */
    this_uart->hw_reg_bit->LCR_DLAB = (uint32_t)0;

    /* set the line control register (bit length, stop bits, parity) */
    this_uart->hw_reg->LCR = line_config;
    
    /* FIFO configuration */
    this_uart->hw_reg->FCR = (uint8_t)MSS_UART_FIFO_SINGLE_BYTE;
    
    /* disable loopback */
    this_uart->hw_reg_bit->MCR_LOOP = (uint32_t)0;

    /* Instance setup */
    this_uart->tx_buff_size = TX_COMPLETE;
    this_uart->tx_buffer = (const uint8_t *)0;
    this_uart->tx_idx = 0U;
    
    this_uart->rx_handler = (mss_uart_rx_handler_t)0;
}

/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
void 
MSS_UART_polled_tx
( 
	mss_uart_instance_t * this_uart, 
	const uint8_t * pbuff,
	uint32_t tx_size
)
{
	uint32_t char_idx;
	uint32_t status;

    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );
    
    for ( char_idx = 0U; char_idx < tx_size; char_idx++ )
    {
        /* Wait for UART to become ready to transmit. */
        do {
            status = this_uart->hw_reg_bit->LSR_THRE;
        } while ( (status & TX_READY) == 0U );
        /* Send next character in the buffer. */
        this_uart->hw_reg->THR = pbuff[char_idx];
    }
}

/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
void 
MSS_UART_polled_tx_string
( 
	mss_uart_instance_t * this_uart, 
	const uint8_t * p_sz_string
)
{
	uint32_t char_idx;
	uint32_t status;

    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );
    
    char_idx = 0U;
    
    while ( p_sz_string[char_idx] != 0U )
    {
        /* Wait for UART to become ready to transmit. */
        do {
            status = this_uart->hw_reg_bit->LSR_THRE;
        } while ( (status & TX_READY) == 0U);
        /* Send next character in the buffer. */
        this_uart->hw_reg->THR = p_sz_string[char_idx];
        ++char_idx;
    }
}

/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
void 
MSS_UART_irq_tx
( 
	mss_uart_instance_t * this_uart, 
	const uint8_t * pbuff,
	uint32_t tx_size
)
{
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );
    
    if ( tx_size > 0U )
    {
        /*Initialise the transmit info for the UART instance with the arguments.*/
        this_uart->tx_buffer = pbuff;
        this_uart->tx_buff_size = tx_size;
        this_uart->tx_idx = (uint16_t)0;
                
        /* enables TX interrupt */
        this_uart->hw_reg_bit->IER_ETBEI = (uint32_t)1;
        
        /* Enable UART instance interrupt in Cortex-M3 NVIC. */
        NVIC_EnableIRQ( this_uart->irqn );
    }
}

/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
int8_t 
MSS_UART_tx_complete
( 
	mss_uart_instance_t * this_uart 
)
{
    int8_t ret_value = 0;
    uint32_t transmit_empty = this_uart->hw_reg_bit->LSR_TEMT;
    
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );

    if ( ( TX_COMPLETE == this_uart->tx_buff_size ) && transmit_empty )
    {
        ret_value = 1;
    }
    
    return ret_value;
}


/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
size_t
MSS_UART_get_rx
(
    mss_uart_instance_t * this_uart,
    uint8_t * rx_buff,
    size_t buff_size
)
{
    size_t rx_size = 0U;
    
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );

    while (( this_uart->hw_reg_bit->LSR_DR != 0U) && ( rx_size < buff_size ) )
    {
        rx_buff[rx_size] = this_uart->hw_reg->RBR;
        ++rx_size;
    }
               
    return rx_size;
}

/***************************************************************************//**
 * Interrupt service routine triggered by the Transmitter Holding Register
 * Empty (THRE) interrupt or Received Data Available (RDA). 
 * On THRE irq this routine will transmit the data from the transmit buffer. 
 * When all bytes are transmitted, this routine disables the THRE interrupt
 * and resets the transmit counter.
 * On RDA irq this routine will call the user's receive handler routine previously
 * registered with the UART driver through a call to UART_set_rx_handler().
 */
static void 
MSS_UART_isr
( 
	mss_uart_instance_t * this_uart 
)
{
	uint8_t iirf;
    uint32_t tx_empty;
	
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );

    iirf = this_uart->hw_reg->IIR & IIRF_MASK;
   
    switch ( iirf )
    {
    case IIRF_MODEM_STATUS:
        break;
        
    case IIRF_THRE: /* Transmitter Holding Register Empty */
        tx_empty = this_uart->hw_reg_bit->LSR_TEMT;
        
        if ( tx_empty )
        {
            uint32_t i;
            uint32_t fill_size = TX_FIFO_SIZE;
            uint32_t tx_remain = this_uart->tx_buff_size - this_uart->tx_idx;
            if ( tx_remain < TX_FIFO_SIZE )
            {
                fill_size = tx_remain;
            }
            /* Fill up FIFO */
            for ( i = 0U; i < fill_size; ++i )
            {
                this_uart->hw_reg->THR = this_uart->tx_buffer[this_uart->tx_idx];
                ++this_uart->tx_idx;
            }
        }
        else
        {
            this_uart->hw_reg->THR = this_uart->tx_buffer[this_uart->tx_idx];
            ++this_uart->tx_idx;
        }
        
        if ( this_uart->tx_idx == this_uart->tx_buff_size )
        {
            this_uart->tx_buff_size = TX_COMPLETE;
            /* disables TX interrupt */
            this_uart->hw_reg_bit->IER_ETBEI = 0U;
        }
        break;
        
    case IIRF_RX_DATA:          /* Received Data Available */
    case IIRF_DATA_TIMEOUT:
        if (this_uart->rx_handler != 0)
        {
            (*(this_uart->rx_handler))();
        }
        break;
        
    case IIRF_RX_LINE_STATUS:
        break;
        
    default:
        /* Disable other interrupts */
        this_uart->hw_reg_bit->IER_ELSI = 0U;
        this_uart->hw_reg_bit->IER_EDSSI = 0U;
        break;
    }
}

/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
void
MSS_UART_set_rx_handler
(
	mss_uart_instance_t *       this_uart,
    mss_uart_rx_handler_t       handler,
    mss_uart_rx_trig_level_t    trigger_level
)
{
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );
    
    this_uart->rx_handler = handler;
    
    /* Set the receive interrupt trigger level. */
    this_uart->hw_reg->FCR = (this_uart->hw_reg->FCR & (uint8_t)(~((uint8_t)FCR_TRIG_LEVEL_MASK))) | (uint8_t)trigger_level;
    
    /* Enable receive interrupt. */
    this_uart->hw_reg_bit->IER_ERBFI = 1U;
    
    /* Enable UART instance interrupt in Cortex-M3 NVIC. */
    NVIC_EnableIRQ( this_uart->irqn );
}

/***************************************************************************//**
 * See mss_uart.h for details of how to use this function.
 */
void
MSS_UART_set_loopback
(
	mss_uart_instance_t *   this_uart,
	mss_uart_loopback_t     loopback
)
{
    ASSERT( (this_uart == &g_mss_uart0) || (this_uart == &g_mss_uart1) );
    
    if ( loopback == MSS_UART_LOOPBACK_OFF )
    {
        this_uart->hw_reg_bit->MCR_LOOP = 0U;
    }
    else
    {
        this_uart->hw_reg_bit->MCR_LOOP = 1U;
    }
}

/***************************************************************************//**
 * UART0 interrupt service routine.
 * UART0_IRQHandler is included within the Cortex-M3 vector table as part of the
 * Fusion 2 CMSIS.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void UART0_IRQHandler( void )
#else
void UART0_IRQHandler( void )
#endif
{
    MSS_UART_isr( &g_mss_uart0 );
    NVIC_ClearPendingIRQ( UART0_IRQn );
}

/***************************************************************************//**
 * UART1 interrupt service routine.
 * UART2_IRQHandler is included within the Cortex-M3 vector table as part of the
 * Fusion 2 CMSIS.
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void UART1_IRQHandler( void )
#else
void UART1_IRQHandler( void )
#endif
{
    MSS_UART_isr( &g_mss_uart1 );
    NVIC_ClearPendingIRQ( UART1_IRQn );
}

#ifdef __cplusplus
}
#endif
