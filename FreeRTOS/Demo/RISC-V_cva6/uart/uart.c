/*******************************************************************************
 * Copyright (c) 2020 Thales.
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 */
// Additional contributions by:
//         Sebastien Jacq - sjthales on github.com
//         Anjali Gedam - anjaliigedam on github.com
//
// Description: Driver for UART Ip of the CVA6 platform
//
// =========================================================================== //
// Revisions  :
// Date        Version  Author       Description
// 2020-10-06  0.1      S.Jacq       modification of the Test for CVA6 softcore
// 2021-07-12  0.2      Anjali G     modification for the CVA6 FPGA
// =========================================================================== //


#include "uart.h"

//#include "plic.h"
#include "../hw_platform.h"


/*******************************************************************************
 * Defines
 */
#define TX_COMPLETE                     0u
#define TX_FIFO_SIZE                    16u

#define FCR_TRIG_LEVEL_MASK             0xC0u

#define IIRF_MASK                       0x0Fu

#define INVALID_INTERRUPT               0u
#define INVALID_IRQ_HANDLER             ((uart_irq_handler_t) 0)
#define NULL_HANDLER                    ((uart_irq_handler_t) 0)

#define UART_DATA_READY             ((uint8_t) 0x01)


/*******************************************************************************
 * Possible values for Interrupt Identification Register Field.
 */
#define IIRF_MODEM_STATUS               0x00u
#define IIRF_THRE                       0x02u
//#define IIRF_MMI                        0x03u
#define IIRF_RX_DATA                    0x04u
#define IIRF_RX_LINE_STATUS             0x06u
#define IIRF_DATA_TIMEOUT               0x0Cu


uart_instance_t g_uart_0 = { .hw_reg = FPGA_UART_0_BASE };

/*******************************************************************************
 * Global initialization for all modes
 */
static void global_init
(
    uart_instance_t * this_uart,
    uint32_t baud_rate,
    uint8_t line_config
)
{
    
    /* disable interrupts */
    this_uart->hw_reg->IER = 0u;

    /* FIFO configuration */
    this_uart->hw_reg->FCR = 0u;

    /* clear receiver FIFO */
    this_uart->hw_reg->FCR = FIFO_RX_TRIGGER_LEVEL_14_MASK | CLEAR_RX_FIFO_MASK | CLEAR_TX_FIFO_MASK | RXRDY_TXRDYN_EN_MASK;

    /* clear transmitter FIFO */
    this_uart->hw_reg->FCR |= CLEAR_TX_FIFO_MASK;

    /* set default READY mode : Mode 0*/
    /* enable RXRDYN and TXRDYN pins. The earlier FCR write to set the TX FIFO
     * trigger level inadvertently disabled the FCR_RXRDY_TXRDYN_EN bit. */
    this_uart->hw_reg->FCR |= RXRDY_TXRDYN_EN_MASK;

    this_uart->hw_reg->MCR = 0u;


    
    /* 
     * Configure baud rate divisors. This uses the fractional baud rate divisor
     * where possible to provide the most accurate baud rat possible.
     */
    config_baud_divisors(this_uart, baud_rate);

    /* set the line control register (bit length, stop bits, parity) */
    this_uart->hw_reg->LCR = line_config;

    /* Instance setup */
    this_uart->baudrate = baud_rate;
    this_uart->lineconfig = line_config;
    this_uart->tx_buff_size = TX_COMPLETE;
    this_uart->tx_buffer = (const uint8_t*)0;
    this_uart->tx_idx = 0u;

    /* Default handlers for MSS UART interrupts */
    this_uart->rx_handler       = NULL_HANDLER;
    this_uart->tx_handler       = NULL_HANDLER;
    this_uart->linests_handler  = NULL_HANDLER;
    this_uart->modemsts_handler = NULL_HANDLER;

    /* Initialize the sticky status */
    this_uart->status = 0u;
}

/*******************************************************************************
 * Public Functions
 *******************************************************************************/
/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void 
UART_init
(
    uart_instance_t* this_uart, 
    uint32_t baud_rate,
    uint8_t line_config
)
{
    /* Perform generic initialization */
    global_init(this_uart, baud_rate, line_config);


    /* set default tx handler for automated TX using interrupt in USART mode */
    this_uart->tx_handler = default_tx_handler;
}



/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_polled_tx
(
    uart_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
)
{
    uint32_t char_idx = 0u;
   // uint32_t size_sent;
    uint8_t status;
    //uint32_t temp_tx_size = tx_size;

    //ASSERT(pbuff != ( (uint8_t*)0));
    //ASSERT(tx_size > 0u);

    if ((pbuff != ((uint8_t*)0)) && (tx_size > 0u))
    {
        /* Remain in this loop until the entire input buffer
         * has been transferred to the UART.
         */
        do
        {
            /* Wait until TX FIFO is empty. */
            do
            {
                status = this_uart->hw_reg->LSR;
               // this_uart->status |= status;
            }while (0u == (status & UART_THRE));


            /* Check if TX FIFO is empty. */
           // if (status & UART_THRE)
            //{
               // uint32_t fill_size = TX_FIFO_SIZE;

                /* Calculate the number of bytes to transmit. */
                //if (temp_tx_size < TX_FIFO_SIZE)
                //{
                //    fill_size = temp_tx_size;
                //}

                /* Fill the TX FIFO with the calculated the number of bytes. */
                //for (size_sent = 0u; size_sent < fill_size; ++size_sent)
                //{
                    /* Send next character in the buffer. */
                    this_uart->hw_reg->THR = pbuff[char_idx];
                    char_idx++;
                //}

                /* Calculate the number of bytes remaining(not transmitted yet)*/
                //temp_tx_size -= size_sent;
            //}
        }while (char_idx < tx_size);
    }
}


/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_polled_tx_string
(
    uart_instance_t * this_uart,
    const uint8_t * p_sz_string
)
{
    uint32_t char_idx = 0u;
    //uint32_t fill_size;
    uint8_t data_byte;
    volatile uint8_t status;

    //ASSERT(p_sz_string != ((uint8_t*)0));

    if (p_sz_string != ((uint8_t*)0))
    {
        /* Get the first data byte from the input buffer */
        data_byte = p_sz_string[char_idx];

        /* First check for the NULL terminator byte.
         * Then remain in this loop until the entire string in the input buffer
         * has been transferred to the UART.
         */
        while (0u != data_byte)
        {
            /* Wait until TX FIFO is empty. */
            do
            {
                status = this_uart->hw_reg->LSR;
               // this_uart->status |= status;
            }while (0u == (status & UART_THRE));

		
            /* Send bytes from the input buffer until the TX FIFO is full
             * or we reach the NULL terminator byte.
             */
            //fill_size = 0u;

           // while ((0u != data_byte) && (fill_size < TX_FIFO_SIZE))
            //{
                /* Send the data byte */
                this_uart->hw_reg->THR = data_byte;
                //++fill_size;
                char_idx++;
                /* Get the next data byte from the input buffer */
                data_byte = p_sz_string[char_idx];
            //}
        }
    }
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_irq_tx
(
    uart_instance_t * this_uart,
    const uint8_t * pbuff,
    uint32_t tx_size
)
{
    //ASSERT(pbuff != ((uint8_t*)0));
    //ASSERT(tx_size > 0u);

    if ((tx_size > 0u) && (pbuff != ((uint8_t*)0)))
    {
        /*Initialize the transmit info for the UART instance with the arguments*/
        this_uart->tx_buffer = pbuff;
        this_uart->tx_buff_size = tx_size;
        this_uart->tx_idx = 0u;

        /* assign default handler for data transfer */
        this_uart->tx_handler = default_tx_handler;

        /* enables TX interrupt */
        this_uart->hw_reg->IER |= ETBEI_MASK;
        enable_irq(this_uart);
    }
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
int8_t
UART_tx_complete
(
    uart_instance_t * this_uart
)
{
    int8_t ret_value = 0;
    uint8_t status = 0u;

    /* Read the Line Status Register and update the sticky record. */
    status = this_uart->hw_reg->LSR;
    this_uart->status |= status;

    if ((TX_COMPLETE == this_uart->tx_buff_size) &&
       ((status & UART_TEMT) != 0u))
    {
        ret_value = (int8_t)1;
    }

    return ret_value;
}


/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
size_t
UART_get_rx
(
    uart_instance_t * this_uart,
    uint8_t * rx_buff,
    size_t buff_size
)
{
    size_t rx_size = 0u;
    uint8_t status = 0u;

    //ASSERT(rx_buff != ((uint8_t*)0));
    //ASSERT(buff_size > 0u);
    //printf("UART_get_rx() called buff_size = %d\n", buff_size);

    if ((rx_buff != (uint8_t*)0) && (buff_size > 0u))
    {
        status = this_uart->hw_reg->LSR;
        this_uart->status |= status;
        //printf("UART_get_rx() LSR status = %d\n", status);
        
        while (((status & UART_DATA_READY) != 0u) && (rx_size < buff_size))
        {
            rx_buff[rx_size] = this_uart->hw_reg->RBR;
            ++rx_size;
            status = this_uart->hw_reg->LSR;
            //printf("1 UART_get_rx() LSR status = %d\n", status);
            this_uart->status |= status;
            //printf("2 UART_get_rx() LSR status = %d\n", status);
        
        }
    }

    return rx_size;
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_enable_irq
(
    uart_instance_t * this_uart,
    uart_irq_t irq_mask
)
{
    //ASSERT(UART_INVALID_IRQ > irq_mask);

    enable_irq(this_uart);

    if (UART_INVALID_IRQ > irq_mask)
    {
        /* irq_mask encoding: 1- enable
         * bit 0 - Receive Data Available Interrupt
         * bit 1 - Transmitter Holding  Register Empty Interrupt
         * bit 2 - Receiver Line Status Interrupt
         * bit 3 - Modem Status Interrupt
         */
        this_uart->hw_reg->IER |= ((uint8_t)(((uint32_t)irq_mask &
                                                            (uint32_t)IIRF_MASK)));

    }
}


/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_set_rx_handler
(
    uart_instance_t *       this_uart,
    uart_irq_handler_t      handler,
    uart_rx_trig_level_t    trigger_level
)
{
    //ASSERT(handler != INVALID_IRQ_HANDLER );
    //ASSERT(trigger_level < UART_FIFO_INVALID_TRIG_LEVEL);
    //PLIC_init();
    
    if ((handler != INVALID_IRQ_HANDLER) &&
       (trigger_level < UART_FIFO_INVALID_TRIG_LEVEL))
    {
        //printf("UART DEBUG1\n");
        this_uart->rx_handler = handler;

        /* Set the receive interrupt trigger level. */
        this_uart->hw_reg->FCR = (this_uart->hw_reg->FCR &
                                 (uint8_t)(~((uint8_t)FCR_TRIG_LEVEL_MASK))) |
                                 (uint8_t)trigger_level;

        /* Enable receive interrupt. */
        this_uart->hw_reg->IER |= ERBFI_MASK;
        //printf("UART Enable IRQ\n");
        enable_irq(this_uart);
    }
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_set_tx_handler
(
    uart_instance_t * this_uart,
    uart_irq_handler_t handler
)
{
    //ASSERT(handler != INVALID_IRQ_HANDLER);

    if (handler != INVALID_IRQ_HANDLER)
    {
        this_uart->tx_handler = handler;

        /* Make TX buffer info invalid */
        this_uart->tx_buffer = (const uint8_t*)0;
        this_uart->tx_buff_size = 0u;

        /* Enable transmitter holding register Empty interrupt. */
        this_uart->hw_reg->IER |= ETBEI_MASK;
        enable_irq(this_uart);
    }
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_set_modemstatus_handler
(
    uart_instance_t * this_uart,
    uart_irq_handler_t handler
)
{
    //ASSERT(handler != INVALID_IRQ_HANDLER);

    if (handler != INVALID_IRQ_HANDLER)
    {
        this_uart->modemsts_handler = handler;

        /* Enable modem status interrupt. */
        this_uart->hw_reg->IER |= EDSSI_MASK;
        enable_irq(this_uart);
    }
}


/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
size_t
UART_fill_tx_fifo
(
    uart_instance_t * this_uart,
    const uint8_t * tx_buffer,
    size_t tx_size
)
{
    uint8_t status = 0u;
    uint32_t size_sent = 0u;

    //ASSERT(tx_buffer != ( (uint8_t*)0));
    //ASSERT(tx_size > 0);

    /* Fill the UART's Tx FIFO until the FIFO is full or the complete input
     * buffer has been written. */
    if ((tx_buffer != ((uint8_t*)0)) && (tx_size > 0u))
    {
        status = this_uart->hw_reg->LSR;
        this_uart->status |= status;

        if (status & UART_THRE)
        {
            uint32_t fill_size = TX_FIFO_SIZE;

            if (tx_size < TX_FIFO_SIZE)
            {
                fill_size = tx_size;
            }

            /* Fill up FIFO */
            for (size_sent = 0u; size_sent < fill_size; size_sent++)
            {
                /* Send next character in the buffer. */
                this_uart->hw_reg->THR = tx_buffer[size_sent];
            }
        }
    }

    return size_sent;
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
uint8_t
UART_get_rx_status
(
    uart_instance_t * this_uart
)
{
    uint8_t status = UART_INVALID_PARAM;

    /*
     * Extract UART receive error status.
     * Bit 1 - Overflow error status
     * Bit 2 - Parity error status
     * Bit 3 - Frame error status
     * Bit 4 - Break interrupt indicator
     * Bit 7 - FIFO data error status
     */
    this_uart->status |= (this_uart->hw_reg->LSR);
    status = (this_uart->status & STATUS_ERROR_MASK);
    
    //printf("UART_get_rx_status = %d", status);
    //printf("UART_get_rx_LSR = %d", this_uart->hw_reg->LSR);


    /* Clear the sticky status after reading */
    this_uart->status = 0u;

    return status;
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
uint8_t
UART_get_modem_status
(
    const uart_instance_t * this_uart
)
{
    uint8_t status = UART_INVALID_PARAM;

    /*
     * Extract UART modem status and place in lower bits of "status".
     * Bit 0 - Delta Clear to Send Indicator
     * Bit 1 - Delta Clear to Receive Indicator
     * Bit 2 - Trailing edge of Ring Indicator detector
     * Bit 3 - Delta Data Carrier Detect indicator
     * Bit 4 - Clear To Send
     * Bit 5 - Data Set Ready
     * Bit 6 - Ring Indicator
     * Bit 7 - Data Carrier Detect
     */
    status = this_uart->hw_reg->MSR;
    //printf("UART_get_modem_status = %d", status);
    
    return status;
}


/***************************************************************************//**
 * UART_get_tx_status.
 * See uart.h for details of how to use this function.
 */
uint8_t
UART_get_tx_status
(
    uart_instance_t * this_uart
)
{
    uint8_t status = UART_TX_BUSY;

    /* Read the Line Status Register and update the sticky record. */
    status = this_uart->hw_reg->LSR;
    this_uart->status |= status;
    
    /*
     * Extract the transmit status bits from the UART's Line Status Register.
     * Bit 5 - Transmitter Holding Register/FIFO Empty (THRE) status. 
               (If = 1, TX FIFO is empty)
     * Bit 6 - Transmitter Empty (TEMT) status. 
               (If = 1, both TX FIFO and shift register are empty)
     */
    status &= (UART_THRE | UART_TEMT);

    return status;
}

/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_set_break
(
    uart_instance_t * this_uart
)
{
    /* set break character on Tx line */
    this_uart->hw_reg->LCR |= SB_MASK;
}


/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
void
UART_clear_break
(
    uart_instance_t * this_uart
)
{
    /* remove break character from Tx line */
    this_uart->hw_reg->LCR &= ~SB_MASK;
}

/***************************************************************************//**
 * Configure baud divisors using fractional baud rate if possible.
 */
static void
config_baud_divisors
(
    uart_instance_t * this_uart,
    uint32_t baudrate
)
{
    uint32_t baud_value;
    uint32_t baud_value_by_64;
    uint32_t baud_value_by_128;
//    uint32_t fractional_baud_value;
    uint64_t pclk_freq;

    this_uart->baudrate = baudrate;

    /* Use the system clock value from hw_platform.h */
    pclk_freq = FPGA_UART_0_FREQUENCY;

    /*
     * Compute baud value based on requested baud rate and PCLK frequency.
     * The baud value is computed using the following equation:
     *      baud_value = PCLK_Frequency / (baud_rate * 16)
     */
    baud_value_by_128 = (uint32_t)((8UL * pclk_freq) / baudrate);
    baud_value_by_64 = baud_value_by_128 / 2u;
    baud_value = baud_value_by_64 / 64u;
//    fractional_baud_value = baud_value_by_64 - (baud_value * 64u);
//    fractional_baud_value += (baud_value_by_128 - (baud_value * 128u))
 //                            - (fractional_baud_value * 2u);

    /* //ASSERT if integer baud value fits in 16-bit. */
    //ASSERT(baud_value <= UINT16_MAX);

    if (baud_value <= (uint32_t)UINT16_MAX)
    {
        
        /*
        * Use Fractional baud rate divisors
        */
        /* set divisor latch */
        this_uart->hw_reg->LCR = DLAB_MASK;

        /* msb of baud value */
        this_uart->hw_reg->DLM = (uint8_t)(baud_value >> 8);
        /* lsb of baud value */
        this_uart->hw_reg->DLL = (uint8_t)baud_value;

        /* reset divisor latch */
        this_uart->hw_reg->LCR = 0;
	    }
}

/***************************************************************************//**
 * Interrupt service routine triggered by any MSS UART interrupt. This routine
 * will call the handler function appropriate to the interrupt from the
 * handlers previously registered with the driver through calls to the
 * UART_set_*_handler() functions, or it will call the default_tx_handler()
 * function in response to transmit interrupts if UART_irq_tx() is used to
 * transmit data.
 */
static void __attribute__ ((unused))
uart_isr
(
    uart_instance_t * this_uart
)
{
    //printf("uart_isr called\n");
    uint8_t iirf;

    iirf = this_uart->hw_reg->IIR & IIRF_MASK;

    switch (iirf)
    {
        case IIRF_MODEM_STATUS:  /* Modem status interrupt */
        {
            //ASSERT(NULL_HANDLER != this_uart->modemsts_handler);
            if (NULL_HANDLER != this_uart->modemsts_handler)
            {
               (*(this_uart->modemsts_handler))(this_uart);
            }
        }
        break;

        case IIRF_THRE: /* Transmitter Holding Register Empty */
        {
            //ASSERT(NULL_HANDLER != this_uart->tx_handler);
            if (NULL_HANDLER != this_uart->tx_handler)
            {
                (*(this_uart->tx_handler))(this_uart);
            }
        }
        break;

        case IIRF_RX_DATA:      /* Received Data Available */
        case IIRF_DATA_TIMEOUT: /* Received Data Timed-out */
        {
            //ASSERT(NULL_HANDLER != this_uart->rx_handler);
            if (NULL_HANDLER != this_uart->rx_handler)
            {
                (*(this_uart->rx_handler))(this_uart);
            }
        }
        break;

        case IIRF_RX_LINE_STATUS:  /* Line Status Interrupt */
        {
            //ASSERT(NULL_HANDLER != this_uart->linests_handler);
            if (NULL_HANDLER != this_uart->linests_handler)
            {
               (*(this_uart->linests_handler))(this_uart);
            }
        }
        
        default:
        {
            //ASSERT(INVALID_INTERRUPT); /*Alternative case has been considered*/
        }
        break;
    }
}



/***************************************************************************//**
 * See uart.h for details of how to use this function.
 */
static void
default_tx_handler
(
    uart_instance_t * this_uart
)
{
    uint8_t status;

    //ASSERT(( (uint8_t*)0 ) != this_uart->tx_buffer);
    //ASSERT(0u < this_uart->tx_buff_size);

    if ((((uint8_t*)0 ) != this_uart->tx_buffer) &&
       (0u < this_uart->tx_buff_size))
    {
        /* Read the Line Status Register and update the sticky record. */
        status = this_uart->hw_reg->LSR;
        this_uart->status |= status;

        /*
         * This function should only be called as a result of a THRE interrupt.
         * Verify that this is true before proceeding to transmit data.
         */
        if (status & UART_THRE)
        {
            uint32_t cnt;
            uint32_t fill_size = TX_FIFO_SIZE;
            uint32_t tx_remain = this_uart->tx_buff_size - this_uart->tx_idx;

            /* Calculate the number of bytes to transmit. */
            if (tx_remain < TX_FIFO_SIZE)
            {
                fill_size = tx_remain;
            }

            /* Fill the TX FIFO with the calculated the number of bytes. */
            for (cnt = 0u; cnt < fill_size; ++cnt)
            {
                /* Send next character in the buffer. */
                this_uart->hw_reg->THR = this_uart->tx_buffer[this_uart->tx_idx];
                ++this_uart->tx_idx;
            }
        }

        /* Flag Tx as complete if all data has been pushed into the Tx FIFO. */
        if (this_uart->tx_idx == this_uart->tx_buff_size)
        {
            this_uart->tx_buff_size = TX_COMPLETE;

            /* disables TX interrupt */
            this_uart->hw_reg->IER &= ~ETBEI_MASK;
        }
    }
}


static void __attribute__ ((unused))
enable_irq
(
    const uart_instance_t * this_uart
)
{


   //PLIC_IRQn_Type plic_num = 0;

    if (&g_uart_0 == this_uart )
    {
        //printf("enable_irq() UART assign plic_num = %d\n",plic_num);
        //plic_num = UART_0_PLIC_IRQHandler;

    }
    else
    {
        //printf("ASSERT(0) called\n");
        //ASSERT(0); /*Alternative case has been considered*/
    }

    /* Enable UART instance interrupt in PLIC. */
    //PLIC_EnableIRQ(plic_num);
}

static void __attribute__ ((unused))
disable_irq
(
    const uart_instance_t * this_uart
)
{
    //PLIC_IRQn_Type plic_num = 0;

    if (&g_uart_0 == this_uart )
    {
        //plic_num = UART_0_PLIC_IRQHandler;
    }
    else
    {
        //ASSERT(0); /*Alternative case has been considered*/
    }

    /* Disable UART instance interrupt in PLIC. */
    //PLIC_DisableIRQ(plic_num);
}

