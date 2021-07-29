#include "usart.h"
#include <avr/interrupt.h>
#include "FreeRTOS.h"

#if (USART_INSTANCE  ==  0)

#define USART               USART0
#define USART_DRE_vect      USART0_DRE_vect
#define USART_RXC_vect      USART0_RXC_vect
#define USART_TXC_vect      USART0_TXC_vect
#define USART_PIN_INIT()    PORTA.DIRCLR = PIN1_bm; \
                            PORTA.DIRSET = PIN0_bm;

#elif (USART_INSTANCE  ==  1)

#define USART               USART1
#define USART_DRE_vect      USART1_DRE_vect
#define USART_RXC_vect      USART1_RXC_vect
#define USART_TXC_vect      USART1_TXC_vect
#define USART_PIN_INIT()    PORTC.DIRCLR = PIN1_bm; \
                            PORTC.DIRSET = PIN0_bm;

#elif (USART_INSTANCE  ==  2)

#define USART               USART2
#define USART_DRE_vect      USART2_DRE_vect
#define USART_RXC_vect      USART2_RXC_vect
#define USART_TXC_vect      USART2_TXC_vect
#define USART_PIN_INIT()    PORTF.DIRCLR = PIN1_bm; \
                            PORTF.DIRSET = PIN0_bm;

#elif (USART_INSTANCE  ==  3)

#define USART               USART3
#define USART_DRE_vect      USART3_DRE_vect
#define USART_RXC_vect      USART3_RXC_vect
#define USART_TXC_vect      USART3_TXC_vect
#define USART_PIN_INIT()    PORTB.DIRCLR = PIN1_bm; \
                            PORTB.DIRSET = PIN0_bm;

#else

#error The selected USART instance not supported.

#endif

#define USART_RX_BUFFER_MASK (USART_rx_size - 1)
#define USART_TX_BUFFER_MASK (USART_tx_size - 1)

static uint8_t *USART_rx_buff;
static volatile uint16_t USART_rx_head;
static volatile uint16_t USART_rx_tail;
static volatile uint16_t USART_rx_elements;
static volatile uint16_t USART_rx_size;

static uint8_t *USART_tx_buff;
static volatile uint16_t USART_tx_head;
static volatile uint16_t USART_tx_tail;
static volatile uint16_t USART_tx_elements;
static volatile uint16_t USART_tx_size;

static uint8_t USART_initialized = 0;

static void USART_setRxBuff(void *rxBuffer, uint16_t size)
{
    USART_rx_tail = 0;
    USART_rx_head = 0;
    USART_rx_elements = 0;
    
    USART_rx_buff = (uint8_t *)rxBuffer;
    USART_rx_size = size;
}

static void USART_setTxBuff(void *txBuffer, uint16_t size)
{
    USART_tx_tail = 0;
    USART_tx_head = 0;
    USART_tx_elements = 0;
    
    USART_tx_buff = (uint8_t *)txBuffer;
    USART_tx_size = size;
}

static void USART_setDefaultConfigs(unsigned long baudrate)
{
    USART.CTRLA = 1 << USART_RXCIE_bp;
    USART.CTRLB = 1 << USART_RXEN_bp | 1 << USART_TXEN_bp;
    USART.CTRLC = 0x03;
    USART.BAUD = (uint16_t)USART_BAUD_RATE(baudrate);
}

void USART_setConfigs(USART_cfg_t cfg)
{
    USART.CTRLA = cfg.CTRLA;
    USART.CTRLB = cfg.CTRLB;
    USART.CTRLC = cfg.CTRLC;
    USART.BAUD = cfg.BAUD;
    USART.CTRLD = cfg.CTRLD;
    USART.DBGCTRL = cfg.DBGCTRL;
    USART.EVCTRL = cfg.EVCTRL;

    USART_initialized = 1;
}

void USART_initConfigs(USART_cfg_t *cfg)
{
    cfg->CTRLA = 0;
    cfg->CTRLB = 0;
    cfg->CTRLC = 0;
    cfg->CTRLD = 0;
    cfg->BAUD = 0;
    cfg->CTRLD = 0;
    cfg->DBGCTRL = 0;
    cfg->EVCTRL = 0;
    
    USART_initialized = 0;
}

void USART_initialize(void *rxBuffer, uint16_t rxSize, void *txBuffer, uint16_t txSize, unsigned long baudrate)
{
    /* Software init */
    USART_setRxBuff(rxBuffer, rxSize);
    USART_setTxBuff(txBuffer, txSize);

    /* Hardware init */
    USART_PIN_INIT();
    if(!USART_initialized)
    {
        USART_setDefaultConfigs(baudrate);
    }
}

uint8_t USART_read(void)
{
    uint16_t tmptail;

    /* Wait for incoming data */
    while (USART_rx_elements == 0)
    {
        ;
    }
    /* Calculate buffer index */
    tmptail = (USART_rx_tail + 1) & USART_RX_BUFFER_MASK;
    /* Store new index */
    USART_rx_tail = tmptail;
    portENTER_CRITICAL();
    USART_rx_elements--;
    portEXIT_CRITICAL();

    /* Return data */
    return USART_rx_buff[tmptail];
}

void USART_write(const uint8_t data)
{
    uint16_t tmphead;

    /* Calculate buffer index */
    tmphead = (USART_tx_head + 1) & USART_TX_BUFFER_MASK;
    /* Wait for free space in buffer */
    while (USART_tx_elements == USART_tx_size)
    {
        ;
    }
    /* Store data in buffer */
    USART_tx_buff[tmphead] = data;
    /* Store new index */
    USART_tx_head = tmphead;
    portENTER_CRITICAL();
    USART_tx_elements++;
    portEXIT_CRITICAL();
    /* Enable Tx interrupt */
    USART.CTRLA |= (1 << USART_DREIE_bp);
}

void USART_blocking_write(const uint8_t data)
{
       while (!(USART.STATUS & USART_DREIF_bm));
       USART.TXDATAL = data;
}

uint8_t USART_isRxReady(void)
{
    return (USART_rx_elements != 0);
}

uint8_t USART_isTxReady(void)
{
    return (USART_tx_elements != USART_tx_size);
}

uint16_t USART_getRxElements(void)
{
    return USART_rx_elements;
}

uint16_t USART_getTxElements(void)
{
    return USART_tx_elements;
}

void USART_close(void)
{
    USART.CTRLB &= ~(USART_RXEN_bm | USART_TXEN_bm);
}

ISR(USART_RXC_vect)
{
    uint8_t data;
    uint16_t tmphead;

    /* Read the received data */
    data = USART.RXDATAL;
    /* Calculate buffer index */
    tmphead = (USART_rx_head + 1) & USART_RX_BUFFER_MASK;

    if (tmphead == USART_rx_tail)
    {
        /* ERROR! Receive buffer overflow */
    }
    else
    {
        /*Store new index*/
        USART_rx_head = tmphead;

        /* Store received data in buffer */
        USART_rx_buff[tmphead] = data;
        USART_rx_elements++;
    }
}

ISR(USART_DRE_vect)
{
    uint16_t tmptail;

    /* Check if all data is transmitted */
    if (USART_tx_elements != 0)
    {
        /* Calculate buffer index */
        tmptail = (USART_tx_tail + 1) & USART_TX_BUFFER_MASK;
        /* Store new index */
        USART_tx_tail = tmptail;
        /* Start transmission */
        USART.TXDATAL = USART_tx_buff[tmptail];

        USART_tx_elements--;
    }

    if (USART_tx_elements == 0)
    {
        /* Disable Tx interrupt */
        USART.CTRLA &= ~(1 << USART_DREIE_bp);
    }
}

ISR(USART_TXC_vect)
{
    USART.STATUS |= USART_TXCIF_bm;
}
