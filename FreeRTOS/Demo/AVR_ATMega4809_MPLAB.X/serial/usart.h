#ifndef USART_H
#define USART_H

#include <stdint.h>

#define USART_INSTANCE  3

#define USART_BAUD_RATE(BAUD_RATE)    ( ( float ) ( configCPU_CLOCK_HZ * 64 / ( 16 * ( float ) BAUD_RATE ) ) + 0.5 )

typedef struct USART_cfg_t
{
    uint8_t CTRLA;
    uint8_t CTRLB;
    uint8_t CTRLC;
    uint16_t BAUD;
    uint8_t CTRLD;
    uint8_t DBGCTRL;
    uint8_t EVCTRL;
} USART_cfg_t;

void USART_initialize(void *rxBuffer, uint16_t rxSize, void *txBuffer, uint16_t txSize, unsigned long baudrate);
void USART_close(void);

void USART_setConfigs(USART_cfg_t cfg);
void USART_initConfigs(USART_cfg_t *cfg);

void USART_write(const uint8_t data);
uint8_t USART_read(void);

uint8_t USART_isTxReady(void);
uint8_t USART_isRxReady(void);

uint16_t USART_getRxElements(void);
uint16_t USART_getTxElements(void);

#endif /* USART_H */
