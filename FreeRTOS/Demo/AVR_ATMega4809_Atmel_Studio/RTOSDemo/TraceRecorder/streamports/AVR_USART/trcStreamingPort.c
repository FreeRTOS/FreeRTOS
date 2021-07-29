/*
 *
 (c) 2018 Microchip Technology Inc. and its subsidiaries.

 Subject to your compliance with these terms,you may use this software and
 any derivatives exclusively with Microchip products.It is your responsibility
 to comply with third party license terms applicable to your use of third party
 software (including open source software) that may accompany Microchip software.

 THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER
 EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED
 WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A
 PARTICULAR PURPOSE.

 IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
 INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
 WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
 BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO THE
 FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN
 ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY,
 THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
 *
 */
#include "trcRecorder.h"
#include <avr/interrupt.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)
#if(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifdef USART_BAUD_RATE
#undef USART_BAUD_RATE
#endif
#define USART_BAUD_RATE(BAUD_RATE) ( ( float ) ( configCPU_CLOCK_HZ * 64 / ( 8 * ( float ) BAUD_RATE ) ) + 0.5 )

void usart_init(void)
{
    USART_cfg_t cfg;
    USART_initConfigs(&cfg);

    cfg.BAUD = (uint16_t)USART_BAUD_RATE(460800);

    //RXCIE enabled; TXCIE enabled; DREIE disabled; RXSIE enabled; LBME disabled; ABEIE disabled; RS485 DISABLE;
    cfg.CTRLA = 0xC0;

    //RXEN enabled; TXEN enabled; SFDEN disabled; ODME disabled; RXMODE NORMAL; MPCM disabled;
    cfg.CTRLB = 0xC0;
    cfg.CTRLB |= USART_RXMODE_CLK2X_gc;//enable doublespeed mode

    //CMODE ASYNCHRONOUS; PMODE DISABLED; SBMODE 1BIT; CHSIZE 8BIT; UDORD disabled; UCPHA disabled;
    cfg.CTRLC = 0x03;

    //DBGCTRL_DBGRUN
    cfg.DBGCTRL = USART_DBGRUN_bm;

    //EVCTRL_IREI
    cfg.EVCTRL = 0x00;

    USART_setConfigs(cfg);
}

/* The READ function, used in trcStreamingPort.h */
int32_t usart_rx_pkt(void *data, uint32_t size, int32_t* NumBytes)
{
    uint8_t *rx_buff = (uint8_t *)data;

    if (USART_getRxElements() < size) return 0;
    
    *NumBytes=size;
    
    for (;size>0;size--)
    {
        *rx_buff = USART_read();
        rx_buff++;
    }
    return 0;
}

#if (TRC_UART_INT_MODE == 1)

/* The WRITE function, used in trcStreamingPort.h */
int32_t usart_tx_pkt(void* data, uint32_t size, int32_t * noOfBytesSent )
{
    uint8_t * data_ptr = (uint8_t *)data;

    *noOfBytesSent=size;
    for (;size > 0; size--)
    {
        USART_write( *data_ptr);
        data_ptr++;
    }
    return 0;
}
#else

/* The WRITE function, used in trcStreamingPort.h */
int32_t usart_tx_pkt(void* data, uint32_t size, int32_t * noOfBytesSent )
{
    uint8_t * data_ptr = (uint8_t *)data;
    *noOfBytesSent=size;
    for (;size > 0; size--)
    {
        USART_blocking_write(*data_ptr);
        data_ptr++;
    }
    return 0;
}
#endif

#endif  /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/
#endif  /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/
