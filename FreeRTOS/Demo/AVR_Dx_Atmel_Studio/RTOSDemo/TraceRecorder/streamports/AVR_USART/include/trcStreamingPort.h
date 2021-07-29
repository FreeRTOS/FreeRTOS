/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.2.0
 * Percepio AB, www.percepio.com
 *
 * trcStreamingPort.h
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use USB CDC as streaming channel.
 * The example is for STM32 using STM32Cube.
 *
 * Terms of Use
 * This file is part of the trace recorder library (RECORDER), which is the
 * intellectual property of Percepio AB (PERCEPIO) and provided under a
 * license as follows.
 * The RECORDER may be used free of charge for the purpose of recording data
 * intended for analysis in PERCEPIO products. It may not be used or modified
 * for other purposes without explicit permission from PERCEPIO.
 * You may distribute the RECORDER in its original source code form, assuming
 * this text (terms of use, disclaimer, copyright notice) is unchanged. You are
 * allowed to distribute the RECORDER with minor modifications intended for
 * configuration or porting of the RECORDER, e.g., to allow using it on a
 * specific processor, processor family or with a specific communication
 * interface. Any such modifications should be documented directly below
 * this comment block.
 *
 * Disclaimer
 * The RECORDER is being delivered to you AS IS and PERCEPIO makes no warranty
 * as to its use or performance. PERCEPIO does not and cannot warrant the
 * performance or results you may obtain by using the RECORDER or documentation.
 * PERCEPIO make no warranties, express or implied, as to noninfringement of
 * third party rights, merchantability, or fitness for any particular purpose.
 * In no event will PERCEPIO, its technology partners, or distributors be liable
 * to you for any consequential, incidental or special damages, including any
 * lost profits or lost savings, even if a representative of PERCEPIO has been
 * advised of the possibility of such damages, or for any claim by any third
 * party. Some jurisdictions do not allow the exclusion or limitation of
 * incidental, consequential or special damages, or the exclusion of implied
 * warranties or limitations on how long an implied warranty may last, so the
 * above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2017.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_STREAMING_PORT_H
#define TRC_STREAMING_PORT_H

#ifdef __cplusplus
extern "C" {
#endif

#include "../../../../serial/usart.h"
    
/*******************************************************************************
 * Configuration Macro: TRC_UART_INT_MODE
 *
 * Defines if the USART Tx interrupts are used or not
 *  -  TRC_UART_INT_MODE = 0 - Tx interrupts are not used, the transmit is done  
 *            in pooling mode. TRC_CFG_USART_TX_BUFFER_SIZE is set to 1 to avoid 
 *            compiler warnings. This configuration will increase the CPU load for 
 *            trace task, but decrease the size of RAM required 
 *  -  TRC_UART_INT_MODE = 1 - Tx interrupts are used, the transmit is done in  
 *            interrupt mode. This configuration has a lower CPU load for 
 *            trace task, but increase the size of RAM required by application
******************************************************************************/ 
#define TRC_UART_INT_MODE         1

/*******************************************************************************
 * Configuration Macro: TRC_CFG_USART_TX_BUFFER_SIZE
 *
 * Defines the size of the USART TX buffer (target -> host) to use for writing
 * the trace data.
 *
 * The size is depending on the amount of data produced.
 ******************************************************************************/    
    
    
#if (TRC_UART_INT_MODE == 1)
#define TRC_CFG_USART_TX_BUFFER_SIZE       2048
#else
#define TRC_CFG_USART_TX_BUFFER_SIZE         8
#endif
    
#define TRC_CFG_USART_RX_BUFFER_SIZE         32
    
#if TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC
#define TRC_USART_ALLOC_TXBUFF() char _TzTraceData[TRC_CFG_USART_TX_BUFFER_SIZE];    /* Static allocation */
#define TRC_STREAM_PORT_MALLOC() /* Static allocation. Not used. */
#endif
#if TRC_CFG_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC
#define TRC_USART_ALLOC_TXBUFF() char* _TzTraceData = NULL;    /* Dynamic allocation */
#define TRC_STREAM_PORT_MALLOC() _TzTraceData = TRC_PORT_MALLOC(TRC_CFG_USART_TX_BUFFER_SIZE);
#endif

#define TRC_USART_ALLOC_RXBUFF() static char _TzCtrlData[TRC_CFG_USART_RX_BUFFER_SIZE]; /* Always static allocation, since usually small. */

  
#define TRC_STREAM_PORT_ALLOCATE_FIELDS() \
	TRC_USART_ALLOC_TXBUFF() /* Macro that will result in proper USART TX buffer allocation */ \
	TRC_USART_ALLOC_RXBUFF() /* Macro that will result in proper USART RX buffer allocation */

/* Important for the USART port, in most other ports this can be skipped (default is 1) */
#define TRC_STREAM_PORT_USE_INTERNAL_BUFFER 0
    
    
    
int32_t usart_rx_pkt(void *data, uint32_t size, int32_t* NumBytes);
int32_t usart_tx_pkt(void* data, uint32_t size, int32_t * noOfBytesSent );
void usart_init(void);

#define TRC_STREAM_PORT_INIT() \
        TRC_STREAM_PORT_MALLOC(); /*Dynamic allocation or empty if static */ \
        usart_init();                               \
        USART_initialize(_TzCtrlData, TRC_CFG_USART_RX_BUFFER_SIZE, _TzTraceData, TRC_CFG_USART_TX_BUFFER_SIZE, 460800);
        

#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) usart_rx_pkt(_ptrData, _size, _ptrBytesRead)
//#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) 0

#define TRC_STREAM_PORT_WRITE_DATA(_ptrData, _size, _ptrBytesSent) usart_tx_pkt(_ptrData, _size, _ptrBytesSent)

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAMING_PORT_H */