/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcStreamPort.h
 *
 * This file defines the trace streaming interface used by the 
 * Trace Recorder Library. It comes preconfigured for use with SEGGER's RTT and
 * a TCP/IP (needs additional configuration in trcTCPIPConfig.h).
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
 *
 * Disclaimer
 * The trace tool and recorder library is being delivered to you AS IS and
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does
 * not and cannot warrant the performance or results you may obtain by using the
 * software or documentation. Percepio AB make no warranties, express or
 * implied, as to noninfringement of third party rights, merchantability, or
 * fitness for any particular purpose. In no event will Percepio AB, its
 * technology partners, or distributors be liable to you for any consequential,
 * incidental or special damages, including any lost profits or lost savings,
 * even if a representative of Percepio AB has been advised of the possibility
 * of such damages, or for any claim by any third party. Some jurisdictions do
 * not allow the exclusion or limitation of incidental, consequential or special
 * damages, or the exclusion of implied warranties or limitations on how long an
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#ifndef _TRC_STREAM_PORT_H
#define _TRC_STREAM_PORT_H

#ifdef __cplusplus
extern “C” {
#endif

#if (USE_TRACEALYZER_RECORDER == 1)

#define TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK	(0x01)
#define TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_NOBLOCK	(0x02)
#define TRC_RECORDER_TRANSFER_METHOD_TCPIP		(0x03)
#define TRC_RECORDER_TRANSFER_METHOD_CUSTOM		(0xFF)

#define TRC_RECORDER_BUFFER_ALLOCATION_STATIC   (0x00)
#define TRC_RECORDER_BUFFER_ALLOCATION_DYNAMIC  (0x01)

/*******************************************************************************
 *   TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK / NOBLOCK
 ******************************************************************************/
#if TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK || TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_NOBLOCK

#if TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK
#define TRC_STREAM_PORT_BLOCKING_TRANSFER 1
#define RTT_MODE SEGGER_RTT_MODE_BLOCK_IF_FIFO_FULL
#else
#define TRC_STREAM_PORT_BLOCKING_TRANSFER 0
#define RTT_MODE SEGGER_RTT_MODE_NO_BLOCK_SKIP
#endif

#include "SEGGER_RTT_Conf.h"
#include "SEGGER_RTT.h"

/* Up-buffer. If index is defined as 0, the internal RTT buffers will be used instead of this. */ \
#if TRC_RTT_UP_BUFFER_INDEX == 0
#define TRC_RTT_ALLOC_UP() static char* _TzTraceData = NULL;    /* Not actually used. Ignore allocation method. */
#define TRC_STREAM_PORT_MALLOC() /* Static allocation. Not used. */
#else
#if TRC_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC
#define TRC_RTT_ALLOC_UP() static char _TzTraceData[BUFFER_SIZE_UP];    /* Static allocation */
#define TRC_STREAM_PORT_MALLOC() /* Static allocation. Not used. */
#else
#define TRC_RTT_ALLOC_UP() static char* _TzTraceData = NULL;    /* Dynamic allocation */
#define TRC_STREAM_PORT_MALLOC() _TzTraceData = TRC_PORT_MALLOC(BUFFER_SIZE_UP);
#endif
#endif

/* Down-buffer. If index is defined as 0, the internal RTT buffers will be used instead of this. */ \
#if TRC_RTT_DOWN_BUFFER_INDEX == 0
#define TRC_RTT_ALLOC_DOWN() static char* _TzCtrlData = NULL;           /* Not actually used. Ignore allocation method. */
#else
#define TRC_RTT_ALLOC_DOWN() static char _TzCtrlData[BUFFER_SIZE_DOWN]; /* This buffer should be ~32bytes. Ignore allocation method. */
#endif
  
#define TRC_STREAM_PORT_ALLOCATE_FIELDS() \
	TRC_RTT_ALLOC_UP() /* Macro that will result in proper UP buffer allocation */ \
	TRC_RTT_ALLOC_DOWN() /* Macro that will result in proper DOWN buffer allocation */

#define TRC_STREAM_PORT_INIT() \
        TRC_STREAM_PORT_MALLOC(); /*Dynamic allocation or empty if static */ \
	SEGGER_RTT_ConfigUpBuffer(TRC_RTT_UP_BUFFER_INDEX, "TzData", _TzTraceData, sizeof(_TzTraceData), RTT_MODE ); \
	SEGGER_RTT_ConfigDownBuffer(TRC_RTT_DOWN_BUFFER_INDEX, "TzCtrl", _TzCtrlData, sizeof(_TzCtrlData), 0);

#define TRC_STREAM_PORT_ALLOCATE_EVENT(_type, _ptrData, _size) uint8_t tmpEvt[_size]; _type* _ptrData = (_type*)tmpEvt;
#define TRC_STREAM_PORT_COMMIT_EVENT(_ptrData, _size) SEGGER_RTT_Write(TRC_RTT_UP_BUFFER_INDEX, (const char*)_ptrData, _size);
#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) *_ptrBytesRead = SEGGER_RTT_Read(TRC_RTT_DOWN_BUFFER_INDEX, (char*)_ptrData, _size);
#define TRC_STREAM_PORT_PERIODIC_SEND_DATA(_ptrBytesSent)

#define TRC_STREAM_PORT_ON_TRACE_BEGIN() /* Do nothing */
#define TRC_STREAM_PORT_ON_TRACE_END() /* Do nothing */
    
#endif /*TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_BLOCK || TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_JLINK_RTT_NOBLOCK*/

/*******************************************************************************
 *   TRC_RECORDER_TRANSFER_METHOD_TCPIP
 * 
 * This TCP/IP implementation is using a secondary buffer consisting of multiple 
 * pages to avoid the endless recursive calls that occurr when "socket_send" 
 * uses kernel objects such as mutexes and semaphores, which in turn needs to be
 * traced. To use your own TCP/IP stack, modify the functions declared in
 * trcTCPIPConfig.h.
 ******************************************************************************/
#if TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_TCPIP

#include "trcTCPIP.h"
#include "trcPagedEventBuffer.h"
#include "trcPagedEventBufferConfig.h"
#define TRC_STREAM_PORT_BLOCKING_TRANSFER 0

#if TRC_RECORDER_BUFFER_ALLOCATION == TRC_RECORDER_BUFFER_ALLOCATION_STATIC
#define TRC_STREAM_PORT_ALLOCATE_FIELDS() static char _TzTraceData[TRC_PAGED_EVENT_BUFFER_PAGE_COUNT * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE];       /* Static allocation. */
#define TRC_STREAM_PORT_MALLOC() /* Static allocation. Not used. */
#else
#define TRC_STREAM_PORT_ALLOCATE_FIELDS() static char* _TzTraceData = NULL;     /* Dynamic allocation. */
#define TRC_STREAM_PORT_MALLOC() _TzTraceData = TRC_PORT_MALLOC(TRC_PAGED_EVENT_BUFFER_PAGE_COUNT * TRC_PAGED_EVENT_BUFFER_PAGE_SIZE);
#endif

#define TRC_STREAM_PORT_INIT() \
        TRC_STREAM_PORT_MALLOC(); /*Dynamic allocation or empty if static */ \
        vPagedEventBufferInit(_TzTraceData);

#define TRC_STREAM_PORT_ALLOCATE_EVENT(_type, _ptrData, _size) _type* _ptrData; _ptrData = (_type*)vPagedEventBufferGetWritePointer(_size);
#define TRC_STREAM_PORT_COMMIT_EVENT(_ptrData, _size) /* Not needed since we write immediately into the buffer received above by TRC_STREAM_PORT_ALLOCATE_EVENT, and the TRC_STREAM_PORT_PERIODIC_SEND_DATA defined below will take care of the actual trace transfer. */
#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) trcTcpRead(_ptrData, _size, _ptrBytesRead);
#define TRC_STREAM_PORT_PERIODIC_SEND_DATA(_ptrBytesSent) vPagedEventBufferTransfer(trcTcpWrite, _ptrBytesSent);

#define TRC_STREAM_PORT_ON_TRACE_BEGIN() vPagedEventBufferInit(_TzTraceData);
#define TRC_STREAM_PORT_ON_TRACE_END() /* Do nothing */

#endif /*TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_TCPIP*/

/*******************************************************************************
 *   TRC_RECORDER_TRANSFER_METHOD_CUSTOM
 *
 * Implement the following macros in trcConfig.h. If your transfer method uses
 * kernel objects when sending data you will need to use a secondary buffer to 
 * store the trace data before sending it. For this reason we provide 
 * trcPagedEventBuffer. Look at the TCP/IP macros above to see how to use it.
 ******************************************************************************/
#if TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_CUSTOM

/* When using the custom transfer method, define TRC_STREAM_CUSTOM_XXXXXXXXXXXXX in trcConfig.h */
#define TRC_STREAM_PORT_BLOCKING_TRANSFER TRC_STREAM_CUSTOM_BLOCKING_TRANSFER
#define TRC_STREAM_PORT_ALLOCATE_FIELDS() TRC_STREAM_CUSTOM_ALLOCATE_FIELDS()
#define TRC_STREAM_PORT_INIT() TRC_STREAM_CUSTOM_INIT()
#define TRC_STREAM_PORT_ALLOCATE_EVENT(_type, _ptr, _size) TRC_STREAM_CUSTOM_ALLOCATE_EVENT(_type, _ptr, _size)
#define TRC_STREAM_PORT_COMMIT_EVENT(_ptr, _size) TRC_STREAM_CUSTOM_COMMIT_EVENT(_ptr, _size)
#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) TRC_STREAM_CUSTOM_READ_DATA(_ptrData, _size, _ptrBytesRead)
#define TRC_STREAM_PORT_PERIODIC_SEND_DATA(_ptrBytesSent) TRC_STREAM_CUSTOM_PERIODIC_SEND_DATA(_ptrBytesSent)
#define TRC_STREAM_PORT_ON_TRACE_BEGIN() TRC_STREAM_CUSTOM_ON_TRACE_BEGIN()
#define TRC_STREAM_PORT_ON_TRACE_END() TRC_STREAM_CUSTOM_ON_TRACE_END()

#endif /*TRC_RECORDER_TRANSFER_METHOD == TRC_RECORDER_TRANSFER_METHOD_CUSTOM*/

#ifndef TRC_STREAM_PORT_ALLOCATE_FIELDS
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_ALLOCATE_FIELDS!"
#endif

#ifndef TRC_STREAM_PORT_ALLOCATE_EVENT
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_ALLOCATE_EVENT!"
#endif

#ifndef TRC_STREAM_PORT_COMMIT_EVENT
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_COMMIT_EVENT!"
#endif

#ifndef TRC_STREAM_PORT_INIT
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_INIT!"
#endif

#ifndef TRC_STREAM_PORT_BLOCKING_TRANSFER
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_BLOCKING_TRANSFER!"
#endif

#ifndef TRC_STREAM_PORT_READ_DATA
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_READ_DATA!"
#endif

#ifndef TRC_STREAM_PORT_PERIODIC_SEND_DATA
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_PERIODIC_SEND_DATA!"
#endif

#ifndef TRC_STREAM_PORT_ON_TRACE_BEGIN
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_ON_TRACE_BEGIN!"
#endif

#ifndef TRC_STREAM_PORT_ON_TRACE_END
#error "Selected TRC_RECORDER_TRANSFER_METHOD does not define TRC_STREAM_PORT_ON_TRACE_END!"
#endif

#endif /*(USE_TRACEALYZER_RECORDER == 1)*/

#ifdef __cplusplus
}
#endif

#endif /* _TRC_STREAM_PORT_H */
