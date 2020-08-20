/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.3.11
 * Percepio AB, www.percepio.com
 *
 * trcStreamingPort.h
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use ARM ITM as streaming channel.
 *
 * To setup Keil uVision for ITM tracing with a Keil ULINKpro (or ULINKplus),
 * see Percepio Application Note PA-021, available at
 * https://percepio.com/2018/05/04/keil-itm-support/
 * 
 * To setup IAR Embedded Workbench for ITM tracing with an IAR I-Jet,
 * see Percepio Application Note PA-023, https://percepio.com/iar
 *
 * NOTE: This stream port may block the application in case the ITM port
 * is not ready for more data (the TPIU FIFO has become full). This is
 * necessary to avoid data loss, as the TPIU FIFO is often quite small.
 *
 * --- Direct vs. Indirect ITM streaming ---
 * Direct streaming: By default, this stream port writes directly to the ITM
 * register mode without any RAM buffer. This assumes you have a fast debug
 * probe, like aKeil ULINKpro or IAR I-Jet, to avoid excessive blocking.
 * In case the ITM blocking appears to disturb your application, make sure your
 * debugger is configured for maximum performance, as described in the above
 * Application Nodes.
 *
 * Indirect streaming: If direct streaming gives too much overhead, you may
 * instead try indirect ITM streaming. This is done by enabling the internal
 * RAM buffer, like below. This reconfigures the recorder to store the events
 * in the internal RAM buffer instead of writing them directly to the ITM port.
 * 
 * Set TRC_STREAM_PORT_USE_INTERNAL_BUFFER to 1 to use the indirect mode.
 *
 * This increases RAM usage but eliminates peaks in the trace data rate.
 * Moreover, the ITM writes are then performed in a separate task (TzCtrl).
 * You find relevant settings (buffer size etc.) in trcStreamingConfig.h.
 *
 * See also https://percepio.com/2018/10/11/tuning-your-custom-trace-streaming 
 *
 * --- One-way vs. Two-way Communication ---
 * The ITM port only provides one-way communication, from target to host.  
 * This is sufficient if you start the tracing from the target application,
 * using vTraceEnable(TRC_START). Just make sure to start the Tracealyzer
 * recording before you start the target system.
 *
 * In case you prefer to interactively start and stop the tracing from the host
 * computer, you need two-way communication to send commands to the recorder.
 * This is possible by writing such "start" and "stop" commands to a special
 * buffer, monitored by the recorder library, using the debugger IDE. 
 * See trcStreamingPort.c and also the example macro for Keil uVision 
 * (Keil-uVision-Tracealyzer-ITM-Exporter.ini).
 *
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
 * Copyright Percepio AB, 2018.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_STREAMING_PORT_H
#define TRC_STREAMING_PORT_H

#ifdef __cplusplus
extern "C" {
#endif


int32_t itm_write(void* ptrData, uint32_t size, int32_t* ptrBytesWritten);
int32_t read_from_host(void* ptrData, uint32_t size, int32_t* ptrBytesRead);

/*******************************************************************************
 * TRC_CFG_ITM_PORT
 *
 * Possible values: 0 - 31
 *
 * What ITM port to use for the ITM software events. Make sure the IDE is
 * configured for the same channel.
 *
 * Default: 1 (0 is typically terminal output and 31 is used by Keil)
 *
 ******************************************************************************/
#define TRC_CFG_ITM_PORT 1

#if (TRC_CFG_ITM_PORT < 0) || (TRC_CFG_ITM_PORT > 31)
#error "Bad ITM port selected."
#endif

// Not used for ITM - no RAM buffer...
#define TRC_STREAM_PORT_ALLOCATE_FIELDS()

// Not used for ITM - assume the IDE configures the ITM setup
#define TRC_STREAM_PORT_INIT()

/* Important for the ITM port - no RAM buffer, direct writes. In most other ports this can be skipped (default is 1) */
#define TRC_STREAM_PORT_USE_INTERNAL_BUFFER 0
  
#define TRC_STREAM_PORT_WRITE_DATA(_ptrData, _size, _ptrBytesWritten) itm_write(_ptrData, _size, _ptrBytesWritten)

#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) read_from_host(_ptrData, _size, _ptrBytesRead)

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAMING_PORT_H */
