/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.4.0
 * Percepio AB, www.percepio.com
 *
 * trcStreamingPort.c
 *
 * Supporting functions for trace streaming, used by the "stream ports" 
 * for reading and writing data to the interface.
 * Existing ports can easily be modified to fit another setup, e.g., a 
 * different TCP/IP stack, or to define your own stream port.
 *
 * This stream port is for ITM streaming on Arm Cortex-M devices.
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

#include "trcRecorder.h"

#if (TRC_USE_TRACEALYZER_RECORDER == 1)
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

static void itm_write_32(uint32_t data);

/* These variables are used for reading commands from the host, using read_from_host().
 * This is not required if using vTraceEnable(TRC_START).
 * A debugger IDE may write to these functions using a macro. 
 * An example for Keil is included (Keil-uVision-Tracealyzer-ITM-Exporter.ini). */
 
volatile int32_t tz_host_command_bytes_to_read = 0;
volatile char tz_host_command_data[32];

/* This reads "command" data from a RAM buffer, written by a host macro in the debugger */
int32_t read_from_host(void* ptrData, uint32_t size, int32_t* ptrBytesRead)
{
	if ( tz_host_command_bytes_to_read > 0)
	{		
		int i;
		uint8_t * bytesBuffer = (uint8_t*) ptrData;

		if (ptrBytesRead != NULL)
			*ptrBytesRead = (int32_t)tz_host_command_bytes_to_read;
	
		if (tz_host_command_bytes_to_read != size)
		{
			return -1;
		}
			
		for (i=0; i < tz_host_command_bytes_to_read; i++)
		{
			bytesBuffer[i] = tz_host_command_data[i];
		}
		
		tz_host_command_bytes_to_read = 0;
	}

	return 0;
}

static void itm_write_32(uint32_t data)
{	
     if   ((CoreDebug->DEMCR & CoreDebug_DEMCR_TRCENA_Msk)  &&      // Trace enabled
           (ITM->TCR & ITM_TCR_ITMENA_Msk)                  &&      // ITM enabled
           (ITM->TER & (1UL << TRC_CFG_ITM_PORT)))                  // ITM port enabled
    {
        while (ITM->PORT[TRC_CFG_ITM_PORT].u32 == 0);     // Block until room in ITM FIFO - This stream port is always in "blocking mode", since intended for high-speed ITM!
        ITM->PORT[TRC_CFG_ITM_PORT].u32 = data;           // Write the data
	}	
}

/* This is assumed to execute from within the recorder, with interrupts disabled */
int32_t itm_write(void* ptrData, uint32_t size, int32_t* ptrBytesWritten)
{
	uint32_t bytesWritten = 0;
	uint32_t* ptr32 = (uint32_t*)ptrData;
	
	if (size % 4 != 0) return -2;
		
	while(bytesWritten < size)
	{
		itm_write_32(*ptr32);
		ptr32++;
		bytesWritten += 4;
	}

	*ptrBytesWritten = bytesWritten;
	
	return 0;
}

#endif
#endif
