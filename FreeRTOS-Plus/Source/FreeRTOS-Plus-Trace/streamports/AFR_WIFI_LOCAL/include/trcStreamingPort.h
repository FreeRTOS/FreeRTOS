/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.4.0
 * Percepio AB, www.percepio.com
 *
 * trcStreamingPort.c
 *
 * This stream port provides trace streaming using the Amazon FreeRTOS sockets
 * layer and is intended for streaming over Wifi directly to a computer on the
 * local Wifi network. 
 *
 * Note that this does NOT use the TLS encryption available in Amazon
 * FreeRTOS, due to performance and memory usage concerns. However, it does not
 * use any AWS services either, and is intended for your local network only.
 *
 * This should be started using vTraceEnable(TRC_START) and this call should be
 * made AFTER the kernel has started and the Wifi interface is ready.
 *
 * In the Tracealyzer setting -> "PSF Streaming Settings" make sure that the
 * "Target Connection" setting is "TCP (Target Initiated)".
 *
 * To use this, make sure to start the trace recording in Tracealyzer before
 * you start your target system. This ensures that Tracealyzer is ready when
 * the target system connects.
 *
 * And don't forget to enter the IP address of the Tracealyzer host computer
 * in trcStreamingPort.h.
 *
 * NOTES:
 *
 * 1: The tracing will increase the stack usage of you application, so you
 * may want to increase configMINIMAL_STACK_SIZE in your FreeRTOSConfig.h.
 *
 * 2: To reduce the amount of trace data, we recommend disabling the tracing
 * of OS Ticks and memory allocation events.
 * See TRC_CFG_INCLUDE_OSTICK_EVENTS in trcConfig.h.
 *
 * 3: The transmission of trace data is done in the TzCtrl task. To avoid that
 * the trace streaming is blocked during the (long) MQTT connection phase,
 * make sure the scheduling priority of TzCtrl is higher than the MQTT task.
 * Otherwise, if you prefer to run the TzCtrl task at lower priority to avoid
 * interfering with your application, wait with the vTraceEnable call until
 * after the MQTT connection is established.
 * See TRC_CFG_CTRL_TASK_PRIORITY in trcStreamingConfig.h.
 *
 * 4: The Wifi transmission of trace data often uses FreeRTOS functions, that
 * are traced and thus produce additional trace data. This may cause a fast
 * increase in trace data rate, that may saturate the trace buffer and cause
 * data loss (i.e. incomplete traces).
 * To eliminate this effect and reduce the amount of trace data produced, we
 * recommend excluding all FreeRTOS objects that are used by Wifi stack.
 * This is done using vTraceSetFilterGroup and vTraceSetFilterMask:
 *
 *   // Just before wifi initialization:
 *
 *   // All objects created after this point are assigned to group 15.
 *   vTraceSetFilterGroup(FilterGroup15);
 *
 *   // Only trace objects assigned to group 0 (the default group).
 *   vTraceSetFilterMask(FilterGroup0);
 *
 *   // The wifi stack initialization... (creates semaphores etc.)
 *   if ( eWifi_Connected == prvWifiConnect() )
 *   {
 *       yMainState = eMain_StartApplication;
 *
 *       // When connected, restore the FilterGroup setting to Group 0, so
 *       // that later created objects are included, like the TzCtrl task
 *       // created in vTraceEnable. Excluding tasks is not recommended!
 *       vTraceSetFilterGroup(FilterGroup0);
 *
 *       // Then call vTraceEnable to start the tracing.
 *       vTraceEnable(TRC_START);
 *   }
 *
 * 5: If you still get "red sections" in Tracealyzer (lost data), you need
 * to adjust the other settings in trcStreamingConfig.h.
 *
 *   - TRC_CFG_PAGED_EVENT_BUFFER_PAGE_COUNT
 *     Increase this, as long as you have memory to spare.
 *
 *   - TRC_CFG_PAGED_EVENT_BUFFER_PAGE_SIZE
 *     Increase this, as long as you have memory to spare.
 *     But don't exceed the maximum payload size of the Wifi chip, which
 *     is often limited to 1000-1500 bytes. Some chips crash if you try to
 *     send to large chunks...
 *
 *   - TRC_CFG_CTRL_TASK_DELAY
 *     Decrease this to flush the trace buffer more frequently.
 *
 * See also http://percepio.com/2016/10/05/rtos-tracing 
 * and https://percepio.com/2018/10/11/tuning-your-custom-trace-streaming/
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


#define HOST_IPADDRESS_0 192
#define HOST_IPADDRESS_1 168
#define HOST_IPADDRESS_2 10
#define HOST_IPADDRESS_3 116
#define HOST_PORT 12000

void prvInitSocket(void);
int32_t prvReadFromSocket(void* ptrData, uint32_t size, int32_t* ptrBytesRead);
int32_t prvWriteToSocket(void* ptrData, uint32_t size, int32_t* ptrBytesWritten);

#define TRC_STREAM_PORT_INIT() \
	TRC_STREAM_PORT_MALLOC(); \
	prvInitSocket();

#define TRC_STREAM_PORT_USE_INTERNAL_BUFFER 1
  
#define TRC_STREAM_PORT_WRITE_DATA(_ptrData, _size, _ptrBytesWritten) prvWriteToSocket(_ptrData, _size, _ptrBytesWritten)

#define TRC_STREAM_PORT_READ_DATA(_ptrData, _size, _ptrBytesRead) prvReadFromSocket(_ptrData, _size, _ptrBytesRead)

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAMING_PORT_H */
