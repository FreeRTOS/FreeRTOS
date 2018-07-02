-------------------------------------------------------------------------------
          Tracealyzer Recorder Library v4.1.0 for FreeRTOS
-------------------------------------------------------------------------------

Tracealyzer is a sophisticated tool for tracing and visualization
of FreeRTOS-based software systems.

Tracealyzer gives an unprecedented insight into the runtime behavior, which 
speeds up debugging, validation and optimization. 

This, the Trace Recorder Library, is the target-side part of Tracealyzer, that
performs the actual tracing. The resulting data can then be viewed in the
Tracealyzer PC application, found at https://percepio.com/tracealyzer

To learn more, see these links.

 - Getting Started (videos etc): https://percepio.com/gettingstarted

 - FAQ: https://percepio.com/category/faq

In case you have any questions, don't hesitate to contact support@percepio.com

Tracealyzer supports FreeRTOS v7.3 and newer, including Amazon FreeRTOS.

-------------------------------------------------------------------------------

Changes, v4.0.3 -> v4.1.0

- Improved performance of User Events
- Fixed handling of format strings ending with '%'
- Improved handling of creative user configuration macros

-------------------------------------------------------------------------------

Changes, v4.0.2 -> v4.0.3

- Minor fix for TCP/IP stream port.
- Corrected default RTT mode setting.

-------------------------------------------------------------------------------

Changes, v4.0.1 -> v4.0.2

- Memory allocation trace events now ignore filters.

-------------------------------------------------------------------------------

Changes, v4.0.0 -> v4.0.1

- Minor fixes to default values.

-------------------------------------------------------------------------------

Changes, v3.3.0 -> v4.0.0

- Fixed some issues with filters.

-------------------------------------------------------------------------------

Changes, v3.2.0 -> v3.3.0

- Added support for FreeRTOS v10, including the new object types Message Buffer
  and Stream Buffer.

- Improved the object-level filtering to also support Timer, Event Group, 
  Message Buffer and Stream Buffer objects.

- Fixed a few remaining build problems with older FreeRTOS versions (v7.x).

- vTraceStoreISRBegin now reports an error on invalid handles, i.e., if the 
  initialization of the handle (xTraceSetISRProperties) had not been made.

-------------------------------------------------------------------------------

Changes, v3.1.2 -> v3.2.0

- Added new filtering system - that works in both snapshot and streaming mode.
  Filtering was previously not supported in streaming mode, but can be very
  useful for slower streaming interfaces. By exluding irrelevant events, the
  amount of data produced can be reduced a lot.

    * New functions vTraceSetFilterGroup and vTraceSetFilterMask allows for
      excluding all events from specific objects (like a semaphore or queue).

    * Added new "generic" filters (preprocessor level) to trcConfig.h, that
      exclude all events of a particular types.
      - TRC_CFG_INCLUDE_NOTIFY_EVENTS
      - TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS
      - TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS
      - TRC_CFG_INCLUDE_TIMER_EVENTS

    * Upgraded some previous filters from "Snapshot only" to the Common API 
      and thereby moved them from trcSnapshotConfig.h to trcConfig.h.
       - TRC_CFG_SCHEDULING_ONLY
       - TRC_CFG_INCLUDE_MEMMANG_EVENTS
       - TRC_CFG_INCLUDE_USER_EVENTS
       - TRC_CFG_INCLUDE_ISR_TRACING
       - TRC_CFG_INCLUDE_READY_EVENTS
       - TRC_CFG_INCLUDE_OSTICK_EVENTS

    * Removed the old filter system from trcSnapshotRecorder.c.

- Improved streaming interface - Now only two (2) macros are needed to be 
  defined in most cases, read and write. This makes it a lot easier to make
  custom stream ports.

    * Many definitions that were identical in most stream ports, have been
      replaced by default definitions in the recorder core. If needed, they
      can be overriden by custom definitions in trcStreamingPort.h.

    * Stream ports are now assumed to use recorder's internal event buffer.
      Other stream ports that writes directly to the streaming interface
      (like J-Link) should define TRC_STREAM_PORT_USE_INTERNAL_BUFFER
      as zero (0) to make it work correctly.

    * Macro TRC_STREAM_PORT_PERIODIC_SEND_DATA has been replaced by
      TRC_STREAM_PORT_WRITE_DATA. Together with TRC_STREAM_PORT_READ_DATA,
      this is all that is necessary for a typical stream port.

    * Return values from the stream port macros READ_DATA and WRITE_DATA are
      now checked. Expects 0 on success, anything else produces a warning
      that can be retrived using xTraceGetLastError() and also seen in
      Tracealyzer if a trace was produced.

    * Stream ports should no longer call prvPagedEventBufferInit explicitly
      (e.g. in TRC_STREAM_PORT_ON_TRACE_BEGIN). This is now called 
      automatically if TRC_STREAM_PORT_USE_INTERNAL_BUFFER == 1.

    * Macros TRC_STREAM_PORT_ON_TRACE_BEGIN and TRC_STREAM_PORT_ON_TRACE_END
      are now unused by default and don't need to be defined.
      You can however use them to hook in some own function at these events.

- Added two new stream ports

    * TCPIP-Win32: allows for testing the streaming on Windows ports of your
      RTOS, using Winsock.

    * File: example of streaming to a local file system (tested on Windows,
      but easy to modify).

- Added support for FreeRTOS v9.0.1

    * Replaced FreeRTOS version code TRC_FREERTOS_VERSION_9_X with
      - TRC_FREERTOS_VERSION_9_0_0
      - TRC_FREERTOS_VERSION_9_0_1

    * Using TRC_FREERTOS_VERSION_9_X is no longer allowed.

- Added additional events for xQueuePeek, for blocking and timeouts events.

- Added event for traceTIMER_EXPIRED, showing when the timer callback
  function is called.

- Improved diagnostics in streaming mode, in case of errors in the recorder.

    * Added prvTraceWarning() - registers a "warning" error code, without
      stopping the recorder. Called if READ_DATA or WRITE_DATA returns a
      non-zero value, and in several other cases where the recorder 
      configuration is incorrect (e.g., too small symbol table). 

    * Added several new warning codes (PSF_WARNING_XYZ), corresponding to the
    issues detected by prvCheckRecorderStatus.

    * Fixed duplicate definitions of warning messages, so the warnings reported
      to Tracealyzer are the same as those provided in xTraceGetLastError().

    * Added better explainations of warning/error messages in the body of
      xTraceGetLastError (in streaming mode).

- Added xTraceIsRecordingEnabled() to Common API.

- Added "unofficial" hardware port for Altera Nios-II. 
  This is a user contribition, not yet verified by Percerpio.

- Fixed bug in vTraceEnable - option TRC_START_AWAIT_HOST was ignored if already initialized. 

- Fixed a few remaining compiler warnings.

- Changed order of some settings in trcConfig.h - moved advanced stuff to the
  bottom.

- Removed SEGGER_RTT_Printf.c from the J-Link stream port since not required
  for Tracealyzer.

-------------------------------------------------------------------------------

Changes, v3.1.1 -> v3.1.2
- Fixed two bugs related to User Events, one in vTracePrintF and other in vTracePrint.

- Fixed a build problem related to a single reference of the old FreeRTOS type "xTaskHandle", in trcKernelPort.c.
  Changed to "TaskHandle_t", unless if using an older FreeRTOS kernel or the "compatibility mode".

- Removed traceCREATE_MUTEX hook for FreeRTOS v9 or later (no longer required)

- Updated the User Manual regarding snapshot trace via IAR Embedded Workbench.

- Renamed vTraceGetTraceBuffer to xTraceGetTraceBuffer, since returning a pointer.

-------------------------------------------------------------------------------

Changes, v3.1.0 -> v3.1.1

After the major changes in the v3.1.0 trace recorder library, this update 
corrects a number of minor issues. Only minor functional improvements.

- You can now use TRC_ALLOC_CUSTOM_BUFFER to declare a trace buffer on a custom
  location (using linker directives). 
  The related function vTraceSetRecorderDataBuffer has been promoted to the
  Common API (previously only supported in snapshot mode, but custom allocation
  is now generally supported also in streaming mode).
  
- Removed TRC_CFG_USE_LINKER_PRAGMA. No longer necessary thanks to the custom
  allocation mode.
  
- Added support for timestamping from custom periodic timers, required for
  accurate timestamping on Cortex-M0/M0+ devices when using tickless idle.
  Only for streaming mode so far. See TRC_CUSTOM_TIMER_INCR / DECR.

- ARM Cortex-M port: Made sure the DWT unit is initialized properly, in case
  the debugger doesn't handle this.

- ARM Cortex-M port: Added possibility to use Systick timestamping also on
  Cortex-M3/M4/M7 devices (that otherwise use DWT timestamping by default).
  To use this option, define the macro TRC_CFG_ARM_CM_USE_SYSTICK.

- J-Link streaming: The default RTT buffer has been changed from 0 to 1.

- J-Link streaming: The RTT buffer settings for buffer 1 and higher, are now
  found in trcStreamingPort.h. Note: These settings don't apply to buffer 0.

- vTracePrint has been optimized for better performance in string logging.

- Minor performance improvement related to symbol table transfer in streaming mode.

- Timer names now registered also in streaming mode.

- Timer start and stop event are now traced.

- Implemented support for queue registry (traceQUEUE_REGISTRY_ADD) also for streaming.

- Fixed a bug related to repeated calls of vTraceEnable.

- Fixed a bug where task-switches seemed to occur even though the scheduler was disabled.

- Renamed HARDWARE_PORT_TEXAS_INSTRUMENTS_TMS570_RM48, added prefix TRC.

- Fixed several language issues in the comments and documentation.

- Fixed several minor issues and warnings from different compilers
 (including PowerPC/gcc) and configurations.

-------------------------------------------------------------------------------
 
Changes, v3.0.9 -> v3.1.0

- Merge of previously separated snapshot and streaming recorders into a single
  recorder supporting both streaming and snapshot as different modes.
  
- New common API for supporting both streaming and snapshot modes.
  
- New integration guide, see the User Manual.

- Major improvement of API documentation in source files and User Manual.
  
- New concept of "stream ports", giving a better structure defining streaming
  interfaces, and restructured the J-Link and TCP/IP streaming as stream ports.
  
- Added a stream port for USB CDC connections, with STM32 as example.
  Since Tracealyzer now can receive serial data on Windows COM ports, this is
  really easy to use.

- Added a warning (#error) for cases where FreeRTOS tickless idle mode is used
  together with timestamping using SysTick or other periodic interrupt timers,
  Tracing with tickless idle requires an independent time source to correctly
  capture the length of the idle periods.
 
- Major changes in the recorder API. Important examples are:

  * Some configuration macros have changed names, e.g. for "hardware port".
    Make sure to remove any old "trcConfig.h" files if upgrading from an
    earlier version!

  * Recorder configuration in trcConfig.h has been minimized and now only 
    includes the important settings that are independent of recorder mode.
    Advanced settings for each mode are found in trcSnapshotConfig.h and
    trcStreamingConfig.h.
        
  * vTraceEnable replaces Trace_Init and vTraceInitTraceData, as well as
    vTraceStart and uiTraceStart.
  
  * vTraceStop now part of the common API and thereby available also in
    streaming. And since vTraceEnable can start the streaming directly
    you have the option control the tracing from target, e.g., for
    streaming to a device file system.
  
  * vTraceStoreKernelObjectName from old streaming recorder has been replaced
    by vTraceSetQueueName, vTraceSetSemaphoreName, etc.
     
  * vTraceSetISRProperties now returns a "traceHandle" that should be passed as
    parameter to vTraceStoreISRBegin and vTraceStoreISREnd.
    
  * xTraceRegisterString has replaced the old functions xTraceOpenLabel and 
    vTraceStoreUserEventChannelName. This now returns a "traceString" for use
    as "channel" parameter in vTracePrintF, and in other places where strings
    are stored.
    
  * Removed vTraceStoreISREndManual and vTraceStoreISREndAuto, use
    vTraceStoreISREnd instead.
  
  * Renamed the functions for saving User Events in a separate buffer:
     - xTraceRegisterChannelFormat  -> xTraceRegisterUBChannel
     - vTraceChannelPrintF          -> vTraceUBData
     - vTraceChannelUserEvent       -> vTraceUBEvent
  
 
-------------------------------------------------------------------------------
Copyright Percepio AB, 2018. 