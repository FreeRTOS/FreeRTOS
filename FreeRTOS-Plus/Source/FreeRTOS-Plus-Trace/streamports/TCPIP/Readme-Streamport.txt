Tracealyzer Stream Port for TCP/IP (lwIP example)
Percepio AB
www.percepio.com
-------------------------------------------------

This directory contains a "stream port" for the Tracealyzer recorder library,
i.e., the specific code needed to use a particular interface for streaming a
Tracealyzer RTOS trace. The stream port is defined by a set of macros in
trcStreamPort.h, found in the "include" directory.

This particular stream port targets TCP/IP. This example assumes lwIP but is
easy to modify for other TCP/IP stacks.

Instructions:

1. Integrate the trace recorder and configure it for streaming, as described
   in the Tracealyzer User Manual. For FreeRTOS this is found at:
   https://percepio.com/docs/FreeRTOS/manual/index.html#Creating_and_Loading_Traces___Introduction

2. Make sure all .c and .h files from this stream port folder is included in 
   your build, and that no other variant of trcStreamPort.h is included.

3. In lwipopts.h, make sure you have this line:
   
   #define LWIP_SOCKET 1

4. Make sure that vTraceEnable(TRC_INIT) is called during the startup, before
   any RTOS calls are made.

5. In Tracealyzer, open File -> Settings -> PSF Streaming Settings and
   select Target Connection: TCP. Enter the IP address of the target system
   and the port number (by default 12000).

6. Start your target system, wait a few seconds to ensure that the lwIP is operational, 
   then select Start Recording in Tracealyzer.

Troubleshooting:

- If the tracing suddenly stops, check the "errno" value in trcSocketSend (trcStreamingPort.c).
You can see the error code definitions in lwip/errno.h. If errno is ENOMEM, may you need to 
increase MEM_SIZE in lwipopts.h.

- Since lwIP performs a lot of semaphore and mutex operations, we recommend filtering out 
such events from the trace, at least those caused by the transmission of trace data in the
TzCtrl task. This can be done using vTraceSetFilterGroup() and vTraceSetFilterMask().

Note that lwIP is not included in the stream port, but assumed to exist in the project already.

See also http://percepio.com/2016/10/05/rtos-tracing.
