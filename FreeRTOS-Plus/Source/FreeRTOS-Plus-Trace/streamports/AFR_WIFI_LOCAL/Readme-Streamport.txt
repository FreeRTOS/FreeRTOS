Tracealyzer Stream Port for Amazon FreeRTOS TCP/WIFI
----------------------------------------------------

This directory contains a "stream port" for the Tracealyzer recorder library,
i.e., the specific code needed to use a particular interface for streaming a
Tracealyzer RTOS trace. The stream port is defined by a set of macros in
trcStreamingPort.h, found in the "include" directory.

This particular stream port is for streaming via a TCP socket in Amazon
FreeRTOS (AFR) directly to a host computer on the local network, typically 
using Wifi. Read more in trcStreamingPort.h.

To use this stream port, make sure that include/trcStreamingPort.h is found
by the compiler (i.e., add this folder to your project's include paths) and
add all included source files to your build. Make sure no other versions of
trcStreamingPort.h are included by mistake!

See also http://percepio.com/2016/10/05/rtos-tracing 
and https://percepio.com/2018/10/11/tuning-your-custom-trace-streaming/

Percepio AB
www.percepio.com