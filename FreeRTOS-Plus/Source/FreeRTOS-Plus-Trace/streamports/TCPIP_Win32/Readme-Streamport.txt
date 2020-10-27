Tracealyzer Stream Port for TCP/IP (Win32 example)
-------------------------------------------------

This directory contains a "stream port" for the Tracealyzer recorder library,
i.e., the I/O code needed for streaming a Tracealyzer RTOS trace over specific
interface. The stream port is defined by a set of macros in trcStreamingPort.h,
found in the "include" directory.

This particular stream port is for streaming over TCP/IP on Windows, intended
for the FreeRTOS Windows port (WIN32-MSVC). To try it:

1. Open the WIN32-MSVC demo project found in the FreeRTOS demo folder. You 
need will Visual Studio, but there are free versions (Express or Community).

2. Make sure the project includes a recent version or the recorder library
(v3.1.x).

3. Make sure the recorder library is configured for streaming mode (see
trcConfig.h).

4. Make sure the project's include paths contains trcStreamingPort.h found in
this include folder (and not any other stream port), and the related code 
in this folder.

5. Build and start the Win32 demo application. It should begin waiting for
a connection. 

6. In Tracealyzer, open File -> Settings... -> Streaming Trace Settings.
Specify target connection: TCP, host: 127.0.0.1 (i.e. localhost) and port 8888.

7. In Tracealyzer, now open File -> Connect to Target System... and there 
click "Start Recording". Now you should see a live CPU load graph and some 
counters. Let it record for a few seconds, then click "Stop Recording" and then "View Trace".

See also http://percepio.com/2016/10/05/rtos-tracing.

Percepio AB
www.percepio.com