Tracealyzer Stream Port for STM32 USB CDC (Virtual COM Port)
------------------------------------------------------------

This directory contains a "stream port" for the Tracealyzer recorder library,
allowing for streaming the trace data over a USB connection. The stream port is defined by a set of macros in
trcStreamingPort.h, found in the "include" directory, that relies on functions in trcStreamingPort.c.

This particular stream port targets STM32 devices using USB CDC (virtual COM port).
It was been tested with STM32F767 and STM32L475.

--- Prerequisites ---

- An STM32 device with a USB connector for application use.

- Tracealyzer 4 with a license for FreeRTOS, SafeRTOS or Micrium µC/OS-III.

- STM32CubeIDE or the stand-alone STM32CubeMX configuration tool.

--- Instructions ---

1. Follow the general instructions (Section 1) at https://percepio.com/gettingstarted-freertos/
and verify that Snapshot mode works. The basic integration of the recorder library is the same.

2. Open the Device Configuration Tool (STM32CubeMX), e.g. by double-clicking on the .ioc file in your STM32CubeIDE project.

2.1. Under "Middleware", enable "USB_DEVICE" and...
- In "USB_DEVICE Mode and Configuration", set the "Class for FS IP" to "Communication Device Class (Virtual Com Port)".
- Under Configuration -> Parameter Settings, set the TX and RX buffer sizes to a small value (e.g. 1).
The default TX and RX buffers are not used by the trace recorder library, so this avoids wasting RAM. 

2.2. Under "Connectivity", open "USB_OTG_FS" and... 
- In "USB_OTG_FS Mode and Configuration", make sure "Mode" is set to "Device_Only" 
- Under "Configuration", open "NVIC Settings" and make sure "USB OTG FS global interrupt" is enabled.

3. Open trcConfig.h and set TRC_CFG_RECORDER_MODE to TRC_RECORDER_MODE_STREAMING.

4. Copy trcStreamingPort.c and include/trcStreamingPort.h into your project.

5. Make sure you have "vTraceEnable(TRC_INIT);" in main.c (not TRC_START or so).
This should be placed after the HW setup but before making any RTOS calls.

6. Plug in a USB cable to the connector labeled "USB OTG" or similar (i.e. for application use).

7. Build the project and start it. Check that your computer finds a new USB device (there should be a notification).

8. Check the number of the new COM port, that should have appeared. This is NOT "STLink Virtual COM port".

9. Start Tracealyzer and open Recording Settings and select Target Connection: SerialPort.
You can also access these settings via File -> Settings -> PSF Streaming Settings.

10. Enter the number of the COM port in the "Device" field. The settings (data
bits, data rate etc.) are irrelevant for USB serial connections and not used.

11. While the target is running, select Record Streaming Trace in Tracealyzer.
You should now see a live display of the trace, while it is being received.
Make sure there are no warnings about "Dropped Events" (in that case, see Troubleshooting, below).

Note that you can still debug and use breakpoints while streaming the trace. 

--- Further reading ---

- http://percepio.com/2017/02/03/usb-trace-streaming-st-nucleo-f767zi-board
- http://percepio.com/2016/10/05/rtos-tracing
- https://percepio.com/2018/10/11/tuning-your-custom-trace-streaming/

--- Troubleshooting ---

A. If you get an error about "multiple definition of SysTick_Handler", open 
FreeRTOSConfig.h (found in Core/Inc) and add this line in the bottom, 
after the definition of xPortSysTickHandler.

#undef xPortSysTickHandler

B. If you get "Missed Events" in the Live Stream window, it is typically because
your application produces more trace data than can be transferred, so the trace 
buffer overflows.
You may try the following to start with:
- Increase TRC_CFG_PAGED_EVENT_BUFFER_PAGE_COUNT and/or TRC_CFG_PAGED_EVENT_BUFFER_PAGE_SIZE in trcStreamingConfig.h 
- Decrease TRC_CFG_CTRL_TASK_DELAY in trcConfig.h 
- Increase TRC_CFG_CTRL_TASK_PRIORITY in trcConfig.h 

Also see the "tuning" guide at https://percepio.com/2018/10/11/tuning-your-custom-trace-streaming/ 

Also note that this USB stream port has a diagnostics option that might come handy. 
Enable USB_PERF_DIAGNOSTICS in trcStreamingPort.h. This will save additional "user events"
each time a buffer page is transmitted, showing the number of bytes sent and the 
remaining capacity in the trace buffer (if this goes down to zero, data is lost).

#define USB_PERF_DIAGNOSTICS 1 

If you need assistence, feel free to contact support@percepio.com.

Percepio AB
https://percepio.com