Tracealyzer Stream Port for ARM Cortex-M ITM
--------------------------------------------
2018-05-04

This directory contains a "stream port" for the Tracealyzer recorder library,
i.e., the specific code needed to use a particular interface for streaming a
Tracealyzer RTOS trace. The stream port is defined by a set of macros in
trcStreamingPort.h, found in the "include" directory.

This particular stream port targets ARM's ITM interface, which together with
a fast debug probe such as a Keil ULINKpro or ULINKplus provides excellent
performance. This stream port does not use any RAM buffer for the trace, but
writes the data directly to the ITM registers. This is very fast.

To setup Keil uVision for ITM tracing with a Keil ULINKpro (or ULINKplus),
see Percepio Application Note PA-021 https://percepio.com/2018/05/04/keil-itm-support/

Learning more:
 - Tracealyzer User Manual (Help -> User Manual)
 - https://percepio.com/gettingstarted
 - Percepio Application Note PA-021 https://percepio.com/2018/05/04/keil-itm-support/
 - About ITM trace, https://percepio.com/2016/06/09/arm-itm/
 - About the recorder and custom streaming, http://percepio.com/2016/10/05/rtos-tracing

For questions, please contact support@percepio.com

Percepio AB
www.percepio.com