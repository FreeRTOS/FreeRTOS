Tracealyzer Stream Port for ARM Cortex-M ITM
Percepio AB
www.percepio.com
--------------------------------------------

This directory contains a "stream port" for the Tracealyzer recorder library,
i.e., the specific code needed to use a particular interface for streaming a
Tracealyzer RTOS trace. The stream port is defined by a set of macros in
trcStreamPort.h, found in the "include" directory.

This particular stream port targets ARM's ITM interface, which together with
a fast debug probe such as a Keil ULINKpro or ULINKplus provides excellent
performance. This stream port does not use any RAM buffer for the trace, but
writes the data directly to the ITM registers. This is very fast.

To setup Keil uVision for ITM tracing with a Keil ULINKpro (or ULINKplus),
see Percepio Application Note PA-021, https://percepio.com/2018/05/04/keil-itm-support/

To setup IAR Embedded Workbench for ITM tracing with an IAR I-Jet,
see Percepio Application Note PA-023, https://percepio.com/iar

To setup Lauterbach TRACE32 for ITM tracing with a uTrace,
see Percepio Application Note PA-033, https://percepio.com/apn/PA033-TRACE32%20ITM%20Streaming.pdf

Learn more:
 - Tracealyzer User Manual (Help -> User Manual)
 - https://percepio.com/gettingstarted
 - Percepio Application Note PA-021 (Keil), https://percepio.com/2018/05/04/keil-itm-support/
 - Percepio Application Note PA-023 (IAR), https://percepio.com/iar
 - Percepio Application Note PA-033 (Lauterbach), https://percepio.com/apn/PA033-TRACE32%20ITM%20Streaming.pdf
 - About ITM trace, https://percepio.com/2016/06/09/arm-itm/
 - About the recorder and custom streaming, http://percepio.com/2016/10/05/rtos-tracing

For questions, please contact support@percepio.com
