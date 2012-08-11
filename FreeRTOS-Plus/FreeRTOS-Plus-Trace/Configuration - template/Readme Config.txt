FreeRTOS+Trace v2.2.3
---------------------

This directory contains the recorder files that the typical FreeRTOS+Trace user needs to be aware of.

- trcPort.h - contains the hardware ports and the setting of what port to use.
- trcConfig.h - contains the recorder configuration.

The files in this directory are however not referenced by any of the demo projects. 
Copies of these files are instead found in each Demo project directory.

These copies are included here to make the TraceRecorderSrc directory complete.

If you use this template, you will need to update the following macro definitions in trcPort.h:
- SELECTED_PORT
- IRQ_PRIORITY_ORDER
- vTraceConsoleMessage (optional, if console prints are desired)

Always remember to check the settings used in trcConfig.h.

Percepio AB
www.percepio.se
