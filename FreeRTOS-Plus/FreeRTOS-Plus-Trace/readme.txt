
FreeRTOS+Trace Demo
-------------------
Percepio AB
www.percepio.se

This package contains:
/Demo/DemoAppl									The demo application used in the included demo projects.
/Demo/Eclipse-AT91SAM7          Demo project for Eclipse/GCC with Atmel AT91SAM7X256 as preconfigured target.
/Demo/IAR - Cortex M3           Demo project for IAR Embedded Workbench for ARM, with NXP LPC1766 as preconfigured target.
/Demo/Renesas RDK HEW - RX600   Demo project for Renesas HEW, with the RX62N as preconfigured target.
/Demo/MSVC Win32                Demo project Microsoft Visual Studio, using the Win32 port of FreeRTOS.
/FreeRTOS-v7.1.1                A subset of FreeRTOS v7.1.1 (the only change is that the Demo directory has been removed - it is quite large!).
/TraceRecorderSrc               The trace recorder library for FreeRTOS / FreeRTOS+Trace.

Note that the individual Demo project directories are not self-contained.
They refer to the FreeRTOS-v7.1.1, DemoAppl and TraceRecorderSrc directories.

Hardware Timer Ports
--------------------
This release contains hardware timer ports for the following hardware architectures:

- ARM Cortex M3/M4 (all brands)
- Atmel AT91SAM7X
- Renesas RX600

The package moreover contain several "unofficial" ports, provided by external contributors and not yet verified by Percepio AB.
See trcPort.h for the details. 

In case your hardware is not yet directly supported, developing a new port is quite easy. 
See trcPort.h for further information.

In case you have any questions, do not hesitate to contact support@percepio.se

Percepio AB
Köpmangatan 1A
72215 Västerås
Sweden

www.percepio.se