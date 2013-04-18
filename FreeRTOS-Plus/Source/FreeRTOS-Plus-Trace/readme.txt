
FreeRTOS+Trace Trace Recorder Library
-------------------------------------
Percepio AB
www.percepio.com

This directory contains the core trace recorder library used by FreeRTOS+Trace v2.3. 

Ready-to-run demonstrations projects are found at www.percepio.com.

For information on how to integrate the recorder library in your FreeRTOS build, see
the FreeRTOS+Trace User Manual, section 2.

For information on how to upload the trace data from your target system RAM to 
FreeRTOS+Trace, see "debugger trace upload.txt"

NOTE: This trace recorder library requires FreeRTOS v7.3.0 or later.

Files included
--------------
- trcConfig.h               - The recorder's configuration file, check this!
- trcUser.c / trcUser.h     - The main API towards the application (trcUser.h in the only include necessary).
- trcKernel.c / trcKernel.h - Internal routines for storing kernel events.
- trcBase.c / trcBase.h     - Internal routines for manipulating the data structures and calculating timestamps.
- trcPort.c / trcPort.h     - The port layer, abstracting the hardware (mainly the timer used for timestamping).
- trcHooks.h				- The interface between FreeRTOS and the recorder, containing trace macro defintions.
- trcTypes.h				- Type definitions used.

Hardware Timer Ports
--------------------
This release contains hardware timer ports for the following hardware architectures:

- ARM Cortex M3/M4 (all brands, such as Atmel SAM3/SAM4, NXP 17xx, 18xx, 43xx, STM32, Freescale Kinetis, ...)
- Atmel AT91SAM7x
- Atmel AT32UC3 (AVR32)
- Renesas RX600 (e.g., RX62N)
- Microchip dsPIC/PIC24

These are defined in trcPort.h. This also contains several "unofficial" ports, provided by external contributors.
By unofficial, it means that they are not yet verified by Percepio AB. Please refer to trcPort.h for detailed information. 
If you use an unofficial port and beleive it is incorrect, please let us know!

In case your MCU is not yet supported directly, developing a new port is quite easy, just a matter of defining a few macros
according to your specific MCU. See trcPort.h for further information.

In case you have any questions, do not hesitate to contact support@percepio.com

Percepio AB
Köpmangatan 1A
72215 Västerås
Sweden

www.percepio.com