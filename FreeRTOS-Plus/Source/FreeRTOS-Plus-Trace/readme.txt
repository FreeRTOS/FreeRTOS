
Tracealyzer Trace Recorder Library
-------------------------------------
Percepio AB
www.percepio.com

This directory contains the a generic trace recorder library for Tracealyzer v2.6. 

For information on how to upload the trace data from your target system RAM to 
Tracealyzer, see "debugger trace upload.txt"

Files included
--------------
- trcConfig.h             - The recorder's configuration file, set your recorder configuration here!
- trcUser.c/.h            - The main API towards the application (trcUser.h in the only include necessary).
- trcKernel.c/.h          - Internal routines for storing kernel events.
- trcBase.c/.h            - Internal routines for manipulating the data structures and calculating timestamps.
- trcHardwarePort.c/.h    - The hardware interface, especially for timestamping.
- trcKernelPort.c/.h      - Kernel specific implementations of macros and data.
- trcKernelHooks.h        - The trace macro defines (OS independent).
- trcTypes.h              - Type definitions used.

Hardware Timer Ports
--------------------
This release contains hardware timer ports for the following hardware architectures:

- ARM Cortex M3/M4/M0/M0+ (all brands, such as Atmel SAM3x/SAM4x/SAM D20, NXP 17xx, 18xx, 43xx, STM32, Freescale Kinetis, ...)
- Atmel AT91SAM7x
- Atmel AT32UC3 (AVR32)
- Renesas RX600 (e.g., RX62N)
- Microchip dsPIC/PIC24
- Microchip PIC32
- NXP LPC2106
- Texas Instruments TMS570 (Cortex-R4)
- Texas Instruments MSP430
- Xilinx PowerPC 405
- Xilinx PowerPC 440
- Xilinx Microblaze

These are defined in trcHardwarePort.h. Some of these are "unofficial" ports, provided by external contributors.
By unofficial, it means that they are not yet verified by Percepio AB. Please refer to trcHardwarePort.h for detailed information. 
If you use an unofficial port and beleive it is incorrect, please let us know! (support@percepio.com)

In case your MCU is not yet supported directly, developing a new port is quite easy, just a matter of defining a few macros
according to your specific MCU. See trcHardwarePort.h for further information.

In case you have any questions, do not hesitate to contact support@percepio.com

Percepio AB
Köpmangatan 1A
72215 Västerås
Sweden

www.percepio.com