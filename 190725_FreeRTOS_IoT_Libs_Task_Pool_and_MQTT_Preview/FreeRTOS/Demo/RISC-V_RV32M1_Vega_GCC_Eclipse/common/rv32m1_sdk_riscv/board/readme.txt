Overview
========
The Hello World demo application provides a sanity check for the new SDK build environments and board bring up. The Hello
World demo prints the "Hello World" string to the terminal using the SDK UART drivers. The purpose of this demo is to
show how to use the UART, and to provide a simple project for debugging and further development.

Toolchain supported
===================
- GCC RISC-V Embedded 7.1.1
- RISC-V Eclipse IDE 4.7.2

Hardware requirements
=====================
- Mini/micro USB cable
- RV32M1-VEGA board
- Personal Computer

Board settings
==============
No special settings are required.
If download M0+ core project, need to let MCU boot from M0+ core, please follow below steps:
1. Download blhost.exe from www.nxp.com/kboot.
2. Connect J8 on board to PC using USB cable.
3. After PC recognize the USB HID device, go to blhost.exe folder, open command line.
4. Run command "blhost.exe -u -- flash-erase-all-unsecure", it will erase the flash on chip.
5. Run command "blhost.exe -u -- flash-program-once 0x84 4 ffffffbf", set FOPT3 to boot from M0+ core.

Prepare the Demo
================
1.  Connect a USB cable between the host PC and the OpenSDA USB port on the target board. 
2.  Open a serial terminal with the following settings:
    - 115200 baud rate
    - 8 data bits
    - No parity
    - One stop bit
    - No flow control
3.  Download the program to the target board.
4.  Either press the reset button on your board or launch the debugger in your IDE to begin running the demo.

Running the demo
================
The log below shows the output of the hello world demo in the terminal window:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
hello world.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Customization options
=====================

