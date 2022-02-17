
# Overview

This directory contains an FT32F072XX demo project (ARM compiler V6.16) for FT32F072XX StarterKit board equipped with FT32F072XX microcontroller (128 KB Flash and 8 KB SRAM or 128 KB Flash and 24 KB SRAM).  

The project comes with two different demos, selectable by a define in the "**FreeRTOSConfig.h**" file. Follow the instructions on the RTOS port documentation page for details about how to setup the target hardware, download and execute the demo application.

### main-standardtest Demo

**#define       mainCREATE_DEMO_ONLY 	0**

Standardtest demos are [the standard demos/tests](https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/ThirdParty/Template/README.md). The whole functionality is included in the **main-standardtest.c** file by call the void vStartTests( void ) function which contains all the test in the [FreeRTOS/Demo/Common/Minimal](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS/Demo/Common/Minimal).  

This demo uses the **check** task to periodically inspect the standard demo tasks in order to ensure all the tasks are functioning as expected.

To see the console output from serial communication tasks, serial port could be configured as: 
 - baud rate 115200
 - data 8-bit
 - parity none
 - stop bits 1-bit
 - flow control none
 
**Notice:**

Because of FT32F072X8(except FT32F072XB) lack of RAM space, you need run tests one by one or in groups by defining configSTART_<Test_Name>_TESTS macros to 0 or 1 as needed. 

### main Demo

**#define       mainCREATE_DEMO_ONLY	  1**

The main_demo create just three [tasks](https://www.freertos.org/a00015.html) that communicates with each other through a [queue](https://www.freertos.org/Embedded-RTOS-Queues.html).

The whole functionality is included in the **main_demo.c** file by using the following tasks:

 - InitTask Task (**InitProTask.c**)
 - HighProTask Task (**HighProTask.c**)
 - LowProTask Task (**LowProTask.c**) 

InitProTask initialises the peripheral GPIO as LED and KEY-press, the USART sending and receiving, the analog-digital conversion(ADC) and the TIMER.Then delete itself.  

HighProTask and LowProTask are two task with different priority. HighProTask deal the functions such as key-press detection and serial port data sending and receiving which require real-time response.   

LowProTask deal the functions such as LED toggle, key-press data process and ADC process.

It also prints data by serial port(USART). To see the console output from serial communication tasks, serial port could be configured as: 
 - baud rate 115200
 - data 8-bit
 - parity none
 - stop bits 1-bit
 - flow control none


# Quick start

To run this demo on  FT32F072XX StarterKit board, the following steps are required:
 - install **Keil uVision5**
 - open **FreeRTOS_Demo.uvprojx** project file from current folder
 - select desired demo using **#define       mainCREATE_DEMO_ONLY  1 or 0** as explained in the previous section
 - build and debug the project

# References
  - [ft32f0xx_rm_rev1.0](https://www.fremontmicro.com/downfile.aspx?filepath=/upload/2021/1118/1500pt60x2.pdf&filename=ft32f0xx_rm_rev1.0.pdf)
  - [Keil uVision5](https://www.keil.com/demo/eval/arm.htm)
  - [FT32F072XX](https://www.fremontmicro.com/product/32%20bit%20mcu/arm%20core_1/index.aspx).

