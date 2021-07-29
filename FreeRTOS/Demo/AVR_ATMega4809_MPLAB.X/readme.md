
# Overview

This directory contains a MPLAB-X demo project (XC8 compiler) for Atmega4809 Curiosity Nano board equipped with Atmega4809 microcontroller (48 KB Flash, 6 KB SRAM, 256 bytes EEPROM).  

The project comes with six different demos, selectable by a define in the "**FreeRTOSConfig.h**" file. Each demo has its own main_***demo_name***.c and FreeRTOSConfig_***demo_name***.h files. Follow the instructions on the RTOS port documentation page for details about how to setup the target hardware, download and execute the demo application.

### Blinky Demo

**#define       mainSELECTED_APPLICATION	  BLINKY_DEMO**

Blinky demos are intended for beginners. They normally create just two [tasks](https://www.freertos.org/a00015.html) that communicates with each other through a [queue](https://www.freertos.org/Embedded-RTOS-Queues.html). Their functionality is contained in a single C source file called **main_blinky.c**.

One of the tasks repeatedly sends a predefined value to the queue with 200 ms intervals, while the other task waits for messages to be available in the queue. Once a new message is available, it toggles on board LED if the value matches the expected value.

### Minimal Demo

**#define       mainSELECTED_APPLICATION	  MINIMAL_DEMO**

This demo includes a higher number of tasks than the **Blinky demo**, but the complexity is still fairly low. The whole functionality is included in the **main_minimal.c** file by using the following tasks:

 - integer math task (**Integer.c**)
 - register tasks to verify the context switch (**Regtest.c**)
 - polled queue tasks (**PollQ.c**)
 - serial communiation tasks (**Serial.c**)
 - check task that periodically checks the other tasks are operating without error.

This demo uses the **check** task to periodically inspect the standard demo tasks in order to ensure all the tasks are functioning as expected. The check task also toggles an LED to give a visual feedback of the system status. If the LED is toggling roughly every second, then the check task has not discovered any problems. If the LED stops toggling, then the check task has discovered a problem in one or more tasks.

To see the console output from serial communication tasks, serial port could be configured as: 
 - baud rate 9600
 - data 8-bit
 - parity none
 - stop bits 1-bit
 - flow control none

### Full Demo

**#define       mainSELECTED_APPLICATION	  FULL_DEMO**

This demo is a comprehensive demonstration and test of a lot of FreeRTOS features, including direct task to task notifications, queues, semaphores, recursive semaphores, software timers, and more. The following tasks are created in **main_full.c** file:

 - register tasks to verify the context switch (**Regtest.c**)
 - semaphores task (**Semtest.c**)
 - direct task to task notification task (**TaskNotify.c**)
 - recursive semaphores task (**Regmutex.c**)
 - check task that periodically checks the other tasks are operating without error

The demo uses the **check** task to periodically inspect the standard demo tasks in order to ensure all the tasks are functioning as expected. The check task also toggles an LED to give a visual feedback of the system status. If the LED is toggling roughly every 3 seconds, then the check task has not discovered any problems. If the LED stops toggling, then the check task has discovered a problem in one or more tasks.

### CLI Demo

**#define       mainSELECTED_APPLICATION	  CLI_DEMO**

This demo demonstrates console line interface implementation for AVR devices (https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_CLI/FreeRTOS_Plus_Command_Line_Interface.html).
The example application provides information about the running tasks, similar with other FreeRTOS CLI demos. The whole functionality is included in the **main_cli.c** file by using the following tasks:

 - console task (**UARTCommandConsole.c**)
 - polled queue tasks (**PollQ.c**)
 - check task that periodically checks the other tasks are operating without error.

This demo uses the **check** task to periodically inspect the standard demo tasks in order to ensure all the tasks are functioning as expected. The check task also toggles an LED to give a visual feedback of the system status. If the LED is toggling roughly every second, then the check task has not discovered any problems. If the LED stops toggling, then the check task has discovered a problem in one or more tasks.

To interract with the console, the serial port needs to be configured with: 
 - baud rate 230400
 - data 8-bit
 - parity none
 - stop bits 1-bit
 - flow control RTC/CTS

The following commands are implemented:
- task-stats
- run-time-stats
- echo-3-parameters <param1> <param2> <param3>
- echo-parameters <param>
- version

### Tickless Demo

**#define       mainSELECTED_APPLICATION	  TICKLESS_DEMO**

This project shows built in low-power (tickless) functionality implementation for megaAVR® 0-series of devices (https://www.freertos.org/low-power-tickless-rtos.html). Low-power support is fully integrated in port files and can be enabled by defining configUSE_TICKLESS_IDLE to 1 in FreeRTOSConfig.h.

The demo creates two tasks ("Rx" and "Tx") which communicates with each other through a queue. The whole functionality is included in the **main_tickless.c** file.

The Rx task waits in a blocked state until data is received in the queue. For each data, it turns the LED on for 30 ms and then off again. The task will then return in the blocking state of the queue.

The Tx task waits in a blocked state until its previous sent data was received by the Rx task or until a time-out has occured. After leaving the blocking state, the task uses the queue to send data to the Rx task.

### Trace Demo

**#define       mainSELECTED_APPLICATION	  TRACE_DEMO**

The trace project ilustrates how to add Percepio trace support to an AVR FreeRTOS application (for details refer to: https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_Trace/RTOS_Trace_Instructions.html). This implementation allows continuous streaming of trace data using a serial interface.

The demo application used is similar with the **Blinky Demo**, creating two tasks that communicates with each other through a queue. Their functionality is contained in a single C source file called **main_trace.c**.

The streamed data can be viewed using the **Percepio Tracealyzer** tool, which will show the CPU load, task occurences, events, timings and custom trace informations.

The tracked data is streamed through a serial port which needs to be configured with: 
 - baud rate 460800
 - data 8-bit
 - parity none
 - stop bits 1-bit
 - flow control none

# Quick start

To run this demo on AVR128DA48 Curiosity Nano platform, the following steps are required:
 - install **MPLAB® X IDE**
 - install **MPLAB® XC8** compiler
 - open **AVR_ATMega4809_MPLAB.X** project file from current folder
 - select desired demo using **#define       mainSELECTED_APPLICATION** as explained in the previous section
 - build and debug the project


# References
  - [Atmega4809 Curiosity Nano platform](https://www.microchip.com/DevelopmentTools/ProductDetails/PartNO/DM320115)
  - MPLAB® X IDE 5.40 or newer [(microchip.com/mplab/mplab-x-ide)](http://www.microchip.com/mplab/mplab-x-ide)
  - MPLAB® XC8 2.20 or a newer compiler [(microchip.com/mplab/compilers)](http://www.microchip.com/mplab/compilers)
  - [Atmega4809](https://www.microchip.com/wwwproducts/en/ATMEGA4809), [Atmega4808](https://www.microchip.com/wwwproducts/en/ATMEGA4808), [Atmega3208](https://www.microchip.com/wwwproducts/en/ATMEGA3208) and [Atmega3209](https://www.microchip.com/wwwproducts/en/ATMEGA3209) devices page
  
