# FreeRTOS for the Renesas RL78 microcontrollers

This directory contains an application that demonstrates the use of FreeRTOS on a [Renesas RL78 16-bit microcontroller](https://renesas.com/rl78) using the [IAR compiler](https://www.iar.com/ewrl78).

## Overview
The demo project includes multiple _build configurations_. Each _build configuration_ is set for an evaluation board.

| __Build Configuration__                 | __Description__                    |
| -                                       | -                                  |
| [YRPBRL78G13][url-yrpbrl78g13]          | Renesas Promotion Board RL78/G13   |
| [YRPBRL78G14][url-yrpbrl78g14]          | Renesas Promotion Board RL78/G14   |
| [YRDKRL78G14][url-yrdkrl78g14]          | Renesas Development Kit RL78/G14   |
| [RSKRL78G1C][url-rskrl78g1c]            | Renesas Starter Kit RL78/G1C       |
| [RSKRL78L13][url-rskrl78l13]            | Renesas Starter Kit RL78/L13       |
| [RSKRL78L1C][url-rskrl78l1c]            | Renesas Starter Kit RL78/L1C       |
| [QB_R5F10ELE_TB][url-qb-r5f10ele-tb]    | Renesas Target Board RL78/G1A      |

<!-- links -->
[url-yrpbrl78g13]:    https://renesas.com/yrpbrl78g13
[url-yrpbrl78g14]:    https://renesas.com/yrpbrl78g14
[url-yrdkrl78g14]:    https://renesas.com/yrdkrl78g14
[url-rskrl78g1c]:     https://www.renesas.com/products/microcontrollers-microprocessors/rl78-low-power-8-16-bit-mcus/rl78g1c-starter-kit-renesas-starter-kit-rl78g1c
[url-rskrl78l13]:     https://www.renesas.com/products/microcontrollers-microprocessors/rl78-low-power-8-16-bit-mcus/rl78-l13-starter-kit-renesas-starter-kit-rl78l13
[url-rskrl78l1c]:     https://www.renesas.com/products/microcontrollers-microprocessors/rl78-low-power-8-16-bit-mcus/rl78-l1c-starter-kit-renesas-starter-kit-rl78l1c
[url-qb-r5f10ele-tb]: https://renesas.com/qb-r5f10ele-tb
                
>:warning: This demo project requires __IAR Embedded Workbench for Renesas RL78__ (EWRL78) version __3.10.1 or later__.


## Important notes
Please read all the following sections before using this RTOS port.
* [Source Code Organization](#source-code-organization)
* [The Demo Application](#the-demo-application)
* [Configuration and Usage Details](#configuration-and-usage-details)

>:bulb: See also the FAQ [My application does not run, what could be wrong?](https://www.freertos.org/FAQHelp.html)


## Source Code Organization
The FreeRTOS download contains the source code for all the FreeRTOS ports, so contains many more files than used by this demo.

>:bulb: See the [Source Code Organization](https://www.freertos.org/a00017.html) section for a description of the downloaded files and information on creating a new project.

## The Demo Application
### Demo application hardware setup
The demo application makes use of an LED that is mounted directly onto each of the supported hardware platforms. No hardware setup is required.

### Functionality
`mainCREATE_SIMPLE_BLINKY_DEMO_ONLY` is defined in [main.c](https://github.com/FreeRTOS/FreeRTOS/blob/main/FreeRTOS/Demo/RL78_multiple_IAR/main.c). If `mainCREATE_SIMPLE_BLINKY_DEMO_ONLY` is set to __1__ then `main()` will call `main_blinky()`, which creates a simple 'blinky' style demo. If `mainCREATE_SIMPLE_BLINKY_DEMO_ONLY` is set to __0__ then `main()` will call `main_full()` which creates a more comprehensive demo.

### Functionality when `mainCREATE_SIMPLE_BLINKY_DEMO_ONLY` is set to 1
`main_blinky()` creates one queue, and two tasks before starting the RTOS scheduler.

* The **"Queue Send"** Task:
The queue send task is implemented by the `prvQueueSendTask()` function in __main_blinky.c__.  `prvQueueSendTask()` sits in a loop that causes it to repeatedly block for 200 ms, before sending the value 100 to the queue that was created within `main_blinky()`. Once the value is sent, the task loops back around to block for another 200 ms, and so on.

* The **"Queue Receive"** Task:
The queue receive task is implemented by the `prvQueueReceiveTask()` function in __main_blinky.c__.  `prvQueueReceiveTask()` sits in a loop where it repeatedly blocks on attempts to read data from the queue that was created within `main_blinky()`, toggling an LED each time the value 100 is received.

The queue receive task will only leave the Blocked state when the queue send task writes to the queue. As the queue send task writes to the queue every 200 ms, the queue receive task leaves the Blocked state and toggles the LED every 200 ms.


### Functionality when `mainCREATE_SIMPLE_BLINKY_DEMO_ONLY` is set to 0
`main_full()` creates 13 tasks, 4 queues, and 2 software timers. Many of the tasks are from the set of standard demo tasks that are used with all the RTOS demos, and are documented on the [FreeRTOS.org](https://freertos.org) website.

The following tasks and timers are created in addition to the standard demo tasks.

* The __"Reg test"__ tasks:
These fill the registers with known values, then check that each register still contains its expected value. Each task uses a different set of values. The reg test tasks execute with a very low priority, so get preempted very frequently. A register containing an unexpected value is indicative of an error in the context switching mechanism.

* The __"Demo"__ Software Timer and Callback Function:
The demo software timer callback function does nothing more than increment a variable. The period of the demo timer is set relative to the period of the check timer (described below). This allows the check timer to know how many times the demo timer callback function should execute between each execution of the check timer callback function. The variable incremented in the demo timer callback function is used to determine how many times the callback function has executed.

* The __"Check"__ Software Timer and Callback Function:
The check software timer period is initially set to 3 seconds. The check timer callback function checks that all the standard demo tasks, the reg test tasks, and the demo timer are not only still executing, but are executing without reporting any errors. If the check timer discovers that a task or timer has stalled, or reported an error, then it changes its own period from the initial 3 seconds, to just 200 ms.

The check timer callback function also toggles an LED each time it is called. This provides a visual indication of the system status: If the LED toggles every 3 seconds, then no issues have been discovered. If the LED toggles every 200 ms, then an issue has been discovered with at least one task.


### Building the demo application
1. Launch the __IAR Embedded Workbench for Renesas RL78__.
2. In the menu, select __File__ → __Open Workspace__ and choose the __RTOSDemo.eww__ workspace.
3. Use the drop-down list at the top of the Workspace window to select the _build configuration_ that is correct for the target hardware being used.
4. Press <kbd>F7</kbd> to build the project. The project should build without any errors or warnings.


### Programming the microcontroller and debugging
1. Ensure the target board is connected to the host computer as appropriate. Some development boards include a built in __TK__ interface and only require a USB cable. Other boards require a __Renesas E1 Emulator__ (or later) debug interface.
2. In the menu, select __Project__ → __Download and Debug__. When a debug session is launched for the first time in the EWRL78, a message will show up saying that the emulator has to be configured before downloading a new application. Click the __OK__ button to open the "Emulator Hardware Setup" window for the debug probe. The configuration window provides several options such as "Power supply" for when powering the evaluation board directly from the probe. Once the configuration is complete, the flash memory will be programmed and the program initialization will execute until the debugger breaks on the `main()` function entry point.


## Configuration and Usage Details
### RTOS port specific configuration
Configuration items specific to this demo are contained in [FreeRTOSConfig.h](FreeRTOSConfig.h). The constants defined in this file can be edited to suit your application.
Each port defines `BaseType_t` to equal the most efficient data type for that processor. This port defines `BaseType_t` to be of type `short`.

>:warning: `vPortEndScheduler()` has not been implemented.

### Memory models
The FreeRTOS port will automatically switch between the __near__ and __far__ memory models, depending on the settings in the IAR project options. 

This port has been tested with 2 memory model combinations, which are:
| __Combination__ | __Code Model__ | __Data Model__ |
| --------------- | -------------- | -------------- |
| Combination 1   | NEAR           | NEAR           |
| Combination 2   | FAR            | FAR            |

### Writing interrupt service routines
Interrupt service routines that cannot cause a context switch have no special requirements and can be written as described by the IAR compiler documentation.
Often you will require an interrupt service routine to cause a context switch. For example, a serial port character being received may unblock a high priority task that was blocked waiting for the character to arrive. If the unblocked task has a higher priority than the current task (the task that was interrupted by the ISR), then the ISR should return directly to the unblocked task. The use of the IAR tools necessitates such interrupt service routines are entered using an assembly file wrapper as it can be seen in the [interrupt_vector.s](interrupt_vector.s) file. An example is provided below, and another example is provided in [main.c](main.c).


__Assembly wrapper__ in [interrupt_vector.s](interrupt_vector.s):
```assembly
;   The portmacro.h header provides the portSAVE_CONTEXT() and
;   portRESTORE_context() macros.
#include "portmacro.h"
...
    PUBLIC _vAnExampleISR_ASM_Wrapper
    EXTERN _vAnExampleISR_C_Handler

    SECTION `.text`:CODE
_vAnExampleISR_ASM_Wrapper:
    portSAVE_CONTEXT                    ; The wrapped ISR must start with the portSAVE_CONTEXT() macro.

    CALL    _vAnExampleISR_C_Handler    ; Once the context has been saved the C handler can be called.

    portRESTORE_CONTEXT                 ; The wrapped ISR must end with the to portRESTORE_CONTEXT() macro.

    RETI                                ; Returns from the interrupt to whichever task task is now the task selected
                                        ; to run (which might differ from the task that was running before the ISR.
...
;-------------------------------------------------------------------------------
;   Place a pointer to the _vAnExampleISR_ASM_Wrapper at the correct index into
;   the interrupt vector table. This is an example for a ISR which needs context
;   switch.
;
;   NOTE: 0x3A is used is purely as an example.  The correct vector index for
;   the interrupt being installed must be used.
;-------------------------------------------------------------------------------
___interrupt_tab_0x3A:
    DATA16
    DC16      _vAnExampleISR_ASM_Wrapper
;-------------------------------------------------------------------------------
```

The C portion of the interrupt handler is just a standard C function.
```c
/* This standard C function is called from the assembly wrapper above. */
void vISRHandler( void )
{
short sHigherPriorityTaskWoken = pdFALSE;

    /* Handler code goes here, for purposes of demonstration, assume
    at some point the hander calls xSemaphoreGiveFromISR().*/
    xSemaphoreGiveFromISR( xSemaphore, &sHigherPriorityTaskWoken );

    /* If giving the semaphore unblocked a task, and the unblocked task has a
    priority that is higher than the currently running task, then
    sHigherPriorityTaskWoken will have been set to pdTRUE.  Passing a pdTRUE
    value to portYIELD_FROM_ISR() will cause this interrupt to return directly
    to the higher priority unblocked task. */
    portYIELD_FROM_ISR( sHigherPriorityTaskWoken );
}
```
The C portion of the example interrupt handler.


### Resources used by the RTOS kernel
By default the RTOS kernel uses the RL78 Interval Timer peripheral to generate the RTOS tick. The application writer can modify the `vApplicationSetupTimerInterrupt()` in the [main.c]() such that their own tick interrupt configuration is used in place of the default. 

>:warning: `vPortTickISR()` must be installed as the handler for which ever interrupt is used to generate the RTOS tick. 

>:warning: The RTOS kernel also requires __exclusive__ use of the __BRK software interrupt__ instruction.


### Compiler options
As with all the ports, it is essential that the correct compiler options are used. The best way to ensure this is to base your application on the provided demo application files.


### Memory allocation
The [heap_1,c](https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/portable/MemMang/heap_1.c) is included in the demo application project to provide the memory allocation required by the RTOS kernel. Please refer to the [Memory Management](https://www.freertos.org/a00111.html) section of the API documentation for full information.
