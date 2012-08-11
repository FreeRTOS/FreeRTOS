==========================================================================
                   Template Project for MB96348HS Series
==========================================================================
                   Fujitsu Microelectronics Europe GmbH                       
   
 The following  software  is for  demonstration  purposes only.  It is not
 fully  tested, nor validated  in order  to fullfill  its task  under  all
 circumstances.  Therefore,  this software or  any part of it must only be
 used in an evaluation laboratory environment.                        
 This software is subject to the rules of our standard DISCLAIMER, that is
 delivered with our SW-tools on the Fujitsu Microcontrollers DVD 
 (V5.0 or higher "\START.HTM").
==========================================================================
               
History
Date        Ver     Author  Softune     Description
2007-10-29  1.0     MPi     V30L33R11   original version
2007-11-02  1.1     MPi     V30L33R11   Added the watchdog functionality
										Used vTaskStartScheduler() instead
										of xPortStartScheduler()
2007-11-12  1.2     MPi     V30L33R11   Updated FreeRTOS 4.6.1 and tested
2007-11-23  1.3     MPi     V30L33R11   Seperated watchdog functionality in watchdog.c 
										and watchdog.h
2008-01-03  1.4     MPi     V30L33R11   Added portYIELDFromISR() and now all the
										demo application functions are working.
2008-01-04  1.5     MPi     V30L33R11   Updated FreeRTOS 4.7.0 and tested
2008-01-10  1.6     MPi     V30L33R11   Replaced INT9 with INT #122 in macro portYIELD()
2008-01-14  1.7     MPi     V30L33R11   Modified the code to work with  SK-16FX-100PMC V1.1
2008-01-15  1.8     MPi     V30L33R11   Integrated SVN releases 1.5 and 1.6.   			
==========================================================================
1.0.
This is a project is to test the FreeRTOS port for 16FX and the demo application
which runs on FLASH-CAN-100P-240.

This FreeRTOS port uses the Task Stack pointed by User Stack pointer (USB:USP) for
tasks and the system stack pointed by System Stack pointer (SSB:SSP) for everything
else. 

This port is tested with MEDIUM and LARGE memory model and seems to be working fine.
The define MEMMODEL has to be configured in order to use the corresponding memory
model.

This port doesnt use any register banking and always uses bank 0. It also consider that
the parameters to the tasks is passed via stack and not via registers.        

In this port the implemetation of portENTER_CRITICAL() and portEXIT_CRITICAL() macros
is changed in order to make them more efficient. Now usCriticalNesting variable is not
used to keep track of global interrupt enable. Rather the current PS is stored on to 
the stack and interrupts are disabled for portENTER_CRITICAL(). And for portEXIT_CRITICAL()
simply the PS is restored from stack.

1.1.
In this port, the functionality is added to initialize and clear the watchdog in the
dedicated task, Tick Hook or the Idle Hook. The place exactly where the wtachdog can be 
cleared can be configured. Though Idle Hook is not an approproiate place to clear the 
watchdog, its done here for demonstration purpose only.

Also from Main function vTaskStartScheduler() function is called instead of xPortStartScheduler().
After doing this change now no more IDLE task is required to be added seperately as 
vTaskStartScheduler() adds prvIdleTask() on its own.

1.2.
Updated the FreeRTOS version to 4.6.1 and tested with the same.

1.3.
Moved the watchdog functionality to watchdog.c and watchdog.h.

1.4.
Added portYIELDFromISR() which uses delayed interrupt. This macro needs to be used from the
application ISRs in order to force a context switch from them if required. It should be noted
that the interrupt priority of such application ISRs MUST be always higher than the dealyed 
interrupt (currently 23) in order to perform the context switch correctly.

It should be also noted that the RLT0 and Delayed Interrupt priority MUST be always same in order 
to assure correct working of this port.

Now portYIELD() used software interrupt INT9 instead of delayed interrupt.

Now all the queue functions works ok.

Tested with the heap_1.c, heap_2.c and heap_3.c.

At one time, either of heap_1.c or heap_2.c or heap_3.c needs to be used. Hence the files those are not 
required to be used should be removed from the target of the build.

Added the __STD_LIB_sbrk.c file in order to define the *sbrk() function. This is required while using
heap_3.c file which uses the dynamic memory allocation.

Made changes to the demo application files crhook.c. Please refer the file and grep for "Added by MPi" 
to find the changes. It should be noted that if INCLUDE_StartHookCoRoutines is defined as 0 (i.e. if
vStartHookCoRoutines() functionality is NOT required) then crhook.c file should be removed from target 
build and uncomment the vApplicationTickHook() function from main.c should be uncommnented.

Added taskutility.c file. This file contains vUART2Task() which calls vTaskList() and vTaskStartTrace()
functions.

If vCreateBlockTimeTasks() is not called then the LED at PDR00_P7 blinks at normal rate (3s).

This port is tested with MEDIUM and LARGE memory model and working fine.

configMINIMAL_STACK_SIZE value changed to 172 from 70 in order to make the port work.

1.5.
Updated the FreeRTOS version to 4.7.0 and tested with the same. Tested for pre-emptive as well as 
co-operative approach.

1.6.
portYIELD() macro now uses INT #122 instead of INT9.

Optimized functions vParTestToggleLED() and vParTestSetLED() in main.c.

Now watchdog uses 2^23 as clock prescaler instead of 2^24. Also updated the WTC_CLR_PER in watchdog.h.

1.7.
Modified the code to work with  SK-16FX-100PMC V1.1.

Made changes to the demo application files crflash.c. Please refer the file and grep for "Added by MPi" 
to find the changes.

Made changes to taskutility.c and vectors.c in order to use UART1 instead of UART2.
 
Made changes to main.c file in order to handle use the 7-segment display (SEG1) connected to Port09 for tasks
and 7-segment display (SEG2) connected to Port00 for co-routines.

Added config.h and moved the demo application configs there.

1.8.
It should be noted that the readme, appnote and SVN tag version numbers may be different for the same release.

This readme is specific to project FreeRTOS_96348hs_SK16FX100PMC. And this project specifically works
on board SK-16FX-100PMC V1.1 along with EUROScope debugger.

Created 4 different configuration Config_1 to Config_4. Each config includes certain demo application function.
More details specific to each configuration can be found in the appnote.

Used relative path to include files instead of absolute.

Created config, MemMang, serial and utility subdirectories and moved corresponding functionlaity there.

Updated config.h, main.c and start.asm in order to have configuration specific build.

Clock settings:
---------------
Crystal:  4 MHz
CLKB:    56 MHz
CLKP1:   56 MHz
CLKP2:   56 MHz
