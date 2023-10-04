
==========================================================================
                   Template Project for MB91F467D 
==========================================================================
                   Fujitsu Microelectronics Europe GmbH                       
                 http://emea.fujitsu.com/microelectronics 
                                                            
The  following  software  is for  demonstration  purposes only.  It is not
fully  tested, nor validated  in  order  to fullfill  its task  under  all
circumstances.  Therefore,  this software  or  any part of it must only be
used in an evaluation laboratory environment.                        
This software is subject to  the rules of our standard DISCLAIMER, that is
delivered  with  our  SW-tools  on  the  Fujitsu  Microcontrollers CD /DVD
(V3.4 or higher "\START.HTM").
==========================================================================
               
History
Date        Ver     Author  Softune     Description
2007-11-12  1.0     MPi     V60L06		original version
2007-11-12  1.1     MPi     V60L06		Changed the version for consistency
										with SVN
2007-11-23  1.2     MPi     V60L06		Seperated Watchdog functionality
										added watchdog.c and watchdog.h
2007-12-13  1.3     MPi     V60L06		Tested with the FreeRTOS version 4.6.1.
2007-12-13  1.4     MPi     V60L06		Tested with the FreeRTOS version 4.7.0.
2007-01-07  1.5     MPi     V60L06		Removed watchdog.c, watchdog.h, port.c 
										and portmacro.h from directory
										\FreeRTOS_Port_FR\91467d_FreeRTOS\SRC
2007-01-18  1.6     MPi     V60L06		Tested with monitor debugger
==========================================================================
1.0.
This is a project is to test the FreeRTOS port for FR (91467D) and the demo 
application which runs on SK-91F467-Felxray V1.1.

1.1.
This FreeRTOS port uses the Task Stack pointed by User Stack pointer (USP) for
tasks and the system stack pointed by System Stack pointer (SSP) for everything
else. 

1.2.
In this port, the functionality is added to initialize and clear the watchdog in 
the dedicated task, Tick Hook or the Idle Hook. The place exactly where the 
watchdog can be cleared can be configured. Though Idle Hook is not an approproiate
place to clear the watchdog, its done here for demonstration purpose only.

Also from Main function vTaskStartScheduler() function is called instead of 
xPortStartScheduler(). After doing this change now no more IDLE task is required
to be added seperately as vTaskStartScheduler() adds prvIdleTask() on its own.

The System Stack required by each of the RLT0 and Delayed Interrupt ISR is around 100 
bytes. This is considering no interrupts has higher priority than the RLT0 and Delayed 
interrupt (23). If an application has interrupt whose priority is higher than these 
interrupts, which is very likely, then for each such interrupt the user has to increase 
the stack size at least by 50 bytes, though this is not an optimum figure and very well 
depends upon the application.
Hence though the STACK_SYS_SIZE is defined as 2000, its optimum value would be very well
dependent on the application where the port would be used.

1.3.
Tested with the FreeRTOS version 4.6.1.

Changed portBYTE_ALIGNMENT to 4 from 1.

Added portYIELDFromISR() which uses delayed interrupt. This macro needs to be used from the
application ISRs in order to force a context switch from them if required. It should be noted
that the interrupt priority of such application ISRs MUST be always higher than the dealyed 
interrupt (currently 23) in order to perform the context switch correctly.

It should be also noted that the RLT0 and Delayed Interrupt priority MUST be always same in order 
to assure correct working of this port.

Now portYIELD() used software interrupt INT #40H instead of delayed interrupt.

Now all the queue functions works ok.

Tested with the heap_1.c, heap_2.c and heap_3.c.

Added the __STD_LIB_sbrk.c file in order to define the *sbrk() function. This is required while using
heap_3.c file which uses the dynamic memory allocation.

Made changes to the demo application files crflash.c and crhook.c. Please refer those file
and grep for "Added by MPi" to find the changes.

Added taskutility.c file. This file contains vUART4Task() which calls vTaskList() and vTaskStartTrace()
functions.

If vCreateBlockTimeTasks() is not called then the LED at PDR25_D7 blinks at normal rate (3s).

1.4.
Tested with the FreeRTOS version 4.6.1.

At one time, either of heap_1.c or heap_2.c or heap_3.c needs to be used. Hence the files those are not 
required to be used should be removed from the target of the build.

1.5.
Removed watchdog.c, watchdog.h, port.c and portmacro.h from directory \FreeRTOS_Port_FR\91467d_FreeRTOS\SRC, 
since they are moved to folders watchdog and port respectively.

1.6.
It should be noted that the readme, appnote and SVN tag version numbers may be different for the same release.

Used relative path to include files instead of absolute.

Created config, MemMang, serial and utility subdirectories and moved corresponding functionlaity there.

Updated taskuitlity.c, vectors.c in oredr to use UART 5 instead of UART 4

Updated flash.c to increase LEDs to 4 from 3.

Clock settings:
---------------
Crystal:  4 MHz
CPU:     64 MHz
CLKP:    16 MHz
