
                FREERTOS COLDFIRE MCF523x PORT with lwIP

REQUIREMENTS
============

The FreeRTOS port is designed for the MCF523x processor where the hardware
dependent part consists of the CPU and the peripherals used in this  port.
This includes a programmable timer  (PIT)  for  the  preemptive  scheduler
and a UART for the demo application.  The Coldfire specific part  includes
the number and type of processor registers, the  stack  frame  layout  and
the usage of a software interrupt (trap) for the yield call.

The development environment used is  based  on  the  GNU  C  Compiler  for
a m68k-elf target as well as the insight debugger with  some  patches  for
the BDM interface[1].  GDB startup and linker scripts  are  supplied  with
the demo for the M5235BCC evaluation kit from Freescale.

 [1] ... BDM tools: http://sourceforge.net/projects/bdm/

USAGE
=====

A makefile is supplied with the demo  application  and  a  binary  can  be
produced by calling 'make all'.  A  special  target  'debug'  is  provided
which executes the insight  debugger.   At  the  insight  debugger  prompt
one should select the  appropriate  target  interface  (either  BDM/Direct
or BDM/TCP)  and  should  download  the  application  to  the  development
board.  It is important that the GDB  script  setup-and-load  is  executed
prior to downloading to  initialize  the  SDRAM.   After  downloading  one
should call the GDB function 'execute' and the PC  is  set  to  the  start
of the executable.  Execution can  be  started  by  typing  'continue'  at
the Insight console interface.
After this  startup phase the  insight debugger should work as usual, i.e.
no grayed out buttons, ...


COMMON PROBLEMS
===============
 
Most of the problems have  their  origin  in  the  startup  scripts.   The
following list should serve as  a  checklist  where  each  point  must  be
satisfied for the port to work.

 - The FreeRTOS port only works correctly in the supervisor mode.   There-
   fore the Coldfire CPU must run in the supervisor mode.

 - portVECTOR_TABLE does not point to the currently active  vector  table.
   Please also note that the vector table must be in  RAM  such  that  the
   FreeRTOS port can install a traphandler for the portYIELD() call.


$Id: README.txt,v 1.1 2006/08/29 02:24:03 wolti Exp $

MCF5235 + lwIP port - Copyright (c) 2006 Christian Walter.

