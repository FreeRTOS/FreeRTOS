Links to a documentation page for each demo are provided on the following
URL: http://www.freertos.org/a00090.html

Each RTOS port has a demo application to demonstrate it's use.

+ The Demo/Common directory contains the demo application files as described on 
the http://www.FreeRTOS.org WEB site.  Each file creates one or more tasks.
The files in the Demo/Common directory are used by every demo application for
every port.

+ All the other directories contain a project or makefile for the demo
application targeted at a particular microcontroller.  


For example, if you are interested in the ATMega323 demo application for
the WinAVR tools then the AVR_ATMega323_WinAVR directory contains the 
relevant makefile.  The makefile includes files from the Demo/ATMega323 
and the Demo/Common directories.  If this is the only port you are 
interested in then all the other directories can be ignored.
