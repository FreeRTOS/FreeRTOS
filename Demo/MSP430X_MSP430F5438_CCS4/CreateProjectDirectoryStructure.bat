REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST FreeRTOS_Source Goto END

	REM Create the required directory structure.
	MD FreeRTOS_Source
	MD FreeRTOS_Source\include	
	MD FreeRTOS_Source\portable\CCS4
	MD FreeRTOS_Source\portable\CCS4\MSP430X
	MD FreeRTOS_Source\portable\MemMang	
	MD Demo_Source\Common_Demo_Files
	MD Demo_Source\Common_Demo_Files\include
	
	REM Copy the core kernel files.
	copy ..\..\Source\tasks.c FreeRTOS_Source
	copy ..\..\Source\queue.c FreeRTOS_Source
	copy ..\..\Source\list.c FreeRTOS_Source
	
	REM Copy the common header files

	copy ..\..\Source\include\*.* FreeRTOS_Source\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\CCS4\MSP430X\*.* FreeRTOS_Source\portable\CCS4\MSP430X
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_1.c FreeRTOS_Source\portable\MemMang

	REM Copy the files that define the common demo tasks.
	copy ..\Common\minimal\dynamic.c Demo_Source\Common_Demo_Files
	copy ..\Common\minimal\comtest.c Demo_Source\Common_Demo_Files
	copy ..\Common\minimal\GenQTest.c Demo_Source\Common_Demo_Files
	
	REM Copy the common demo file headers.
	copy ..\Common\include\dynamic.h Demo_Source\Common_Demo_Files\include
	copy ..\Common\include\comtest.h Demo_Source\Common_Demo_Files\include
	copy ..\Common\include\comtest2.h Demo_Source\Common_Demo_Files\include
	copy ..\Common\include\GenQTest.h Demo_Source\Common_Demo_Files\include
	copy ..\Common\include\serial.h Demo_Source\Common_Demo_Files\include
	copy ..\Common\include\partest.h Demo_Source\Common_Demo_Files\include
	
: END