REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST RTOSDemo\FreeRTOS Goto END

	REM Create the required directory structure.
	MD RTOSDemo\FreeRTOS
	MD RTOSDemo\FreeRTOS\include	
	MD RTOSDemo\FreeRTOS\portable\GCC\NiosII
	MD RTOSDemo\FreeRTOS\portable\MemMang	
	MD "RTOSDemo\Common_Demo_Tasks"
	MD "RTOSDemo\Common_Demo_Tasks\include"
	
	REM Copy the core kernel files.
	copy ..\..\Source\tasks.c RTOSDemo\FreeRTOS
	copy ..\..\Source\queue.c RTOSDemo\FreeRTOS
	copy ..\..\Source\list.c RTOSDemo\FreeRTOS
	
	REM Copy the common header files

	copy ..\..\Source\include\*.* RTOSDemo\FreeRTOS\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\GCC\NiosII\*.* RTOSDemo\FreeRTOS\portable\GCC\NiosII
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_2.c RTOSDemo\FreeRTOS\portable\MemMang

	REM Copy the files that define the Common_Demo_Tasks.
	copy ..\Common\minimal\BlockQ.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\blocktim.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\comtest.c "RTOSDemo\Common_Demo_Tasks"	
	copy ..\Common\minimal\countsem.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\death.c "RTOSDemo\Common_Demo_Tasks"	
	copy ..\Common\minimal\dynamic.c "RTOSDemo\Common_Demo_Tasks"	
	copy ..\Common\minimal\flash.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\GenQTest.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\integer.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\PollQ.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\QPeek.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\recmutex.c "RTOSDemo\Common_Demo_Tasks"
	copy ..\Common\minimal\semtest.c "RTOSDemo\Common_Demo_Tasks"
	
	REM Copy the common demo file headers.
	copy ..\Common\include\*.* "RTOSDemo\Common_Demo_Tasks\include"
	
: END
