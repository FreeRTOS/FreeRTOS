REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST FreeRTOS Goto END

	REM Create the required directory structure.
	MD FreeRTOS
	MD FreeRTOS\include	
	MD FreeRTOS\portable\GCC\AVR32_UC3
	MD FreeRTOS\portable\MemMang	
	MD Common_Demo_Tasks
	MD Common_Demo_Tasks\Minimal
	MD Common_Demo_Tasks\include
	
	REM Copy the core kernel files.
	copy ..\..\Source\*.* FreeRTOS
	
	REM Copy the common header files
	copy ..\..\Source\include\*.* FreeRTOS\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\GCC\AVR32_UC3\*.* FreeRTOS\portable\GCC\AVR32_UC3
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_3.c FreeRTOS\portable\MemMang

	REM Copy the files that define the common demo tasks.
	copy ..\common\Minimal\BlockQ.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\comtest.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\death.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\dynamic.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\flash.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\flop.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\integer.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\PollQ.c Common_Demo_Tasks\Minimal
	copy ..\common\Minimal\semtest.c Common_Demo_Tasks\Minimal
	
	REM Copy the common demo file headers.
	copy ..\common\include\*.* Common_Demo_Tasks\include
	
: END
