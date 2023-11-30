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
	MD FreeRTOS_Source\portable\GCC
	MD FreeRTOS_Source\portable\GCC\ARM_CM3
	MD FreeRTOS_Source\portable\MemMang	
	
	REM Copy the core kernel files.
	copy ..\..\Source\tasks.c FreeRTOS_Source
	copy ..\..\Source\queue.c FreeRTOS_Source
	copy ..\..\Source\list.c FreeRTOS_Source
	copy ..\..\Source\timers.c FreeRTOS_Source
	
	REM Copy the common header files

	copy ..\..\Source\include\*.* FreeRTOS_Source\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\GCC\ARM_CM3\*.* FreeRTOS_Source\portable\GCC\ARM_CM3
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_1.c FreeRTOS_Source\portable\MemMang
	
: END
