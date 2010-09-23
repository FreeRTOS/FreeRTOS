REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST src\FreeRTOS Goto END

	REM Create the required directory structure.
	MD src\FreeRTOS
	MD src\FreeRTOS\include	
	MD src\FreeRTOS\portable\GCC\ARM_CM3_MPU
	MD src\FreeRTOS\portable\MemMang	
	
	REM Copy the core kernel files.
	copy ..\..\Source\tasks.c src\FreeRTOS
	copy ..\..\Source\queue.c src\FreeRTOS
	copy ..\..\Source\list.c src\FreeRTOS
	
	REM Copy the common header files

	copy ..\..\Source\include\*.* src\FreeRTOS\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\GCC\ARM_CM3_MPU\*.* src\FreeRTOS\portable\GCC\ARM_CM3_MPU
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_2.c src\FreeRTOS\portable\MemMang

: END