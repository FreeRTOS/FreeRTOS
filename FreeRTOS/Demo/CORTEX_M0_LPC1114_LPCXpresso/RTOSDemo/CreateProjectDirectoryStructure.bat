REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST Source\FreeRTOS_Source Goto END

	REM Create the required directory structure.
	MD Source\FreeRTOS_Source
	MD Source\FreeRTOS_Source\include
	MD Source\FreeRTOS_Source\portable
	MD Source\FreeRTOS_Source\portable\GCC
	MD Source\FreeRTOS_Source\portable\GCC\ARM_CM0
	MD Source\FreeRTOS_Source\portable\MemMang
	MD Source\Common_Demo_Tasks
	MD Source\Common_Demo_Tasks\include
	
	REM Copy the core kernel files.
	copy ..\..\..\Source\tasks.c Source\FreeRTOS_Source
	copy ..\..\..\Source\queue.c Source\FreeRTOS_Source
	copy ..\..\..\Source\list.c Source\FreeRTOS_Source
	copy ..\..\..\Source\timers.c Source\FreeRTOS_Source
	
	REM Copy the common header files

	copy ..\..\..\Source\include\*.* Source\FreeRTOS_Source\include
	
	REM Copy the portable layer files
	copy ..\..\..\Source\portable\GCC\ARM_CM0\*.* Source\FreeRTOS_Source\portable\GCC\ARM_CM0
	
	REM Copy the basic memory allocation files
	copy ..\..\..\Source\portable\MemMang\heap_1.c Source\FreeRTOS_Source\portable\MemMang

	REM Copy the files that define the common demo tasks.
	copy ..\..\Common\minimal\blocktim.c Source\Common_Demo_Tasks
	copy ..\..\Common\minimal\recmutex.c Source\Common_Demo_Tasks
	copy ..\..\Common\minimal\countsem.c Source\Common_Demo_Tasks
	copy ..\..\Common\minimal\IntQueue.c Source\Common_Demo_Tasks
	
	REM Copy the common demo file headers.
	copy ..\..\Common\include\blocktim.h Source\Common_Demo_Tasks\include
	copy ..\..\Common\include\recmutex.h Source\Common_Demo_Tasks\include
	copy ..\..\Common\include\countsem.h Source\Common_Demo_Tasks\include
	copy ..\..\Common\include\IntQueue.h Source\Common_Demo_Tasks\include
	
: END