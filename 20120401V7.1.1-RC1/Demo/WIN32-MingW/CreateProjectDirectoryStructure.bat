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
	MD FreeRTOS\portable
	MD FreeRTOS\portable\MSVC-MingW
	MD FreeRTOS\portable\MemMang
	MD DemoTasks
	MD DemoTasks\include
	
	REM Copy the core kernel files.
	copy ..\..\Source\tasks.c FreeRTOS
	copy ..\..\Source\queue.c FreeRTOS
	copy ..\..\Source\list.c FreeRTOS
	
	REM Copy the common header files

	copy ..\..\Source\include\*.* FreeRTOS\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\MSVC-MingW\*.* FreeRTOS\portable\MSVC-MingW
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_3.c FreeRTOS\portable\MemMang

	REM Copy the common demo files that are used by this demo
	copy ..\Common\include\BlockQ.h DemoTasks\include
	copy ..\Common\include\integer.h DemoTasks\include
	copy ..\Common\include\semtest.h DemoTasks\include
	copy ..\Common\include\PollQ.h DemoTasks\include
	copy ..\Common\include\GenQTest.h DemoTasks\include
	copy ..\Common\include\QPeek.h DemoTasks\include
	copy ..\Common\include\flop.h DemoTasks\include
	copy ..\Common\include\recmutex.h DemoTasks\include
	copy ..\Common\Minimal\BlockQ.c DemoTasks
	copy ..\Common\Minimal\integer.c DemoTasks
	copy ..\Common\Minimal\semtest.c DemoTasks
	copy ..\Common\Minimal\PollQ.c DemoTasks
	copy ..\Common\Minimal\GenQTest.c DemoTasks
	copy ..\Common\Minimal\QPeek.c DemoTasks
	copy ..\Common\Minimal\flop.c DemoTasks
	
: END