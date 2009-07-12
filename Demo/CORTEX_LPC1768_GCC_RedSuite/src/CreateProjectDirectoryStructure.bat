REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST FreeRTOS Goto END

	REM Create the required directory structure.
	MD FreeRTOS
	MD FreeRTOS\include	
	MD FreeRTOS\portable\GCC\ARM_CM3
	MD FreeRTOS\portable\MemMang	
	MD "Common Demo Tasks"
	MD "Common Demo Tasks\include"
	
	REM Copy the core kernel files.
	copy ..\..\..\Source\tasks.c FreeRTOS
	copy ..\..\..\Source\queue.c FreeRTOS
	copy ..\..\..\Source\list.c FreeRTOS
	
	REM Copy the common header files

	copy ..\..\..\Source\include\*.* FreeRTOS\include
	
	REM Copy the portable layer files
	copy ..\..\..\Source\portable\GCC\ARM_CM3\*.* FreeRTOS\portable\GCC\ARM_CM3
	
	REM Copy the basic memory allocation files
	copy ..\..\..\Source\portable\MemMang\*.* FreeRTOS\portable\MemMang

	REM Copy the files that define the common demo tasks.
	copy ..\..\Common\minimal\BlockQ.c "Common Demo Tasks"
	copy ..\..\Common\minimal\blocktim.c "Common Demo Tasks"
	copy ..\..\Common\minimal\flash.c "Common Demo Tasks"
	copy ..\..\Common\minimal\GenQTest.c "Common Demo Tasks"
	copy ..\..\Common\minimal\integer.c "Common Demo Tasks"
	copy ..\..\Common\minimal\PollQ.c "Common Demo Tasks"
	copy ..\..\Common\minimal\QPeek.c "Common Demo Tasks"
	copy ..\..\Common\minimal\recmutex.c "Common Demo Tasks"
	copy ..\..\Common\minimal\semtest.c "Common Demo Tasks"
	
	REM Copy the common demo file headers.
	copy ..\..\Common\include\*.* "Common Demo Tasks\include"
	
: END