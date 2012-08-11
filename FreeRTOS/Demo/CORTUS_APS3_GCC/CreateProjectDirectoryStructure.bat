REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST Source Goto END

	REM Create the required directory structure.
	MD Source
	MD Source\include	
	MD Source\portable\GCC\CORTUS_APS3
	MD Source\portable\MemMang	
	MD Demo\Common
	MD Demo\Common\include
	
	REM Copy the core kernel files.
	copy ..\..\Source\*.* Source
	
	REM Copy the common header files
	copy ..\..\Source\include\*.* Source\include
	
	REM Copy the portable layer files
	copy ..\..\Source\portable\GCC\CORTUS_APS3\*.* Source\portable\GCC\CORTUS_APS3
	
	REM Copy the basic memory allocation files
	copy ..\..\Source\portable\MemMang\heap_2.c Source\portable\MemMang

	REM Copy the files that define the common demo tasks.
	copy ..\common\Minimal\BlockQ.c Demo\Common
	copy ..\common\Minimal\comtest.c Demo\Common
	copy ..\common\Minimal\dynamic.c Demo\Common
	copy ..\common\Minimal\flash.c Demo\Common
	copy ..\common\Minimal\integer.c Demo\Common
	copy ..\common\Minimal\PollQ.c Demo\Common
	copy ..\common\Minimal\semtest.c Demo\Common
	
	REM Copy the common demo file headers.
	copy ..\common\include\*.* Demo\Common\include
	
: END
