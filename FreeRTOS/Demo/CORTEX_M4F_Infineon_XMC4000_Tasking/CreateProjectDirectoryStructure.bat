REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Standard paths
SET FREERTOS_SOURCE=..\..\Source
SET COMMON_SOURCE=..\Common\minimal
SET COMMON_INCLUDE=..\Common\include

REM Have the files already been copied?
IF EXIST FreeRTOS_Source Goto END

    REM Create the required directory structure.
    MD FreeRTOS_Source
    MD FreeRTOS_Source\include    
    MD FreeRTOS_Source\portable\
	MD FreeRTOS_Source\portable\Tasking
    MD FreeRTOS_Source\portable\Tasking\ARM_CM4F
    MD FreeRTOS_Source\portable\MemMang    
    MD Common_Demo_Source
    MD Common_Demo_Source\include
    
    REM Copy the core kernel files into the SDK projects directory
    copy %FREERTOS_SOURCE%\tasks.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\queue.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\list.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\timers.c FreeRTOS_Source

    REM Copy the common header files into the SDK projects directory
    copy %FREERTOS_SOURCE%\include\*.* FreeRTOS_Source\include
    
    REM Copy the portable layer files into the projects directory
    copy %FREERTOS_SOURCE%\portable\Tasking\ARM_CM4F\*.* FreeRTOS_Source\portable\Tasking\ARM_CM4F
    
    REM Copy the basic memory allocation files into the SDK projects directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_2.c FreeRTOS_Source\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy %COMMON_SOURCE%\dynamic.c         Common_Demo_Source
    copy %COMMON_SOURCE%\blocktim.c        Common_Demo_Source
    copy %COMMON_SOURCE%\recmutex.c        Common_Demo_Source
    copy %COMMON_SOURCE%\sp_flop.c         Common_Demo_Source
    copy %COMMON_SOURCE%\QueueSet.c        Common_Demo_Source
	copy %COMMON_SOURCE%\QueueOverwrite.c  Common_Demo_Source
	copy %COMMON_SOURCE%\GenQTest.c        Common_Demo_Source
    
    REM Copy the common demo file headers.
    copy %COMMON_INCLUDE%\*.h              Common_Demo_Source\include
    
: END
