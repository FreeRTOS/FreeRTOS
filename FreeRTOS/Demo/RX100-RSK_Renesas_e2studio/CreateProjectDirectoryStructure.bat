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
IF EXIST RTOSDemo\FreeRTOS_Source Goto END

    REM Create the required directory structure.
    MD RTOSDemo\FreeRTOS_Source
	MD RTOSDemo\FreeRTOS_Source\include
	MD RTOSDemo\FreeRTOS_Source\portable
	MD RTOSDemo\FreeRTOS_Source\portable\MemMang
	MD RTOSDemo\FreeRTOS_Source\portable\Renesas
	MD RTOSDemo\FreeRTOS_Source\portable\Renesas\RX100
    MD RTOSDemo\Common_Demo_Tasks
	MD RTOSDemo\Common_Demo_Tasks\include

    REM Copy the core kernel files into the project directory
    copy %FREERTOS_SOURCE%\tasks.c RTOSDemo\FreeRTOS_Source
    copy %FREERTOS_SOURCE%\queue.c RTOSDemo\FreeRTOS_Source
    copy %FREERTOS_SOURCE%\list.c RTOSDemo\FreeRTOS_Source
    copy %FREERTOS_SOURCE%\timers.c RTOSDemo\FreeRTOS_Source

    REM Copy the common header files into the project directory
    copy %FREERTOS_SOURCE%\include\*.* RTOSDemo\FreeRTOS_Source\include

    REM Copy the portable layer files into the project directory
    copy %FREERTOS_SOURCE%\portable\Renesas\RX100\*.* RTOSDemo\FreeRTOS_Source\portable\Renesas\RX100

    REM Copy the memory allocation files into the project directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_4.c RTOSDemo\FreeRTOS_Source\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy %COMMON_SOURCE%\death.c           RTOSDemo\Common_Demo_Tasks
    copy %COMMON_SOURCE%\blocktim.c        RTOSDemo\Common_Demo_Tasks
    copy %COMMON_SOURCE%\GenQTest.c        RTOSDemo\Common_Demo_Tasks
    copy %COMMON_SOURCE%\recmutex.c        RTOSDemo\Common_Demo_Tasks

    REM Copy the common demo file headers.
    copy %COMMON_INCLUDE%\*.h              RTOSDemo\Common_Demo_Tasks\include

: END
