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
IF EXIST .\FreeRTOS_Source Goto END

    REM Create the required directory structure.
    MD FreeRTOS
    MD FreeRTOS\include
    MD FreeRTOS\portable
    MD FreeRTOS\portable\CCS
    MD FreeRTOS\portable\CCS\ARM_Cortex-R4_RM48_TMS570
    MD FreeRTOS\portable\MemMang    
	MD Common-Demo-Source
    MD Common-Demo-Source\include
    
    REM Copy the core kernel files into the project directory
    copy %FREERTOS_SOURCE%\tasks.c FreeRTOS
    copy %FREERTOS_SOURCE%\queue.c FreeRTOS
    copy %FREERTOS_SOURCE%\list.c FreeRTOS
    copy %FREERTOS_SOURCE%\timers.c FreeRTOS

    REM Copy the common header files into the project directory
    copy %FREERTOS_SOURCE%\include\*.* FreeRTOS\include
    
    REM Copy the portable layer files into the project directory
    copy %FREERTOS_SOURCE%\portable\CCS\ARM_Cortex-R4_RM48_TMS570\*.* FreeRTOS\portable\CCS\ARM_Cortex-R4_RM48_TMS570
    
    REM Copy the memory allocation files into the project directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_4.c FreeRTOS\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy %COMMON_SOURCE%\dynamic.c         Common-Demo-Source
    copy %COMMON_SOURCE%\BlockQ.c          Common-Demo-Source
    copy %COMMON_SOURCE%\death.c           Common-Demo-Source
    copy %COMMON_SOURCE%\blocktim.c        Common-Demo-Source
    copy %COMMON_SOURCE%\semtest.c         Common-Demo-Source
    copy %COMMON_SOURCE%\PollQ.c           Common-Demo-Source
    copy %COMMON_SOURCE%\GenQTest.c        Common-Demo-Source
    copy %COMMON_SOURCE%\recmutex.c        Common-Demo-Source
    copy %COMMON_SOURCE%\countsem.c        Common-Demo-Source
    copy %COMMON_SOURCE%\integer.c         Common-Demo-Source
    
    REM Copy the common demo file headers.
    copy %COMMON_INCLUDE%\*.h              Common-Demo-Source\include
    
: END
