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
IF EXIST src\FreeRTOS_Source Goto END

    REM Create the required directory structure.
    MD src\FreeRTOS_Source
    MD src\FreeRTOS_Source\include    
    MD src\FreeRTOS_Source\portable\GCC
    MD src\FreeRTOS_Source\portable\GCC\ARM_CM4F
    MD src\FreeRTOS_Source\portable\MemMang    
    MD src\Common_Demo_Source
    MD src\Common_Demo_Source\include
    
    REM Copy the core kernel files into the SDK projects directory
    copy %FREERTOS_SOURCE%\tasks.c src\FreeRTOS_Source
    copy %FREERTOS_SOURCE%\queue.c src\FreeRTOS_Source
    copy %FREERTOS_SOURCE%\list.c src\FreeRTOS_Source
    copy %FREERTOS_SOURCE%\timers.c src\FreeRTOS_Source

    REM Copy the common header files into the SDK projects directory
    copy %FREERTOS_SOURCE%\include\*.* src\FreeRTOS_Source\include
    
    REM Copy the portable layer files into the projects directory
    copy %FREERTOS_SOURCE%\portable\GCC\ARM_CM4F\*.* src\FreeRTOS_Source\portable\GCC\ARM_CM4F
    
    REM Copy the basic memory allocation files into the SDK projects directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_2.c src\FreeRTOS_Source\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy %COMMON_SOURCE%\dynamic.c         src\Common_Demo_Source
    copy %COMMON_SOURCE%\BlockQ.c          src\Common_Demo_Source
    copy %COMMON_SOURCE%\death.c           src\Common_Demo_Source
    copy %COMMON_SOURCE%\blocktim.c        src\Common_Demo_Source
    copy %COMMON_SOURCE%\semtest.c         src\Common_Demo_Source
    copy %COMMON_SOURCE%\PollQ.c           src\Common_Demo_Source
    copy %COMMON_SOURCE%\GenQTest.c        src\Common_Demo_Source
    copy %COMMON_SOURCE%\recmutex.c        src\Common_Demo_Source
    copy %COMMON_SOURCE%\sp_flop.c         src\Common_Demo_Source
    copy %COMMON_SOURCE%\countsem.c        src\Common_Demo_Source
    copy %COMMON_SOURCE%\integer.c         src\Common_Demo_Source
    
    REM Copy the common demo file headers.
    copy %COMMON_INCLUDE%\*.h              src\Common_Demo_Source\include
    
: END
