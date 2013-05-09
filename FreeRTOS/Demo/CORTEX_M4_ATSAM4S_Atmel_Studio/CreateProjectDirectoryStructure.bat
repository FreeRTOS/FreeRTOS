REM This file should be executed from the command line prior to the first
REM build. Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Atmel Studio project directory.

REM Standard paths
SET FREERTOS_SOURCE=..\..\Source
SET COMMON_SOURCE=..\Common\minimal
SET COMMON_INCLUDE=..\Common\include

REM Have the files already been copied?
IF EXIST src\asf\thirdparty\FreeRTOS Goto END

    REM Create the required directory structure.
    MD src\asf\thirdparty\FreeRTOS
    MD src\asf\thirdparty\FreeRTOS\include
    MD src\asf\thirdparty\FreeRTOS\portable
    MD src\asf\thirdparty\FreeRTOS\portable\GCC
    MD src\asf\thirdparty\FreeRTOS\portable\GCC\ARM_CM3
    MD src\asf\thirdparty\FreeRTOS\portable\MemMang
    MD src\Common-Demo-Source\include

    REM Copy the core kernel files into the project directory
    copy %FREERTOS_SOURCE%\tasks.c src\asf\thirdparty\FreeRTOS
    copy %FREERTOS_SOURCE%\queue.c src\asf\thirdparty\FreeRTOS
    copy %FREERTOS_SOURCE%\list.c src\asf\thirdparty\FreeRTOS
    copy %FREERTOS_SOURCE%\timers.c src\asf\thirdparty\FreeRTOS

    REM Copy the common header files into the project directory
    copy %FREERTOS_SOURCE%\include\*.* src\asf\thirdparty\FreeRTOS\include

    REM Copy the portable layer files into the project directory
    copy %FREERTOS_SOURCE%\portable\GCC\ARM_CM3\*.* src\asf\thirdparty\FreeRTOS\portable\GCC\ARM_CM3

    REM Copy the memory allocation files into the project directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_4.c src\asf\thirdparty\FreeRTOS\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy %COMMON_SOURCE%\dynamic.c         src\Common-Demo-Source
    copy %COMMON_SOURCE%\BlockQ.c          src\Common-Demo-Source
    copy %COMMON_SOURCE%\flash_timer.c     src\Common-Demo-Source
    copy %COMMON_SOURCE%\death.c           src\Common-Demo-Source
    copy %COMMON_SOURCE%\blocktim.c        src\Common-Demo-Source
    copy %COMMON_SOURCE%\semtest.c         src\Common-Demo-Source
    copy %COMMON_SOURCE%\PollQ.c           src\Common-Demo-Source
    copy %COMMON_SOURCE%\GenQTest.c        src\Common-Demo-Source
    copy %COMMON_SOURCE%\recmutex.c        src\Common-Demo-Source
    copy %COMMON_SOURCE%\countsem.c        src\Common-Demo-Source
    copy %COMMON_SOURCE%\integer.c         src\Common-Demo-Source
    copy %COMMON_SOURCE%\QueueSet.c        src\Common-Demo-Source

    REM Copy the common demo file headers.
    copy %COMMON_INCLUDE%\*.h              src\Common-Demo-Source\include

: END
