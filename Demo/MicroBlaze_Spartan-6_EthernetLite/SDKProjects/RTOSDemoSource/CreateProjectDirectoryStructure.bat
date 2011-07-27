REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Have the files already been copied?
IF EXIST FreeRTOS_Source Goto END

    REM Create the required directory structure.
    MD FreeRTOS_Source
    MD FreeRTOS_Source\include    
    MD FreeRTOS_Source\portable\GCC
    MD FreeRTOS_Source\portable\GCC\MicroBlazeV8
    MD FreeRTOS_Source\portable\MemMang    
    MD Demo_Source
    MD Demo_Source\include
    MD lwIP\api
    MD lwIP\core
    MD lwIP\core\ipv4
    MD lwIP\include
    MD lwIP\include\ipv4
    MD lwIP\include\ipv4\lwip
    MD lwIP\include\lwip
    MD lwIP\include\netif
    MD lwIP\netif
    MD lwIP\netif\include
    MD lwIP\netif\include\arch
    
    REM Copy the core kernel files.
    copy ..\..\..\..\Source\tasks.c FreeRTOS_Source
    copy ..\..\..\..\Source\queue.c FreeRTOS_Source
    copy ..\..\..\..\Source\list.c FreeRTOS_Source
    copy ..\..\..\..\Source\timers.c FreeRTOS_Source
    
    REM Copy the common header files
    copy ..\..\..\..\Source\include\*.* FreeRTOS_Source\include
    
    REM Copy the portable layer files
    copy ..\..\..\..\Source\portable\GCC\MicroBlazeV8\*.* FreeRTOS_Source\portable\GCC\MicroBlazeV8
    
    REM Copy the basic memory allocation files
    copy ..\..\..\..\Source\portable\MemMang\heap_2.c FreeRTOS_Source\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy ..\..\..\Common\minimal\dynamic.c         Demo_Source
    copy ..\..\..\Common\minimal\BlockQ.c          Demo_Source
    copy ..\..\..\Common\minimal\death.c           Demo_Source
    copy ..\..\..\Common\minimal\blocktim.c        Demo_Source
    copy ..\..\..\Common\minimal\semtest.c         Demo_Source
    copy ..\..\..\Common\minimal\PollQ.c           Demo_Source
    copy ..\..\..\Common\minimal\GenQTest.c        Demo_Source
    copy ..\..\..\Common\minimal\QPeek.c           Demo_Source
    copy ..\..\..\Common\minimal\recmutex.c        Demo_Source
    copy ..\..\..\Common\minimal\sp_flop.c         Demo_Source
    copy ..\..\..\Common\minimal\flash.c           Demo_Source
    copy ..\..\..\Common\minimal\comtest_strings.c Demo_Source
    copy ..\..\..\Common\minimal\TimerDemo.c       Demo_Source
    
    REM Copy the common demo file headers.
    copy ..\..\..\Common\include\dynamic.h         Demo_Source\include
    copy ..\..\..\Common\include\partest.h         Demo_Source\include
    copy ..\..\..\Common\include\BlockQ.h          Demo_Source\include
    copy ..\..\..\Common\include\death.h           Demo_Source\include
    copy ..\..\..\Common\include\blocktim.h        Demo_Source\include
    copy ..\..\..\Common\include\semtest.h         Demo_Source\include
    copy ..\..\..\Common\include\PollQ.h           Demo_Source\include
    copy ..\..\..\Common\include\GenQTest.h        Demo_Source\include
    copy ..\..\..\Common\include\QPeek.h           Demo_Source\include
    copy ..\..\..\Common\include\recmutex.h        Demo_Source\include
    copy ..\..\..\Common\include\flop.h            Demo_Source\include
    copy ..\..\..\Common\include\flash.h           Demo_Source\includeREM
    copy ..\..\..\Common\include\comtest_strings.h Demo_Source\include
    copy ..\..\..\Common\include\serial.h          Demo_Source\include
    copy ..\..\..\Common\include\comtest.h         Demo_Source\include
    copy ..\..\..\Common\include\TimerDemo.h       Demo_Source\include
    
    REM Copy the required lwIP files
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\api\*.c                       lwIP\api
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\core\*.c                      lwIP\core
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\core\ipv4\*.c                 lwIP\core\ipv4
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\include\ipv4\lwip\*.h         lwIP\include\ipv4\lwip
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\include\lwip\*.h              lwIP\include\lwip
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\include\netif\*.h             lwIP\include\netif
    copy ..\..\..\Common\ethernet\lwip-1.4.0\src\netif\etharp.c                lwIP\netif
    copy ..\..\..\Common\ethernet\lwip-1.4.0\ports\MicroBlaze-Ethernet-Lite    lwip\netif
    copy ..\..\..\Common\ethernet\lwip-1.4.0\ports\MicroBlaze-Ethernet-Lite\include\arch lwip\netif\include\arch

: END
