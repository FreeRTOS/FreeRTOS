REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Files will also be copied into the BSP directory, which can be used to
REM generate FreeRTOS BSP packages directly from within the Xilinx SDK.
SET BSP_SOURCE=..\..\KernelAwareBSPRepository\bsp\freertos_v2_00_a\src\Source

REM Standard paths
SET FREERTOS_SOURCE=..\..\..\..\Source
SET COMMON_SOURCE=..\..\..\Common\minimal
SET COMMON_INCLUDE=..\..\..\Common\include
SET LWIP_SOURCE=..\..\..\Common\ethernet\lwip-1.4.0

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
    
    REM Copy the core kernel files into the SDK projects directory
    copy %FREERTOS_SOURCE%\tasks.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\queue.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\list.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\timers.c FreeRTOS_Source

    REM Copy the core kernel files into the BSP directory
    copy %FREERTOS_SOURCE%\tasks.c %BSP_SOURCE%
    copy %FREERTOS_SOURCE%\queue.c %BSP_SOURCE%
    copy %FREERTOS_SOURCE%\list.c %BSP_SOURCE%
    copy %FREERTOS_SOURCE%\timers.c %BSP_SOURCE%
    
    REM Copy the common header files into the SDK projects directory
    copy %FREERTOS_SOURCE%\include\*.* FreeRTOS_Source\include
    
    REM Copy the common header files into the BSP directory
    copy %FREERTOS_SOURCE%\include\*.* %BSP_SOURCE%\include

    REM Copy the portable layer files into the SDK projects directory
    copy %FREERTOS_SOURCE%\portable\GCC\MicroBlazeV8\*.* FreeRTOS_Source\portable\GCC\MicroBlazeV8
    
    REM Copy the portable layer files into the BSP projects directory
    copy %FREERTOS_SOURCE%\portable\GCC\MicroBlazeV8\*.* %BSP_SOURCE%\portable\GCC\MicroBlazeV8

    REM Copy the basic memory allocation files into the SDK projects directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_2.c FreeRTOS_Source\portable\MemMang

    REM Copy the basic memory allocation files into the BSP directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_2.c %BSP_SOURCE%\portable\MemMang

    REM Copy the files that define the common demo tasks.
    copy %COMMON_SOURCE%\dynamic.c         Demo_Source
    copy %COMMON_SOURCE%\BlockQ.c          Demo_Source
    copy %COMMON_SOURCE%\death.c           Demo_Source
    copy %COMMON_SOURCE%\blocktim.c        Demo_Source
    copy %COMMON_SOURCE%\semtest.c         Demo_Source
    copy %COMMON_SOURCE%\PollQ.c           Demo_Source
    copy %COMMON_SOURCE%\GenQTest.c        Demo_Source
    copy %COMMON_SOURCE%\QPeek.c           Demo_Source
    copy %COMMON_SOURCE%\recmutex.c        Demo_Source
    copy %COMMON_SOURCE%\sp_flop.c         Demo_Source
    copy %COMMON_SOURCE%\flash.c           Demo_Source
    copy %COMMON_SOURCE%\comtest_strings.c Demo_Source
    copy %COMMON_SOURCE%\TimerDemo.c       Demo_Source
    
    REM Copy the common demo file headers.
    copy %COMMON_INCLUDE%\dynamic.h         Demo_Source\include
    copy %COMMON_INCLUDE%\partest.h         Demo_Source\include
    copy %COMMON_INCLUDE%\BlockQ.h          Demo_Source\include
    copy %COMMON_INCLUDE%\death.h           Demo_Source\include
    copy %COMMON_INCLUDE%\blocktim.h        Demo_Source\include
    copy %COMMON_INCLUDE%\semtest.h         Demo_Source\include
    copy %COMMON_INCLUDE%\PollQ.h           Demo_Source\include
    copy %COMMON_INCLUDE%\GenQTest.h        Demo_Source\include
    copy %COMMON_INCLUDE%\QPeek.h           Demo_Source\include
    copy %COMMON_INCLUDE%\recmutex.h        Demo_Source\include
    copy %COMMON_INCLUDE%\flop.h            Demo_Source\include
    copy %COMMON_INCLUDE%\flash.h           Demo_Source\include
    copy %COMMON_INCLUDE%\comtest_strings.h Demo_Source\include
    copy %COMMON_INCLUDE%\serial.h          Demo_Source\include
    copy %COMMON_INCLUDE%\comtest.h         Demo_Source\include
    copy %COMMON_INCLUDE%\TimerDemo.h       Demo_Source\include
    
    REM Copy the required lwIP files
    copy %LWIP_SOURCE%\src\api\*.c                       lwIP\api
    copy %LWIP_SOURCE%\src\core\*.c                      lwIP\core
    copy %LWIP_SOURCE%\src\core\ipv4\*.c                 lwIP\core\ipv4
    copy %LWIP_SOURCE%\src\include\ipv4\lwip\*.h         lwIP\include\ipv4\lwip
    copy %LWIP_SOURCE%\src\include\lwip\*.h              lwIP\include\lwip
    copy %LWIP_SOURCE%\src\include\netif\*.h             lwIP\include\netif
    copy %LWIP_SOURCE%\src\netif\etharp.c                lwIP\netif
    copy %LWIP_SOURCE%\ports\MicroBlaze-Ethernet-Lite    lwip\netif
    copy %LWIP_SOURCE%\ports\MicroBlaze-Ethernet-Lite\include\arch lwip\netif\include\arch

: END
