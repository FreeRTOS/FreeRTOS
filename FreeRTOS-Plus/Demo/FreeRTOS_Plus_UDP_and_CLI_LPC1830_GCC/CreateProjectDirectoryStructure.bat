REM This file should be executed from the command line prior to the first
REM build.  It will be necessary to refresh the Eclipse project once the
REM .bat file has been executed (normally just press F5 to refresh).

REM Copies all the required files from their location within the standard
REM FreeRTOS directory structure to under the Eclipse project directory.
REM This permits the Eclipse project to be used in 'managed' mode and without
REM having to setup any linked resources.

REM Standard paths
SET FREERTOS_SOURCE=..\..\..\FreeRTOS\Source
SET FREERTOS_UDP_SOURCE=..\..\Source\FreeRTOS-Plus-UDP
SET FREERTOS_CLI_SOURCE=..\..\Source\FreeRTOS-Plus-CLI

REM Have the files already been copied?
IF EXIST FreeRTOS_Source Goto END

    REM Create the required directory structure.
    MD FreeRTOS_Source
    MD FreeRTOS_Source\include
    MD FreeRTOS_Source\portable\
	MD FreeRTOS_Source\portable\GCC
    MD FreeRTOS_Source\portable\GCC\ARM_CM3
    MD FreeRTOS_Source\portable\MemMang
	MD FreeRTOS_Plus_UDP
	MD FreeRTOS_Plus_UDP\include
	MD FreeRTOS_Plus_UDP\portable
	MD FreeRTOS_Plus_UDP\portable\Compiler
	MD FreeRTOS_Plus_UDP\portable\Compiler\GCC
	MD FreeRTOS_Plus_UDP\portable\BufferManagement
	MD FreeRTOS_Plus_UDP\portable\NetworkInterface
	MD FreeRTOS_Plus_UDP\portable\NetworkInterface\LPC18xx
	MD FreeRTOS_Plus_CLI
	MD Examples\Ethernet

    REM Copy the core kernel files into the SDK projects directory
    copy %FREERTOS_SOURCE%\tasks.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\queue.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\list.c FreeRTOS_Source
    copy %FREERTOS_SOURCE%\timers.c FreeRTOS_Source

    REM Copy the common header files into the SDK projects directory
    copy %FREERTOS_SOURCE%\include\*.* FreeRTOS_Source\include

    REM Copy the portable layer files into the projects directory
    copy %FREERTOS_SOURCE%\portable\GCC\ARM_CM3\*.* FreeRTOS_Source\portable\GCC\ARM_CM3

    REM Copy the memory allocation file into the project's directory
    copy %FREERTOS_SOURCE%\portable\MemMang\heap_4.c FreeRTOS_Source\portable\MemMang

	REM Copy the FreeRTOS+UDP core files
	copy %FREERTOS_UDP_SOURCE%\*.c FreeRTOS_Plus_UDP
	copy %FREERTOS_UDP_SOURCE%\*.h FreeRTOS_Plus_UDP
	copy %FREERTOS_UDP_SOURCE%\readme.txt FreeRTOS_Plus_UDP
	copy %FREERTOS_UDP_SOURCE%\include\*.* FreeRTOS_Plus_UDP\include

	REM Copy the FreeRTOS+UDP portable layer files
	copy %FREERTOS_UDP_SOURCE%\portable\NetworkInterface\LPC18xx\*.* FreeRTOS_Plus_UDP\portable\NetworkInterface\LPC18xx
	copy %FREERTOS_UDP_SOURCE%\portable\NetworkInterface\*.* FreeRTOS_Plus_UDP\portable\NetworkInterface
	copy %FREERTOS_UDP_SOURCE%\portable\BufferManagement\BufferAllocation_2.c FreeRTOS_Plus_UDP\portable\BufferManagement
	copy %FREERTOS_UDP_SOURCE%\portable\Compiler\GCC\*.* FreeRTOS_Plus_UDP\portable\Compiler\GCC

	REM Copy the FreeRTOS+CLI files
	copy %FREERTOS_CLI_SOURCE%\*.* FreeRTOS_Plus_CLI

	REM Copy the echo client example implementation
	copy ..\Common\FreeRTOS_Plus_UDP_Demos\EchoClients\TwoEchoClients.c Examples\Ethernet
	copy ..\Common\FreeRTOS_Plus_UDP_Demos\EchoClients\TwoEchoClients.h Examples\include

	REM Copy the example IP trace macro implementation
	copy ..\Common\FreeRTOS_Plus_UDP_Demos\TraceMacros\Example1\DemoIPTrace.c Examples\Ethernet
	copy ..\Common\FreeRTOS_Plus_UDP_Demos\TraceMacros\Example1\DemoIPTrace.h Examples\include

	REM Copy the CLI commands implementation into the project directory.
	copy ..\Common\FreeRTOS_Plus_UDP_Demos\CLICommands\CLI-commands.c .

: END
