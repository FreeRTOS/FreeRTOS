REM Copy the FreeRTOS source files, including the Cortex-A9 and Microblaze port
REM layers into the repository directory structure.

copy ..\..\Source\*.c .\repo\bsp\freertos822_xilinx_v1_0\src\Source
copy ..\..\Source\include\*.h .\repo\bsp\freertos822_xilinx_v1_0\src\Source\include
copy ..\..\Source\portable\GCC\ARM_CA9\*.* .\repo\bsp\freertos822_xilinx_v1_0\src\Source\portable\GCC\ARM_CA9
copy ..\..\Source\portable\GCC\MicroBlazeV8\*.* .\repo\bsp\freertos822_xilinx_v1_0\src\Source\portable\GCC\MicroBlazeV8
copy ..\..\Source\portable\MemMang\heap_4.c .\repo\bsp\freertos822_xilinx_v1_0\src\Source\portable\MemMang

