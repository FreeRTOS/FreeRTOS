# Running with VSCode Launch Configurations

## Prerequisites
* Install [C/C++ extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode.cpptools) in VSCode.
* Install [arm-none-eabi-gcc](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads).
* Install GNU make utility.
* Ensure the required binaries are in PATH with ```arm-none-eabi-gcc --version```, ```arm-none-eabi-gdb --version```, and ```make --version```.

## Building and Running
1. Open VSCode to the folder ```FreeRTOS/Demo/CORTEX_MPS2_QEMU_IAR_GCC```.
2. Open ```.vscode/launch.json```, and ensure the ```miDebuggerPath``` variable is set to the path where arm-none-eabi-gdb is on your machine.
3. Open ```main.c```, and set ```mainCREATE_SIMPLE_BLINKY_DEMO_ONLY``` to ```1``` to generate just the [simply blinky demo](https://www.freertos.org/a00102.html#simple_blinky_demo).
4. On the VSCode left side panel, select the “Run and Debug” button. Then select “Launch QEMU RTOSDemo” from the dropdown on the top right and press the play button. This will build, run, and attach a debugger to the demo program.
