# Intro

This directory contains a FreeRTOS project to build either a Blinky, or MPU demo
for the [RM57L843](https://www.ti.com/product/RM57L843) Target.

It is set up to blink LEDs on the Texas Instruments
[LAUNCHXL2-RM57L](https://www.ti.com/tool/LAUNCHXL2-RM57L)
and the [TMDXRM57LHDK](https://www.ti.com/tool/TMDXRM57LHDK) Development Kits.

The code related to the Main Demo Files can be found in the
[source](./source) directory.
The code related to the board setup can be found in the
[BoardFiles](./BoardFiles) directory

## Building

This demo can either be loaded into Texas Instrument's
[Code Composer Studio (CCS)](https://www.ti.com/tool/CCSTUDIO).
or built using [CMake](https://cmake.org/).

### CCS Build

If building with CCS you need to install CCS, and then install the
[ARM Compiler Tools](https://software-dl.ti.com/ccs/esd/documents/ccs_compiler-installation-selection.html#compiler-installation)
as well as the RM57
[device support targets](https://software-dl.ti.com/ccs/esd/documents/users_guide/ccs_installation.html#device-support).

After doing this you can then open this directory in CCS, which will load up the RM57
project. If everything installed correctly you should then be able to build and flash
to the board.

Please be aware there is a filter on [CMakeLists.txt](./CMakeLists.txt) and the *build*
directory in the CCS project.

This is to keep CCS from attempting to use resources generated with a CMAKE build.
If a directory other than "build" is selected when building using CMAKE CCS will
attempt to use the the files in that directory, leading to build issues in CCS.
At time of writing this can be fixed by right clicking the folder in CCS
and selecting "Exclude from build".

### CMake build

When using CMake you will need to install a compatible version of the
[Arm GNU Toolchain](https://developer.arm.com/Tools%20and%20Software/GNU%20Toolchain)
and add this to your `PATH`.

After doing this you can then build either a [Blinky](./source/main_blinky.c#L122),
or the [MPU Demo](../Common/MPU_Demo/mpu_demo.c#L257).
The two targets are the  RM57_FreeRTOS_Blinky_Demo.out, and RM57_FreeRTOS_MPU_Demo.out
binaries.

The `all` options builds both of these.
Example Usage:

```sh
cmake -S . -B build;
make -C build all;
```

The generated binaries can then be found in the `build` directory.
These binaries can then be flashed to the board by using
[Uniflash](https://www.ti.com/tool/UNIFLASH) or by using CCS.

## UART Output

Rudimentary UART output is available by opening a Serial Connection
to the board. The settings for the UART are a BAUD rate of 115200, 1 stopbit,
and None Parity
