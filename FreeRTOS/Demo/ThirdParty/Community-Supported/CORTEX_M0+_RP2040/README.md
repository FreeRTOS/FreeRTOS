## Introduction

These are the demo programs for the RP2040 port of the FreeRTOS-Kernel. Note that these
same examples are used for both the regular and SMP versions of the RP2040 FreeRTOS-Kernel, although obviously the SMP specific examples are skipped in the former.

To switch between SMP or regular FreeRTOS-Kernel, you can currently change the branch of the FreeRTOS-Kernel at `/Source` between `main` and `smp`, or you can use the `FREERTOS_KERNEL_PATH` (see below) to point to the version you want.

## Building

The examples build as regular Raspberry Pi Pico SDK applications. You can build either from this root directory, or build from within the individual examples' directories.

See [Getting Started With Pico](https://datasheets.raspberrypi.org/pico/getting-started-with-pico.pdf) in the SDK documentation for setting up a Raspberry Pi Pico SDK build environment. If you are already set up, then just make sure `PICO_SDK_PATH` is set in your environment or pass it via `-DPICO_SDK_PATH=xxx` on the Cmake command line.

To build from the command line on unix, from this directory (or from the individual examples' directories), type:

```shell
mkdir build
cd build
cmake ..
make
```

This will generate `.uf2` files for each example under the relevant build directories.

You may set `FREERTOS_KERNEL_PATH` in your environment or on the CMake command line to point at a specific instance of the FreeRTOS Kernel, otherwise the version from `Source/` within this project is used.

## Demos

### Standard

These are the standard _Minimal_ main_blink and main_full test demos.

### OnEitherCore

Two versions of the same demo of interaction with SDK code running on one core, and FreeRTOS tasks running on the other (and the use of SDK synchronization primitives to communicate between them). One version has FreeRTOS on core 0, the other has FreeRTOS on core 1.