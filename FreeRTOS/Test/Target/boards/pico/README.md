# FreeRTOS SMP SMP on target test for RP2040 Explorer Board

> **FreeRTOS-SMP Kernel is still being tested.**

This page documents a SMP on target test that uses the FreeRTOS symmetric multiprocessing (SMP) version.
The test targets the [RP2040](https://www.raspberrypi.com/documentation/microcontrollers/rp2040.html), which has 2
cores. The project uses [Raspberry Pi Pico SDK](https://github.com/raspberrypi/pico-sdk) to
build the FreeRTOS RP2040 port. This test shows that [Raspberry Pi Pico](https://www.raspberrypi.com/products/raspberry-pi-pico/)
supports [FreeRTOS Kernel Symmetric Multiprocessing (SMP)](https://github.com/FreeRTOS/FreeRTOS-Kernel/tree/smp).

---

## IMPORTANT! Notes on using the FreeRTOS RP2040 SMP on target test

Please read all the following points before using this RTOS port.

1. [Source Code Organization](#source-code-organization)
1. [The SMP On Target Test Application](#the-smp-on-target-test-application)
1. [Building and Running the FreeRTOS SMP On Target Test](#building-and-running-the-smp-on-target-test-application)
1. [FreeRTOS Configuration and Usage Details](#freertos-configuration-and-usage-details)
1. [Trouble Shooting](#)

Also see the FAQ [My application does not run, what could be wrong](https://www.freertos.org/FAQHelp.html)?

---

## Source Code Organization

The project files for this test are located in the [FreeRTOS/Test/Target/boards/pico](./)
directory of the [FreeRTOS repository](https://github.com/FreeRTOS/FreeRTOS).
FreeRTOS Port files compiled in the project are in the
[FreeRTOS/Source/portable/ThirdParty/GCC/RP2040](../../../../Source/portable/ThirdParty/GCC/RP2040/) directory.

Test cases are listed in [FreeRTOS/Test/Target/tests/smp](../../tests/smp) directory.
And [Raspberry Pi Pico](https://www.raspberrypi.com/products/raspberry-pi-pico/) can pass all test cases with corresponding [test_runners](./tests/smp/).

Test cases includes:

-   disable_multiple_priorities
-   disable_preemption
-   interrupt_wait_critical
-   multiple_tasks_running
-   only_one_task_enter_critical
-   only_one_task_enter_suspendall
-   schedule_affinity
-   schedule_equal_priority
-   schedule_highest_priority
-   suspend_scheduler
-   task_delete

---

## The SMP On Target Test Application

The SMP On Target Test is used to verify kernel behavior with SMP(FreeRTOS symmetric multiprocessing)
enabled. Each test case verifies different scenarios on SMP. And the configurations for FreeRTOS are changed
based on test cases, which means it needs several images to test.
To simplify the framework and to debug easily, the test framework uses individual images for each test case.
Each test case has its own [test_runners](./tests/smp/). The SMP On Target Test uses only one tile to run the
test and keep the other tile in idle.

### The SMP On Target Test Flow

The test starts from main() in [main.c](./main.c), then runs the test runner corresponding to each test case.
Take test case `Multiple Tasks Running` as example:

1. Start from main() in [main.c](./main.c).
1. Call vRunTest() in [multiple_tasks_running_test_runner.c](./tests/smp/multiple_tasks_running/multiple_tasks_running_test_runner.c).
1. Create task to run prvTestRunnerTask() in [multiple_tasks_running_test_runner.c](./tests/smp/multiple_tasks_running/multiple_tasks_running_test_runner.c).
1. Execute test case vRunMultipleTasksRunningTest() in [multiple_tasks_running.c](../../tests/smp/multiple_tasks_running/multiple_tasks_running.c).

---

## Building and Running the SMP On Target Test Application

### Hardware setup

Plug the Pico board with your host PC/laptop via USB cable.
To flash the image, you need to press the BOOTSEL button when you're pluging the USB cable.

### Toolchain installation

The development tools can be used on both Linux/Windows environments.

1. Download Pico SDK by following the instructions on Chapter 2 in [Getting Started With Pico](https://datasheets.raspberrypi.org/pico/getting-started-with-pico.pdf).

### Build and Run the application

1. Go to pico directory:

```sh
$ cd FreeRTOS/Test/Target/boards/pico
```

1. Create build directory and go to build folder:

```sh
$ mkdir build
$ cd build
```

1. Build:

    - Linux:

        ```sh
        $ cmake ..\ -GMake
        $ make
        ```

    - Windows:

        ```sh
        $ cmake ..\ -GNinja
        $ ninja
        ```

1. Clean the binaries:

```sh
$ rm *
```

---

## FreeRTOS Configuration and Usage Details

-   Configuration items specific to this test are contained in
    [FreeRTOSConfig.h](./FreeRTOSConfig.h). The
    [constants defined in that file](https://www.freertos.org/a00110.html) can be
    edited to suit your application. The following configuration options are set in test_config.h
    for every test case, which is specific to the SMP support in the FreeRTOS Kernel:
    -   `configNUMBER_OF_CORES` - Set the number of cores.
    -   `configRUN_MULTIPLE_PRIORITIES` - Enable/Disable simultaneously running tasks with multiple priorities.
    -   `configUSE_CORE_AFFINITY` - Enable/Disable setting a task's affinity to certain cores.
    -   `configUSE_TASK_PREEMPTION_DISABLE` - Enable/Disable functions (vTaskPreemptionDisable/vTaskPreemptionEnable)
        to stop preempting MCU resource from specific task.
    -   `configUSE_PREEMPTION` - Enable/Disable preemption as general rule.
-   `Source/Portable/MemMang/heap_4.c` is included in the project to provide the
    memory allocation required by the RTOS kernel. Please refer to the
    [Memory Management](https://www.freertos.org/a00111.html) section of the API
    documentation for complete information.

---

## Trouble Shooting

[RP2040](https://www.raspberrypi.com/documentation/microcontrollers/rp2040.html) supports openocd as on target debug tool.
We can debug with gdb commands by following steps:

1. Follow [Hardware Setup](#hardware-setup) and [Toolchain installation](#toolchain-installation) to set the environment.
1. Set CMAKE_BUILD_TYPE to 'Debug' while building the image.

    - Linux:

        ```sh
        $ cmake ..\ -DCMAKE_BUILD_TYPE='Debug' -GMake
        $ make
        ```

    - Windows:

        ```sh
        $ cmake ..\ -DCMAKE_BUILD_TYPE='Debug' -GNinja
        $ ninja
        ```

1. Follow [Learn how to Program and Debug Raspberry Pi Pico with SWD](https://www.electronicshub.org/programming-raspberry-pi-pico-with-swd/) to do on target debugging with Raspberry Pi via OpenOCD.

---
