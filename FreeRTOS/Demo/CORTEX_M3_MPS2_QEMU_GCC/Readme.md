# Emulating MPS2 Cortex M3 AN385 on QEMU

## Requirements
1. GNU Arm Embedded Toolchain download [here](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads)
3. qemu-arm-system downlaod [here](https://www.qemu.org/download)
2. Make (tested on version 3.82)
4. Linux OS (tested on Ubuntu 18.04)

## How to build
    Navigate with the command line to FreeRTOS/Demo/CORTEX_M3_MPS2_QEMU_GCC
    For a realease build run:
    ```
    $ make
    ```
    and for a versions with debugging symbols and no optimizations activated, run:
    ```
    $ make DEBUG=1
    ```

## How to run
run:
```
$ qemu-system-arm -machine mps2-an385 -monitor null -semihosting \
        --semihosting-config enable=on,target=native \
        -kernel /path/to/executable/mps2_demo -serial stdio -nographic
```

## How to start debugging (gdb)
Append the -s and -S switches to the previous command (qemu-system-arm)
-s: allow gdb to be attached to the process remotely at port 1234
-S: start the program in the paused state

run: (make sure you build the debug version)
```
arm-none-eabi-gdb -q /path/to/executable/mps2_demo 
```

