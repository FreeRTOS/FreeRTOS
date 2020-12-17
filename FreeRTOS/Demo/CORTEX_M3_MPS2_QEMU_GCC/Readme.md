# Emulating MPS2 Cortex M3 AN385 on QEMU

## Requirements
1. GNU Arm Embedded Toolchain download [here](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads)
3. qemu-arm-system download [here](https://www.qemu.org/download)
2. Make (tested on version 3.82)
4. Linux OS (tested on Ubuntu 18.04)

## How to download
Navigate to a parent directory of your choice and run the following command
```
$ git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules --depth 1
```
The previous command should create a directory named **FreeRTOS**

## Blinky Demo
### How to build blinky demo
Navigate with the command line to FreeRTOS/Demo/CORTEX\_M3\_MPS2\_QEMU\_GCC
For a release build run:

```
$ export PATH=/path/to/arm/toolchain:$PATH
$ make
```
For a versions with debugging symbols and no optimizations **-O0**, run:
```
$ make DEBUG=1
```

### How to run the blinky demo
run:
```
$ sudo qemu-system-arm -machine mps2-an385 -monitor null -semihosting \
        --semihosting-config enable=on,target=native \
        -kernel ./build/RTOSDemo.axf \
        -serial stdio -nographic
```
### Blinky Demo Expectations
after running the blinky demo you shoud see on the screen the word blinking
printed continuously


## How to start debugging
1. gdb
<P>
Append the -s and -S switches to the previous command (qemu-system-arm)<br>
-s: allow gdb to be attached to the process remotely at port 1234 <br>
-S: start the program in the paused state <br>

run: (make sure you build the debug version)
```
$ arm-none-eabi-gdb -q ./build/RTOSDemo.axf

(gdb) target remote :1234
(gdb) break main
(gdb) c
```
