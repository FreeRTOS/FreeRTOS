# Emulating MPS2 Cortex M3 AN385 on QEMU

## Requirements
1. GNU Arm Embedded Toolchain download [here](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads) (tested on versiom 9.3.1 20200408)
3. qemu-arm-system download [here](https://www.qemu.org/download) (tested on version 5.0.1 (v5.0.1-dirty))
2. Make (tested on version 3.82)
4. Linux OS (tested on Ubuntu 18.04)

## How to download
Navigate to a parent directory of your choice and run the following command
```
$ git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules --depth 1
```
The previous command should create a directory named **FreeRTOS**

## Getting Started on Windows using WSL
The Windows Subsystem for Linux allows you to run native Linux applications from a shell on your windows machine.

To set up your Windows 10 machine to run this QEMU based demo you can follow these steps
1. Install Ubuntu 20.04 LTS version from Microsoft Store, search for "Ubuntu"
2. Update apt-get
```
sudo apt-get update
```
3. Install Make and Qemu
```
sudo apt-get install -y make qemu qemu-system-arm
```
4. Download and unzip Arm tools
```
cd ~
curl https://armkeil.blob.core.windows.net/developer/Files/downloads/gnu-rm/10-2020q4/gcc-arm-none-eabi-10-2020-q4-major-x86_64-linux.tar.bz2 -o gcc-arm-none-eabi-10-2020-q4-major-x86_64-linux.tar.bz2
tar -xjvf gcc-arm-none-eabi-10-2020-q4-major-x86_64-linux.tar.bz2
```

5. Update your path to include the arm toolchain Edit ".profile", add the unzipped bin folder to the front of the path. You can run the same command in the terminal to update the path temporarily in the current shell
```
export PATH="$HOME/gcc-arm-none-eabi-10-2020-q4-major/bin:$PATH"
```

6. Clone FreeRTOS
```
git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules
```

7. Compile the code
```
cd ./FreeRTOS/FreeRTOS/Demo/CORTEX_M3_MPS2_QEMU_GCC
make
```
8. Run the Blinky Demo
```
sudo qemu-system-arm -machine mps2-an385 -monitor null -semihosting --semihosting-config enable=on,target=native -kernel ./build/RTOSDemo.axf -serial stdio -nographic
```


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
After running the blinky demo you shoud see on the screen the word blinking
printed continuously

## Full Demo
### How to build the Full Demo
Navigate with the command line to FreeRTOS/Demo/CORTEX\_M3\_MPS2\_QEMU\_GCC
For a release build run:

```
$ export PATH=/path/to/arm/toolchain:$PATH
$ make FULL_DEMO=1
```
For a versions with debugging symbols and no optimizations **-O0**, run:
```
$ make FULL_DEMO=1 DEBUG=1
```

### How to run the Full Demo
run:
```
$ sudo qemu-system-arm -machine mps2-an385 -monitor null -semihosting \
        --semihosting-config enable=on,target=native \
        -kernel ./build/RTOSDemo.axf \
        -serial stdio -nographic
```
### Full Demo Expectations
The full demo includes a ‘check’ that executes every (simulated) ten seconds,
but has the highest priority to ensure it gets processing time. Its main
function is to check all the standard demo tasks are still operational. The
check task maintains a status string that is output to the console each time
it executes. If all the standard demo tasks are running without error, then
the string contains “OK” and the current tick count. If an error has been
detected, then the string contains a message that indicates which task
reported the error.


## How to start debugging
1. Build the debug version by using `DEBUG=1`:
```
$ make DEBUG=1
```
2. Run the binary with `-s` and `-S` flags:
```
$ sudo qemu-system-arm -machine mps2-an385 -monitor null -semihosting \
        --semihosting-config enable=on,target=native \
        -kernel ./build/RTOSDemo.axf \
        -serial stdio -nographic -s -S
```
The options: <br>
`-s` allows gdb to be attached to the process remotely at port 1234<br>
`-S` starts the program in the paused state.<br>

3. Open another terminal to run GDB and connect to the process:
```
$ arm-none-eabi-gdb -q ./build/RTOSDemo.axf
(gdb) target remote :1234
(gdb) break main
(gdb) c
```
