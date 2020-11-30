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

## How to build blinky demo
Navigate with the command line to FreeRTOS/Demo/CORTEX\_M3\_MPS2\_QEMU\_GCC
For a release build run:

```
$ export PATH=/path/to/arm/toolchain:$PATH
$ make
```
and for a versions with debugging symbols and no optimizations activated, run:
```
$ make DEBUG=1
```

### How to run for blinky demo
run:
```
$ sudo qemu-system-arm -machine mps2-an385 -monitor null -semihosting \
        --semihosting-config enable=on,target=native \
        -kernel ./build/RTOSDemo.axf \
        -serial stdio -nographic
```

## Networking Support
To make networking support possible a few steps needs to be done on the machine
lets assume the following interfaces using ubuntu 18.04 (the names on your machine could
        be different)
```
l0:         loopback in terface
enp0s5:     ethernet interface
virbr0:     virtual bridge         (to be created)
virbr0-nic: veth virtual interface (to be created)
```

### How to build echo client demo
For a normal build (no debugging)
```
$ make NETWORKING=1
```
For a debug build which gives access to the symbols and gdb access run:
```
$ make DEBUG=1 NETWORKING=1
```
### How to run echo client demo

#### On the server machine (where the echo server will be running)
On a different machine run the following command
```
$ sudo nc -l 7
```
This will start an server at port 7
No output is expected, just the console cursor disappears
take note of the ip address of that machine
#### On the client machine (where the demo will be running)
```
$ sudo qemu-system-arm -machine mps2-an385 -cpu cortex-m3 
          -kernel ./build/RTOSDemo.axf \
          -netdev tap,id=mynet0,ifname=virbr0-nic,script=no \
          -net nic,macaddr=52:54:00:12:34:AD,model=lan9118,netdev=mynet0 \
          -object filter-dump,id=tap_dump,netdev=mynet0,file=/tmp/qemu_tap_dump\
          -display gtk -m 16M  -nographic -serial stdio \
          -monitor null -semihosting -semihosting-config enable=on,target=native 
```
take hold of the mac address in the command and change it appropriately
(52:54:00:12:34:AD)

## How to start debugging (gdb)
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
## Demo
This Demo implements the blinky demo, the user should expect the word 
"blinking" to be repeatedly printed on the screen.
