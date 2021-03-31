# Preliminary Port (GCC) of Raspberry Pi Pico for FreeRTOS
This is the preliminary port of the Raspberry Pi Pico FreeRTOS with GCC
toolchain. The demo is able to blink the onboard LED. Most of the code is
based on the Pi Pico SDK codebase.

## Limitations
 - This port uses only Core 0 (Core 1 is always idle).
 - Most of the peripherals aren't readily usable as the module specific
   libraries haven't been ported yet.

## Requirements
Both host and target binaries are necessary for the demo to work correctly.

1. GNU ARM embedded toolchain (tested on arm-none-eabi-gcc (15:9-2019-q4-0ubuntu1) 9.2.1 20191025 (release) [ARM/arm-9-branch revision 277599])
2. GNU Make
3. Python 3
4. g++ for x86_64 (Needs to support C++ 14 standard).
5. Linux OS (tested on Ubuntu 20.04.2 LTS).
6. gdb-multiarch (if debugging).


## Blinky Demo
### How to build the demo
Make sure that the GNU ARM embedded toolchain is on the path. Navigate to
FreeRTOS/Demo/CORTEX_M0+_RaspberryPiPico_GCC directory.
```
$ make
```
You should see: ```build/blinky.uf2```. This is the file that you need to drop into the FAT16 partition that appears when the Pico device is booted
into the USB device mode.

### Booting the Pi Pico into USB device mode
Press the BOOTSEL switch and plug in the Pi Pico to a USB cable attached to
the host computer. Now release the BOOTSEL switch.
You should see a mass storage device and its FAT16 partiton should be 
automounted on the host computer.

### Flash the Pi Pico
Drag and drop the ```build/blinky.uf2``` file into the mounted partition.

-or-

copy it to the mounted partition (assuming it is mounted under /media/developer/RPI-RP2/):
```
cp build/blinky.uf2 /media/developer/RPI-RP2/
```

The Pi Pico will write into the flash with the relevant bits and reboot.

At this point you should see the onboard LED blinking.


If you are not interested in debugging your applications you can skip
the following sections

## Cleanup
Run
```
make clean
```
to remove the build artifacts.


## Building a debug version
You can build a debug version with:
```
$ make DEBUG=1
```

## Preapare the Picoprobe
Read Appendix A of Getting started with Rasperry Pi Pico [document](https://datasheets.raspberrypi.org/pico/getting-started-with-pico.pdf) to prepare
the debug setup with two Pi Pico boards.

## Start openocd

```
$ src/openocd -f interface/picoprobe.cfg -f target/rp2040.cfg -s tcl
Open On-Chip Debugger 0.10.0+dev-geb22ace-dirty (2021-02-27-21:46)
Licensed under GNU GPL v2
For bug reports, read
        http://openocd.org/doc/doxygen/bugs.html
Info : only one transport option; autoselect 'swd'
Warn : Transport "swd" was already selected
adapter speed: 5000 kHz

Info : Hardware thread awareness created
Info : Hardware thread awareness created
Info : RP2040 Flash Bank Command
Info : Listening on port 6666 for tcl connections
Info : Listening on port 4444 for telnet connections
Info : clock speed 5000 kHz
Info : SWD DPIDR 0x0bc12477
Info : SWD DLPIDR 0x00000001
Info : SWD DPIDR 0x0bc12477
Info : SWD DLPIDR 0x10000001
Info : rp2040.core0: hardware has 4 breakpoints, 2 watchpoints
Info : rp2040.core1: hardware has 4 breakpoints, 2 watchpoints
Info : starting gdb server for rp2040.core0 on 3333
Info : Listening on port 3333 for gdb connections
```

## Start gdb
```
$ gdb-multiarch
```

You should see the gdb prompt.

## Connect to the gdb server
```
(gdb) target remote localhost:3333
Remote debugging using localhost:3333
warning: No executable has been specified and target does not support
determining executable automatically.  Try using the "file" command.
0x1000057e in ?? ()
(gdb) 
```

## Load debug symbols
```
(gdb) file build/blinky.elf
A program is being debugged already.
Are you sure you want to change the file? (y or n) y
Reading symbols from build/blinky.elf...
(gdb) 
```

## Flash the binary into target
```
(gdb) load build/blinky.elf
Loading section .boot2, size 0x100 lma 0x10000000
Loading section .text, size 0x61d8 lma 0x10000100
Loading section .rodata, size 0x460 lma 0x100062d8
Loading section .ARM.exidx, size 0x8 lma 0x10006738
Loading section .data, size 0xed4 lma 0x10006740
Start address 0x100001e8, load size 30228
Transfer rate: 8 KB/sec, 5038 bytes/write.
(gdb) 
```

## Run the binary in the target
```
(gdb) continue
Continuing.
```
You should see the LED blinking

## Stop the target and see the stack trace
Press Ctrl+C in the GDB window and you should see the target halt. Type
```bt``` in the gdb prompt to see the stack trace.

```
^Ctarget halted due to debug-request, current mode: Thread 
xPSR: 0x01000000 pc: 0x00000178 msp: 0x20041f00

Thread 1 received signal SIGINT, Interrupt.
vPortSuppressTicksAndSleep (xExpectedIdleTime=134) at /home/romit/codepush/FreeRTOS/FreeRTOS/Source/portable/GCC/ARM_CM0/port.c:485
485                 __asm volatile ( "cpsie i" ::: "memory" );
(gdb) bt
#0  vPortSuppressTicksAndSleep (xExpectedIdleTime=134) at /home/romit/codepush/FreeRTOS/FreeRTOS/Source/portable/GCC/ARM_CM0/port.c:485
#1  0x10000ff6 in prvIdleTask (pvParameters=<optimized out>) at /home/romit/codepush/FreeRTOS/FreeRTOS/Source/tasks.c:3520
#2  0x10000330 in frame_dummy ()
#3  0xa5a5a5a4 in ?? ()
Backtrace stopped: previous frame identical to this frame (corrupt stack?)
(gdb) 
```

Once you are done debugging you can type ```c``` on the gdb prompt to let
the target continue.
