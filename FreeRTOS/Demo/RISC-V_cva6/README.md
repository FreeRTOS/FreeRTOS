# cva6-freertos
# Getting started

To get more familiar with CVA6 architecture, a documentation is available:

https://cva6.readthedocs.io/en/latest/
https://github.com/openhwgroup/cva6 

# Prerequisites


## RISC-V tool chain setting up
The tool chain is available at: https://github.com/riscv/riscv-gnu-toolchain.
At first, you have to get the sources of the RISCV GNU toolchain:
$ git clone https://github.com/riscv/riscv-gnu-toolchain 
$ cd riscv-gnu-toolchain 
$ git checkout ed53ae7a71dfc6df1940c2255aea5bf542a9c422
$ git submodule update --init --recursive

Next, you have to install all standard packages needed to build the toolchain depending on your Linux distribution.
Before installing the tool chain, it is important to define the environment variable RISCV=”path where the tool chain will be installed”.
Then, you have to set up the compiler by running the following command:

$ export RISCV=/path/to/install/riscv/compilators
$ ./configure --prefix=$RISCV --disable-linux --with-cmodel=medany --with-arch=rv32ima
$ make newlib 
When the installation is achieved, do not forget to add $RISCV/bin to your PATH.

$ export PATH=$PATH:$RISCV/bin

**** My example: riscv32-unknown-elf-gdb installed ****
export RISCV=<path>/cva6/tools/riscv_gnu_toolchain/install_latest_rv32imaf/
export PATH=$PATH:$RISCV/bin
>> riscv32-unknown-elf-gdb --version                                                                                                                   
>> GNU gdb (GDB) 10.1                                                                                                                                                                                          
>> export RISCV_CCPATH=<path>/cva6/tools/riscv_gnu_toolchain/install_latest_rv32imaf/



 


## OpenOCD

To be able to run and debug software applications on CVA6, you need to install OpenOCD tool.
OpenOCD is a free and open-source software distributed under the GPL-2.0 license.
It provides on-chip programming and debugging support with a layered architecture of JTAG interface and TAP support.

Global documentation on OpenOCD is available at https://github.com/ThalesGroup/pulpino-compliant-debug/tree/pulpino-dbg/doc/riscv-debug-notes/pdfs

These documents aim at providing help about OpenOCD and RISC-V debug.

Before setting up OpenOCD, other tools are needed:
- make
- libtool
- pkg-congfig > 0.23
- autoconf > 2.64
- automake > 1.14
- texinfo

On Ubuntu, ensure that everything is installed with:
$ sudo apt install make libtool pkg-config autoconf automake texinfo

Furthermore, you need to set up libusb and libftdi libraries.
On Ubuntu:
$ sudo apt install libusb-1.0-0-dev libftdi1-dev

Once all dependencies are installed, OpenOCD can be set up.
- Download sources:
$ git clone https://github.com/riscv/riscv-openocd
$ cd riscv-openocd
$ git checkout aec5cca15b41d778fb85e95b38a9a552438fec6a
- Prepare a **build** directory:
$ mkdir build
- Launch the bootstrap script:
$ ./bootstrap
- Launch configure:
$ ./configure --enable-ftdi --prefix=build --exec-prefix=build
- Compile and install files:
$ make
$ make install
When the installation is achieved, do not forget to add riscv-openocd/build/bin to your PATH.
$ export PATH=$PATH:<path to riscv-openocd>/build/bin

**** My example: openocd installed ****
>> export PATH=$PATH:<path>/cva6/tools/openocd/riscv-openocd/build/bin
>> openocd --version
>> Open On-Chip Debugger 0.10.0+dev-00832-gaec5cca15 (2021-11-28-16:47)

# FreeRTOS

## FPGA emulation

A FPGA platform emulating **CV32A6** (CVA6 in 32b flavor) has been implemented on **Genesys-2** board.
This platform includes a CV32A6 processor, a JTAG interface to run and debug software applications and a UART interface to display strings on hyperterminal.
Refer: https://github.com/openhwgroup/cva6

The steps to run the FreeRTOS on CV32A6 FPGA platform are described below.

## Compile FreeRTOS

git clone --recursive https://github.com/FreeRTOS/FreeRTOS.git
cd FreeRTOS/FreeRTOS/Demo/RISC-V_cva6
make

## Get started with FreeRTOS application on Genesys-2

When the mcs is loaded, the orange LED `done` lights up.
1. Then, in a terminal, launch **OpenOCD**:
```
$ openocd -f corev_apu/fpga/ariane.cfg
```
If it is succesful, you should see something like:
```
Open On-Chip Debugger 0.10.0+dev-00832-gaec5cca (2019-12-10-14:21)
Licensed under GNU GPL v2
For bug reports, read
    http://openocd.org/doc/doxygen/bugs.html
Info : auto-selecting first available session transport "jtag". To override use 'transport select <transport>'.
Info : clock speed 1000 kHz
Info : JTAG tap: riscv.cpu tap/device found: 0x249511c3 (mfg: 0x0e1 (Wintec Industries), part: 0x4951, ver: 0x2)
Info : datacount=2 progbufsize=8
Info : Examined RISC-V core; found 1 harts
Info :  hart 0: XLEN=32, misa=0x40141105
Info : Listening on port 3333 for gdb connections
Ready for Remote Connections
Info : Listening on port 6666 for tcl connections
Info : Listening on port 4444 for telnet connections

```
2. In a separate terminal, launch **gdb**:
```
$ riscv32-unknown-elf-gdb <path>/FreeRTOS/FreeRTOS/Demo/RISC-V_cva6/build/RTOSDemo.elf   
```
You must use gdb from the RISC-V toolchain. If it is successful, you should see:
```
GNU gdb (GDB) 9.1
Copyright (C) 2020 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
Type "show copying" and "show warranty" for details.
This GDB was configured as "--host=x86_64-pc-linux-gnu --target=riscv32-unknown-elf".
Type "show configuration" for configuration details.
For bug reporting instructions, please see:
<http://www.gnu.org/software/gdb/bugs/>.
Find the GDB manual and other documentation resources online at:
    <http://www.gnu.org/software/gdb/documentation/>.

For help, type "help".
Type "apropos word" to search for commands related to "word"...
Reading symbols from riscv-spike.elf...
(gdb) 
```
3. In gdb, you need to connect gdb to openocd:
```
(gdb) target remote :3333
```
if it is successful, you should see the gdb connection in openocd:
```
Info : accepting 'gdb' connection on tcp/3333
```
4. In gdb, load **FreeRTOSDemo.elf** to CV32A6 FPGA platform:
```
(gdb) load
Loading section .vectors, size 0x80 lma 0x80000000
Loading section .init, size 0x60 lma 0x80000080
Loading section .text, size 0x16044 lma 0x800000e0
Loading section .rodata, size 0x122a4 lma 0x80016130
Loading section .eh_frame, size 0x50 lma 0x800283d4
Loading section .init_array, size 0x4 lma 0x80028424
Loading section .data, size 0xc1c lma 0x80028428
Loading section .sdata, size 0x2c lma 0x80029048
Start address 0x80000080, load size 168036
Transfer rate: 61 KB/sec, 9884 bytes/write.
```

5. At last, in gdb, you can run the riscv-spike application by command `c`:
```
(gdb) c
Continuing.
(gdb) 
```

6. On hyperterminal configured on /dev/ttyUSB0 115200-8-N-1, you should see:
```
Hello CVA6
FreeRTOS Demo Start
FreeRTOS Demo SUCCESS
FreeRTOS Demo SUCCESS
FreeRTOS Demo SUCCESS
```
This result is obtained just after the FPGA bitstream loading.








