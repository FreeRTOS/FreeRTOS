# Emulating generic RISC-V 32bit machine on spike

## Requirements

1. GNU RISC-V toolchains (tested on Crosstool-NG)
2. spike from https://github.com/riscv/riscv-isa-sim
3. OpenOCD from https://github.com/riscv/riscv-openocd

## How to build toolchain

Clone the Crosstool-NG and build.

```
$ git clone https://github.com/crosstool-ng/crosstool-ng
$ cd crosstool-ng
$ ./bootstrap
$ ./configure --enable-local
$ make

$ ./ct-ng menuconfig
```

Change the following configs:

```
CT_EXPERIMENTAL=y
CT_ARCH_RISCV=y
CT_ARCH_64=y
CT_ARCH_ARCH=rv32ima
CT_ARCH_ABI=ilp32
CT_MULTILIB=y
CT_DEBUG_GDB=y
```

Build the GNU toolchain for RISC-V.

```
$ ./ct-ng build
```

A toolchain is installed at ~/x-tools/riscv64-unknown-elf directory.


## How to build

Add path of toolchain that is described above section.

```
$ export PATH=~/x-tools/riscv64-unknown-elf/bin:$PATH
```

For release build:

```
$ make
```

For debug build:

```
$ make DEBUG=1
```

If success to build, executable file RTOSDemo.axf in ./build directory.


## How to run

```
$ spike -p1 --isa RV32IMAFDCV -m0x80000000:0x10000000 --rbb-port 9824 \
        ./build/RTOSDemo.axf
```


## How to debug with gdb

Start OpenOCD in one terminal:
```
$ openocd -f spike-1.cfg
```

Start gdb in another:
```
$ riscv64-unknown-elf-gdb ./build/RTOSDemo.axf
...
(gdb) target extended-remote localhost:3333
...
(gdb) info threads
```

(As of 3/18/2021 OpenOCD's RISC-V FreeRTOS awareness is still incomplete.)

## Description

This demo starts separate transmit and receive threads. The transmit thread sends integers through a queue. Both threads print out what they're sending/receiving using HTIF.