# Emulating generic RISC-V 32bit machine on QEMU
There is an updated version of this original submission from Katsuhiro Suzuki
in the FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC directory.

## Demo Summary
This demo prints Tx/Rx message of queue to serial port, using no
other hardware and usinh only the primary core (currently hart 0).
Other cores are simply going to wfi state and execute nothing else.

## Requirements

1. GNU RISC-V toolchains (tested on [SiFive](https://www.sifive.com/software) + [Crosstool-NG](https://github.com/crosstool-ng/crosstool-ng) toolchains)
1. qemu-riscv32-system (tested on Debian 10 package)
1. Linux OS (tested on Debian 10/Ubuntu)


## Prerequisites
### QEMU installation
This is OS specific. For Debian, some general instructions can be found [here](https://wiki.debian.org/RISC-V/32).

### RISC-V Toolchain Setup
You can download a RISC-V toolchain from SiFive at [this url](https://www.sifive.com/software). You'll need to extract this somewhere you'll remember as you need to add it to your PATH.

You can add the toolchain to you path with the following command
```
export PATH=<your-toolchain-path>/<your-toolchain>/bin:$PATH
```

For example, if you install the SiFive v2020.12.8 toolchain on an Ubuntu machine in your user home directory, it would be something like
```
export PATH=~/riscv64-unknown-elf-toolchain-10.2.0-2020.12.8-x86_64-linux-ubuntu14/bin:$PATH
```

___________

## Building and Running the Demo
The demo is built using a makefile, so the command to build the demo is simply...
```
make
```
This file can become important if you want to change your RISC-V microarchitecture or Application Binary Interface (ABI).

To run the demo in Qemu...
```
qemu-system-riscv32 -nographic -machine virt -net none \
  -chardev stdio,id=con,mux=on -serial chardev:con \
  -mon chardev=con,mode=readline -bios none \
  -smp 4 -kernel ./build/RTOSDemo.axf
```

This command is quite lengthy but essentially spins up an emulated 32-bit RISC-V procressor without any display running the demo you just built as the kernel on 4 simulated cores. Textual output of this simulation will be directed to standard I/O.

## Building and Debugging the Demo
The debuggable demo is also built using a makefile, so the command to build the demo is simply...
```
make DEBUG=1
```
Notice the addition of the `DEBUG=1` parameter. This is what tells the makefile to include debugging information when building the demo.

To run the demo in Qemu...
```
qemu-system-riscv32 -nographic -machine virt -net none \
  -chardev stdio,id=con,mux=on -serial chardev:con \
  -mon chardev=con,mode=readline -bios none \
  -smp 4 -kernel ./build/RTOSDemo.axf \
  -s -S 
```
This command is nearly identical to the one above with the exception of the `-s` and `-S` flags. The `-s` flag attaches Qemu to port 1234 for GDB to connect to. The `-S` flag starts the simulation halted and waits for GDB to connect.

At this point you'll need to attach GDB before the demo runs. To do so you'll need to run a RISC-V compatible GDB. This should be provided in the toolchain you've downloaded. The command to start GDB will be...

```
riscv64-unknown-elf-gdb build/RTOSDemo.axf
```
Note - You'll need to run this command from the same directory as this readme.

From here, there are three GDB commands you'll want to run

```
target remote localhost:1234

break main

continue
```

The first attaches GDB to the port Qemu is running against. The second sets a breakpoint at the main function. The third runs the program until the breakpoint. You can run `continue` or `c` again to continue the program after the breakpoint.

## Building Your Own Toolchain
This section should be viewed as experimental. Take these steps as more of a starting off point than a dead set way to build a toolchain for your demo.

### CrossTools-NG

Clone the Crosstool-NG and build.

```
$ git clone https://github.com/crosstool-ng/crosstool-ng
$ ./bootstrap
$ ./configure --enable-local
$ make

$ ./ct-ng menuconfig
```

The following configuration values need to be set:

```
CT_EXPERIMENTAL=y
CT_ARCH_RISCV=y
CT_ARCH_64=y
CT_ARCH_ARCH=rv32ima
CT_ARCH_ABI=ilp32
CT_MULTILIB=y
CT_DEBUG=y
```

These configurations can be found through the menuconfig though they are not immediately obvious. You will need to read the help page for each option to see what `CT_XXX` flag it corresponds to. For the flags above, the settings to edit are...
* CT_EXPIREMENTAL
  * Paths and misc options -> Try features marked as EXPERIMENTAL
* CT_ARCH_RISCV
  * Target options -> Target Architecture
* CT_ARCH_64
  * Target options -> Bitness
* CT_ARCH_ARCH
  * Target options -> Architecture level -> Enter "rv32ima"
* CT_ARCH_ABI
  * Target options -> Generate code for the specific ABI -> Enter "ilp32"
* CT_MULTILIB
  * Target options -> Build a multilib toolchain
* CT_DEBUG
  * Debug facilities -> gdb


Build the GNU toolchain for RISC-V.

```
$ ./ct-ng build
```

A toolchain is installed at ~/x-tools/riscv64-unknown-elf directory. You can now follow the 'Building and Running/Debugging" steps above

## Troubleshooting
### Your own toolchain Builds
### ZICSR Failures
If you receive the following while building
```
main.c: Assembler messages:
main.c:70: Error: unrecognized opcode `csrc mstatus,8', extension `zicsr' required
```
You'll need to swap the `-march` flag from `-march=rv32ima` to `-march=rv32ima_zicsr`

### -pie not supported
If you receive this error while linking, add the `-no-pie` flag to your linker flags.
See https://man.archlinux.org/man/community/riscv64-elf-binutils/riscv64-elf-ld.1.en#no~24 for more.
