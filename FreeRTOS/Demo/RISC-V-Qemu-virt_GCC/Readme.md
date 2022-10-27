There is an updated version of this original submission from Katsuhiro Suzuki
in the FreeRTOS/Demo/RISC-V_RV32_QEMU_VIRT_GCC directory.

# Emulating generic RISC-V 32bit machine on QEMU

## Requirements

1. GNU RISC-V toolchains (tested on Crosstool-NG)
1. qemu-riscv32-system (tested on Debian 10 package)
1. Linux OS (tested on Debian 10)

### Host OS Tips
* Crosstools-ng requires a case-sensitive file system if used on a Mac.
* For officially supported OSes, check https://crosstool-ng.github.io/docs/os-setup/

## How to build toolchain

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
$ qemu-system-riscv32 -nographic -machine virt -net none \
  -chardev stdio,id=con,mux=on -serial chardev:con \
  -mon chardev=con,mode=readline -bios none \
  -smp 4 -kernel ./build/RTOSDemo.axf
```


## How to debug with gdb

Append -s and -S options to the previous qemu command.

- -s: enable to attach gdb to QEMU at port 1234
- -S: start and halted CPU (wait for attach from gdb)

This is just recommend to use 'debug build' for more efficient debugging.
Run these commands after starting the QEMU with above options:

```
$ riscv64-unknown-elf-gdb build/RTOSDemo.axf

(gdb) target remote localhost:1234
(gdb) break main
Breakpoint 1 at 0x80000110

(gdb) c
Continuing.

Breakpoint 1, 0x80000110 in main ()
```


## Description

This demo just prints Tx/Rx message of queue to serial port, use no
other hardware and use only primary core (currently hart 0).
Other cores are simply going to wfi state and execute nothing else.

## Troubleshooting
### Builds
#### ZICSR Failures
If you receive the following while building
```
main.c: Assembler messages:
main.c:70: Error: unrecognized opcode `csrc mstatus,8', extension `zicsr' required
```
You'll need to swap the `-march` flag from `-march=rv32ima` to `-march=rv32ima_zicsr`

#### -pie not supported
If you receive this error while linking, add the `-no-pie` flag to your linker flags.
See https://man.archlinux.org/man/community/riscv64-elf-binutils/riscv64-elf-ld.1.en#no~24 for more.
