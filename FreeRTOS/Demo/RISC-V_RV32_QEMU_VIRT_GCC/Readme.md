# Emulating generic RISC-V 32bit machine on QEMU

## Requirements

1. GNU RISC-V toolchains (tested on pre-built Sifive GNU Embedded Toolchain — v2020.12.8)
  - https://www.sifive.com/software
1. qemu-riscv32-system  (tested on pre-built Sifive QEMU — v2020.08.1)
  - https://www.sifive.com/software
1. Linux OS (tested on Ubuntu 20.04.3 LTS)


## How to build

Add path of toolchain that is described above section, such as:

```
$ export PATH="/YOUR_PATH/riscv64-unknown-elf/bin:${PATH}"
```

For release build:

```
$ make -C build/gcc/
```

For debug build:

```
$ make -C build/gcc/ DEBUG=1
```

To clean build artifacts:

```
$ make -C build/gcc/ clean
```

If the build was successful, the RTOSDemo.elf executable will be located in the build/gcc/output directory.


## How to run

```
$ qemu-system-riscv32 -nographic -machine virt -net none \
  -chardev stdio,id=con,mux=on -serial chardev:con \
  -mon chardev=con,mode=readline -bios none \
  -smp 4 -kernel ./build/gcc/output/RTOSDemo.elf
```


## How to debug with gdb

Append -s and -S options to the previous qemu command.

- -s: enable to attach gdb to QEMU at port 1234
- -S: start and halted CPU (wait for attach from gdb)

It is recommended to use the 'debug build' so that gdb can automatically map symbols.
Run these commands after starting the QEMU with above options:

```
$ riscv64-unknown-elf-gdb -x build/gcc/gdbinit
```


## Description

This demo just prints Tx/Rx message of queue to serial port, use no
other hardware and use only primary core (currently hart 0).
Other cores are simply going to wfi state and execute nothing else.
