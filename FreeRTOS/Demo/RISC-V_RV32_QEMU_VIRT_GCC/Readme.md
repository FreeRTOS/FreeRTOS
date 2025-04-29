# Emulating generic RISC-V 32bit machine on QEMU

## Requirements

1. GNU RISC-V toolchains Tested on:
  * Pre-built Sifive GNU Embedded Toolchain — v3.0.4 - https://www.sifive.com/software
  * Self built from https://github.com/riscv-collab/riscv-gnu-toolchain/tree/a33dac0251d17a7b74d99bd8fd401bfce87d2aed (tag: 2025.01.20)

1. qemu-riscv64-system. Tested on:
  * pre-built Sifive QEMU — v3.0.4 - https://www.sifive.com/software
  * qemu-system-riscv64 v 8.2.2
1. Linux OS. Tested on:
  * Ubuntu 24.04 LTS


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

For any of the previous configurations, if you want to use the port on a RVA23 system instead of a RV32, you may append append `RVA23=1`

```
$ make -C build/gcc/ RVA23=1
```

If the build was successful, the RTOSDemo.elf executable will be located in the build/gcc/output directory.


## How to run

For the RV32 build:

```
$ qemu-system-riscv32 -nographic -machine virt -net none -chardev stdio,id=con,mux=on \
    -serial chardev:con -mon chardev=con,mode=readline -bios none -smp 4 \
    -s --kernel build/gcc/output/RTOSDemo.elf
```

For the RVA23 build:

```
$ qemu-system-riscv64 -nographic -machine virt -net none -chardev stdio,id=con,mux=on \
    -serial chardev:con -mon chardev=con,mode=readline -bios none -smp 4 \
    -cpu rv64,zba=true,zbb=true,v=true,vlen=256,vext_spec=v1.0,rvv_ta_all_1s=true,rvv_ma_all_1s=true -s --kernel build/gcc/output/RTOSDemo.elf
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
