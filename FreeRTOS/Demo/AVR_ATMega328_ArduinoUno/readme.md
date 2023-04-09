
# Overview

This directory contains a make demo project (avr-gcc compiler) for AVR Arduino Uno board equipped with AVR ATMEGA328 microcontroller (32 KB Flash, 2 KB SRAM, 512 bytes EEPROM).  
There are additional targets in makefile that allow to use qemu-system-avr for debugging and simulations.

# Quick start

 - make - for compile
 - make simulator - for starting qemu with compiled project. Use TCP port 5678 for forwarding virtual UART
 - make gdbserver - start qemu with gdb server. Prepared script for visual code allows to attach to gdbserver
