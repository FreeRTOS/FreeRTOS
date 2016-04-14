Copyright (c) 2015, Atmel Corporation All rights reserved.
----------------------------------------------------------

* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*
* - Redistributions of source code must retain the above copyright notice,
* this list of conditions and the disclaimer below.
*
* Atmel's name may not be used to endorse or promote products derived from
* this software without specific prior written permission.
*
* DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


# Atmel SAMA5D2x Software Package

## Overview

This softpack comes as an early delivery and all presented APIs are subject to change.

Each software module is provided with full source code, example of usage, and ready-to-use projects.

### Supported Platforms

Windows and Linux with the gnu GCC ARM Embedded toolchain. It is downloadable at this address: https://launchpad.net/gcc-arm-embedded (Mac OS X should also work but as not been tested yet).
Dependencies:
- GNU make (from MinGW, Cygwin or GnuWin32 for Windows architectures)
- bash (from MinGW, Cygwin for Windows architectures)

Windows with IAR Embedded Workbench.
Dependencies:
- IAR Embedded Workbench (Tested on version 7.40)
- bash (from MinGW, Cygwin or GnuWin32) for IAR project generation
- GNU make (from MinGW, Cygwin or GnuWin32) for IAR project generation
- mktemp (from MinGW, Cygwin or GnuWin32) for IAR project generation

Notice: This softpack comes as an early delivery and all presented APIs are subject to change.

## Contents 

### Directory Architecture

- target/sama5d2
  All chip and board specific source files

- target/sama5d2/toolchain/
  Linker and debugger scripts

- scripts/
  generators and build script templates (Makefiles)

- drivers/
  Driver source files

- examples/
  All examples 

### Examples

This release contains the following examples:

adc: Example using ADC

can: Example using CAN

crypto_aes: AES hardware computation (with and without DMA)

crypto_sha: SHA hardware computation (with and without DMA)

crypto_tdes: Triple-DES hardware computation (with and without DMA)

fifo: Test Flexcom USART FIFO

gettting-started: LED blink (uses PIT and PIO)

gmac: GMAC example using a simple IP stack

gmac_lwip: GMAC example using LWIP stack

gmac_uip_helloworld: GMAC example using UIP stack (UIP helloworld example)

gmac_uip_telnetd: GMAC example using UIP stack (UIP telnetd example)

gmac_uip_webserver: GMAC example using UIP stack (UIP webserver example)

isc: Example using ISC controller (OV7740 sensor)

lcd: Example using LCD controller

qspi_flash: Read/Write/Delete commands to a QSPI serial flash

rtc: RTC Example

spi_serialflash: Read/Write/Delete commands to an SPI serial flash

trng: Example using hardware RNG (interrupt mode)

twi_eeprom: Read/Write/Delete commands to an Two-Wire EEPROM

wdt: Example using watchdog timer

xdma: Memory-to-memory DMA transfert example

xdma_usart: Bidirectionnal Usart-memory DMA transfert example

## Usage (GCC ARM Embedded)

### Environment Variable

TARGET: Name of the wanted target (sama5d2-xplained for samad52 XPLAINED ULTRA boards). This variable is mandatory to launch any build.

DEBUG: Build with debug flags (default).

TRACE_LEVEL: The wanted log level, 5 correspond to full, 0 to none (default to 5)

RELEASE: Build with the release flags

only TARGET must be provided or set at each make invocation.

### Build

Run:

make
#or
make TARGET=wanted_target # if TARGET is not set

### Run and Debug (with GDB)

To run examples with gdb, first, JLinkGDBServer must be started. It can be downloaded for each platform at http://www.segger.com

A make target is provided to launch the test with the correct gdb command arguments, run:

make debug
#or
make TARGET=wanted_target debug # if TARGET is not set

## Usage (IAR)

The Win version of this softpack release comes with pregenerated IAR projects compatible with IAR Systems Embedded Workbench for ARM version 7.40.

The C-SPY device description files and device selections files are not included and must be installed manually.

### IAR Project generation

An IAR project can be generated with GNU make, run in the example directory:

make iar
#or
make TARGET=wanted_target iar # if TARGET is not set

All needed IAR project files will be put in the example directory, including a default workspace one.

Notice:
GNU make may fail on Windows platforms if the Makefile contains UNIX line endings.
You can use unix2dos on all Makefile files in scripts/ directory to fix this issue.
