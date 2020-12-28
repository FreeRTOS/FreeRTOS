/*******************************************************************************
 * Project           		 : shakti devt board
 * Name of the file              : start.S 
 * Brief description             : first instruction to execute in an application
 * Name of Author                : Abhinav Ramnath & Sathya Narayanan N
 * Email id                      : abhinavramnath13@gmail.com & sathya281@gmail.com

 Copyright (C) 2019  IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.

********************************************************************************/
/**
@file start.S
@detail first instruction to execute in an application is here. 
 Registers are initialized, trap entry is setup here.
*/

#include "defines.h"

.section ".text.init"
.globl _start

_start:

li  x1, 0
li  x2, 0
li  x3, 0
li  x4, 0
li  x5, 0
li  x6, 0
li  x7, 0
li  x8, 0
li  x9, 0
li  x10,0
li  x11,0
li  x12,0
li  x13,0
li  x14,0
li  x15,0
li  x16,0
li  x17,0
li  x18,0
li  x19,0
li  x20,0
li  x21,0
li  x22,0
li  x23,0
li  x24,0
li  x25,0
li  x26,0
li  x27,0
li  x28,0
li  x29,0
li  x30,0
li  x31,0

# initialize global pointer
.option push
.option norelax
la gp, __global_pointer$
.option pop

init_bss:
    /* init bss section */
    la	a0, __bss_start
    la	a1, __bss_end-4 /* section end is actually the start of the next section */
    li	a2, 0x0
  1:
    sw		a2, 0(a0)
    bgeu	a0, a1, init_sbss
    addi	a0, a0, 4
    j	        1b

init_sbss:
    /* init bss section */
    la	a0, __sbss_start
    la	a1, __sbss_end-4 /* section end is actually the start of the next section */
    li	a2, 0x0
   1:
    sw		a2, 0(a0)
    bgeu	a0, a1, 1f
    addi	a0, a0, 4
    j	        1b

1:
# initialize stack pointer
.option push
.option norelax
la sp, __stack_pointer$
.option pop

la  tp, _end + 63
and tp, tp, -64

j init

1:
  j 1b

.section ".tdata.begin"
.globl _tdata_begin
_tdata_begin:

.section ".tdata.end"
.globl _tdata_end
_tdata_end:

.section ".tbss.end"
.globl _tbss_end
_tbss_end:
