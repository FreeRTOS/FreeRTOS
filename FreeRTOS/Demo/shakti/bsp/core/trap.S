/*************************************************************************
 * Name of the file              : trap.S 
 * Brief description             : header file for handling traps 
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

****************************************************************************/
#include "defines.h"

  .global trap_entry
  .align 2

  trap_entry:

  /*
     If trap comes, do
     1. push all x* register values to stack
     2. handle trap
     3. restore x* register values from stack
   */

  addi sp, sp, -32*REGSIZE
  .p2align 3
  SREG x1, 1*REGSIZE(sp)
  SREG x2, 2*REGSIZE(sp)
  SREG x3, 3*REGSIZE(sp)
  SREG x4, 4*REGSIZE(sp)
  SREG x5, 5*REGSIZE(sp)
  SREG x6, 6*REGSIZE(sp)
  SREG x7, 7*REGSIZE(sp)
  SREG x8, 8*REGSIZE(sp)
  SREG x9, 9*REGSIZE(sp)
  SREG x10, 10*REGSIZE(sp)
  SREG x11, 11*REGSIZE(sp)
  SREG x12, 12*REGSIZE(sp)
  SREG x13, 13*REGSIZE(sp)
  SREG x14, 14*REGSIZE(sp)
  SREG x15, 15*REGSIZE(sp)
  SREG x16, 16*REGSIZE(sp)
  SREG x17, 17*REGSIZE(sp)
  SREG x18, 18*REGSIZE(sp)
  SREG x19, 19*REGSIZE(sp)
  SREG x20, 20*REGSIZE(sp)
  SREG x21, 21*REGSIZE(sp)
  SREG x22, 22*REGSIZE(sp)
  SREG x23, 23*REGSIZE(sp)
  SREG x24, 24*REGSIZE(sp)
  SREG x25, 25*REGSIZE(sp)
  SREG x26, 26*REGSIZE(sp)
  SREG x27, 27*REGSIZE(sp)
  SREG x28, 28*REGSIZE(sp)
  SREG x29, 29*REGSIZE(sp)
  SREG x30, 30*REGSIZE(sp)
  SREG x31, 31*REGSIZE(sp)

  csrr a0, mcause
  csrr a1, mepc
  mv a2, sp
  jal handle_trap
  csrw mepc, a0

  LREG x1, 1*REGSIZE(sp)
  LREG x2, 2*REGSIZE(sp)
  LREG x3, 3*REGSIZE(sp)
  LREG x4, 4*REGSIZE(sp)
  LREG x5, 5*REGSIZE(sp)
  LREG x6, 6*REGSIZE(sp)
  LREG x7, 7*REGSIZE(sp)
  LREG x8, 8*REGSIZE(sp)
  LREG x9, 9*REGSIZE(sp)
  LREG x10, 10*REGSIZE(sp)
  LREG x11, 11*REGSIZE(sp)
  LREG x12, 12*REGSIZE(sp)
  LREG x13, 13*REGSIZE(sp)
  LREG x14, 14*REGSIZE(sp)
  LREG x15, 15*REGSIZE(sp)
  LREG x16, 16*REGSIZE(sp)
  LREG x17, 17*REGSIZE(sp)
  LREG x18, 18*REGSIZE(sp)
  LREG x19, 19*REGSIZE(sp)
  LREG x20, 20*REGSIZE(sp)
  LREG x21, 21*REGSIZE(sp)
  LREG x22, 22*REGSIZE(sp)
  LREG x23, 23*REGSIZE(sp)
  LREG x24, 24*REGSIZE(sp)
  LREG x25, 25*REGSIZE(sp)
  LREG x26, 26*REGSIZE(sp)
  LREG x27, 27*REGSIZE(sp)
  LREG x28, 28*REGSIZE(sp)
  LREG x29, 29*REGSIZE(sp)
  LREG x30, 30*REGSIZE(sp)
  LREG x31, 31*REGSIZE(sp)

  addi sp, sp, 32*REGSIZE
  mret

