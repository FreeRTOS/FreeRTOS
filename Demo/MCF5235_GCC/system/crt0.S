/*
    FreeRTOS MCF5235 port - Copyright (C) 2006 Christian Walter.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
    See http://www.FreeRTOS.org for documentation, latest information, license
    and contact details.  Please ensure to read the configuration and relevant
    port sections of the online documentation.

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
    ***************************************************************************
*/

  .title "crt0.S"

  .extern main
  .extern __stack
  .extern __bss_start
  .extern __text_start
  .extern init_main

  .equ    MCF5XXX_RAMBAR_SPV,   0x00000200
  .equ    MCF5XXX_RAMBAR_V,     0x00000001
  .global start

  .align  4
debug:
  .word   0x2C80    /* write to CSR */
  .word   0x0010
  .word   0x0400
  .word   0x0000

start:
  /* disable all interrupts on startup. */
  move.w  #0x2700, sr

  /* prepare internal SRAM. */
  move.l  #__SRAM, d0
  ori.l   #( MCF5XXX_RAMBAR_SPV | MCF5XXX_RAMBAR_V ), d0
  movec   d0, rambar

  /* prepare stack and frame pointer. */
  move.l  #__stack, sp
  link    a6, #-8

  /* initialize hardware. */
  jsr     init_main

  /* zero out the bss section. */
  move.l  #__bss_start, d1
  move.l  #_end, d0
  cmp.l   d0, d1
  jbeq    3f
  move.l  d1, a0
  sub.l   d1, d0
  subq.l  #1, d0
2:
  clr.b   (a0)+
  subq.l  #1, d0
  jbpl    2b
3:

  /* Relocate the data section. */
  move.l  #__data_load_start, %a0         /* .data in ROM */
  move.l  #copy_start, %a1                /* .data in RAM */

  /* Test if the two sections overlap. This is the case when we are working
   * with the debugger and the debugger loads the .data section.
   */
  cmpa.l  %a0, %a1
  beq     2f
1:
  /* Have we already copied everything. */
  cmpa.l  #__data_load_end, %a0
  beq     2f
  move.b  (%a0)+, (%a1)+
  bra     1b

2:

  /* C library */
  move.l  #__FINI_SECTION__, -(%sp)
  jsr     atexit
  jsr     __INIT_SECTION__

  /* call main(int argc, char *argv[] */
  move.l  #0, -(sp)
  move.l  #0, -(sp)
  move.l  #0, -(sp)
  jsr     main
  lea     (sp, 12), %sp

  /* stop on exit from main. */
1:
  halt

