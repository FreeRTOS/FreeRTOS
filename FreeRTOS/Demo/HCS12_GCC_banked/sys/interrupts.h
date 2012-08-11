/* Interrupt Vectors
   Copyright (C) 2000, 2002, 2003 Free Software Foundation, Inc.
   Written by Stephane Carrez (stcarrez@nerim.fr)	

This file is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 2, or (at your option) any
later version.

In addition to the permissions in the GNU General Public License, the
Free Software Foundation gives you unlimited permission to link the
compiled version of this file with other programs, and to distribute
those programs without any restriction coming from the use of this
file.  (The General Public License restrictions do apply in other
respects; for example, they cover modification of the file, and
distribution when not linked into another program.)

This file is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; see the file COPYING.  If not, write to
the Free Software Foundation, 59 Temple Place - Suite 330,
Boston, MA 02111-1307, USA.  */

#ifndef _SYS_INTERRUPTS_H
#define _SYS_INTERRUPTS_H

#include <sys/param.h>

#ifdef mc6811
//# include <asm-m68hc11/interrupts.h>
#endif

#ifdef mc68hcs12
# include <asm-m68hcs12/interrupts.h>
#elif defined(mc6812)
//# include <asm-m68hc12/interrupts.h>
#endif

/*! Install an interrupt handler.

    Install the interrupt handler for an exception.  The handler
    is installed for \b bootstrap mode and also for \b normal operating
    mode.
    
    @param id the interrupt number to be installed
    @param handler the interrupt handler entry point
*/
extern void
set_interrupt_handler (interrupt_vector_id id, interrupt_t handler);

/*! Default and fatal interrupt handler.

    This function is an interrupt handler intended to be used to
    handle all interrupt not used by a program.  Since it is an
    error to have an interrupt when it is not handled, the default
    behavior is to print a message and stop.  */
extern void __attribute__((interrupt, noreturn))
fatal_interrupt (void);

#include <arch/interrupts.h>

/*! Entry point of any program.

    This function should never be called by itself.  It represents the
    entry point of any program.  It is intended to be used in an
    interrupt table to specify the function to jump to after reset.  */
extern void _start (void);

#endif
