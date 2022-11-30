/* interrupts.h - Register interrupt vectors (if ram based)
   Copyright (C) 2004 Robotronics, Inc.
   Author Jefferson Smith, Robotronics

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

#ifndef _M68HC12_ARCH_DRAGON12_INTERRUPTS_H
#define _M68HC12_ARCH_DRAGON12_INTERRUPTS_H

#define USE_INTERRUPT_TABLE

/* Only for RAM target. Initializes an interrupt handler vector.  */
extern inline void
set_interrupt_handler (interrupt_vector_id id ATTRIBUTE_UNUSED,
                       interrupt_t handler ATTRIBUTE_UNUSED)
{
  _vectors_addr[id] = handler;
}

#endif  /* _M68HC12_ARCH_DRAGON12_INTERRUPTS_H */
