/* m68hc11/ports.h -- Definition of 68HC11 ports
   Copyright 1999, 2000, 2003 Free Software Foundation, Inc.
   Written by Stephane Carrez (stcarrez@nerim.fr)

   Modified by Jefferson L Smith, Robotronics Inc.

This file is part of GDB, GAS, and the GNU binutils.

GDB, GAS, and the GNU binutils are free software; you can redistribute
them and/or modify them under the terms of the GNU General Public
License as published by the Free Software Foundation; either version
1, or (at your option) any later version.

GDB, GAS, and the GNU binutils are distributed in the hope that they
will be useful, but WITHOUT ANY WARRANTY; without even the implied
warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See
the GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this file; see the file COPYING.  If not, write to the Free
Software Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.  */

#ifndef _M68HC11_PORTS_H
#define _M68HC11_PORTS_H

#include "ports_def.h"

/** Define default SCI port registers */
#if defined(M6812_DEF_SCI)

#if M6812_DEF_SCI==2
# define SCI_BASE	SCI2_BASE
#elif M6812_DEF_SCI==1
# define SCI_BASE	SCI1_BASE
#else /* default M6812_DEF_SCI==0 */
# define SCI_BASE	SCI0_BASE
#endif /* default M6812_DEF_SCI==0 */

#else  /* M6812_DEF_SCI not defined */
# define SCI_BASE	SCI0_BASE
#endif /* M6812_DEF_SCI */

# define SCIBD		PORTIO_16(SCI_BASE + _SCIBD)
# define SCICR1		PORTIO_8(SCI_BASE + _SCICR1)
# define SCICR2		PORTIO_8(SCI_BASE + _SCICR2)
# define SCISR1		PORTIO_8(SCI_BASE + _SCISR1)
# define SCISR2		PORTIO_8(SCI_BASE + _SCISR2)
# define SCIDRL		PORTIO_8(SCI_BASE + _SCIDRL)

extern inline unsigned short
get_timer_counter (void)
{
  return TCNT;
}

extern inline void
set_timer_counter (unsigned short value)
{
  TCNT = value;
}
#if 0
extern inline unsigned short
get_input_capture_1 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TIC1_H])[0];
}

extern inline void
set_input_capture_1 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TIC1_H])[0] = value;
}

extern inline unsigned short
get_input_capture_2 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TIC2_H])[0];
}

extern inline void
set_input_capture_2 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TIC2_H])[0] = value;
}

extern inline unsigned short
get_input_capture_3 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TIC3_H])[0];
}

extern inline void
set_input_capture_3 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TIC3_H])[0] = value;
}

/* Get output compare 16-bit register.  */
extern inline unsigned short
get_output_compare_1 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TOC1_H])[0];
}

extern inline void
set_output_compare_1 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TOC1_H])[0] = value;
}

extern inline unsigned short
get_output_compare_2 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TOC2_H])[0];
}

extern inline void
set_output_compare_2 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TOC2_H])[0] = value;
}

extern inline unsigned short
get_output_compare_3 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TOC3_H])[0];
}

extern inline void
set_output_compare_3 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TOC3_H])[0] = value;
}

extern inline unsigned short
get_output_compare_4 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TOC4_H])[0];
}

extern inline void
set_output_compare_4 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TOC4_H])[0] = value;
}

extern inline unsigned short
get_output_compare_5 (void)
{
  return ((unsigned volatile short*) &_io_ports[M6811_TOC5_H])[0];
}

extern inline void
set_output_compare_5 (unsigned short value)
{
  ((unsigned volatile short*) &_io_ports[M6811_TOC5_H])[0] = value;
}

#endif

/* Reset the COP.  */
extern inline void
cop_reset (void)
{
  ARMCOP = 0x55;
  ARMCOP = 0xAA;
}

extern inline void
cop_optional_reset (void)
{
#if defined(M6811_USE_COP) && M6811_USE_COP == 1
  cop_reset ();
#endif
}

/* Acknowledge the timer interrupt.  */
extern inline void
timer_acknowledge (void)
{
  CRGFLG = RTIF;
}

/* Initialize the timer.  */
extern inline void
timer_initialize_rate (unsigned char divisor)
{
  RTICTL = divisor;
}

#endif /* _M68HC11_PORTS_H */

