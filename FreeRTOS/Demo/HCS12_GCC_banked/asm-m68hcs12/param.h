/* param.h - Board specific parameters
   Copyright (C) 2000 Free Software Foundation, Inc.
   Written by Stephane Carrez (stcarrez@worldnet.fr)	

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

#ifndef _M68HC11_PARAM_H
#define _M68HC11_PARAM_H

/**@name M68HC12 Board Parameters.

   This section contains several '#define' to give configuration
   characteristics of the target board.  */
/*@{*/

/** CPU Clock frequency.
 
   Define the frequency of the oscillator plugged on the processor.
   The value is in hertz. */
#ifndef M6811_CPU_CLOCK
# define M6811_CPU_CLOCK (16e6L)
#endif

/** CPU E clock.
    
   The E clock frequency.  This frequency is used as the
   basis for timer computation.  The value is in hertz.  */
#ifndef M6811_CPU_E_CLOCK
# define M6811_CPU_E_CLOCK (24e6L)
#endif

#ifndef M6812_REFCLOCK
# define M6812_REFCLOCK		M6811_CPU_CLOCK
#endif

#ifndef M6812_REFDVVAL
# define M6812_REFDVVAL		(M6811_CPU_CLOCK / M6812_REFCLOCK) - 1
#endif

#ifndef M6812_SYNRVAL
#define M6812_SYNRVAL		(M6811_CPU_E_CLOCK / M6812_REFCLOCK) - 1
#endif

/** SIO default baud rate.
    
   Defines the default baud rate of the SIO.  This value
   is used to configure the BAUD register.
  */
#ifndef M6811_DEF_BAUD
# define M6811_DEF_BAUD	(unsigned short)(M6811_CPU_E_CLOCK / 16 / 9600)
#endif

/** Use the COP.
    
   Define this if you are using the COP timer.
   This activate the COP reset while polling and writing on
   the serial line.  */
#ifndef M6811_USE_COP
# define M6811_USE_COP 0
#endif

/** Timer prescaler value.  */
#ifndef M6811_DEF_TPR
# define M6811_DEF_TPR 0
#endif

#ifndef M6811_DEF_RTR
# define M6811_DEF_RTR 0
#endif

/** SCI default port. */
#ifndef M6812_DEF_SCI
# define M6812_DEF_SCI   0
#endif

/*@}*/

#endif
