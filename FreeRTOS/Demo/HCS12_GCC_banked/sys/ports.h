/* sys/ports.h -- Definition of system ports
   Copyright 2000, 2001, 2002 Free Software Foundation, Inc.
   Written by Stephane Carrez (stcarrez@worldnet.fr)

This file is part of GEL.

GEL is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License** as published by
the Free Software Foundation; either version 2, or (at your option)
any later version.

GEL is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GEL; see the file COPYING.  If not, write to
the Free Software Foundation, 59 Temple Place - Suite 330,
Boston, MA 02111-1307, USA.  */

#ifndef _SYS_PORTS_H
#define _SYS_PORTS_H

#ifdef __cplusplus
extern "C" {
#endif

  extern unsigned short get_timer_counter (void);
  extern void set_timer_counter (unsigned short);
  extern unsigned short get_input_capture_1 (void);
  extern void set_input_capture_1 (unsigned short);
  extern unsigned short get_input_capture_2 (void);
  extern void set_input_capture_2 (unsigned short);
  extern unsigned short get_input_capture_3 (void);
  extern void set_input_capture_3 (unsigned short);
  extern unsigned short get_output_compare_1 (void);
  extern void set_output_compare_1 (unsigned short);
  extern unsigned short get_output_compare_2 (void);
  extern void set_output_compare_2 (unsigned short);
  extern unsigned short get_output_compare_3 (void);
  extern void set_output_compare_3 (unsigned short);
  extern unsigned short get_output_compare_4 (void);
  extern void set_output_compare_4 (unsigned short);
  extern unsigned short get_output_compare_5 (void);
  extern void set_output_compare_5 (unsigned short);
  extern void set_bus_expanded (void);
  extern void set_bus_single_chip (void);
  extern void cop_reset (void);
  extern void cop_optional_reset (void);
  extern void timer_acknowledge (void);
  extern void timer_initialize_rate (unsigned char);
  
#ifdef mc6811
//# include <asm-m68hc11/ports.h>
#endif

#ifdef mc68hcs12
# include <asm-m68hcs12/ports.h>
#elif defined(mc6812)
//# include <asm-m68hc12/ports.h>
#endif

#ifdef __cplusplus
};
#endif
  
#endif /* _SYS_PORTS_H */

