/* sys/ports_def.h -- Definition of system ports
   Copyright 2000 Free Software Foundation, Inc.
   Written by Stephane Carrez (stcarrez@worldnet.fr)

This file is part of GEL.

GEL is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
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

#ifndef _SYS_PORTS_DEF_H
#define _SYS_PORTS_DEF_H

#ifdef mc6811
//# include <asm-m68hc11/ports_def.h>
#endif

#ifdef mc68hcs12
# include <asm-m68hcs12/ports_def.h>
#elif defined(mc6812)
//# include <asm-m68hc12/ports_def.h>
#endif

#endif /* _SYS_PORTS_DEF_H */

