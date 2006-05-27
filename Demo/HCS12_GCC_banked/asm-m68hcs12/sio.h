/* m68hc11/sio.h -- Utility methods to read/write the SIO
   Copyright 1999, 2000, 2003 Free Software Foundation, Inc.
   Written by Stephane Carrez (stcarrez@nerim.fr)

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

#ifndef _M68HC12_SIO_H
#define _M68HC12_SIO_H

#include <sys/param.h>
#include <sys/ports.h>

/*  Initialize SCI serial port to default baudrate and enable. */
extern inline void
serial_init (void)
{
  SCIBD = M6811_DEF_BAUD;
  SCICR1 = 0x00;            //typical 8 bit
  SCICR2 = 0x0c;            //Enable sci for polling
}

/* Return != 0 if there is something to read on the serial line.  */
extern inline unsigned char
serial_receive_pending (void)
{
  return SCISR1 & RDRF;
}

/* Wait until the SIO has finished to send the character.  */
extern inline void
serial_flush (void)
{
  while (!(SCISR1 & TDRE))
    cop_optional_reset ();
}

/* Return != 0 if serial port is ready to send another char.  */
extern inline unsigned char
serial_send_ready (void)
{
  return SCISR1 & TDRE;
}

/* Send the character on the serial line.  */
extern inline void
serial_send (char c)
{
  serial_flush ();
  SCIDRL = c;
  SCICR2 |= (1<<3);
}

/* Wait for a character on the serial line and return it.  */
extern inline unsigned char
serial_recv (void)
{
  while (!(SCISR1 & RDRF))
    cop_optional_reset ();

  return SCIDRL;
}

extern void serial_print (const char *msg);
extern void serial_getline (char *buf);

#endif /* _M68HC11_SIO_H */

