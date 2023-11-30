/* sys/sio.h -- Utility methods to read/write the SIO
   Copyright 2000 Free Software Foundation, Inc.
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

#ifndef _SYS_SIO_H
#define _SYS_SIO_H

#include <sys/param.h>
#include <sys/ports.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void serial_init (void);

/* Return != 0 if there is something to read on the serial line.  */
extern unsigned char serial_receive_pending (void);

/* Wait until the SIO has finished to send the character.  */
extern void serial_flush (void);

/* Return != 0 if serial port is ready to send another char.  */
extern unsigned char serial_send_ready (void);

/* Send the character on the serial line.  */
extern void serial_send (char c);

/* Wait for a character on the serial line and return it.  */
extern unsigned char serial_recv (void);

/** Write the string on the serial line.

    @param msg null terminated string to write.

    @see serial_init, serial_send
*/
extern void serial_print (const char *msg);

/** Wait for a string from serial line.

    @param msg buffer that will hold the string.

    @see serial_init, serial_recv
*/
extern void serial_getline (char *buf);

#ifdef mc6811
//# include <asm-m68hc11/sio.h>
#endif

#ifdef mc68hcs12
# include <asm-m68hcs12/sio.h>
#elif defined(mc6812)
//# include <asm-m68hc12/sio.h>
#endif


#ifdef __cplusplus
};
#endif
#endif /* _SYS_SIO_H */

