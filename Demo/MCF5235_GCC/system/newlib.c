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
	***************************************************************************
	*																		  *
	* SAVE TIME AND MONEY!  Why not get us to quote to get FreeRTOS.org		  *
	* running on your hardware - or even write all or part of your application*
	* for you?  See http://www.OpenRTOS.com for details.					  *
	*																		  *
	***************************************************************************
	***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/* ------------------------ System includes ------------------------------- */
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>

/* ------------------------ FreeRTOS includes ----------------------------- */
#include <FreeRTOS.h>
#include <serial.h>

/* ------------------------ Prototypes ------------------------------------ */
void vSerialPutStringNOISR( xComPortHandle pxPort,
                            const signed portCHAR * const pcString,
                            unsigned portSHORT usStringLength );

/* ------------------------ Start implementation -------------------------- */
void
_exit( int status )
{
    asm volatile    ( "halt" );

    for( ;; );
}

pid_t
getpid( void )
{
    return 0;
}

int
kill( pid_t pid, int sig )
{
    _exit( 0 );
}

int
close( int fd )
{
    return 0;
}

int
fstat( int fd, struct stat *buf )
{
    buf->st_mode = S_IFCHR;
    buf->st_blksize = 0;
    return 0;
}

ssize_t
write( int fd, const void *buf, size_t nbytes )
{
    ssize_t res = nbytes;
    extern xComPortHandle xSTDComPort;
    switch ( fd )
    {
        case STDERR_FILENO:
            vSerialPutStringNOISR( xSTDComPort,
                                   ( const signed portCHAR * const )buf,
                                   ( unsigned portSHORT )nbytes );
            break;
        case STDOUT_FILENO:
            vSerialPutString( xSTDComPort,
                              ( const signed portCHAR * const)buf,
                              ( unsigned portSHORT )nbytes );
            break;
        default:
            errno = EIO;
            res = -1;
            break;
    }
    return res;
}

int
read( int fd, void *buf, size_t nbytes )
{
    switch ( fd )
    {
        default:
            errno = EIO;
            return -1;
    }
}

int
isatty( int fd )
{
    return 0;
}

off_t
lseek( int fd, off_t offset, int whence )
{
    errno = EIO;
    return ( off_t ) - 1;
}

extern char     _end[];
char           *heap_ptr;

void           *
sbrk( ptrdiff_t nbytes )
{
    char           *base;

    if( !heap_ptr )
        heap_ptr = ( char * )&_end;
    base = heap_ptr;
    heap_ptr += nbytes;

    return base;
}
