/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * Stubs for Newlib system calls.
 *  
 * SVN $Revision: 2020 $
 * SVN $Date: 2010-01-20 14:51:50 +0000 (Wed, 20 Jan 2010) $
 */
#include <stdlib.h>
#include <sys/unistd.h>
#include <sys/stat.h>
#include <sys/times.h>
#include <errno.h>
#undef errno
extern int errno;

/*==============================================================================
 * Redirection of standard output to a SmartFusion MSS UART.
 *------------------------------------------------------------------------------
 * A default implementation for the redirection of the output of printf() to a
 * UART is provided as the bottom of this file. This redirection is enabled by
 * adding the symbol/define ACTEL_STDIO_THRU_UART to your project and
 * specifying the baud rate using the ACTEL_STDIO_BAUD_RATE define.
 */
#ifdef ACTEL_STDIO_THRU_UART
#include "../../drivers/mss_uart/mss_uart.h"

#ifndef ACTEL_STDIO_BAUD_RATE
#define ACTEL_STDIO_BAUD_RATE  MSS_UART_57600_BAUD
#endif

/*------------------------------------------------------------------------------
 * Global flag used to indicate if the UART driver needs to be initialized.
 */
static int g_stdio_uart_init_done = 0;

#endif	/* ACTEL_STDIO_THRU_UART */

/*==============================================================================
 * Environment variables.
 * A pointer to a list of environment variables and their values. For a minimal
 * environment, this empty list is adequate:
 */
char *__env[1] = { 0 };
char **environ = __env;

/*==============================================================================
 * Close a file.
 */
int _close(int file)
{
    return -1;
}

/*==============================================================================
 * Transfer control to a new process.
 */
int _execve(char *name, char **argv, char **env)
{
    errno = ENOMEM;
    return -1;
}

/*==============================================================================
 * Exit a program without cleaning up files.
 */
void _exit( int code )
{
	/* Should we force a system reset? */
	while( 1 )
	{
		;
	}
}

/*==============================================================================
 * Create a new process.
 */
int _fork(void)
{
    errno = EAGAIN;
    return -1;
}

/*==============================================================================
 * Status of an open file.
 */
int _fstat(int file, struct stat *st)
{
    st->st_mode = S_IFCHR;
    return 0;
}

/*==============================================================================
 * Process-ID
 */
int _getpid(void)
{
    return 1;
}

/*==============================================================================
 * Query whether output stream is a terminal.
 */
int _isatty(int file)
{
    return 1;
}

/*==============================================================================
 * Send a signal.
 */
int _kill(int pid, int sig)
{
    errno = EINVAL;
    return -1;
}

/*==============================================================================
 * Establish a new name for an existing file.
 */
int _link(char *old, char *new)
{
    errno = EMLINK;
    return -1;
}

/*==============================================================================
 * Set position in a file.
 */
int _lseek(int file, int ptr, int dir)
{
    return 0;
}

/*==============================================================================
 * Open a file.
 */
int _open(const char *name, int flags, int mode)
{
    return -1;
}

/*==============================================================================
 * Read from a file.
 */
int _read(int file, char *ptr, int len)
{
    return 0;
}

/*==============================================================================
 * Increase program data space. As malloc and related functions depend on this,
 * it is useful to have a working implementation. The following suffices for a
 * standalone system; it exploits the symbol _end automatically defined by the
 * GNU linker. 
 */
caddr_t _sbrk(int incr)
{
    extern char _end;		/* Defined by the linker */
    static char *heap_end;
    char *prev_heap_end;
    char * stack_ptr;
    
    if (heap_end == 0)
    {
      heap_end = &_end;
    }
    
    prev_heap_end = heap_end;
    asm volatile ("MRS %0, msp" : "=r" (stack_ptr) );
    if (heap_end + incr > stack_ptr)
    {
      write (1, "Heap and stack collision\n", 25);
      abort ();
    }
  
    heap_end += incr;
    return (caddr_t) prev_heap_end;
}

/*==============================================================================
 * Status of a file (by name).
 */
int _stat(char *file, struct stat *st)
{
    st->st_mode = S_IFCHR;
    return 0;
}

/*==============================================================================
 * Timing information for current process.
 */
int _times(struct tms *buf)
{
    return -1;
}

/*==============================================================================
 * Remove a file's directory entry.
 */
int _unlink(char *name)
{
    errno = ENOENT;
    return -1;
}

/*==============================================================================
 * Wait for a child process.
 */
int _wait(int *status)
{
    errno = ECHILD;
    return -1;
}

/*==============================================================================
 * Write to a file. libc subroutines will use this system routine for output to
 * all files, including stdout—so if you need to generate any output, for
 * example to a serial port for debugging, you should make your minimal write
 * capable of doing this.
 */
int _write_r( void * reent, int file, char * ptr, int len )
{
#ifdef ACTEL_STDIO_THRU_UART
	/*--------------------------------------------------------------------------
	 * Initialize the UART driver if it is the first time this function is
	 * called.
	 */
	if ( !g_stdio_uart_init_done )
	{
		MSS_UART_init( &g_mss_uart0, ACTEL_STDIO_BAUD_RATE, (MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY));
		g_stdio_uart_init_done = 1;
	}
	
	/*--------------------------------------------------------------------------
	 * Output text to the UART.
	 */
	MSS_UART_polled_tx( &g_mss_uart0, (uint8_t *)ptr, len );
	
	return len;
#else	/* ACTEL_STDIO_THRU_UART */
	return 0;
#endif	/* ACTEL_STDIO_THRU_UART */
}


