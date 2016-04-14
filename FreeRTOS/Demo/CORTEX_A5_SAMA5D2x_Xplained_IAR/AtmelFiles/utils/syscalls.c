/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
  * \file syscalls.c
  *
  * Implementation of syscall bindings.
  *
  */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "compiler.h"
#include "misc/console.h"

#ifdef __GNUC__

#include <stdio.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/stat.h>

/*----------------------------------------------------------------------------
 *        Imported variables
 *----------------------------------------------------------------------------*/

extern int _heap;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/* Desactivate stream buffering */
CONSTRUCTOR static void _disable_io_buffering(void)
{
	setvbuf(stdout, (char *)NULL, _IONBF, 0);
}

extern caddr_t _sbrk(int incr);
caddr_t _sbrk(int incr)
{
	static unsigned char *heap = NULL;
	unsigned char *prev_heap;

	if (heap == NULL) {
		heap = (unsigned char *) &_heap;
	}
	prev_heap = heap;

	heap += incr;

	return (caddr_t) prev_heap;
}

extern int _getpid(void);
int _getpid(void)
{
	return -1;
}

extern void _kill(int pid, int sig);
void _kill(int pid, int sig)
{
	return;
}

extern void _exit(int status);
void _exit(int status)
{
	printf("Program terminated with status %d.\n", status);
	while (1) ;
}

extern int _fstat(int file, struct stat *st);
int _fstat(int file, struct stat *st)
{
	st->st_mode = S_IFCHR;
	return 0;
}

extern int _lseek(int file, int ptr, int dir);
int _lseek(int file, int ptr, int dir)
{
	return 0;
}

extern int _isatty(int file);
int _isatty(int file)
{
	return 1;
}

extern int _read(int file, char *ptr, int len);
int _read(int file, char *ptr, int len)
{
	return 0;
}

extern int _write(int file, char *ptr, int len);
int _write(int file, char *ptr, int len)
{
	int i;

	for (i = 0; i < len; i++, ptr++) {
		console_put_char(*ptr);
	}

	return i;
}

extern int _close(int file);
int _close(int file)
{
	return -1;
}

#elif defined __ICCARM__  /* IAR Ewarm 5.41+ */

/**
 * \brief Outputs a character on the DBGU.
 *
 * \param c  Character to output.
 *
 * \return The character that was output.
 */
WEAK int putchar(int c)
{
	console_put_char(c);
	return c;
}

#endif  /* defined __ICCARM__ */
