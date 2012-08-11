/* Don't need anything here. */

#include <stdlib.h>
#include <sys/stat.h>

int _read_r (struct _reent *r, int file, char * ptr, int len)
{
	( void ) r;
	( void ) file;
	( void ) ptr;
	( void ) len;
	return -1;
}

/***************************************************************************/

int _lseek_r (struct _reent *r, int file, int ptr, int dir)
{
	( void ) r;
	( void ) file;
	( void ) ptr;
	( void ) dir;
	
	return 0;
}

/***************************************************************************/

int _write_r (struct _reent *r, int file, char * ptr, int len)
{  
	( void ) r;
	( void ) file;
	( void ) ptr;
	( void ) len;
	
	return 0;
}

/***************************************************************************/

int _close_r (struct _reent *r, int file)
{
	( void ) r;
	( void ) file;

	return 0;
}

/***************************************************************************/

caddr_t _sbrk_r (struct _reent *r, int incr)
{
	( void ) r;
	( void ) incr;
	
	return 0;
}

/***************************************************************************/

int _fstat_r (struct _reent *r, int file, struct stat * st)
{
	( void ) r;
	( void ) file;
	( void ) st;
	
	return 0;
}

/***************************************************************************/

int _isatty_r(struct _reent *r, int fd)
{
	( void ) r;
	( void ) fd;
	
	return 0;
}




