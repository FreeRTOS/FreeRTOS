/*
 * FreeRTOS+FAT FS V1.0.0 (C) 2013 HCC Embedded
 *
 * The FreeRTOS+FAT SL license terms are different to the FreeRTOS license 
 * terms.
 * 
 * FreeRTOS+FAT SL uses a dual license model that allows the software to be used
 * under a pure GPL open source license (as opposed to the modified GPL licence
 * under which FreeRTOS is distributed) or a commercial license.  Details of 
 * both license options follow:
 * 
 * - Open source licensing -
 * FreeRTOS+FAT SL is a free download and may be used, modified, evaluated and
 * distributed without charge provided the user adheres to version two of the 
 * GNU General Public License (GPL) and does not remove the copyright notice or 
 * this text.  The GPL V2 text is available on the gnu.org web site, and on the
 * following URL: http://www.FreeRTOS.org/gpl-2.0.txt.
 * 
 * - Commercial licensing -
 * Businesses and individuals who for commercial or other reasons cannot comply
 * with the terms of the GPL V2 license must obtain a commercial license before 
 * incorporating FreeRTOS+FAT SL into proprietary software for distribution in 
 * any form.  Commercial licenses can be purchased from 
 * http://shop.freertos.org/fat_sl and do not require any source files to be 
 * changed.
 *
 * FreeRTOS+FAT SL is distributed in the hope that it will be useful.  You
 * cannot use FreeRTOS+FAT SL unless you agree that you use the software 'as
 * is'.  FreeRTOS+FAT SL is provided WITHOUT ANY WARRANTY; without even the
 * implied warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. Real Time Engineers Ltd. and HCC Embedded disclaims all
 * conditions and terms, be they implied, expressed, or statutory.
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/FreeRTOS-Plus
 *
 */

#define FS_MUTEX_DEFINED

#include "../../api/fat_sl.h"
#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

#if F_FS_THREAD_AWARE == 1

xSemaphoreHandle fs_lock_semaphore;


/*
** fr_findfirst
**
** find first time a file using wildcards
**
** INPUT : filename - name of the file
**         *find - pointer to a pre-define F_FIND structure
** RETURN: F_NOERR - on success
**         F_ERR_NOTFOUND - if not found
*/
unsigned char fr_findfirst ( const char * filename, F_FIND * find )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_findfirst( filename, find );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_findnext
**
** find next time a file using wildcards
**
** INPUT : *find - pointer to a pre-define F_FIND structure
** RETURN: F_NOERR - on success
**         F_ERR_NOTFOUND - if not found
*/
unsigned char fr_findnext ( F_FIND * find )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_findnext( find );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_filelength
**
** Get the length of a file
**
** INPUT : filename - name of the file
** RETURN: size of the file or F_ERR_INVALID if not exists or volume not working
*/
long fr_filelength ( const char * filename )
{
  unsigned long  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_filelength( filename );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = 0;
  }

  return rc;
}


/*
** fr_open
**
** open a file
**
** INPUT : filename - file to be opened
**         mode - open method (r,w,a,r+,w+,a+)
** RETURN: pointer to a file descriptor or 0 on error
*/
F_FILE * fr_open ( const char * filename, const char * mode )
{
  F_FILE * rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_open( filename, mode );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = NULL;
  }

  return rc;
}


/*
** fr_close
**
** Close a previously opened file.
**
** INPUT : *filehandle - pointer to the file descriptor
** RETURN: F_NOERR on success, other if error
*/
unsigned char fr_close ( F_FILE * filehandle )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_close( filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_read
**
** Read from a file.
**
** INPUT : buf - buffer to read data
**         size - number of unique
**         size_st - size of unique
**         *filehandle - pointer to file descriptor
** OUTPUT: number of read bytes
*/
long fr_read ( void * bbuf, long size, long size_st, F_FILE * filehandle )
{
  long  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_read( bbuf, size, size_st, filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = 0;
  }

  return rc;
}


/*
** fr_write
**
** INPUT : bbuf - buffer to write from
**         size - number of unique
**         size_st - size of unique
**         *filehandle - pointer to the file descriptor
** RETURN: number of written bytes
*/
long fr_write ( const void * bbuf, long size, long size_st, F_FILE * filehandle )
{
  long  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_write( bbuf, size, size_st, filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = 0;
  }

  return rc;
}

/*
** fr_seek
**
** Seek in a file.
**
** INPUT : *filehandle - pointer to a file descriptor
**         offset - offset
**         whence - F_SEEK_SET: position = offset
**                  F_SEEK_CUR: position = position + offset
**                  F_SEEK_END: position = end of file (offset=0)
** RETURN: F_NOERR on succes, other if error.
*/
unsigned char fr_seek ( F_FILE * filehandle, long offset, unsigned char whence )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_seek( filehandle, offset, whence );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}

/*
** fr_tell
**
** get current position in the file
**
** INPUT : *filehandle - pointer to a file descriptor
** RETURN: -1 on error or current position.
*/
long fr_tell ( F_FILE * filehandle )
{
  long  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_tell( filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = -1;
  }

  return rc;
}

/*
** fr_getc
**
** read one byte from a file
**
** INPUT : *filehandle - pointer to a file descriptor
** RETURN: -1 if error, otherwise the read character.
*/
int fr_getc ( F_FILE * filehandle )
{
  int  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_getc( filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = -1;
  }

  return rc;
}

/*
** fr_putc
**
** write one byte to a file
**
** INPUT : ch - character to write
**         *filehandle - pointer to a file handler
** RETURN: ch on success, -1 on error
*/
int fr_putc ( int ch, F_FILE * filehandle )
{
  int  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_putc( ch, filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = -1;
  }

  return rc;
}

/*
** fr_rewind
**
** set current position in the file to the beginning
**
** INPUT : *filehandle - pointer to a file descriptor
** RETURN: F_NOERR on succes, other if error.
*/
unsigned char fr_rewind ( F_FILE * filehandle )
{
  unsigned char rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_rewind( filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}

/*
** fr_eof
**
** check if current position is at the end of the file.
**
** INPUT : *filehandle - pointer to a file descriptor
** RETURN: F_ERR_EOF - at the end of the file
**         F_NOERR - no error, end of the file not reached
**         other - on error
*/
unsigned char fr_eof ( F_FILE * filehandle )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_eof( filehandle );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}

/*
** Format the device
*/
unsigned char fr_hardformat ( unsigned char fattype )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_hardformat( fattype );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}

/*
** fr_get_serial
**
** Get serial number
**
** OUTPUT: serial - where to write the serial number
** RETURN: error code
*/
unsigned char fr_getserial ( unsigned long * serial )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_getserial( serial );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_delete
**
** Delete a file. Removes the chain that belongs to the file and inserts a new descriptor
** to the directory with first_cluster set to 0.
**
** INPUT : filename - name of the file to delete
** RETURN: F_NOERR on success, other if error.
*/
unsigned char fr_delete ( const char * filename )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_delete( filename );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}

/*
** fr_truncate
**
** Open a file and set end of file
**
** INPUT:	filename - name of the file
**		filesize - required new size
** RETURN:	NULL on error, otherwise file pointer
*/
F_FILE * fr_truncate ( const char * filename, long filesize )
{
  F_FILE * f;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    f = fn_truncate( filename, filesize );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    f = NULL;
  }

  return f;
}


/*
** fr_getfreespace
**
** Get free space on the volume
**
** OUTPUT: *sp - pre-defined F_SPACE structure, where information will be stored
** RETURN: F_NOERR - on success
**         F_ERR_NOTFORMATTED - if volume is not formatted
*/
unsigned char fr_getfreespace ( F_SPACE * sp )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_getfreespace( sp );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_chdir
**
** Change to a directory
**
** INPUT:  path - path to the dircetory
** RETURN: 0 - on success, other if error
*/
unsigned char fr_chdir ( const char * path )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_chdir( path );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_mkdir
**
** Create a directory
**
** INPUT:  path - new directory path
** RETURN: 0 - on success, other if error
*/
unsigned char fr_mkdir ( const char * path )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_mkdir( path );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_rmdir
**
** Removes a directory
**
** INPUT:  path - path to remove
** RETURN: 0 - on success, other if error
*/
unsigned char fr_rmdir ( const char * path )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_rmdir( path );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_getcwd
**
** Get current working directory
**
** INPUT:  maxlen - maximum length allowed
** OUTPUT: path - current working directory
** RETURN: 0 - on success, other if error
*/
unsigned char fr_getcwd ( char * path, unsigned char maxlen, char root )
{
  unsigned char  rc;

  if( xSemaphoreTake( fs_lock_semaphore, F_MAX_LOCK_WAIT_TICKS ) == pdPASS )
  {
    rc = fn_getcwd( path, maxlen, root );
    xSemaphoreGive( fs_lock_semaphore );
  }
  else
  {
    rc = F_ERR_OS;
  }

  return rc;
}


/*
** fr_init
**
** Initialize FAT_SL OS module
**
** RETURN: F_NO_ERROR or F_ERR_OS
*/
unsigned char fr_init ( void )
{
  return F_NO_ERROR;
}

#endif /* F_FS_THREAD_AWARE */

