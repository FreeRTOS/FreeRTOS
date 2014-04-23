/*
 * FreeRTOS+FAT SL V1.0.1 (C) 2014 HCC Embedded
 *
 * The FreeRTOS+FAT SL license terms are different to the FreeRTOS license 
 * terms.
 * 
 * FreeRTOS+FAT SL uses a dual license model that allows the software to be used 
 * under a standard GPL open source license, or a commercial license.  The 
 * standard GPL license (unlike the modified GPL license under which FreeRTOS 
 * itself is distributed) requires that all software statically linked with 
 * FreeRTOS+FAT SL is also distributed under the same GPL V2 license terms.  
 * Details of both license options follow:
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

#ifndef _API_FAT_SL_H_
#define _API_FAT_SL_H_

#include "config_fat_sl.h"

#include "../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 5 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

#ifdef __cplusplus
extern "C" {
#endif

#define F_MAXNAME 8                  /* 8 byte name */
#define F_MAXEXT  3                  /* 3 byte extension */

typedef struct
{
  char  path[F_MAXPATH];        /*  /directory1/dir2/  */
  char  filename[F_MAXNAME];    /* filename */
  char  fileext[F_MAXEXT];      /* extension */
} F_NAME;

typedef struct
{
  unsigned long  cluster;
  unsigned long  sector;
  unsigned long  sectorend;
  unsigned long  pos;
} F_POS;

typedef struct
{
  char            filename[F_MAXPATH]; /*file name+ext*/
  char            name[F_MAXNAME];     /*file name*/
  char            ext[F_MAXEXT];       /*file extension*/
  unsigned char   attr;                /*attribute of the file*/

  unsigned short  ctime;        /*creation time*/
  unsigned short  cdate;        /*creation date*/
  unsigned long   cluster;

  long            filesize;         /*length of file*/

  F_NAME          findfsname;   /*find properties*/
  F_POS           pos;
} F_FIND;

#define F_ATTR_ARC         0x20
#define F_ATTR_DIR         0x10
#define F_ATTR_VOLUME      0x08
#define F_ATTR_SYSTEM      0x04
#define F_ATTR_HIDDEN      0x02
#define F_ATTR_READONLY    0x01

#define F_CLUSTER_FREE     ( (unsigned long)0x00000000 )
#define F_CLUSTER_RESERVED ( (unsigned long)0x0ffffff0 )
#define F_CLUSTER_BAD      ( (unsigned long)0x0ffffff7 )
#define F_CLUSTER_LAST     ( (unsigned long)0x0ffffff8 )
#define F_CLUSTER_LASTF32R ( (unsigned long)0x0fffffff )

#define F_ST_MISSING       0x00000001
#define F_ST_CHANGED       0x00000002
#define F_ST_WRPROTECT     0x00000004

typedef struct
{
  unsigned long  abspos;
  unsigned long  filesize;
  unsigned long  startcluster;
  unsigned long  relpos;
  unsigned char  modified;
  unsigned char  mode;
  unsigned char  _tdata[F_SECTOR_SIZE];
  F_POS          pos;
  F_POS          dirpos;
#if F_FILE_CHANGED_EVENT
  char           filename[F_MAXPATH];   /* filename with full path */
#endif
} F_FILE;

enum
{
  F_UNKNOWN_MEDIA
  , F_FAT12_MEDIA
  , F_FAT16_MEDIA
  , F_FAT32_MEDIA
};

enum
{
/*  0 */
  F_NO_ERROR,

/*  1 */ F_ERR_RESERVED_1,

/*  2 */ F_ERR_NOTFORMATTED,

/*  3 */ F_ERR_INVALIDDIR,

/*  4 */ F_ERR_INVALIDNAME,

/*  5 */ F_ERR_NOTFOUND,

/*  6 */ F_ERR_DUPLICATED,

/*  7 */ F_ERR_NOMOREENTRY,

/*  8 */ F_ERR_NOTOPEN,

/*  9 */ F_ERR_EOF,

/* 10 */ F_ERR_RESERVED_2,

/* 11 */ F_ERR_NOTUSEABLE,

/* 12 */ F_ERR_LOCKED,

/* 13 */ F_ERR_ACCESSDENIED,

/* 14 */ F_ERR_NOTEMPTY,

/* 15 */ F_ERR_INITFUNC,

/* 16 */ F_ERR_CARDREMOVED,

/* 17 */ F_ERR_ONDRIVE,

/* 18 */ F_ERR_INVALIDSECTOR,

/* 19 */ F_ERR_READ,

/* 20 */ F_ERR_WRITE,

/* 21 */ F_ERR_INVALIDMEDIA,

/* 22 */ F_ERR_BUSY,

/* 23 */ F_ERR_WRITEPROTECT,

/* 24 */ F_ERR_INVFATTYPE,

/* 25 */ F_ERR_MEDIATOOSMALL,

/* 26 */ F_ERR_MEDIATOOLARGE,

/* 27 */ F_ERR_NOTSUPPSECTORSIZE

/* 28 */, F_ERR_ALLOCATION

#if F_FS_THREAD_AWARE == 1
/* 29 */, F_ERR_OS = 29
#endif /* F_FS_THREAD_AWARE */
};

typedef struct
{
  unsigned long  total;
  unsigned long  free;
  unsigned long  used;
  unsigned long  bad;

  unsigned long  total_high;
  unsigned long  free_high;
  unsigned long  used_high;
  unsigned long  bad_high;
} F_SPACE;

enum
{
  F_SEEK_SET   /*Beginning of file*/
  , F_SEEK_CUR /*Current position of file pointer*/
  , F_SEEK_END /*End of file*/
};


/****************************************************************************
 *
 * for file changed events
 *
 ***************************************************************************/

#if F_FILE_CHANGED_EVENT

typedef struct
{
  unsigned char   action;
  unsigned char   flags;
  unsigned char   attr;
  unsigned short  ctime;
  unsigned short  cdate;
  unsigned long   filesize;
  char            filename[F_MAXPATH];
} ST_FILE_CHANGED;

typedef void ( *F_FILE_CHANGED_EVENTFUNC )( ST_FILE_CHANGED * fc );

extern F_FILE_CHANGED_EVENTFUNC  f_filechangedevent;

 #define f_setfilechangedevent( filechangeevent ) f_filechangedevent = filechangeevent

/* flags */

 #define FFLAGS_NONE              0x00000000

 #define FFLAGS_FILE_NAME         0x00000001
 #define FFLAGS_DIR_NAME          0x00000002
 #define FFLAGS_NAME              0x00000003
 #define FFLAGS_ATTRIBUTES        0x00000004
 #define FFLAGS_SIZE              0x00000008
 #define FFLAGS_LAST_WRITE        0x00000010

/* actions */

 #define FACTION_ADDED            0x00000001
 #define FACTION_REMOVED          0x00000002
 #define FACTION_MODIFIED         0x00000003
 #define FACTION_RENAMED_OLD_NAME 0x00000004
 #define FACTION_RENAMED_NEW_NAME 0x00000005

#endif /* if F_FILE_CHANGED_EVENT */

unsigned char fs_init ( void );
unsigned char fs_delete ( void );

#define f_initvolume fn_initvolume
#define f_delvolume  fn_delvolume

unsigned char fn_initvolume ( F_DRIVERINIT initfunc );
unsigned char fn_delvolume ( void );

unsigned char fn_getfreespace ( F_SPACE * pspace );

unsigned char fn_chdir ( const char * dirname );
unsigned char fn_mkdir ( const char * dirname );
unsigned char fn_rmdir ( const char * dirname );

unsigned char fn_findfirst ( const char * filename, F_FIND * find );
unsigned char fn_findnext ( F_FIND * find );

long fn_filelength ( const char * filename );

unsigned char fn_close ( F_FILE * filehandle );
F_FILE * fn_open ( const char * filename, const char * mode );

long fn_read ( void * buf, long size, long _size_t, F_FILE * filehandle );

long fn_write ( const void * buf, long size, long _size_t, F_FILE * filehandle );

unsigned char fn_seek ( F_FILE * filehandle, long offset, unsigned char whence );

long fn_tell ( F_FILE * filehandle );
int fn_getc ( F_FILE * filehandle );
int fn_putc ( int ch, F_FILE * filehandle );
unsigned char fn_rewind ( F_FILE * filehandle );
unsigned char fn_eof ( F_FILE * filehandle );

unsigned char fn_delete ( const char * filename );

unsigned char fn_seteof ( F_FILE * );

F_FILE * fn_truncate ( const char *, long );

unsigned char fn_getcwd ( char * buffer, unsigned char maxlen, char root );

unsigned char fn_hardformat ( unsigned char fattype );

unsigned char fn_getserial ( unsigned long * );


#if F_FS_THREAD_AWARE == 1

#include "FreeRTOS.h"
#include "semphr.h"

unsigned char fr_hardformat ( unsigned char fattype );
#define f_hardformat( fattype ) fr_hardformat( fattype )
#define f_format( fattype )    fr_hardformat( fattype )

unsigned char fr_getcwd ( char * buffer, unsigned char maxlen, char root );
#define f_getcwd( buffer, maxlen ) fr_getcwd( buffer, maxlen, 1 )

unsigned char fr_getfreespace ( F_SPACE * pspace );
#define f_getfreespace fr_getfreespace


unsigned char fr_chdir ( const char * dirname );
#define f_chdir( dirname ) fr_chdir( dirname )
unsigned char fr_mkdir ( const char * dirname );
#define f_mkdir( dirname ) fr_mkdir( dirname )
unsigned char fr_rmdir ( const char * dirname );
#define f_rmdir( dirname ) fr_rmdir( dirname )

unsigned char fr_findfirst ( const char * filename, F_FIND * find );
unsigned char fr_findnext ( F_FIND * find );
#define f_findfirst( filename, find ) fr_findfirst( filename, find )
#define f_findnext( find )            fr_findnext( find )

long fr_filelength ( const char * filename );
#define f_filelength( filename ) fr_filelength( filename )

unsigned char fr_close ( F_FILE * filehandle );
F_FILE * fr_open ( const char * filename, const char * mode );

long fr_read ( void * buf, long size, long _size_t, F_FILE * filehandle );

unsigned char fr_getserial ( unsigned long * );
#define f_getserial( serial )  fr_getserial( serial )

unsigned char fr_flush ( F_FILE * f );
#define f_flush( filehandle ) fr_flush( filehandle )

long fr_write ( const void * buf, long size, long _size_t, F_FILE * filehandle );
#define f_write( buf, size, _size_t, filehandle ) fr_write( buf, size, _size_t, filehandle )

unsigned char fr_seek ( F_FILE * filehandle, long offset, unsigned char whence );
#define f_seek( filehandle, offset, whence ) fr_seek( filehandle, offset, whence )

long fr_tell ( F_FILE * filehandle );
#define f_tell( filehandle )     fr_tell( filehandle )
int fr_getc ( F_FILE * filehandle );
#define f_getc( filehandle )     fr_getc( filehandle )
int fr_putc ( int ch, F_FILE * filehandle );
#define f_putc( ch, filehandle ) fr_putc( ch, filehandle )
unsigned char fr_rewind ( F_FILE * filehandle );
#define f_rewind( filehandle )   fr_rewind( filehandle )
unsigned char fr_eof ( F_FILE * filehandle );
#define f_eof( filehandle )      fr_eof( filehandle )

unsigned char fr_delete ( const char * filename );
#define f_delete( filename ) fr_delete( filename )

unsigned char fr_seteof ( F_FILE * );
#define f_seteof( file ) fr_seteof( file )

F_FILE * fr_truncate ( const char *, long );
#define f_truncate( filename, filesize ) fr_truncate( filename, filesize )

#define f_close( filehandle )                    fr_close( filehandle )
#define f_open( filename, mode )                 fr_open( filename, mode )
#define f_read( buf, size, _size_t, filehandle ) fr_read( buf, size, _size_t, filehandle )

#else /* F_FS_THREAD_AWARE */

#define f_hardformat( fattype ) fn_hardformat( fattype )
#define f_format( fattype )    fn_hardformat( fattype )

#define f_getcwd( buffer, maxlen ) fn_getcwd( buffer, maxlen, 1 )

unsigned char fn_getfreespace ( F_SPACE * pspace );
#define f_getfreespace fn_getfreespace


unsigned char fn_chdir ( const char * dirname );
#define f_chdir( dirname ) fn_chdir( dirname )
unsigned char fn_mkdir ( const char * dirname );
#define f_mkdir( dirname ) fn_mkdir( dirname )
unsigned char fn_rmdir ( const char * dirname );
#define f_rmdir( dirname ) fn_rmdir( dirname )

unsigned char fn_findfirst ( const char * filename, F_FIND * find );
unsigned char fn_findnext ( F_FIND * find );
#define f_findfirst( filename, find ) fn_findfirst( filename, find )
#define f_findnext( find )            fn_findnext( find )

#define f_filelength( filename ) fn_filelength( filename )

#define f_getserial( serial )  fn_getserial( serial )

unsigned char fn_flush ( F_FILE * f );
#define f_flush( filehandle ) fn_flush( filehandle )

#define f_write( buf, size, _size_t, filehandle ) fn_write( buf, size, _size_t, filehandle )

#define f_seek( filehandle, offset, whence ) fn_seek( filehandle, offset, whence )

long fn_tell ( F_FILE * filehandle );
#define f_tell( filehandle )     fn_tell( filehandle )
int fn_getc ( F_FILE * filehandle );
#define f_getc( filehandle )     fn_getc( filehandle )
int fn_putc ( int ch, F_FILE * filehandle );
#define f_putc( ch, filehandle ) fn_putc( ch, filehandle )
unsigned char fn_rewind ( F_FILE * filehandle );
#define f_rewind( filehandle )   fn_rewind( filehandle )
unsigned char fn_eof ( F_FILE * filehandle );
#define f_eof( filehandle )      fn_eof( filehandle )

unsigned char fn_delete ( const char * filename );
#define f_delete( filename ) fn_delete( filename )

unsigned char fn_seteof ( F_FILE * );
#define f_seteof( file ) fn_seteof( file )

F_FILE * fn_truncate ( const char *, long );
#define f_truncate( filename, filesize ) fn_truncate( filename, filesize )

#define f_close( filehandle )                    fn_close( filehandle )
#define f_open( filename, mode )                 fn_open( filename, mode )
#define f_read( buf, size, _size_t, filehandle ) fn_read( buf, size, _size_t, filehandle )

#endif /* F_FS_THREAD_AWARE */


/****************************************************************************
 *
 * end of fat_sl.h
 *
 ***************************************************************************/
#ifdef __cplusplus
}
#endif

#endif /*_API_FAT_SL_H_*/

