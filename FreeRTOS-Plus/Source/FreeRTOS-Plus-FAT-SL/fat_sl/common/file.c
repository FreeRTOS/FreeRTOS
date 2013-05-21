/*
 * FreeRTOS+FAT FS V1.0.0 (C) 2013 HCC Embedded
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

#include "../../api/fat_sl.h"
#include "../../psp/include/psp_string.h"

#include "util.h"
#include "volume.h"
#include "drv.h"
#include "fat.h"
#include "dir.h"
#include "file.h"

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

static unsigned char _f_emptywritebuffer ( void );


/****************************************************************************
 *
 * fn_filelength
 *
 * Get a file length
 *
 * INPUTS
 *
 * filename - file whose length is needed
 *
 * RETURNS
 *
 * length of the file
 *
 ***************************************************************************/

long fn_filelength ( const char * filename )
{
  F_POS        pos;
  F_DIRENTRY * de;
  F_NAME       fsname;

  if ( _f_setfsname( filename, &fsname ) )
  {
    return 0;                                     /*invalid name*/
  }

  if ( _f_checknamewc( fsname.filename, fsname.fileext ) )
  {
    return 0;                                                    /*invalid name*/
  }

  if ( _f_getvolume() )
  {
    return 0;                     /*can't get the size*/
  }

  if ( !_f_findpath( &fsname, &pos ) )
  {
    return 0;
  }

  if ( !_f_findfilewc( fsname.filename, fsname.fileext, &pos, &de, 0 ) )
  {
    return 0;
  }

  if ( de->attr & F_ATTR_DIR )
  {
    return 0;                                           /*directory*/
  }

  return (long)_f_getlong( &de->filesize );
} /* fn_filelength */





/****************************************************************************
 *
 * _f_emptywritebuffer
 *
 * empty write buffer if it contains unwritten data
 *
 * RETURNS
 * error code or zero if successful
 *
 ***************************************************************************/


static unsigned char _f_emptywritebuffer ( void )
{
  unsigned char  ret;

  ret = _f_writeglsector( gl_file.pos.sector );
  if ( ret )
  {
    return ret;
  }

  gl_file.modified = 0;

  gl_file.pos.sector++;

  if ( gl_file.pos.sector >= gl_file.pos.sectorend )
  {
    unsigned long  value;

    gl_volume.fatsector = (unsigned long)-1;
    ret = _f_getclustervalue( gl_file.pos.cluster, &value );
    if ( ret )
    {
      return ret;
    }

    if ( ( value >= 2 ) && ( value < F_CLUSTER_RESERVED ) ) /*we are in chain*/
    {
      gl_file.prevcluster = gl_file.pos.cluster;
      _f_clustertopos( value, &gl_file.pos );    /*go to next cluster*/
    }
    else
    {
      unsigned long  nextcluster;

      ret = _f_alloccluster( &nextcluster );
      if ( ret )
      {
        return ret;
      }

      ret = _f_setclustervalue( nextcluster, F_CLUSTER_LAST );
      if ( ret )
      {
        return ret;
      }

      ret = _f_setclustervalue( gl_file.pos.cluster, nextcluster );
      if ( ret )
      {
        return ret;
      }

      gl_file.prevcluster = gl_file.pos.cluster;

      _f_clustertopos( nextcluster, &gl_file.pos );

      return _f_writefatsector();
    }
  }


  return F_NO_ERROR;
} /* _f_emptywritebuffer */




/****************************************************************************
 *
 * _f_extend
 *
 * Extend file to a certain size
 *
 ***************************************************************************/
static unsigned char _f_extend ( long size )
{
  unsigned long  _size;
  unsigned char  rc;

  size -= gl_file.filesize;
  _size = (unsigned long)size;

  rc = _f_getcurrsector();
  if ( rc )
  {
    return rc;
  }

  psp_memset( gl_sector + gl_file.relpos, 0, ( F_SECTOR_SIZE - gl_file.relpos ) );

  if ( gl_file.relpos + _size > F_SECTOR_SIZE )
  {
    _size -= ( F_SECTOR_SIZE - gl_file.relpos );
    while ( _size )
    {
      if ( _f_emptywritebuffer() )
      {
        return F_ERR_WRITE;
      }

      psp_memset( gl_sector, 0, F_SECTOR_SIZE );
      _size -= ( _size > F_SECTOR_SIZE ? F_SECTOR_SIZE : _size );
    }
  }
  else
  {
    _size += gl_file.relpos;
  }

  gl_file.modified = 1;
  gl_file.filesize += size;
  gl_file.abspos = gl_file.filesize & ( ~( F_SECTOR_SIZE - 1 ) );
  gl_file.relpos = _size;

  return F_NO_ERROR;
} /* _f_extend */



/****************************************************************************
 *
 * _f_fseek
 *
 * subfunction for f_seek it moves position into given offset and read
 * the current sector
 *
 * INPUTS
 * offset - position from start
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
static unsigned char _f_fseek ( long offset )
{
  unsigned long  cluster;
  unsigned long  tmp;
  unsigned char  ret = F_NO_ERROR;
  long           remain;

  if ( offset < 0 )
  {
    offset = 0;
  }

  if ( ( (unsigned long) offset <= gl_file.filesize )
       && ( (unsigned long) offset >= gl_file.abspos )
       && ( (unsigned long) offset < gl_file.abspos + F_SECTOR_SIZE ) )
  {
    gl_file.relpos = (unsigned short)( offset - gl_file.abspos );
  }
  else
  {
    if ( gl_file.modified )
    {
      ret = _f_writeglsector( (unsigned long)-1 );
      if ( ret )
      {
        gl_file.mode = F_FILE_CLOSE; /*cant accessed any more*/
        return ret;
      }
    }

    if ( gl_file.startcluster )
    {
      gl_file.abspos = 0;
      gl_file.relpos = 0;
      gl_file.prevcluster = 0;
      gl_file.pos.cluster = gl_file.startcluster;
      remain = gl_file.filesize;

      tmp = gl_volume.bootrecord.sector_per_cluster;
      tmp *= F_SECTOR_SIZE;   /* set to cluster size */

      /*calc cluster*/
      gl_volume.fatsector = (unsigned long)-1;
      while ( (unsigned long)offset >= tmp )
      {
        ret = _f_getclustervalue( gl_file.pos.cluster, &cluster );
        if ( ret )
        {
          gl_file.mode = F_FILE_CLOSE;
          return ret;
        }

        if ( (long) tmp >= remain )
        {
          break;
        }

        remain -= tmp;
        offset -= tmp;
        gl_file.abspos += tmp;
        if ( cluster >= F_CLUSTER_RESERVED )
        {
          break;
        }

        gl_file.prevcluster = gl_file.pos.cluster;
        gl_file.pos.cluster = cluster;
      }

      _f_clustertopos( gl_file.pos.cluster, &gl_file.pos );
      if ( remain && offset )
      {
        while ( ( offset > (long) F_SECTOR_SIZE )
               && ( remain > (long) F_SECTOR_SIZE ) )
        {
          gl_file.pos.sector++;
          offset -= F_SECTOR_SIZE;
          remain -= F_SECTOR_SIZE;
          gl_file.abspos += F_SECTOR_SIZE;
        }
      }

      if ( remain < offset )
      {
        gl_file.relpos = (unsigned short)remain;
        ret = _f_extend( gl_file.filesize + offset - remain );
      }
      else
      {
        gl_file.relpos = (unsigned short)offset;
      }
    }
  }

  return ret;
} /* _f_fseek */



/****************************************************************************
 *
 * fn_open
 *
 * open a file for reading/writing/appending
 *
 * INPUTS
 *
 * filename - which file need to be opened
 * mode - string how to open ("r"-read, "w"-write, "w+"-overwrite, "a"-append
 *
 * RETURNS
 *
 * F_FILE pointer if successfully
 * 0 - if any error
 *
 ***************************************************************************/
F_FILE * fn_open ( const char * filename, const char * mode )
{
  F_DIRENTRY    * de;
  F_NAME          fsname;
  unsigned short  date;
  unsigned short  time;
  unsigned char   m_mode = F_FILE_CLOSE;

  if ( mode[1] == 0 )
  {
    if ( mode[0] == 'r' )
    {
      m_mode = F_FILE_RD;
    }

    if ( mode[0] == 'w' )
    {
      m_mode = F_FILE_WR;
    }

    if ( mode[0] == 'a' )
    {
      m_mode = F_FILE_A;
    }
  }

  if ( ( mode[1] == '+' ) && ( mode[2] == 0 ) )
  {
    if ( mode[0] == 'r' )
    {
      m_mode = F_FILE_RDP;
    }

    if ( mode[0] == 'w' )
    {
      m_mode = F_FILE_WRP;
    }

    if ( mode[0] == 'a' )
    {
      m_mode = F_FILE_AP;
    }

  }

  if ( m_mode == F_FILE_CLOSE )
  {
    return 0;                                       /*invalid mode*/
  }

  if ( _f_setfsname( filename, &fsname ) )
  {
    return 0;                                     /*invalid name*/
  }

  if ( _f_checknamewc( fsname.filename, fsname.fileext ) )
  {
    return 0;                                                    /*invalid name*/
  }

  if ( fsname.filename[0] == '.' )
  {
    return 0;
  }

  if ( _f_getvolume() )
  {
    return 0;                     /*cant open any*/
  }

  if ( gl_file.mode != F_FILE_CLOSE )
  {
    return 0;
  }

  psp_memset( &gl_file, 0, 21 );

  if ( !_f_findpath( &fsname, &gl_file.dirpos ) )
  {
    return 0;
  }

  switch ( m_mode )
  {
    case F_FILE_RDP:   /*r*/
    case F_FILE_RD:   /*r*/
      if ( !_f_findfilewc( fsname.filename, fsname.fileext, &gl_file.dirpos, &de, 0 ) )
      {
        return 0;
      }

      if ( de->attr & F_ATTR_DIR )
      {
        return 0;                                      /*directory*/
      }

      gl_file.startcluster = _f_getdecluster( de );

      if ( gl_file.startcluster )
      {
        _f_clustertopos( gl_file.startcluster, &gl_file.pos );
        gl_file.filesize = _f_getlong( &de->filesize );
        gl_file.abspos = (unsigned long) (-1 * (long) F_SECTOR_SIZE);
        if ( _f_fseek( 0 ) )
        {
          return 0;
        }
      }

#if F_FILE_CHANGED_EVENT
      if ( m_mode == F_FILE_RDP )
      {
        _f_createfullname( gl_file.filename, sizeof( gl_file.filename ), fsname.path, fsname.filename, fsname.fileext );
      }

#endif

      break;

    case F_FILE_AP:
    case F_FILE_A: /*a*/
      psp_memcpy( &( gl_file.pos ), &( gl_file.dirpos ), sizeof( F_POS ) );
      if ( _f_findfilewc( fsname.filename, fsname.fileext, &gl_file.dirpos, &de, 0 ) )
      {
        if ( de->attr & ( F_ATTR_DIR | F_ATTR_READONLY ) )
        {
          return 0;
        }

        gl_file.startcluster = _f_getdecluster( de );
        gl_file.filesize = _f_getlong( &de->filesize );

        if ( gl_file.startcluster )
        {
          _f_clustertopos( gl_file.startcluster, &gl_file.pos );
          gl_file.abspos = (unsigned long) (-1 * (long) F_SECTOR_SIZE);   /*forcing seek to read 1st sector! abspos=0;*/
          if ( _f_fseek( (long)gl_file.filesize ) )
          {
            gl_file.mode = F_FILE_CLOSE;
            return 0;
          }
        }
      }
      else
      {
        psp_memcpy( &( gl_file.dirpos ), &( gl_file.pos ), sizeof( F_POS ) );
        _f_clustertopos( gl_file.dirpos.cluster, &gl_file.pos );

        if ( _f_addentry( &fsname, &gl_file.dirpos, &de ) )
        {
          return 0;                                                  /*couldnt be added*/
        }

        de->attr |= F_ATTR_ARC;         /*set as archiv*/
        if ( _f_writeglsector( (unsigned long)-1 ) )
        {
          return 0;
        }
      }

 #if F_FILE_CHANGED_EVENT
      _f_createfullname( gl_file.filename, sizeof( gl_file.filename ), fsname.path, fsname.filename, fsname.fileext );
 #endif
      break;


    case F_FILE_WR:  /*w*/
    case F_FILE_WRP: /*w+*/
      _f_clustertopos( gl_file.dirpos.cluster, &gl_file.pos );
      if ( _f_findfilewc( fsname.filename, fsname.fileext, &gl_file.pos, &de, 0 ) )
      {
        unsigned long  cluster = _f_getdecluster( de );    /*exist*/

        if ( de->attr & ( F_ATTR_DIR | F_ATTR_READONLY ) )
        {
          return 0;
        }

        psp_memcpy( &( gl_file.dirpos ), &( gl_file.pos ), sizeof( F_POS ) );

        _f_setlong( de->filesize, 0 );  /*reset size;*/
        de->attr |= F_ATTR_ARC;         /*set as archiv*/
        _f_setword( de->clusterlo, 0 ); /*no points anywhere*/
        _f_setword( de->clusterhi, 0 );

        if ( gl_volume.mediatype == F_FAT32_MEDIA )
        {
          f_igettimedate( &time, &date );
          _f_setword( &de->crtdate, date );        /*if there is realtime clock then creation date could be set from*/
          _f_setword( &de->crttime, time );        /*if there is realtime clock then creation time could be set from*/
          _f_setword( &de->lastaccessdate, date ); /*if there is realtime clock then creation date could be set from*/
        }

        if ( _f_writeglsector( (unsigned long)-1 ) )
        {
          return 0;
        }

        if ( _f_removechain( cluster ) )
        {
          return 0;                                /*remove */
        }
      }
      else
      {
        if ( _f_addentry( &fsname, &gl_file.dirpos, &de ) )
        {
          return 0;                                                  /*couldnt be added*/
        }

        psp_memset( &gl_file, 0, 21 );
        de->attr |= F_ATTR_ARC;         /*set as archiv*/
        if ( _f_writeglsector( (unsigned long)-1 ) )
        {
          return 0;
        }
      }

 #if F_FILE_CHANGED_EVENT
      _f_createfullname( gl_file.filename, sizeof( gl_file.filename ), fsname.path, fsname.filename, fsname.fileext );
 #endif

      break;

    default:
      return 0;        /*invalid mode*/
  } /* switch */

  if ( ( m_mode != F_FILE_RD ) && ( gl_file.startcluster == 0 ) )
  {
    gl_volume.fatsector = (unsigned long)-1;
    if ( _f_alloccluster( &( gl_file.startcluster ) ) )
    {
      return 0;
    }

    _f_clustertopos( gl_file.startcluster, &gl_file.pos );
    if ( _f_setclustervalue( gl_file.startcluster, F_CLUSTER_LAST ) )
    {
      return 0;
    }

    if ( _f_writefatsector() )
    {
      return 0;
    }
  }


  gl_file.mode = m_mode; /* lock it */
  return (F_FILE *)1;
} /* fn_open */


/****************************************************************************
 * _f_updatefileentry
 * Updated a file directory entry or removes the entry
 * and the fat chain belonging to it.
 ***************************************************************************/
static unsigned char _f_updatefileentry ( int remove )
{
  F_DIRENTRY    * de;
  unsigned short  date;
  unsigned short  time;

  de = (F_DIRENTRY *)( gl_sector + sizeof( F_DIRENTRY ) * gl_file.dirpos.pos );
  if ( _f_readglsector( gl_file.dirpos.sector ) || remove )
  {
    _f_setdecluster( de, 0 );
    _f_setlong( &de->filesize, 0 );
    (void)_f_writeglsector( (unsigned long)-1 );
    (void)_f_removechain( gl_file.startcluster );
    return F_ERR_WRITE;
  }

  _f_setdecluster( de, gl_file.startcluster );
  _f_setlong( &de->filesize, gl_file.filesize );
  f_igettimedate( &time, &date );
  _f_setword( &de->cdate, date );  /*if there is realtime clock then creation date could be set from*/
  _f_setword( &de->ctime, time );  /*if there is realtime clock then creation time could be set from*/
  if ( gl_volume.mediatype == F_FAT32_MEDIA )
  {
    _f_setword( &de->lastaccessdate, date );  /*if there is realtime clock then creation date could be set from*/
  }

  return _f_writeglsector( (unsigned long)-1 );
} /* _f_updatefileentry */


/****************************************************************************
 *
 * fn_close
 *
 * close a previously opened file
 *
 * INPUTS
 *
 * filehandle - which file needs to be closed
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
unsigned char fn_close ( F_FILE * f )
{
  unsigned char  ret;

#if F_FILE_CHANGED_EVENT
  unsigned char  mode;
#endif

  if ( !f )
  {
    return F_ERR_NOTOPEN;
  }

  ret = _f_getvolume();
  if ( ret )
  {
    return ret;
  }

  if ( gl_file.mode == F_FILE_CLOSE )
  {
    return F_ERR_NOTOPEN;
  }

  else if ( gl_file.mode == F_FILE_RD )
  {
    gl_file.mode = F_FILE_CLOSE;
    return F_NO_ERROR;
  }
  else
  {
 #if F_FILE_CHANGED_EVENT
    mode = f->mode;
 #endif
    gl_file.mode = F_FILE_CLOSE;

    if ( gl_file.modified )
    {
      if ( _f_writeglsector( (unsigned long)-1 ) )
      {
        (void)_f_updatefileentry( 1 );
        return F_ERR_WRITE;
      }
    }

    ret = _f_updatefileentry( 0 );

 #if F_FILE_CHANGED_EVENT
    if ( f_filechangedevent && !ret )
    {
      ST_FILE_CHANGED  fc;
      if ( ( mode == F_FILE_WR )  || ( mode == F_FILE_WRP ) )
      {
        fc.action = FACTION_ADDED;
        fc.flags  = FFLAGS_FILE_NAME;
      }
      else if ( ( mode == F_FILE_A )  || ( mode == F_FILE_RDP ) )
      {
        fc.action = FACTION_MODIFIED;
        fc.flags  = FFLAGS_FILE_NAME | FFLAGS_SIZE;
      }

      strcpy( fc.filename, f->filename );
      if ( f->filename[0] )
      {
        f_filechangedevent( &fc );
      }

      f->filename[0] = '\0';
    }

 #endif /* if F_FILE_CHANGED_EVENT */
    return ret;
  }
} /* fn_close */


/****************************************************************************
 *
 * fn_flush
 *
 * flush a previously opened file
 *
 * INPUTS
 *
 * filehandle - which file needs to be closed
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
unsigned char fn_flush ( F_FILE * f )
{
  unsigned char  ret;

  if ( !f )
  {
    return F_ERR_NOTOPEN;
  }

  ret = _f_getvolume();
  if ( ret )
  {
    return ret;
  }

  if ( gl_file.mode == F_FILE_CLOSE )
  {
    return F_ERR_NOTOPEN;
  }
  else if ( gl_file.mode != F_FILE_RD )
  {
    if ( gl_file.modified )
    {
      if ( _f_writeglsector( (unsigned long)-1 ) )
      {
        (void)_f_updatefileentry( 1 );
        return F_ERR_WRITE;
      }
    }

    return _f_updatefileentry( 0 );
  }

  return F_NO_ERROR;
} /* fn_flush */


/****************************************************************************
 *
 * fn_read
 *
 * read data from file
 *
 * INPUTS
 *
 * buf - where the store data
 * size - size of items to be read
 * _size_t - number of items need to be read
 * filehandle - file where to read from
 *
 * RETURNS
 *
 * with the number of read bytes
 *
 ***************************************************************************/
long fn_read ( void * buf, long size, long _size_st, F_FILE * f )
{
  char * buffer = (char *)buf;
  long   retsize;

  if ( !f )
  {
    return 0;
  }

  if ( ( gl_file.mode & ( F_FILE_RD | F_FILE_RDP | F_FILE_WRP | F_FILE_AP ) ) == 0 )
  {
    return 0;
  }

  retsize = size;
  size *= _size_st;
  _size_st = retsize;
  retsize = 0;

  if ( _f_getvolume() )
  {
    return 0;                     /*cant read any*/
  }

  if ( size + gl_file.relpos + gl_file.abspos >= gl_file.filesize ) /*read len longer than the file*/
  {
    size = (long)( ( gl_file.filesize ) - ( gl_file.relpos ) - ( gl_file.abspos ) ); /*calculate new size*/
  }

  if ( size <= 0 )
  {
    return 0;
  }

  if ( _f_getcurrsector() )
  {
    gl_file.mode = F_FILE_CLOSE; /*no more read allowed*/
    return 0;
  }

  for( ; ; )
  {
    unsigned long  rdsize = (unsigned long)size;

    if ( gl_file.relpos == F_SECTOR_SIZE )
    {
      unsigned char  ret;

      gl_file.abspos += gl_file.relpos;
      gl_file.relpos = 0;

      if ( gl_file.modified )
      {
        ret = _f_writeglsector( (unsigned long)-1 );     /*empty write buffer */
        if ( ret )
        {
          gl_file.mode = F_FILE_CLOSE;         /*no more read allowed*/
          return retsize;
        }
      }

      gl_file.pos.sector++;         /*goto next*/

      ret = _f_getcurrsector();
      if ( ( ret == F_ERR_EOF ) && ( !size ) )
      {
        return retsize;
      }

      if ( ret )
      {
        gl_file.mode = F_FILE_CLOSE;       /*no more read allowed*/
        return retsize;
      }
    }

    if ( !size )
    {
      break;
    }

    if ( rdsize >= F_SECTOR_SIZE - gl_file.relpos )
    {
      rdsize = (unsigned long)( F_SECTOR_SIZE - gl_file.relpos );
    }

    psp_memcpy( buffer, gl_sector + gl_file.relpos, rdsize ); /*always less than 512*/

    buffer += rdsize;
    gl_file.relpos += rdsize;
    size -= rdsize;
    retsize += rdsize;
  }

  return retsize / _size_st;
} /* fn_read */


/****************************************************************************
 *
 * fn_write
 *
 * write data into file
 *
 * INPUTS
 *
 * buf - where the store data
 * size - size of items to be read
 * size_t - number of items need to be read
 * filehandle - file where to read from
 *
 * RETURNS
 *
 * with the number of read bytes
 *
 ***************************************************************************/

long fn_write ( const void * buf, long size, long _size_st, F_FILE * f )
{
  char * buffer = (char *)buf;
  long   retsize;
  long   ret = 0;

  if ( !f )
  {
    return 0;
  }

  if ( ( gl_file.mode & ( F_FILE_WR | F_FILE_A | F_FILE_RDP | F_FILE_WRP | F_FILE_AP ) ) == 0 )
  {
    return 0;
  }

  retsize = size;
  size *= _size_st;
  _size_st = retsize;
  retsize = 0;

  if ( _f_getvolume() )
  {
    return 0;                     /*can't write*/
  }

  if ( ( gl_file.mode ) & ( F_FILE_A | F_FILE_AP ) )
  {
    if ( _f_fseek( (long)gl_file.filesize ) )
    {
      gl_file.mode = F_FILE_CLOSE;
      return 0;
    }
  }

  if ( _f_getcurrsector() )
  {
    gl_file.mode = F_FILE_CLOSE;
    return 0;
  }

  for( ; ; )
  {
    unsigned long  wrsize = (unsigned long)size;

    if ( gl_file.relpos == F_SECTOR_SIZE )
    {     /*now full*/
      if ( gl_file.modified )
      {
        if ( _f_emptywritebuffer() )
        {
          gl_file.mode = F_FILE_CLOSE;
          if ( _f_updatefileentry( 0 ) == 0 )
          {
            return retsize;
          }
          else
          {
            return 0;
          }
        }
      }
      else
      {
        gl_file.pos.sector++;       /*goto next*/
      }

      gl_file.abspos += gl_file.relpos;
      gl_file.relpos = 0;

      if ( wrsize && ( wrsize < F_SECTOR_SIZE ) )
      {
        ret = _f_getcurrsector();

        if ( ret )
        {
          if ( ret != F_ERR_EOF )
          {
            gl_file.mode = F_FILE_CLOSE;       /*no more read allowed*/
            return retsize;
          }
        }
      }
    }

    if ( !size )
    {
      break;
    }

    if ( wrsize >= F_SECTOR_SIZE - gl_file.relpos )
    {
      wrsize = (unsigned long)( F_SECTOR_SIZE - gl_file.relpos );
    }


    psp_memcpy( gl_sector + gl_file.relpos, buffer, wrsize );
    gl_file.modified = 1;    /*sector is modified*/

    buffer += wrsize;
    gl_file.relpos += wrsize;
    size -= wrsize;
    retsize += wrsize;

    if ( gl_file.filesize < gl_file.abspos + gl_file.relpos )
    {
      gl_file.filesize = gl_file.abspos + gl_file.relpos;
    }
  }

  return retsize / _size_st;
} /* fn_write */



/****************************************************************************
 *
 * fn_seek
 *
 * moves position into given offset in given file
 *
 * INPUTS
 *
 * filehandle - F_FILE structure which file position needed to be modified
 * offset - relative position
 * whence - where to calculate position (F_SEEK_SET,F_SEEK_CUR,F_SEEK_END)
 *
 * RETURNS
 *
 * 0 - if successfully
 * other - if any error
 *
 ***************************************************************************/


unsigned char fn_seek ( F_FILE * f, long offset, unsigned char whence )
{
  unsigned char  ret;

  if ( !f )
  {
    return F_ERR_NOTOPEN;
  }

  if ( ( gl_file.mode & ( F_FILE_RD | F_FILE_WR | F_FILE_A | F_FILE_RDP | F_FILE_WRP | F_FILE_AP ) ) == 0 )
  {
    return F_ERR_NOTOPEN;
  }

  ret = _f_getvolume();
  if ( ret )
  {
    return ret;
  }

  if ( whence == F_SEEK_CUR )
  {
    return _f_fseek( (long)( gl_file.abspos + gl_file.relpos + offset ) );
  }
  else if ( whence == F_SEEK_END )
  {
    return _f_fseek( (long)( gl_file.filesize + offset ) );
  }
  else if ( whence == F_SEEK_SET )
  {
    return _f_fseek( offset );
  }

  return F_ERR_NOTUSEABLE;
} /* fn_seek */



/****************************************************************************
 *
 * fn_tell
 *
 * Tells the current position of opened file
 *
 * INPUTS
 *
 * filehandle - which file needs the position
 *
 * RETURNS
 *
 * position in the file from start
 *
 ***************************************************************************/

long fn_tell ( F_FILE * f )
{
  if ( !f )
  {
    return 0;
  }

  if ( ( gl_file.mode & ( F_FILE_RD | F_FILE_WR | F_FILE_A | F_FILE_RDP | F_FILE_WRP | F_FILE_AP ) ) == 0 )
  {
    return 0;
  }

  return (long)( gl_file.abspos + gl_file.relpos );
}



/****************************************************************************
 *
 * fn_eof
 *
 * Tells if the current position is end of file or not
 *
 * INPUTS
 *
 * filehandle - which file needs the checking
 *
 * RETURNS
 *
 * 0 - if not EOF
 * other - if EOF or invalid file handle
 *
 ***************************************************************************/

unsigned char fn_eof ( F_FILE * f )
{
  if ( !f )
  {
    return F_ERR_NOTOPEN;          /*if error*/
  }

  if ( gl_file.abspos + gl_file.relpos < gl_file.filesize )
  {
    return 0;
  }

  return F_ERR_EOF;  /*EOF*/
}




/****************************************************************************
 *
 * fn_rewind
 *
 * set the fileposition in the opened file to the begining
 *
 * INPUTS
 *
 * filehandle - which file needs to be rewinded
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/

unsigned char fn_rewind ( F_FILE * filehandle )
{
  return fn_seek( filehandle, 0L, F_SEEK_SET );
}



/****************************************************************************
 *
 * fn_putc
 *
 * write a character into file
 *
 * INPUTS
 *
 * ch - what to write into file
 * filehandle - file where to write
 *
 * RETURNS
 *
 * with the number of written bytes (1-success, 0-not successfully)
 *
 ***************************************************************************/

int fn_putc ( int ch, F_FILE * filehandle )
{
  unsigned char  tmpch = (unsigned char)ch;

  if ( fn_write( &tmpch, 1, 1, filehandle ) )
  {
    return ch;
  }
  else
  {
    return -1;
  }
}



/****************************************************************************
 *
 * fn_getc
 *
 * get a character from file
 *
 * INPUTS
 *
 * filehandle - file where to read from
 *
 * RETURNS
 *
 * with the read character or -1 if read was not successfully
 *
 ***************************************************************************/
int fn_getc ( F_FILE * filehandle )
{
  unsigned char  ch;

  if ( !fn_read( &ch, 1, 1, filehandle ) )
  {
    return -1;
  }

  return (int)ch;
}



/****************************************************************************
 *
 * fn_delete
 *
 * delete a file
 *
 * INPUTS
 *
 * filename - file which wanted to be deleted (with or without path)
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
unsigned char fn_delete ( const char * filename )
{
  F_POS          pos;
  F_DIRENTRY   * de;
  F_NAME         fsname;
  unsigned char  ret;

  if ( _f_setfsname( filename, &fsname ) )
  {
    return F_ERR_INVALIDNAME;                                     /*invalid name*/
  }

  if ( _f_checknamewc( fsname.filename, fsname.fileext ) )
  {
    return F_ERR_INVALIDNAME;                                                    /*invalid name*/
  }

  if ( fsname.filename[0] == '.' )
  {
    return F_ERR_NOTFOUND;
  }

  ret = _f_getvolume();
  if ( ret )
  {
    return ret;
  }

  if ( !( _f_findpath( &fsname, &pos ) ) )
  {
    return F_ERR_INVALIDDIR;
  }

  if ( !_f_findfilewc( fsname.filename, fsname.fileext, &pos, &de, 0 ) )
  {
    return F_ERR_NOTFOUND;
  }

  if ( de->attr & F_ATTR_DIR )
  {
    return F_ERR_INVALIDDIR;                                /*directory*/
  }

  if ( de->attr & F_ATTR_READONLY )
  {
    return F_ERR_ACCESSDENIED;                                      /*readonly*/
  }

  if ( ( gl_file.mode != F_FILE_CLOSE ) && ( gl_file.dirpos.sector == pos.sector ) && ( gl_file.dirpos.pos == pos.pos ) )
  {
    return F_ERR_LOCKED;
  }

  de->name[0] = (unsigned char)0xe5; /*removes it*/
  ret = _f_writeglsector( (unsigned long)-1 );
  if ( ret )
  {
    return ret;
  }

  ret = _f_removechain( _f_getdecluster( de ) );

 #if F_FILE_CHANGED_EVENT
  if ( f_filechangedevent && !ret )
  {
    ST_FILE_CHANGED  fc;
    fc.action = FACTION_REMOVED;
    fc.flags = FFLAGS_FILE_NAME;

    if ( !_f_createfullname( fc.filename, sizeof( fc.filename ), fsname.path, fsname.filename, fsname.fileext ) )
    {
      f_filechangedevent( &fc );
    }
  }

 #endif

  return ret;
} /* fn_delete */




/****************************************************************************
 *
 * _f_seteof
 *
 * Set end of file
 *
 * INPUT:	f - file pointer
 *		filesize - required new size
 * RETURN:	F_NO_ERROR - on success
 *		other if error
 *
 ***************************************************************************/
unsigned char _f_seteof ( F_FILE * f, long filesize )
{
  unsigned char  rc = F_NO_ERROR;

  if ( !f )
  {
    return F_ERR_NOTOPEN;        /*if error*/
  }

  if ( ( unsigned long) filesize < gl_file.filesize )
  {
    rc = _f_fseek( filesize );
    if ( rc == F_NO_ERROR )
    {
      unsigned long  cluster;
      rc = _f_getclustervalue( gl_file.pos.cluster, &cluster );
      if ( rc == F_NO_ERROR )
      {
        if ( cluster != F_CLUSTER_LAST )
        {
          rc = _f_removechain( cluster );
          if ( rc )
          {
            return rc;
          }

          rc = _f_setclustervalue( gl_file.pos.cluster, F_CLUSTER_LAST );
          if ( rc )
          {
            return rc;
          }

          rc = _f_writefatsector();
          if ( rc )
          {
            return rc;
          }
        }

        gl_file.filesize = (unsigned long)filesize;
      }
    }
  }
  else if ( (unsigned long) filesize > gl_file.filesize )
  {
    rc = _f_fseek( filesize );
  }

  return rc;
} /* _f_seteof */


/****************************************************************************
 *
 * fn_seteof
 *
 * Set end of file
 *
 * INPUT:	f - file pointer
 *		filesize - required new size
 * RETURN:	F_NO_ERROR - on success
 *		other if error
 *
 ***************************************************************************/
unsigned char fn_seteof ( F_FILE * f )
{
  unsigned char  rc = F_NO_ERROR;

  rc = _f_seteof( f, ( gl_file.abspos + gl_file.relpos ) );

  return rc;
} /* fn_seteof */




/****************************************************************************
 *
 * fn_truncate
 *
 * Open a file and set end of file
 *
 * INPUT:	filename - name of the file
 *		filesize - required new size
 * RETURN:	NULL on error, otherwise file pointer
 *
 ***************************************************************************/
F_FILE * fn_truncate ( const char * filename, long filesize )
{
  F_FILE       * f = fn_open( filename, "r+" );
  unsigned char  rc;

  if ( f != NULL )
  {
    rc = _f_fseek( (long)gl_file.filesize );
    if ( rc == F_NO_ERROR )
    {
      rc = _f_seteof( f, filesize );
    }

    if ( rc )
    {
      fn_close( f );
      f = NULL;
    }
  }

  return f;
} /* fn_truncate */

