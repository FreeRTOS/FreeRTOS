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

#include "../../api/fat_sl.h"
#include "../../psp/include/psp_string.h"

#include "volume.h"
#include "util.h"
#include "drv.h"
#include "fat.h"
#include "dir.h"
#include "file.h"

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 5 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

#if F_FS_THREAD_AWARE == 1
  #include "f_lock.h"
#endif

F_VOLUME  gl_volume;                /* only one volume */
F_FILE    gl_file;                  /* file */
char      gl_sector[F_SECTOR_SIZE]; /* actual sector */

#if F_FILE_CHANGED_EVENT
F_FILE_CHANGED_EVENTFUNC  f_filechangedevent;
#endif


/* Defines the number of sectors per cluster on a sector number basis */
typedef struct
{
  unsigned long  max_sectors;
  unsigned char  sector_per_cluster;
} t_FAT32_CS;

static const t_FAT32_CS  FAT32_CS[] =
{
  { 0x00020000, 1 }     /* ->64MB */
  , { 0x00040000, 2 }   /* ->128MB */
  , { 0x00080000, 4 }   /* ->256MB */
  , { 0x01000000, 8 }   /* ->8GB */
  , { 0x02000000, 16 }  /* ->16GB */
  , { 0x0ffffff0, 32 }  /* -> ... */
};


/****************************************************************************
 *
 * _f_writebootrecord
 *
 * writing boot record onto a volume, it uses number of hidden sector variable
 *
 * INPUTS
 * phy - media physical descriptor
 *
 * RETURNS
 * error code or zero if successful
 *
 ***************************************************************************/
static unsigned char _f_writebootrecord ( F_PHY * phy )
{
  unsigned char   jump_code[] =
  {
    0xeb, 0x3c, 0x90
  };
  unsigned char   oem_name[] = "MSDOS5.0";
  unsigned char   executable_marker[] =
  {
    0x55, 0xaa
  };
  unsigned char * ptr = (unsigned char *)gl_sector;
  unsigned char   rs;
  unsigned short  mre;

  unsigned char   ret;
  unsigned char   _n = 0;

  if ( gl_volume.mediatype == F_FAT32_MEDIA )
  {  /*write FS_INFO*/
    unsigned char  a;

    rs = 32 + 4;
    mre = 0;

    psp_memset( ptr, 0, F_SECTOR_SIZE );

    for ( a = 0 ; a < rs ; a++ )
    {
      ret = _f_writeglsector( a ); /*erase reserved area*/
      if ( ret )
      {
        return ret;
      }
    }

    ptr = _setlong( 0x41615252, ptr ); /*signature*/
    ptr = _setcharzero( 480, ptr );    /*reserved*/
    ptr = _setlong( 0x61417272, ptr ); /*signature*/
    ptr = _setlong( 0xffffffff, ptr ); /*no last*/
    ptr = _setlong( 0xffffffff, ptr ); /*no hint*/
    ptr = _setcharzero( 12, ptr );     /*reserved*/
    ptr = _setlong( 0xaa550000, ptr ); /*trail*/


    ret = _f_writeglsector( 1 ); /*write FSINFO*/
    if ( ret )
    {
      return ret;
    }

    ret = _f_writeglsector( 1 + 6 ); /*write FSINFO*/
    if ( ret )
    {
      return ret;
    }
  }
  else
  {
    rs = 1;
    mre = 512;
  }

  ptr = (unsigned char *)gl_sector;
  ptr = _setchar( jump_code, sizeof( jump_code ), ptr );
  ptr = _setchar( oem_name, sizeof( oem_name ) - 1, ptr );
  ptr = _setword( F_SECTOR_SIZE, ptr );
  *ptr++ = gl_volume.bootrecord.sector_per_cluster;
  ptr = _setword( rs, ptr );  /* reserved sectors */
  *ptr++ = 2;                 /* number of FATs */
  ptr = _setword( mre, ptr ); /* max root entry */
  if ( phy->number_of_sectors < 0x10000 )
  {
    ptr = _setword( (unsigned short)phy->number_of_sectors, ptr );
  }
  else
  {
    ptr = _setword( 0, ptr );
  }

  *ptr++ = 0xf0;                /* media descriptor */
  ptr = _setword( (unsigned short)gl_volume.bootrecord.sector_per_FAT, ptr );
  ptr = _setword( phy->sector_per_track, ptr );
  ptr = _setword( phy->number_of_heads, ptr );
  ptr = _setlong( 0, ptr ); /* number of hidden sectors */
  if ( phy->number_of_sectors >= 0x10000 )
  {
    ptr = _setlong( phy->number_of_sectors, ptr );
  }
  else
  {
    ptr = _setlong( 0, ptr );                                       /* number of sectors */
  }

  if ( gl_volume.mediatype == F_FAT32_MEDIA )
  {
    ptr = _setlong( gl_volume.bootrecord.sector_per_FAT32, ptr );
    ptr = _setword( 0, ptr );
    ptr = _setword( 0, ptr );
    ptr = _setlong( 2, ptr );
    ptr = _setword( 1, ptr );
    ptr = _setword( 6, ptr );
    ptr = _setchar( NULL, 12, ptr );
    _n = 28;
  }


  ptr = _setword( 0, ptr ); /* logical drive num */
  *ptr++ = 0x29;            /* extended signature */
  ptr = _setlong( 0x11223344, ptr );
  ptr = _setchar( (const unsigned char *)"NO NAME    ", 11, ptr ); /* volume name */

  switch ( gl_volume.mediatype )
  {
    case F_FAT12_MEDIA:
      ptr = _setchar( (const unsigned char *)"FAT12   ", 8, ptr );
      break;

    case F_FAT16_MEDIA:
      ptr = _setchar( (const unsigned char *)"FAT16   ", 8, ptr );
      break;

    case F_FAT32_MEDIA:
      ptr = _setchar( (const unsigned char *)"FAT32   ", 8, ptr );
      break;

    default:
      return F_ERR_INVALIDMEDIA;
  } /* switch */

  ptr = _setchar( 0, 448 - _n, ptr );
  ptr = _setchar( executable_marker, sizeof( executable_marker ), ptr );

  if ( _n )
  {
    ret = _f_writeglsector( 6 );
    if ( ret )
    {
      return ret;
    }
  }


  return _f_writeglsector( 0 ); /*write bootrecord*/
} /* _f_writebootrecord */


/****************************************************************************
 *
 * _f_buildsectors
 *
 * INPUTS
 * phy - media physical descriptor
 *
 * calculate relative sector position from boot record
 *
 ***************************************************************************/
static unsigned char _f_buildsectors ( F_PHY * phy )
{
  gl_volume.mediatype = F_UNKNOWN_MEDIA;


  if ( gl_volume.bootrecord.sector_per_FAT )
  {
    gl_volume.firstfat.sector = 1;
    gl_volume.firstfat.num = gl_volume.bootrecord.sector_per_FAT;
    gl_volume.root.sector = gl_volume.firstfat.sector + ( gl_volume.firstfat.num * (unsigned long)( gl_volume.bootrecord.number_of_FATs ) );
    gl_volume.root.num = ( 512 * sizeof( F_DIRENTRY ) ) / F_SECTOR_SIZE;

    gl_volume._tdata.sector = gl_volume.root.sector + gl_volume.root.num;
    gl_volume._tdata.num = 0;  /*??*/
  }
  else
  {
    gl_volume.firstfat.sector = ( 32 + 4 );
    gl_volume.firstfat.num = gl_volume.bootrecord.sector_per_FAT32;
    gl_volume._tdata.sector = gl_volume.firstfat.sector;
    gl_volume._tdata.sector += gl_volume.firstfat.num * (unsigned long)( gl_volume.bootrecord.number_of_FATs );
    gl_volume._tdata.num = 0;  /*??*/

    {
      unsigned long  sectorcou = gl_volume.bootrecord.sector_per_cluster;
      gl_volume.root.sector = ( ( gl_volume.bootrecord.rootcluster - 2 ) * sectorcou ) + gl_volume._tdata.sector;
      gl_volume.root.num = gl_volume.bootrecord.sector_per_cluster;
    }
  }

  {
    unsigned long  maxcluster;
    maxcluster = phy->number_of_sectors;
    maxcluster -= gl_volume._tdata.sector;
    maxcluster /= gl_volume.bootrecord.sector_per_cluster;
    gl_volume.maxcluster = maxcluster;
  }

  if ( gl_volume.maxcluster < ( F_CLUSTER_RESERVED & 0xfff ) )
  {
    gl_volume.mediatype = F_FAT12_MEDIA;
  }
  else if ( gl_volume.maxcluster < ( F_CLUSTER_RESERVED & 0xffff ) )
  {
    gl_volume.mediatype = F_FAT16_MEDIA;
  }
  else
  {
    gl_volume.mediatype = F_FAT32_MEDIA;
  }

  return F_NO_ERROR;
} /* _f_buildsectors */



/****************************************************************************
 *
 * _f_prepareformat
 *
 * preparing boot record for formatting, it sets and calculates values
 *
 * INPUTS
 * phy - media physical descriptor
 * f_bootrecord - which bootrecord need to be prepare
 * number_of_hidden_sectors - where boot record starts
 * fattype - one of this definitions F_FAT12_MEDIA,F_FAT16_MEDIA,F_FAT32_MEDIA
 *
 * RETURNS
 * error code or zero if successful
 *
 ***************************************************************************/
static unsigned char _f_prepareformat ( F_PHY * phy, unsigned char fattype )
{
  if ( !phy->number_of_sectors )
  {
    return F_ERR_INVALIDSECTOR;
  }

  gl_volume.bootrecord.number_of_FATs = 2;
  gl_volume.bootrecord.media_descriptor = 0xf0;

  if ( fattype != F_FAT32_MEDIA )
  {
    unsigned long  _n;
    switch ( fattype )
    {
      case F_FAT12_MEDIA:
        _n = F_CLUSTER_RESERVED & 0xfff;
        break;

      case F_FAT16_MEDIA:
        _n = F_CLUSTER_RESERVED & 0xffff;
        break;

      default:
        return F_ERR_INVFATTYPE;
    }

    gl_volume.bootrecord.sector_per_cluster = 1;
    while ( gl_volume.bootrecord.sector_per_cluster )
    {
      if ( phy->number_of_sectors / gl_volume.bootrecord.sector_per_cluster < _n )
      {
        break;
      }

      gl_volume.bootrecord.sector_per_cluster <<= 1;
    }

    if ( !gl_volume.bootrecord.sector_per_cluster )
    {
      return F_ERR_MEDIATOOLARGE;
    }
  }

  else
  {
    unsigned char  i;
    for ( i = 0 ; i<( sizeof( FAT32_CS ) / sizeof( t_FAT32_CS ) ) - 1 && phy->number_of_sectors>FAT32_CS[i].max_sectors ; i++ )
    {
    }

    gl_volume.bootrecord.sector_per_cluster = FAT32_CS[i].sector_per_cluster;
  }

  if ( !gl_volume.bootrecord.sector_per_cluster )
  {
    return F_ERR_INVALIDMEDIA;                                               /*fat16 cannot be there*/
  }

  {
    long           secpercl = gl_volume.bootrecord.sector_per_cluster;
    long           nfat = gl_volume.bootrecord.number_of_FATs;
    unsigned long  roots;
    unsigned long  fatsec;

    roots = ( 512 * sizeof( F_DIRENTRY ) ) / F_SECTOR_SIZE;

    switch ( fattype )
    {
      case F_FAT32_MEDIA:
      {
        unsigned long  _n = (unsigned long)( 128 * secpercl + nfat );
        fatsec = ( phy->number_of_sectors - ( 32 + 4 ) + 2 * secpercl );
        fatsec += ( _n - 1 );
        fatsec /= _n;
        gl_volume.bootrecord.sector_per_FAT32 = fatsec;
        gl_volume.bootrecord.sector_per_FAT = 0;
      }
      break;

      case F_FAT16_MEDIA:
      {
        unsigned long  _n = (unsigned long)( 256 * secpercl + nfat );
        fatsec = ( phy->number_of_sectors - 1 - roots + 2 * secpercl );
        fatsec += ( _n - 1 );
        fatsec /= _n;
        gl_volume.bootrecord.sector_per_FAT = (unsigned short)( fatsec );
      }
      break;

      case F_FAT12_MEDIA:
      {
        unsigned long  _n = (unsigned long)( 1024 * secpercl + 3 * nfat );
        fatsec = ( phy->number_of_sectors - 1 - roots + 2 * secpercl );
        fatsec *= 3;
        fatsec += ( _n - 1 );
        fatsec /= _n;
        gl_volume.bootrecord.sector_per_FAT = (unsigned short)( fatsec );
      }
      break;

      default:
        return F_ERR_INVALIDMEDIA;
    } /* switch */

    return F_NO_ERROR;
  }
} /* _f_prepareformat */



/****************************************************************************
 *
 * _f_postformat
 *
 * erase fats, erase root directory, reset variables after formatting
 *
 * INPUTS
 * phy - media physical descriptor
 * fattype - one of this definitions F_FAT12_MEDIA,F_FAT16_MEDIA,F_FAT32_MEDIA
 *
 * RETURNS
 * error code or zero if successful
 *
 ***************************************************************************/
static unsigned char _f_postformat ( F_PHY * phy, unsigned char fattype )
{
  unsigned long  a;
  unsigned char  ret;

  _f_buildsectors( phy ); /*get positions*/
  if ( gl_volume.mediatype != fattype )
  {
    return F_ERR_MEDIATOOSMALL;
  }

  gl_volume.fatsector = (unsigned long)( -1 );

  {
    unsigned char * ptr = (unsigned char *)gl_sector;
    unsigned char   j = 2;
    unsigned long   i;

    psp_memset( ptr, 0, F_SECTOR_SIZE );

    switch ( gl_volume.mediatype )
    {
      case F_FAT16_MEDIA:
        j = 3;
        break;

      case F_FAT32_MEDIA:
        j = 11;
        break;
    }

    *ptr = gl_volume.bootrecord.media_descriptor;
    psp_memset( ptr + 1, 0xff, j );
    if ( gl_volume.mediatype == F_FAT32_MEDIA )
    {
      *( ptr + 8 ) = (unsigned char)( F_CLUSTER_LAST & 0xff );
    }

    (void)_f_writeglsector( gl_volume.firstfat.sector );
    (void)_f_writeglsector( gl_volume.firstfat.sector + gl_volume.firstfat.num );
    psp_memset( ptr, 0, ( j + 1 ) );

    for ( i = 1 ; i < gl_volume.firstfat.num ; i++ )
    {
      (void)_f_writeglsector( gl_volume.firstfat.sector + i );
      (void)_f_writeglsector( gl_volume.firstfat.sector + i + gl_volume.firstfat.num );
    }
  }

  for ( a = 0 ; a < gl_volume.root.num ; a++ ) /*reset root direntries*/
  {
    ret = _f_writeglsector( gl_volume.root.sector + a );
    if ( ret )
    {
      return ret;
    }
  }

  return _f_writebootrecord( phy );
} /* _f_postformat */


/****************************************************************************
 *
 * fn_hardformat
 *
 * Making a complete format on media, independently from master boot record,
 * according to media physical
 *
 * INPUTS
 * fattype - one of this definitions F_FAT12_MEDIA,F_FAT16_MEDIA,F_FAT32_MEDIA
 *
 * RETURNS
 * error code or zero if successful
 *
 ***************************************************************************/
unsigned char fn_hardformat ( unsigned char fattype )
{
  unsigned char  ret;
  int            mdrv_ret;
  F_PHY          phy;

  ret = _f_getvolume();
  if ( ret && ( ret != F_ERR_NOTFORMATTED ) )
  {
    return ret;
  }

  gl_volume.state = F_STATE_NEEDMOUNT;

  psp_memset( &phy, 0, sizeof( F_PHY ) );

  mdrv_ret = mdrv->getphy( mdrv, &phy );
  if ( mdrv_ret )
  {
    return F_ERR_ONDRIVE;
  }

  ret = _f_prepareformat( &phy, fattype ); /*no partition*/
  if ( ret )
  {
    return ret;
  }

  return _f_postformat( &phy, fattype );
} /* fn_hardformat */




/****************************************************************************
 *
 * _f_readbootrecord
 *
 * read boot record from a volume, it detects if there is MBR on the media
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
static unsigned char _f_readbootrecord ( void )
{
  unsigned char   ret;
  unsigned char * ptr = (unsigned char *)gl_sector;
  unsigned long   maxcluster, _n;
  unsigned long   first_sector = 0;

  gl_volume.mediatype = F_UNKNOWN_MEDIA;


  ret = _f_readglsector( 0 );
  if ( ret )
  {
    return ret;
  }


  if ( ( ptr[0x1fe] != 0x55 ) || ( ptr[0x1ff] != 0xaa ) )
  {
    return F_ERR_NOTFORMATTED;                                              /*??*/
  }

  if ( ( ptr[0] != 0xeb ) && ( ptr[0] != 0xe9 ) )
  {
    first_sector = _f_getlong( &ptr[0x08 + 0x1be] ); /*start sector for 1st partioon*/

    ret = _f_readglsector( first_sector );
    if ( ret )
    {
      return ret;
    }

    if ( ( ptr[0x1fe] != 0x55 ) || ( ptr[0x1ff] != 0xaa ) )
    {
      return F_ERR_NOTFORMATTED;                                                /*??*/
    }

    if ( ( ptr[0] != 0xeb ) && ( ptr[0] != 0xe9 ) )
    {
      return F_ERR_NOTFORMATTED;                                        /*??*/
    }
  }

  ptr += 11;
  if ( _f_getword( ptr ) != F_SECTOR_SIZE )
  {
    return F_ERR_NOTSUPPSECTORSIZE;
  }

  ptr += 2;
  gl_volume.bootrecord.sector_per_cluster = *ptr++;
  gl_volume.firstfat.sector = _f_getword( ptr );
  ptr += 2;
  gl_volume.bootrecord.number_of_FATs = *ptr++;
  gl_volume.root.num = _f_getword( ptr );
  ptr += 2;
  gl_volume.root.num *= sizeof( F_DIRENTRY );
  gl_volume.root.num /= F_SECTOR_SIZE;
  maxcluster = _f_getword( ptr );
  ptr += 2;
  gl_volume.bootrecord.media_descriptor = *ptr++;
  gl_volume.firstfat.num = _f_getword( ptr );
  ptr += 6;
  _n = _f_getlong( ptr );
  ptr += 4;
  if ( _n < first_sector )
  {
    _n = first_sector;
  }

  gl_volume.firstfat.sector += _n;
  if ( !maxcluster )
  {
    maxcluster = _f_getlong( ptr );
  }

  ptr += 4;


  if ( gl_volume.firstfat.num )
  {
    gl_volume.root.sector = gl_volume.firstfat.sector + ( gl_volume.firstfat.num * gl_volume.bootrecord.number_of_FATs );
    gl_volume._tdata.sector = gl_volume.root.sector + gl_volume.root.num;
    gl_volume._tdata.num = 0;
    ptr += 3;
  }
  else
  {
    gl_volume.firstfat.num = _f_getlong( ptr );
    ptr += 8;
    gl_volume._tdata.sector = gl_volume.firstfat.sector;
    gl_volume._tdata.sector += gl_volume.firstfat.num * gl_volume.bootrecord.number_of_FATs;
    gl_volume._tdata.num = 0;
    gl_volume.bootrecord.rootcluster = _f_getlong( ptr );
    ptr += 23;
    gl_volume.root.num = gl_volume.bootrecord.sector_per_cluster;
    gl_volume.root.sector = ( ( gl_volume.bootrecord.rootcluster - 2 ) * gl_volume.root.num ) + gl_volume._tdata.sector;
  }

  gl_volume.bootrecord.serial_number = _f_getlong( ptr );

  maxcluster -= gl_volume._tdata.sector;
  maxcluster += _n;
  gl_volume.maxcluster = maxcluster / gl_volume.bootrecord.sector_per_cluster;

  if ( gl_volume.maxcluster < ( F_CLUSTER_RESERVED & 0xfff ) )
  {
    gl_volume.mediatype = F_FAT12_MEDIA;
  }
  else if ( gl_volume.maxcluster < ( F_CLUSTER_RESERVED & 0xffff ) )
  {
    gl_volume.mediatype = F_FAT16_MEDIA;
  }
  else
  {
    gl_volume.mediatype = F_FAT32_MEDIA;
  }

  if ( gl_volume.bootrecord.media_descriptor != 0xf8 )    /*fixdrive*/
  {
    if ( gl_volume.bootrecord.media_descriptor != 0xf0 )  /*removable*/
    {
      return F_ERR_NOTFORMATTED;      /*??*/
    }
  }

  return F_NO_ERROR;
} /* _f_readbootrecord */




/****************************************************************************
 *
 * _f_getvolume
 *
 * getting back a volume info structure of a given drive, it try to mounts
 * drive if it was not mounted before
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
unsigned char _f_getvolume ( void )
{
  switch ( gl_volume.state )
  {
    case F_STATE_NONE:
      return F_ERR_ONDRIVE;

    case F_STATE_WORKING:

      if ( !_f_checkstatus() )
      {
        return F_NO_ERROR;
      }

    /* here we don't stop case flow,  */
    /* because we have to clean up this volume! */

    case F_STATE_NEEDMOUNT:
    {
      gl_file.modified = 0;
      gl_volume.modified = 0;
      gl_volume.lastalloccluster = 0;
      gl_volume.actsector = (unsigned long)( -1 );
      gl_volume.fatsector = (unsigned long)( -1 );

      gl_file.mode = F_FILE_CLOSE;

      gl_volume.cwd[0] = 0;     /*reset cwd*/
      gl_volume.mediatype = F_UNKNOWN_MEDIA;

      if ( mdrv->getstatus != NULL )
      {
        if ( mdrv->getstatus( mdrv ) & F_ST_MISSING )
        {
          gl_volume.state = F_STATE_NEEDMOUNT;         /*card missing*/
          return F_ERR_CARDREMOVED;
        }
      }

      if ( !_f_readbootrecord() )
      {
        gl_volume.state = F_STATE_WORKING;
        return F_NO_ERROR;
      }

      gl_volume.mediatype = F_UNKNOWN_MEDIA;
      return F_ERR_NOTFORMATTED;
    }
  } /* switch */

  return F_ERR_ONDRIVE;
} /* _f_getvolume */



/****************************************************************************
 *
 * fn_getfreespace
 *
 * get total/free/used/bad diskspace
 *
 * INPUTS
 * pspace - pointer where to store the information
 *
 * RETURNS
 * error code
 *
 ***************************************************************************/
unsigned char fn_getfreespace ( F_SPACE * pspace )
{
  unsigned char  ret;
  unsigned long  a;
  unsigned long  clustersize;

  ret = _f_getvolume();
  if ( ret )
  {
    return ret;
  }

  psp_memset( pspace, 0, sizeof( F_SPACE ) );
  pspace->total = gl_volume.maxcluster;

  gl_volume.fatsector = (unsigned long)-1;
  for ( a = 2 ; a < gl_volume.maxcluster + 2 ; a++ )
  {
    unsigned long  value;

    ret = _f_getclustervalue( a, &value );
    if ( ret )
    {
      return ret;
    }

    if ( !value )
    {
      ++( pspace->free );
    }
    else if ( value == F_CLUSTER_BAD )
    {
      ++( pspace->bad );
    }
    else
    {
      ++( pspace->used );
    }
  }

  clustersize = (unsigned long)( gl_volume.bootrecord.sector_per_cluster * F_SECTOR_SIZE );
  for ( a = 0 ; ( clustersize & 1 ) == 0 ; a++ )
  {
    clustersize >>= 1;
  }

  pspace->total_high = ( pspace->total ) >> ( 32 - a );
  pspace->total <<= a;
  pspace->free_high = ( pspace->free ) >> ( 32 - a );
  pspace->free <<= a;
  pspace->used_high = ( pspace->used ) >> ( 32 - a );
  pspace->used <<= a;
  pspace->bad_high = ( pspace->bad ) >> ( 32 - a );
  pspace->bad <<= a;

  return F_NO_ERROR;
} /* fn_getfreespace */


/****************************************************************************
 *
 * fn_getserial
 *
 * get serial number
 *
 * INPUTS
 * serial - pointer where to store the serial number
 *
 * RETURNS
 * error code
 *
 ***************************************************************************/
unsigned char fn_getserial ( unsigned long * serial )
{
  unsigned char  ret;

  ret = _f_getvolume();
  if ( ret )
  {
    return ret;
  }

  *serial = gl_volume.bootrecord.serial_number;
  return 0;
}


/*
** fs_init
**
** Initialize STHIN file system
**
** RETURN: F_NO_ERROR on success, other if error.
*/
unsigned char fs_init ( void )
{
  unsigned char  rc = F_NO_ERROR;

#if RTOS_SUPPORT
  rc = fsr_init();
  if ( rc )
  {
    return rc;
  }

#endif
  return rc;
} /* fs_init */


/*
** fs_delete
**
** Delete STHIN file system
**
** RETURN: F_NO_ERROR on success, other if error.
*/
unsigned char fs_delete ( void )
{
  unsigned char  rc = F_NO_ERROR;

#if RTOS_SUPPORT
  rc = fsr_delete();
  if ( rc )
  {
    return rc;
  }

#endif
  return rc;
} /* fs_delete */


/****************************************************************************
 *
 * fn_initvolume
 *
 * initiate a volume, this function has to be called 1st to set physical
 * driver function to a given volume
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
unsigned char fn_initvolume ( F_DRIVERINIT initfunc )
{
#if F_FS_THREAD_AWARE == 1
	{
		extern xSemaphoreHandle fs_lock_semaphore;

		if( fs_lock_semaphore == NULL )
		{
			fs_lock_semaphore = xSemaphoreCreateMutex();
			if( fs_lock_semaphore == NULL )
			{
				return F_ERR_OS;
			}
		}
	}
#endif /* F_FS_THREAD_AWARE */

  gl_volume.state = F_STATE_NONE;

  mdrv = initfunc( 0 );
  if ( mdrv == NULL )
  {
    return F_ERR_INITFUNC;
  }

  gl_volume.state = F_STATE_NEEDMOUNT;

#if F_FILE_CHANGED_EVENT
  f_filechangedevent = 0;
#endif

  return _f_getvolume();
} /* fn_initvolume */


/****************************************************************************
 *
 * fn_delvolume
 *
 ***************************************************************************/
unsigned char fn_delvolume ( void )
{
  if ( mdrv->release )
  {
    (void)mdrv->release( mdrv );
  }

  return 0;
}
