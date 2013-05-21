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

#include "util.h"

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif



/****************************************************************************
 *
 * _f_checknameprim
 *
 * checking a string if could be valid
 *
 * INPUTS
 *
 * ptr - pointer to name or extension
 * len - number max char of name or extension
 *
 * RETURNS
 *
 ***************************************************************************/
static unsigned char _f_checknameprim ( char * ptr, unsigned char len )
{
  unsigned char  inspace = 0;

  while ( len-- )
  {
    char  ch = *ptr++;
    if ( !inspace )
    {
      if ( ch == ' ' )
      {
        inspace = 1;
      }

      if ( ( ch == '|' ) || ( ch == '[' ) || ( ch == ']' ) || ( ch == '<' ) || ( ch == '>' ) || ( ch == '/' ) || ( ch == '\\' ) || ( ch == ':' ) )
      {
        return 1;
      }
    }
    else if ( ch != ' ' )
    {
      return 1;                     /*no inspace allowed*/
    }
  }

  return 0;
} /* _f_checknameprim */


/****************************************************************************
 *
 * _f_checkname
 *
 * checking filename and extension for special characters
 *
 * INPUTS
 *
 * name - filename (e.g.: filename)
 * ext - extension of file (e.g.: txt)
 *
 * RETURNS
 *
 * 0 - if no contains invalid character
 * other - if contains any invalid character
 *
 ***************************************************************************/
unsigned char _f_checkname ( char * name, char * ext )
{
  if ( _f_checknameprim( name, F_MAXNAME ) )
  {
    return 1;
  }

  if ( _f_checknameprim( ext, F_MAXEXT ) )
  {
    return 1;
  }

  return 0;
}


/****************************************************************************
 *
 * _f_checknamewc
 *
 * checking filename and extension for wildcard character
 *
 * INPUTS
 *
 * name - filename (e.g.: filename)
 * ext - extension of file (e.g.: txt)
 *
 * RETURNS
 *
 * 0 - if no contains wildcard character (? or *)
 * other - if contains any wildcard character
 *
 ***************************************************************************/
unsigned char _f_checknamewc ( const char * name, const char * ext )
{
  unsigned char  a = 0;

  for ( a = 0 ; a < F_MAXNAME ; a++ )
  {
    char  ch = name[a];
    if ( ( ch == '?' ) || ( ch == '*' ) )
    {
      return 1;
    }
  }

  for ( a = 0 ; a < F_MAXEXT ; a++ )
  {
    char  ch = ext[a];
    if ( ( ch == '?' ) || ( ch == '*' ) )
    {
      return 1;
    }
  }

  return _f_checkname( (char *)name, (char *)ext );
} /* _f_checknamewc */




/****************************************************************************
 *
 * _f_setnameext
 *
 * convert a string into filename and extension separatelly, the terminator
 * character could be zero char, '/' or '\'
 *
 * INPUTS
 *
 * s - source string (e.g.: hello.txt)
 * name - where to store name (this array size has to be F_MAXNAME (8))
 * ext - where to store extension (this array size has to be F_MAXEXT (3))
 *
 * RETURNS
 *
 * length of the used bytes from source string array
 *
 ***************************************************************************/
unsigned char _f_setnameext ( char * s, char * name, char * ext )
{
  unsigned char  len, extlen = 0;
  unsigned char  a;
  unsigned char  setext = 1;

  for ( len = 0 ; ; )
  {
    unsigned char  ch = s[len];
    if ( ( ch == 0 ) || ( ch == '\\' ) || ( ch == '/' ) )
    {
      break;
    }

    len++;                      /*calculate len*/
  }

  if ( len && ( s[0] == '.' ) )
  {
/*		if (len==1 || (s[1]=='.' && len==2)) goto dots;		*/
    if ( ( len == 1 ) || ( s[1] == '.' ) )
    {
      goto dots;
    }
  }

  for ( a = len ; a ; a-- )
  {
    if ( s[a - 1] == '.' )
    {
      unsigned char  b;

      extlen = (unsigned char)( len - a + 1 );
      len = (unsigned char)( a - 1 );

      for ( b = 0 ; b < F_MAXEXT ; b++ )
      {
        if ( b < extlen - 1 )
        {
          ext[b] = _f_toupper( s[a++] );
        }
        else
        {
          ext[b] = ' ';
        }
      }

      setext = 0;
      break;
    }
  }

dots:
  if ( setext )
  {
    for ( a = 0 ; a < F_MAXEXT ; a++ )
    {
      ext[a] = ' ';
    }
  }

  for ( a = 0 ; a < F_MAXNAME ; a++ )
  {
    if ( a < len )
    {
      name[a] = _f_toupper( s[a] );
    }
    else
    {
      name[a] = ' ';
    }
  }

  return (unsigned char)( len + extlen );
} /* _f_setnameext */



/****************************************************************************
 *
 * _f_setfsname
 *
 * convert a single string into F_NAME structure
 *
 * INPUTS
 *
 * name - combined name with drive,path,filename,extension used for source
 * fsname - where to fill this structure with separated drive,path,name,ext
 *
 * RETURNS
 *
 * 0 - if successfully
 * other - if name contains invalid path or name
 *
 ***************************************************************************/
unsigned char _f_setfsname ( const char * name, F_NAME * fsname )
{
  char           s[F_MAXPATH];
  unsigned char  namepos = 0;

  unsigned char  pathpos = 0;
  unsigned char  a;

  s[0] = 0;

  if ( !name[0] )
  {
    return 1;               /*no name*/
  }

  if ( name[1] == ':' )
  {
    name += 2;
  }

  if ( ( name[0] != '/' ) && ( name[0] != '\\' ) )
  {
    if ( fn_getcwd( fsname->path, F_MAXPATH, 0 ) )
    {
      return 1;                                            /*error*/
    }

    for ( pathpos = 0 ; fsname->path[pathpos] ; )
    {
      pathpos++;
    }
  }


  for ( ; ; )
  {
    char  ch = _f_toupper( *name++ );

    if ( !ch )
    {
      break;
    }

    if ( ch == ':' )
    {
      return 1;                /*not allowed*/
    }

    if ( ( ch == '/' ) || ( ch == '\\' ) )
    {
      if ( pathpos )
      {
        if ( fsname->path[pathpos - 1] == '/' )
        {
          return 1;                                         /*not allowed double */
        }

        if ( pathpos >= F_MAXPATH - 2 )
        {
          return 1;                                 /*path too long*/
        }

        fsname->path[pathpos++] = '/';
      }

      for ( ; namepos ; )
      {
        if ( s[namepos - 1] != ' ' )
        {
          break;
        }

        namepos--;                /*remove end spaces*/
      }

      for ( a = 0 ; a < namepos ; a++ )
      {
        if ( pathpos >= F_MAXPATH - 2 )
        {
          return 1;                                 /*path too long*/
        }

        fsname->path[pathpos++] = s[a];
      }

      namepos = 0;
      continue;
    }

    if ( ( ch == ' ' ) && ( !namepos ) )
    {
      continue;                              /*remove start spaces*/
    }

    if ( namepos >= ( sizeof( s ) - 2 ) )
    {
      return 1;                               /*name too long*/
    }

    s[namepos++] = ch;
  }

  s[namepos] = 0; /*terminates it*/
  fsname->path[pathpos] = 0;  /*terminates it*/

  for ( ; namepos ; )
  {
    if ( s[namepos - 1] != ' ' )
    {
      break;
    }

    s[namepos - 1] = 0; /*remove end spaces*/
    namepos--;
  }

  if ( !_f_setnameext( s, fsname->filename, fsname->fileext ) )
  {
    return 2;                                                         /*no name*/
  }

  if ( fsname->filename[0] == ' ' )
  {
    return 1;                               /*cannot be*/
  }

  return 0;
} /* _f_setfsname */


/****************************************************************************
 *
 * _f_createfullname
 *
 * create full name
 *
 * INPUTS
 *
 * buffer - where to create
 * buffersize - size of the buffer
 * drivenum - drive number
 * path - path of the file
 * filename - file name
 * fileext - file extension
 *
 * RETURNS
 *
 * 1 - if found and osize is filled
 * 0 - not found
 *
 ***************************************************************************/
int _f_createfullname ( char * buffer, int buffersize, char * path, char * filename, char * fileext )
{
  char * fullname = buffer;
  int    a;

  /* adding drive letter */
  if ( buffersize < 1 )
  {
    return 1;
  }

  *fullname++ = '/';
  buffersize -= 1;

  /* adding path */
  if ( path[0] )
  {
    for ( ; ; )
    {
      char  ch = *path++;

      if ( !ch )
      {
        break;
      }

      if ( buffersize <= 0 )
      {
        return 1;
      }

      *fullname++ = ch;
      buffersize--;
    }

    /* adding separator */
    if ( buffersize <= 0 )
    {
      return 1;
    }

    *fullname++ = '/';
  }

  /* adding name */
  for ( a = 0 ; a < F_MAXNAME ; a++ )
  {
    char  ch = *filename++;

    if ( ( !ch ) || ( ch == 32 ) )
    {
      break;
    }

    if ( buffersize <= 0 )
    {
      return 1;
    }

    *fullname++ = ch;
    buffersize--;
  }

  /* adding ext*/
  if ( fileext[0] && ( fileext[0] != 32 ) )
  {
    /* adding dot */
    if ( !buffersize )
    {
      return 1;
    }

    *fullname++ = '.';

    for ( a = 0 ; a < F_MAXEXT ; a++ )
    {
      char  ch = *fileext++;

      if ( ( !ch ) || ( ch == 32 ) )
      {
        break;
      }

      if ( buffersize <= 0 )
      {
        return 1;
      }

      *fullname++ = ch;
      buffersize--;
    }
  }

  /* adding terminator */
  if ( buffersize <= 0 )
  {
    return 1;
  }

  *fullname++ = 0;

  return 0;
} /* _f_createfullname */



