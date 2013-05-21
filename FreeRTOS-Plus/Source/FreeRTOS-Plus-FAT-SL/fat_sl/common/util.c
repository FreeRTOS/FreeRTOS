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
#include "../../psp/include/psp_rtc.h"
#include "dir.h"

#include "util.h"

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif


/****************************************************************************
 *
 * _f_getword
 *
 * get a word 16bit number from a memory (it uses LITTLE ENDIAN mode always)
 *
 * INPUTS
 *
 * ptr - pointer where data is
 *
 * RETURNS
 *
 * word number
 *
 ***************************************************************************/
unsigned short _f_getword ( void * ptr )
{
  unsigned char * sptr = (unsigned char *)ptr;
  unsigned short  ret;

  ret = (unsigned short)( sptr[1] & 0xff );
  ret <<= 8;
  ret |= ( sptr[0] & 0xff );
  return ret;
}


/****************************************************************************
 *
 * _f_setword
 *
 * set a word 16bit number into a memory (it uses LITTLE ENDIAN mode always)
 *
 * INPUTS
 *
 * ptr - where to store data
 * num - 16 bit number to store
 *
 ***************************************************************************/
void _f_setword ( void * ptr, unsigned short num )
{
  unsigned char * sptr = (unsigned char *)ptr;

  sptr[1] = (unsigned char)( num >> 8 );
  sptr[0] = (unsigned char)( num );
}


/****************************************************************************
 *
 * _f_getlong
 *
 * get a long 32bit number from a memory (it uses LITTLE ENDIAN mode always)
 *
 * INPUTS
 *
 * ptr - pointer where data is
 *
 * RETURNS
 *
 * long number
 *
 ***************************************************************************/
unsigned long _f_getlong ( void * ptr )
{
  unsigned char * sptr = (unsigned char *)ptr;
  unsigned long   ret;

  ret = (unsigned long)( sptr[3] & 0xff );
  ret <<= 8;
  ret |= ( sptr[2] & 0xff );
  ret <<= 8;
  ret |= ( sptr[1] & 0xff );
  ret <<= 8;
  ret |= ( sptr[0] & 0xff );
  return ret;
}


/****************************************************************************
 *
 * _f_setlong
 *
 * set a long 32bit number into a memory (it uses LITTLE ENDIAN mode always)
 *
 * INPUTS
 *
 * ptr - where to store data
 * num - 32 bit number to store
 *
 ***************************************************************************/
void _f_setlong ( void * ptr, unsigned long num )
{
  unsigned char * sptr = (unsigned char *)ptr;

  sptr[3] = (unsigned char)( num >> 24 );
  sptr[2] = (unsigned char)( num >> 16 );
  sptr[1] = (unsigned char)( num >> 8 );
  sptr[0] = (unsigned char)( num );
}


/****************************************************************************
 *
 * _setcharzero
 *
 * fills with zero charater to memory
 *
 * INPUTS
 *
 * num - number of characters
 * ptr - where to store data
 *
 * RETURNS
 *
 * last write position
 *
 ***************************************************************************/
unsigned char * _setcharzero ( int num, unsigned char * ptr )
{
  while ( num-- )
  {
    *ptr++ = 0;
  }

  return ptr;
}


/****************************************************************************
 *
 * _setchar
 *
 * copy a charater string to memory
 *
 * INPUTS
 *
 * array - original code what to copy
 * num - number of characters
 * ptr - where to store data
 *
 * RETURNS
 *
 * last write position
 *
 ***************************************************************************/
unsigned char * _setchar ( const unsigned char * array, int num, unsigned char * ptr )
{
  if ( !array )
  {
    return _setcharzero( num, ptr );
  }

  while ( num-- )
  {
    *ptr++ = *array++;
  }

  return ptr;
}


/****************************************************************************
 *
 * _setword
 *
 * store a 16bit word into memory
 *
 * INPUTS
 *
 * num - 16bit number to store
 * ptr - where to store data
 *
 * RETURNS
 *
 * last write position
 *
 ***************************************************************************/
unsigned char * _setword ( unsigned short num, unsigned char * ptr )
{
  _f_setword( ptr, num );
  return ptr + 2;
}


/****************************************************************************
 *
 * _setlong
 *
 * store a 32bit long number into memory
 *
 * INPUTS
 *
 * num - 32bit number to store
 * ptr - where to store data
 *
 * RETURNS
 *
 * last write position
 *
 ***************************************************************************/
unsigned char * _setlong ( unsigned long num, unsigned char * ptr )
{
  _f_setlong( ptr, num );
  return ptr + 4;
}


/****************************************************************************
 *
 * _f_toupper
 *
 * convert a string into lower case
 *
 * INPUTS
 *
 * s - input string to convert
 *
 ***************************************************************************/
char _f_toupper ( char ch )
{
  if ( ( ch >= 'a' ) && ( ch <= 'z' ) )
  {
    return (char)( ch - 'a' + 'A' );
  }

  return ch;
}


/****************************************************************************
 *
 * f_igettimedate
 *
 * INPUTS
 *    time - pointer to time variable
 *    date - pointer to date variable
 * OUTPUTS
 *    time - current time
 *    date - current date
 *
 * RETURNS
 *    none
 *
 ***************************************************************************/
void f_igettimedate ( unsigned short * time, unsigned short * date )
{
  t_psp_timedate  s_timedate;

  psp_getcurrenttimedate( &s_timedate );

  *time = ( ( (uint16_t)s_timedate.hour << F_CTIME_HOUR_SHIFT ) & F_CTIME_HOUR_MASK )
          | ( ( (uint16_t)s_timedate.min << F_CTIME_MIN_SHIFT )  & F_CTIME_MIN_MASK )
          | ( ( ( (uint16_t)s_timedate.sec >> 1 ) << F_CTIME_SEC_SHIFT )  & F_CTIME_SEC_MASK );

  *date = ( ( ( s_timedate.year - 1980 ) << F_CDATE_YEAR_SHIFT ) & F_CDATE_YEAR_MASK )
          | ( ( (uint16_t)s_timedate.month << F_CDATE_MONTH_SHIFT ) & F_CDATE_MONTH_MASK )
          | ( ( (uint16_t)s_timedate.day << F_CDATE_DAY_SHIFT ) & F_CDATE_DAY_MASK );

  return;
}









