#ifndef _TEST_C_
#define _TEST_C_


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

#include "test.h"
#include "../../api/fat_sl.h"
#include "../../psp/target/fat_sl/psp_test.h"

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

static char  cwd[F_MAXPATH];

static F_FIND  find;

static void _f_deleteall ( void )
{
  F_FIND         f2;
  unsigned char  sd = 0, rc, fl = 0;

  f2 = find;
  do
  {
    rc = f_findfirst( "*.*", &find );
    while ( rc == 0 && find.filename[0] == '.' )
    {
      rc = f_findnext( &find );
    }

    if ( rc == 0 )
    {
      if ( find.attr & F_ATTR_DIR )
      {
        ++sd;
        fl = 1;
        f2 = find;
        (void)f_chdir( find.filename );
        continue;
      }
      else
      {
        (void)f_delete( find.filename );
        rc = f_findnext( &find );
      }
    }

    if ( rc && sd && fl )
    {
      (void)f_chdir( ".." );
      --sd;
      fl = 0;
      find = f2;
      (void)f_rmdir( find.filename );
      rc = f_findnext( &find );
    }

    if ( rc && sd && !fl )
    {
      (void)f_chdir( "/" );
      sd = 0;
      rc = 0;
    }
  }
  while ( rc == 0 );
} /* _f_deleteall */

char  stmp[20];
static char * f_nameconv ( char * s )
{
  char * ss = stmp;

  for ( ; ; )
  {
    char  ch = *s++;
    if ( ( ch >= 'a' ) && ( ch <= 'z' ) )
    {
      ch += 'A' - 'a';
    }

    *ss++ = ch;
    if ( !ch )
    {
      break;
    }
  }

  return stmp;
} /* f_nameconv */

static unsigned char f_formatting ( void )
{
  unsigned char  ret;

  _f_dump( "f_formatting" );

/*checking formatting*/
  ret = f_format( F_FAT_TYPE );
  if ( ret )
  {
    return _f_result( 0, ret );
  }

  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 1, ret );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 2, ret );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_formatting */

static unsigned char _f_checkcwd ( char * orig )
{
  unsigned char  ret;

  ret = f_getcwd( cwd, F_MAXPATH );
  if ( ret )
  {
    return ret;
  }

  if ( strcmp( orig, cwd ) )
  {
    return (unsigned char)-1;
  }

  return 0;
}

static unsigned char f_dirtest ( void )
{
  unsigned char  ret;

  _f_dump( "f_dirtest" );

  _f_deleteall();

/*creates a ab abc abcd*/
  ret = f_mkdir( "a" );
  if ( ret )
  {
    return _f_result( 1, ret );
  }

  ret = f_mkdir( "ab" );
  if ( ret )
  {
    return _f_result( 2, ret );
  }

  ret = f_mkdir( "abc" );
  if ( ret )
  {
    return _f_result( 3, ret );
  }

  ret = f_mkdir( "abca" );
  if ( ret )
  {
    return _f_result( 4, ret );
  }

/*creates directories in /a  -  a ab abc abcd*/
  ret = f_mkdir( "a/a" );
  if ( ret )
  {
    return _f_result( 5, ret );
  }

  ret = f_mkdir( "a/ab" );
  if ( ret )
  {
    return _f_result( 6, ret );
  }

  ret = f_mkdir( "a/abc" );
  if ( ret )
  {
    return _f_result( 7, ret );
  }

  ret = f_mkdir( "a/abcd" );
  if ( ret )
  {
    return _f_result( 8, ret );
  }

/*change into a/abcd and check cwd*/
  ret = f_chdir( "a/abcd" );
  if ( ret )
  {
    return _f_result( 9, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/a/abcd" ) );
  if ( ret )
  {
    return _f_result( 10, ret );
  }

/*make directory t change into t and check cwd="a/abcd/t"*/
  ret = f_mkdir( "t" );
  if ( ret )
  {
    return _f_result( 11, ret );
  }

  ret = f_chdir( "t" );
  if ( ret )
  {
    return _f_result( 12, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/a/abcd/t" ) );
  if ( ret )
  {
    return _f_result( 13, ret );
  }

  ret = f_chdir( "." );
  if ( ret )
  {
    return _f_result( 14, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/a/abcd/t" ) );
  if ( ret )
  {
    return _f_result( 15, ret );
  }

  ret = f_chdir( "../." );
  if ( ret )
  {
    return _f_result( 16, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/a/abcd" ) );
  if ( ret )
  {
    return _f_result( 17, ret );
  }

/*removing t dir*/
  ret = f_rmdir( "t" );
  if ( ret )
  {
    return _f_result( 18, ret );
  }

  ret = f_chdir( "t" );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 19, ret );
  }

/*removing /a dir*/
  ret = f_rmdir( "/ab" );
  if ( ret )
  {
    return _f_result( 20, ret );
  }

  ret = f_chdir( "/ab" );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 21, ret );
  }

/*removing /a dir*/
  ret = f_rmdir( "../../a" );
  if ( ret != F_ERR_NOTEMPTY )
  {
    return _f_result( 22, ret );
  }

/*removing /abca dir*/
  ret = f_rmdir( "a:/abca" );
  if ( ret )
  {
    return _f_result( 24, ret );
  }

/*changing invalid dirs*/
  ret = f_chdir( "" );
  if ( ret != F_ERR_INVALIDNAME )
  {
    return _f_result( 25, ret );
  }

  ret = f_chdir( " " );
  if ( ret )
  {
    return _f_result( 26, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/a/abcd" ) );
  if ( ret )
  {
    return _f_result( 27, ret );
  }

  ret = f_chdir( "?" );
  if ( ret != F_ERR_INVALIDNAME )
  {
    return _f_result( 28, ret );
  }

  ret = f_chdir( "*.*" );
  if ( ret != F_ERR_INVALIDNAME )
  {
    return _f_result( 29, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/a/abcd" ) );
  if ( ret )
  {
    return _f_result( 30, ret );
  }

/*changing into /abc and removes subfolder from /a/ */
  ret = f_chdir( "/abc" );
  if ( ret )
  {
    return _f_result( 31, ret );
  }

  ret = f_rmdir( "/a/a" );
  if ( ret )
  {
    return _f_result( 32, ret );
  }

  ret = f_rmdir( "A:../a/ab" );
  if ( ret )
  {
    return _f_result( 33, ret );
  }

  ret = f_rmdir( "A:/a/abc" );
  if ( ret )
  {
    return _f_result( 34, ret );
  }

  ret = f_rmdir( ".././abc/.././a/../a/abcd" );
  if ( ret )
  {
    return _f_result( 35, ret );
  }

/*some invalid rmdir*/
  ret = f_rmdir( "." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 36, ret );
  }

  ret = f_rmdir( ".." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 37, ret );
  }

/*create again abc remove abc*/
  ret = f_mkdir( ".././abc" );
  if ( ret != F_ERR_DUPLICATED )
  {
    return _f_result( 38, ret );
  }

  ret = f_rmdir( "../abc" );
  if ( ret )
  {
    return _f_result( 39, ret );
  }

  ret = f_mkdir( ".././abc" );
  if ( ret != F_ERR_INVALIDDIR )
  {
    return _f_result( 40, ret );                         /*cwd is not exist*/
  }

  ret = f_chdir( "/" );
  if ( ret )
  {
    return _f_result( 41, ret );
  }

/*try . and .. in the root*/
  ret = f_chdir( "." );
  if ( ret )
  {
    return _f_result( 42, ret );
  }

  ret = f_chdir( "./././." );
  if ( ret )
  {
    return _f_result( 43, ret );
  }

  ret = f_chdir( ".." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 44, ret );
  }

  ret = _f_checkcwd( "/" ); /*root!*/
  if ( ret )
  {
    return _f_result( 45, ret );
  }

/*test . and .. in a and remove a*/
  ret = f_chdir( "a" );
  if ( ret )
  {
    return _f_result( 46, ret );
  }

  ret = f_chdir( ".." );
  if ( ret )
  {
    return _f_result( 47, ret );
  }

  ret = f_chdir( "a" );
  if ( ret )
  {
    return _f_result( 48, ret );
  }

  ret = f_chdir( "." );
  if ( ret )
  {
    return _f_result( 49, ret );
  }

  ret = f_chdir( "a" );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 50, ret );
  }

  ret = f_chdir( "./.." );
  if ( ret )
  {
    return _f_result( 51, ret );
  }

  ret = f_rmdir( "a" );
  if ( ret )
  {
    return _f_result( 52, ret );
  }

/*check if all are removed*/
  ret = f_findfirst( "*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 53, ret );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_dirtest */


static unsigned char f_findingtest ( void )
{
  unsigned char  ret;

  _f_dump( "f_findingtest" );

  _f_deleteall();

/*check empty*/
  ret = f_findfirst( "*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 0, ret );
  }

/*create Hello.dir*/
  ret = f_mkdir( "Hello.dir" );
  if ( ret )
  {
    return _f_result( 1, ret );
  }

/*check if it is exist, and only exist*/
  ret = f_findfirst( "*.*", &find );
  if ( ret )
  {
    return _f_result( 2, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "Hello.dir" ) ) )
  {
    return _f_result( 3, 0 );
  }

  if ( find.attr != F_ATTR_DIR )
  {
    return _f_result( 4, 0 );
  }

  ret = f_findnext( &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 5, ret );
  }

/*check some not founds*/
  ret = f_findfirst( "q*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 6, ret );
  }

  ret = f_findfirst( "Hello.", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 7, ret );
  }

  ret = f_findfirst( "a/*.*", &find );
  if ( ret != F_ERR_INVALIDDIR )
  {
    return _f_result( 8, ret );
  }

  ret = f_findfirst( ".", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 9, ret );
  }

  ret = f_findfirst( "..", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 10, ret );
  }

  ret = f_findfirst( "?e.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 11, ret );
  }

  ret = f_findfirst( "*.", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 12, ret );
  }

  ret = f_findfirst( "*.?", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 13, ret );
  }

  ret = f_findfirst( "*.??", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 14, ret );
  }


/*check some founds*/
  ret = f_findfirst( "*.dir", &find );
  if ( ret )
  {
    return _f_result( 15, ret );
  }

  ret = f_findfirst( "*.d?r", &find );
  if ( ret )
  {
    return _f_result( 16, ret );
  }

  ret = f_findfirst( "*.d??", &find );
  if ( ret )
  {
    return _f_result( 17, ret );
  }

  ret = f_findfirst( "*.???", &find );
  if ( ret )
  {
    return _f_result( 18, ret );
  }

  ret = f_findfirst( "?ello.???", &find );
  if ( ret )
  {
    return _f_result( 19, ret );
  }

  ret = f_findfirst( "he??o.dir", &find );
  if ( ret )
  {
    return _f_result( 20, ret );
  }

  ret = f_findfirst( "he?*.dir", &find );
  if ( ret )
  {
    return _f_result( 21, ret );
  }

  ret = f_findfirst( "HELLO.DIR", &find ); /*no capitals sensitivity in find!!*/
  if ( ret )
  {
    return _f_result( 22, ret );
  }

/*change into hello.dir*/
  ret = f_chdir( "hello.dir" );
  if ( ret )
  {
    return _f_result( 23, ret );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret )
  {
    return _f_result( 24, ret );
  }

  ret = f_findfirst( "..", &find );
  if ( ret )
  {
    return _f_result( 25, ret );
  }

  ret = f_findfirst( "??", &find );
  if ( ret )
  {
    return _f_result( 26, ret );
  }

  ret = f_findfirst( ".", &find );
  if ( ret )
  {
    return _f_result( 27, ret );
  }

  ret = f_findfirst( "k*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 28, ret );
  }

  ret = f_findfirst( "*.", &find );
  if ( ret )
  {
    return _f_result( 29, ret );
  }

  if ( strcmp( find.filename, "." ) )
  {
    return _f_result( 29, 0 );
  }

  ret = f_findnext( &find );
  if ( ret )
  {
    return _f_result( 29, ret );
  }

  if ( strcmp( find.filename, ".." ) )
  {
    return _f_result( 29, 0 );
  }

  ret = f_findnext( &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 29, ret );
  }


  ret = f_findfirst( "*.a", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 30, ret );
  }

/*creating testdir and find it*/
  ret = f_mkdir( "testdir" );
  if ( ret )
  {
    return _f_result( 31, ret );
  }

  ret = f_findfirst( "*.", &find );
  if ( ret )
  {
    return _f_result( 32, ret );
  }

  if ( strcmp( find.filename, "." ) )
  {
    return _f_result( 32, 0 );
  }

  ret = f_findnext( &find );
  if ( ret )
  {
    return _f_result( 32, ret );
  }

  if ( strcmp( find.filename, ".." ) )
  {
    return _f_result( 32, 0 );
  }

  ret = f_findnext( &find );
  if ( ret )
  {
    return _f_result( 32, ret );
  }


  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 33, 0 );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret )
  {
    return _f_result( 34, ret );
  }

  if ( strcmp( find.filename, "." ) )
  {
    return _f_result( 35, 0 );
  }

  ret = f_findnext( &find );
  if ( ret )
  {
    return _f_result( 35, ret );
  }

  if ( strcmp( find.filename, ".." ) )
  {
    return _f_result( 35, 0 );
  }

  ret = f_findnext( &find );
  if ( ret )
  {
    return _f_result( 36, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 37, 0 );
  }

  ret = f_findnext( &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 38, ret );
  }

/*search exact file*/
  ret = f_findfirst( "testDir", &find ); /*no capitals!*/
  if ( ret )
  {
    return _f_result( 39, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 40, 0 );
  }

  ret = f_findnext( &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 41, ret );
  }


/*go back to root and remove dirs*/
  ret = f_chdir( "\\" );
  if ( ret )
  {
    return _f_result( 42, ret );
  }

  ret = f_rmdir( "Hello.dir/testdir" );
  if ( ret )
  {
    return _f_result( 43, ret );
  }

  ret = f_rmdir( "Hello.dir" );
  if ( ret )
  {
    return _f_result( 44, ret );
  }

/*check if all are removed*/
  ret = f_findfirst( "*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 45, ret );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_findingtest */

static unsigned char f_powerfail ( void )
{
  unsigned char  ret;

  _f_dump( "f_powerfail" );

/*checking if its power fail system (RAMDRIVE is not powerfail!)*/
  ret = f_mkdir( "testdir" );
  if ( ret )
  {
    return _f_result( 0, ret );
  }

  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 1, ret );
  }

  ret = f_findfirst( "testdir", &find );
  if ( ret )
  {
    return _f_result( 2, ret );
  }

/*checking formatting*/
  ret = f_format( F_FAT_TYPE );
  if ( ret )
  {
    return _f_result( 3, ret );
  }

  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 4, ret );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 5, ret );
  }

/*checking formatting, 1st creating*/
  ret = f_format( F_FAT_TYPE );
  if ( ret )
  {
    return _f_result( 6, ret );
  }

  ret = f_mkdir( "testdir" );
  if ( ret )
  {
    return _f_result( 7, ret );
  }

  ret = f_findfirst( "testdir", &find );
  if ( ret )
  {
    return _f_result( 8, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 9, 0 );
  }

  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 10, ret );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret )
  {
    return _f_result( 11, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 12, 0 );
  }

/*checking formatting, 2nd creating*/
  ret = f_format( F_FAT_TYPE );
  if ( ret )
  {
    return _f_result( 13, ret );
  }

  ret = f_mkdir( "testdir" );
  if ( ret )
  {
    return _f_result( 14, ret );
  }

  ret = f_findfirst( "testdir", &find );
  if ( ret )
  {
    return _f_result( 15, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 16, 0 );
  }

  ret = f_mkdir( "testdir2" );
  if ( ret )
  {
    return _f_result( 17, ret );
  }

  ret = f_findfirst( "testdir2", &find );
  if ( ret )
  {
    return _f_result( 18, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir2" ) ) )
  {
    return _f_result( 19, 0 );
  }

  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 20, ret );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret )
  {
    return _f_result( 21, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir" ) ) )
  {
    return _f_result( 22, 0 );
  }

  ret = f_findnext( &find );
  if ( ret )
  {
    return _f_result( 23, ret );
  }

  if ( strcmp( find.filename, f_nameconv( "testdir2" ) ) )
  {
    return _f_result( 24, 0 );
  }

  ret = f_findnext( &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 25, ret );
  }


/*checking empty*/
  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 26, ret );
  }

  ret = f_format( F_FAT_TYPE );
  if ( ret )
  {
    return _f_result( 27, ret );
  }

  ret = _f_poweron();
  if ( ret )
  {
    return _f_result( 28, ret );
  }

  ret = f_findfirst( "*.*", &find );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 29, ret );
  }


  _f_dump( "passed..." );
  return 0;
} /* f_powerfail */


char  testbuffer[F_MAX_SEEK_TEST + 16]; /* +16 for f_appending test */

static unsigned char checkfilecontent ( long nums, unsigned char value, F_FILE * file )
{
  unsigned char  ch;

  while ( nums-- )
  {
    if ( f_eof( file ) )
    {
      return 1;                    /*eof ?*/
    }

    if ( 1 != f_read( &ch, 1, 1, file ) )
    {
      return 1;
    }

    if ( ch != value )
    {
      return 1;
    }
  }

  return 0;
} /* checkfilecontent */

static unsigned char f_seeking ( int sectorsize )
{
  F_FILE       * file;
  unsigned char  ret;
  unsigned long  size;
  unsigned long  pos;

  if ( sectorsize == 128 )
  {
    _f_dump( "f_seeking with 128" );
  }

  #if ( F_MAX_SEEK_TEST > 128 )
  else if ( sectorsize == 256 )
  {
    _f_dump( "f_seeking with 256" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 256 )
  else if ( sectorsize == 512 )
  {
    _f_dump( "f_seeking with 512" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 512 )
  else if ( sectorsize == 1024 )
  {
    _f_dump( "f_seeking with 1024" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 1024 )
  else if ( sectorsize == 2048 )
  {
    _f_dump( "f_seeking with 2048" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 2048 )
  else if ( sectorsize == 4096 )
  {
    _f_dump( "f_seeking with 4096" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 4096 )
  else if ( sectorsize == 8192 )
  {
    _f_dump( "f_seeking with 8192" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 8192 )
  else if ( sectorsize == 16384 )
  {
    _f_dump( "f_seeking with 16384" );
  }
  #endif
  #if ( F_MAX_SEEK_TEST > 16384 )
  else if ( sectorsize == 32768 )
  {
    _f_dump( "f_seeking with 32768" );
  }
  #endif
  else
  {
    _f_dump( "f_seeking with random" );
  }

/*checking sector boundary seekeng*/
  file = f_open( "test.bin", "w+" );
  if ( !file )
  {
    return _f_result( 0, 0 );
  }

/*write sectorsize times 0*/
  psp_memset( testbuffer, 0, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, (long)sectorsize, file );
  if ( size != (unsigned long) sectorsize )
  {
    return _f_result( 1, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) sectorsize )
  {
    return _f_result( 2, pos );
  }

/*seek back and read some*/
  ret = f_seek( file, 0, F_SEEK_SET ); /*seek back*/
  if ( ret )
  {
    return _f_result( 3, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos )
  {
    return _f_result( 4, pos );
  }

  size = (unsigned long)f_read( testbuffer, 1, sectorsize, file );
  if ( size != (unsigned long) sectorsize )
  {
    return _f_result( 5, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) sectorsize )
  {
    return _f_result( 6, pos );
  }

/*fake read at eof*/
  size = (unsigned long)f_read( testbuffer, 1, 2, file ); /*eof!*/
  if ( size != 0 )
  {
    return _f_result( 7, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) sectorsize )
  {
    return _f_result( 8, pos );
  }

/*writing sectorsize times 1 at the end*/
  psp_memset( testbuffer, 1, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, sectorsize, file );
  if ( size != (unsigned long) sectorsize )
  {
    return _f_result( 11, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( sectorsize * 2 ) )
  {
    return _f_result( 12, pos );
  }

/*seeking back and read 1byte less*/
  ret = f_seek( file, 0, F_SEEK_SET );
  if ( ret )
  {
    return _f_result( 13, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos )
  {
    return _f_result( 14, pos );
  }

  size = (unsigned long)f_read( testbuffer, 1, sectorsize - 1, file );
  if ( size != (unsigned long) ( sectorsize - 1 ) )
  {
    return _f_result( 15, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( sectorsize - 1 ) )
  {
    return _f_result( 16, pos );
  }


/*write 2 times 2*/
  psp_memset( testbuffer, 2, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, 2, file );
  if ( size != 2 )
  {
    return _f_result( 17, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( sectorsize + 1 ) )
  {
    return _f_result( 18, pos );
  }

/*read 2 bytes*/
  size = (unsigned long)f_read( testbuffer, 2, 1, file );
  if ( size != 1 )
  {
    return _f_result( 19, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( sectorsize + 3 ) )
  {
    return _f_result( 20, pos );
  }


/*write 4 times 3*/
  psp_memset( testbuffer, 3, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, 4, file );
  if ( size != 4 )
  {
    return _f_result( 21, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( sectorsize + 3 + 4 ) )
  {
    return _f_result( 22, pos );
  }

/*seek at 2*/
  ret = f_seek( file, 2, F_SEEK_SET );
  if ( ret )
  {
    return _f_result( 23, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != 2 )
  {
    return _f_result( 24, pos );
  }

/*write 6 times 4*/
  psp_memset( testbuffer, 4, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, 6, file );
  if ( size != 6 )
  {
    return _f_result( 25, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != 8 )
  {
    return _f_result( 26, pos );
  }

/*seek end -4*/
  ret = f_seek( file, -4, F_SEEK_END );
  if ( ret )
  {
    return _f_result( 27, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize - 4 ) )
  {
    return _f_result( 28, pos );
  }

/*read 2 bytes*/
  size = (unsigned long)f_read( testbuffer, 1, 2, file );
  if ( size != 2 )
  {
    return _f_result( 29, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize - 2 ) )
  {
    return _f_result( 30, pos );
  }

/*write 8 times 5*/
  psp_memset( testbuffer, 5, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, 8, file );
  if ( size != 8 )
  {
    return _f_result( 31, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize + 6 ) )
  {
    return _f_result( 32, pos );
  }

/*seek to the begining*/
  ret = f_seek( file, 0, F_SEEK_SET );
  if ( ret )
  {
    return _f_result( 33, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos )
  {
    return _f_result( 34, pos );
  }

/*seek to the end*/
  ret = f_seek( file, 2 * sectorsize + 6, F_SEEK_SET );
  if ( ret )
  {
    return _f_result( 35, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize + 6 ) )
  {
    return _f_result( 36, pos );
  }

/*write 2 times 6*/
  psp_memset( testbuffer, 6, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, 2, file );
  if ( size != 2 )
  {
    return _f_result( 37, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize + 8 ) )
  {
    return _f_result( 38, pos );
  }

/*seek to the begining*/
  (void)f_seek( file, -( 2 * sectorsize + 8 ), F_SEEK_CUR );
  if ( ret )
  {
    return _f_result( 39, ret );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos )
  {
    return _f_result( 40, pos );
  }

/*read 2 times sector*/
  size = (unsigned long)f_read( testbuffer, 1, sectorsize, file );
  if ( size != (unsigned long) sectorsize )
  {
    return _f_result( 41, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) sectorsize )
  {
    return _f_result( 42, pos );
  }

  size = (unsigned long)f_read( testbuffer, 1, sectorsize, file );
  if ( size != (unsigned long) sectorsize )
  {
    return _f_result( 43, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize ) )
  {
    return _f_result( 44, pos );
  }

/*write 1 once 7*/
  psp_memset( testbuffer, 7, sectorsize );
  size = (unsigned long)f_write( testbuffer, 1, 1, file );
  if ( size != 1 )
  {
    return _f_result( 45, size );
  }

  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize + 1 ) )
  {
    return _f_result( 46, pos );
  }

/*close it*/
  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 47, ret );
  }


/*check the result*/
  size = (unsigned long)f_filelength( "test.bin" );
  if ( size != (unsigned long) ( 2 * sectorsize + 8 ) )
  {
    return _f_result( 48, size );
  }

/*opens it*/
  file = f_open( "test.bin", "r" );
  if ( !file )
  {
    return _f_result( 49, size );
  }

  if ( checkfilecontent( 2, 0, file ) )
  {
    return _f_result( 50, 0 );
  }

  if ( checkfilecontent( 6, 4, file ) )
  {
    return _f_result( 51, 0 );
  }

  if ( checkfilecontent( sectorsize - 8 - 1, 0, file ) )
  {
    return _f_result( 52, 0 );
  }

  if ( checkfilecontent( 2, 2, file ) )
  {
    return _f_result( 53, 0 );
  }

  if ( checkfilecontent( 2, 1, file ) )
  {
    return _f_result( 54, 0 );
  }

  if ( checkfilecontent( 4, 3, file ) )
  {
    return _f_result( 55, 0 );
  }

  if ( checkfilecontent( sectorsize - 7 - 2, 1, file ) )
  {
    return _f_result( 56, 0 );
  }

  if ( checkfilecontent( 2, 5, file ) )
  {
    return _f_result( 57, 0 );
  }

  if ( checkfilecontent( 1, 7, file ) )
  {
    return _f_result( 58, 0 );
  }

  if ( checkfilecontent( 5, 5, file ) )
  {
    return _f_result( 59, 0 );
  }

  if ( checkfilecontent( 2, 6, file ) )
  {
    return _f_result( 60, 0 );
  }

/*check pos result*/
  pos = (unsigned long)f_tell( file );
  if ( pos != (unsigned long) ( 2 * sectorsize + 8 ) )
  {
    return _f_result( 61, pos );
  }

/*this has to be eof*/
  pos = f_eof( file );
  if ( !pos )
  {
    return _f_result( 62, pos );
  }

/*close it*/
  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 63, ret );
  }

/*deletes it*/
  ret = f_delete( "test.bin" );
  if ( ret )
  {
    return _f_result( 64, ret );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_seeking */

static unsigned char f_opening ( void )
{
  F_FILE        * file;
  F_FILE        * file2;
  unsigned char   ret;
  unsigned short  size, pos;

  _f_dump( "f_opening" );

/*test non existing file open r, r+*/
  file = f_open( "file.bin", "r" );
  if ( file )
  {
    return _f_result( 0, 0 );
  }

  file = f_open( "file.bin", "r+" );
  if ( file )
  {
    return _f_result( 1, 0 );
  }

/*test non existing appends	"a" a+*/
  file = f_open( "file.bin", "a" );
  if ( !file )
  {
    return _f_result( 2, 0 );
  }

  file2 = f_open( "file.bin", "a+" ); /*open again*/
  if ( file2 )
  {
    return _f_result( 3, 0 );
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 3, 1 );
  }

  ret = f_close( file2 );
  if ( ret != F_ERR_NOTOPEN )
  {
    return _f_result( 3, 2 );
  }


/*try to creates it w*/
  file = f_open( "file.bin", "w" );
  if ( !file )
  {
    return _f_result( 4, 0 );
  }

/*write 512 times 1*/
  psp_memset( testbuffer, 1, 512 );                           /*set all 1*/
  size = (unsigned short)f_write( testbuffer, 1, 512, file ); /*test write*/
  if ( size != 512 )
  {
    return _f_result( 5, size );
  }

/*go back, and read it*/
  ret = f_rewind( file ); /*back to the begining*/
  if ( ret )
  {
    return _f_result( 6, ret );       /*it should fail*/
  }

  size = (unsigned short)f_read( testbuffer, 1, 512, file ); /*test read*/
  if ( size )
  {
    return _f_result( 7, size );        /*it should fail*/
  }

/*close and check size*/
  size = (unsigned short)f_filelength( "file.bin" );
  if ( size )
  {
    return _f_result( 8, size );        /*has to be zero*/
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 9, ret );
  }

  size = (unsigned short)f_filelength( "file.bin" );
  if ( size != 512 )
  {
    return _f_result( 10, size );
  }

/*try to owerwrites it it*/
  file = f_open( "file.bin", "w+" );
  if ( !file )
  {
    return _f_result( 11, 0 );
  }

/*close and check size*/
  size = (unsigned short)f_filelength( "file.bin" );
  if ( size )
  {
    return _f_result( 12, size );        /*has to be zero*/
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 13, ret );
  }

  size = (unsigned short)f_filelength( "file.bin" );
  if ( size )
  {
    return _f_result( 14, size );
  }



/*test non existing appends	"a" */
  file = f_open( "file.bin", "r+" );
  if ( !file )
  {
    return _f_result( 15, 0 );
  }

/*write 512 times 1*/
  psp_memset( testbuffer, 1, 512 );                           /*set all 1*/
  size = (unsigned short)f_write( testbuffer, 1, 512, file ); /*test write*/
  if ( size != 512 )
  {
    return _f_result( 16, size );
  }

/*go back, and read it*/
  ret = f_rewind( file );                                    /*back to the begining*/
  size = (unsigned short)f_read( testbuffer, 1, 512, file ); /*test read*/
  if ( size != 512 )
  {
    return _f_result( 17, size );             /*it should fail*/
  }

  ret = f_rewind( file ); /*back to the begining*/

/*write 256 times 2*/
  psp_memset( testbuffer, 2, 512 );                           /*set all 2*/
  size = (unsigned short)f_write( testbuffer, 1, 256, file ); /*test write*/
  if ( size != 256 )
  {
    return _f_result( 18, size );
  }

  pos = (unsigned short)f_tell( file );
  if ( pos != 256 )
  {
    return _f_result( 19, pos );            /*position has to be 512*/
  }

  size = (unsigned short)f_filelength( "file.bin" );
  if ( size )
  {
    return _f_result( 20, size );        /*has to be zero*/
  }

/*close and check size*/
  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 21, ret );
  }

  size = (unsigned short)f_filelength( "file.bin" );
  if ( size != 512 )
  {
    return _f_result( 22, size );
  }


/*test non existing appends a+*/
  file = f_open( "file.bin", "a+" );
  if ( !file )
  {
    return _f_result( 23, 0 );
  }

  pos = (unsigned short)f_tell( file );
  if ( pos != 512 )
  {
    return _f_result( 24, pos );            /*position has to be 512*/
  }

/*write 512 times 3*/
  psp_memset( testbuffer, 3, 512 );                           /*set all 3*/
  size = (unsigned short)f_write( testbuffer, 1, 512, file ); /*test write*/
  if ( size != 512 )
  {
    return _f_result( 25, size );
  }

/*go back, and read it*/
  ret = f_rewind( file ); /*back to the begining*/
  if ( ret )
  {
    return _f_result( 26, ret );       /*it should fail*/
  }

  size = (unsigned short)f_read( testbuffer, 1, 512, file ); /*test read*/
  if ( size != 512 )
  {
    return _f_result( 27, size );             /*it should fail*/
  }

  pos = (unsigned short)f_tell( file );
  if ( pos != 512 )
  {
    return _f_result( 28, pos );            /*position has to be 512*/
  }

/*close and check size*/
  size = (unsigned short)f_filelength( "file.bin" );
  if ( size != 512 )
  {
    return _f_result( 29, size );             /*has to be zero*/
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 30, ret );
  }

  size = (unsigned short)f_filelength( "file.bin" );
  if ( size != 1024 )
  {
    return _f_result( 31, size );
  }

/*close again!*/
  ret = f_close( file );
  if ( ret != F_ERR_NOTOPEN )
  {
    return _f_result( 32, pos );
  }

  ret = f_delete( "file.bin" );
  if ( ret )
  {
    return _f_result( 33, ret );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_opening */

static unsigned char f_appending ( void )
{
  F_FILE        * file;
  unsigned short  size, tsize, pos;
  unsigned char   a, b, ret;

  _f_dump( "f_appending" );

  _f_deleteall();

  for ( tsize = 0, a = 0 ; a < 16 ; a++ )
  {
    file = f_open( "ap.bin", "a" );
    if ( !file )
    {
      return _f_result( 1, 0 );
    }

    psp_memset( testbuffer, a, sizeof( testbuffer ) );
    size = (unsigned short)f_write( testbuffer, 1, a + 128, file );
    if ( size != a + 128 )
    {
      return _f_result( 2, size );
    }

    size = (unsigned short)f_filelength( "ap.bin" );
    if ( size != tsize )
    {
      return _f_result( 3, size );
    }

    tsize += a + 128;

    ret = f_close( file );
    if ( ret )
    {
      return _f_result( 4, ret );
    }

    size = (unsigned short)f_filelength( "ap.bin" );
    if ( size != tsize )
    {
      return _f_result( 5, size );
    }
  }

  file = f_open( "ap.bin", "r" );
  if ( !file )
  {
    return _f_result( 6, 0 );
  }

  for ( tsize = 0, a = 0 ; a < 16 ; a++ )
  {
    if ( checkfilecontent( a + 128, (char)a, file ) )
    {
      return _f_result( 7, a );
    }
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 8, ret );
  }

  for ( tsize = 0, a = 0 ; a < 16 ; a++ )
  {
    file = f_open( "ap.bin", "r" );
    if ( !file )
    {
      return _f_result( 9, 0 );
    }

    ret = f_seek( file, tsize, F_SEEK_SET );
    if ( ret )
    {
      return _f_result( 10, ret );
    }

    pos = (unsigned short)f_tell( file );
    if ( pos != tsize )
    {
      return _f_result( 11, pos );
    }

    size = (unsigned short)f_read( testbuffer, 1, a + 128, file );
    if ( size != a + 128 )
    {
      return _f_result( 12, size );
    }

    for ( b = 0 ; b < a + 128 ; b++ )
    {
      if ( testbuffer[b] != (char)a )
      {
        return _f_result( 13, a );
      }
    }

    tsize += a + 128;

    pos = (unsigned short)f_tell( file );
    if ( pos != tsize )
    {
      return _f_result( 13, pos );
    }

    ret = f_close( file );
    if ( ret )
    {
      return _f_result( 14, ret );
    }
  }

  ret = f_close( file );
  if ( ret != F_ERR_NOTOPEN )
  {
    return _f_result( 9, ret );
  }

  ret = f_delete( "ap.bin" );
  if ( ret )
  {
    return _f_result( 14, ret );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_appending */

static unsigned char f_writing ( void )
{
  F_FILE        * file;
  unsigned short  size;
  unsigned char   a, ret;
  F_SPACE         before, after;

  _f_dump( "f_writing" );

  ret = f_getfreespace( &before );
  if ( ret )
  {
    return _f_result( 0, ret );
  }

  for ( a = 0 ; a < 4 ; a++ )
  {
    file = f_open( "wr.bin", "w" );
    if ( !file )
    {
      return _f_result( 1, 0 );
    }

    psp_memset( testbuffer, a, sizeof( testbuffer ) );
    size = (unsigned short)f_write( testbuffer, 1, a * 128, file );
    if ( size != a * 128 )
    {
      return _f_result( 2, size );
    }

    ret = f_close( file );
    if ( ret )
    {
      return _f_result( 3, ret );
    }

    size = (unsigned short)f_filelength( "wr.bin" );
    if ( size != a * 128 )
    {
      return _f_result( 4, size );
    }

    file = f_open( "wr.bin", "r" );
    if ( !file )
    {
      return _f_result( 5, 0 );
    }

    if ( checkfilecontent( a * 128, (char)a, file ) )
    {
      return _f_result( 6, a );
    }

    ret = f_close( file );
    if ( ret )
    {
      return _f_result( 7, ret );
    }
  }


  for ( a = 0 ; a < 4 ; a++ )
  {
    file = f_open( "wr.bin", "w+" );
    if ( !file )
    {
      return _f_result( 8, 0 );
    }

    psp_memset( testbuffer, a, sizeof( testbuffer ) );
    size = (unsigned short)f_write( testbuffer, 1, a * 128, file );
    if ( size != a * 128 )
    {
      return _f_result( 9, size );
    }

    ret = f_close( file );
    if ( ret )
    {
      return _f_result( 10, ret );
    }

    size = (unsigned short)f_filelength( "wr.bin" );
    if ( size != a * 128 )
    {
      return _f_result( 11, size );
    }

    file = f_open( "wr.bin", "r+" );
    if ( !file )
    {
      return _f_result( 12, 0 );
    }

    if ( checkfilecontent( a * 128, (char)a, file ) )
    {
      return _f_result( 13, a );
    }

    ret = f_close( file );
    if ( ret )
    {
      return _f_result( 14, ret );
    }
  }

  ret = f_getfreespace( &after );
  if ( ret )
  {
    return _f_result( 15, ret );
  }

  if ( before.bad != after.bad )
  {
    return _f_result( 16, 0 );
  }

  if ( before.free == after.free )
  {
    return _f_result( 17, 0 );
  }

  if ( before.used == after.used )
  {
    return _f_result( 18, 0 );
  }

  if ( before.total != after.total )
  {
    return _f_result( 19, 0 );
  }

  if ( before.used + before.free != after.used + after.free )
  {
    return _f_result( 20, 0 );
  }

  ret = f_delete( "wr.bin" );
  if ( ret )
  {
    return _f_result( 21, ret );
  }

  ret = f_getfreespace( &after );
  if ( ret )
  {
    return _f_result( 22, ret );
  }

  if ( before.bad != after.bad )
  {
    return _f_result( 23, 0 );
  }

  if ( before.free != after.free )
  {
    return _f_result( 24, 0 );
  }

  if ( before.used != after.used )
  {
    return _f_result( 25, 0 );
  }

  if ( before.total != after.total )
  {
    return _f_result( 26, 0 );
  }

  _f_dump( "passed..." );
  return 0;
} /* f_writing */

static unsigned char f_dots ( void )
{
  unsigned char  ret;
  unsigned char  a, size;
  F_FILE       * file;

  _f_dump( "f_dots" );

  ret = f_mkdir( "/tt" );
  if ( ret )
  {
    return _f_result( 0, ret );
  }

  ret = f_chdir( "/tt" );
  if ( ret )
  {
    return _f_result( 1, ret );
  }

  ret = f_rmdir( "." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 4, ret );
  }

  ret = f_rmdir( ".." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 5, ret );
  }

  ret = f_chdir( "." );
  if ( ret )
  {
    return _f_result( 6, ret );
  }

  ret = _f_checkcwd( f_nameconv( "/tt" ) );
  if ( ret )
  {
    return _f_result( 7, ret );
  }

  ret = f_delete( "." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 8, ret );
  }

  ret = f_delete( ".." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 9, ret );
  }

  ret = f_mkdir( "." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 10, ret );
  }

  ret = f_mkdir( ".." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 11, ret );
  }

  ret = f_mkdir( "..." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 12, ret );
  }

  for ( a = 0 ; a < 6 ; a++ )
  {
    char * mode;
    switch ( a )
    {
      case 0:
        mode = "r";
        break;

      case 1:
        mode = "r+";
        break;

      case 2:
        mode = "w";
        break;

      case 3:
        mode = "w+";
        break;

      case 4:
        mode = "a";
        break;

      case 5:
        mode = "a+";
        break;

      default:
        return _f_result( 13, a );
    } /* switch */

    file = f_open( ".", mode );
    if ( file )
    {
      return _f_result( 14, a );
    }

    file = f_open( "..", mode );
    if ( file )
    {
      return _f_result( 15, a );
    }

    file = f_open( "...", mode );
    if ( file )
    {
      return _f_result( 16, a );
    }
  }

  size = (unsigned char)f_filelength( "." );
  if ( size )
  {
    return _f_result( 17, size );
  }

  size = (unsigned char)f_filelength( ".." );
  if ( size )
  {
    return _f_result( 18, size );
  }

  size = (unsigned char)f_filelength( "..." );
  if ( size )
  {
    return _f_result( 19, size );
  }


  ret = f_chdir( "..." );
  if ( ret != F_ERR_NOTFOUND )
  {
    return _f_result( 20, ret );
  }

  ret = f_chdir( ".." );
  if ( ret )
  {
    return _f_result( 21, ret );
  }

  ret = f_rmdir( "tt" );
  if ( ret )
  {
    return _f_result( 27, ret );
  }


  _f_dump( "passed..." );
  return 0;
} /* f_dots */


typedef struct
{
  unsigned char  MagicNum;
  unsigned char  Line;
  unsigned char  Buf[87];
} struct_TestFileSysEntry;
  #define NUM_OF_RECORDS 10
static unsigned char f_rit ( void )
{
  unsigned char             i;
  unsigned char             ret;
  F_FILE                  * File;
  struct_TestFileSysEntry * Entry = (struct_TestFileSysEntry *)( ( ( (long)testbuffer + 3 ) >> 2 ) << 2 );
  unsigned short            Pos;
  unsigned char             Ch;
  unsigned char             Founded;

  _f_dump( "f_rit" );

  (void)f_delete( "MyTest" );
  File = f_open( "MyTest", "a+" );
  if ( !File )
  {
    return _f_result( 1, 0 );
  }

  /* add records  */
  for ( i = 0 ; i < NUM_OF_RECORDS ; i++ )
  {
    Ch = (char)( i % 10 );
    Entry->MagicNum = 0xbc;
    Entry->Line = i;
    Entry->Buf[0] = Ch;
    Entry->Buf[10] = (unsigned char)( Ch + 1 );

    if ( F_NO_ERROR != f_seek( File, 0, F_SEEK_END ) )
    {
      return _f_result( 2, 0 ); /* Fail, could not go to the end of the file */
    }

    if ( sizeof( struct_TestFileSysEntry ) != f_write( (void *)Entry, 1, sizeof( struct_TestFileSysEntry ), File ) )
    {
      return _f_result( 3, 0 ); /* Fail, could not write new entry */
    }

    Pos = (unsigned short)f_tell( File );
    if ( ( ( Pos / sizeof( struct_TestFileSysEntry ) ) - 1 ) != i )
    {
      return _f_result( 4, 0 ); /* Fail, wrong file position */
    }

    if ( F_NO_ERROR != f_seek( File, (long)( Pos - sizeof( struct_TestFileSysEntry ) ), F_SEEK_SET ) )
    {
      return _f_result( 5, 0 ); /* Fail, could not go to new entry position */
    }

    if ( sizeof( struct_TestFileSysEntry ) != f_read( (void *)Entry, 1, sizeof( struct_TestFileSysEntry ), File ) )
    {
      return _f_result( 6, 0 ); /* Fail, could not read the new entry */
    }

    if ( ( Entry->MagicNum != 0xbc ) || ( Entry->Line != (int)i ) || ( Entry->Buf[0] != Ch ) || ( Entry->Buf[10] != Ch + 1 ) )
    {
      return _f_result( 7, 0 ); /*Fail, the new entry is corrupted"*/
    }
  }

  ret = f_close( File );
  if ( ret )
  {
    return _f_result( 8, ret );
  }


  /*Open file again*/
  File = f_open( "MyTest", "a+" );
  if ( !File )
  {
    return _f_result( 9, 0 );
  }

  /* read records  */
  for ( i = 0 ; i < NUM_OF_RECORDS ; i++ )
  {
    Ch = (char)( i % 10 );

    if ( F_NO_ERROR != f_seek( File, 0, F_SEEK_SET ) )
    {
      return _f_result( 10, 0 ); /* Fail, could not go to the start of the file */
    }

    Founded = 0;
    while ( sizeof( struct_TestFileSysEntry ) == f_read( (void *)Entry, 1, sizeof( struct_TestFileSysEntry ), File ) )
    {
      if ( ( Entry->MagicNum == 0xbc )
          && ( Entry->Line == (int)i )
          && ( Entry->Buf[0] == Ch )
          && ( Entry->Buf[10] == Ch + 1 ) )
      {
        Founded = 1;
        break;
      }
    }

    if ( !Founded )
    {
      return _f_result( 11, i );      /* Entry not founded */
    }
  }

  ret = f_close( File );
  if ( ret )
  {
    return _f_result( 12, ret );
  }


  ret = f_delete( "MyTest" );
  if ( ret )
  {
    return _f_result( 13, ret );
  }

  _f_dump( "passed..." );

  return 0;
} /* f_rit */




static unsigned char f_truncating ( void )
{
  F_FILE       * file;
  unsigned long  size;
  unsigned char  ret;

  _f_dump( "f_truncating" );

  file = f_open( "test.bin", "w+" );
  if ( !file )
  {
    return _f_result( 0, 0 );
  }

  (void)psp_memset( testbuffer, 1, F_MAX_SEEK_TEST );
  size = (unsigned long)f_write( testbuffer, 1, F_MAX_SEEK_TEST, file );
  if ( size != F_MAX_SEEK_TEST )
  {
    return _f_result( 1, size );
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 2, ret );
  }

  file = f_truncate( "test.bin", F_MAX_SEEK_TEST - 4 );
  if ( !file )
  {
    return _f_result( 3, 0 );
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 4, ret );
  }

  size = (unsigned long)f_filelength( "test.bin" );
  if ( size != F_MAX_SEEK_TEST - 4 )
  {
    return _f_result( 5, size );
  }


  file = f_truncate( "test.bin", F_MAX_SEEK_TEST );
  if ( !file )
  {
    return _f_result( 3, 0 );
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 4, ret );
  }

  size = (unsigned long)f_filelength( "test.bin" );
  if ( size != F_MAX_SEEK_TEST )
  {
    return _f_result( 5, size );
  }


  file = f_truncate( "test.bin", ( F_MAX_SEEK_TEST / 2 ) - 92 );
  if ( !file )
  {
    return _f_result( 6, 0 );
  }

  (void)psp_memset( testbuffer, 2, 92 );
  size = (unsigned long)f_write( testbuffer, 1, 92, file );
  if ( size != 92 )
  {
    return _f_result( 7, size );
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 8, ret );
  }

  size = (unsigned long)f_filelength( "test.bin" );
  if ( size != ( F_MAX_SEEK_TEST / 2 ) )
  {
    return _f_result( 9, size );
  }


  file = f_truncate( "test.bin", 1 );
  if ( !file )
  {
    return _f_result( 10, 0 );
  }

  (void)psp_memset( testbuffer, 3, 2 );
  size = (unsigned long)f_write( testbuffer, 1, 2, file );
  if ( size != 2 )
  {
    return _f_result( 11, size );
  }

  ret = f_close( file );
  if ( ret )
  {
    return _f_result( 12, ret );
  }

  size = (unsigned long)f_filelength( "test.bin" );
  if ( size != 3 )
  {
    return _f_result( 13, size );
  }



  _f_dump( "passed..." );
  return 0;
} /* f_truncating */


void f_dotest ( unsigned char t )
{
  _f_dump( "File system test started..." );
  _f_dump( "WARNING: The contents of your drive will be destroyed!\n" );

  (void)_f_poweron();

  switch ( t )
  {
    case 0:
    case 1:
      (void)f_formatting();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 2:
      (void)f_dirtest();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 3:
      (void)f_findingtest();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 4:
      (void)f_powerfail();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 5:
      (void)f_seeking( 128 );
      if ( t )
      {
        break;
      }

  #if ( F_MAX_SEEK_TEST > 128 )

    /* fall through */
    case 6:
      (void)f_seeking( 256 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 256 )

    /* fall through */
    case 7:
      (void)f_seeking( 512 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 512 )

    /* fall through */
    case 8:
      (void)f_seeking( 1024 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 1024 )

    /* fall through */
    case 9:
      (void)f_seeking( 2048 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 2048 )

    /* fall through */
    case 10:
      (void)f_seeking( 4096 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 4096 )

    /* fall through */
    case 11:
      (void)f_seeking( 8192 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 8192 )

    /* fall through */
    case 12:
      (void)f_seeking( 16384 );
      if ( t )
      {
        break;
      }

  #endif
  #if ( F_MAX_SEEK_TEST > 16384 )

    /* fall through */
    case 13:
      (void)f_seeking( 32768 );
      if ( t )
      {
        break;
      }

  #endif

    /* fall through */
    case 14:
      (void)f_opening();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 15:
      (void)f_appending();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 16:
      (void)f_writing();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 17:
      (void)f_dots();
      if ( t )
      {
        break;
      }


    /* fall through */
    case 18:
      (void)f_rit();
      if ( t )
      {
        break;
      }

    case 19:
      (void)f_truncating();
      if ( t )
      {
        break;
      }

      break;
  } /* switch */

  _f_dump( "End of tests..." );
} /* f_dotest */



/****************************************************************************
 *
 * end of test.c
 *
 ***************************************************************************/
#endif  /*_TEST_C_*/
