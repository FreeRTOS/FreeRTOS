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

#ifndef __TEST_H
#define __TEST_H

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

#ifdef __cplusplus
extern "C" {
#endif


/*
** Maximum size for seek test.
** Options: 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768
*/
#define F_MAX_SEEK_TEST 16384


/*
** Defines media type for testing.
** Options: F_FAT12_MEDIA, F_FAT16_MEDIA
*/
#define F_FAT_TYPE      F_FAT12_MEDIA


/*
** Start filesystem test.
** Parameter:
**	0  - run all the tests
**
**	2  - directory
**	3  - find
**
**	5* - seek 128
**	6* - seek 256
**	7* - seek 512
**	8* - seek 1024
**	9* - seek 2048
**	10*- seek 4096
**	11*- seek 8192
**	12*- seek 16384
**	13*- seek 32768
**	14 - open
**	15 - append
**	16 - write
**	17 - dots
**	18 - rit
**  *Note that only seek tests allowed by F_MAX_SEEK_TEST are executed.
**
**  The following defines are required for the specific test:
**			                  1 1 1 1 1 1 1 1 1
**			  2 3   5 6 7 8 9 0 1 2 3 4 5 6 7 8
** F_CHDIR		  x x   - - - - - - - - - - x - x -
** F_MKDIR		  x x   - - - - - - - - - - - - x -
** F_RMDIR		  x x   - - - - - - - - - - x - x -
** F_DELETE		  x x   x x x x x x x x x x x x x x
** F_FILELENGTH		  - -   x x x x x x x x x x x x - -
** F_FINDING		  x x   - - - - - - - - - - x - - -
** F_TELL		  - -   x x x x x x x x x x x x - x
** F_REWIND		  - -   - - - - - - - - - x - - - -
** F_EOF		  - -   x x x x x x x x x - - x - -
** F_SEEK		  - -   x x x x x x x x x - x x - x
** F_WRITE		  - -   x x x x x x x x x x x x - x
** F_WRITING		  x x   x x x x x x x x x x x x x x
** F_DIRECTORIES	  x x   - - - - - - - - - - x - x -
** F_CHECKNAME		  x -   - - - - - - - - - - - - x -
*/
void f_dotest ( unsigned char );

#ifdef __cplusplus
}
#endif

#endif /* ifndef __TEST_H */


