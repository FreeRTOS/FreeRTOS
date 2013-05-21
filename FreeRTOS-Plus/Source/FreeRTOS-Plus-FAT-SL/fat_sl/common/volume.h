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

#ifndef __VOLUME_H
#define __VOLUME_H

#include "config_fat_sl.h"

#include "../../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

#ifdef __cplusplus
extern "C" {
#endif


typedef struct
{
  unsigned char  sector_per_cluster;
  unsigned char  number_of_FATs;
  unsigned char  media_descriptor;
  unsigned long  rootcluster;
  unsigned long  sector_per_FAT;
  unsigned long  sector_per_FAT32;
  unsigned long  serial_number;
} F_BOOTRECORD;


typedef struct
{
  unsigned long  sector; /*start sector*/
  unsigned long  num;    /*number of sectors*/
} F_SECTOR;


typedef struct
{
  unsigned char  state;
  F_BOOTRECORD   bootrecord;
  F_SECTOR       firstfat;
  F_SECTOR       root;
  F_SECTOR       _tdata;

  unsigned long  actsector;
  unsigned long  fatsector;

  unsigned long  lastalloccluster;
  unsigned char  modified;
  char           cwd[F_MAXPATH]; /*current working folder in this volume*/
  unsigned char  mediatype;
  unsigned long  maxcluster;
} F_VOLUME;


enum
{
/*  0 */
  F_STATE_NONE,

/*  1 */ F_STATE_NEEDMOUNT,

/*  2 */ F_STATE_WORKING
};


extern F_VOLUME  gl_volume;
extern F_FILE    gl_file;
extern char      gl_sector[F_SECTOR_SIZE]; /* actual sector */

unsigned char _f_getvolume ( void );

#ifdef __cplusplus
}
#endif

#endif /* ifndef __VOLUME_H */
