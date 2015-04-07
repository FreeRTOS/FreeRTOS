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

#ifndef _API_MDRIVER_H_
#define _API_MDRIVER_H_

#include "../version/ver_mdriver.h"
#if VER_MDRIVER_MAJOR != 1 || VER_MDRIVER_MINOR != 0
 #error Incompatible MDRIVER version number!
#endif

#ifdef __cplusplus
extern "C" {
#endif


typedef struct
{
  unsigned short  number_of_cylinders;
  unsigned short  sector_per_track;
  unsigned short  number_of_heads;
  unsigned long   number_of_sectors;
  unsigned char   media_descriptor;

  unsigned short  bytes_per_sector;
} F_PHY;

/* media descriptor to be set in getphy function */
#define F_MEDIADESC_REMOVABLE 0xf0
#define F_MEDIADESC_FIX       0xf8

/* return bitpattern for driver getphy function */
#define F_ST_MISSING          0x00000001
#define F_ST_CHANGED          0x00000002
#define F_ST_WRPROTECT        0x00000004

/* Driver definitions */
typedef struct F_DRIVER  F_DRIVER;

typedef int           ( *F_WRITESECTOR )( F_DRIVER * driver, void * data, unsigned long sector );
typedef int           ( *F_READSECTOR )( F_DRIVER * driver, void * data, unsigned long sector );
typedef int           ( *F_GETPHY )( F_DRIVER * driver, F_PHY * phy );
typedef long          ( *F_GETSTATUS )( F_DRIVER * driver );
typedef void          ( *F_RELEASE )( F_DRIVER * driver );

typedef struct F_DRIVER
{
  unsigned long  user_data;     /* user defined data */
  void         * user_ptr;      /* user define pointer */

  /* driver functions */
  F_WRITESECTOR          writesector;
  F_READSECTOR           readsector;
  F_GETPHY               getphy;
  F_GETSTATUS            getstatus;
  F_RELEASE              release;
} _F_DRIVER;

typedef F_DRIVER *( *F_DRIVERINIT )( unsigned long driver_param );

#ifdef __cplusplus
}
#endif

#endif /* _API_MDRIVER_H_ */


