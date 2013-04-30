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

#ifndef _CONFIG_FAT_SL_H
#define _CONFIG_FAT_SL_H

#include "../version/ver_fat_sl.h"
#if VER_FAT_SL_MAJOR != 3 || VER_FAT_SL_MINOR != 2
 #error Incompatible FAT_SL version number!
#endif

#include "../api/api_mdriver.h"

#ifdef __cplusplus
extern "C" {
#endif


/**************************************************************************
**
**  FAT SL user settings
**
**************************************************************************/
#define F_SECTOR_SIZE           512u  /* Disk sector size. */
#define F_FS_THREAD_AWARE       1     /* Set to one if the file system will be access from more than one task. */
#define F_MAXPATH               64    /* Maximum length a file name (including its full path) can be. */
#define F_MAX_LOCK_WAIT_TICKS   20    /* The maximum number of RTOS ticks to wait when attempting to obtain a lock on the file system when F_FS_THREAD_AWARE is set to 1. */

#ifdef __cplusplus
}
#endif

#endif /* _CONFIG_FAT_SL_H */

