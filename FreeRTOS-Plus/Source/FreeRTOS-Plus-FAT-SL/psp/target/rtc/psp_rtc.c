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

#include <stdint.h>
#include <stddef.h>
#include "../../include/psp_rtc.h"

#include "../../../version/ver_psp_rtc.h"
#if VER_PSP_RTC_MAJOR != 1
 #error "VER_PSP_RTC_MAJOR invalid"
#endif
#if VER_PSP_RTC_MINOR != 0
 #error "VER_PSP_RTC_MINOR invalid"
#endif


/****************************************************************************
 *
 * psp_getcurrenttimedate
 *
 * Need to be ported depending on system, it retreives the
 * current time and date.
 * Please take care of correct roll-over handling.
 * Roll-over problem is to read a date at 23.59.59 and then reading time at
 * 00:00.00.
 *
 * INPUT
 *
 * p_timedate - pointer where to store time and date
 *
 ***************************************************************************/
void psp_getcurrenttimedate ( t_psp_timedate * p_timedate )
{
  if ( p_timedate != NULL )
  {
    p_timedate->sec = 0;
    p_timedate->min = 0;
    p_timedate->hour = 12u;

    p_timedate->day = 1u;
    p_timedate->month = 1u;
    p_timedate->year = 1980u;
  }
} /* psp_getcurrenttimedate */

