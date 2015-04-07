/*
 * FreeRTOS+FAT SL V1.0.1 (C) 2014 HCC Embedded
 *
 * FreeRTOS+FAT SL is an complementary component provided to Real Time Engineers
 * Ltd. by HCC Embedded for use with FreeRTOS.  It is not, in itself, part of
 * the FreeRTOS kernel.  FreeRTOS+FAT SL is licensed separately from FreeRTOS,
 * and uses a different license to FreeRTOS.  FreeRTOS+FAT SL uses a dual
 * license model, information on which is provided below:
 *
 * - Open source licensing -
 * FreeRTOS+FAT SL is a free download and may be used, modified and distributed
 * without charge provided the user adheres to version two of the GNU General
 * Public license (GPL) and does not remove the copyright notice or this text.
 * The GPL V2 text is available on the gnu.org web site, and on the following
 * URL: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * - Commercial licensing -
 * Businesses and individuals who wish to incorporate FreeRTOS+FAT SL into
 * proprietary software for redistribution in any form must first obtain a
 * commercial license - and in-so-doing support the maintenance, support and
 * further development of the FreeRTOS+FAT SL product.  Commercial licenses can
 * be obtained from http://shop.freertos.org and do not require any source files
 * to be changed.
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

#ifndef _CONFIG_MDRIVER_RAM_H_
#define _CONFIG_MDRIVER_RAM_H_

#include "../version/ver_mdriver_ram.h"
#if VER_MDRIVER_RAM_MAJOR != 1 || VER_MDRIVER_RAM_MINOR != 2
 #error Incompatible MDRIVER_RAM version number!
#endif

#define MDRIVER_RAM_SECTOR_SIZE   512       /* Sector size */

#define MDRIVER_RAM_VOLUME0_SIZE  (64 * 1024) /* defintion for size of ramdrive0 */

#define MDRIVER_MEM_LONG_ACCESS   1         /* set this value to 1 if 32bit access available */

#endif /* ifndef _CONFIG_MDRIVER_RAM_H_ */

