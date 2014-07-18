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

#include "../../api/api_mdriver_ram.h"
#include "config_mdriver_ram.h"
#include "../../psp/include/psp_string.h"

#include "../../version/ver_mdriver_ram.h"
#if VER_MDRIVER_RAM_MAJOR != 1 || VER_MDRIVER_RAM_MINOR != 2
 #error Incompatible MDRIVER_RAM version number!
#endif

/* The array used as the RAM disk storage. */
static char  ramdrv[ MDRIVER_RAM_VOLUME0_SIZE ];

/* The F_DRIVER structure that is filled with the RAM disk versions of the read
sector, write sector, etc. functions. */
static F_DRIVER  t_driver;

static const unsigned long maxsector = MDRIVER_RAM_VOLUME0_SIZE / MDRIVER_RAM_SECTOR_SIZE;

/* Disk not initialized yet. */
static char in_use = 0;


/****************************************************************************
 * Read one sector
 ***************************************************************************/
static int ram_readsector ( F_DRIVER * driver, void * data, unsigned long sector )
{
  long       len;
  char     * d = (char *)data;
  char     * s;

  /* Not used. */
  ( void ) driver;

  /* Check for valid sector. */
  if ( sector >= maxsector )
  {
    return MDRIVER_RAM_ERR_SECTOR;
  }

  if( in_use == 0 )
  {
    return MDRIVER_RAM_ERR_NOTAVAILABLE;
  }

  /* Locate offset into RAM disk for sector. */
  s = ramdrv;
  s += sector * MDRIVER_RAM_SECTOR_SIZE;
  len = MDRIVER_RAM_SECTOR_SIZE;

#if MDRIVER_MEM_LONG_ACCESS
  if ( ( !( len & 3 ) ) && ( !( ( (long)d ) & 3 ) ) && ( !( ( (long)s ) & 3 ) ) )
  {
    long * dd = (long *)d;
    long * ss = (long *)s;
    len >>= 2;
	/* Read words. */
    while ( len-- )
    {
      *dd++ = *ss++;
    }

    return MDRIVER_RAM_NO_ERROR;
  }

#endif /* if MDRIVER_MEM_LONG_ACCESS */

  /* Read bytes. */
  while ( len-- )
  {
    *d++ = *s++;
  }

  return MDRIVER_RAM_NO_ERROR;
}

/****************************************************************************
 * Write one sector
 ***************************************************************************/
static int ram_writesector ( F_DRIVER * driver, void * data, unsigned long sector )
{
  long       len;
  char     * s = (char *)data;
  char     * d;

  /* Not used. */
  ( void ) driver;

  /* Check for valid sector. */
  if ( sector >= maxsector )
  {
    return MDRIVER_RAM_ERR_SECTOR;
  }

  if( in_use == 0 )
  {
	  return MDRIVER_RAM_ERR_NOTAVAILABLE;
  }

  /* Locate offset into RAM disk for sector. */
  d = ramdrv;
  d += sector * MDRIVER_RAM_SECTOR_SIZE;
  len = MDRIVER_RAM_SECTOR_SIZE;

#if MDRIVER_MEM_LONG_ACCESS
  if ( ( !( len & 3 ) ) && ( !( ( (long)d ) & 3 ) ) && ( !( ( (long)s ) & 3 ) ) )
  {
    long * dd = (long *)d;
    long * ss = (long *)s;
    len >>= 2;

	/* Write words. */
    while ( len-- )
    {
      *dd++ = *ss++;
    }

    return MDRIVER_RAM_NO_ERROR;
  }
#endif /* if MDRIVER_MEM_LONG_ACCESS */

  /* Write bytes. */
  while ( len-- )
  {
    *d++ = *s++;
  }

  return MDRIVER_RAM_NO_ERROR;
}


/****************************************************************************
 *
 * ram_getphy
 *
 * determinate ramdrive physicals
 *
 * INPUTS
 *
 * driver - driver structure
 * phy - this structure has to be filled with physical information
 *
 * RETURNS
 *
 * error code or zero if successful
 *
 ***************************************************************************/
static int ram_getphy ( F_DRIVER * driver, F_PHY * phy )
{
  /* Not used. */
  ( void ) driver;

  phy->number_of_sectors = maxsector;
  phy->bytes_per_sector = MDRIVER_RAM_SECTOR_SIZE;

  return MDRIVER_RAM_NO_ERROR;
}


/****************************************************************************
 *
 * ram_release
 *
 * Releases a drive
 *
 * INPUTS
 *
 * driver_param - driver parameter
 *
 ***************************************************************************/
static void ram_release ( F_DRIVER * driver )
{
  /* Not used. */
  ( void ) driver;

  /* Disk no longer in use. */
  in_use = 0;
}


/****************************************************************************
 *
 * ram_initfunc
 *
 * this init function has to be passed for highlevel to initiate the
 * driver functions
 *
 * INPUTS
 *
 * driver_param - driver parameter
 *
 * RETURNS
 *
 * driver structure pointer
 *
 ***************************************************************************/
F_DRIVER * ram_initfunc ( unsigned long driver_param )
{
  ( void ) driver_param;

  if( in_use )
    return NULL;

  (void)psp_memset( &t_driver, 0, sizeof( F_DRIVER ) );

  t_driver.readsector = ram_readsector;
  t_driver.writesector = ram_writesector;
  t_driver.getphy = ram_getphy;
  t_driver.release = ram_release;

  in_use = 1;

  return &t_driver;
} /* ram_initfunc */

