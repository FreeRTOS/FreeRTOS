/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----
 *
 *                 Copyright (c) 2014-2015 Datalight, Inc.
 *                     All Rights Reserved Worldwide.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; use version 2 of the License.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
 *  of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*  Businesses and individuals that for commercial or other reasons cannot
 *  comply with the terms of the GPLv2 license may obtain a commercial license
 *  before incorporating Reliance Edge into proprietary software for
 *  distribution in any form.  Visit http://www.datalight.com/reliance-edge for
 *  more information.
 */

/** @file
 *  @brief Implements real-time clock functions.
 */
#include <redfs.h>


/** @brief Initialize the real time clock.
 *
 *  The behavior of calling this function when the RTC is already initialized
 *  is undefined.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0   Operation was successful.
 */
REDSTATUS RedOsClockInit( void )
{
    return 0;
}


/** @brief Uninitialize the real time clock.
 *
 *  The behavior of calling this function when the RTC is not initialized is
 *  undefined.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0   Operation was successful.
 */
REDSTATUS RedOsClockUninit( void )
{
    return 0;
}


/** @brief Get the date/time.
 *
 *  The behavior of calling this function when the RTC is not initialized is
 *  undefined.
 *
 *  @return The number of seconds since January 1, 1970 excluding leap seconds
 *          (in other words, standard Unix time).  If the resolution or epoch
 *          of the RTC is different than this, the implementation must convert
 *          it to the expected representation.
 */
uint32_t RedOsClockGetTime( void )
{
    /*  FreeRTOS does not provide an RTC abstraction since most of the systems
     *  it targets have no RTC hardware.  If your hardware includes an RTC that
     *  you would like to use, this function must be customized.
     */
    return 0;
}
