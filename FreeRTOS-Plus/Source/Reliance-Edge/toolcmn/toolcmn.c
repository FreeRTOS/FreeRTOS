/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----

                   Copyright (c) 2014-2015 Datalight, Inc.
                       All Rights Reserved Worldwide.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; use version 2 of the License.

    This program is distributed in the hope that it will be useful,
    but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/
/*  Businesses and individuals that for commercial or other reasons cannot
    comply with the terms of the GPLv2 license may obtain a commercial license
    before incorporating Reliance Edge into proprietary software for
    distribution in any form.  Visit http://www.datalight.com/reliance-edge for
    more information.
*/
/** @file
    @brief Implements common-code utilities for tools and tests.
*/
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>

#include <redfs.h>
#include <redcoreapi.h>
#include <redvolume.h>
#include <redtoolcmn.h>


/** @brief Convert a string into a volume number.

    In a POSIX-like configuration, @p pszVolume can either be a volume number or
    a volume path prefix.  In case of ambiguity, the volume number of a matching
    path prefix takes precedence.

    In an FSE configuration, @p pszVolume can be a volume number.

    @param pszVolume    The volume string.

    @return On success, returns the volume number; on failure, returns
            #REDCONF_VOLUME_COUNT.
*/
uint8_t RedFindVolumeNumber(
    const char     *pszVolume)
{
    unsigned long   ulNumber;
    const char     *pszEndPtr;
    uint8_t         bVolNum = REDCONF_VOLUME_COUNT;
  #if REDCONF_API_POSIX == 1
    uint8_t         bIndex;
  #endif

    /*  Determine if pszVolume can be interpreted as a volume number.
    */
    errno = 0;
    ulNumber = strtoul(pszVolume, (char **)&pszEndPtr, 10);
    if((errno == 0) && (ulNumber != ULONG_MAX) && (pszEndPtr[0U] == '\0') && (ulNumber < REDCONF_VOLUME_COUNT))
    {
        bVolNum = (uint8_t)ulNumber;
    }

  #if REDCONF_API_POSIX == 1
    /*  Determine if pszVolume is a valid path prefix.
    */
    for(bIndex = 0U; bIndex < REDCONF_VOLUME_COUNT; bIndex++)
    {
        if(strcmp(gaRedVolConf[bIndex].pszPathPrefix, pszVolume) == 0)
        {
            break;
        }
    }

    if(bIndex < REDCONF_VOLUME_COUNT)
    {
        /*  Edge case: It is technically possible for pszVolume to be both a
            valid volume number and a valid volume prefix, for different
            volumes.  For example, if pszVolume is "2", that would be recognized
            as volume number 2 above.  But if "2" is the (poorly chosen) path
            prefix for volume number 4, that would also be matched.  Since the
            POSIX-like API is primarily name based, and the ability to use
            volume numbers with this tool is just a convenience, the volume
            prefix takes precedence.
        */
        bVolNum = bIndex;
    }
  #endif

    return bVolNum;
}

