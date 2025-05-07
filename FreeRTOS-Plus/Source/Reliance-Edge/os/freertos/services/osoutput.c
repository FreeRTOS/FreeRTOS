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
 *  @brief Implements outputting a character string.
 */
#include <redfs.h>

#if REDCONF_OUTPUT == 1

    #include <redosdeviations.h>


/** @brief Write a string to a user-visible output location.
 *
 *  Write a null-terminated string to the serial port, console, terminal, or
 *  other display device, such that the text is visible to the user.
 *
 *  @param pszString    A null-terminated string.
 */
    void RedOsOutputString( const char * pszString )
    {
        if( pszString == NULL )
        {
            REDERROR();
        }
        else
        {
            uint32_t ulIdx = 0U;

            while( pszString[ ulIdx ] != '\0' )
            {
                OUTPUT_CHARACTER( pszString[ ulIdx ] );

                /*  Serial output often requires a \r to print newlines correctly.
                 */
                if( pszString[ ulIdx ] == '\n' )
                {
                    OUTPUT_CHARACTER( '\r' );
                }

                ulIdx++;
            }
        }
    }

#endif /* if REDCONF_OUTPUT == 1 */
