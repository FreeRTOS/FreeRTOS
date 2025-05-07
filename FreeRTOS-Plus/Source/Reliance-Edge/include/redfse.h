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
 *  @brief Interface for the Reliance Edge FSE API.
 *
 *  The FSE (File Systems Essentials) API is a minimalist file system API
 *  intended for simple use cases with a fixed number of statically-defined
 *  files.  It does not support creating or deleting files dynamically.  Files
 *  are referenced by a fixed file number, rather than by name; there are no
 *  file names and no directories.  There are also no file handles: files are
 *  not opened or closed, and file offsets are given explicitly.
 *
 *  If the FSE API is too limited to meet the needs of your application,
 *  consider using the more feature-rich POSIX-like file system API instead.
 */
#ifndef REDFSE_H
    #define REDFSE_H

/*  This header is intended for application use; some applications are written
 *  in C++.
 */
    #ifdef __cplusplus
    extern "C" {
    #endif

    #include <redconf.h>

    #if REDCONF_API_FSE == 1

        #include <redtypes.h>
        #include "redapimacs.h"
        #include "rederrno.h"


/** @brief First valid file number.
 *
 *  This macro can be used to statically define file numbers for given files,
 *  as in the below example:
 *
 *  ~~~{.c}
 #define LOG_FILE        (RED_FILENUM_FIRST_VALID)
 #define DATABASE_FILE   (RED_FILENUM_FIRST_VALID + 1U)
 #define ICON1_FILE      (RED_FILENUM_FIRST_VALID + 2U)
 #define ICON2_FILE      (RED_FILENUM_FIRST_VALID + 3U)
 *  ~~~
 */
        #define RED_FILENUM_FIRST_VALID    ( 2U )


        REDSTATUS RedFseInit( void );
        REDSTATUS RedFseUninit( void );
        REDSTATUS RedFseMount( uint8_t bVolNum );
        REDSTATUS RedFseUnmount( uint8_t bVolNum );
        #if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_FORMAT == 1 )
            REDSTATUS RedFseFormat( uint8_t bVolNum );
        #endif
        int32_t RedFseRead( uint8_t bVolNum,
                            uint32_t ulFileNum,
                            uint64_t ullFileOffset,
                            uint32_t ulLength,
                            void * pBuffer );
        #if REDCONF_READ_ONLY == 0
            int32_t RedFseWrite( uint8_t bVolNum,
                                 uint32_t ulFileNum,
                                 uint64_t ullFileOffset,
                                 uint32_t ulLength,
                                 const void * pBuffer );
        #endif
        #if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_TRUNCATE == 1 )
            REDSTATUS RedFseTruncate( uint8_t bVolNum,
                                      uint32_t ulFileNum,
                                      uint64_t ullNewFileSize );
        #endif
        int64_t RedFseSizeGet( uint8_t bVolNum,
                               uint32_t ulFileNum );
        #if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_TRANSMASKSET == 1 )
            REDSTATUS RedFseTransMaskSet( uint8_t bVolNum,
                                          uint32_t ulEventMask );
        #endif
        #if REDCONF_API_FSE_TRANSMASKGET == 1
            REDSTATUS RedFseTransMaskGet( uint8_t bVolNum,
                                          uint32_t * pulEventMask );
        #endif
        #if REDCONF_READ_ONLY == 0
            REDSTATUS RedFseTransact( uint8_t bVolNum );
        #endif

    #endif /* REDCONF_API_FSE == 1 */


    #ifdef __cplusplus
}
    #endif

#endif /* ifndef REDFSE_H */
