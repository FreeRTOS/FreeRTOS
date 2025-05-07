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
 */
#ifndef REDCOREAPI_H
#define REDCOREAPI_H


#include <redstat.h>


REDSTATUS RedCoreInit( void );
REDSTATUS RedCoreUninit( void );

REDSTATUS RedCoreVolSetCurrent( uint8_t bVolNum );

#if FORMAT_SUPPORTED
    REDSTATUS RedCoreVolFormat( void );
#endif
#if REDCONF_CHECKER == 1
    REDSTATUS RedCoreVolCheck( void );
#endif
REDSTATUS RedCoreVolMount( void );
REDSTATUS RedCoreVolUnmount( void );
#if REDCONF_READ_ONLY == 0
    REDSTATUS RedCoreVolTransact( void );
#endif
#if REDCONF_API_POSIX == 1
    REDSTATUS RedCoreVolStat( REDSTATFS * pStatFS );
#endif

#if ( REDCONF_READ_ONLY == 0 ) && ( ( REDCONF_API_POSIX == 1 ) || ( REDCONF_API_FSE_TRANSMASKSET == 1 ) )
    REDSTATUS RedCoreTransMaskSet( uint32_t ulEventMask );
#endif
#if ( REDCONF_API_POSIX == 1 ) || ( REDCONF_API_FSE_TRANSMASKGET == 1 )
    REDSTATUS RedCoreTransMaskGet( uint32_t * pulEventMask );
#endif

#if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_POSIX == 1 )
    REDSTATUS RedCoreCreate( uint32_t ulPInode,
                             const char * pszName,
                             bool fDir,
                             uint32_t * pulInode );
#endif
#if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_POSIX == 1 ) && ( REDCONF_API_POSIX_LINK == 1 )
    REDSTATUS RedCoreLink( uint32_t ulPInode,
                           const char * pszName,
                           uint32_t ulInode );
#endif
#if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_POSIX == 1 ) && ( ( REDCONF_API_POSIX_UNLINK == 1 ) || ( REDCONF_API_POSIX_RMDIR == 1 ) )
    REDSTATUS RedCoreUnlink( uint32_t ulPInode,
                             const char * pszName );
#endif
#if REDCONF_API_POSIX == 1
    REDSTATUS RedCoreLookup( uint32_t ulPInode,
                             const char * pszName,
                             uint32_t * pulInode );
#endif
#if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_POSIX == 1 ) && ( REDCONF_API_POSIX_RENAME == 1 )
    REDSTATUS RedCoreRename( uint32_t ulSrcPInode,
                             const char * pszSrcName,
                             uint32_t ulDstPInode,
                             const char * pszDstName );
#endif
#if REDCONF_API_POSIX == 1
    REDSTATUS RedCoreStat( uint32_t ulInode,
                           REDSTAT * pStat );
#endif
#if REDCONF_API_FSE == 1
    REDSTATUS RedCoreFileSizeGet( uint32_t ulInode,
                                  uint64_t * pullSize );
#endif

REDSTATUS RedCoreFileRead( uint32_t ulInode,
                           uint64_t ullStart,
                           uint32_t * pulLen,
                           void * pBuffer );
#if REDCONF_READ_ONLY == 0
    REDSTATUS RedCoreFileWrite( uint32_t ulInode,
                                uint64_t ullStart,
                                uint32_t * pulLen,
                                const void * pBuffer );
#endif
#if TRUNCATE_SUPPORTED
    REDSTATUS RedCoreFileTruncate( uint32_t ulInode,
                                   uint64_t ullSize );
#endif

#if ( REDCONF_API_POSIX == 1 ) && ( REDCONF_API_POSIX_READDIR == 1 )
    REDSTATUS RedCoreDirRead( uint32_t ulInode,
                              uint32_t * pulPos,
                              char * pszName,
                              uint32_t * pulInode );
#endif


#endif /* ifndef REDCOREAPI_H */
