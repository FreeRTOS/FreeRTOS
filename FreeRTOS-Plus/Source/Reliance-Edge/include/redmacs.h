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
#ifndef REDMACS_H
#define REDMACS_H


#ifndef NULL
    #define NULL    ( ( void * ) 0 )
#endif

#ifndef UINT8_MAX
    #define UINT8_MAX     ( 0xFFU )
#endif
#ifndef UINT16_MAX
    #define UINT16_MAX    ( 0xFFFFU )
#endif
#ifndef UINT32_MAX
    #define UINT32_MAX    ( 0xFFFFFFFFU )
#endif
#ifndef UINT64_MAX
    #define UINT64_MAX    UINT64_SUFFIX( 0xFFFFFFFFFFFFFFFF )
#endif
#ifndef INT32_MAX
    #define INT32_MAX     ( 0x7FFFFFFF )
#endif
#ifndef INT64_MAX
    #define INT64_MAX     INT64_SUFFIX( 0x7FFFFFFFFFFFFFFF )
#endif

#ifndef true
    #define true             ( 1 )
#endif
#ifndef false
    #define false            ( 0 )
#endif

#define SECTOR_SIZE_MIN      ( 256U )

#if   REDCONF_BLOCK_SIZE == 256U
    #define BLOCK_SIZE_P2    8U
#elif REDCONF_BLOCK_SIZE == 512U
    #define BLOCK_SIZE_P2    9U
#elif REDCONF_BLOCK_SIZE == 1024U
    #define BLOCK_SIZE_P2    10U
#elif REDCONF_BLOCK_SIZE == 2048U
    #define BLOCK_SIZE_P2    11U
#elif REDCONF_BLOCK_SIZE == 4096U
    #define BLOCK_SIZE_P2    12U
#elif REDCONF_BLOCK_SIZE == 8192U
    #define BLOCK_SIZE_P2    13U
#elif REDCONF_BLOCK_SIZE == 16384U
    #define BLOCK_SIZE_P2    14U
#elif REDCONF_BLOCK_SIZE == 32768U
    #define BLOCK_SIZE_P2    15U
#elif REDCONF_BLOCK_SIZE == 65536U
    #define BLOCK_SIZE_P2    16U
#else /* if   REDCONF_BLOCK_SIZE == 256U */
    #error "REDCONF_BLOCK_SIZE must be a power of two value between 256 and 65536"
#endif /* if   REDCONF_BLOCK_SIZE == 256U */

#define REDMIN( a, b )    ( ( ( a ) < ( b ) ) ? ( a ) : ( b ) )

#define INODE_INVALID        ( 0U )                /* General-purpose invalid inode number (must be zero). */
#define INODE_FIRST_VALID    ( 2U )                /* First valid inode number. */
#define INODE_ROOTDIR        ( INODE_FIRST_VALID ) /* Inode number of the root directory. */

/*  Expands to a "const" qualifier when the volume count is one, otherwise
 *  expands to nothing.  This is useful for variables that never change in
 *  single-volume configurations but do change in multi-volume configurations.
 */
#if REDCONF_VOLUME_COUNT == 1U
    #define CONST_IF_ONE_VOLUME    const
#else
    #define CONST_IF_ONE_VOLUME
#endif


#endif /* ifndef REDMACS_H */
