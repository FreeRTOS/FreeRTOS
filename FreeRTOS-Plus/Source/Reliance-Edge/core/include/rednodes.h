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
#ifndef REDNODES_H
#define REDNODES_H


#define NODEHEADER_SIZE          ( 16U )
#define NODEHEADER_OFFSET_SIG    ( 0U )
#define NODEHEADER_OFFSET_CRC    ( 4U )
#define NODEHEADER_OFFSET_SEQ    ( 8U )

/** @brief Common header for all metadata nodes.
 */
typedef struct
{
    uint32_t ulSignature; /**< Value which uniquely identifies the metadata node type. */
    uint32_t ulCRC;       /**< CRC-32 checksum of the node contents, starting after the CRC. */
    uint64_t ullSequence; /**< Current sequence number at the time the node was written to disk. */
} NODEHEADER;


/** Flag set in the master block when REDCONF_API_POSIX == 1. */
#define MBFLAG_API_POSIX           ( 0x01U )

/** Flag set in the master block when REDCONF_INODE_TIMESTAMPS == 1. */
#define MBFLAG_INODE_TIMESTAMPS    ( 0x02U )

/** Flag set in the master block when REDCONF_INODE_BLOCKS == 1. */
#define MBFLAG_INODE_BLOCKS        ( 0x04U )

/** Flag set in the master block when (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_LINK == 1). */
#define MBFLAG_INODE_NLINK         ( 0x08U )


/** @brief Node which identifies the volume and stores static volume information.
 */
typedef struct
{
    NODEHEADER hdr;             /**< Common node header. */

    uint32_t ulVersion;         /**< On-disk layout version number. */
    char acBuildNum[ 8U ];      /**< Build number of the product (not null terminated). */
    uint32_t ulFormatTime;      /**< Date and time the volume was formatted. */
    uint32_t ulInodeCount;      /**< Compile-time configured number of inodes. */
    uint32_t ulBlockCount;      /**< Compile-time configured number of logical blocks. */
    uint16_t uMaxNameLen;       /**< Compile-time configured maximum file name length. */
    uint16_t uDirectPointers;   /**< Compile-time configured number of direct pointers per inode. */
    uint16_t uIndirectPointers; /**< Compile-time configured number of indirect pointers per inode. */
    uint8_t bBlockSizeP2;       /**< Compile-time configured block size, expressed as a power of two. */
    uint8_t bFlags;             /**< Compile-time booleans which affect on-disk structures. */
} MASTERBLOCK;


#if REDCONF_API_POSIX == 1
    #define METAROOT_HEADER_SIZE    ( NODEHEADER_SIZE + 16U )                     /* Size in bytes of the metaroot header fields. */
#else
    #define METAROOT_HEADER_SIZE    ( NODEHEADER_SIZE + 12U )                     /* Size in bytes of the metaroot header fields. */
#endif
#define METAROOT_ENTRY_BYTES        ( REDCONF_BLOCK_SIZE - METAROOT_HEADER_SIZE ) /* Number of bytes remaining in the metaroot block for entries. */
#define METAROOT_ENTRIES            ( METAROOT_ENTRY_BYTES * 8U )

/** @brief Metadata root node; each volume has two.
 */
typedef struct
{
    NODEHEADER hdr;            /**< Common node header. */

    uint32_t ulSectorCRC;      /**< CRC-32 checksum of the first sector. */
    uint32_t ulFreeBlocks;     /**< Number of allocable blocks that are free. */
    #if REDCONF_API_POSIX == 1
        uint32_t ulFreeInodes; /**< Number of inode slots that are free. */
    #endif
    uint32_t ulAllocNextBlock; /**< Forward allocation pointer. */

    /** Imap bitmap.  With inline imaps, this is the imap bitmap that indicates
     *  which inode blocks are used and which allocable blocks are used.
     *  Otherwise, this bitmap toggles nodes in the external imap between one
     *  of two possible block locations.
     */
    uint8_t abEntries[ METAROOT_ENTRY_BYTES ];
} METAROOT;


#if REDCONF_IMAP_EXTERNAL == 1
    #define IMAPNODE_HEADER_SIZE    ( NODEHEADER_SIZE )                           /* Size in bytes of the imap node header fields. */
    #define IMAPNODE_ENTRY_BYTES    ( REDCONF_BLOCK_SIZE - IMAPNODE_HEADER_SIZE ) /* Number of bytes remaining in the imap node for entries. */
    #define IMAPNODE_ENTRIES        ( IMAPNODE_ENTRY_BYTES * 8U )

/** @brief One node of the external imap.
 */
    typedef struct
    {
        NODEHEADER hdr; /**< Common node header. */

        /** Bitmap which indicates which inode blocks are used and which allocable
         *  blocks are used.
         */
        uint8_t abEntries[ IMAPNODE_ENTRY_BYTES ];
    } IMAPNODE;
#endif /* if REDCONF_IMAP_EXTERNAL == 1 */


#define INODE_HEADER_SIZE                                                  \
    ( NODEHEADER_SIZE + 8U + ( ( REDCONF_INODE_BLOCKS == 1 ) ? 4U : 0U ) + \
      ( ( REDCONF_INODE_TIMESTAMPS == 1 ) ? 12U : 0U ) + 4U + ( ( REDCONF_API_POSIX == 1 ) ? 4U : 0U ) )
#define INODE_ENTRIES    ( ( REDCONF_BLOCK_SIZE - INODE_HEADER_SIZE ) / 4U )

#if ( REDCONF_DIRECT_POINTERS < 0 ) || ( REDCONF_DIRECT_POINTERS > ( INODE_ENTRIES - REDCONF_INDIRECT_POINTERS ) )
    #error "Configuration error: invalid value of REDCONF_DIRECT_POINTERS"
#endif
#if ( REDCONF_INDIRECT_POINTERS < 0 ) || ( REDCONF_INDIRECT_POINTERS > ( INODE_ENTRIES - REDCONF_DIRECT_POINTERS ) )
    #error "Configuration error: invalid value of REDCONF_INDIRECT_POINTERS"
#endif

/** @brief Stores metadata for a file or directory.
 */
typedef struct
{
    NODEHEADER hdr;        /**< Common node header. */

    uint64_t ullSize;      /**< Size of the inode, in bytes. */
    #if REDCONF_INODE_BLOCKS == 1
        uint32_t ulBlocks; /**< Total number file data blocks allocated to the inode. */
    #endif
    #if REDCONF_INODE_TIMESTAMPS == 1
        uint32_t ulATime;       /**< Time of last access (seconds since January 1, 1970). */
        uint32_t ulMTime;       /**< Time of last modification (seconds since January 1, 1970). */
        uint32_t ulCTime;       /**< Time of last status change (seconds since January 1, 1970). */
    #endif
    uint16_t uMode;             /**< Inode type (file or directory) and permissions (reserved). */
    #if ( REDCONF_API_POSIX == 1 ) && ( REDCONF_API_POSIX_LINK == 1 )
        uint16_t uNLink;        /**< Link count, number of names pointing to the inode. */
    #else
        uint8_t abPadding[ 2 ]; /**< Padding to 32-bit align the next member. */
    #endif
    #if REDCONF_API_POSIX == 1
        uint32_t ulPInode; /**< Parent inode number.  Only guaranteed to be accurate for directories. */
    #endif

    /** Block numbers for lower levels of the file metadata structure.  Some
     *  fraction of these entries are for direct pointers (file data block
     *  numbers), some for indirect pointers, some for double-indirect
     *  pointers; the number allocated to each is static but user-configurable.
     *  For all types, an array slot is zero if the range is sparse or beyond
     *  the end of file.
     */
    uint32_t aulEntries[ INODE_ENTRIES ];
} INODE;


#define INDIR_HEADER_SIZE    ( NODEHEADER_SIZE + 4U )
#define INDIR_ENTRIES        ( ( REDCONF_BLOCK_SIZE - INDIR_HEADER_SIZE ) / 4U )

/** @brief Node for storing block pointers.
 */
typedef struct
{
    NODEHEADER hdr;   /**< Common node header. */

    uint32_t ulInode; /**< Inode which owns this indirect or double indirect. */

    /** For indirect nodes, stores block numbers of file data.  For double
     *  indirect nodes, stores block numbers of indirect nodes.  An array
     *  slot is zero if the corresponding block or indirect range is beyond
     *  the end of file or entirely sparse.
     */
    uint32_t aulEntries[ INDIR_ENTRIES ];
} INDIR, DINDIR;


#endif /* ifndef REDNODES_H */
