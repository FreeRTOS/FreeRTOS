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
 *  @brief Implements path utilities for the POSIX-like API layer.
 */
#include <redfs.h>

#if REDCONF_API_POSIX == 1

    #include <redcoreapi.h>
    #include <redvolume.h>
    #include <redposix.h>
    #include <redpath.h>


    static bool IsRootDir( const char * pszLocalPath );
    static bool PathHasMoreNames( const char * pszPathIdx );


/** @brief Split a path into its component parts: a volume and a volume-local
 *         path.
 *
 *  @param pszPath          The path to split.
 *  @param pbVolNum         On successful return, if non-NULL, populated with
 *                          the volume number extracted from the path.
 *  @param ppszLocalPath    On successful return, populated with the
 *                          volume-local path: the path stripped of any volume
 *                          path prefixing.  If this parameter is NULL, that
 *                          indicates there should be no local path, and any
 *                          characters beyond the prefix (other than path
 *                          separators) are treated as an error.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p pszPath is `NULL`.
 *  @retval -RED_ENOENT @p pszPath could not be matched to any volume; or
 *                      @p ppszLocalPath is NULL but @p pszPath includes a local
 *                      path.
 */
    REDSTATUS RedPathSplit( const char * pszPath,
                            uint8_t * pbVolNum,
                            const char ** ppszLocalPath )
    {
        REDSTATUS ret = 0;

        if( pszPath == NULL )
        {
            ret = -RED_EINVAL;
        }
        else
        {
            const char * pszLocalPath = pszPath;
            uint8_t bMatchVol = UINT8_MAX;
            uint32_t ulMatchLen = 0U;
            uint8_t bDefaultVolNum = UINT8_MAX;
            uint8_t bVolNum;

            for( bVolNum = 0U; bVolNum < REDCONF_VOLUME_COUNT; bVolNum++ )
            {
                const char * pszPrefix = gaRedVolConf[ bVolNum ].pszPathPrefix;
                uint32_t ulPrefixLen = RedStrLen( pszPrefix );

                if( ulPrefixLen == 0U )
                {
                    /*  A volume with a path prefix of an empty string is the
                     *  default volume, used when the path does not match the
                     *  prefix of any other volume.
                     *
                     *  The default volume should only be found once.  During
                     *  initialization, RedCoreInit() ensures that all volume
                     *  prefixes are unique (including empty prefixes).
                     */
                    REDASSERT( bDefaultVolNum == UINT8_MAX );
                    bDefaultVolNum = bVolNum;
                }

                /*  For a path to match, it must either be the prefix exactly, or
                 *  be followed by a path separator character.  Thus, with a volume
                 *  prefix of "/foo", both "/foo" and "/foo/bar" are matches, but
                 *  "/foobar" is not.
                 */
                else if( ( RedStrNCmp( pszPath, pszPrefix, ulPrefixLen ) == 0 ) &&
                         ( ( pszPath[ ulPrefixLen ] == '\0' ) || ( pszPath[ ulPrefixLen ] == REDCONF_PATH_SEPARATOR ) ) )
                {
                    /*  The length of this match should never exactly equal the
                     *  length of a previous match: that would require a duplicate
                     *  volume name, which should have been detected during init.
                     */
                    REDASSERT( ulPrefixLen != ulMatchLen );

                    /*  If multiple prefixes match, the longest takes precedence.
                     *  Thus, if there are two prefixes "Flash" and "Flash/Backup",
                     *  the path "Flash/Backup/" will not be erroneously matched
                     *  with the "Flash" volume.
                     */
                    if( ulPrefixLen > ulMatchLen )
                    {
                        bMatchVol = bVolNum;
                        ulMatchLen = ulPrefixLen;
                    }
                }
                else
                {
                    /*  No match, keep looking.
                     */
                }
            }

            if( bMatchVol != UINT8_MAX )
            {
                /*  The path matched a volume path prefix.
                 */
                bVolNum = bMatchVol;
                pszLocalPath = &pszPath[ ulMatchLen ];
            }
            else if( bDefaultVolNum != UINT8_MAX )
            {
                /*  The path didn't match any of the prefixes, but one of the
                 *  volumes has a path prefix of "", so an unprefixed path is
                 *  assigned to that volume.
                 */
                bVolNum = bDefaultVolNum;
                REDASSERT( pszLocalPath == pszPath );
            }
            else
            {
                /*  The path cannot be assigned a volume.
                 */
                ret = -RED_ENOENT;
            }

            if( ret == 0 )
            {
                if( pbVolNum != NULL )
                {
                    *pbVolNum = bVolNum;
                }

                if( ppszLocalPath != NULL )
                {
                    *ppszLocalPath = pszLocalPath;
                }
                else
                {
                    /*  If no local path is expected, then the string should either
                     *  terminate after the path prefix or the local path should name
                     *  the root directory.  Allowing path separators here means that
                     *  red_mount("/data/") is OK with a path prefix of "/data".
                     */
                    if( pszLocalPath[ 0U ] != '\0' )
                    {
                        if( !IsRootDir( pszLocalPath ) )
                        {
                            ret = -RED_ENOENT;
                        }
                    }
                }
            }
        }

        return ret;
    }


/** @brief Lookup the inode named by the given path.
 *
 *  @param pszLocalPath The path to lookup; this is a local path, without any
 *                      volume prefix.
 *  @param pulInode     On successful return, populated with the number of the
 *                      inode named by @p pszLocalPath.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0                   Operation was successful.
 *  @retval -RED_EINVAL         @p pszLocalPath is `NULL`; or @p pulInode is
 *                              `NULL`.
 *  @retval -RED_EIO            A disk I/O error occurred.
 *  @retval -RED_ENOENT         @p pszLocalPath is an empty string; or
 *                              @p pszLocalPath does not name an existing file
 *                              or directory.
 *  @retval -RED_ENOTDIR        A component of the path other than the last is
 *                              not a directory.
 *  @retval -RED_ENAMETOOLONG   The length of a component of @p pszLocalPath is
 *                              longer than #REDCONF_NAME_MAX.
 */
    REDSTATUS RedPathLookup( const char * pszLocalPath,
                             uint32_t * pulInode )
    {
        REDSTATUS ret;

        if( ( pszLocalPath == NULL ) || ( pulInode == NULL ) )
        {
            REDERROR();
            ret = -RED_EINVAL;
        }
        else if( pszLocalPath[ 0U ] == '\0' )
        {
            ret = -RED_ENOENT;
        }
        else if( IsRootDir( pszLocalPath ) )
        {
            ret = 0;
            *pulInode = INODE_ROOTDIR;
        }
        else
        {
            uint32_t ulPInode;
            const char * pszName;

            ret = RedPathToName( pszLocalPath, &ulPInode, &pszName );

            if( ret == 0 )
            {
                ret = RedCoreLookup( ulPInode, pszName, pulInode );
            }
        }

        return ret;
    }


/** @brief Given a path, return the parent inode number and a pointer to the
 *         last component in the path (the name).
 *
 *  @param pszLocalPath The path to examine; this is a local path, without any
 *                      volume prefix.
 *  @param pulPInode    On successful return, populated with the inode number of
 *                      the parent directory of the last component in the path.
 *                      For example, with the path "a/b/c", populated with the
 *                      inode number of "b".
 *  @param ppszName     On successful return, populated with a pointer to the
 *                      last component in the path.  For example, with the path
 *                      "a/b/c", populated with a pointer to "c".
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0                   Operation was successful.
 *  @retval -RED_EINVAL         @p pszLocalPath is `NULL`; or @p pulPInode is
 *                              `NULL`; or @p ppszName is `NULL`; or the path
 *                              names the root directory.
 *  @retval -RED_EIO            A disk I/O error occurred.
 *  @retval -RED_ENOENT         @p pszLocalPath is an empty string; or a
 *                              component of the path other than the last does
 *                              not exist.
 *  @retval -RED_ENOTDIR        A component of the path other than the last is
 *                              not a directory.
 *  @retval -RED_ENAMETOOLONG   The length of a component of @p pszLocalPath is
 *                              longer than #REDCONF_NAME_MAX.
 */
    REDSTATUS RedPathToName( const char * pszLocalPath,
                             uint32_t * pulPInode,
                             const char ** ppszName )
    {
        REDSTATUS ret;

        if( ( pszLocalPath == NULL ) || ( pulPInode == NULL ) || ( ppszName == NULL ) )
        {
            REDERROR();
            ret = -RED_EINVAL;
        }
        else if( IsRootDir( pszLocalPath ) )
        {
            ret = -RED_EINVAL;
        }
        else if( pszLocalPath[ 0U ] == '\0' )
        {
            ret = -RED_ENOENT;
        }
        else
        {
            uint32_t ulInode = INODE_ROOTDIR;
            uint32_t ulPInode = INODE_INVALID;
            uint32_t ulPathIdx = 0U;
            uint32_t ulLastNameIdx = 0U;

            ret = 0;

            do
            {
                uint32_t ulNameLen;

                /*  Skip over path separators, to get pszLocalPath[ulPathIdx]
                 *  pointing at the next name.
                 */
                while( pszLocalPath[ ulPathIdx ] == REDCONF_PATH_SEPARATOR )
                {
                    ulPathIdx++;
                }

                if( pszLocalPath[ ulPathIdx ] == '\0' )
                {
                    break;
                }

                /*  Point ulLastNameIdx at the first character of the name; after
                 *  we exit the loop, it will point at the first character of the
                 *  last name in the path.
                 */
                ulLastNameIdx = ulPathIdx;

                /*  Point ulPInode at the parent inode: either the root inode
                 *  (first pass) or the inode of the previous name.  After we exit
                 *  the loop, this will point at the parent inode of the last name.
                 */
                ulPInode = ulInode;

                ulNameLen = RedNameLen( &pszLocalPath[ ulPathIdx ] );

                /*  Lookup the inode of the name, unless we are at the last name in
                 *  the path: we don't care whether the last name exists or not.
                 */
                if( PathHasMoreNames( &pszLocalPath[ ulPathIdx + ulNameLen ] ) )
                {
                    ret = RedCoreLookup( ulPInode, &pszLocalPath[ ulPathIdx ], &ulInode );
                }

                /*  Move on to the next path element.
                 */
                if( ret == 0 )
                {
                    ulPathIdx += ulNameLen;
                }
            }
            while( ret == 0 );

            if( ret == 0 )
            {
                *pulPInode = ulPInode;
                *ppszName = &pszLocalPath[ ulLastNameIdx ];
            }
        }

        return ret;
    }


/** @brief Determine whether a path names the root directory.
 *
 *  @param pszLocalPath The path to examine; this is a local path, without any
 *                      volume prefix.
 *
 *  @return Returns whether @p pszLocalPath names the root directory.
 *
 *  @retval true    @p pszLocalPath names the root directory.
 *  @retval false   @p pszLocalPath does not name the root directory.
 */
    static bool IsRootDir( const char * pszLocalPath )
    {
        bool fRet;

        if( pszLocalPath == NULL )
        {
            REDERROR();
            fRet = false;
        }
        else
        {
            uint32_t ulIdx = 0U;

            /*  A string containing nothing but path separators (usually only one)
             *  names the root directory.  An empty string does *not* name the root
             *  directory, since in POSIX empty strings typically elicit -RED_ENOENT
             *  errors.
             */
            while( pszLocalPath[ ulIdx ] == REDCONF_PATH_SEPARATOR )
            {
                ulIdx++;
            }

            fRet = ( ulIdx > 0U ) && ( pszLocalPath[ ulIdx ] == '\0' );
        }

        return fRet;
    }


/** @brief Determine whether there are more names in a path.
 *
 *  Example | Result
 *  ------- | ------
 *  ""        false
 *  "/"       false
 *  "//"      false
 *  "a"       true
 *  "/a"      true
 *  "//a"     true
 *
 *  @param pszPathIdx   The path to examine, incremented to the point of
 *                      interest.
 *
 *  @return Returns whether there are more names in @p pszPathIdx.
 *
 *  @retval true    @p pszPathIdx has more names.
 *  @retval false   @p pszPathIdx has no more names.
 */
    static bool PathHasMoreNames( const char * pszPathIdx )
    {
        bool fRet;

        if( pszPathIdx == NULL )
        {
            REDERROR();
            fRet = false;
        }
        else
        {
            uint32_t ulIdx = 0U;

            while( pszPathIdx[ ulIdx ] == REDCONF_PATH_SEPARATOR )
            {
                ulIdx++;
            }

            fRet = pszPathIdx[ ulIdx ] != '\0';
        }

        return fRet;
    }

#endif /* REDCONF_API_POSIX */
