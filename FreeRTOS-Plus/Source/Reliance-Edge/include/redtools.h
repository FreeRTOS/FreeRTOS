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
#ifndef REDTOOLS_H
#define REDTOOLS_H


#ifdef _WIN32
    #include <Windows.h>
    #define HOST_PATH_MAX    MAX_PATH
#else
    #include <linux/limits.h>
    #define HOST_PATH_MAX    PATH_MAX
#endif


#if REDCONF_IMAGE_BUILDER == 1

    #define MACRO_NAME_MAX_LEN    32

    typedef struct
    {
        uint8_t bVolNumber;
        const char * pszInputDir;
        const char * pszOutputFile;
        #if REDCONF_API_POSIX == 1
            const char * pszVolName;
        #else
            const char * pszMapFile;
            const char * pszDefineFile;
            bool fNowarn;
        #endif
    } IMGBLDPARAM;


    void ImgbldParseParams( int argc,
                            char * argv[],
                            IMGBLDPARAM * pParam );
    int ImgbldStart( IMGBLDPARAM * pParam );


    typedef struct
    {
        #if REDCONF_API_POSIX == 1
            char asOutFilePath[ HOST_PATH_MAX ];
        #else
            uint32_t ulOutFileIndex;
        #endif
        char asInFilePath[ HOST_PATH_MAX ];
    } FILEMAPPING;


    extern void * gpCopyBuffer;
    extern uint32_t gulCopyBufferSize;


/*  Implemented in ibposix.c
 */
    #if REDCONF_API_POSIX == 1
        REDSTATUS IbPosixCopyDir( const char * pszVolName,
                                  const char * pszInDir );
        int IbPosixCreateDir( const char * pszVolName,
                              const char * pszFullPath,
                              const char * pszBasePath );
        int IbConvertPath( const char * pszVolName,
                           const char * pszFullPath,
                           const char * pszBasePath,
                           char * szOutPath );
    #endif


/*  Implemented in ibfse.c
 */
    #if REDCONF_API_FSE == 1
        typedef struct sFILELISTENTRY FILELISTENTRY;
        struct sFILELISTENTRY
        {
            FILEMAPPING fileMapping;
            FILELISTENTRY * pNext;
        };


        void FreeFileList( FILELISTENTRY ** ppsFileList );

        int IbFseGetFileList( const char * pszPath,
                              const char * pszIndirPath,
                              FILELISTENTRY ** ppFileListHead );
        int IbFseOutputDefines( FILELISTENTRY * pFileList,
                                const IMGBLDPARAM * pOptions );
        int IbFseCopyFiles( int volNum,
                            const FILELISTENTRY * pFileList );
    #endif /* if REDCONF_API_FSE == 1 */


/*  Implemented in os-specific space (ibwin.c and iblinux.c)
 */
    #if REDCONF_API_POSIX == 1
        int IbPosixCopyDirRecursive( const char * pszVolName,
                                     const char * pszInDir );
    #endif
    #if REDCONF_API_FSE == 1
        int IbFseBuildFileList( const char * pszDirPath,
                                FILELISTENTRY ** ppFileListHead );
    #endif
    #if REDCONF_API_FSE == 1
        int IbSetRelativePath( char * pszPath,
                               const char * pszParentPath );
    #endif
    bool IsRegularFile( const char * pszPath );


/*  Implemented in ibcommon.c
 */
    int IbCopyFile( int volNum,
                    const FILEMAPPING * pFileMapping );
    int IbCheckFileExists( const char * pszPath,
                           bool * pfExists );


/*  Implemented separately in ibfse.c and ibposix.c
 */
    int IbApiInit( void );
    int IbApiUninit( void );
    int IbWriteFile( int volNum,
                     const FILEMAPPING * pFileMapping,
                     uint64_t ullOffset,
                     void * pData,
                     uint32_t ulDataLen );

#endif /* IMAGE_BUILDER */

/*  For image copier tool
 */

#ifdef _WIN32
    #define HOST_PSEP       '\\'
    #if !__STDC__
        #define snprintf    _snprintf
        #define stat        _stat
        #define S_IFDIR     _S_IFDIR
        #define rmdir       _rmdir
    #endif
#else
    #define HOST_PSEP       '/'
#endif

typedef struct
{
    uint8_t bVolNumber;
    const char * pszOutputDir;
    const char * pszBDevSpec;
    #if REDCONF_API_POSIX == 1
        const char * pszVolName;
    #endif
    bool fNoWarn;
} IMGCOPYPARAM;

typedef struct
{
    #if REDCONF_API_POSIX == 1
        const char * pszVolume;  /* Volume path prefix. */
        uint32_t ulVolPrefixLen; /* strlen(COPIER::pszVolume) */
    #else
        uint8_t bVolNum;         /* Volume number. */
    #endif
    const char * pszOutputDir;   /* Output directory path. */
    bool fNoWarn;                /* If true, no warning to overwrite. */
    uint8_t * pbCopyBuffer;      /* Buffer for copying file data. */
} COPIER;


void ImgcopyParseParams( int argc,
                         char * argv[],
                         IMGCOPYPARAM * pParam );
int ImgcopyStart( IMGCOPYPARAM * pParam );

/*  Implemented separately in imgcopywin.c and imgcopylinux.c.  These functions
 *  print an error message and abort on failure.
 */
void ImgcopyMkdir( const char * pszDir );
void ImgcopyRecursiveRmdir( const char * pszDir );


#endif /* REDTOOLS_H */
