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
    @brief Prototypes for Reliance Edge test entry points.
*/
#ifndef REDTESTS_H
#define REDTESTS_H

#include <redtypes.h>
#include "redtestutils.h"
#include "redver.h"

/*  This macro is only defined by the error injection project.
*/
#ifdef REDCONF_ERROR_INJECTION
#include <rederrinject.h>
#endif

#define FSSTRESS_SUPPORTED  \
    (    ((RED_KIT == RED_KIT_GPL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0) && (REDCONF_PATH_SEPARATOR == '/') \
      && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_UNLINK == 1) && (REDCONF_API_POSIX_MKDIR == 1) \
      && (REDCONF_API_POSIX_RMDIR == 1) && (REDCONF_API_POSIX_RENAME == 1) && (REDCONF_API_POSIX_LINK == 1) \
      && (REDCONF_API_POSIX_FTRUNCATE == 1) && (REDCONF_API_POSIX_READDIR == 1))

#define FSE_STRESS_TEST_SUPPORTED \
    (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0) && (REDCONF_API_FSE == 1) \
      && (REDCONF_API_FSE_FORMAT == 1) && (REDCONF_API_FSE_TRANSMASKSET == 1) && (REDCONF_API_FSE_TRANSMASKGET == 1) \
      && (REDCONF_API_FSE_TRUNCATE == 1))

#define POSIX_API_TEST_SUPPORTED \
    (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) \
      && (REDCONF_API_POSIX_FORMAT == 1) && (REDCONF_API_POSIX_UNLINK == 1))

#define FSE_API_TEST_SUPPORTED \
   (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0) && (REDCONF_API_FSE == 1) \
      && (REDCONF_API_FSE_FORMAT == 1))

#define STOCH_POSIX_TEST_SUPPORTED \
    (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) \
      && (REDCONF_API_POSIX_FORMAT == 1) && (REDCONF_API_POSIX_READDIR == 1) \
      && (REDCONF_API_POSIX_MKDIR == 1) && (REDCONF_API_POSIX_RMDIR == 1) && (REDCONF_API_POSIX_UNLINK == 1) \
      && (REDCONF_API_POSIX_RENAME == 1))

#define FSIOTEST_SUPPORTED \
    (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_API_POSIX == 1))

#define BDEVTEST_SUPPORTED \
    (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
      && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0))

#define DISKFULL_TEST_SUPPORTED \
   (    ((RED_KIT == RED_KIT_COMMERCIAL) || (RED_KIT == RED_KIT_SANDBOX)) \
     && (REDCONF_OUTPUT == 1) && (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) \
     && (REDCONF_API_POSIX_FORMAT == 1) && (REDCONF_API_POSIX_FTRUNCATE == 1))


typedef enum
{
    PARAMSTATUS_OK,     /* Parameters were good; continue. */
    PARAMSTATUS_BAD,    /* Parameters were bad; stop. */
    PARAMSTATUS_HELP    /* Help request; not an error, but stop. */
} PARAMSTATUS;


#if FSSTRESS_SUPPORTED
typedef struct
{
    bool        fNoCleanup; /**< --no-cleanup */
    uint32_t    ulLoops;    /**< --loops */
    uint32_t    ulNops;     /**< --nops */
    bool        fNamePad;   /**< --namepad */
    uint32_t    ulSeed;     /**< --seed */
    bool        fVerbose;   /**< --verbose */
} FSSTRESSPARAM;

PARAMSTATUS FsstressParseParams(int argc, char *argv[], FSSTRESSPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void FsstressDefaultParams(FSSTRESSPARAM *pParam);
int FsstressStart(const FSSTRESSPARAM *pParam);
#endif

#if STOCH_POSIX_TEST_SUPPORTED
typedef struct
{
    const char *pszVolume;          /**< Volume path prefix. */
    uint32_t    ulIterations;       /**< --iterations */
    uint32_t    ulFileListMax;      /**< --files */
    uint32_t    ulDirListMax;       /**< --dirs */
    uint32_t    ulOpenFileListMax;  /**< --open-files */
    uint32_t    ulOpenDirListMax;   /**< --open-dirs */
    uint32_t    ulRandomSeed;       /**< --seed */
} STOCHPOSIXPARAM;

PARAMSTATUS RedStochPosixParseParams(int argc, char *argv[], STOCHPOSIXPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void RedStochPosixDefaultParams(STOCHPOSIXPARAM *pParam);
int RedStochPosixStart(const STOCHPOSIXPARAM *pParam);
#endif

#if FSE_STRESS_TEST_SUPPORTED
typedef struct
{
    uint8_t     bVolNum;        /**< Volume number. */
    uint32_t    ulFileCount;    /**< --files */
    uint32_t    ulMaxFileSize;  /**< --max */
    uint32_t    ulMaxOpSize;    /**< --buffer-size */
    uint32_t    ulNops;         /**< --nops */
    uint32_t    ulLoops;        /**< --loops */
    uint32_t    ulSampleRate;   /**< --sample-rate */
    uint64_t    ullSeed;        /**< --seed */
} FSESTRESSPARAM;

PARAMSTATUS FseStressParseParams(int argc, char *argv[], FSESTRESSPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void FseStressDefaultParams(FSESTRESSPARAM *pParam);
int FseStressStart(const FSESTRESSPARAM *pParam);
#endif

#if POSIX_API_TEST_SUPPORTED
typedef struct
{
    const char *pszVolume;      /**< Volume path prefix. */
    bool        fQuick;         /**< --quick */
    bool        fQuitOnFailure; /**< --quit-on-failure */
    bool        fDebugErrors;   /**< --debug */
} POSIXTESTPARAM;

PARAMSTATUS RedPosixTestParseParams(int argc, char *argv[], POSIXTESTPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void RedPosixTestDefaultParams(POSIXTESTPARAM *pParam);
int RedPosixTestStart(const POSIXTESTPARAM *pParam);
#endif


#if POSIX_API_TEST_SUPPORTED
typedef struct
{
    const char *pszVolume;      /**< Volume path prefix. */
    bool        fQuick;         /**< --quick */
    bool        fVerbose;       /**< --verbose */
    bool        fQuitOnFailure; /**< --quit-on-failure */
    bool        fDebugErrors;   /**< --debug */
} OSAPITESTPARAM;

PARAMSTATUS RedOsApiTestParseParams(int argc, char *argv[], OSAPITESTPARAM *pParam, const char **ppszDevice);
void RedOsApiTestDefaultParams(OSAPITESTPARAM *pParam);
int RedOsApiTestStart(const OSAPITESTPARAM *pParam);
#endif


#if FSE_API_TEST_SUPPORTED
typedef struct
{
    uint8_t bVolNum;        /**< Volume number. */
    bool    fQuitOnFailure; /**< --quit-on-failure */
    bool    fDebugErrors;   /**< --debug */
} FSETESTPARAM;

PARAMSTATUS RedFseTestParseParams(int argc, char *argv[], FSETESTPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void RedFseTestDefaultParams(FSETESTPARAM *pParam);
int RedFseTestStart(const FSETESTPARAM *pParam);
#endif

#if FSIOTEST_SUPPORTED
typedef enum
{
    TESTFS_RELEDGE, /* Datalight Reliance Edge */
    TESTFS_FATFS,   /* ChaN's FatFs */
    TESTFS_FATSL    /* FreeRTOS+FAT SL */
} TESTFS;

typedef struct
{
    TESTFS      testfs;                 /**< --fs */
    const char *pszVolume;              /**< Volume path prefix. */
    bool        fSeqRead;               /**< --seq=r */
    bool        fSeqWrite;              /**< --seq=w */
    bool        fSeqRewrite;            /**< --seq=e */
    bool        fRandomRead;            /**< --rand=r */
    bool        fRandomWrite;           /**< --rand=w */
    bool        fMixedWrite;            /**< --mixed */
    bool        fScanTest;              /**< --scan */
    uint32_t    ulFSBlockSize;          /**< --block-size */
    uint32_t    ulMaxFileSize;          /**< --max */
    uint32_t    ulRandomReadPasses;     /**< --rand-pass=r:w (r part) */
    uint32_t    ulRandomWritePasses;    /**< --rand-pass=r:w (w part) */
    uint32_t    ulMixedWritePasses;     /**< --mixed-pass */
    int32_t     iFlushOnWriteRatio;     /**< --rand-fow */
    uint32_t    ulBufferMin;            /**< --start */
    uint32_t    ulBufferSize;           /**< --buffer-size */
    bool        fWriteVerify;           /**< --verify */
    uint32_t    ulSampleRate;           /**< --sample-rate */
    uint32_t    ulScanCount;            /**< --scan-files */
    uint64_t    ullSeed;                /**< --seed */
} FSIOTESTPARAM;

PARAMSTATUS FSIOTestParseParams(int argc, char *argv[], FSIOTESTPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void FSIOTestDefaultParams(FSIOTESTPARAM *pParam);
int FSIOTestStart(const FSIOTESTPARAM *pParam);
#endif

#if BDEVTEST_SUPPORTED
typedef struct
{
    uint8_t     bDrvNum;        /**< Volume number (for sector size/count). */
    bool        fSeqWrite;      /**< --seq:w */
    bool        fSeqRead;       /**< --seq:r */
    bool        fRandWrite;     /**< --rand:w */
    bool        fRandRead;      /**< --rand:r */
    uint32_t    ulSampleSecs;   /**< --sample-rate */
    uint32_t    ulPasses;       /**< --passes */
    uint32_t    ulMinIOSectors; /**< --count=min[:max] (min part) */
    uint32_t    ulMaxIOSectors; /**< --count=min[:max] (max part) */
    uint32_t    ulMaxSizeKB;    /**< --max */
    uint32_t    ulTestSeconds;  /**< --time */
    bool        fVerify;        /**< --verify */
    bool        fAsyncWrites;   /**< --async */
    uint64_t    ullSeed;        /**< --seed */
} BDEVTESTPARAM;

PARAMSTATUS BDevTestParseParams(int argc, char *argv[], BDEVTESTPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void BDevTestDefaultParams(BDEVTESTPARAM *pParam);
int BDevTestStart(const BDEVTESTPARAM *pParam);
#endif

#if DISKFULL_TEST_SUPPORTED
typedef struct
{
    const char *pszVolume;      /**< Volume path prefix. */
    bool        fQuitOnFailure; /**< --quit-on-failure */
    bool        fDebugErrors;   /**< --debug */
} DISKFULLTESTPARAM;

PARAMSTATUS DiskFullTestParseParams(int argc, char *argv[], DISKFULLTESTPARAM *pParam, uint8_t *pbVolNum, const char **ppszDevice);
void DiskFullTestDefaultParams(DISKFULLTESTPARAM *pParam);
int DiskFullTestStart(const DISKFULLTESTPARAM *pParam);
#endif


#endif

