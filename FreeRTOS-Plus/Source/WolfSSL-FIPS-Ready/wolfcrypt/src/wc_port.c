/* port.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/types.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/wc_port.h>
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif
#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
#endif

/* IPP header files for library initialization */
#ifdef HAVE_FAST_RSA
    #include <ipp.h>
    #include <ippcp.h>
#endif

#ifdef FREESCALE_LTC_TFM
    #include <wolfssl/wolfcrypt/port/nxp/ksdk_port.h>
#endif

#ifdef WOLFSSL_PSOC6_CRYPTO
    #include <wolfssl/wolfcrypt/port/cypress/psoc6_crypto.h>
#endif

#if defined(WOLFSSL_ATMEL) || defined(WOLFSSL_ATECC508A) || \
    defined(WOLFSSL_ATECC608A)
    #include <wolfssl/wolfcrypt/port/atmel/atmel.h>
#endif
#if defined(WOLFSSL_RENESAS_TSIP)
    #include <wolfssl/wolfcrypt/port/Renesas/renesas-tsip-crypt.h>
#endif
#if defined(WOLFSSL_STSAFEA100)
    #include <wolfssl/wolfcrypt/port/st/stsafe.h>
#endif

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    #include <wolfssl/openssl/evp.h>
#endif

#if defined(USE_WOLFSSL_MEMORY) && defined(WOLFSSL_TRACK_MEMORY)
    #include <wolfssl/wolfcrypt/memory.h>
    #include <wolfssl/wolfcrypt/mem_track.h>
#endif

#if defined(WOLFSSL_IMX6_CAAM) || defined(WOLFSSL_IMX6_CAAM_RNG) || \
    defined(WOLFSSL_IMX6_CAAM_BLOB)
    #include <wolfssl/wolfcrypt/port/caam/wolfcaam.h>
#endif

#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
#endif

#ifdef HAVE_INTEL_QA_SYNC
    #include <wolfssl/wolfcrypt/port/intel/quickassist_sync.h>
#endif

#ifdef HAVE_CAVIUM_OCTEON_SYNC
    #include <wolfssl/wolfcrypt/port/cavium/cavium_octeon_sync.h>
#endif

#ifdef WOLFSSL_SCE
    #include "hal_data.h"
#endif

#if defined(WOLFSSL_DSP) && !defined(WOLFSSL_DSP_BUILD)
    #include "rpcmem.h"
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

/* prevent multiple mutex initializations */
static volatile int initRefCount = 0;

/* Used to initialize state for wolfcrypt
   return 0 on success
 */
int wolfCrypt_Init(void)
{
    int ret = 0;

    if (initRefCount == 0) {
        WOLFSSL_ENTER("wolfCrypt_Init");

    #ifdef WOLFSSL_FORCE_MALLOC_FAIL_TEST
        {
            word32 rngMallocFail;
            time_t seed = time(NULL);
            srand((word32)seed);
            rngMallocFail = rand() % 2000; /* max 2000 */
            printf("\n--- RNG MALLOC FAIL AT %d---\n", rngMallocFail);
            wolfSSL_SetMemFailCount(rngMallocFail);
        }
    #endif

    #ifdef WOLF_CRYPTO_CB
        wc_CryptoCb_Init();
    #endif

    #ifdef WOLFSSL_ASYNC_CRYPT
        ret = wolfAsync_HardwareStart();
        if (ret != 0) {
            WOLFSSL_MSG("Async hardware start failed");
            /* don't return failure, allow operation to continue */
        }
    #endif

    #if defined(WOLFSSL_RENESAS_TSIP_CRYPT)
        ret = tsip_Open( );
        if( ret != TSIP_SUCCESS ) {
            WOLFSSL_MSG("RENESAS TSIP Open failed");
            /* not return 1 since WOLFSSL_SUCCESS=1*/
            ret = -1;/* FATAL ERROR */
            return ret;
        }
    #endif

    #if defined(WOLFSSL_TRACK_MEMORY) && !defined(WOLFSSL_STATIC_MEMORY)
        ret = InitMemoryTracker();
        if (ret != 0) {
            WOLFSSL_MSG("InitMemoryTracker failed");
            return ret;
        }
    #endif

    #if WOLFSSL_CRYPT_HW_MUTEX
        /* If crypto hardware mutex protection is enabled, then initialize it */
        ret = wolfSSL_CryptHwMutexInit();
        if (ret != 0) {
            WOLFSSL_MSG("Hw crypt mutex init failed");
            return ret;
        }
    #endif

    /* if defined have fast RSA then initialize Intel IPP */
    #ifdef HAVE_FAST_RSA
        WOLFSSL_MSG("Attempting to use optimized IPP Library");
        if ((ret = ippInit()) != ippStsNoErr) {
            /* possible to get a CPU feature support status on optimized IPP
              library but still use default library and see competitive speeds */
            WOLFSSL_MSG("Warning when trying to set up optimization");
            WOLFSSL_MSG(ippGetStatusString(ret));
            WOLFSSL_MSG("Using default fast IPP library");
            ret = 0;
            (void)ret; /* suppress not read warning */
        }
    #endif

    #if defined(FREESCALE_LTC_TFM) || defined(FREESCALE_LTC_ECC)
        ret = ksdk_port_init();
        if (ret != 0) {
            WOLFSSL_MSG("KSDK port init failed");
            return ret;
        }
    #endif

    #if defined(WOLFSSL_ATMEL) || defined(WOLFSSL_ATECC508A) || \
        defined(WOLFSSL_ATECC608A)
        ret = atmel_init();
        if (ret != 0) {
            WOLFSSL_MSG("CryptoAuthLib init failed");
            return ret;
        }
    #endif
    #if defined(WOLFSSL_CRYPTOCELL)
        /* enable and initialize the ARM CryptoCell 3xx runtime library */
        ret = cc310_Init();
        if (ret != 0) {
            WOLFSSL_MSG("CRYPTOCELL init failed");
            return ret;
        }
    #endif
    #if defined(WOLFSSL_STSAFEA100)
        stsafe_interface_init();
    #endif

    #if defined(WOLFSSL_PSOC6_CRYPTO)
        ret = psoc6_crypto_port_init();
        if (ret != 0) {
            WOLFSSL_MSG("PSoC6 crypto engine init failed");
            return ret;
        }
    #endif

    #ifdef WOLFSSL_ARMASM
        WOLFSSL_MSG("Using ARM hardware acceleration");
    #endif

    #ifdef WOLFSSL_AFALG
	WOLFSSL_MSG("Using AF_ALG for crypto acceleration");
    #endif

    #if !defined(WOLFCRYPT_ONLY) && defined(OPENSSL_EXTRA)
        wolfSSL_EVP_init();
    #endif

    #if defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)
        if ((ret = wc_LoggingInit()) != 0) {
            WOLFSSL_MSG("Error creating logging mutex");
            return ret;
        }
    #endif

#ifdef HAVE_ECC
    #ifdef FP_ECC
        wc_ecc_fp_init();
    #endif
    #ifdef ECC_CACHE_CURVE
        if ((ret = wc_ecc_curve_cache_init()) != 0) {
            WOLFSSL_MSG("Error creating curve cache");
            return ret;
        }
    #endif
#endif

#ifdef WOLFSSL_SCE
        ret = (int)WOLFSSL_SCE_GSCE_HANDLE.p_api->open(
                WOLFSSL_SCE_GSCE_HANDLE.p_ctrl, WOLFSSL_SCE_GSCE_HANDLE.p_cfg);
        if (ret == SSP_ERR_CRYPTO_SCE_ALREADY_OPEN) {
            WOLFSSL_MSG("SCE already open");
            ret = 0;
        }
        if (ret != SSP_SUCCESS) {
            WOLFSSL_MSG("Error opening SCE");
            return -1; /* FATAL_ERROR */
        }
#endif

#if defined(WOLFSSL_IMX6_CAAM) || defined(WOLFSSL_IMX6_CAAM_RNG) || \
    defined(WOLFSSL_IMX6_CAAM_BLOB)
        if ((ret = wc_caamInit()) != 0) {
            return ret;
        }
#endif

#if defined(WOLFSSL_DSP) && !defined(WOLFSSL_DSP_BUILD)
	if ((ret = wolfSSL_InitHandle()) != 0) {
            return ret;
        }
        rpcmem_init();
#endif
    }
    initRefCount++;

    return ret;
}


/* return success value is the same as wolfCrypt_Init */
int wolfCrypt_Cleanup(void)
{
    int ret = 0;

    initRefCount--;
    if (initRefCount < 0)
        initRefCount = 0;

    if (initRefCount == 0) {
        WOLFSSL_ENTER("wolfCrypt_Cleanup");

#ifdef HAVE_ECC
    #ifdef FP_ECC
        wc_ecc_fp_free();
    #endif
    #ifdef ECC_CACHE_CURVE
        wc_ecc_curve_cache_free();
    #endif
#endif /* HAVE_ECC */

    #if defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)
        ret = wc_LoggingCleanup();
    #endif

    #if defined(WOLFSSL_TRACK_MEMORY) && !defined(WOLFSSL_STATIC_MEMORY)
        ShowMemoryTracker();
    #endif

    #ifdef WOLFSSL_ASYNC_CRYPT
        wolfAsync_HardwareStop();
    #endif
    #ifdef WOLFSSL_SCE
        WOLFSSL_SCE_GSCE_HANDLE.p_api->close(WOLFSSL_SCE_GSCE_HANDLE.p_ctrl);
    #endif
    #if defined(WOLFSSL_IMX6_CAAM) || defined(WOLFSSL_IMX6_CAAM_RNG) || \
        defined(WOLFSSL_IMX6_CAAM_BLOB)
        wc_caamFree();
    #endif
    #if defined(WOLFSSL_CRYPTOCELL)
        cc310_Free();
    #endif
    #if defined(WOLFSSL_RENESAS_TSIP_CRYPT)
        tsip_Close();
    #endif
    #if defined(WOLFSSL_DSP) && !defined(WOLFSSL_DSP_BUILD)
        rpcmem_deinit();
        wolfSSL_CleanupHandle();
    #endif
    }

    return ret;
}

#ifndef NO_FILESYSTEM

/* Helpful function to load file into allocated buffer */
int wc_FileLoad(const char* fname, unsigned char** buf, size_t* bufLen, 
    void* heap)
{
    int ret;
    size_t fileSz;
    XFILE f;

    if (fname == NULL || buf == NULL || bufLen == NULL) {
        return BAD_FUNC_ARG;
    }

    /* set defaults */
    *buf = NULL;
    *bufLen = 0;

    /* open file (read-only binary) */
    f = XFOPEN(fname, "rb");
    if (!f) {
        WOLFSSL_MSG("wc_LoadFile file load error");
        return BAD_PATH_ERROR;
    }

    XFSEEK(f, 0, SEEK_END);
    fileSz = XFTELL(f);
    XREWIND(f);
    if (fileSz > 0) {
        *bufLen = fileSz;
        *buf = (byte*)XMALLOC(*bufLen, heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (*buf == NULL) {
            WOLFSSL_MSG("wc_LoadFile memory error");
            ret = MEMORY_E;
        }
        else {
            size_t readLen = XFREAD(*buf, 1, *bufLen, f);

            /* check response code */
            ret = (readLen == *bufLen) ? 0 : -1;
        }
    }
    else {
        ret = BUFFER_E;
    }
    XFCLOSE(f);

    (void)heap;

    return ret;
}

#if !defined(NO_WOLFSSL_DIR) && \
    !defined(WOLFSSL_NUCLEUS) && !defined(WOLFSSL_NUCLEUS_1_2)

/* File Handling Helpers */
/* returns 0 if file found, WC_READDIR_NOFILE if no files or negative error */
int wc_ReadDirFirst(ReadDirCtx* ctx, const char* path, char** name)
{
    int ret = WC_READDIR_NOFILE; /* default to no files found */
    int pathLen = 0;
    int dnameLen = 0;

    if (name)
        *name = NULL;

    if (ctx == NULL || path == NULL) {
        return BAD_FUNC_ARG;
    }

    XMEMSET(ctx->name, 0, MAX_FILENAME_SZ);
    pathLen = (int)XSTRLEN(path);

#ifdef USE_WINDOWS_API
    if (pathLen > MAX_FILENAME_SZ - 3)
        return BAD_PATH_ERROR;

    XSTRNCPY(ctx->name, path, MAX_FILENAME_SZ - 3);
    XSTRNCPY(ctx->name + pathLen, "\\*", MAX_FILENAME_SZ - pathLen);

    ctx->hFind = FindFirstFileA(ctx->name, &ctx->FindFileData);
    if (ctx->hFind == INVALID_HANDLE_VALUE) {
        WOLFSSL_MSG("FindFirstFile for path verify locations failed");
        return BAD_PATH_ERROR;
    }

    do {
        if (!(ctx->FindFileData.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)) {
            dnameLen = (int)XSTRLEN(ctx->FindFileData.cFileName);

            if (pathLen + dnameLen + 2 > MAX_FILENAME_SZ) {
                return BAD_PATH_ERROR;
            }
            XSTRNCPY(ctx->name, path, pathLen + 1);
            ctx->name[pathLen] = '\\';
            XSTRNCPY(ctx->name + pathLen + 1,
                     ctx->FindFileData.cFileName,
                     MAX_FILENAME_SZ - pathLen - 1);
            if (name)
                *name = ctx->name;
            return 0;
        }
    } while (FindNextFileA(ctx->hFind, &ctx->FindFileData));
#elif defined(WOLFSSL_ZEPHYR)
    if (fs_opendir(&ctx->dir, path) != 0) {
        WOLFSSL_MSG("opendir path verify locations failed");
        return BAD_PATH_ERROR;
    }
    ctx->dirp = &ctx->dir;

    while ((fs_readdir(&ctx->dir, &ctx->entry)) != 0) {
        dnameLen = (int)XSTRLEN(ctx->entry.name);

        if (pathLen + dnameLen + 2 >= MAX_FILENAME_SZ) {
            ret = BAD_PATH_ERROR;
            break;
        }
        XSTRNCPY(ctx->name, path, pathLen + 1);
        ctx->name[pathLen] = '/';

        /* Use dnameLen + 1 for GCC 8 warnings of truncating d_name. Because
         * of earlier check it is known that dnameLen is less than
         * MAX_FILENAME_SZ - (pathLen + 2)  so dnameLen +1 will fit */
        XSTRNCPY(ctx->name + pathLen + 1, ctx->entry.name, dnameLen + 1);
        if (fs_stat(ctx->name, &ctx->s) != 0) {
            WOLFSSL_MSG("stat on name failed");
            ret = BAD_PATH_ERROR;
            break;
        } else if (ctx->s.type == FS_DIR_ENTRY_FILE) {
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#elif defined(WOLFSSL_TELIT_M2MB)
    ctx->dir = m2mb_fs_opendir((const CHAR*)path);
    if (ctx->dir == NULL) {
        WOLFSSL_MSG("opendir path verify locations failed");
        return BAD_PATH_ERROR;
    }

    while ((ctx->entry = m2mb_fs_readdir(ctx->dir)) != NULL) {
        dnameLen = (int)XSTRLEN(ctx->entry->d_name);

        if (pathLen + dnameLen + 2 >= MAX_FILENAME_SZ) {
            ret = BAD_PATH_ERROR;
            break;
        }
        XSTRNCPY(ctx->name, path, pathLen + 1);
        ctx->name[pathLen] = '/';

        /* Use dnameLen + 1 for GCC 8 warnings of truncating d_name. Because
         * of earlier check it is known that dnameLen is less than
         * MAX_FILENAME_SZ - (pathLen + 2)  so dnameLen +1 will fit */
        XSTRNCPY(ctx->name + pathLen + 1, ctx->entry->d_name, dnameLen + 1);

        if (m2mb_fs_stat(ctx->name, &ctx->s) != 0) {
            WOLFSSL_MSG("stat on name failed");
            ret = BAD_PATH_ERROR;
            break;
        }
        else if (ctx->s.st_mode & M2MB_S_IFREG) {
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#else
    ctx->dir = opendir(path);
    if (ctx->dir == NULL) {
        WOLFSSL_MSG("opendir path verify locations failed");
        return BAD_PATH_ERROR;
    }

    while ((ctx->entry = readdir(ctx->dir)) != NULL) {
        dnameLen = (int)XSTRLEN(ctx->entry->d_name);

        if (pathLen + dnameLen + 2 >= MAX_FILENAME_SZ) {
            ret = BAD_PATH_ERROR;
            break;
        }
        XSTRNCPY(ctx->name, path, pathLen + 1);
        ctx->name[pathLen] = '/';

        /* Use dnameLen + 1 for GCC 8 warnings of truncating d_name. Because
         * of earlier check it is known that dnameLen is less than
         * MAX_FILENAME_SZ - (pathLen + 2)  so dnameLen +1 will fit */
        XSTRNCPY(ctx->name + pathLen + 1, ctx->entry->d_name, dnameLen + 1);
        if (stat(ctx->name, &ctx->s) != 0) {
            WOLFSSL_MSG("stat on name failed");
            ret = BAD_PATH_ERROR;
            break;
        } else if (S_ISREG(ctx->s.st_mode)) {
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#endif
    wc_ReadDirClose(ctx);

    return ret;
}

/* returns 0 if file found, WC_READDIR_NOFILE if no more files */
int wc_ReadDirNext(ReadDirCtx* ctx, const char* path, char** name)
{
    int ret = WC_READDIR_NOFILE; /* default to no file found */
    int pathLen = 0;
    int dnameLen = 0;

    if (name)
        *name = NULL;

    if (ctx == NULL || path == NULL) {
        return BAD_FUNC_ARG;
    }

    XMEMSET(ctx->name, 0, MAX_FILENAME_SZ);
    pathLen = (int)XSTRLEN(path);

#ifdef USE_WINDOWS_API
    while (FindNextFileA(ctx->hFind, &ctx->FindFileData)) {
        if (!(ctx->FindFileData.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)) {
            dnameLen = (int)XSTRLEN(ctx->FindFileData.cFileName);

            if (pathLen + dnameLen + 2 > MAX_FILENAME_SZ) {
                return BAD_PATH_ERROR;
            }
            XSTRNCPY(ctx->name, path, pathLen + 1);
            ctx->name[pathLen] = '\\';
            XSTRNCPY(ctx->name + pathLen + 1,
                     ctx->FindFileData.cFileName,
                     MAX_FILENAME_SZ - pathLen - 1);
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#elif defined(WOLFSSL_ZEPHYR)
    while ((fs_readdir(&ctx->dir, &ctx->entry)) != 0) {
        dnameLen = (int)XSTRLEN(ctx->entry.name);

        if (pathLen + dnameLen + 2 >= MAX_FILENAME_SZ) {
            ret = BAD_PATH_ERROR;
            break;
        }
        XSTRNCPY(ctx->name, path, pathLen + 1);
        ctx->name[pathLen] = '/';
        /* Use dnameLen + 1 for GCC 8 warnings of truncating d_name. Because
         * of earlier check it is known that dnameLen is less than
         * MAX_FILENAME_SZ - (pathLen + 2) so that dnameLen +1 will fit */
        XSTRNCPY(ctx->name + pathLen + 1, ctx->entry.name, dnameLen + 1);

        if (fs_stat(ctx->name, &ctx->s) != 0) {
            WOLFSSL_MSG("stat on name failed");
            ret = BAD_PATH_ERROR;
            break;
        } else if (ctx->s.type == FS_DIR_ENTRY_FILE) {
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#elif defined(WOLFSSL_TELIT_M2MB)
    while ((ctx->entry = m2mb_fs_readdir(ctx->dir)) != NULL) {
        dnameLen = (int)XSTRLEN(ctx->entry->d_name);

        if (pathLen + dnameLen + 2 >= MAX_FILENAME_SZ) {
            ret = BAD_PATH_ERROR;
            break;
        }
        XSTRNCPY(ctx->name, path, pathLen + 1);
        ctx->name[pathLen] = '/';

        /* Use dnameLen + 1 for GCC 8 warnings of truncating d_name. Because
         * of earlier check it is known that dnameLen is less than
         * MAX_FILENAME_SZ - (pathLen + 2)  so dnameLen +1 will fit */
        XSTRNCPY(ctx->name + pathLen + 1, ctx->entry->d_name, dnameLen + 1);

        if (m2mb_fs_stat(ctx->name, &ctx->s) != 0) {
            WOLFSSL_MSG("stat on name failed");
            ret = BAD_PATH_ERROR;
            break;
        }
        else if (ctx->s.st_mode & M2MB_S_IFREG) {
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#else
    while ((ctx->entry = readdir(ctx->dir)) != NULL) {
        dnameLen = (int)XSTRLEN(ctx->entry->d_name);

        if (pathLen + dnameLen + 2 >= MAX_FILENAME_SZ) {
            ret = BAD_PATH_ERROR;
            break;
        }
        XSTRNCPY(ctx->name, path, pathLen + 1);
        ctx->name[pathLen] = '/';
        /* Use dnameLen + 1 for GCC 8 warnings of truncating d_name. Because
         * of earlier check it is known that dnameLen is less than
         * MAX_FILENAME_SZ - (pathLen + 2) so that dnameLen +1 will fit */
        XSTRNCPY(ctx->name + pathLen + 1, ctx->entry->d_name, dnameLen + 1);

        if (stat(ctx->name, &ctx->s) != 0) {
            WOLFSSL_MSG("stat on name failed");
            ret = BAD_PATH_ERROR;
            break;
        } else if (S_ISREG(ctx->s.st_mode)) {
            if (name)
                *name = ctx->name;
            return 0;
        }
    }
#endif

    wc_ReadDirClose(ctx);

    return ret;
}

void wc_ReadDirClose(ReadDirCtx* ctx)
{
    if (ctx == NULL) {
        return;
    }

#ifdef USE_WINDOWS_API
    if (ctx->hFind != INVALID_HANDLE_VALUE) {
        FindClose(ctx->hFind);
        ctx->hFind = INVALID_HANDLE_VALUE;
    }
#elif defined(WOLFSSL_ZEPHYR)
    if (ctx->dirp) {
        fs_closedir(ctx->dirp);
        ctx->dirp = NULL;
    }
#elif defined(WOLFSSL_TELIT_M2MB)
    if (ctx->dir) {
        m2mb_fs_closedir(ctx->dir);
        ctx->dir = NULL;
    }
#else
    if (ctx->dir) {
        closedir(ctx->dir);
        ctx->dir = NULL;
    }
#endif
}

#endif /* !NO_WOLFSSL_DIR */
#endif /* !NO_FILESYSTEM */

#if !defined(NO_FILESYSTEM) && defined(WOLFSSL_ZEPHYR)
XFILE z_fs_open(const char* filename, const char* perm)
{
    XFILE file;

    file = XMALLOC(sizeof(*file), NULL, DYNAMIC_TYPE_FILE);
    if (file != NULL) {
        if (fs_open(file, filename) != 0) {
            XFREE(file, NULL, DYNAMIC_TYPE_FILE);
            file = NULL;
        }
    }

    return file;
}

int z_fs_close(XFILE file)
{
    int ret;

    if (file == NULL)
        return -1;
    ret = (fs_close(file) == 0) ? 0 : -1;

    XFREE(file, NULL, DYNAMIC_TYPE_FILE);

    return ret;
}

#endif /* !NO_FILESYSTEM && !WOLFSSL_ZEPHYR */

#if !defined(WOLFSSL_USER_MUTEX) 
wolfSSL_Mutex* wc_InitAndAllocMutex(void)
{
    wolfSSL_Mutex* m = (wolfSSL_Mutex*) XMALLOC(sizeof(wolfSSL_Mutex), NULL,
            DYNAMIC_TYPE_MUTEX);
    if (m != NULL) {
        if (wc_InitMutex(m) != 0) {
            WOLFSSL_MSG("Init Mutex failed");
            XFREE(m, NULL, DYNAMIC_TYPE_MUTEX);
            m = NULL;
        }
    }
    else {
        WOLFSSL_MSG("Memory error with Mutex allocation");
    }

    return m;
}
#endif

#ifdef USE_WOLF_STRTOK
/* String token (delim) search. If str is null use nextp. */
char* wc_strtok(char *str, const char *delim, char **nextp)
{
    char* ret;
    int i, j;

    /* Use next if str is NULL */
    if (str == NULL && nextp)
        str = *nextp;

    /* verify str input */
    if (str == NULL || *str == '\0')
        return NULL;

    /* match on entire delim */
    for (i = 0; str[i]; i++) {
        for (j = 0; delim[j]; j++) {
            if (delim[j] == str[i])
                break;
        }
        if (!delim[j])
            break;
    }
    str += i;
    /* if end of string, not found so return NULL */
    if (*str == '\0')
        return NULL;

    ret = str;

    /* match on first delim */
    for (i = 0; str[i]; i++) {
        for (j = 0; delim[j]; j++) {
            if (delim[j] == str[i])
                break;
        }
        if (delim[j] == str[i])
            break;
    }
    str += i;

    /* null terminate found string */
    if (*str)
        *str++ = '\0';

    /* return pointer to next */
    if (nextp)
        *nextp = str;

    return ret;
}
#endif /* USE_WOLF_STRTOK */

#ifdef USE_WOLF_STRSEP
char* wc_strsep(char **stringp, const char *delim)
{
    char *s, *tok;
    const char *spanp;

    /* null check */
    if (stringp == NULL || *stringp == NULL)
        return NULL;

    s = *stringp;
    for (tok = s; *tok; ++tok) {
        for (spanp = delim; *spanp; ++spanp) {
            /* found delimiter */
            if (*tok == *spanp) {
                *tok = '\0'; /* replace delim with null term */
                *stringp = tok + 1; /* return past delim */
                return s;
            }
        }
    }

    *stringp = NULL;
    return s;
}
#endif /* USE_WOLF_STRSEP */

#if WOLFSSL_CRYPT_HW_MUTEX
/* Mutex for protection of cryptography hardware */
static wolfSSL_Mutex wcCryptHwMutex;
static int wcCryptHwMutexInit = 0;

int wolfSSL_CryptHwMutexInit(void)
{
    int ret = 0;
    if (wcCryptHwMutexInit == 0) {
        ret = wc_InitMutex(&wcCryptHwMutex);
        if (ret == 0) {
            wcCryptHwMutexInit = 1;
        }
    }
    return ret;
}
int wolfSSL_CryptHwMutexLock(void)
{
    int ret = BAD_MUTEX_E;
    /* Make sure HW Mutex has been initialized */
    ret = wolfSSL_CryptHwMutexInit();
    if (ret == 0) {
        ret = wc_LockMutex(&wcCryptHwMutex);
    }
    return ret;
}
int wolfSSL_CryptHwMutexUnLock(void)
{
    int ret = BAD_MUTEX_E;
    if (wcCryptHwMutexInit) {
        ret = wc_UnLockMutex(&wcCryptHwMutex);
    }
    return ret;
}
#endif /* WOLFSSL_CRYPT_HW_MUTEX */


/* ---------------------------------------------------------------------------*/
/* Mutex Ports */
/* ---------------------------------------------------------------------------*/
#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    static mutex_cb*     compat_mutex_cb = NULL;

    /* Function that locks or unlocks a mutex based on the flag passed in.
     *
     * flag lock or unlock i.e. CRYPTO_LOCK
     * type the type of lock to unlock or lock
     * file name of the file calling
     * line the line number from file calling
     */
    int wc_LockMutex_ex(int flag, int type, const char* file, int line)
    {
        if (compat_mutex_cb != NULL) {
            compat_mutex_cb(flag, type, file, line);
            return 0;
        }
        else {
            WOLFSSL_MSG("Mutex call back function not set. Call wc_SetMutexCb");
            return BAD_STATE_E;
        }
    }


    /* Set the callback function to use for locking/unlocking mutex
     *
     * cb callback function to use
     */
    int wc_SetMutexCb(mutex_cb* cb)
    {
        compat_mutex_cb = cb;
        return 0;
    }
#endif /* defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER) */
#ifdef SINGLE_THREADED

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        (void)m;
        return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex *m)
    {
        (void)m;
        return 0;
    }


    int wc_LockMutex(wolfSSL_Mutex *m)
    {
        (void)m;
        return 0;
    }


    int wc_UnLockMutex(wolfSSL_Mutex *m)
    {
        (void)m;
        return 0;
    }

#elif defined(FREERTOS) || defined(FREERTOS_TCP) || \
  defined(FREESCALE_FREE_RTOS)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        int iReturn;

        *m = ( wolfSSL_Mutex ) xSemaphoreCreateMutex();
        if( *m != NULL )
            iReturn = 0;
        else
            iReturn = BAD_MUTEX_E;

        return iReturn;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        vSemaphoreDelete( *m );
        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        /* Assume an infinite block, or should there be zero block? */
        xSemaphoreTake( *m, portMAX_DELAY );
        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        xSemaphoreGive( *m );
        return 0;
    }

#elif defined(WOLFSSL_SAFERTOS)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        vSemaphoreCreateBinary(m->mutexBuffer, m->mutex);
        if (m->mutex == NULL)
            return BAD_MUTEX_E;

        return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        (void)m;
        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        /* Assume an infinite block */
        xSemaphoreTake(m->mutex, portMAX_DELAY);
        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        xSemaphoreGive(m->mutex);
        return 0;
    }

#elif defined(USE_WINDOWS_API)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        InitializeCriticalSection(m);
        return 0;
    }


    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        DeleteCriticalSection(m);
        return 0;
    }


    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        EnterCriticalSection(m);
        return 0;
    }


    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        LeaveCriticalSection(m);
        return 0;
    }

#elif defined(WOLFSSL_PTHREADS)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        if (pthread_mutex_init(m, 0) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }


    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        if (pthread_mutex_destroy(m) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }


    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        if (pthread_mutex_lock(m) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }


    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        if (pthread_mutex_unlock(m) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }

#elif defined(WOLFSSL_VXWORKS)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        if (m) {
            if ((*m = semMCreate(0)) != SEM_ID_NULL)
                return 0;
        }
        return BAD_MUTEX_E;
    }


    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        if (m) {
            if (semDelete(*m) == OK)
                return 0;
        }
        return BAD_MUTEX_E;
    }


    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        if (m) {
            if (semTake(*m, WAIT_FOREVER) == OK)
                return 0;
        }
        return BAD_MUTEX_E;
    }


    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        if (m) {
            if (semGive(*m) == OK)
                return 0;
        }
        return BAD_MUTEX_E;
    }

#elif defined(THREADX)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        if (tx_mutex_create(m, "wolfSSL Mutex", TX_NO_INHERIT) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }


    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        if (tx_mutex_delete(m) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }


    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        if (tx_mutex_get(m, TX_WAIT_FOREVER) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        if (tx_mutex_put(m) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }

#elif defined(WOLFSSL_DEOS)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        mutexStatus mutStat;
        /*
        The empty string "" denotes an anonymous mutex, so objects do not cause name collisions.
        `protectWolfSSLTemp` in an XML configuration element template describing a mutex.
        */
        if (m) {
            mutStat = createMutex("", "protectWolfSSLTemp", m);
            if (mutStat == mutexSuccess)
                return 0;
            else{
                WOLFSSL_MSG("wc_InitMutex failed");
                return mutStat;
            }
        }
        return BAD_MUTEX_E;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        mutexStatus mutStat;
        if (m) {
            mutStat = deleteMutex(*m);
            if (mutStat == mutexSuccess)
                return 0;
            else{
                WOLFSSL_MSG("wc_FreeMutex failed");
                return mutStat;
            }
        }
        return BAD_MUTEX_E;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        mutexStatus mutStat;
        if (m) {
            mutStat = lockMutex(*m);
            if (mutStat == mutexSuccess)
                return 0;
            else{
                WOLFSSL_MSG("wc_LockMutex failed");
                return mutStat;
            }
        }
        return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        mutexStatus mutStat;
        if (m) {
            mutStat = unlockMutex(*m);
            if (mutStat== mutexSuccess)
                return 0;
            else{
                WOLFSSL_MSG("wc_UnLockMutex failed");
                return mutStat;
            }
        }
        return BAD_MUTEX_E;
    }

#elif defined(MICRIUM)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        OS_ERR err;

        OSMutexCreate(m, "wolfSSL Mutex", &err);

        if (err == OS_ERR_NONE)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        #if (OS_CFG_MUTEX_DEL_EN == DEF_ENABLED)
            OS_ERR err;

            OSMutexDel(m, OS_OPT_DEL_ALWAYS, &err);

            if (err == OS_ERR_NONE)
                return 0;
            else
                return BAD_MUTEX_E;
        #else
            return 0;
        #endif
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        OS_ERR err;

        OSMutexPend(m, 0, OS_OPT_PEND_BLOCKING, NULL, &err);

        if (err == OS_ERR_NONE)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        OS_ERR err;

        OSMutexPost(m, OS_OPT_POST_NONE, &err);

        if (err == OS_ERR_NONE)
            return 0;
        else
            return BAD_MUTEX_E;
    }

#elif defined(EBSNET)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        if (rtp_sig_mutex_alloc(m, "wolfSSL Mutex") == -1)
            return BAD_MUTEX_E;
        else
            return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        rtp_sig_mutex_free(*m);
        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        if (rtp_sig_mutex_claim_timed(*m, RTIP_INF) == 0)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        rtp_sig_mutex_release(*m);
        return 0;
    }

    int ebsnet_fseek(int a, long b, int c)
    {
        int retval;

        retval = vf_lseek(a, b, c);
        if (retval > 0)
            retval = 0;
        else
            retval =  -1;

        return(retval);
    }

#elif defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        if (_mutex_init(m, NULL) == MQX_EOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        if (_mutex_destroy(m) == MQX_EOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        if (_mutex_lock(m) == MQX_EOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        if (_mutex_unlock(m) == MQX_EOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }

#elif defined(WOLFSSL_TIRTOS)
    #include <xdc/runtime/Error.h>

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        Semaphore_Params params;
        Error_Block eb;

        Error_init(&eb);
        Semaphore_Params_init(&params);
        params.mode = Semaphore_Mode_BINARY;

        *m = Semaphore_create(1, &params, &eb);
        if (Error_check(&eb)) {
            Error_raise(&eb, Error_E_generic, "Failed to Create the semaphore.",
                NULL);
            return BAD_MUTEX_E;
        }
        else
            return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        Semaphore_delete(m);

        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        Semaphore_pend(*m, BIOS_WAIT_FOREVER);

        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        Semaphore_post(*m);

        return 0;
    }

#elif defined(WOLFSSL_uITRON4)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        int iReturn;
        m->sem.sematr  = TA_TFIFO;
        m->sem.isemcnt = 1;
        m->sem.maxsem  = 1;
        m->sem.name    = NULL;

        m->id = acre_sem(&m->sem);
        if( m->id != E_OK )
            iReturn = 0;
        else
            iReturn = BAD_MUTEX_E;

        return iReturn;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        del_sem( m->id );
        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        wai_sem(m->id);
        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        sig_sem(m->id);
        return 0;
    }

    /****  uITRON malloc/free ***/
    static ID ID_wolfssl_MPOOL = 0;
    static T_CMPL wolfssl_MPOOL = {TA_TFIFO, 0, NULL, "wolfSSL_MPOOL"};

    int uITRON4_minit(size_t poolsz) {
        ER ercd;
        wolfssl_MPOOL.mplsz = poolsz;
        ercd = acre_mpl(&wolfssl_MPOOL);
        if (ercd > 0) {
            ID_wolfssl_MPOOL = ercd;
            return 0;
        } else {
            return -1;
        }
    }

    void *uITRON4_malloc(size_t sz) {
        ER ercd;
        void *p = NULL;
        ercd = get_mpl(ID_wolfssl_MPOOL, sz, (VP)&p);
        if (ercd == E_OK) {
            return p;
        } else {
            return 0;
        }
    }

    void *uITRON4_realloc(void *p, size_t sz) {
      ER ercd;
      void *newp;
      if(p) {
          ercd = get_mpl(ID_wolfssl_MPOOL, sz, (VP)&newp);
          if (ercd == E_OK) {
              XMEMCPY(newp, p, sz);
              ercd = rel_mpl(ID_wolfssl_MPOOL, (VP)p);
              if (ercd == E_OK) {
                  return newp;
              }
          }
      }
      return 0;
    }

    void uITRON4_free(void *p) {
        ER ercd;
        ercd = rel_mpl(ID_wolfssl_MPOOL, (VP)p);
        if (ercd == E_OK) {
            return;
        } else {
            return;
        }
    }

#elif defined(WOLFSSL_uTKERNEL2)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        int iReturn;
        m->sem.sematr  = TA_TFIFO;
        m->sem.isemcnt = 1;
        m->sem.maxsem  = 1;

        m->id = tk_cre_sem(&m->sem);
        if( m->id != NULL )
            iReturn = 0;
        else
            iReturn = BAD_MUTEX_E;

        return iReturn;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        tk_del_sem(m->id);
        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        tk_wai_sem(m->id, 1, TMO_FEVR);
        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        tk_sig_sem(m->id, 1);
        return 0;
    }

    /****  uT-Kernel malloc/free ***/
    static ID ID_wolfssl_MPOOL = 0;
    static T_CMPL wolfssl_MPOOL = {
        NULL,       /* Extended information */
        TA_TFIFO,   /* Memory pool attribute */
        0,          /* Size of whole memory pool (byte) */
        "wolfSSL"   /* Object name (max 8-char) */
    };

    int uTKernel_init_mpool(unsigned int sz) {
        ER ercd;
        wolfssl_MPOOL.mplsz = sz;
        ercd = tk_cre_mpl(&wolfssl_MPOOL);
        if (ercd > 0) {
            ID_wolfssl_MPOOL = ercd;
            return 0;
        } else {
            return (int)ercd;
        }
    }

    void *uTKernel_malloc(unsigned int sz) {
        ER ercd;
        void *p = NULL;
        ercd = tk_get_mpl(ID_wolfssl_MPOOL, sz, (VP)&p, TMO_FEVR);
        if (ercd == E_OK) {
            return p;
        } else {
            return 0;
        }
    }

    void *uTKernel_realloc(void *p, unsigned int sz) {
      ER ercd;
      void *newp;
      if (p) {
          ercd = tk_get_mpl(ID_wolfssl_MPOOL, sz, (VP)&newp, TMO_FEVR);
          if (ercd == E_OK) {
              XMEMCPY(newp, p, sz);
              ercd = tk_rel_mpl(ID_wolfssl_MPOOL, (VP)p);
              if (ercd == E_OK) {
                  return newp;
              }
          }
      }
      return 0;
    }

    void uTKernel_free(void *p) {
        ER ercd;
        ercd = tk_rel_mpl(ID_wolfssl_MPOOL, (VP)p);
        if (ercd == E_OK) {
            return;
        } else {
            return;
        }
    }

#elif defined (WOLFSSL_FROSTED)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        *m = mutex_init();
        if (*m)
            return 0;
        else
            return -1;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        mutex_destroy(*m);
        return(0);
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        mutex_lock(*m);
        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        mutex_unlock(*m);
        return 0;
    }

#elif defined(WOLFSSL_CMSIS_RTOS)

    #define CMSIS_NMUTEX 10
    osMutexDef(wolfSSL_mt0);  osMutexDef(wolfSSL_mt1);  osMutexDef(wolfSSL_mt2);
    osMutexDef(wolfSSL_mt3);  osMutexDef(wolfSSL_mt4);  osMutexDef(wolfSSL_mt5);
    osMutexDef(wolfSSL_mt6);  osMutexDef(wolfSSL_mt7);  osMutexDef(wolfSSL_mt8);
    osMutexDef(wolfSSL_mt9);

    static const osMutexDef_t *CMSIS_mutex[] = { osMutex(wolfSSL_mt0),
        osMutex(wolfSSL_mt1),    osMutex(wolfSSL_mt2),   osMutex(wolfSSL_mt3),
        osMutex(wolfSSL_mt4),    osMutex(wolfSSL_mt5),   osMutex(wolfSSL_mt6),
        osMutex(wolfSSL_mt7),    osMutex(wolfSSL_mt8),   osMutex(wolfSSL_mt9) };

    static osMutexId CMSIS_mutexID[CMSIS_NMUTEX] = {0};

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        int i;
        for (i=0; i<CMSIS_NMUTEX; i++) {
            if(CMSIS_mutexID[i] == 0) {
                CMSIS_mutexID[i] = osMutexCreate(CMSIS_mutex[i]);
                (*m) = CMSIS_mutexID[i];
            return 0;
            }
        }
        return -1;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        int i;
        osMutexDelete   (*m);
        for (i=0; i<CMSIS_NMUTEX; i++) {
            if(CMSIS_mutexID[i] == (*m)) {
                CMSIS_mutexID[i] = 0;
                return(0);
            }
        }
        return(-1);
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        osMutexWait(*m, osWaitForever);
        return(0);
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        osMutexRelease (*m);
        return 0;
    }

#elif defined(WOLFSSL_CMSIS_RTOSv2)
    int wc_InitMutex(wolfSSL_Mutex *m)
    {
        static const osMutexAttr_t attr = {
            "wolfSSL_mutex", osMutexRecursive, NULL, 0};

        if ((*m = osMutexNew(&attr)) != NULL)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_FreeMutex(wolfSSL_Mutex *m)
    {
        if (osMutexDelete(*m) == osOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }


    int wc_LockMutex(wolfSSL_Mutex *m)
    {
        if (osMutexAcquire(*m, osWaitForever) == osOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex *m)
    {
        if (osMutexRelease(*m) == osOK)
            return 0;
        else
            return BAD_MUTEX_E;
    }

#elif defined(WOLFSSL_MDK_ARM)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        os_mut_init (m);
        return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        return(0);
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        os_mut_wait (m, 0xffff);
        return(0);
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        os_mut_release (m);
        return 0;
    }

#elif defined(INTIME_RTOS)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        int ret = 0;

        if (m == NULL)
            return BAD_FUNC_ARG;

        *m = CreateRtSemaphore(
            1,                      /* initial unit count */
            1,                      /* maximum unit count */
            PRIORITY_QUEUING        /* creation flags: FIFO_QUEUING or PRIORITY_QUEUING */
        );
        if (*m == BAD_RTHANDLE) {
            ret = GetLastRtError();
            if (ret != E_OK)
                ret = BAD_MUTEX_E;
        }
        return ret;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        int ret = 0;
        BOOLEAN del;

        if (m == NULL)
            return BAD_FUNC_ARG;

        del = DeleteRtSemaphore(
            *m                      /* handle for RT semaphore */
        );
    	if (del != TRUE)
    		ret = BAD_MUTEX_E;

        return ret;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        int ret = 0;
        DWORD lck;

        if (m == NULL)
            return BAD_FUNC_ARG;

        lck = WaitForRtSemaphore(
            *m,                     /* handle for RT semaphore */
            1,                      /* number of units to wait for */
            WAIT_FOREVER            /* number of milliseconds to wait for units */
        );
        if (lck == WAIT_FAILED) {
            ret = GetLastRtError();
            if (ret != E_OK)
                ret = BAD_MUTEX_E;
        }
        return ret;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        int ret = 0;
        BOOLEAN rel;

        if (m == NULL)
            return BAD_FUNC_ARG;

        rel = ReleaseRtSemaphore(
            *m,                     /* handle for RT semaphore */
            1                       /* number of units to release to semaphore */
        );
    	if (rel != TRUE)
    		ret = BAD_MUTEX_E;

        return ret;
    }

#elif defined(WOLFSSL_NUCLEUS_1_2)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        /* Call the Nucleus function to create the semaphore */
        if (NU_Create_Semaphore(m, "WOLFSSL_MTX", 1,
                                NU_PRIORITY) == NU_SUCCESS) {
            return 0;
        }

        return BAD_MUTEX_E;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        if (NU_Delete_Semaphore(m) == NU_SUCCESS)
            return 0;

        return BAD_MUTEX_E;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        /* passing suspend task option */
        if (NU_Obtain_Semaphore(m, NU_SUSPEND) == NU_SUCCESS)
            return 0;

        return BAD_MUTEX_E;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        if (NU_Release_Semaphore(m) == NU_SUCCESS)
            return 0;

        return BAD_MUTEX_E;
    }

#elif defined(WOLFSSL_ZEPHYR)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        k_mutex_init(m);

        return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        int ret = 0;

        if (k_mutex_lock(m, K_FOREVER) != 0)
            ret = BAD_MUTEX_E;

        return ret;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        k_mutex_unlock(m);

        return 0;
    }

#elif defined(WOLFSSL_TELIT_M2MB)

    int wc_InitMutex(wolfSSL_Mutex* m)
    {
        M2MB_OS_RESULT_E        osRes;
        M2MB_OS_MTX_ATTR_HANDLE mtxAttrHandle;
        UINT32                  inheritVal = 1;

        osRes = m2mb_os_mtx_setAttrItem(&mtxAttrHandle,
                                    CMDS_ARGS(
                                      M2MB_OS_MTX_SEL_CMD_CREATE_ATTR, NULL,
                                      M2MB_OS_MTX_SEL_CMD_NAME, "wolfMtx",
                                      M2MB_OS_MTX_SEL_CMD_INHERIT, inheritVal
                                    )
                                );
        if (osRes != M2MB_OS_SUCCESS) {
            return BAD_MUTEX_E;
        }

        osRes = m2mb_os_mtx_init(m, &mtxAttrHandle);
        if (osRes != M2MB_OS_SUCCESS) {
            return BAD_MUTEX_E;
        }

        return 0;
    }

    int wc_FreeMutex(wolfSSL_Mutex* m)
    {
        M2MB_OS_RESULT_E osRes;

        if (m == NULL)
            return BAD_MUTEX_E;

        osRes = m2mb_os_mtx_deinit(*m);
        if (osRes != M2MB_OS_SUCCESS) {
            return BAD_MUTEX_E;
        }

        return 0;
    }

    int wc_LockMutex(wolfSSL_Mutex* m)
    {
        M2MB_OS_RESULT_E osRes;

        if (m == NULL)
            return BAD_MUTEX_E;

        osRes = m2mb_os_mtx_get(*m, M2MB_OS_WAIT_FOREVER);
        if (osRes != M2MB_OS_SUCCESS) {
            return BAD_MUTEX_E;
        }

        return 0;
    }

    int wc_UnLockMutex(wolfSSL_Mutex* m)
    {
        M2MB_OS_RESULT_E osRes;

        if (m == NULL)
            return BAD_MUTEX_E;

        osRes = m2mb_os_mtx_put(*m);
        if (osRes != M2MB_OS_SUCCESS) {
            return BAD_MUTEX_E;
        }

        return 0;
    }

#elif defined(WOLFSSL_USER_MUTEX)

    /* Use user own mutex */
    
    /*
    int wc_InitMutex(wolfSSL_Mutex* m) { ... }
    int wc_FreeMutex(wolfSSL_Mutex *m) { ... }
    int wc_LockMutex(wolfSSL_Mutex *m) { ... }
    int wc_UnLockMutex(wolfSSL_Mutex *m) { ... }
    */

#else
    #warning No mutex handling defined

#endif

#ifndef NO_ASN_TIME
#if defined(_WIN32_WCE)
time_t windows_time(time_t* timer)
{
    SYSTEMTIME     sysTime;
    FILETIME       fTime;
    ULARGE_INTEGER intTime;
    time_t         localTime;

    if (timer == NULL)
        timer = &localTime;

    GetSystemTime(&sysTime);
    SystemTimeToFileTime(&sysTime, &fTime);

    XMEMCPY(&intTime, &fTime, sizeof(FILETIME));
    /* subtract EPOCH */
    intTime.QuadPart -= 0x19db1ded53e8000;
    /* to secs */
    intTime.QuadPart /= 10000000;
    *timer = (time_t)intTime.QuadPart;

    return *timer;
}
#endif /*  _WIN32_WCE */

#if defined(WOLFSSL_APACHE_MYNEWT)
#include "os/os_time.h"

time_t mynewt_time(time_t* timer)
{
    time_t now;
    struct os_timeval tv;
    os_gettimeofday(&tv, NULL);
    now = (time_t)tv.tv_sec;
    if(timer != NULL) {
        *timer = now;
    }
    return now;
}
#endif /* WOLFSSL_APACHE_MYNEWT */

#if defined(WOLFSSL_GMTIME)
struct tm* gmtime(const time_t* timer)
{
    #define YEAR0          1900
    #define EPOCH_YEAR     1970
    #define SECS_DAY       (24L * 60L * 60L)
    #define LEAPYEAR(year) (!((year) % 4) && (((year) % 100) || !((year) %400)))
    #define YEARSIZE(year) (LEAPYEAR(year) ? 366 : 365)

    static const int _ytab[2][12] =
    {
        {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31},
        {31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31}
    };

    static struct tm st_time;
    struct tm* ret = &st_time;
    time_t secs = *timer;
    unsigned long dayclock, dayno;
    int year = EPOCH_YEAR;

    dayclock = (unsigned long)secs % SECS_DAY;
    dayno    = (unsigned long)secs / SECS_DAY;

    ret->tm_sec  = (int) dayclock % 60;
    ret->tm_min  = (int)(dayclock % 3600) / 60;
    ret->tm_hour = (int) dayclock / 3600;
    ret->tm_wday = (int) (dayno + 4) % 7;        /* day 0 a Thursday */

    while(dayno >= (unsigned long)YEARSIZE(year)) {
        dayno -= YEARSIZE(year);
        year++;
    }

    ret->tm_year = year - YEAR0;
    ret->tm_yday = (int)dayno;
    ret->tm_mon  = 0;

    while(dayno >= (unsigned long)_ytab[LEAPYEAR(year)][ret->tm_mon]) {
        dayno -= _ytab[LEAPYEAR(year)][ret->tm_mon];
        ret->tm_mon++;
    }

    ret->tm_mday  = (int)++dayno;
    ret->tm_isdst = 0;

    return ret;
}
#endif /* WOLFSSL_GMTIME */


#if defined(HAVE_RTP_SYS)
#define YEAR0          1900

struct tm* rtpsys_gmtime(const time_t* timer)       /* has a gmtime() but hangs */
{
    static struct tm st_time;
    struct tm* ret = &st_time;

    DC_RTC_CALENDAR cal;
    dc_rtc_time_get(&cal, TRUE);

    ret->tm_year  = cal.year - YEAR0;       /* gm starts at 1900 */
    ret->tm_mon   = cal.month - 1;          /* gm starts at 0 */
    ret->tm_mday  = cal.day;
    ret->tm_hour  = cal.hour;
    ret->tm_min   = cal.minute;
    ret->tm_sec   = cal.second;

    return ret;
}

#endif /* HAVE_RTP_SYS */


#if defined(MICROCHIP_TCPIP_V5) || defined(MICROCHIP_TCPIP)

/*
 * time() is just a stub in Microchip libraries. We need our own
 * implementation. Use SNTP client to get seconds since epoch.
 */
time_t pic32_time(time_t* timer)
{
#ifdef MICROCHIP_TCPIP_V5
    DWORD sec = 0;
#else
    uint32_t sec = 0;
#endif
    time_t localTime;

    if (timer == NULL)
        timer = &localTime;

#ifdef MICROCHIP_MPLAB_HARMONY
    sec = TCPIP_SNTP_UTCSecondsGet();
#else
    sec = SNTPGetUTCSeconds();
#endif
    *timer = (time_t) sec;

    return *timer;
}

#endif /* MICROCHIP_TCPIP || MICROCHIP_TCPIP_V5 */

#if defined(WOLFSSL_DEOS)

time_t deos_time(time_t* timer)
{
    const uint32_t systemTickTimeInHz = 1000000 / systemTickInMicroseconds();
    uint32_t *systemTickPtr = systemTickPointer();

    if (timer != NULL)
        *timer = *systemTickPtr/systemTickTimeInHz;

    #if defined(CURRENT_UNIX_TIMESTAMP)
        /* CURRENT_UNIX_TIMESTAMP is seconds since Jan 01 1970. (UTC) */
        return (time_t) *systemTickPtr/systemTickTimeInHz + CURRENT_UNIX_TIMESTAMP;
    #else
        return (time_t) *systemTickPtr/systemTickTimeInHz;
    #endif
}
#endif /* WOLFSSL_DEOS */

#if defined(MICRIUM)

time_t micrium_time(time_t* timer)
{
    CLK_TS_SEC sec;

    Clk_GetTS_Unix(&sec);

    if (timer != NULL)
        *timer = sec;

    return (time_t) sec;
}

#endif /* MICRIUM */

#if defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)

time_t mqx_time(time_t* timer)
{
    time_t localTime;
    TIME_STRUCT time_s;

    if (timer == NULL)
        timer = &localTime;

    _time_get(&time_s);
    *timer = (time_t) time_s.SECONDS;

    return *timer;
}

#endif /* FREESCALE_MQX || FREESCALE_KSDK_MQX */


#if defined(WOLFSSL_TIRTOS) && defined(USER_TIME)

time_t XTIME(time_t * timer)
{
    time_t sec = 0;

    sec = (time_t) Seconds_get();

    if (timer != NULL)
        *timer = sec;

    return sec;
}

#endif /* WOLFSSL_TIRTOS */

#if defined(WOLFSSL_XILINX)
#include "xrtcpsu.h"

time_t XTIME(time_t * timer)
{
    time_t sec = 0;
    XRtcPsu_Config* con;
    XRtcPsu         rtc;

    con = XRtcPsu_LookupConfig(XPAR_XRTCPSU_0_DEVICE_ID);
    if (con != NULL) {
        if (XRtcPsu_CfgInitialize(&rtc, con, con->BaseAddr) == XST_SUCCESS) {
            sec = (time_t)XRtcPsu_GetCurrentTime(&rtc);
        }
        else {
            WOLFSSL_MSG("Unable to initialize RTC");
        }
    }

    if (timer != NULL)
        *timer = sec;

    return sec;
}

#endif /* WOLFSSL_XILINX */

#if defined(WOLFSSL_ZEPHYR)

time_t z_time(time_t * timer)
{
    struct timespec ts;

    if (clock_gettime(CLOCK_REALTIME, &ts) == 0)
        if (timer != NULL)
            *timer = ts.tv_sec;

    return ts.tv_sec;
}

#endif /* WOLFSSL_ZEPHYR */


#if defined(WOLFSSL_WICED)
    #ifndef WOLFSSL_WICED_PSEUDO_UNIX_EPOCH_TIME
        #error Please define WOLFSSL_WICED_PSEUDO_UNIX_EPOCH_TIME at build time.
    #endif /* WOLFSSL_WICED_PSEUDO_UNIX_EPOCH_TIME */

time_t wiced_pseudo_unix_epoch_time(time_t * timer)
{
    time_t epoch_time;
    /* The time() function return uptime on WICED platform. */
    epoch_time = time(NULL) + WOLFSSL_WICED_PSEUDO_UNIX_EPOCH_TIME;

    if (timer != NULL) {
        *timer = epoch_time;
    }
    return epoch_time;
}
#endif /* WOLFSSL_WICED */

#ifdef WOLFSSL_TELIT_M2MB
    time_t m2mb_xtime(time_t * timer)
    {
        time_t myTime = 0;
        INT32 fd = m2mb_rtc_open("/dev/rtc0", 0);
        if (fd != -1) {
            M2MB_RTC_TIMEVAL_T timeval;

            m2mb_rtc_ioctl(fd, M2MB_RTC_IOCTL_GET_TIMEVAL, &timeval);

            myTime = timeval.sec;

            m2mb_rtc_close(fd);
        }
        return myTime;
    }
    #ifdef WOLFSSL_TLS13
    time_t m2mb_xtime_ms(time_t * timer)
    {
        time_t myTime = 0;
        INT32 fd = m2mb_rtc_open("/dev/rtc0", 0);
        if (fd != -1) {
            M2MB_RTC_TIMEVAL_T timeval;

            m2mb_rtc_ioctl(fd, M2MB_RTC_IOCTL_GET_TIMEVAL, &timeval);

            myTime = timeval.sec + timeval.msec;

            m2mb_rtc_close(fd);
        }
        return myTime;
    }
    #endif /* WOLFSSL_TLS13 */
    #ifndef NO_CRYPT_BENCHMARK
    double m2mb_xtime_bench(int reset)
    {
        double myTime = 0;
        INT32 fd = m2mb_rtc_open("/dev/rtc0", 0);
        if (fd != -1) {
            M2MB_RTC_TIMEVAL_T timeval;

            m2mb_rtc_ioctl(fd, M2MB_RTC_IOCTL_GET_TIMEVAL, &timeval);

            myTime = (double)timeval.sec + ((double)timeval.msec / 1000);

            m2mb_rtc_close(fd);
        }
        return myTime;
    }
    #endif /* !NO_CRYPT_BENCHMARK */
#endif /* WOLFSSL_TELIT_M2MB */

#endif /* !NO_ASN_TIME */

#ifndef WOLFSSL_LEANPSK
char* mystrnstr(const char* s1, const char* s2, unsigned int n)
{
    unsigned int s2_len = (unsigned int)XSTRLEN(s2);

    if (s2_len == 0)
        return (char*)s1;

    while (n >= s2_len && s1[0]) {
        if (s1[0] == s2[0])
            if (XMEMCMP(s1, s2, s2_len) == 0)
                return (char*)s1;
        s1++;
        n--;
    }

    return NULL;
}
#endif

/* custom memory wrappers */
#ifdef WOLFSSL_NUCLEUS_1_2

    /* system memory pool */
    extern NU_MEMORY_POOL System_Memory;

    void* nucleus_malloc(unsigned long size, void* heap, int type)
    {
        STATUS status;
        void*  stack_ptr;

        status = NU_Allocate_Memory(&System_Memory, &stack_ptr, size,
                                    NU_NO_SUSPEND);
        if (status == NU_SUCCESS) {
            return 0;
        } else {
            return stack_ptr;
        }
    }

    void* nucleus_realloc(void* ptr, unsigned long size, void* heap, int type)
    {
        DM_HEADER* old_header;
        word32     old_size, copy_size;
        void*      new_mem;

        /* if ptr is NULL, behave like malloc */
        new_mem = nucleus_malloc(size, NULL, 0);
        if (new_mem == 0 || ptr == 0) {
            return new_mem;
        }

        /* calculate old memory block size */
        /* mem pointers stored in block headers (ref dm_defs.h) */
        old_header = (DM_HEADER*) ((byte*)ptr - DM_OVERHEAD);
        old_size   = (byte*)old_header->dm_next_memory - (byte*)ptr;

        /* copy old to new */
        if (old_size < size) {
            copy_size = old_size;
        } else {
            copy_size = size;
        }
        XMEMCPY(new_mem, ptr, copy_size);

        /* free old */
        nucleus_free(ptr, NULL, 0);

        return new_mem;
    }

    void nucleus_free(void* ptr, void* heap, int type)
    {
        if (ptr != NULL)
            NU_Deallocate_Memory(ptr);
    }

#endif /* WOLFSSL_NUCLEUS_1_2 */

#if defined(WOLFSSL_TI_CRYPT) || defined(WOLFSSL_TI_HASH)
    #include <wolfcrypt/src/port/ti/ti-ccm.c>  /* initialize and Mutex for TI Crypt Engine */
    #include <wolfcrypt/src/port/ti/ti-hash.c> /* md5, sha1, sha224, sha256 */
#endif

#if defined(WOLFSSL_CRYPTOCELL)
    #define WOLFSSL_CRYPTOCELL_C
    #include <wolfcrypt/src/port/arm/cryptoCell.c> /* CC310, RTC and RNG */
    #if !defined(NO_SHA256)
        #define WOLFSSL_CRYPTOCELL_HASH_C
        #include <wolfcrypt/src/port/arm/cryptoCellHash.c> /* sha256 */
    #endif
#endif
