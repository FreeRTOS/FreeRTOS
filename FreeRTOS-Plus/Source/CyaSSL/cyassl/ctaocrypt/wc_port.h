/* port.h
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifndef CTAO_CRYPT_PORT_H
#define CTAO_CRYPT_PORT_H


#ifdef __cplusplus
    extern "C" {
#endif


#ifdef USE_WINDOWS_API 
    #ifdef CYASSL_GAME_BUILD
        #include "system/xtl.h"
    #else
        #ifndef WIN32_LEAN_AND_MEAN
            #define WIN32_LEAN_AND_MEAN
        #endif
        #if defined(_WIN32_WCE) || defined(WIN32_LEAN_AND_MEAN)
            /* On WinCE winsock2.h must be included before windows.h */
            #include <winsock2.h>
        #endif
        #include <windows.h>
    #endif
#elif defined(THREADX)
    #ifndef SINGLE_THREADED
        #include "tx_api.h"
    #endif
#elif defined(MICRIUM)
    /* do nothing, just don't pick Unix */
#elif defined(FREERTOS) || defined(CYASSL_SAFERTOS)
    /* do nothing */
#elif defined(EBSNET)
    /* do nothing */
#elif defined(FREESCALE_MQX)
    /* do nothing */
#elif defined(CYASSL_MDK_ARM)
    #if defined(CYASSL_MDK5)
         #include "cmsis_os.h"
    #else
        #include <rtl.h>
    #endif
#elif defined(CYASSL_CMSIS_RTOS)
    #include "cmsis_os.h"    
#else
    #ifndef SINGLE_THREADED
        #define CYASSL_PTHREADS
        #include <pthread.h>
    #endif
    #if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)
        #include <unistd.h>      /* for close of BIO */
    #endif
#endif


#ifdef SINGLE_THREADED
    typedef int CyaSSL_Mutex;
#else /* MULTI_THREADED */
    /* FREERTOS comes first to enable use of FreeRTOS Windows simulator only */
    #ifdef FREERTOS
        typedef xSemaphoreHandle CyaSSL_Mutex;
    #elif defined(CYASSL_SAFERTOS)
        typedef struct CyaSSL_Mutex {
            signed char mutexBuffer[portQUEUE_OVERHEAD_BYTES];
            xSemaphoreHandle mutex;
        } CyaSSL_Mutex;
    #elif defined(USE_WINDOWS_API)
        typedef CRITICAL_SECTION CyaSSL_Mutex;
    #elif defined(CYASSL_PTHREADS)
        typedef pthread_mutex_t CyaSSL_Mutex;
    #elif defined(THREADX)
        typedef TX_MUTEX CyaSSL_Mutex;
    #elif defined(MICRIUM)
        typedef OS_MUTEX CyaSSL_Mutex;
    #elif defined(EBSNET)
        typedef RTP_MUTEX CyaSSL_Mutex;
    #elif defined(FREESCALE_MQX)
        typedef MUTEX_STRUCT CyaSSL_Mutex;
    #elif defined(CYASSL_MDK_ARM)
        #if defined(CYASSL_CMSIS_RTOS)
            typedef osMutexId CyaSSL_Mutex;
        #else
            typedef OS_MUT CyaSSL_Mutex;
        #endif
    #elif defined(CYASSL_CMSIS_RTOS)
        typedef osMutexId CyaSSL_Mutex;
    #else
        #error Need a mutex type in multithreaded mode
    #endif /* USE_WINDOWS_API */
#endif /* SINGLE_THREADED */

CYASSL_LOCAL int InitMutex(CyaSSL_Mutex*);
CYASSL_LOCAL int FreeMutex(CyaSSL_Mutex*);
CYASSL_LOCAL int LockMutex(CyaSSL_Mutex*);
CYASSL_LOCAL int UnLockMutex(CyaSSL_Mutex*);


/* filesystem abstraction layer, used by ssl.c */
#ifndef NO_FILESYSTEM

#if defined(EBSNET)
    #define XFILE                    int
    #define XFOPEN(NAME, MODE)       vf_open((const char *)NAME, VO_RDONLY, 0);
    #define XFSEEK                   vf_lseek
    #define XFTELL                   vf_tell
    #define XREWIND                  vf_rewind
    #define XFREAD(BUF, SZ, AMT, FD) vf_read(FD, BUF, SZ*AMT)
    #define XFWRITE(BUF, SZ, AMT, FD) vf_write(FD, BUF, SZ*AMT)
    #define XFCLOSE                  vf_close
    #define XSEEK_END                VSEEK_END
    #define XBADFILE                 -1
#elif defined(LSR_FS)
    #include <fs.h>
    #define XFILE                   struct fs_file*
    #define XFOPEN(NAME, MODE)      fs_open((char*)NAME);
    #define XFSEEK(F, O, W)         (void)F
    #define XFTELL(F)               (F)->len
    #define XREWIND(F)              (void)F
    #define XFREAD(BUF, SZ, AMT, F) fs_read(F, (char*)BUF, SZ*AMT)
    #define XFWRITE(BUF, SZ, AMT, F) fs_write(F, (char*)BUF, SZ*AMT)
    #define XFCLOSE                 fs_close
    #define XSEEK_END               0
    #define XBADFILE                NULL
#elif defined(FREESCALE_MQX)
    #define XFILE                   MQX_FILE_PTR
    #define XFOPEN                  fopen
    #define XFSEEK                  fseek
    #define XFTELL                  ftell
    #define XREWIND(F)              fseek(F, 0, IO_SEEK_SET)
    #define XFREAD                  fread
    #define XFWRITE                 fwrite
    #define XFCLOSE                 fclose
    #define XSEEK_END               IO_SEEK_END
    #define XBADFILE                NULL
#elif defined(MICRIUM)
    #include <fs.h>
    #define XFILE      FS_FILE*
    #define XFOPEN     fs_fopen
    #define XFSEEK     fs_fseek
    #define XFTELL     fs_ftell
    #define XREWIND    fs_rewind
    #define XFREAD     fs_fread
    #define XFWRITE    fs_fwrite
    #define XFCLOSE    fs_fclose
    #define XSEEK_END  FS_SEEK_END
    #define XBADFILE   NULL
#else
    /* stdio, default case */
    #define XFILE      FILE*
    #if defined(CYASSL_MDK_ARM)
        #include <stdio.h>
        extern FILE * CyaSSL_fopen(const char *name, const char *mode) ;
        #define XFOPEN     CyaSSL_fopen
    #else
        #define XFOPEN     fopen
    #endif
    #define XFSEEK     fseek
    #define XFTELL     ftell
    #define XREWIND    rewind
    #define XFREAD     fread
    #define XFWRITE    fwrite
    #define XFCLOSE    fclose
    #define XSEEK_END  SEEK_END
    #define XBADFILE   NULL
#endif

#endif /* NO_FILESYSTEM */


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* CTAO_CRYPT_PORT_H */

