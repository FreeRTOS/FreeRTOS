/* logging.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

/* submitted by eof */

#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/error-crypt.h>


#ifdef __cplusplus
    extern "C" {
#endif
    WOLFSSL_API int  wolfSSL_Debugging_ON(void);
    WOLFSSL_API void wolfSSL_Debugging_OFF(void);
#ifdef __cplusplus
    } 
#endif


#ifdef DEBUG_WOLFSSL

/* Set these to default values initially. */
static wolfSSL_Logging_cb log_function = 0;
static int loggingEnabled = 0;

#endif /* DEBUG_WOLFSSL */


int wolfSSL_SetLoggingCb(wolfSSL_Logging_cb f)
{
#ifdef DEBUG_WOLFSSL
    int res = 0;

    if (f)
        log_function = f;
    else
        res = BAD_FUNC_ARG;

    return res;
#else
    (void)f;
    return NOT_COMPILED_IN;
#endif
}


int wolfSSL_Debugging_ON(void)
{
#ifdef DEBUG_WOLFSSL
    loggingEnabled = 1;
    return 0;
#else
    return NOT_COMPILED_IN;
#endif
}


void wolfSSL_Debugging_OFF(void)
{
#ifdef DEBUG_WOLFSSL
    loggingEnabled = 0;
#endif
}


#ifdef DEBUG_WOLFSSL

#ifdef FREESCALE_MQX
    #include <fio.h>
#else
    #include <stdio.h>   /* for default printf stuff */
#endif

#ifdef THREADX
    int dc_log_printf(char*, ...);
#endif

static void wolfssl_log(const int logLevel, const char *const logMessage)
{
    if (log_function)
        log_function(logLevel, logMessage);
    else {
        if (loggingEnabled) {
#ifdef THREADX
            dc_log_printf("%s\n", logMessage);
#elif defined(MICRIUM)
        #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
            NetSecure_TraceOut((CPU_CHAR *)logMessage);
        #endif
#elif defined(WOLFSSL_MDK_ARM)
            fflush(stdout) ;
            printf("%s\n", logMessage);
            fflush(stdout) ;
#else
            fprintf(stderr, "%s\n", logMessage);
#endif
        }
    }
}


void WOLFSSL_MSG(const char* msg)
{
    if (loggingEnabled)
        wolfssl_log(INFO_LOG , msg);
}


void WOLFSSL_ENTER(const char* msg)
{
    if (loggingEnabled) {
        char buffer[80];
        sprintf(buffer, "wolfSSL Entering %s", msg);
        wolfssl_log(ENTER_LOG , buffer);
    }
}


void WOLFSSL_LEAVE(const char* msg, int ret)
{
    if (loggingEnabled) {
        char buffer[80];
        sprintf(buffer, "wolfSSL Leaving %s, return %d", msg, ret);
        wolfssl_log(LEAVE_LOG , buffer);
    }
}


void WOLFSSL_ERROR(int error)
{
    if (loggingEnabled) {
        char buffer[80];
        sprintf(buffer, "wolfSSL error occured, error = %d", error);
        wolfssl_log(ERROR_LOG , buffer);
    }
}

#endif  /* DEBUG_WOLFSSL */
