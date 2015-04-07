/* logging.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

/* submitted by eof */

#include <cyassl/ctaocrypt/logging.h>
#include <cyassl/ctaocrypt/error-crypt.h>


#ifdef __cplusplus
    extern "C" {
#endif
    CYASSL_API int  CyaSSL_Debugging_ON(void);
    CYASSL_API void CyaSSL_Debugging_OFF(void);
#ifdef __cplusplus
    } 
#endif


#ifdef DEBUG_CYASSL

/* Set these to default values initially. */
static CyaSSL_Logging_cb log_function = 0;
static int loggingEnabled = 0;

#endif /* DEBUG_CYASSL */


int CyaSSL_SetLoggingCb(CyaSSL_Logging_cb f)
{
#ifdef DEBUG_CYASSL
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


int CyaSSL_Debugging_ON(void)
{
#ifdef DEBUG_CYASSL
    loggingEnabled = 1;
    return 0;
#else
    return NOT_COMPILED_IN;
#endif
}


void CyaSSL_Debugging_OFF(void)
{
#ifdef DEBUG_CYASSL
    loggingEnabled = 0;
#endif
}


#ifdef DEBUG_CYASSL

#ifdef FREESCALE_MQX
    #include <fio.h>
#else
    #include <stdio.h>   /* for default printf stuff */
#endif

#ifdef THREADX
    int dc_log_printf(char*, ...);
#endif

static void cyassl_log(const int logLevel, const char *const logMessage)
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
#elif defined(CYASSL_MDK_ARM)
            fflush(stdout) ;
            printf("%s\n", logMessage);
            fflush(stdout) ;
#else
            fprintf(stderr, "%s\n", logMessage);
#endif
        }
    }
}


void CYASSL_MSG(const char* msg)
{
    if (loggingEnabled)
        cyassl_log(INFO_LOG , msg);
}


void CYASSL_ENTER(const char* msg)
{
    if (loggingEnabled) {
        char buffer[80];
        sprintf(buffer, "CyaSSL Entering %s", msg);
        cyassl_log(ENTER_LOG , buffer);
    }
}


void CYASSL_LEAVE(const char* msg, int ret)
{
    if (loggingEnabled) {
        char buffer[80];
        sprintf(buffer, "CyaSSL Leaving %s, return %d", msg, ret);
        cyassl_log(LEAVE_LOG , buffer);
    }
}


void CYASSL_ERROR(int error)
{
    if (loggingEnabled) {
        char buffer[80];
        sprintf(buffer, "CyaSSL error occured, error = %d", error);
        cyassl_log(ERROR_LOG , buffer);
    }
}

#endif  /* DEBUG_CYASSL */ 
