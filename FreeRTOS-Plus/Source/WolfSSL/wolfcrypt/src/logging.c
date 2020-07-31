/* logging.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)
/* avoid adding WANT_READ and WANT_WRITE to error queue */
#include <wolfssl/error-ssl.h>
#endif

#if defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)
static wolfSSL_Mutex debug_mutex; /* mutex for access to debug structure */

/* accessing any node from the queue should be wrapped in a lock of
 * debug_mutex */
static void* wc_error_heap;
struct wc_error_queue {
    void*  heap; /* the heap hint used with nodes creation */
    struct wc_error_queue* next;
    struct wc_error_queue* prev;
    char   error[WOLFSSL_MAX_ERROR_SZ];
    char   file[WOLFSSL_MAX_ERROR_SZ];
    int    value;
    int    line;
};
volatile struct wc_error_queue* wc_errors;
static struct wc_error_queue* wc_current_node;
static struct wc_error_queue* wc_last_node;
/* pointer to last node in queue to make insertion O(1) */
#endif

#ifdef WOLFSSL_FUNC_TIME
/* WARNING: This code is only to be used for debugging performance.
 *          The code is not thread-safe.
 *          Do not use WOLFSSL_FUNC_TIME in production code.
 */
static double wc_func_start[WC_FUNC_COUNT];
static double wc_func_time[WC_FUNC_COUNT] = { 0, };
static const char* wc_func_name[WC_FUNC_COUNT] = {
    "SendHelloRequest",
    "DoHelloRequest",
    "SendClientHello",
    "DoClientHello",
    "SendServerHello",
    "DoServerHello",
    "SendEncryptedExtensions",
    "DoEncryptedExtensions",
    "SendCertificateRequest",
    "DoCertificateRequest",
    "SendCertificate",
    "DoCertificate",
    "SendCertificateVerify",
    "DoCertificateVerify",
    "SendFinished",
    "DoFinished",
    "SendKeyUpdate",
    "DoKeyUpdate",
    "SendEarlyData",
    "DoEarlyData",
    "SendNewSessionTicket",
    "DoNewSessionTicket",
    "SendServerHelloDone",
    "DoServerHelloDone",
    "SendTicket",
    "DoTicket",
    "SendClientKeyExchange",
    "DoClientKeyExchange",
    "SendCertificateStatus",
    "DoCertificateStatus",
    "SendServerKeyExchange",
    "DoServerKeyExchange",
    "SendEarlyData",
    "DoEarlyData",
};

#include <sys/time.h>

/* WARNING: This function is not portable. */
static WC_INLINE double current_time(int reset)
{
    struct timeval tv;
    gettimeofday(&tv, 0);
    (void)reset;

    return (double)tv.tv_sec + (double)tv.tv_usec / 1000000;
}
#endif /* WOLFSSL_FUNC_TIME */

#ifdef DEBUG_WOLFSSL

/* Set these to default values initially. */
static wolfSSL_Logging_cb log_function = NULL;
static int loggingEnabled = 0;

#if defined(WOLFSSL_APACHE_MYNEWT)
#include "log/log.h"
static struct log mynewt_log;
#endif /* WOLFSSL_APACHE_MYNEWT */

#endif /* DEBUG_WOLFSSL */


/* allow this to be set to NULL, so logs can be redirected to default output */
int wolfSSL_SetLoggingCb(wolfSSL_Logging_cb f)
{
#ifdef DEBUG_WOLFSSL
    log_function = f;
    return 0;
#else
    (void)f;
    return NOT_COMPILED_IN;
#endif
}

/* allow this to be set to NULL, so logs can be redirected to default output */
wolfSSL_Logging_cb wolfSSL_GetLoggingCb(void)
{
#ifdef DEBUG_WOLFSSL
    return log_function;
#else
    return NULL;
#endif
}


int wolfSSL_Debugging_ON(void)
{
#ifdef DEBUG_WOLFSSL
    loggingEnabled = 1;
#if defined(WOLFSSL_APACHE_MYNEWT)
    log_register("wolfcrypt", &mynewt_log, &log_console_handler, NULL, LOG_SYSLEVEL);
#endif /* WOLFSSL_APACHE_MYNEWT */
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

#ifdef WOLFSSL_FUNC_TIME
/* WARNING: This code is only to be used for debugging performance.
 *          The code is not thread-safe.
 *          Do not use WOLFSSL_FUNC_TIME in production code.
 */
void WOLFSSL_START(int funcNum)
{
    double now = current_time(0) * 1000.0;
#ifdef WOLFSSL_FUNC_TIME_LOG
    fprintf(stderr, "%17.3f: START - %s\n", now, wc_func_name[funcNum]);
#endif
    wc_func_start[funcNum] = now;
}

void WOLFSSL_END(int funcNum)
{
    double now = current_time(0) * 1000.0;
    wc_func_time[funcNum] += now - wc_func_start[funcNum];
#ifdef WOLFSSL_FUNC_TIME_LOG
    fprintf(stderr, "%17.3f: END   - %s\n", now, wc_func_name[funcNum]);
#endif
}

void WOLFSSL_TIME(int count)
{
    int i;
    double avg, total = 0;

    for (i = 0; i < WC_FUNC_COUNT; i++) {
        if (wc_func_time[i] > 0) {
            avg = wc_func_time[i] / count;
            fprintf(stderr, "%8.3f ms: %s\n", avg, wc_func_name[i]);
            total += avg;
        }
    }
    fprintf(stderr, "%8.3f ms\n", total);
}
#endif

#ifdef DEBUG_WOLFSSL

#if defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)
    /* see wc_port.h for fio.h and nio.h includes */
#elif defined(WOLFSSL_SGX)
    /* Declare sprintf for ocall */
    int sprintf(char* buf, const char *fmt, ...);
#elif defined(WOLFSSL_DEOS)
#elif defined(MICRIUM)
    #if (BSP_SER_COMM_EN  == DEF_ENABLED)
        #include <bsp_ser.h>
    #endif
#elif defined(WOLFSSL_USER_LOG)
    /* user includes their own headers */
#elif defined(WOLFSSL_ESPIDF)
    #include "esp_types.h"
    #include "esp_log.h"
#elif defined(WOLFSSL_TELIT_M2MB)
    #include <stdio.h>
    #include "m2m_log.h"
#elif defined(WOLFSSL_ANDROID_DEBUG)
    #include <android/log.h>
#else
    #include <stdio.h>   /* for default printf stuff */
#endif

#if defined(THREADX) && !defined(THREADX_NO_DC_PRINTF)
    int dc_log_printf(char*, ...);
#endif

static void wolfssl_log(const int logLevel, const char *const logMessage)
{
    if (log_function)
        log_function(logLevel, logMessage);
    else {
#if defined(WOLFSSL_USER_LOG)
        WOLFSSL_USER_LOG(logMessage);
#elif defined(WOLFSSL_LOG_PRINTF)
        printf("%s\n", logMessage);

#elif defined(THREADX) && !defined(THREADX_NO_DC_PRINTF)
        dc_log_printf("%s\n", logMessage);
#elif defined(WOLFSSL_DEOS)
        printf("%s\r\n", logMessage);
#elif defined(MICRIUM)
        BSP_Ser_Printf("%s\r\n", logMessage);
#elif defined(WOLFSSL_MDK_ARM)
        fflush(stdout) ;
        printf("%s\n", logMessage);
        fflush(stdout) ;
#elif defined(WOLFSSL_UTASKER)
        fnDebugMsg((char*)logMessage);
        fnDebugMsg("\r\n");
#elif defined(MQX_USE_IO_OLD)
        fprintf(_mqxio_stderr, "%s\n", logMessage);

#elif defined(WOLFSSL_APACHE_MYNEWT)
        LOG_DEBUG(&mynewt_log, LOG_MODULE_DEFAULT, "%s\n", logMessage);
#elif defined(WOLFSSL_ESPIDF)
        ESP_LOGI("wolfssl", "%s", logMessage);
#elif defined(WOLFSSL_ZEPHYR)
        printk("%s\n", logMessage);
#elif defined(WOLFSSL_TELIT_M2MB)
        M2M_LOG_INFO("%s\n", logMessage);
#elif defined(WOLFSSL_ANDROID_DEBUG)
        __android_log_print(ANDROID_LOG_VERBOSE, "[wolfSSL]", "%s", logMessage);
#else
        fprintf(stderr, "%s\n", logMessage);
#endif
    }
}

#ifndef WOLFSSL_DEBUG_ERRORS_ONLY
void WOLFSSL_MSG(const char* msg)
{
    if (loggingEnabled)
        wolfssl_log(INFO_LOG , msg);
}

#ifndef LINE_LEN
#define LINE_LEN 16
#endif
void WOLFSSL_BUFFER(const byte* buffer, word32 length)
{
    int i, buflen = (int)length, bufidx;
    char line[(LINE_LEN * 4) + 3]; /* \t00..0F | chars...chars\0 */

    if (!loggingEnabled) {
        return;
    }

    if (!buffer) {
        wolfssl_log(INFO_LOG, "\tNULL");
        return;
    }

    while (buflen > 0) {
        bufidx = 0;
        XSNPRINTF(&line[bufidx], sizeof(line)-bufidx, "\t");
        bufidx++;

        for (i = 0; i < LINE_LEN; i++) {
            if (i < buflen) {
                XSNPRINTF(&line[bufidx], sizeof(line)-bufidx, "%02x ", buffer[i]);
            }
            else {
                XSNPRINTF(&line[bufidx], sizeof(line)-bufidx, "   ");
            }
            bufidx += 3;
        }

        XSNPRINTF(&line[bufidx], sizeof(line)-bufidx, "| ");
        bufidx++;

        for (i = 0; i < LINE_LEN; i++) {
            if (i < buflen) {
                XSNPRINTF(&line[bufidx], sizeof(line)-bufidx,
                     "%c", 31 < buffer[i] && buffer[i] < 127 ? buffer[i] : '.');
                bufidx++;
            }
        }

        wolfssl_log(INFO_LOG, line);
        buffer += LINE_LEN;
        buflen -= LINE_LEN;
    }
}


void WOLFSSL_ENTER(const char* msg)
{
    if (loggingEnabled) {
        char buffer[WOLFSSL_MAX_ERROR_SZ];
        XSNPRINTF(buffer, sizeof(buffer), "wolfSSL Entering %s", msg);
        wolfssl_log(ENTER_LOG , buffer);
    }
}


void WOLFSSL_LEAVE(const char* msg, int ret)
{
    if (loggingEnabled) {
        char buffer[WOLFSSL_MAX_ERROR_SZ];
        XSNPRINTF(buffer, sizeof(buffer), "wolfSSL Leaving %s, return %d",
                msg, ret);
        wolfssl_log(LEAVE_LOG , buffer);
    }
}

WOLFSSL_API int WOLFSSL_IS_DEBUG_ON(void)
{
    return loggingEnabled;
}
#endif /* !WOLFSSL_DEBUG_ERRORS_ONLY */
#endif /* DEBUG_WOLFSSL */

/*
 * When using OPENSSL_EXTRA or DEBUG_WOLFSSL_VERBOSE macro then WOLFSSL_ERROR is
 * mapped to new function WOLFSSL_ERROR_LINE which gets the line # and function
 * name where WOLFSSL_ERROR is called at.
 */
#if defined(DEBUG_WOLFSSL) || defined(OPENSSL_ALL) || \
    defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY) || \
    defined(OPENSSL_EXTRA)

#if (defined(OPENSSL_EXTRA) && !defined(_WIN32) && !defined(NO_ERROR_QUEUE)) \
    || defined(DEBUG_WOLFSSL_VERBOSE)
void WOLFSSL_ERROR_LINE(int error, const char* func, unsigned int line,
        const char* file, void* usrCtx)
#else
void WOLFSSL_ERROR(int error)
#endif
{
#ifdef WOLFSSL_ASYNC_CRYPT
    if (error != WC_PENDING_E)
#endif
    {
        char buffer[WOLFSSL_MAX_ERROR_SZ];

    #if (defined(OPENSSL_EXTRA) && !defined(_WIN32) && \
            !defined(NO_ERROR_QUEUE)) || defined(DEBUG_WOLFSSL_VERBOSE)
        (void)usrCtx; /* a user ctx for future flexibility */
        (void)func;

        if (wc_LockMutex(&debug_mutex) != 0) {
            WOLFSSL_MSG("Lock debug mutex failed");
            XSNPRINTF(buffer, sizeof(buffer),
                    "wolfSSL error occurred, error = %d", error);
        }
        else {
            #if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)
            /* If running in compatibility mode do not add want read and
               want right to error queue */
            if (error != WANT_READ && error != WANT_WRITE) {
            #endif
            if (error < 0)
                error = error - (2 * error); /* get absolute value */
            XSNPRINTF(buffer, sizeof(buffer),
                    "wolfSSL error occurred, error = %d line:%d file:%s",
                    error, line, file);
            if (wc_AddErrorNode(error, line, buffer, (char*)file) != 0) {
                WOLFSSL_MSG("Error creating logging node");
                /* with void function there is no return here, continue on
                 * to unlock mutex and log what buffer was created. */
            }
            #if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)
            }
            else {
                XSNPRINTF(buffer, sizeof(buffer),
                    "wolfSSL error occurred, error = %d", error);

            }
            #endif

            wc_UnLockMutex(&debug_mutex);
        }
    #else
        XSNPRINTF(buffer, sizeof(buffer),
                "wolfSSL error occurred, error = %d", error);
    #endif

    #ifdef DEBUG_WOLFSSL
        if (loggingEnabled)
            wolfssl_log(ERROR_LOG , buffer);
    #endif
    }
}

void WOLFSSL_ERROR_MSG(const char* msg)
{
#ifdef DEBUG_WOLFSSL
    if (loggingEnabled)
        wolfssl_log(ERROR_LOG , msg);
#else
    (void)msg;
#endif
}

#endif  /* DEBUG_WOLFSSL || WOLFSSL_NGINX || WOLFSSL_HAPROXY */

#if defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)
/* Internal function that is called by wolfCrypt_Init() */
int wc_LoggingInit(void)
{
    if (wc_InitMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Bad Init Mutex");
        return BAD_MUTEX_E;
    }
    wc_errors          = NULL;
    wc_current_node    = NULL;
    wc_last_node       = NULL;

    return 0;
}


/* internal function that is called by wolfCrypt_Cleanup */
int wc_LoggingCleanup(void)
{
    /* clear logging entries */
    wc_ClearErrorNodes();

    /* free mutex */
    if (wc_FreeMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Bad Mutex free");
        return BAD_MUTEX_E;
    }
    return 0;
}


/* peek at an error node
 *
 * idx : if -1 then the most recent node is looked at, otherwise search
 *         through queue for node at the given index
 * file  : pointer to internal file string
 * reason : pointer to internal error reason
 * line  : line number that error happened at
 *
 * Returns a negative value in error case, on success returns the nodes error
 * value which is positive (absolute value)
 */
int wc_PeekErrorNode(int idx, const char **file, const char **reason,
        int *line)
{
    struct wc_error_queue* err;

    if (wc_LockMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Lock debug mutex failed");
        return BAD_MUTEX_E;
    }

    if (idx < 0) {
        err = wc_last_node;
    }
    else {
        int i;

        err = (struct wc_error_queue*)wc_errors;
        for (i = 0; i < idx; i++) {
            if (err == NULL) {
                WOLFSSL_MSG("Error node not found. Bad index?");
                wc_UnLockMutex(&debug_mutex);
                return BAD_FUNC_ARG;
            }
            err = err->next;
        }
    }

    if (err == NULL) {
        WOLFSSL_MSG("No Errors in queue");
        wc_UnLockMutex(&debug_mutex);
        return BAD_STATE_E;
    }

    if (file != NULL) {
        *file = err->file;
    }

    if (reason != NULL) {
        *reason = err->error;
    }

    if (line != NULL) {
        *line = err->line;
    }

    wc_UnLockMutex(&debug_mutex);

    return err->value;
}


/* Pulls the current node from error queue and increments current state.
 * Note: this does not delete nodes because input arguments are pointing to
 *       node buffers.
 *
 * file   pointer to file that error was in. Can be NULL to return no file.
 * reason error string giving reason for error. Can be NULL to return no reason.
 * line   return line number of where error happened.
 *
 * returns the error value on success and BAD_MUTEX_E or BAD_STATE_E on failure
 */
int wc_PullErrorNode(const char **file, const char **reason, int *line)
{
    struct wc_error_queue* err;
    int value;

    if (wc_LockMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Lock debug mutex failed");
        return BAD_MUTEX_E;
    }

    err = wc_current_node;
    if (err == NULL) {
        WOLFSSL_MSG("No Errors in queue");
        wc_UnLockMutex(&debug_mutex);
        return BAD_STATE_E;
    }

    if (file != NULL) {
        *file = err->file;
    }

    if (reason != NULL) {
        *reason = err->error;
    }

    if (line != NULL) {
        *line = err->line;
    }

    value = err->value;
    wc_current_node = err->next;
    wc_UnLockMutex(&debug_mutex);

    return value;
}


/* create new error node and add it to the queue
 * buffers are assumed to be of size WOLFSSL_MAX_ERROR_SZ for this internal
 * function. debug_mutex should be locked before a call to this function. */
int wc_AddErrorNode(int error, int line, char* buf, char* file)
{
#if defined(NO_ERROR_QUEUE)
    (void)error;
    (void)line;
    (void)buf;
    (void)file;
    WOLFSSL_MSG("Error queue turned off, can not add nodes");
#else
    struct wc_error_queue* err;
    err = (struct wc_error_queue*)XMALLOC(
            sizeof(struct wc_error_queue), wc_error_heap, DYNAMIC_TYPE_LOG);
    if (err == NULL) {
        WOLFSSL_MSG("Unable to create error node for log");
        return MEMORY_E;
    }
    else {
        int sz;

        XMEMSET(err, 0, sizeof(struct wc_error_queue));
        err->heap = wc_error_heap;
        sz = (int)XSTRLEN(buf);
        if (sz > WOLFSSL_MAX_ERROR_SZ - 1) {
            sz = WOLFSSL_MAX_ERROR_SZ - 1;
        }
        if (sz > 0) {
            XMEMCPY(err->error, buf, sz);
        }

        sz = (int)XSTRLEN(file);
        if (sz > WOLFSSL_MAX_ERROR_SZ - 1) {
            sz = WOLFSSL_MAX_ERROR_SZ - 1;
        }
        if (sz > 0) {
            XMEMCPY(err->file, file, sz);
        }

        err->value = error;
        err->line  = line;

        /* make sure is terminated */
        err->error[WOLFSSL_MAX_ERROR_SZ - 1] = '\0';
        err->file[WOLFSSL_MAX_ERROR_SZ - 1]  = '\0';


        /* since is queue place new node at last of the list */
        if (wc_last_node == NULL) {
            /* case of first node added to queue */
            if (wc_errors != NULL) {
                /* check for unexpected case before over writing wc_errors */
                WOLFSSL_MSG("ERROR in adding new node to logging queue!!\n");
                /* In the event both wc_last_node and wc_errors are NULL, err
                 * goes unassigned to external wc_errors, wc_last_node. Free
                 * err in this instance since wc_ClearErrorNodes will not
                 */
                XFREE(err, wc_error_heap, DYNAMIC_TYPE_LOG);
            }
            else {
                wc_errors    = err;
                wc_last_node = err;
                wc_current_node = err;
            }
        }
        else {
            wc_last_node->next = err;
            err->prev = wc_last_node;
            wc_last_node = err;

            /* check the case where have read to the end of the queue and the
             * current node to read needs updated */
            if (wc_current_node == NULL) {
                wc_current_node = err;
            }
        }
    }
#endif
    return 0;
}

/* Removes the error node at the specified index.
 * idx : if -1 then the most recent node is looked at, otherwise search
 *         through queue for node at the given index
 */
void wc_RemoveErrorNode(int idx)
{
    struct wc_error_queue* current;

    if (wc_LockMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Lock debug mutex failed");
        return;
    }

    if (idx == -1)
        current = wc_last_node;
    else {
        current = (struct wc_error_queue*)wc_errors;
        for (; current != NULL && idx > 0; idx--)
             current = current->next;
    }
    if (current != NULL) {
        if (current->prev != NULL)
            current->prev->next = current->next;
        if (current->next != NULL)
            current->next->prev = current->prev;
        if (wc_last_node == current)
            wc_last_node = current->prev;
        if (wc_errors == current)
            wc_errors = current->next;
        if (wc_current_node == current)
            wc_current_node = current->next;
        XFREE(current, current->heap, DYNAMIC_TYPE_LOG);
    }

    wc_UnLockMutex(&debug_mutex);
}


/* Clears out the list of error nodes.
 */
void wc_ClearErrorNodes(void)
{
#if defined(DEBUG_WOLFSSL) || defined(WOLFSSL_NGINX) || \
    defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)

    if (wc_LockMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Lock debug mutex failed");
        return;
    }

    /* free all nodes from error queue */
    {
        struct wc_error_queue* current;
        struct wc_error_queue* next;

        current = (struct wc_error_queue*)wc_errors;
        while (current != NULL) {
            next = current->next;
            XFREE(current, current->heap, DYNAMIC_TYPE_LOG);
            current = next;
        }
    }

    wc_errors       = NULL;
    wc_last_node    = NULL;
    wc_current_node = NULL;
    wc_UnLockMutex(&debug_mutex);
#endif /* DEBUG_WOLFSSL || WOLFSSL_NGINX */
}

int wc_SetLoggingHeap(void* h)
{
    if (wc_LockMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Lock debug mutex failed");
        return BAD_MUTEX_E;
    }
    wc_error_heap = h;
    wc_UnLockMutex(&debug_mutex);
    return 0;
}


/* frees all nodes in the queue
 *
 * id  this is the thread id
 */
int wc_ERR_remove_state(void)
{
    struct wc_error_queue* current;
    struct wc_error_queue* next;

    if (wc_LockMutex(&debug_mutex) != 0) {
        WOLFSSL_MSG("Lock debug mutex failed");
        return BAD_MUTEX_E;
    }

    /* free all nodes from error queue */
    current = (struct wc_error_queue*)wc_errors;
    while (current != NULL) {
        next = current->next;
        XFREE(current, current->heap, DYNAMIC_TYPE_LOG);
        current = next;
    }

    wc_errors          = NULL;
    wc_last_node       = NULL;

    wc_UnLockMutex(&debug_mutex);

    return 0;
}

#if !defined(NO_FILESYSTEM) && !defined(NO_STDIO_FILESYSTEM)
/* empties out the error queue into the file */
static int wc_ERR_dump_to_file (const char *str, size_t len, void *u)
{
    XFILE fp = (XFILE ) u;
    fprintf(fp, "%-*.*s\n", (int)len, (int)len, str);
    return 0;
}

/* This callback allows the application to provide a custom error printing
 * function. */
void wc_ERR_print_errors_cb(int (*cb)(const char *str, size_t len, void *u),
                            void *u)
{
    WOLFSSL_ENTER("wc_ERR_print_errors_cb");

    if (cb == NULL) {
        /* Invalid param */
        return;
    }

    if (wc_LockMutex(&debug_mutex) != 0)
    {
        WOLFSSL_MSG("Lock debug mutex failed");
    }
    else
    {
        /* free all nodes from error queue and print them to file */
        struct wc_error_queue *current;
        struct wc_error_queue *next;

        current = (struct wc_error_queue *)wc_errors;
        while (current != NULL)
        {
            next = current->next;
            cb(current->error, strlen(current->error), u);
            XFREE(current, current->heap, DYNAMIC_TYPE_LOG);
            current = next;
        }

        /* set global pointers to match having been freed */
        wc_errors = NULL;
        wc_last_node = NULL;

        wc_UnLockMutex(&debug_mutex);
    }
}

void wc_ERR_print_errors_fp(XFILE fp)
{
    WOLFSSL_ENTER("wc_ERR_print_errors_fp");

    /* Send all errors to the wc_ERR_dump_to_file function */
    wc_ERR_print_errors_cb(wc_ERR_dump_to_file, fp);
}

#endif /* !defined(NO_FILESYSTEM) && !defined(NO_STDIO_FILESYSTEM) */

#endif /* defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE) */
