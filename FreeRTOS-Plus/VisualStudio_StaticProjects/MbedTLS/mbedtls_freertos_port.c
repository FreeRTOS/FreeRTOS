/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#include <stdlib.h>
#include <string.h>

#include "FreeRTOSConfig.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"

/* mbed TLS includes. */
#if defined( MBEDTLS_CONFIG_FILE )
#include MBEDTLS_CONFIG_FILE
#else
#include "mbedtls/mbedtls_config.h"
#endif
#include "mbedtls/entropy.h"

#include "entropy_poll.h"

#include "mbedtls_freertos_port.h"

/*-----------------------------------------------------------*/

/**
 * @brief Allocates memory for an array of members.
 *
 * @param[in] nmemb Number of members that need to be allocated.
 * @param[in] size Size of each member.
 *
 * @return Pointer to the beginning of newly allocated memory.
 */
void * mbedtls_platform_calloc( size_t nmemb,
                                size_t size )
{
    size_t totalSize = nmemb * size;
    void * pBuffer = NULL;

    /* Check that neither nmemb nor size were 0. */
    if( totalSize > 0 )
    {
        /* Overflow check. */
        if( ( totalSize / size ) == nmemb )
        {
            pBuffer = pvPortMalloc( totalSize );

            if( pBuffer != NULL )
            {
                ( void ) memset( pBuffer, 0U, totalSize );
            }
        }
    }

    return pBuffer;
}

/*-----------------------------------------------------------*/

/**
 * @brief Frees the space previously allocated by calloc.
 *
 * @param[in] ptr Pointer to the memory to be freed.
 */
void mbedtls_platform_free( void * ptr )
{
    if( ptr != NULL )
    {
        vPortFree( ptr );
    }
}

/*-----------------------------------------------------------*/

#if defined( MBEDTLS_THREADING_C )

/**
 * @brief Creates a mutex.
 *
 * @param[in, out] pMutex mbedtls mutex handle.
 */
static void mbedtls_platform_mutex_init( mbedtls_threading_mutex_t * pMutex )
{
    configASSERT( pMutex != NULL );

    #if( configSUPPORT_STATIC_ALLOCATION == 1 )
        /* Create a statically-allocated FreeRTOS mutex. This should never fail as
        * storage is provided. */

        pMutex->mutexHandle = xSemaphoreCreateMutexStatic( &( pMutex->mutexStorage ) );
    #elif( configSUPPORT_DYNAMIC_ALLOCATION == 1 )
        pMutex->mutexHandle = xSemaphoreCreateMutex();
    #endif

    configASSERT( pMutex->mutexHandle != NULL );
}

/*-----------------------------------------------------------*/

/**
 * @brief Frees a mutex.
 *
 * @param[in] pMutex mbedtls mutex handle.
 *
 * @note This function is an empty stub as nothing needs to be done to free
 * a statically allocated FreeRTOS mutex.
 */
static void mbedtls_platform_mutex_free( mbedtls_threading_mutex_t * pMutex )
{
    vSemaphoreDelete( pMutex->mutexHandle );
    pMutex->mutexHandle = NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Function to lock a mutex.
 *
 * @param[in] pMutex mbedtls mutex handle.
 *
 * @return 0 (success) is always returned as any other failure is asserted.
 */
static int mbedtls_platform_mutex_lock( mbedtls_threading_mutex_t * pMutex )
{
    BaseType_t mutexStatus = 0;

    configASSERT( pMutex != NULL );
    configASSERT( pMutex->mutexHandle != NULL );

    /* mutexStatus is not used if asserts are disabled. */
    ( void ) mutexStatus;

    /* This function should never fail if the mutex is initialized. */
    mutexStatus = xSemaphoreTake( pMutex->mutexHandle, portMAX_DELAY );

    configASSERT( mutexStatus == pdTRUE );

    return 0;
}

/*-----------------------------------------------------------*/

/**
 * @brief Function to unlock a mutex.
 *
 * @param[in] pMutex mbedtls mutex handle.
 *
 * @return 0 is always returned as any other failure is asserted.
 */
static int mbedtls_platform_mutex_unlock( mbedtls_threading_mutex_t * pMutex )
{
    BaseType_t mutexStatus = 0;

    configASSERT( pMutex != NULL );
    configASSERT( pMutex->mutexHandle != NULL );
    /* mutexStatus is not used if asserts are disabled. */
    ( void ) mutexStatus;

    /* This function should never fail if the mutex is initialized. */
    mutexStatus = xSemaphoreGive( pMutex->mutexHandle );
    configASSERT( mutexStatus == pdTRUE );

    return 0;
}

/*-----------------------------------------------------------*/

#if defined( MBEDTLS_THREADING_ALT )
int mbedtls_platform_threading_init( void )
{
    mbedtls_threading_set_alt( mbedtls_platform_mutex_init,
                               mbedtls_platform_mutex_free,
                               mbedtls_platform_mutex_lock,
                               mbedtls_platform_mutex_unlock );
    return 0;
}

#else /* !MBEDTLS_THREADING_ALT */

void (* mbedtls_mutex_init)( mbedtls_threading_mutex_t * mutex ) = mbedtls_platform_mutex_init;
void (* mbedtls_mutex_free)( mbedtls_threading_mutex_t * mutex ) = mbedtls_platform_mutex_free;
int (* mbedtls_mutex_lock)( mbedtls_threading_mutex_t * mutex ) = mbedtls_platform_mutex_lock;
int (* mbedtls_mutex_unlock)( mbedtls_threading_mutex_t * mutex ) = mbedtls_platform_mutex_unlock;

#endif /* !MBEDTLS_THREADING_ALT */

#endif /* MBEDTLS_THREADING_C */
/*-----------------------------------------------------------*/

#if defined( MBEDTLS_ENTROPY_HARDWARE_ALT )
    /* Determine which API is available */
    #if defined(_WIN32)
        #define RNG_SOURCE_WINDOWS_CRYPT
    #elif defined(__linux__)
        #include <unistd.h>
        #include <sys/syscall.h>
        #if defined(SYS_getrandom)
            #define RNG_SOURCE_GETRANDOM
        #endif /* SYS_getrandom */
    #elif defined( ARM_RDI_MONITOR ) || defined( SEMIHOSTING )
        #define RNG_SOURCE_SEMIHOST
    #else
        #define RNG_SOURCE_DEV_RANDOM
    #endif

    #if defined(RNG_SOURCE_WINDOWS_CRYPT)
        #include <windows.h>
        #include <wincrypt.h>
        int mbedtls_hardware_poll( void * data,
                                unsigned char * output,
                                size_t len,
                                size_t * olen )
        {
            int lStatus = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
            HCRYPTPROV hProv = 0;

            /* Unferenced parameter. */
            ( void ) data;

            /*
            * This is port-specific for the Windows simulator, so just use Crypto API.
            */

            if( TRUE == CryptAcquireContextA(
                    &hProv, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT ) )
            {
                if( TRUE == CryptGenRandom( hProv, len, output ) )
                {
                    lStatus = 0;
                    *olen = len;
                }

                CryptReleaseContext( hProv, 0 );
            }

            return lStatus;
        }
    #elif defined( RNG_SOURCE_GETRANDOM )
        int mbedtls_hardware_poll( void * data,
                                   unsigned char * output,
                                   size_t len,
                                   size_t * olen )
        {
            ( void ) data;
            int rslt = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;

            configASSERT( olen != NULL );

            rslt = getrandom( output, len, 0 );

            if( rslt >= 0 )
            {
                *olen = (size_t) rslt;
                rslt = 0;
            }
            else
            {
                rslt = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
            }
            return rslt;
        }
    #elif defined( RNG_SOURCE_SEMIHOST )
        int mbedtls_hardware_poll( void * data,
                                   unsigned char * output,
                                   size_t len,
                                   size_t * olen )
        {
            int rslt = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
            int file;

            (void) data;

            configASSERT( olen != NULL );
            configASSERT( output != NULL );

            file = _open( "/dev/urandom", O_RDONLY );

            if( file >= 0 )
            {
                rslt = _read( file, ( char * ) output, len );
            }

            if( rslt >= 0 )
            {
                *olen = len;
            }

            if( rslt >= 0 )
            {
                *olen = len;
                rslt = 0;
            }
            else
            {
                rslt = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
            }

            ( void ) _close( file );
            return rslt;
        }
    #else
        #include <stdio.h>
        int mbedtls_hardware_poll( void * data,
                                   unsigned char * output,
                                   size_t len,
                                   size_t * olen )
        {
            int rslt = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
            FILE * file;
            size_t read_length = 0U;

            configASSERT( olen != NULL );
            configASSERT( output != NULL );

            file = fopen("/dev/urandom", "rb");
            if( file != NULL )
            {
                rslt = fread( output, 1, len, file );
                fclose( file );
            }

            if( rslt >= 0 )
            {
                *olen = len;
                rslt = 0;
            }
            else
            {
                rslt = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
            }
            return rslt;
        }
    #endif
#endif
/*-----------------------------------------------------------*/
