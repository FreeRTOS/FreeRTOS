/*
 * FreeRTOS PKCS #11 PAL for Windows Simulator V1.0.4
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


/**
 * @file iot_pkcs11_pal.c
 * @brief Windows Simulator file save and read implementation
 * for PKCS#11 based on mbedTLS with for software keys. This
 * file deviates from the FreeRTOS style standard for some function names and
 * data types in order to maintain compliance with the PKCS#11 standard.
 */

/*-----------------------------------------------------------*/

#include "FreeRTOS.h"
#include "iot_pkcs11.h"
#include "iot_pkcs11_config.h"


/* C runtime includes. */
#include <stdio.h>
#include <string.h>

/**
 * @ingroup pkcs11_macros
 * @brief Macros for managing PKCS #11 objects in flash.
 *
 */
#define pkcs11palFILE_NAME_CLIENT_CERTIFICATE    "FreeRTOS_P11_Certificate.dat"       /**< The file name of the Certificate object. */
#define pkcs11palFILE_NAME_KEY                   "FreeRTOS_P11_Key.dat"               /**< The file name of the Key object. */
#define pkcs11palFILE_CODE_SIGN_PUBLIC_KEY       "FreeRTOS_P11_CodeSignKey.dat"       /**< The file name of the Code Sign Key object. */

/**
 * @ingroup pkcs11_macros
 * @brief PKCS #11 logging macro.
 *
 */
#define PKCS11_PAL_PRINT( X )    configPRINTF( X )

/**
 * @ingroup pkcs11_enums
 * @brief Enums for managing PKCS #11 object types.
 *
 */
enum eObjectHandles
{
    eInvalidHandle = 0,            /**< According to PKCS #11 spec, 0 is never a valid object handle. */
    eAwsDevicePrivateKey = 1,      /**< Private Key. */
    eAwsDevicePublicKey,           /**< Public Key. */
    eAwsDeviceCertificate,         /**< Certificate. */
    eAwsCodeSigningKey             /**< Code Signing Key. */
};

/*-----------------------------------------------------------*/

/**
 * @brief Checks to see if a file exists
 *
 * @param[in] pcFileName         The name of the file to check for existance.
 * 
 * @returns pdTRUE if the file exists, pdFALSE if not.
 */
BaseType_t prvFileExists( const char * pcFileName )
{
    DWORD xReturn;

    xReturn = GetFileAttributesA( pcFileName );

    if( INVALID_FILE_ATTRIBUTES == xReturn )
    {
        return pdFALSE;
    }
    else
    {
        return pdTRUE;
    }
}

/**
 * @brief Checks to see if a file exists
 *
 * @param[in] pcLabel            The PKCS #11 label to convert to a file name
 * @param[out] pcFileName        The name of the file to check for existance.
 * @param[out] pHandle           The type of the PKCS #11 object.
 * 
 */
void prvLabelToFilenameHandle( uint8_t * pcLabel,
                               char ** pcFileName,
                               CK_OBJECT_HANDLE_PTR pHandle )
{
    if( pcLabel != NULL )
    {
        /* Translate from the PKCS#11 label to local storage file name. */
        if( 0 == memcmp( pcLabel,
                         &pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                         sizeof( pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_CLIENT_CERTIFICATE;
            *pHandle = eAwsDeviceCertificate;
        }
        else if( 0 == memcmp( pcLabel,
                              &pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                              sizeof( pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_KEY;
            *pHandle = eAwsDevicePrivateKey;
        }
        else if( 0 == memcmp( pcLabel,
                              &pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
                              sizeof( pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_KEY;
            *pHandle = eAwsDevicePublicKey;
        }
        else if( 0 == memcmp( pcLabel,
                              &pkcs11configLABEL_CODE_VERIFICATION_KEY,
                              sizeof( pkcs11configLABEL_CODE_VERIFICATION_KEY ) ) )
        {
            *pcFileName = pkcs11palFILE_CODE_SIGN_PUBLIC_KEY;
            *pHandle = eAwsCodeSigningKey;
        }
        else
        {
            *pcFileName = NULL;
            *pHandle = eInvalidHandle;
        }
    }
}

/*-----------------------------------------------------------*/

CK_RV PKCS11_PAL_Initialize( void )
{
    return CKR_OK;
}

CK_OBJECT_HANDLE PKCS11_PAL_SaveObject( CK_ATTRIBUTE_PTR pxLabel,
                                        CK_BYTE_PTR pucData,
                                        CK_ULONG ulDataSize )
{
    uint32_t ulStatus = 0;
    HANDLE hFile = INVALID_HANDLE_VALUE;
    DWORD lpNumberOfBytesWritten;
    char * pcFileName = NULL;
    CK_OBJECT_HANDLE xHandle = eInvalidHandle;

    /* Converts a label to its respective filename and handle. */
    prvLabelToFilenameHandle( pxLabel->pValue,
                              &pcFileName,
                              &xHandle );

    /* If your project requires additional PKCS#11 objects, add them here. */

    if( pcFileName != NULL )
    {
        /* Create the file. */
        hFile = CreateFileA( pcFileName,
                             GENERIC_WRITE,
                             0,
                             NULL,
                             CREATE_ALWAYS,
                             FILE_ATTRIBUTE_NORMAL,
                             NULL );

        if( INVALID_HANDLE_VALUE == hFile )
        {
            ulStatus = GetLastError();
            PKCS11_PAL_PRINT( ( "ERROR: Unable to create file %d \r\n", ulStatus ) );
            xHandle = eInvalidHandle;
        }

        /* Write the object data. */
        if( ERROR_SUCCESS == ulStatus )
        {
            if( FALSE == WriteFile( hFile, pucData, ulDataSize, &lpNumberOfBytesWritten, NULL ) )
            {
                ulStatus = GetLastError();
                xHandle = eInvalidHandle;
            }
        }

        /* Clean up. */
        if( INVALID_HANDLE_VALUE != hFile )
        {
            CloseHandle( hFile );
        }
    }

    return xHandle;
}

/*-----------------------------------------------------------*/


CK_OBJECT_HANDLE PKCS11_PAL_FindObject( CK_BYTE_PTR pxLabel,
                                        CK_ULONG usLength )
{
    /* Avoid compiler warnings about unused variables. */
    ( void ) usLength;

    CK_OBJECT_HANDLE xHandle = eInvalidHandle;
    char * pcFileName = NULL;

    /* Converts a label to its respective filename and handle. */
    prvLabelToFilenameHandle( pxLabel,
                              &pcFileName,
                              &xHandle );

    /* Check if object exists/has been created before returning. */
    if( pdTRUE != prvFileExists( pcFileName ) )
    {
        xHandle = eInvalidHandle;
    }

    return xHandle;
}
/*-----------------------------------------------------------*/

CK_RV PKCS11_PAL_GetObjectValue( CK_OBJECT_HANDLE xHandle,
                                      CK_BYTE_PTR * ppucData,
                                      CK_ULONG_PTR pulDataSize,
                                      CK_BBOOL * pIsPrivate )
{
    CK_RV ulReturn = CKR_OK;
    uint32_t ulDriverReturn = 0;
    HANDLE hFile = INVALID_HANDLE_VALUE;
    uint32_t ulSize = 0;
    char * pcFileName = NULL;


    if( xHandle == eAwsDeviceCertificate )
    {
        pcFileName = pkcs11palFILE_NAME_CLIENT_CERTIFICATE;
        *pIsPrivate = CK_FALSE;
    }
    else if( xHandle == eAwsDevicePrivateKey )
    {
        pcFileName = pkcs11palFILE_NAME_KEY;
        *pIsPrivate = CK_TRUE;
    }
    else if( xHandle == eAwsDevicePublicKey )
    {
        /* Public and private key are stored together in same file. */
        pcFileName = pkcs11palFILE_NAME_KEY;
        *pIsPrivate = CK_FALSE;
    }
    else if( xHandle == eAwsCodeSigningKey )
    {
        pcFileName = pkcs11palFILE_CODE_SIGN_PUBLIC_KEY;
        *pIsPrivate = CK_FALSE;
    }
    else
    {
        ulReturn = CKR_KEY_HANDLE_INVALID;
    }

    if( pcFileName != NULL )
    {
        /* Open the file. */
        hFile = CreateFileA( pcFileName,
                             GENERIC_READ,
                             FILE_SHARE_READ,
                             NULL,
                             OPEN_EXISTING,
                             FILE_ATTRIBUTE_NORMAL,
                             NULL );

        if( INVALID_HANDLE_VALUE == hFile )
        {
            ulDriverReturn = GetLastError();
            PKCS11_PAL_PRINT( ( "ERROR: Unable to open file %d \r\n", ulDriverReturn ) );
            ulReturn = CKR_FUNCTION_FAILED;
        }

        if( 0 == ulReturn )
        {
            /* Get the file size. */
            *pulDataSize = GetFileSize( hFile, ( LPDWORD ) ( &ulSize ) );

            /* Create a buffer. */
            *ppucData = pvPortMalloc( *pulDataSize );

            if( NULL == *ppucData )
            {
                ulReturn = CKR_HOST_MEMORY;
            }
        }

        /* Read the file. */
        if( 0 == ulReturn )
        {
            if( FALSE == ReadFile( hFile,
                                   *ppucData,
                                   *pulDataSize,
                                   ( LPDWORD ) ( &ulSize ),
                                   NULL ) )
            {
                PKCS11_PAL_PRINT( ( "ERROR: Unable to read file \r\n" ) );
                ulReturn = CKR_FUNCTION_FAILED;
            }
        }

        /* Confirm the amount of data read. */
        if( 0 == ulReturn )
        {
            if( ulSize != *pulDataSize )
            {
                ulReturn = CKR_FUNCTION_FAILED;
            }
        }

        /* Clean up. */
        if( INVALID_HANDLE_VALUE != hFile )
        {
            CloseHandle( hFile );
        }
    }

    return ulReturn;
}

/*-----------------------------------------------------------*/

void PKCS11_PAL_GetObjectValueCleanup( CK_BYTE_PTR pucData,
                                       CK_ULONG ulDataSize )
{
    /* Unused parameters. */
    ( void ) ulDataSize;

    if( NULL != pucData )
    {
        vPortFree( pucData );
    }
}

/*-----------------------------------------------------------*/
