/*
 * FreeRTOS OTA PAL for Windows Simulator V1.0.3
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

/* OTA PAL implementation for Windows platform. */

/* The config header is always included first. */
#include "iot_config.h"

#include <stdio.h>
#include <stdlib.h>
#include "FreeRTOS.h"
#include "iot_crypto.h"
#include "aws_iot_ota_pal.h"
#include "aws_iot_ota_agent_internal.h"
#include "aws_ota_codesigner_certificate.h"

/* Specify the OTA signature algorithm we support on this platform. */
const char cOTA_JSON_FileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

static OTA_Err_t prvPAL_CheckFileSignature( OTA_FileContext_t * const C );
static uint8_t * prvPAL_ReadAndAssumeCertificate( const uint8_t * const pucCertName,
                                                  uint32_t * const ulSignerCertSize );

/*-----------------------------------------------------------*/

static inline BaseType_t prvContextValidate( OTA_FileContext_t * C )
{
    return( ( C != NULL ) &&
            ( C->pxFile != NULL ) ); /*lint !e9034 Comparison is correct for file pointer type. */
}

/* Used to set the high bit of Windows error codes for a negative return value. */
#define OTA_PAL_INT16_NEGATIVE_MASK    ( 1 << 15 )

/* Size of buffer used in file operations on this platform (Windows). */
#define OTA_PAL_WIN_BUF_SIZE           ( ( size_t ) 4096UL )

/* Attempt to create a new receive file for the file chunks as they come in. */

OTA_Err_t prvPAL_CreateFileForRx( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CreateFileForRx" );

    OTA_Err_t eResult = kOTA_Err_Uninitialized; /* For MISRA mandatory. */

    if( C != NULL )
    {
        if( C->pucFilePath != NULL )
        {
            C->pxFile = fopen( ( const char * ) C->pucFilePath, "w+b" ); /*lint !e586
                                                                          * C standard library call is being used for portability. */

            if( C->pxFile != NULL )
            {
                eResult = kOTA_Err_None;
                OTA_LOG_L1( "[%s] Receive file created.\r\n", OTA_METHOD_NAME );
            }
            else
            {
                eResult = ( kOTA_Err_RxFileCreateFailed | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                           * Errno is being used in accordance with host API documentation.
                                                                                           * Bitmasking is being used to preserve host API error with library status code. */
                OTA_LOG_L1( "[%s] ERROR - Failed to start operation: already active!\r\n", OTA_METHOD_NAME );
            }
        }
        else
        {
            eResult = kOTA_Err_RxFileCreateFailed;
            OTA_LOG_L1( "[%s] ERROR - Invalid context provided.\r\n", OTA_METHOD_NAME );
        }
    }
    else
    {
        eResult = kOTA_Err_RxFileCreateFailed;
        OTA_LOG_L1( "[%s] ERROR - Invalid context provided.\r\n", OTA_METHOD_NAME );
    }

    return eResult; /*lint !e480 !e481 Exiting function without calling fclose.
                     * Context file handle state is managed by this API. */
}


/* Abort receiving the specified OTA update by closing the file. */

OTA_Err_t prvPAL_Abort( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_Abort" );

    /* Set default return status to uninitialized. */
    OTA_Err_t eResult = kOTA_Err_Uninitialized;
    int32_t lFileCloseResult;

    if( NULL != C )
    {
        /* Close the OTA update file if it's open. */
        if( NULL != C->pxFile )
        {
            lFileCloseResult = fclose( C->pxFile ); /*lint !e482 !e586
                                                     * Context file handle state is managed by this API. */
            C->pxFile = NULL;

            if( 0 == lFileCloseResult )
            {
                OTA_LOG_L1( "[%s] OK\r\n", OTA_METHOD_NAME );
                eResult = kOTA_Err_None;
            }
            else /* Failed to close file. */
            {
                OTA_LOG_L1( "[%s] ERROR - Closing file failed.\r\n", OTA_METHOD_NAME );
                eResult = ( kOTA_Err_FileAbort | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                  * Errno is being used in accordance with host API documentation.
                                                                                  * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            /* Nothing to do. No open file associated with this context. */
            eResult = kOTA_Err_None;
        }
    }
    else /* Context was not valid. */
    {
        OTA_LOG_L1( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME );
        eResult = kOTA_Err_FileAbort;
    }

    return eResult;
}

/* Write a block of data to the specified file. */
int16_t prvPAL_WriteBlock( OTA_FileContext_t * const C,
                           uint32_t ulOffset,
                           uint8_t * const pacData,
                           uint32_t ulBlockSize )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_WriteBlock" );

    int32_t lResult = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        lResult = fseek( C->pxFile, ulOffset, SEEK_SET ); /*lint !e586 !e713 !e9034
                                                           * C standard library call is being used for portability. */

        if( 0 == lResult )
        {
            lResult = fwrite( pacData, 1, ulBlockSize, C->pxFile ); /*lint !e586 !e713 !e9034
                                                                     * C standard library call is being used for portability. */

            if( lResult < 0 )
            {
                OTA_LOG_L1( "[%s] ERROR - fwrite failed\r\n", OTA_METHOD_NAME );
                /* Mask to return a negative value. */
                lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                                * Errno is being used in accordance with host API documentation.
                                                                * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - fseek failed\r\n", OTA_METHOD_NAME );
            /* Mask to return a negative value. */
            lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                            * Errno is being used in accordance with host API documentation.
                                                            * Bitmasking is being used to preserve host API error with library status code. */
        }
    }
    else /* Invalid context or file pointer provided. */
    {
        OTA_LOG_L1( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME );
        lResult = -1; /*TODO: Need a negative error code from the PAL here. */
    }

    return ( int16_t ) lResult;
}

/* Close the specified file. This shall authenticate the file if it is marked as secure. */

OTA_Err_t prvPAL_CloseFile( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CloseFile" );

    OTA_Err_t eResult = kOTA_Err_None;
    int32_t lWindowsError = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        #if ( configOTA_ENABLE_CODE_SIGNATURE_VERIFICATION )
            /* Verify the file signature, close the file and return the signature verification result. */
            eResult = prvPAL_CheckFileSignature( C );
        #else
            /* Code signature verification is disabled so return no error. */

            OTA_LOG_L1( "[%s] Warning: Code signature verification is disabled in OTA config , see configOTA_ENABLE_CODE_SIGNATURE_VERIFICATION .\r\n", OTA_METHOD_NAME );

            eResult = kOTA_Err_None;
        #endif

        /* Close the file. */
        lWindowsError = fclose( C->pxFile ); /*lint !e482 !e586
                                              * C standard library call is being used for portability. */
        C->pxFile = NULL;

        if( lWindowsError != 0 )
        {
            OTA_LOG_L1( "[%s] ERROR - Failed to close OTA update file.\r\n", OTA_METHOD_NAME );
            eResult = ( kOTA_Err_FileClose | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                              * Errno is being used in accordance with host API documentation.
                                                                              * Bitmasking is being used to preserve host API error with library status code. */
        }

        if( eResult == kOTA_Err_None )
        {
            OTA_LOG_L1( "[%s] %s signature verification passed.\r\n", OTA_METHOD_NAME, cOTA_JSON_FileSignatureKey );
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - Failed to pass %s signature verification: %d.\r\n", OTA_METHOD_NAME,
                        cOTA_JSON_FileSignatureKey, eResult );

            /* If we fail to verify the file signature that means the image is not valid. We need to set the image state to aborted. */
            prvPAL_SetPlatformImageState( eOTA_ImageState_Aborted );
        }
    }
    else /* Invalid OTA Context. */
    {
        /* FIXME: Invalid error code for a null file context and file handle. */
        OTA_LOG_L1( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME );
        eResult = kOTA_Err_FileClose;
    }

    return eResult;
}


/* Verify the signature of the specified file. */

static OTA_Err_t prvPAL_CheckFileSignature( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CheckFileSignature" );

    OTA_Err_t eResult = kOTA_Err_None;
    uint32_t ulBytesRead;
    uint32_t ulSignerCertSize;
    uint8_t * pucBuf, * pucSignerCert;
    void * pvSigVerifyContext;

    if( prvContextValidate( C ) == pdTRUE )
    {
        /* Verify an ECDSA-SHA256 signature. */
        if( pdFALSE == CRYPTO_SignatureVerificationStart( &pvSigVerifyContext, cryptoASYMMETRIC_ALGORITHM_ECDSA, cryptoHASH_ALGORITHM_SHA256 ) )
        {
            eResult = kOTA_Err_SignatureCheckFailed;
        }
        else
        {
            OTA_LOG_L1( "[%s] Started %s signature verification, file: %s\r\n", OTA_METHOD_NAME,
                        cOTA_JSON_FileSignatureKey, ( const char * ) C->pucCertFilepath );
            pucSignerCert = prvPAL_ReadAndAssumeCertificate( ( const uint8_t * const ) C->pucCertFilepath, &ulSignerCertSize );

            if( pucSignerCert != NULL )
            {
                pucBuf = pvPortMalloc( OTA_PAL_WIN_BUF_SIZE ); /*lint !e9079 Allow conversion. */

                if( pucBuf != NULL )
                {
                    /* Rewind the received file to the beginning. */
                    if( fseek( C->pxFile, 0L, SEEK_SET ) == 0 ) /*lint !e586
                                                                 * C standard library call is being used for portability. */
                    {
                        do
                        {
                            ulBytesRead = fread( pucBuf, 1, OTA_PAL_WIN_BUF_SIZE, C->pxFile ); /*lint !e586
                                                                                                * C standard library call is being used for portability. */
                            /* Include the file chunk in the signature validation. Zero size is OK. */
                            CRYPTO_SignatureVerificationUpdate( pvSigVerifyContext, pucBuf, ulBytesRead );
                        } while( ulBytesRead > 0UL );

                        if( pdFALSE == CRYPTO_SignatureVerificationFinal( pvSigVerifyContext,
                                                                          ( char * ) pucSignerCert,
                                                                          ( size_t ) ulSignerCertSize,
                                                                          C->pxSignature->ucData,
                                                                          C->pxSignature->usSize ) ) /*lint !e732 !e9034 Allow comparison in this context. */
                        {
                            eResult = kOTA_Err_SignatureCheckFailed;
                        }

                        pvSigVerifyContext = NULL; /* The context has been freed by CRYPTO_SignatureVerificationFinal(). */
                    }
                    else
                    {
                        /* Nothing special to do. */
                    }

                    /* Free the temporary file page buffer. */
                    vPortFree( pucBuf );
                }
                else
                {
                    OTA_LOG_L1( "[%s] ERROR - Failed to allocate buffer memory.\r\n", OTA_METHOD_NAME );
                    eResult = kOTA_Err_OutOfMemory;
                }

                /* Free the signer certificate that we now own after prvReadAndAssumeCertificate(). */
                vPortFree( pucSignerCert );
            }
            else
            {
                eResult = kOTA_Err_BadSignerCert;
            }
        }
    }
    else
    {
        /* FIXME: Invalid error code for a NULL file context. */
        OTA_LOG_L1( "[%s] ERROR - Invalid OTA file context.\r\n", OTA_METHOD_NAME );
        /* Invalid OTA context or file pointer. */
        eResult = kOTA_Err_NullFilePtr;
    }

    return eResult;
}


/* Read the specified signer certificate from the filesystem into a local buffer. The allocated
 * memory becomes the property of the caller who is responsible for freeing it.
 */

static uint8_t * prvPAL_ReadAndAssumeCertificate( const uint8_t * const pucCertName,
                                                  uint32_t * const ulSignerCertSize )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_ReadAndAssumeCertificate" );

    FILE * pxFile;
    uint8_t * pucSignerCert = NULL;
    uint8_t * pucCertData = NULL;
    int32_t lSize = 0; /* For MISRA mandatory. */
    int32_t lWindowsError;

    pxFile = fopen( ( const char * ) pucCertName, "rb" ); /*lint !e586
                                                           * C standard library call is being used for portability. */

    if( pxFile != NULL )
    {
        lWindowsError = fseek( pxFile, 0, SEEK_END );         /*lint !e586
                                                               * C standard library call is being used for portability. */

        if( lWindowsError == 0 )                              /* fseek returns a non-zero value on error. */
        {
            lSize = ( s32 ) ftell( pxFile );                  /*lint !e586 Allow call in this context. */

            if( lSize != -1L )                                /* ftell returns -1 on error. */
            {
                lWindowsError = fseek( pxFile, 0, SEEK_SET ); /*lint !e586
                                                               * C standard library call is being used for portability. */
            }
            else /* ftell returned an error, pucSignerCert remains NULL. */
            {
                lWindowsError = -1L;
            }
        } /* else fseek returned an error, pucSignerCert remains NULL. */

        if( lWindowsError == 0 )
        {
            /* Allocate memory for the signer certificate plus a terminating zero so we can load and return it to the caller. */
            pucSignerCert = pvPortMalloc( lSize + 1 ); /*lint !e732 !e9034 !e9079 Allow conversion. */
        }

        if( pucSignerCert != NULL )
        {
            if( fread( pucSignerCert, 1, lSize, pxFile ) == ( size_t ) lSize ) /*lint !e586 !e732 !e9034
                                                                                * C standard library call is being used for portability. */
            {
                /* The crypto code requires the terminating zero to be part of the length so add 1 to the size. */
                *ulSignerCertSize = lSize + 1;
                pucSignerCert[ lSize ] = 0;
            }
            else
            { /* There was a problem reading the certificate file so free the memory and abort. */
                vPortFree( pucSignerCert );
                pucSignerCert = NULL;
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - Failed to allocate memory for signer cert contents.\r\n", OTA_METHOD_NAME );
            /* Nothing special to do. */
        }

        lWindowsError = fclose( pxFile ); /*lint !e586
                                           * C standard library call is being used for portability. */

        if( lWindowsError != 0 )
        {
            OTA_LOG_L1( "[%s] ERROR - File pointer operation failed.\r\n", OTA_METHOD_NAME );
            pucSignerCert = NULL;
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] No such certificate file: %s. Using aws_ota_codesigner_certificate.h.\r\n", OTA_METHOD_NAME,
                    ( const char * ) pucCertName );

        /* Allocate memory for the signer certificate plus a terminating zero so we can copy it and return to the caller. */
        lSize = sizeof( signingcredentialSIGNING_CERTIFICATE_PEM );
        pucSignerCert = pvPortMalloc( lSize );                                /*lint !e9029 !e9079 !e838 malloc proto requires void*. */
        pucCertData = ( uint8_t * ) signingcredentialSIGNING_CERTIFICATE_PEM; /*lint !e9005 we don't modify the cert but it could be set by PKCS11 so it's not const. */

        if( pucSignerCert != NULL )
        {
            memcpy( pucSignerCert, pucCertData, lSize );
            *ulSignerCertSize = lSize;
        }
        else
        {
            OTA_LOG_L1( "[%s] Error: No memory for certificate of size %d!\r\n", OTA_METHOD_NAME, lSize );
        }
    }

    return pucSignerCert; /*lint !e480 !e481 fopen and fclose are being used by-design. */
}

/*-----------------------------------------------------------*/

OTA_Err_t prvPAL_ResetDevice( void )
{
    /* Return no error.  Windows implementation does not reset device. */
    return kOTA_Err_None;
}

/*-----------------------------------------------------------*/

OTA_Err_t prvPAL_ActivateNewImage( void )
{
    /* Return no error. Windows implementation simply does nothing on activate.
     * To run the new firmware image, double click the newly downloaded exe */
    return kOTA_Err_None;
}


/*
 * Set the final state of the last transferred (final) OTA file (or bundle).
 * On Windows, the state of the OTA image is stored in PlaformImageState.txt.
 */

OTA_Err_t prvPAL_SetPlatformImageState( OTA_ImageState_t eState )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_SetPlatformImageState" );

    OTA_Err_t eResult = kOTA_Err_None;
    FILE * pstPlatformImageState;

    if( ( eState != eOTA_ImageState_Unknown ) && ( eState <= eOTA_LastImageState ) )
    {
        pstPlatformImageState = fopen( "PlatformImageState.txt", "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

        if( pstPlatformImageState != NULL )
        {
            /* Write the image state to PlatformImageState.txt. */
            if( 1 != fwrite( &eState, sizeof( OTA_ImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                                * C standard library call is being used for portability. */
            {
                OTA_LOG_L1( "[%s] ERROR - Unable to write to image state file.\r\n", OTA_METHOD_NAME );
                eResult = ( kOTA_Err_BadImageState | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                      * Errno is being used in accordance with host API documentation.
                                                                                      * Bitmasking is being used to preserve host API error with library status code. */
            }

            /* Close PlatformImageState.txt. */
            if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586 Allow call in this context. */
            {
                OTA_LOG_L1( "[%s] ERROR - Unable to close image state file.\r\n", OTA_METHOD_NAME );
                eResult = ( kOTA_Err_BadImageState | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                      * Errno is being used in accordance with host API documentation.
                                                                                      * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - Unable to open image state file.\r\n", OTA_METHOD_NAME );
            eResult = ( kOTA_Err_BadImageState | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                  * Errno is being used in accordance with host API documentation.
                                                                                  * Bitmasking is being used to preserve host API error with library status code. */
        }
    } /*lint !e481 Allow fopen and fclose calls in this context. */
    else /* Image state invalid. */
    {
        OTA_LOG_L1( "[%s] ERROR - Invalid image state provided.\r\n", OTA_METHOD_NAME );
        eResult = kOTA_Err_BadImageState;
    }

    return eResult; /*lint !e480 !e481 Allow calls to fopen and fclose in this context. */
}

/* Get the state of the currently running image.
 *
 * On Windows, this is simulated by looking for and reading the state from
 * the PlatformImageState.txt file in the current working directory.
 *
 * We read this at OTA_Init time so we can tell if the MCU image is in self
 * test mode. If it is, we expect a successful connection to the OTA services
 * within a reasonable amount of time. If we don't satisfy that requirement,
 * we assume there is something wrong with the firmware and reset the device,
 * causing it to rollback to the previous code. On Windows, this is not
 * fully simulated as there is no easy way to reset the simulated device.
 */
OTA_PAL_ImageState_t prvPAL_GetPlatformImageState( void )
{
    /* FIXME: This function should return OTA_PAL_ImageState_t, but it doesn't. */
    DEFINE_OTA_METHOD_NAME( "prvPAL_GetPlatformImageState" );

    FILE * pstPlatformImageState;
    OTA_ImageState_t eSavedAgentState = eOTA_ImageState_Unknown;
    OTA_PAL_ImageState_t ePalState = eOTA_PAL_ImageState_Unknown;

    pstPlatformImageState = fopen( "PlatformImageState.txt", "r+b" ); /*lint !e586
                                                                       * C standard library call is being used for portability. */

    if( pstPlatformImageState != NULL )
    {
        if( 1 != fread( &eSavedAgentState, sizeof( OTA_ImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                                     * C standard library call is being used for portability. */
        {
            /* If an error occured reading the file, mark the state as aborted. */
            OTA_LOG_L1( "[%s] ERROR - Unable to read image state file.\r\n", OTA_METHOD_NAME );
            ePalState = ( eOTA_PAL_ImageState_Invalid | ( errno & kOTA_PAL_ErrMask ) );
        }
        else
        {
            switch( eSavedAgentState )
            {
                case eOTA_ImageState_Testing:
                    ePalState = eOTA_PAL_ImageState_PendingCommit;
                    break;

                case eOTA_ImageState_Accepted:
                    ePalState = eOTA_PAL_ImageState_Valid;
                    break;

                case eOTA_ImageState_Rejected:
                case eOTA_ImageState_Aborted:
                default:
                    ePalState = eOTA_PAL_ImageState_Invalid;
                    break;
            }
        }

        if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586
                                                    * C standard library call is being used for portability. */
        {
            OTA_LOG_L1( "[%s] ERROR - Unable to close image state file.\r\n", OTA_METHOD_NAME );
            ePalState = ( eOTA_PAL_ImageState_Invalid | ( errno & kOTA_PAL_ErrMask ) );
        }
    }
    else
    {
        /* If no image state file exists, assume a factory image. */
        ePalState = eOTA_PAL_ImageState_Valid; /*lint !e64 Allow assignment. */
    }

    return ePalState; /*lint !e64 !e480 !e481 I/O calls and return type are used per design. */
}

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#if IOT_BUILD_TESTS == 1
    #include "aws_ota_pal_test_access_define.h"
#endif
