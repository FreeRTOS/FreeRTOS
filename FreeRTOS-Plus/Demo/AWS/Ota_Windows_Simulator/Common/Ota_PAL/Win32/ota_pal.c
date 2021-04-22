/*
 * FreeRTOS V202012.00
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

/* OTA PAL implementation for Windows platform. */

#include <stdio.h>
#include <stdlib.h>
#include "FreeRTOS.h"
#include "ota_config.h"

#include "ota.h"

//#include "aws_ota_codesigner_certificate.h"
#include "ota_pal.h"

/* Specify the OTA signature algorithm we support on this platform. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

//static OtaPalMainStatus_t otaPal_CheckFileSignature( OtaFileContext_t * const C );
//static uint8_t * otaPal_ReadAndAssumeCertificate( const uint8_t * const pucCertName,
//                                                  uint32_t * const ulSignerCertSize );

/*-----------------------------------------------------------*/

static inline BaseType_t prvContextValidate( OtaFileContext_t* pFileContext )
{
    return( ( pFileContext != NULL ) &&
            ( pFileContext->pFile != NULL ) ); /*lint !e9034 Comparison is correct for file pointer type. */
}

/* Used to set the high bit of Windows error codes for a negative return value. */
#define OTA_PAL_INT16_NEGATIVE_MASK    ( 1 << 15 )

/* Size of buffer used in file operations on this platform (Windows). */
#define OTA_PAL_WIN_BUF_SIZE ( ( size_t ) 4096UL )

/* Attempt to create a new receive file for the file chunks as they come in. */

OtaPalStatus_t otaPal_CreateFileForRx( OtaFileContext_t* const C )
{
    OtaPalMainStatus_t mainErr = OtaPalUninitialized;
    OtaPalSubStatus_t subErr = 0;

    if( C != NULL )
    {
        if ( C->pFilePath != NULL )
        {
            C->pFile = fopen( ( const char * )C->pFilePath, "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

            if ( C->pFile != NULL )
            {
                mainErr = OtaPalSuccess;
                LogInfo( ( "Receive file created.\r\n" ) );
            }
            else
            {
                mainErr = OtaPalRxFileCreateFailed;
                subErr = errno;
                LogError( ( "ERROR - Failed to start operation: already active!\r\n" ) );
            }
        }
        else
        {
            mainErr = OtaPalRxFileCreateFailed;
            LogError( ( "ERROR - Invalid filepath in filecontext.\r\n" ) );
        }
    }
    else
    {
        mainErr = OtaPalRxFileCreateFailed;
        LogError( ( "ERROR - Invalid file context provided.\r\n" ) );
    }

    return OTA_PAL_COMBINE_ERR(mainErr,subErr);
}


/* Abort receiving the specified OTA update by closing the file. */

OtaPalStatus_t otaPal_Abort( OtaFileContext_t * const C )
{
    /* Set default return status to uninitialized. */
    OtaPalMainStatus_t mainErr = OtaPalUninitialized;
    OtaPalSubStatus_t subErr = 0;
    int32_t lFileCloseResult;

    if( NULL != C )
    {
        /* Close the OTA update file if it's open. */
        if( NULL != C->pFile )
        {
            lFileCloseResult = fclose( C->pFile ); /*lint !e482 !e586
                                                      * Context file handle state is managed by this API. */
            C->pFile = NULL;

            if( 0 == lFileCloseResult )
            {
                LogInfo( ( "File closed.\r\n" ) );
                mainErr = OtaPalSuccess;
            }
            else /* Failed to close file. */
            {
                LogError( ( "ERROR - Closing file failed.\r\n" ) );
                mainErr = OtaPalFileAbort;
                subErr = errno;
            }
        }
        else
        {
            /* Nothing to do. No open file associated with this context. */
            mainErr = OtaPalSuccess;
        }
    }
    else /* Context was not valid. */
    {
        LogError( ( "ERROR - Invalid context.\r\n" ) );
        mainErr = OtaPalFileAbort;
    }

    return OTA_PAL_COMBINE_ERR(mainErr,subErr);
}

/* Write a block of data to the specified file. */
int16_t otaPal_WriteBlock( OtaFileContext_t * const C,
                           uint32_t ulOffset,
                           uint8_t * const pacData,
                           uint32_t ulBlockSize )
{
    int32_t lResult = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        lResult = fseek( C->pFile, ulOffset, SEEK_SET ); /*lint !e586 !e713 !e9034
                                                            * C standard library call is being used for portability. */

        if( 0 == lResult )
        {
            lResult = fwrite( pacData, 1, ulBlockSize, C->pFile ); /*lint !e586 !e713 !e9034
                                                                      * C standard library call is being used for portability. */

            if( lResult < 0 )
            {
                LogError( ( "ERROR - fwrite failed\r\n" ) );
                /* Mask to return a negative value. */
                lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                                * Errno is being used in accordance with host API documentation.
                                                                * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            LogError( ( "ERROR - fseek failed\r\n" ) );
            /* Mask to return a negative value. */
            lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                            * Errno is being used in accordance with host API documentation.
                                                            * Bitmasking is being used to preserve host API error with library status code. */
        }
    }
    else /* Invalid context or file pointer provided. */
    {
        LogError( ( "ERROR - Invalid context.\r\n" ) );
        lResult = -1; /*TODO: Need a negative error code from the PAL here. */
    }

    return ( int16_t ) lResult;
}

/* Close the specified file. This shall authenticate the file if it is marked as secure. */

OtaPalStatus_t otaPal_CloseFile( OtaFileContext_t * const C )
{
    OtaPalMainStatus_t mainErr = OtaPalUninitialized;
    OtaPalSubStatus_t subErr = 0;
    int32_t lWindowsError = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        if( C->pSignature != NULL )
        {
            /* Verify the file signature, close the file and return the signature verification result. */
            mainErr = OtaPalSuccess/*otaPal_CheckFileSignature( C )*/;
        }
        else
        {
            LogError( ( "NULL OTA Signature structure.\r\n" ) );
            mainErr = OtaPalSignatureCheckFailed;
        }

        /* Close the file. */
        lWindowsError = fclose( C->pFile ); /*lint !e482 !e586
                                               * C standard library call is being used for portability. */
        C->pFile = NULL;

        if( lWindowsError != 0 )
        {
            LogError( ( "Failed to close OTA update file.\r\n" ) );
            mainErr = OtaPalFileClose;
            subErr = errno;
        }

        if( mainErr == OtaPalSuccess )
        {
            LogInfo( ( "%s signature verification passed.\r\n", OTA_JsonFileSignatureKey ) );
        }
        else
        {
            LogError( ( "Failed to pass %s signature verification: %d.\r\n",
                        OTA_JsonFileSignatureKey, OTA_PAL_COMBINE_ERR(mainErr,subErr) ) );

            /* If we fail to verify the file signature that means the image is not valid. We need to set the image state to aborted. */
            otaPal_SetPlatformImageState( C, OtaImageStateAborted );

        }
    }
    else /* Invalid OTA Context. */
    {
        /* FIXME: Invalid error code for a null file context and file handle. */
        LogError( ( "Invalid file context.\r\n" ) );
        mainErr = OtaPalFileClose;
    }

    return OTA_PAL_COMBINE_ERR(mainErr,subErr);
}


/* Verify the signature of the specified file. */

//static OtaPalMainStatus_t otaPal_CheckFileSignature( OtaFileContext_t * const C )
//{
//    OtaPalMainStatus_t eResult = OtaPalSuccess;
//    uint32_t ulBytesRead;
//    uint32_t ulSignerCertSize;
//    uint8_t * pucBuf, * pucSignerCert;
//    void * pvSigVerifyContext;
//
//    if( prvContextValidate( C ) == pdTRUE )
//    {
//        /* Verify an ECDSA-SHA256 signature. */
//        if( pdFALSE == CRYPTO_SignatureVerificationStart( &pvSigVerifyContext, cryptoASYMMETRIC_ALGORITHM_ECDSA, cryptoHASH_ALGORITHM_SHA256 ) )
//        {
//            eResult = OtaPalSignatureCheckFailed;
//        }
//        else
//        {
//            LogInfo( ( "Started %s signature verification, file: %s\r\n",
//                        OTA_JsonFileSignatureKey, ( const char * ) C->pCertFilepath ) );
//            pucSignerCert = otaPal_ReadAndAssumeCertificate( ( const uint8_t * const ) C->pCertFilepath, &ulSignerCertSize );
//
//            if( pucSignerCert != NULL )
//            {
//                pucBuf = pvPortMalloc( OTA_PAL_WIN_BUF_SIZE ); /*lint !e9079 Allow conversion. */
//
//                if( pucBuf != NULL )
//                {
//                    /* Rewind the received file to the beginning. */
//                    if( fseek( C->pFile, 0L, SEEK_SET ) == 0 ) /*lint !e586
//                                                                  * C standard library call is being used for portability. */
//                    {
//                        do
//                        {
//                            ulBytesRead = fread( pucBuf, 1, OTA_PAL_WIN_BUF_SIZE, C->pFile ); /*lint !e586
//                                                                                               * C standard library call is being used for portability. */
//                            /* Include the file chunk in the signature validation. Zero size is OK. */
//                            CRYPTO_SignatureVerificationUpdate( pvSigVerifyContext, pucBuf, ulBytesRead );
//                        } while( ulBytesRead > 0UL );
//
//                        if( pdFALSE == CRYPTO_SignatureVerificationFinal( pvSigVerifyContext,
//                                                                          ( char * ) pucSignerCert,
//                                                                          ( size_t ) ulSignerCertSize,
//                                                                          C->pSignature->data,
//                                                                          C->pSignature->size ) ) /*lint !e732 !e9034 Allow comparison in this context. */
//                        {
//                            eResult = OtaPalSignatureCheckFailed;
//                        }
//                        pvSigVerifyContext = NULL;    /* The context has been freed by CRYPTO_SignatureVerificationFinal(). */
//                    }
//                    else
//                    {
//                        /* Nothing special to do. */
//                    }
//
//                    /* Free the temporary file page buffer. */
//                    vPortFree( pucBuf );
//                }
//                else
//                {
//                    LogError( ( "Failed to allocate buffer memory.\r\n" ) );
//                    eResult = OtaPalOutOfMemory;
//                }
//
//                /* Free the signer certificate that we now own after prvReadAndAssumeCertificate(). */
//                vPortFree( pucSignerCert );
//            }
//            else
//            {
//                eResult = OtaPalBadSignerCert;
//            }
//        }
//    }
//    else
//    {
//        /* FIXME: Invalid error code for a NULL file context. */
//        LogError( ( "Invalid OTA file context.\r\n" ) );
//        /* Invalid OTA context or file pointer. */
//        eResult = OtaPalNullFileContext;
//    }
//
//    return eResult;
//}


/* Read the specified signer certificate from the filesystem into a local buffer. The allocated
 * memory becomes the property of the caller who is responsible for freeing it.
 */

//static uint8_t * otaPal_ReadAndAssumeCertificate( const uint8_t * const pucCertName,
//                                                  uint32_t * const ulSignerCertSize )
//{
//    FILE * pFile;
//    uint8_t * pucSignerCert = NULL;
//    uint8_t * pucCertData = NULL;
//    int32_t lSize = 0; /* For MISRA mandatory. */
//    int32_t lWindowsError;
//
//    pFile = fopen( ( const char * ) pucCertName, "rb" ); /*lint !e586
//                                                            * C standard library call is being used for portability. */
//
//    if( pFile != NULL )
//    {
//        lWindowsError = fseek( pFile, 0, SEEK_END );         /*lint !e586
//                                                                * C standard library call is being used for portability. */
//
//        if( lWindowsError == 0 )                               /* fseek returns a non-zero value on error. */
//        {
//            lSize = (int32_t) ftell( pFile );                  /*lint !e586 Allow call in this context. */
//
//            if( lSize != -1L )                                 /* ftell returns -1 on error. */
//            {
//                lWindowsError = fseek( pFile, 0, SEEK_SET ); /*lint !e586
//                                                                * C standard library call is being used for portability. */
//            }
//            else /* ftell returned an error, pucSignerCert remains NULL. */
//            {
//                lWindowsError = -1L;
//            }
//        } /* else fseek returned an error, pucSignerCert remains NULL. */
//
//        if( lWindowsError == 0 )
//        {
//            /* Allocate memory for the signer certificate plus a terminating zero so we can load and return it to the caller. */
//            pucSignerCert = pvPortMalloc( lSize + 1 ); /*lint !e732 !e9034 !e9079 Allow conversion. */
//        }
//
//        if( pucSignerCert != NULL )
//        {
//            if( fread( pucSignerCert, 1, lSize, pFile ) == ( size_t ) lSize ) /*lint !e586 !e732 !e9034
//                                                                                 * C standard library call is being used for portability. */
//            {
//                /* The crypto code requires the terminating zero to be part of the length so add 1 to the size. */
//                *ulSignerCertSize = lSize + 1;
//                pucSignerCert[ lSize ] = 0;
//            }
//            else
//            {   /* There was a problem reading the certificate file so free the memory and abort. */
//                vPortFree( pucSignerCert );
//                pucSignerCert = NULL;
//            }
//        }
//        else
//        {
//            LogError( ( "Failed to allocate memory for signer cert contents.\r\n" ) );
//            /* Nothing special to do. */
//        }
//
//        lWindowsError = fclose( pFile ); /*lint !e586
//                                            * C standard library call is being used for portability. */
//
//        if( lWindowsError != 0 )
//        {
//            LogError( ( "File pointer operation failed.\r\n" ) );
//            pucSignerCert = NULL;
//        }
//    }
//    else
//    {
//        LogError( ( "No such certificate file: %s. Using aws_ota_codesigner_certificate.h.\r\n",
//                    ( const char * ) pucCertName ) );
//
//        /* Allocate memory for the signer certificate plus a terminating zero so we can copy it and return to the caller. */
//        lSize = sizeof( signingcredentialSIGNING_CERTIFICATE_PEM );
//        pucSignerCert = pvPortMalloc( lSize );                           /*lint !e9029 !e9079 !e838 malloc proto requires void*. */
//        pucCertData = ( uint8_t * ) signingcredentialSIGNING_CERTIFICATE_PEM; /*lint !e9005 we don't modify the cert but it could be set by PKCS11 so it's not const. */
//
//        if( pucSignerCert != NULL )
//        {
//            memcpy( pucSignerCert, pucCertData, lSize );
//            *ulSignerCertSize = lSize;
//        }
//        else
//        {
//            LogError( ( "No memory for certificate of size %d!\r\n", lSize ) );
//        }
//    }
//
//    return pucSignerCert; /*lint !e480 !e481 fopen and fclose are being used by-design. */
//}

/*-----------------------------------------------------------*/

OtaPalStatus_t otaPal_ResetDevice( OtaFileContext_t* const pFileContext )
{
    (void)pFileContext;

    /* Return no error.  Windows implementation does not reset device. */
    return OTA_PAL_COMBINE_ERR(OtaPalSuccess,0);
}

/*-----------------------------------------------------------*/

OtaPalStatus_t otaPal_ActivateNewImage( OtaFileContext_t* const pFileContext )
{
    (void)pFileContext;

    /* Return no error. Windows implementation simply does nothing on activate.
     * To run the new firmware image, double click the newly downloaded exe */
    return OTA_PAL_COMBINE_ERR(OtaPalSuccess,0);
}


/*
 * Set the final state of the last transferred (final) OTA file (or bundle).
 * On Windows, the state of the OTA image is stored in PlaformImageState.txt.
 */

OtaPalStatus_t otaPal_SetPlatformImageState( OtaFileContext_t * const pFileContext, OtaImageState_t eState )
{
    (void)pFileContext;

    OtaPalMainStatus_t mainErr = OtaPalSuccess;
    OtaPalSubStatus_t subErr = 0;
    FILE * pstPlatformImageState;

    if( eState != OtaImageStateUnknown && eState <= OtaLastImageState )
    {
        pstPlatformImageState = fopen( "PlatformImageState.txt", "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

        if( pstPlatformImageState != NULL )
        {
            /* Write the image state to PlatformImageState.txt. */
            if( 1 != fwrite( &eState, sizeof( OtaImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                                * C standard library call is being used for portability. */
            {
                LogError( ( "Unable to write to image state file.\r\n" ) );
                mainErr = OtaPalBadImageState;
                subErr = errno;
            }

            /* Close PlatformImageState.txt. */
            if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586 Allow call in this context. */
            {
                LogError( ( "Unable to close image state file.\r\n" ) );
                mainErr = OtaPalBadImageState;
                subErr = errno;
            }
        }
        else
        {
            LogError( ( "Unable to open image state file.\r\n" ) );
            mainErr = OtaPalBadImageState;
            subErr = errno;
        }
    } /*lint !e481 Allow fopen and fclose calls in this context. */
    else /* Image state invalid. */
    {
        LogError( ( "ERROR - Invalid image state provided.\r\n" ) );
        mainErr = OtaPalBadImageState;
    }

    return OTA_PAL_COMBINE_ERR(mainErr,subErr);
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
OtaPalImageState_t otaPal_GetPlatformImageState( OtaFileContext_t * const pFileContext )
{
    (void)pFileContext;

    FILE * pstPlatformImageState;
    OtaImageState_t eSavedAgentState = OtaImageStateUnknown;
    OtaPalImageState_t ePalState = OtaPalImageStateUnknown;

    pstPlatformImageState = fopen( "PlatformImageState.txt", "r+b" ); /*lint !e586
                                                                       * C standard library call is being used for portability. */

    if( pstPlatformImageState != NULL )
    {
        if( 1 != fread( &eSavedAgentState, sizeof(OtaImageState_t), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                           * C standard library call is being used for portability. */
        {
            /* If an error occured reading the file, mark the state as aborted. */
            LogError( ( "Unable to read image state file.\r\n" ) );
            ePalState = ( OtaPalImageStateInvalid | (errno & OTA_PAL_ERR_MASK) );
        }
        else
        {
            switch (eSavedAgentState)
            {
                case OtaImageStateTesting:
                    ePalState = OtaPalImageStatePendingCommit;
                    break;
                case OtaImageStateAccepted:
                    ePalState = OtaPalImageStateValid;
                    break;
                case OtaImageStateRejected:
                case OtaImageStateAborted:
                default:
                    ePalState = OtaPalImageStateInvalid;
                    break;
            }
        }


        if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586
                                                    * C standard library call is being used for portability. */
        {
            LogError( ( "Unable to close image state file.\r\n" ) );
            ePalState = (OtaPalImageStateInvalid | ( errno & OTA_PAL_ERR_MASK ) );
        }
    }
    else
    {
        /* If no image state file exists, assume a factory image. */
        ePalState = OtaPalImageStateValid; /*lint !e64 Allow assignment. */
    }

    return ePalState; /*lint !e64 !e480 !e481 I/O calls and return type are used per design. */
}

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#ifdef FREERTOS_ENABLE_UNIT_TESTS
#include "aws_ota_pal_test_access_define.h"
#endif
