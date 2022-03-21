/*
 * FreeRTOS V202112.00
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

/**
 * @file ota_pal.c
 * @brief OTA PAL implementation for Windows platform.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* Kernel includes. */
#include "FreeRTOS.h"

/* Library config includes. */
#include "ota_config.h"

/* OTA Library include. */
#include "ota.h"
#include "ota_pal.h"

#include "code_signature_verification.h"

/* Specify the OTA signature algorithm we support on this platform. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

static OtaPalMainStatus_t otaPal_CheckFileSignature( OtaFileContext_t * const C );

/*-----------------------------------------------------------*/

static inline BaseType_t prvContextValidate( OtaFileContext_t* pFileContext )
{
    return( ( pFileContext != NULL ) &&
            ( pFileContext->pFile != NULL ) ); /*lint !e9034 Comparison is correct for file pointer type. */
}

/* Used to set the high bit of Windows error codes for a negative return value. */
#define OTA_PAL_INT16_NEGATIVE_MASK    ( 1 << 15 )

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
            mainErr = otaPal_CheckFileSignature( C );
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

static OtaPalMainStatus_t otaPal_CheckFileSignature( OtaFileContext_t* const C )
{
    OtaPalMainStatus_t eResult = OtaPalSignatureCheckFailed;

    if ( prvContextValidate( C ) == pdTRUE )
    {
        eResult = xValidateImageSignature( C );
    }
    else
    {
        LogError( ( "OTA image signature is invalid.\r\n" ) );
    }

    return eResult;
}

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
            /* If an error occurred reading the file, mark the state as aborted. */
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
