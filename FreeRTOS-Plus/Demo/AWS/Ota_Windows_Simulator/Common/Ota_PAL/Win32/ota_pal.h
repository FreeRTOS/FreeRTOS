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
 * @file ota_pal.h
 * @brief Function declarations for ota_ptal.c.
 */

#ifndef _OTA_PAL_H_
#define _OTA_PAL_H_

#include "ota.h"

//static const char signingcredentialSIGNING_CERTIFICATE_PEM[] = "Paste code signing certificate here.";

/**
 * @brief Abort an OTA transfer.
 *
 * Aborts access to an existing open file represented by the OTA file context C. This is only valid
 * for jobs that started successfully.
 *
 * @note The input OtaFileContext_t C is checked for NULL by the OTA agent before this
 * function is called.
 * This function may be called before the file is opened, so the file pointer C->fileHandle may be NULL
 * when this function is called.
 *
 * @param[in] C OTA file context information.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 *
 * The file pointer will be set to NULL after this function returns.
 * OTA_ERR_NONE is returned when aborting access to the open file was successful.
 * OTA_ERR_FILE_ABORT is returned when aborting access to the open file context was unsuccessful.
 */
OtaPalStatus_t  otaPal_Abort( OtaFileContext_t * const C );

/**
 * @brief Create a new receive file for the data chunks as they come in.
 *
 * @note Opens the file indicated in the OTA file context in the MCU file system.
 *
 * @note The previous image may be present in the designated image download partition or file, so the partition or file
 * must be completely erased or overwritten in this routine.
 *
 * @note The input OtaFileContext_t C is checked for NULL by the OTA agent before this
 * function is called.
 * The device file path is a required field in the OTA job document, so C->pFilePath is
 * checked for NULL by the OTA agent before this function is called.
 *
 * @param[in] C OTA file context information.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 *
 * OTA_ERR_NONE is returned when file creation is successful.
 * OTA_ERR_RX_FILE_TOO_LARGE is returned if the file to be created exceeds the device's non-volatile memory size constraints.
 * OTA_ERR_BOOT_INFO_CREATE_FAILED is returned if the bootloader information file creation fails.
 * OTA_ERR_RX_FILE_CREATE_FAILED is returned for other errors creating the file in the device's non-volatile memory.
 */
OtaPalStatus_t  otaPal_CreateFileForRx( OtaFileContext_t * const C );

/* @brief Authenticate and close the underlying receive file in the specified OTA context.
 *
 * @note The input OtaFileContext_t C is checked for NULL by the OTA agent before this
 * function is called. This function is called only at the end of block ingestion.
 * prvPAL_CreateFileForRx() must succeed before this function is reached, so
 * C->fileHandle(or C->pFile) is never NULL.
 * The certificate path on the device is a required job document field in the OTA Agent,
 * so C->pCertFilepath is never NULL.
 * The file signature key is required job document field in the OTA Agent, so C->pSignature will
 * never be NULL.
 *
 * If the signature verification fails, file close should still be attempted.
 *
 * @param[in] C OTA file context information.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 *
 * OTA_ERR_NONE is returned on success.
 * OTA_ERR_SIGNATURE_CHECK_FAILED is returned when cryptographic signature verification fails.
 * OTA_ERR_BAD_SIGNER_CERT is returned for errors in the certificate itself.
 * OTA_ERR_FILE_CLOSE is returned when closing the file fails.
 */
OtaPalStatus_t  otaPal_CloseFile( OtaFileContext_t * const C );

/**
 * @brief Write a block of data to the specified file at the given offset.
 *
 * @note The input OtaFileContext_t C is checked for NULL by the OTA agent before this
 * function is called.
 * The file pointer/handle C->pFile, is checked for NULL by the OTA agent before this
 * function is called.
 * pacData is checked for NULL by the OTA agent before this function is called.
 * ulBlockSize is validated for range by the OTA agent before this function is called.
 * ulBlockIndex is validated by the OTA agent before this function is called.
 *
 * @param[in] C OTA file context information.
 * @param[in] ulOffset Byte offset to write to from the beginning of the file.
 * @param[in] pacData Pointer to the byte array of data to write.
 * @param[in] ulBlockSize The number of bytes to write.
 *
 * @return The number of bytes written on a success, or a negative error code from the platform abstraction layer.
 */
int16_t otaPal_WriteBlock( OtaFileContext_t * const C,
                           uint32_t ulOffset,
                           uint8_t * const pcData,
                           uint32_t ulBlockSize );

/**
 * @brief Activate the newest MCU image received via OTA.
 *
 * This function shall do whatever is necessary to activate the newest MCU
 * firmware received via OTA. It is typically just a reset of the device.
 *
 * @note This function SHOULD not return. If it does, the platform does not support
 * an automatic reset or an error occurred.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 */
OtaPalStatus_t  otaPal_ActivateNewImage( OtaFileContext_t * const C );

/**
 * @brief Reset the device.
 *
 * This function shall reset the MCU and cause a reboot of the system.
 *
 * @note This function SHOULD not return. If it does, the platform does not support
 * an automatic reset or an error occurred.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 */

OtaPalStatus_t  otaPal_ResetDevice( OtaFileContext_t * const C );

/**
 * @brief Attempt to set the state of the OTA update image.
 *
 * Do whatever is required by the platform to Accept/Reject the OTA update image (or bundle).
 * Refer to the PAL implementation to determine what happens on your platform.
 *
 * @param[in] eState The desired state of the OTA update image.
 *
 * @return The OtaErr_t error code combined with the MCU specific error code. See ota.h for
 *         OTA major error codes and your specific PAL implementation for the sub error code.
 *
 * Major error codes returned are:
 *
 *   OTA_ERR_NONE on success.
 *   OTA_ERR_BAD_IMAGE_STATE: if you specify an invalid OtaImageState_t. No sub error code.
 *   OTA_ERR_ABORT_FAILED: failed to roll back the update image as requested by OtaImageStateAborted.
 *   OTA_ERR_REJECT_FAILED: failed to roll back the update image as requested by OtaImageStateRejected.
 *   OTA_ERR_COMMIT_FAILED: failed to make the update image permanent as requested by OtaImageStateAccepted.
 */
OtaPalStatus_t  otaPal_SetPlatformImageState( OtaFileContext_t * const C,
                                       OtaImageState_t eState );

/**
 * @brief Get the state of the OTA update image.
 *
 * We read this at OTA_Init time and when the latest OTA job reports itself in self
 * test. If the update image is in the "pending commit" state, we start a self test
 * timer to assure that we can successfully connect to the OTA services and accept
 * the OTA update image within a reasonable amount of time (user configurable). If
 * we don't satisfy that requirement, we assume there is something wrong with the
 * firmware and automatically reset the device, causing it to roll back to the
 * previously known working code.
 *
 * If the update image state is not in "pending commit," the self test timer is
 * not started.
 *
 * @return An OtaPalImageState_t. One of the following:
 *   OtaPalImageStatePendingCommit (the new firmware image is in the self test phase)
 *   OtaPalImageStateValid         (the new firmware image is already committed)
 *   OtaPalImageStateInvalid       (the new firmware image is invalid or non-existent)
 *
 *   NOTE: OtaPalImageStateUnknown should NEVER be returned and indicates an implementation error.
 */
OtaPalImageState_t otaPal_GetPlatformImageState( OtaFileContext_t * const C );

#endif /* ifndef _OTA_PAL_H_ */