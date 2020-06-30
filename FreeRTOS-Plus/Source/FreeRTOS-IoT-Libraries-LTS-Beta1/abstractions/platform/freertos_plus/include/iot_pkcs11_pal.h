/*
 * FreeRTOS PKCS #11 V2.1.0
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

#ifndef IOT_PKCS11_PAL
#define IOT_PKCS11_PAL

/**
 * @file iot_pkcs11_pal.h
 * @brief Port Specific File Access functions for PKCS #11
 */

/*-----------------------------------------------------------*/
/*------------ Port Specific File Access API ----------------*/
/*--------- See iot_pkcs11_pal.c for definitions ------------*/
/*-----------------------------------------------------------*/

/*------------------------ PKCS #11 PAL functions -------------------------*/

/**
 * @functions_page{pkcs11_pal,PKCS #11 PAL, PKCS #11 PAL}
 * @functions_brief{PKCS #11 PAL Layer}
 * - @function_name{pkcs11_pal_function_initialize}
 * @function_brief{pkcs11_pal_function_initialize}
 * - @function_name{pkcs11_pal_function_saveobject}
 * @function_brief{pkcs11_pal_function_saveobject}
 * - @function_name{pkcs11_pal_function_destroyobject}
 * @function_brief{pkcs11_pal_function_destroyobject}
 * - @function_name{pkcs11_pal_function_findobject}
 * @function_brief{pkcs11_pal_function_findobject}
 * - @function_name{pkcs11_pal_function_getobjectvalue}
 * @function_brief{pkcs11_pal_function_getobjectvalue}
 * - @function_name{pkcs11_pal_function_getobjectvaluecleanup}
 * @function_brief{pkcs11_pal_function_getobjectvaluecleanup}
 */

/**
 * @function_page{PKCS11_PAL_SaveObject,pkcs11_pal,saveobject}
 * @function_snippet{pkcs11_pal,saveobject,this}
 * @copydoc PKCS11_PAL_SaveObject
 * @function_page{PKCS11_PAL_DestroyObject,pkcs11_pal,destroyobject}
 * @function_snippet{pkcs11_pal,destroyobject,this}
 * @copydoc PKCS11_PAL_DestroyObject
 * @function_page{PKCS11_PAL_FindObject,pkcs11_pal,findobject}
 * @function_snippet{pkcs11_pal,findobject,this}
 * @copydoc PKCS11_PAL_FindObject
 * @function_page{PKCS11_PAL_GetObjectValue,pkcs11_pal,getobjectvalue}
 * @function_snippet{pkcs11_pal,getobjectvalue,this}
 * @copydoc PKCS11_PAL_GetObjectValue
 * @function_page{PKCS11_PAL_GetObjectValueCleanup,pkcs11_pal,getobjectvaluecleanup}
 * @function_snippet{pkcs11_pal,getobjectvaluecleanup,this}
 * @copydoc PKCS11_PAL_GetObjectValueCleanup
 */

/**
 * @brief Initializes the PKCS #11 PAL.
 *
 * This is always called first in C_Initialize if the module is not already
 * initialized.
 *
 * @return CKR_OK on success.
 * CKR_FUNCTION_FAILED on failure.
 */
/* @[declare_pkcs11_pal_initialize] */
CK_RV PKCS11_PAL_Initialize( void );
/* @[declare_pkcs11_pal_initialize] */

/**
 * @brief Saves an object in non-volatile storage.
 *
 * Port-specific file write for cryptographic information.
 *
 * @param[in] pxLabel       Attribute containing label of the object to be stored.
 * @param[in] pucData       The object data to be saved.
 * @param[in] ulDataSize    Size (in bytes) of object data.
 *
 * @return The object handle if successful.
 * eInvalidHandle = 0 if unsuccessful.
 */
/* @[declare_pkcs11_pal_saveobject] */
CK_OBJECT_HANDLE PKCS11_PAL_SaveObject( CK_ATTRIBUTE_PTR pxLabel,
                                        CK_BYTE_PTR pucData,
                                        CK_ULONG ulDataSize );
/* @[declare_pkcs11_pal_saveobject] */

/**
 * @brief Delete an object from NVM.
 *
 * @param[in] xHandle       Handle to a PKCS #11 object.
 */
/* @[declare_pkcs11_pal_destroyobject] */
CK_RV PKCS11_PAL_DestroyObject( CK_OBJECT_HANDLE xHandle );
/* @[declare_pkcs11_pal_destroyobject] */

/**
 * @brief Translates a PKCS #11 label into an object handle.
 *
 * Port-specific object handle retrieval.
 *
 *
 * @param[in] pxLabel         Pointer to the label of the object
 *                           who's handle should be found.
 * @param[in] usLength       The length of the label, in bytes.
 *
 * @return The object handle if operation was successful.
 * Returns eInvalidHandle if unsuccessful.
 */
/* @[declare_pkcs11_pal_findobject] */
CK_OBJECT_HANDLE PKCS11_PAL_FindObject( CK_BYTE_PTR pxLabel,
                                        CK_ULONG usLength );
/* @[declare_pkcs11_pal_findobject] */


/**
 * @brief Gets the value of an object in storage, by handle.
 *
 * Port-specific file access for cryptographic information.
 *
 * This call dynamically allocates the buffer which object value
 * data is copied into.  PKCS11_PAL_GetObjectValueCleanup()
 * should be called after each use to free the dynamically allocated
 * buffer.
 *
 * @sa PKCS11_PAL_GetObjectValueCleanup
 *
 * @param[in]  xHandle      The PKCS #11 object handle of the object to get the value of.
 * @param[out] ppucData     Pointer to buffer for file data.
 * @param[out] pulDataSize  Size (in bytes) of data located in file.
 * @param[out] pIsPrivate   Boolean indicating if value is private (CK_TRUE)
 *                          or exportable (CK_FALSE)
 *
 * @return CKR_OK if operation was successful.  CKR_KEY_HANDLE_INVALID if
 * no such object handle was found, CKR_DEVICE_MEMORY if memory for
 * buffer could not be allocated, CKR_FUNCTION_FAILED for device driver
 * error.
 */
/* @[declare_pkcs11_pal_getobjectvalue] */
CK_RV PKCS11_PAL_GetObjectValue( CK_OBJECT_HANDLE xHandle,
                                 CK_BYTE_PTR * ppucData,
                                 CK_ULONG_PTR pulDataSize,
                                 CK_BBOOL * pIsPrivate );
/* @[declare_pkcs11_pal_getobjectvalue] */

/**
 * @brief Cleanup after PKCS11_GetObjectValue().
 *
 * @param[in] pucData       The buffer to free.
 *                          (*ppucData from PKCS11_PAL_GetObjectValue())
 * @param[in] ulDatasize    The length of the buffer to free.
 *                          (*pulDataSize from PKCS11_PAL_GetObjectValue())
 */
/* @[declare_pkcs11_pal_getobjectvaluecleanup] */
void PKCS11_PAL_GetObjectValueCleanup( CK_BYTE_PTR pucData,
                                       CK_ULONG ulDataSize );
/* @[declare_pkcs11_pal_getobjectvaluecleanup] */

#endif /* IOT_PKCS11_PAL include guard. */
