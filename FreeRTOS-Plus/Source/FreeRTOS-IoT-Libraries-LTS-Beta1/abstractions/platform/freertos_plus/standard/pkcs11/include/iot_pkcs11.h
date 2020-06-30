/*
 * FreeRTOS PKCS #11 V1.1.0
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

#ifndef _IOT_PKCS11_H_
#define _IOT_PKCS11_H_

#include <stdint.h>

#ifdef _WIN32
    #pragma pack(push, cryptoki, 1)
#endif

/**
 * @file iot_pkcs11.h
 * @brief Wrapper functions for PKCS #11
 */

/**
 * @brief FreeRTOS PKCS#11 Interface.
 * The following definitions are required by the PKCS#11 standard public
 * headers.
 */

#define CK_PTR    *

#ifndef NULL_PTR

/**
 * @brief Null in case null is not already defined.
 */
    #define NULL_PTR    0
#endif

/**
 * @brief CK_DEFINE_FUNCTION is deprecated.  Implementations should use CK_DECLARE_FUNCTION
 * instead when possible.
 */
#define CK_DEFINE_FUNCTION( returnType, name )             returnType name

/**
 * @brief Macro for defining a PKCS #11 functions.
 *
 */
#define CK_DECLARE_FUNCTION( returnType, name )            returnType name

/**
 * @brief Macro for defining a PKCS #11 function pointers.
 *
 */
#define CK_DECLARE_FUNCTION_POINTER( returnType, name )    returnType( CK_PTR name )

/**
 * @brief Macro for defining a PKCS #11 callback functions.
 *
 */
#define CK_CALLBACK_FUNCTION( returnType, name )           returnType( CK_PTR name )

/**
 *   @brief Length of a SHA256 digest, in bytes.
 */
#define pkcs11SHA256_DIGEST_LENGTH           32UL

/**
 * @brief Length of a curve P-256 ECDSA signature, in bytes.
 * PKCS #11 EC signatures are represented as a 32-bit R followed
 * by a 32-bit S value, and not ASN.1 encoded.
 */
#define pkcs11ECDSA_P256_SIGNATURE_LENGTH    64UL

/**
 * @brief Key strength for elliptic-curve P-256.
 */
#define pkcs11ECDSA_P256_KEY_BITS            256UL

/**
 * @brief Public exponent for RSA.
 */
#define pkcs11RSA_PUBLIC_EXPONENT            { 0x01, 0x00, 0x01 }

/**
 * @brief The number of bits in the RSA-2048 modulus.
 *
 */
#define pkcs11RSA_2048_MODULUS_BITS          2048UL

/**
 * @brief Length of PKCS #11 signature for RSA 2048 key, in bytes.
 */
#define pkcs11RSA_2048_SIGNATURE_LENGTH      ( pkcs11RSA_2048_MODULUS_BITS / 8UL )

/**
 * @brief Length of RSA signature data before padding.
 *
 * This is calculated by adding the SHA-256 hash len (32) to the 19 bytes in
 * pkcs11STUFF_APPENDED_TO_RSA_SIG = 51 bytes total.
 */
#define pkcs11RSA_SIGNATURE_INPUT_LENGTH     51UL

/**
 * @brief Elliptic-curve object identifiers.
 * From https://tools.ietf.org/html/rfc6637#section-11.
 */
#define pkcs11ELLIPTIC_CURVE_NISTP256        "1.2.840.10045.3.1.7"

/**
 * @brief Maximum length of storage for PKCS #11 label, in bytes.
 */
#define pkcs11MAX_LABEL_LENGTH               32UL /* 31 characters + 1 null terminator. */

/**
 * @brief OID for curve P-256.
 */
#define pkcs11DER_ENCODED_OID_P256           { 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07 }


/**
 * @brief Set to 1 if importing private keys is supported.
 *
 * If private key import is not supported, this value should be defined 0 in aws_pkcs11_config.h
 */
#ifndef pkcs11configIMPORT_PRIVATE_KEYS_SUPPORTED
    #define pkcs11configIMPORT_PRIVATE_KEYS_SUPPORTED    1
#endif

/**
 * @brief RSA signature padding for interoperability between providing hashed messages
 * and providing hashed messages encoded with the digest information.
 *
 * The TLS connection for mbedTLS expects a hashed, but unpadded input,
 * and it appended message digest algorithm encoding.  However, the PKCS #11 sign
 * function either wants unhashed data which it will both hash and pad OR
 * as done in this workaround, we provide hashed data with padding appended.
 *
 * DigestInfo :: = SEQUENCE{
 *      digestAlgorithm DigestAlgorithmIdentifier,
 *      digest Digest }
 *
 * DigestAlgorithmIdentifier :: = AlgorithmIdentifier
 * Digest :: = OCTET STRING
 *
 * This is the DigestInfo sequence, digest algorithm, and the octet string/length
 * for the digest, without the actual digest itself.
 */
#define pkcs11STUFF_APPENDED_TO_RSA_SIG    { 0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20 }

/* Bring in the public header. */

/* Undefine the macro for Keil Compiler to avoid conflict */
#if defined( __PASTE ) && defined( __CC_ARM )
    /* ARM RCVT stdint.h has a duplicate definition with PKCS #11. */
    #undef __PASTE
#endif

#include "pkcs11.h"

/** @brief Certificate Template
 * The object class must be the first attribute in the array.
 */
typedef struct PKCS11_CertificateTemplate
{
    CK_ATTRIBUTE xObjectClass;     /**< @brief CKA_CLASS, set to CKO_CERTIFICATE. */
    CK_ATTRIBUTE xSubject;         /**< @brief CKA_SUBJECT, this parameter is required by the PKCS #11 standard. */
    CK_ATTRIBUTE xCertificateType; /**< @brief CKA_CERTIFICATE_TYPE, set to CKC_X_509. */
    CK_ATTRIBUTE xValue;           /**< @brief CKA_VALUE, the DER byte array of the certificate contents. */
    CK_ATTRIBUTE xLabel;           /**< @brief CKA_LABEL. */
    CK_ATTRIBUTE xTokenObject;     /**< @brief CKA_TOKEN. */
} PKCS11_CertificateTemplate_t;

/*------------------------ PKCS #11 wrapper functions -------------------------*/

/**
 * @functions_page{pkcs11_iot,PKCS #11 Wrapper, PKCS #11 Wrapper}
 * @functions_brief{PKCS #11 Wrapper}
 * - @function_name{pkcs11_iot_function_xinitializepkcs11}
 * @function_brief{pkcs11_iot_function_xinitializepkcs11}
 * - @function_name{pkcs11_iot_function_xgetslotlist}
 * @function_brief{pkcs11_iot_function_xgetslotlist}
 * - @function_name{pkcs11_iot_function_xinitializepkcs11token}
 * @function_brief{pkcs11_iot_function_xinitializepkcs11token}
 * - @function_name{pkcs11_iot_function_xinitializepkcs11session}
 * @function_brief{pkcs11_iot_function_xinitializepkcs11session}
 * - @function_name{pkcs11_iot_function_xfindobjectwithlabelandclass}
 * @function_brief{pkcs11_iot_function_xfindobjectwithlabelandclass}
 * - @function_name{pkcs11_iot_function_vappendsha256algorithmidentifiersequence}
 * @function_brief{pkcs11_iot_function_vappendsha256algorithmidentifiersequence}
 */

/**
 * @function_page{xInitializePKCS11,pkcs11_iot,xinitializepkcs11}
 * @function_snippet{pkcs11_iot,xinitializepkcs11,this}
 * @copydoc xInitializePKCS11
 * @function_page{xGetSlotList,pkcs11_iot,xgetslotlist}
 * @function_snippet{pkcs11_iot,xgetslotlist,this}
 * @copydoc xGetSlotList
 * @function_page{xInitializePkcs11Token,pkcs11_iot,xinitializepkcs11token}
 * @function_snippet{pkcs11_iot,xinitializepkcs11token,this}
 * @copydoc xInitializePkcs11Token
 * @function_page{xInitializePkcs11Session,pkcs11_iot,xinitializepkcs11session}
 * @function_snippet{pkcs11_iot,xinitializepkcs11session,this}
 * @copydoc xInitializePkcs11Session
 * @function_page{xFindObjectWithLabelAndClass,pkcs11_iot,xfindobjectwithlabelandclass}
 * @function_snippet{pkcs11_iot,xfindobjectwithlabelandclass,this}
 * @copydoc xFindObjectWithLabelAndClass
 * @function_page{vAppendSHA256AlgorithmIdentifierSequence,pkcs11_iot,vappendsha256algorithmidentifiersequence}
 * @function_snippet{pkcs11_iot,vappendsha256algorithmidentifiersequence,this}
 * @copydoc vAppendSHA256AlgorithmIdentifierSequence
 */

/**
 * @brief Initializes a PKCS #11 session.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_iot_xinitializepkcs11] */
CK_RV xInitializePKCS11( void );
/* @[declare_pkcs11_iot_xinitializepkcs11] */

/**
 * @brief Get a list of available PKCS #11 slots.
 *
 * \note This function allocates memory for slots.
 * Freeing this memory is the responsibility of the caller.
 *
 *	\param[out] ppxSlotId       Pointer to slot list.  This slot list is
 *                              malloc'ed by the function and must be
 *                              freed by the caller.
 *  \param[out] pxSlotCount     Pointer to the number of slots found.
 *
 *  \return CKR_OK or PKCS #11 error code. (PKCS #11 error codes are positive).
 *
 */
/* @[declare_pkcs11_iot_xgetslotlist] */
CK_RV xGetSlotList( CK_SLOT_ID ** ppxSlotId,
                    CK_ULONG * pxSlotCount );
/* @[declare_pkcs11_iot_xgetslotlist] */

/**
 * \brief Initializes the PKCS #11 module and opens a session.
 *
 * \param[out]     pxSession   Pointer to the PKCS #11 session handle
 *                             that is created by this function.
 *
 * \return  CKR_OK upon success.  PKCS #11 error code on failure.
 *          Note that PKCS #11 error codes are positive.
 */
/* @[declare_pkcs11_iot_xinitializepkcs11session] */
CK_RV xInitializePkcs11Session( CK_SESSION_HANDLE * pxSession );
/* @[declare_pkcs11_iot_xinitializepkcs11session] */

/**
 *  \brief Initializes a PKCS #11 module and token.
 *
 *  \return CKR_OK upon success.  PKCS #11 error code on failure.
 *          Note that PKCS #11 error codes are positive.
 */
/* @[declare_pkcs11_iot_xinitializepkcs11token] */
CK_RV xInitializePkcs11Token( void );
/* @[declare_pkcs11_iot_xinitializepkcs11token] */

/**
 * \brief Searches for an object with a matching label and class provided.
 *
 *   \param[in]  xSession       An open PKCS #11 session.
 *   \param[in]  pcLabelName    A pointer to the object's label (CKA_LABEL).
 *   \param[in]  xClass         The class (CKA_CLASS) of the object.
 *                              ex: CKO_PUBLIC_KEY, CKO_PRIVATE_KEY, CKO_CERTIFICATE
 *   \param[out] pxHandle       Pointer to the location where the handle of
 *                              the found object should be placed.
 *
 * \note If no matching object is found, pxHandle will point
 * to an object with handle 0 (Invalid Object Handle).
 *
 * \note This function assumes that there is only one
 * object that meets the CLASS/LABEL criteria.
 */
/* @[declare_pkcs11_iot_xfindobjectwithlabelandclass] */
CK_RV xFindObjectWithLabelAndClass( CK_SESSION_HANDLE xSession,
                                    char * pcLabelName,
                                    CK_OBJECT_CLASS xClass,
                                    CK_OBJECT_HANDLE_PTR pxHandle );
/* @[declare_pkcs11_iot_xfindobjectwithlabelandclass] */

/**
 * \brief Appends digest algorithm sequence to SHA-256 hash for RSA signatures
 *
 * This function pre-appends the digest algorithm identifier to the SHA-256
 * hash of a message.
 *
 * DigestInfo :: = SEQUENCE{
 *      digestAlgorithm DigestAlgorithmIdentifier,
 *      digest Digest }
 *
 * \param[in] puc32ByteHashedMessage     A 32-byte buffer containing the SHA-256
 *                                      hash of the data to be signed.
 * \param[out] puc51ByteHashOidBuffer    A 51-byte output buffer containing the
 *                                      DigestInfo structure.  This memory
 *                                      must be allocated by the caller.
 *
 * \return CKR_OK if successful, CKR_ARGUMENTS_BAD if NULL pointer passed in.
 *
 */
/* @[declare_pkcs11_iot_vappendsha256algorithmidentifiersequence] */
CK_RV vAppendSHA256AlgorithmIdentifierSequence( const uint8_t * puc32ByteHashedMessage,
                                                uint8_t * puc51ByteHashOidBuffer );
/* @[declare_pkcs11_iot_vappendsha256algorithmidentifiersequence] */

#ifdef _WIN32
    #pragma pack(pop, cryptoki)
#endif

#endif /* ifndef _IOT_PKCS11_H_ */
