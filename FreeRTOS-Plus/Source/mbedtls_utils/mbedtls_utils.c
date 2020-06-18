/*
 *  Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); you may
 *  not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  This file is part of mbed TLS (https://tls.mbed.org)
 */

/**
 * @file mbedtls_utils.c
 * @brief Helper functions originating from mbedTLS.
 */

/* Standard includes. */
#include <string.h>

/* mbedTLS includes. */
#include "mbedtls/base64.h"
#include "mbedtls/rsa.h"
#include "mbedtls/asn1.h"
#include "mbedtls/platform_util.h"
#include "mbedtls/oid.h"
/*-----------------------------------------------------------*/

/* @brief Converts PEM documents into DER formatted byte arrays.
 * This is a helper function from mbedTLS util pem2der.c
 * (https://github.com/ARMmbed/mbedtls/blob/development/programs/util/pem2der.c#L75)
 *
 * \param pucInput[in]       Pointer to PEM object
 * \param xLen[in]           Length of PEM object
 * \param pucOutput[out]     Pointer to buffer where DER oboject will be placed
 * \param pxOlen[in/out]     Pointer to length of DER buffer.  This value is updated
 *                          to contain the actual length of the converted DER object.
 *
 * \return 0 if successful.  Negative if conversion failed.  If buffer is not
 * large enough to hold converted object, pxOlen is still updated but -1 is returned.
 *
 */
int convert_pem_to_der( const unsigned char * pucInput,
                        size_t xLen,
                        unsigned char * pucOutput,
                        size_t * pxOlen )
{
    int lRet;
    const unsigned char * pucS1;
    const unsigned char * pucS2;
    const unsigned char * pucEnd = pucInput + xLen;
    size_t xOtherLen = 0;

    pucS1 = ( unsigned char * ) strstr( ( const char * ) pucInput, "-----BEGIN" );

    if( pucS1 == NULL )
    {
        return( -1 );
    }

    pucS2 = ( unsigned char * ) strstr( ( const char * ) pucInput, "-----END" );

    if( pucS2 == NULL )
    {
        return( -1 );
    }

    pucS1 += 10;

    while( pucS1 < pucEnd && *pucS1 != '-' )
    {
        pucS1++;
    }

    while( pucS1 < pucEnd && *pucS1 == '-' )
    {
        pucS1++;
    }

    if( *pucS1 == '\r' )
    {
        pucS1++;
    }

    if( *pucS1 == '\n' )
    {
        pucS1++;
    }

    if( ( pucS2 <= pucS1 ) || ( pucS2 > pucEnd ) )
    {
        return( -1 );
    }

    lRet = mbedtls_base64_decode( NULL, 0, &xOtherLen, ( const unsigned char * ) pucS1, pucS2 - pucS1 );

    if( lRet == MBEDTLS_ERR_BASE64_INVALID_CHARACTER )
    {
        return( lRet );
    }

    if( xOtherLen > *pxOlen )
    {
        return( -1 );
    }

    if( ( lRet = mbedtls_base64_decode( pucOutput, xOtherLen, &xOtherLen, ( const unsigned char * ) pucS1,
                                        pucS2 - pucS1 ) ) != 0 )
    {
        return( lRet );
    }

    *pxOlen = xOtherLen;

    return( 0 );
}
/*-----------------------------------------------------------*/


/* This function is a modified version of the static function
rsa_rsassa_pkcs1_v15_encode() inside of rsa.c in mbedTLS.  It has been extracted 
so that FreeRTOS PKCS #11 libraries and testing may use it. */

/* Construct a PKCS v1.5 encoding of a hashed message
 *
 * This is used both for signature generation and verification.
 *
 * Parameters:
 * - md_alg:  Identifies the hash algorithm used to generate the given hash;
 *            MBEDTLS_MD_NONE if raw data is signed.
 * - hashlen: Length of hash in case hashlen is MBEDTLS_MD_NONE.
 * - hash:    Buffer containing the hashed message or the raw data.
 * - dst_len: Length of the encoded message.
 * - dst:     Buffer to hold the encoded message.
 *
 * Assumptions:
 * - hash has size hashlen if md_alg == MBEDTLS_MD_NONE.
 * - hash has size corresponding to md_alg if md_alg != MBEDTLS_MD_NONE.
 * - dst points to a buffer of size at least dst_len.
 *
 */

/* \brief Formats cryptographically hashed data for RSA signing in accordance
 * with PKCS #1 version 1.5.
 *
 * Currently assumes SHA-256.
 */
int PKI_RSA_RSASSA_PKCS1_v15_Encode( const unsigned char * hash,
                                     size_t dst_len,
                                     unsigned char * dst )
{
    size_t oid_size = 0;
    size_t nb_pad = dst_len;
    unsigned char * p = dst;
    const char * oid = NULL;
    mbedtls_md_type_t md_alg = MBEDTLS_MD_SHA256;
    unsigned int hashlen = 0;

    const mbedtls_md_info_t * md_info = mbedtls_md_info_from_type( md_alg );

    if( md_info == NULL )
    {
        return( MBEDTLS_ERR_RSA_BAD_INPUT_DATA );
    }

    if( mbedtls_oid_get_oid_by_md( md_alg, &oid, &oid_size ) != 0 )
    {
        return( MBEDTLS_ERR_RSA_BAD_INPUT_DATA );
    }

    hashlen = mbedtls_md_get_size( md_info );

    /* Double-check that 8 + hashlen + oid_size can be used as a
     * 1-byte ASN.1 length encoding and that there's no overflow. */
    if( ( 8 + hashlen + oid_size >= 0x80 ) ||
        ( 10 + hashlen < hashlen ) ||
        ( 10 + hashlen + oid_size < 10 + hashlen ) )
    {
        return( MBEDTLS_ERR_RSA_BAD_INPUT_DATA );
    }

    /*
     * Static bounds check:
     * - Need 10 bytes for five tag-length pairs.
     *   (Insist on 1-byte length encodings to protect against variants of
     *    Bleichenbacher's forgery attack against lax PKCS#1v1.5 verification)
     * - Need hashlen bytes for hash
     * - Need oid_size bytes for hash alg OID.
     */
    if( nb_pad < 10 + hashlen + oid_size )
    {
        return( MBEDTLS_ERR_RSA_BAD_INPUT_DATA );
    }

    nb_pad -= 10 + hashlen + oid_size;

    /* Need space for signature header and padding delimiter (3 bytes),
     * and 8 bytes for the minimal padding */
    if( nb_pad < 3 + 8 )
    {
        return( MBEDTLS_ERR_RSA_BAD_INPUT_DATA );
    }

    nb_pad -= 3;

    /* Now nb_pad is the amount of memory to be filled
     * with padding, and at least 8 bytes long. */

    /* Write signature header and padding */
    *p++ = 0;
    *p++ = MBEDTLS_RSA_SIGN;
    memset( p, 0xFF, nb_pad );
    p += nb_pad;
    *p++ = 0;

    /* Are we signing raw data? */
    if( md_alg == MBEDTLS_MD_NONE )
    {
        memcpy( p, hash, hashlen );
        return( 0 );
    }

    /* Signing hashed data, add corresponding ASN.1 structure
     *
     * DigestInfo ::= SEQUENCE {
     *   digestAlgorithm DigestAlgorithmIdentifier,
     *   digest Digest }
     * DigestAlgorithmIdentifier ::= AlgorithmIdentifier
     * Digest ::= OCTET STRING
     *
     * Schematic:
     * TAG-SEQ + LEN [ TAG-SEQ + LEN [ TAG-OID  + LEN [ OID  ]
     *                                 TAG-NULL + LEN [ NULL ] ]
     *                 TAG-OCTET + LEN [ HASH ] ]
     */
    *p++ = MBEDTLS_ASN1_SEQUENCE | MBEDTLS_ASN1_CONSTRUCTED;
    *p++ = ( unsigned char ) ( 0x08 + oid_size + hashlen );
    *p++ = MBEDTLS_ASN1_SEQUENCE | MBEDTLS_ASN1_CONSTRUCTED;
    *p++ = ( unsigned char ) ( 0x04 + oid_size );
    *p++ = MBEDTLS_ASN1_OID;
    *p++ = ( unsigned char ) oid_size;
    memcpy( p, oid, oid_size );
    p += oid_size;
    *p++ = MBEDTLS_ASN1_NULL;
    *p++ = 0x00;
    *p++ = MBEDTLS_ASN1_OCTET_STRING;
    *p++ = ( unsigned char ) hashlen;
    memcpy( p, hash, hashlen );
    p += hashlen;

    /* Just a sanity-check, should be automatic
     * after the initial bounds check. */
    if( p != dst + dst_len )
    {
        mbedtls_platform_zeroize( dst, dst_len );
        return( MBEDTLS_ERR_RSA_BAD_INPUT_DATA );
    }

    return( 0 );
}
