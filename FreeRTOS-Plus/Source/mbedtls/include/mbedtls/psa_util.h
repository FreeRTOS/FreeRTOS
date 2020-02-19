/**
 * \file psa_util.h
 *
 * \brief Utility functions for the use of the PSA Crypto library.
 *
 * \warning This function is not part of the public API and may
 *          change at any time.
 */
/*
 *  Copyright (C) 2006-2018, ARM Limited, All Rights Reserved
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

#ifndef MBEDTLS_PSA_UTIL_H
#define MBEDTLS_PSA_UTIL_H

#if !defined(MBEDTLS_CONFIG_FILE)
#include "config.h"
#else
#include MBEDTLS_CONFIG_FILE
#endif

#if defined(MBEDTLS_USE_PSA_CRYPTO)

#include "psa/crypto.h"

#include "ecp.h"
#include "md.h"
#include "pk.h"
#include "oid.h"

#include <string.h>

/* Translations for symmetric crypto. */

static inline psa_key_type_t mbedtls_psa_translate_cipher_type(
    mbedtls_cipher_type_t cipher )
{
    switch( cipher )
    {
        case MBEDTLS_CIPHER_AES_128_CCM:
        case MBEDTLS_CIPHER_AES_192_CCM:
        case MBEDTLS_CIPHER_AES_256_CCM:
        case MBEDTLS_CIPHER_AES_128_GCM:
        case MBEDTLS_CIPHER_AES_192_GCM:
        case MBEDTLS_CIPHER_AES_256_GCM:
        case MBEDTLS_CIPHER_AES_128_CBC:
        case MBEDTLS_CIPHER_AES_192_CBC:
        case MBEDTLS_CIPHER_AES_256_CBC:
            return( PSA_KEY_TYPE_AES );

        /* ARIA not yet supported in PSA. */
        /* case MBEDTLS_CIPHER_ARIA_128_CCM:
           case MBEDTLS_CIPHER_ARIA_192_CCM:
           case MBEDTLS_CIPHER_ARIA_256_CCM:
           case MBEDTLS_CIPHER_ARIA_128_GCM:
           case MBEDTLS_CIPHER_ARIA_192_GCM:
           case MBEDTLS_CIPHER_ARIA_256_GCM:
           case MBEDTLS_CIPHER_ARIA_128_CBC:
           case MBEDTLS_CIPHER_ARIA_192_CBC:
           case MBEDTLS_CIPHER_ARIA_256_CBC:
               return( PSA_KEY_TYPE_ARIA ); */

        default:
            return( 0 );
    }
}

static inline psa_algorithm_t mbedtls_psa_translate_cipher_mode(
    mbedtls_cipher_mode_t mode, size_t taglen )
{
    switch( mode )
    {
        case MBEDTLS_MODE_GCM:
            return( PSA_ALG_AEAD_WITH_TAG_LENGTH( PSA_ALG_GCM, taglen ) );
        case MBEDTLS_MODE_CCM:
            return( PSA_ALG_AEAD_WITH_TAG_LENGTH( PSA_ALG_CCM, taglen ) );
        case MBEDTLS_MODE_CBC:
            if( taglen == 0 )
                return( PSA_ALG_CBC_NO_PADDING );
            /* Intentional fallthrough for taglen != 0 */
            /* fallthrough */
        default:
            return( 0 );
    }
}

static inline psa_key_usage_t mbedtls_psa_translate_cipher_operation(
    mbedtls_operation_t op )
{
    switch( op )
    {
        case MBEDTLS_ENCRYPT:
            return( PSA_KEY_USAGE_ENCRYPT );
        case MBEDTLS_DECRYPT:
            return( PSA_KEY_USAGE_DECRYPT );
        default:
            return( 0 );
    }
}

/* Translations for hashing. */

static inline psa_algorithm_t mbedtls_psa_translate_md( mbedtls_md_type_t md_alg )
{
    switch( md_alg )
    {
#if defined(MBEDTLS_MD2_C)
    case MBEDTLS_MD_MD2:
        return( PSA_ALG_MD2 );
#endif
#if defined(MBEDTLS_MD4_C)
    case MBEDTLS_MD_MD4:
        return( PSA_ALG_MD4 );
#endif
#if defined(MBEDTLS_MD5_C)
    case MBEDTLS_MD_MD5:
        return( PSA_ALG_MD5 );
#endif
#if defined(MBEDTLS_SHA1_C)
    case MBEDTLS_MD_SHA1:
        return( PSA_ALG_SHA_1 );
#endif
#if defined(MBEDTLS_SHA256_C)
    case MBEDTLS_MD_SHA224:
        return( PSA_ALG_SHA_224 );
    case MBEDTLS_MD_SHA256:
        return( PSA_ALG_SHA_256 );
#endif
#if defined(MBEDTLS_SHA512_C)
    case MBEDTLS_MD_SHA384:
        return( PSA_ALG_SHA_384 );
    case MBEDTLS_MD_SHA512:
        return( PSA_ALG_SHA_512 );
#endif
#if defined(MBEDTLS_RIPEMD160_C)
    case MBEDTLS_MD_RIPEMD160:
        return( PSA_ALG_RIPEMD160 );
#endif
    case MBEDTLS_MD_NONE:  /* Intentional fallthrough */
    default:
        return( 0 );
    }
}

/* Translations for ECC. */

static inline int mbedtls_psa_get_ecc_oid_from_id(
    psa_ecc_curve_t curve, char const **oid, size_t *oid_len )
{
    switch( curve )
    {
#if defined(MBEDTLS_ECP_DP_SECP192R1_ENABLED)
        case PSA_ECC_CURVE_SECP192R1:
            *oid = MBEDTLS_OID_EC_GRP_SECP192R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP192R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP192R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP224R1_ENABLED)
        case PSA_ECC_CURVE_SECP224R1:
            *oid = MBEDTLS_OID_EC_GRP_SECP224R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP224R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP224R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP256R1_ENABLED)
        case PSA_ECC_CURVE_SECP256R1:
            *oid = MBEDTLS_OID_EC_GRP_SECP256R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP256R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP256R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP384R1_ENABLED)
        case PSA_ECC_CURVE_SECP384R1:
            *oid = MBEDTLS_OID_EC_GRP_SECP384R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP384R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP384R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP521R1_ENABLED)
        case PSA_ECC_CURVE_SECP521R1:
            *oid = MBEDTLS_OID_EC_GRP_SECP521R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP521R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP521R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP192K1_ENABLED)
        case PSA_ECC_CURVE_SECP192K1:
            *oid = MBEDTLS_OID_EC_GRP_SECP192K1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP192K1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP192K1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP224K1_ENABLED)
        case PSA_ECC_CURVE_SECP224K1:
            *oid = MBEDTLS_OID_EC_GRP_SECP224K1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP224K1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP224K1_ENABLED */
#if defined(MBEDTLS_ECP_DP_SECP256K1_ENABLED)
        case PSA_ECC_CURVE_SECP256K1:
            *oid = MBEDTLS_OID_EC_GRP_SECP256K1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_SECP256K1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_SECP256K1_ENABLED */
#if defined(MBEDTLS_ECP_DP_BP256R1_ENABLED)
        case PSA_ECC_CURVE_BRAINPOOL_P256R1:
            *oid = MBEDTLS_OID_EC_GRP_BP256R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_BP256R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_BP256R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_BP384R1_ENABLED)
        case PSA_ECC_CURVE_BRAINPOOL_P384R1:
            *oid = MBEDTLS_OID_EC_GRP_BP384R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_BP384R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_BP384R1_ENABLED */
#if defined(MBEDTLS_ECP_DP_BP512R1_ENABLED)
        case PSA_ECC_CURVE_BRAINPOOL_P512R1:
            *oid = MBEDTLS_OID_EC_GRP_BP512R1;
            *oid_len = MBEDTLS_OID_SIZE( MBEDTLS_OID_EC_GRP_BP512R1 );
            return( 0 );
#endif /* MBEDTLS_ECP_DP_BP512R1_ENABLED */
    }

     return( -1 );
}

#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH 1

#if defined(MBEDTLS_ECP_DP_SECP192R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 192 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 192 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP192R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP224R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 224 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 224 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP224R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP256R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 256 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 256 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP256R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP384R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 384 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 384 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP384R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP521R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 521 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 521 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP521R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP192K1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 192 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 192 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP192K1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP224K1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 224 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 224 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP224K1_ENABLED */

#if defined(MBEDTLS_ECP_DP_SECP256K1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 256 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 256 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_SECP256K1_ENABLED */

#if defined(MBEDTLS_ECP_DP_BP256R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 256 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 256 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_BP256R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_BP384R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 384 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 384 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_BP384R1_ENABLED */

#if defined(MBEDTLS_ECP_DP_BP512R1_ENABLED)
#if MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH < ( 2 * ( ( 512 + 7 ) / 8 ) + 1 )
#undef MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH
#define MBEDTLS_PSA_MAX_EC_PUBKEY_LENGTH ( 2 * ( ( 512 + 7 ) / 8 ) + 1 )
#endif
#endif /* MBEDTLS_ECP_DP_BP512R1_ENABLED */


static inline psa_ecc_curve_t mbedtls_psa_translate_ecc_group( mbedtls_ecp_group_id grpid )
{
    switch( grpid )
    {
#if defined(MBEDTLS_ECP_DP_SECP192R1_ENABLED)
        case MBEDTLS_ECP_DP_SECP192R1:
            return( PSA_ECC_CURVE_SECP192R1 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP224R1_ENABLED)
        case MBEDTLS_ECP_DP_SECP224R1:
            return( PSA_ECC_CURVE_SECP224R1 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP256R1_ENABLED)
        case MBEDTLS_ECP_DP_SECP256R1:
            return( PSA_ECC_CURVE_SECP256R1 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP384R1_ENABLED)
        case MBEDTLS_ECP_DP_SECP384R1:
            return( PSA_ECC_CURVE_SECP384R1 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP521R1_ENABLED)
        case MBEDTLS_ECP_DP_SECP521R1:
            return( PSA_ECC_CURVE_SECP521R1 );
#endif
#if defined(MBEDTLS_ECP_DP_BP256R1_ENABLED)
        case MBEDTLS_ECP_DP_BP256R1:
            return( PSA_ECC_CURVE_BRAINPOOL_P256R1 );
#endif
#if defined(MBEDTLS_ECP_DP_BP384R1_ENABLED)
        case MBEDTLS_ECP_DP_BP384R1:
            return( PSA_ECC_CURVE_BRAINPOOL_P384R1 );
#endif
#if defined(MBEDTLS_ECP_DP_BP512R1_ENABLED)
        case MBEDTLS_ECP_DP_BP512R1:
            return( PSA_ECC_CURVE_BRAINPOOL_P512R1 );
#endif
#if defined(MBEDTLS_ECP_DP_CURVE25519_ENABLED)
        case MBEDTLS_ECP_DP_CURVE25519:
            return( PSA_ECC_CURVE_CURVE25519 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP192K1_ENABLED)
        case MBEDTLS_ECP_DP_SECP192K1:
            return( PSA_ECC_CURVE_SECP192K1 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP224K1_ENABLED)
        case MBEDTLS_ECP_DP_SECP224K1:
            return( PSA_ECC_CURVE_SECP224K1 );
#endif
#if defined(MBEDTLS_ECP_DP_SECP256K1_ENABLED)
        case MBEDTLS_ECP_DP_SECP256K1:
            return( PSA_ECC_CURVE_SECP256K1 );
#endif
#if defined(MBEDTLS_ECP_DP_CURVE448_ENABLED)
        case MBEDTLS_ECP_DP_CURVE448:
            return( PSA_ECC_CURVE_CURVE448 );
#endif
        default:
            return( 0 );
    }
}


#define MBEDTLS_PSA_ECC_KEY_BITS_OF_CURVE( curve )                \
    ( curve == PSA_ECC_CURVE_SECP192R1        ? 192 :             \
      curve == PSA_ECC_CURVE_SECP224R1        ? 224 :             \
      curve == PSA_ECC_CURVE_SECP256R1        ? 256 :             \
      curve == PSA_ECC_CURVE_SECP384R1        ? 384 :             \
      curve == PSA_ECC_CURVE_SECP521R1        ? 521 :             \
      curve == PSA_ECC_CURVE_SECP192K1        ? 192 :             \
      curve == PSA_ECC_CURVE_SECP224K1        ? 224 :             \
      curve == PSA_ECC_CURVE_SECP256K1        ? 256 :             \
      curve == PSA_ECC_CURVE_BRAINPOOL_P256R1 ? 256 :             \
      curve == PSA_ECC_CURVE_BRAINPOOL_P384R1 ? 384 :             \
      curve == PSA_ECC_CURVE_BRAINPOOL_P512R1 ? 512 :             \
      0 )

#define MBEDTLS_PSA_ECC_KEY_BYTES_OF_CURVE( curve )                \
    ( ( MBEDTLS_PSA_ECC_KEY_BITS_OF_CURVE( curve ) + 7 ) / 8 )

/* Translations for PK layer */

static inline int mbedtls_psa_err_translate_pk( psa_status_t status )
{
    switch( status )
    {
        case PSA_SUCCESS:
            return( 0 );
        case PSA_ERROR_NOT_SUPPORTED:
            return( MBEDTLS_ERR_PK_FEATURE_UNAVAILABLE );
        case PSA_ERROR_INSUFFICIENT_MEMORY:
            return( MBEDTLS_ERR_PK_ALLOC_FAILED );
        case PSA_ERROR_INSUFFICIENT_ENTROPY:
            return( MBEDTLS_ERR_ECP_RANDOM_FAILED );
        case PSA_ERROR_BAD_STATE:
            return( MBEDTLS_ERR_PK_BAD_INPUT_DATA );
        /* All other failures */
        case PSA_ERROR_COMMUNICATION_FAILURE:
        case PSA_ERROR_HARDWARE_FAILURE:
        case PSA_ERROR_TAMPERING_DETECTED:
            return( MBEDTLS_ERR_PK_HW_ACCEL_FAILED );
        default: /* We return the same as for the 'other failures',
                  * but list them separately nonetheless to indicate
                  * which failure conditions we have considered. */
            return( MBEDTLS_ERR_PK_HW_ACCEL_FAILED );
    }
}

/* Translations for ECC */

/* This function transforms an ECC group identifier from
 * https://www.iana.org/assignments/tls-parameters/tls-parameters.xhtml#tls-parameters-8
 * into a PSA ECC group identifier. */
static inline psa_ecc_curve_t mbedtls_psa_parse_tls_ecc_group(
    uint16_t tls_ecc_grp_reg_id )
{
    /* The PSA identifiers are currently aligned with those from
     * the TLS Supported Groups registry, so no conversion is necessary. */
    return( (psa_ecc_curve_t) tls_ecc_grp_reg_id );
}

/* This function takes a buffer holding an EC public key
 * exported through psa_export_public_key(), and converts
 * it into an ECPoint structure to be put into a ClientKeyExchange
 * message in an ECDHE exchange.
 *
 * Both the present and the foreseeable future format of EC public keys
 * used by PSA have the ECPoint structure contained in the exported key
 * as a subbuffer, and the function merely selects this subbuffer instead
 * of making a copy.
 */
static inline int mbedtls_psa_tls_psa_ec_to_ecpoint( unsigned char *src,
                                                     size_t srclen,
                                                     unsigned char **dst,
                                                     size_t *dstlen )
{
    *dst = src;
    *dstlen = srclen;
    return( 0 );
}

/* This function takes a buffer holding an ECPoint structure
 * (as contained in a TLS ServerKeyExchange message for ECDHE
 * exchanges) and converts it into a format that the PSA key
 * agreement API understands.
 */
static inline int mbedtls_psa_tls_ecpoint_to_psa_ec( psa_ecc_curve_t curve,
                                                     unsigned char const *src,
                                                     size_t srclen,
                                                     unsigned char *dst,
                                                     size_t dstlen,
                                                     size_t *olen )
{
    ((void) curve);

    if( srclen > dstlen )
        return( MBEDTLS_ERR_ECP_BUFFER_TOO_SMALL );

    memcpy( dst, src, srclen );
    *olen = srclen;
    return( 0 );
}

#endif /* MBEDTLS_USE_PSA_CRYPTO */

#endif /* MBEDTLS_PSA_UTIL_H */
