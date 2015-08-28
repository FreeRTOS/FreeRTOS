/* error.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#include <cyassl/ctaocrypt/error-crypt.h>

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of XSTRNCPY */
    #pragma warning(disable: 4996)
#endif

const char* CTaoCryptGetErrorString(int error)
{
#ifdef NO_ERROR_STRINGS

    (void)error;
    return "no support for error strings built in";

#else

    switch (error) {

    case OPEN_RAN_E :
        return "opening random device error";

    case READ_RAN_E :
        return "reading random device error";

    case WINCRYPT_E :
        return "windows crypt init error";

    case CRYPTGEN_E :
        return "windows crypt generation error";

    case RAN_BLOCK_E :
        return "random device read would block error";

    case BAD_MUTEX_E :
        return "Bad mutex, operation failed";

    case MP_INIT_E :
        return "mp_init error state";

    case MP_READ_E :
        return "mp_read error state";

    case MP_EXPTMOD_E :
        return "mp_exptmod error state";

    case MP_TO_E :
        return "mp_to_xxx error state, can't convert";

    case MP_SUB_E :
        return "mp_sub error state, can't subtract";

    case MP_ADD_E :
        return "mp_add error state, can't add";

    case MP_MUL_E :
        return "mp_mul error state, can't multiply";

    case MP_MULMOD_E :
        return "mp_mulmod error state, can't multiply mod";

    case MP_MOD_E :
        return "mp_mod error state, can't mod";

    case MP_INVMOD_E :
        return "mp_invmod error state, can't inv mod";

    case MP_CMP_E :
        return "mp_cmp error state";

    case MP_ZERO_E :
        return "mp zero result, not expected";

    case MEMORY_E :
        return "out of memory error";

    case RSA_WRONG_TYPE_E :
        return "RSA wrong block type for RSA function";

    case RSA_BUFFER_E :
        return "RSA buffer error, output too small or input too big";

    case BUFFER_E :
        return "Buffer error, output too small or input too big";

    case ALGO_ID_E :
        return "Setting Cert AlogID error";

    case PUBLIC_KEY_E :
        return "Setting Cert Public Key error";

    case DATE_E :
        return "Setting Cert Date validity error";

    case SUBJECT_E :
        return "Setting Cert Subject name error";

    case ISSUER_E :
        return "Setting Cert Issuer name error";

    case CA_TRUE_E :
        return "Setting basic constraint CA true error";

    case EXTENSIONS_E :
        return "Setting extensions error";

    case ASN_PARSE_E :
        return "ASN parsing error, invalid input";

    case ASN_VERSION_E :
        return "ASN version error, invalid number";

    case ASN_GETINT_E :
        return "ASN get big int error, invalid data";

    case ASN_RSA_KEY_E :
        return "ASN key init error, invalid input";

    case ASN_OBJECT_ID_E :
        return "ASN object id error, invalid id";

    case ASN_TAG_NULL_E :
        return "ASN tag error, not null";

    case ASN_EXPECT_0_E :
        return "ASN expect error, not zero";

    case ASN_BITSTR_E :
        return "ASN bit string error, wrong id";

    case ASN_UNKNOWN_OID_E :
        return "ASN oid error, unknown sum id";

    case ASN_DATE_SZ_E :
        return "ASN date error, bad size";

    case ASN_BEFORE_DATE_E :
        return "ASN date error, current date before";

    case ASN_AFTER_DATE_E :
        return "ASN date error, current date after";

    case ASN_SIG_OID_E :
        return "ASN signature error, mismatched oid";

    case ASN_TIME_E :
        return "ASN time error, unkown time type";

    case ASN_INPUT_E :
        return "ASN input error, not enough data";

    case ASN_SIG_CONFIRM_E :
        return "ASN sig error, confirm failure";

    case ASN_SIG_HASH_E :
        return "ASN sig error, unsupported hash type";

    case ASN_SIG_KEY_E :
        return "ASN sig error, unsupported key type";

    case ASN_DH_KEY_E :
        return "ASN key init error, invalid input";

    case ASN_NTRU_KEY_E :
        return "ASN NTRU key decode error, invalid input";

    case ASN_CRIT_EXT_E:
        return "X.509 Critical extension ignored";

    case ECC_BAD_ARG_E :
        return "ECC input argument wrong type, invalid input";

    case ASN_ECC_KEY_E :
        return "ECC ASN1 bad key data, invalid input";

    case ECC_CURVE_OID_E :
        return "ECC curve sum OID unsupported, invalid input";

    case BAD_FUNC_ARG :
        return "Bad function argument";

    case NOT_COMPILED_IN :
        return "Feature not compiled in";

    case UNICODE_SIZE_E :
        return "Unicode password too big";

    case NO_PASSWORD :
        return "No password provided by user";

    case ALT_NAME_E :
        return "Alt Name problem, too big";

    case AES_GCM_AUTH_E:
        return "AES-GCM Authentication check fail";

    case AES_CCM_AUTH_E:
        return "AES-CCM Authentication check fail";

    case CAVIUM_INIT_E:
        return "Cavium Init type error";

    case COMPRESS_INIT_E:
        return "Compress Init error";

    case COMPRESS_E:
        return "Compress error";

    case DECOMPRESS_INIT_E:
        return "DeCompress Init error";

    case DECOMPRESS_E:
        return "DeCompress error";

    case BAD_ALIGN_E:
        return "Bad alignment error, no alloc help";

    case ASN_NO_SIGNER_E :
        return "ASN no signer error to confirm failure";

    case ASN_CRL_CONFIRM_E :
        return "ASN CRL sig error, confirm failure";

    case ASN_CRL_NO_SIGNER_E :
        return "ASN CRL no signer error to confirm failure";

    case ASN_OCSP_CONFIRM_E :
        return "ASN OCSP sig error, confirm failure";

    case BAD_ENC_STATE_E:
        return "Bad ecc encrypt state operation";

    case BAD_PADDING_E:
        return "Bad padding, message wrong length";

    case REQ_ATTRIBUTE_E:
        return "Setting cert request attributes error";

    case PKCS7_OID_E:
        return "PKCS#7 error: mismatched OID value";

    case PKCS7_RECIP_E:
        return "PKCS#7 error: no matching recipient found";

    case FIPS_NOT_ALLOWED_E:
        return "FIPS mode not allowed error";

    case ASN_NAME_INVALID_E:
        return "Name Constraint error";

    case RNG_FAILURE_E:
        return "Random Number Generator failed";

    case HMAC_MIN_KEYLEN_E:
        return "FIPS Mode HMAC Minimum Key Length error";

    default:
        return "unknown error number";

    }

#endif /* NO_ERROR_STRINGS */

}

void CTaoCryptErrorString(int error, char* buffer)
{
    XSTRNCPY(buffer, CTaoCryptGetErrorString(error), CYASSL_MAX_ERROR_SZ);
}
