/*
 * FreeRTOS Error Code Stringification utilies for mbed TLS v2.16.0
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
 * @file mbedtls_error.c
 * @brief This files defines the stringification utilities for mbed TLS high-level and low-level codes.
 */

#include "mbedtls_error.h"

#if !defined( MBEDTLS_CONFIG_FILE )
    #include "mbedtls/config.h"
#else
    #include MBEDTLS_CONFIG_FILE
#endif

#if defined( MBEDTLS_AES_C )
    #include "mbedtls/aes.h"
#endif

#if defined( MBEDTLS_ARC4_C )
    #include "mbedtls/arc4.h"
#endif

#if defined( MBEDTLS_ARIA_C )
    #include "mbedtls/aria.h"
#endif

#if defined( MBEDTLS_BASE64_C )
    #include "mbedtls/base64.h"
#endif

#if defined( MBEDTLS_BIGNUM_C )
    #include "mbedtls/bignum.h"
#endif

#if defined( MBEDTLS_BLOWFISH_C )
    #include "mbedtls/blowfish.h"
#endif

#if defined( MBEDTLS_CAMELLIA_C )
    #include "mbedtls/camellia.h"
#endif

#if defined( MBEDTLS_CCM_C )
    #include "mbedtls/ccm.h"
#endif

#if defined( MBEDTLS_CHACHA20_C )
    #include "mbedtls/chacha20.h"
#endif

#if defined( MBEDTLS_CHACHAPOLY_C )
    #include "mbedtls/chachapoly.h"
#endif

#if defined( MBEDTLS_CIPHER_C )
    #include "mbedtls/cipher.h"
#endif

#if defined( MBEDTLS_CMAC_C )
    #include "mbedtls/cmac.h"
#endif

#if defined( MBEDTLS_CTR_DRBG_C )
    #include "mbedtls/ctr_drbg.h"
#endif

#if defined( MBEDTLS_DES_C )
    #include "mbedtls/des.h"
#endif

#if defined( MBEDTLS_DHM_C )
    #include "mbedtls/dhm.h"
#endif

#if defined( MBEDTLS_ECP_C )
    #include "mbedtls/ecp.h"
#endif

#if defined( MBEDTLS_ENTROPY_C )
    #include "mbedtls/entropy.h"
#endif

#if defined( MBEDTLS_GCM_C )
    #include "mbedtls/gcm.h"
#endif

#if defined( MBEDTLS_HKDF_C )
    #include "mbedtls/hkdf.h"
#endif

#if defined( MBEDTLS_HMAC_DRBG_C )
    #include "mbedtls/hmac_drbg.h"
#endif

#if defined( MBEDTLS_MD_C )
    #include "mbedtls/md.h"
#endif

#if defined( MBEDTLS_MD2_C )
    #include "mbedtls/md2.h"
#endif

#if defined( MBEDTLS_MD4_C )
    #include "mbedtls/md4.h"
#endif

#if defined( MBEDTLS_MD5_C )
    #include "mbedtls/md5.h"
#endif

#if defined( MBEDTLS_NET_C )
    #include "mbedtls/net_sockets.h"
#endif

#if defined( MBEDTLS_OID_C )
    #include "mbedtls/oid.h"
#endif

#if defined( MBEDTLS_PADLOCK_C )
    #include "mbedtls/padlock.h"
#endif

#if defined( MBEDTLS_PEM_PARSE_C ) || defined( MBEDTLS_PEM_WRITE_C )
    #include "mbedtls/pem.h"
#endif

#if defined( MBEDTLS_PK_C )
    #include "mbedtls/pk.h"
#endif

#if defined( MBEDTLS_PKCS12_C )
    #include "mbedtls/pkcs12.h"
#endif

#if defined( MBEDTLS_PKCS5_C )
    #include "mbedtls/pkcs5.h"
#endif

#if defined( MBEDTLS_PLATFORM_C )
    #include "mbedtls/platform.h"
#endif

#if defined( MBEDTLS_POLY1305_C )
    #include "mbedtls/poly1305.h"
#endif

#if defined( MBEDTLS_RIPEMD160_C )
    #include "mbedtls/ripemd160.h"
#endif

#if defined( MBEDTLS_RSA_C )
    #include "mbedtls/rsa.h"
#endif

#if defined( MBEDTLS_SHA1_C )
    #include "mbedtls/sha1.h"
#endif

#if defined( MBEDTLS_SHA256_C )
    #include "mbedtls/sha256.h"
#endif

#if defined( MBEDTLS_SHA512_C )
    #include "mbedtls/sha512.h"
#endif

#if defined( MBEDTLS_SSL_TLS_C )
    #include "mbedtls/ssl.h"
#endif

#if defined( MBEDTLS_THREADING_C )
    #include "mbedtls/threading.h"
#endif

#if defined( MBEDTLS_X509_USE_C ) || defined( MBEDTLS_X509_CREATE_C )
    #include "mbedtls/x509.h"
#endif

#if defined( MBEDTLS_XTEA_C )
    #include "mbedtls/xtea.h"
#endif


const char * mbedtls_strerror_highlevel( int errnum )
{
    const char * rc = NULL;
    int use_ret;

    if( errnum < 0 )
    {
        errnum = -errnum;
    }

    if( errnum & 0xFF80 )
    {
        use_ret = errnum & 0xFF80;

        /* High level error codes */
        switch( use_ret )
        {
            #if defined( MBEDTLS_CIPHER_C )
                case -( MBEDTLS_ERR_CIPHER_FEATURE_UNAVAILABLE ):
                    rc = "CIPHER - The selected feature is not available";
                    break;

                case -( MBEDTLS_ERR_CIPHER_BAD_INPUT_DATA ):
                    rc = "CIPHER - Bad input parameters";
                    break;

                case -( MBEDTLS_ERR_CIPHER_ALLOC_FAILED ):
                    rc = "CIPHER - Failed to allocate memory";
                    break;

                case -( MBEDTLS_ERR_CIPHER_INVALID_PADDING ):
                    rc = "CIPHER - Input data contains invalid padding and is rejected";
                    break;

                case -( MBEDTLS_ERR_CIPHER_FULL_BLOCK_EXPECTED ):
                    rc = "CIPHER - Decryption of block requires a full block";
                    break;

                case -( MBEDTLS_ERR_CIPHER_AUTH_FAILED ):
                    rc = "CIPHER - Authentication failed (for AEAD modes)";
                    break;

                case -( MBEDTLS_ERR_CIPHER_INVALID_CONTEXT ):
                    rc = "CIPHER - The context is invalid. For example, because it was freed";
                    break;

                case -( MBEDTLS_ERR_CIPHER_HW_ACCEL_FAILED ):
                    rc = "CIPHER - Cipher hardware accelerator failed";
                    break;
            #endif /* MBEDTLS_CIPHER_C */

            #if defined( MBEDTLS_DHM_C )
                case -( MBEDTLS_ERR_DHM_BAD_INPUT_DATA ):
                    rc = "DHM - Bad input parameters";
                    break;

                case -( MBEDTLS_ERR_DHM_READ_PARAMS_FAILED ):
                    rc = "DHM - Reading of the DHM parameters failed";
                    break;

                case -( MBEDTLS_ERR_DHM_MAKE_PARAMS_FAILED ):
                    rc = "DHM - Making of the DHM parameters failed";
                    break;

                case -( MBEDTLS_ERR_DHM_READ_PUBLIC_FAILED ):
                    rc = "DHM - Reading of the public values failed";
                    break;

                case -( MBEDTLS_ERR_DHM_MAKE_PUBLIC_FAILED ):
                    rc = "DHM - Making of the public value failed";
                    break;

                case -( MBEDTLS_ERR_DHM_CALC_SECRET_FAILED ):
                    rc = "DHM - Calculation of the DHM secret failed";
                    break;

                case -( MBEDTLS_ERR_DHM_INVALID_FORMAT ):
                    rc = "DHM - The ASN.1 data is not formatted correctly";
                    break;

                case -( MBEDTLS_ERR_DHM_ALLOC_FAILED ):
                    rc = "DHM - Allocation of memory failed";
                    break;

                case -( MBEDTLS_ERR_DHM_FILE_IO_ERROR ):
                    rc = "DHM - Read or write of file failed";
                    break;

                case -( MBEDTLS_ERR_DHM_HW_ACCEL_FAILED ):
                    rc = "DHM - DHM hardware accelerator failed";
                    break;

                case -( MBEDTLS_ERR_DHM_SET_GROUP_FAILED ):
                    rc = "DHM - Setting the modulus and generator failed";
                    break;
            #endif /* MBEDTLS_DHM_C */

            #if defined( MBEDTLS_ECP_C )
                case -( MBEDTLS_ERR_ECP_BAD_INPUT_DATA ):
                    rc = "ECP - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_ECP_BUFFER_TOO_SMALL ):
                    rc = "ECP - The buffer is too small to write to";
                    break;

                case -( MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE ):
                    rc = "ECP - The requested feature is not available, for example, the requested curve is not supported";
                    break;

                case -( MBEDTLS_ERR_ECP_VERIFY_FAILED ):
                    rc = "ECP - The signature is not valid";
                    break;

                case -( MBEDTLS_ERR_ECP_ALLOC_FAILED ):
                    rc = "ECP - Memory allocation failed";
                    break;

                case -( MBEDTLS_ERR_ECP_RANDOM_FAILED ):
                    rc = "ECP - Generation of random value, such as ephemeral key, failed";
                    break;

                case -( MBEDTLS_ERR_ECP_INVALID_KEY ):
                    rc = "ECP - Invalid private or public key";
                    break;

                case -( MBEDTLS_ERR_ECP_SIG_LEN_MISMATCH ):
                    rc = "ECP - The buffer contains a valid signature followed by more data";
                    break;

                case -( MBEDTLS_ERR_ECP_HW_ACCEL_FAILED ):
                    rc = "ECP - The ECP hardware accelerator failed";
                    break;

                case -( MBEDTLS_ERR_ECP_IN_PROGRESS ):
                    rc = "ECP - Operation in progress, call again with the same parameters to continue";
                    break;
            #endif /* MBEDTLS_ECP_C */

            #if defined( MBEDTLS_MD_C )
                case -( MBEDTLS_ERR_MD_FEATURE_UNAVAILABLE ):
                    rc = "MD - The selected feature is not available";
                    break;

                case -( MBEDTLS_ERR_MD_BAD_INPUT_DATA ):
                    rc = "MD - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_MD_ALLOC_FAILED ):
                    rc = "MD - Failed to allocate memory";
                    break;

                case -( MBEDTLS_ERR_MD_FILE_IO_ERROR ):
                    rc = "MD - Opening or reading of file failed";
                    break;

                case -( MBEDTLS_ERR_MD_HW_ACCEL_FAILED ):
                    rc = "MD - MD hardware accelerator failed";
                    break;
            #endif /* MBEDTLS_MD_C */

            #if defined( MBEDTLS_PEM_PARSE_C ) || defined( MBEDTLS_PEM_WRITE_C )
                case -( MBEDTLS_ERR_PEM_NO_HEADER_FOOTER_PRESENT ):
                    rc = "PEM - No PEM header or footer found";
                    break;

                case -( MBEDTLS_ERR_PEM_INVALID_DATA ):
                    rc = "PEM - PEM string is not as expected";
                    break;

                case -( MBEDTLS_ERR_PEM_ALLOC_FAILED ):
                    rc = "PEM - Failed to allocate memory";
                    break;

                case -( MBEDTLS_ERR_PEM_INVALID_ENC_IV ):
                    rc = "PEM - RSA IV is not in hex-format";
                    break;

                case -( MBEDTLS_ERR_PEM_UNKNOWN_ENC_ALG ):
                    rc = "PEM - Unsupported key encryption algorithm";
                    break;

                case -( MBEDTLS_ERR_PEM_PASSWORD_REQUIRED ):
                    rc = "PEM - Private key password can't be empty";
                    break;

                case -( MBEDTLS_ERR_PEM_PASSWORD_MISMATCH ):
                    rc = "PEM - Given private key password does not allow for correct decryption";
                    break;

                case -( MBEDTLS_ERR_PEM_FEATURE_UNAVAILABLE ):
                    rc = "PEM - Unavailable feature, e.g. hashing/encryption combination";
                    break;

                case -( MBEDTLS_ERR_PEM_BAD_INPUT_DATA ):
                    rc = "PEM - Bad input parameters to function";
                    break;
            #endif /* MBEDTLS_PEM_PARSE_C || MBEDTLS_PEM_WRITE_C */

            #if defined( MBEDTLS_PK_C )
                case -( MBEDTLS_ERR_PK_ALLOC_FAILED ):
                    rc = "PK - Memory allocation failed";
                    break;

                case -( MBEDTLS_ERR_PK_TYPE_MISMATCH ):
                    rc = "PK - Type mismatch, eg attempt to encrypt with an ECDSA key";
                    break;

                case -( MBEDTLS_ERR_PK_BAD_INPUT_DATA ):
                    rc = "PK - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_PK_FILE_IO_ERROR ):
                    rc = "PK - Read/write of file failed";
                    break;

                case -( MBEDTLS_ERR_PK_KEY_INVALID_VERSION ):
                    rc = "PK - Unsupported key version";
                    break;

                case -( MBEDTLS_ERR_PK_KEY_INVALID_FORMAT ):
                    rc = "PK - Invalid key tag or value";
                    break;

                case -( MBEDTLS_ERR_PK_UNKNOWN_PK_ALG ):
                    rc = "PK - Key algorithm is unsupported (only RSA and EC are supported)";
                    break;

                case -( MBEDTLS_ERR_PK_PASSWORD_REQUIRED ):
                    rc = "PK - Private key password can't be empty";
                    break;

                case -( MBEDTLS_ERR_PK_PASSWORD_MISMATCH ):
                    rc = "PK - Given private key password does not allow for correct decryption";
                    break;

                case -( MBEDTLS_ERR_PK_INVALID_PUBKEY ):
                    rc = "PK - The pubkey tag or value is invalid (only RSA and EC are supported)";
                    break;

                case -( MBEDTLS_ERR_PK_INVALID_ALG ):
                    rc = "PK - The algorithm tag or value is invalid";
                    break;

                case -( MBEDTLS_ERR_PK_UNKNOWN_NAMED_CURVE ):
                    rc = "PK - Elliptic curve is unsupported (only NIST curves are supported)";
                    break;

                case -( MBEDTLS_ERR_PK_FEATURE_UNAVAILABLE ):
                    rc = "PK - Unavailable feature, e.g. RSA disabled for RSA key";
                    break;

                case -( MBEDTLS_ERR_PK_SIG_LEN_MISMATCH ):
                    rc = "PK - The buffer contains a valid signature followed by more data";
                    break;

                case -( MBEDTLS_ERR_PK_HW_ACCEL_FAILED ):
                    rc = "PK - PK hardware accelerator failed";
                    break;
            #endif /* MBEDTLS_PK_C */

            #if defined( MBEDTLS_PKCS12_C )
                case -( MBEDTLS_ERR_PKCS12_BAD_INPUT_DATA ):
                    rc = "PKCS12 - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_PKCS12_FEATURE_UNAVAILABLE ):
                    rc = "PKCS12 - Feature not available, e.g. unsupported encryption scheme";
                    break;

                case -( MBEDTLS_ERR_PKCS12_PBE_INVALID_FORMAT ):
                    rc = "PKCS12 - PBE ASN.1 data not as expected";
                    break;

                case -( MBEDTLS_ERR_PKCS12_PASSWORD_MISMATCH ):
                    rc = "PKCS12 - Given private key password does not allow for correct decryption";
                    break;
            #endif /* MBEDTLS_PKCS12_C */

            #if defined( MBEDTLS_PKCS5_C )
                case -( MBEDTLS_ERR_PKCS5_BAD_INPUT_DATA ):
                    rc = "PKCS5 - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_PKCS5_INVALID_FORMAT ):
                    rc = "PKCS5 - Unexpected ASN.1 data";
                    break;

                case -( MBEDTLS_ERR_PKCS5_FEATURE_UNAVAILABLE ):
                    rc = "PKCS5 - Requested encryption or digest alg not available";
                    break;

                case -( MBEDTLS_ERR_PKCS5_PASSWORD_MISMATCH ):
                    rc = "PKCS5 - Given private key password does not allow for correct decryption";
                    break;
            #endif /* MBEDTLS_PKCS5_C */

            #if defined( MBEDTLS_RSA_C )
                case -( MBEDTLS_ERR_RSA_BAD_INPUT_DATA ):
                    rc = "RSA - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_RSA_INVALID_PADDING ):
                    rc = "RSA - Input data contains invalid padding and is rejected";
                    break;

                case -( MBEDTLS_ERR_RSA_KEY_GEN_FAILED ):
                    rc = "RSA - Something failed during generation of a key";
                    break;

                case -( MBEDTLS_ERR_RSA_KEY_CHECK_FAILED ):
                    rc = "RSA - Key failed to pass the validity check of the library";
                    break;

                case -( MBEDTLS_ERR_RSA_PUBLIC_FAILED ):
                    rc = "RSA - The public key operation failed";
                    break;

                case -( MBEDTLS_ERR_RSA_PRIVATE_FAILED ):
                    rc = "RSA - The private key operation failed";
                    break;

                case -( MBEDTLS_ERR_RSA_VERIFY_FAILED ):
                    rc = "RSA - The PKCS#1 verification failed";
                    break;

                case -( MBEDTLS_ERR_RSA_OUTPUT_TOO_LARGE ):
                    rc = "RSA - The output buffer for decryption is not large enough";
                    break;

                case -( MBEDTLS_ERR_RSA_RNG_FAILED ):
                    rc = "RSA - The random generator failed to generate non-zeros";
                    break;

                case -( MBEDTLS_ERR_RSA_UNSUPPORTED_OPERATION ):
                    rc = "RSA - The implementation does not offer the requested operation, for example, because of security violations or lack of functionality";
                    break;

                case -( MBEDTLS_ERR_RSA_HW_ACCEL_FAILED ):
                    rc = "RSA - RSA hardware accelerator failed";
                    break;
            #endif /* MBEDTLS_RSA_C */

            #if defined( MBEDTLS_SSL_TLS_C )
                case -( MBEDTLS_ERR_SSL_FEATURE_UNAVAILABLE ):
                    rc = "SSL - The requested feature is not available";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_INPUT_DATA ):
                    rc = "SSL - Bad input parameters to function";
                    break;

                case -( MBEDTLS_ERR_SSL_INVALID_MAC ):
                    rc = "SSL - Verification of the message MAC failed";
                    break;

                case -( MBEDTLS_ERR_SSL_INVALID_RECORD ):
                    rc = "SSL - An invalid SSL record was received";
                    break;

                case -( MBEDTLS_ERR_SSL_CONN_EOF ):
                    rc = "SSL - The connection indicated an EOF";
                    break;

                case -( MBEDTLS_ERR_SSL_UNKNOWN_CIPHER ):
                    rc = "SSL - An unknown cipher was received";
                    break;

                case -( MBEDTLS_ERR_SSL_NO_CIPHER_CHOSEN ):
                    rc = "SSL - The server has no ciphersuites in common with the client";
                    break;

                case -( MBEDTLS_ERR_SSL_NO_RNG ):
                    rc = "SSL - No RNG was provided to the SSL module";
                    break;

                case -( MBEDTLS_ERR_SSL_NO_CLIENT_CERTIFICATE ):
                    rc = "SSL - No client certification received from the client, but required by the authentication mode";
                    break;

                case -( MBEDTLS_ERR_SSL_CERTIFICATE_TOO_LARGE ):
                    rc = "SSL - Our own certificate(s) is/are too large to send in an SSL message";
                    break;

                case -( MBEDTLS_ERR_SSL_CERTIFICATE_REQUIRED ):
                    rc = "SSL - The own certificate is not set, but needed by the server";
                    break;

                case -( MBEDTLS_ERR_SSL_PRIVATE_KEY_REQUIRED ):
                    rc = "SSL - The own private key or pre-shared key is not set, but needed";
                    break;

                case -( MBEDTLS_ERR_SSL_CA_CHAIN_REQUIRED ):
                    rc = "SSL - No CA Chain is set, but required to operate";
                    break;

                case -( MBEDTLS_ERR_SSL_UNEXPECTED_MESSAGE ):
                    rc = "SSL - An unexpected message was received from our peer";
                    break;

                case -( MBEDTLS_ERR_SSL_FATAL_ALERT_MESSAGE ):
                    rc = "SSL - A fatal alert message was received from our peer";
                    break;

                case -( MBEDTLS_ERR_SSL_PEER_VERIFY_FAILED ):
                    rc = "SSL - Verification of our peer failed";
                    break;

                case -( MBEDTLS_ERR_SSL_PEER_CLOSE_NOTIFY ):
                    rc = "SSL - The peer notified us that the connection is going to be closed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CLIENT_HELLO ):
                    rc = "SSL - Processing of the ClientHello handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_SERVER_HELLO ):
                    rc = "SSL - Processing of the ServerHello handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CERTIFICATE ):
                    rc = "SSL - Processing of the Certificate handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CERTIFICATE_REQUEST ):
                    rc = "SSL - Processing of the CertificateRequest handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_SERVER_KEY_EXCHANGE ):
                    rc = "SSL - Processing of the ServerKeyExchange handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_SERVER_HELLO_DONE ):
                    rc = "SSL - Processing of the ServerHelloDone handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CLIENT_KEY_EXCHANGE ):
                    rc = "SSL - Processing of the ClientKeyExchange handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CLIENT_KEY_EXCHANGE_RP ):
                    rc = "SSL - Processing of the ClientKeyExchange handshake message failed in DHM / ECDH Read Public";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CLIENT_KEY_EXCHANGE_CS ):
                    rc = "SSL - Processing of the ClientKeyExchange handshake message failed in DHM / ECDH Calculate Secret";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CERTIFICATE_VERIFY ):
                    rc = "SSL - Processing of the CertificateVerify handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_CHANGE_CIPHER_SPEC ):
                    rc = "SSL - Processing of the ChangeCipherSpec handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_FINISHED ):
                    rc = "SSL - Processing of the Finished handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_ALLOC_FAILED ):
                    rc = "SSL - Memory allocation failed";
                    break;

                case -( MBEDTLS_ERR_SSL_HW_ACCEL_FAILED ):
                    rc = "SSL - Hardware acceleration function returned with error";
                    break;

                case -( MBEDTLS_ERR_SSL_HW_ACCEL_FALLTHROUGH ):
                    rc = "SSL - Hardware acceleration function skipped / left alone data";
                    break;

                case -( MBEDTLS_ERR_SSL_COMPRESSION_FAILED ):
                    rc = "SSL - Processing of the compression / decompression failed";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_PROTOCOL_VERSION ):
                    rc = "SSL - Handshake protocol not within min/max boundaries";
                    break;

                case -( MBEDTLS_ERR_SSL_BAD_HS_NEW_SESSION_TICKET ):
                    rc = "SSL - Processing of the NewSessionTicket handshake message failed";
                    break;

                case -( MBEDTLS_ERR_SSL_SESSION_TICKET_EXPIRED ):
                    rc = "SSL - Session ticket has expired";
                    break;

                case -( MBEDTLS_ERR_SSL_PK_TYPE_MISMATCH ):
                    rc = "SSL - Public key type mismatch (eg, asked for RSA key exchange and presented EC key)";
                    break;

                case -( MBEDTLS_ERR_SSL_UNKNOWN_IDENTITY ):
                    rc = "SSL - Unknown identity received (eg, PSK identity)";
                    break;

                case -( MBEDTLS_ERR_SSL_INTERNAL_ERROR ):
                    rc = "SSL - Internal error (eg, unexpected failure in lower-level module)";
                    break;

                case -( MBEDTLS_ERR_SSL_COUNTER_WRAPPING ):
                    rc = "SSL - A counter would wrap (eg, too many messages exchanged)";
                    break;

                case -( MBEDTLS_ERR_SSL_WAITING_SERVER_HELLO_RENEGO ):
                    rc = "SSL - Unexpected message at ServerHello in renegotiation";
                    break;

                case -( MBEDTLS_ERR_SSL_HELLO_VERIFY_REQUIRED ):
                    rc = "SSL - DTLS client must retry for hello verification";
                    break;

                case -( MBEDTLS_ERR_SSL_BUFFER_TOO_SMALL ):
                    rc = "SSL - A buffer is too small to receive or write a message";
                    break;

                case -( MBEDTLS_ERR_SSL_NO_USABLE_CIPHERSUITE ):
                    rc = "SSL - None of the common ciphersuites is usable (eg, no suitable certificate, see debug messages)";
                    break;

                case -( MBEDTLS_ERR_SSL_WANT_READ ):
                    rc = "SSL - No data of requested type currently available on underlying transport";
                    break;

                case -( MBEDTLS_ERR_SSL_WANT_WRITE ):
                    rc = "SSL - Connection requires a write call";
                    break;

                case -( MBEDTLS_ERR_SSL_TIMEOUT ):
                    rc = "SSL - The operation timed out";
                    break;

                case -( MBEDTLS_ERR_SSL_CLIENT_RECONNECT ):
                    rc = "SSL - The client initiated a reconnect from the same port";
                    break;

                case -( MBEDTLS_ERR_SSL_UNEXPECTED_RECORD ):
                    rc = "SSL - Record header looks valid but is not expected";
                    break;

                case -( MBEDTLS_ERR_SSL_NON_FATAL ):
                    rc = "SSL - The alert message received indicates a non-fatal error";
                    break;

                case -( MBEDTLS_ERR_SSL_INVALID_VERIFY_HASH ):
                    rc = "SSL - Couldn't set the hash for verifying CertificateVerify";
                    break;

                case -( MBEDTLS_ERR_SSL_CONTINUE_PROCESSING ):
                    rc = "SSL - Internal-only message signaling that further message-processing should be done";
                    break;

                case -( MBEDTLS_ERR_SSL_ASYNC_IN_PROGRESS ):
                    rc = "SSL - The asynchronous operation is not completed yet";
                    break;

                case -( MBEDTLS_ERR_SSL_EARLY_MESSAGE ):
                    rc = "SSL - Internal-only message signaling that a message arrived early";
                    break;

                case -( MBEDTLS_ERR_SSL_CRYPTO_IN_PROGRESS ):
                    rc = "SSL - A cryptographic operation is in progress. Try again later";
                    break;
            #endif /* MBEDTLS_SSL_TLS_C */

            #if defined( MBEDTLS_X509_USE_C ) || defined( MBEDTLS_X509_CREATE_C )
                case -( MBEDTLS_ERR_X509_FEATURE_UNAVAILABLE ):
                    rc = "X509 - Unavailable feature, e.g. RSA hashing/encryption combination";
                    break;

                case -( MBEDTLS_ERR_X509_UNKNOWN_OID ):
                    rc = "X509 - Requested OID is unknown";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_FORMAT ):
                    rc = "X509 - The CRT/CRL/CSR format is invalid, e.g. different type expected";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_VERSION ):
                    rc = "X509 - The CRT/CRL/CSR version element is invalid";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_SERIAL ):
                    rc = "X509 - The serial tag or value is invalid";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_ALG ):
                    rc = "X509 - The algorithm tag or value is invalid";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_NAME ):
                    rc = "X509 - The name tag or value is invalid";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_DATE ):
                    rc = "X509 - The date tag or value is invalid";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_SIGNATURE ):
                    rc = "X509 - The signature tag or value invalid";
                    break;

                case -( MBEDTLS_ERR_X509_INVALID_EXTENSIONS ):
                    rc = "X509 - The extension tag or value is invalid";
                    break;

                case -( MBEDTLS_ERR_X509_UNKNOWN_VERSION ):
                    rc = "X509 - CRT/CRL/CSR has an unsupported version number";
                    break;

                case -( MBEDTLS_ERR_X509_UNKNOWN_SIG_ALG ):
                    rc = "X509 - Signature algorithm (oid) is unsupported";
                    break;

                case -( MBEDTLS_ERR_X509_SIG_MISMATCH ):
                    rc = "X509 - Signature algorithms do not match. (see \\c ::mbedtls_x509_crt sig_oid)";
                    break;

                case -( MBEDTLS_ERR_X509_CERT_VERIFY_FAILED ):
                    rc = "X509 - Certificate verification failed, e.g. CRL, CA or signature check failed";
                    break;

                case -( MBEDTLS_ERR_X509_CERT_UNKNOWN_FORMAT ):
                    rc = "X509 - Format not recognized as DER or PEM";
                    break;

                case -( MBEDTLS_ERR_X509_BAD_INPUT_DATA ):
                    rc = "X509 - Input invalid";
                    break;

                case -( MBEDTLS_ERR_X509_ALLOC_FAILED ):
                    rc = "X509 - Allocation of memory failed";
                    break;

                case -( MBEDTLS_ERR_X509_FILE_IO_ERROR ):
                    rc = "X509 - Read/write of file failed";
                    break;

                case -( MBEDTLS_ERR_X509_BUFFER_TOO_SMALL ):
                    rc = "X509 - Destination buffer is too small";
                    break;

                case -( MBEDTLS_ERR_X509_FATAL_ERROR ):
                    rc = "X509 - A fatal error occured, eg the chain is too long or the vrfy callback failed";
                    break;
            #endif /* MBEDTLS_X509_USE_C || MBEDTLS_X509_CREATE_C */
            /* END generated code */
        }
    }

    return rc;
}

const char * mbedtls_strerror_lowlevel( int errnum )
{
    const char * rc = NULL;
    int use_ret;

    if( errnum < 0 )
    {
        errnum = -errnum;
    }

    use_ret = errnum & ~0xFF80;

    if( use_ret == 0 )
    {
        return NULL;
    }

    /* Low level error codes */
    /* */
    switch( use_ret )
    {
        #if defined( MBEDTLS_AES_C )
            case -( MBEDTLS_ERR_AES_INVALID_KEY_LENGTH ):
                rc = "AES - Invalid key length";
                break;

            case -( MBEDTLS_ERR_AES_INVALID_INPUT_LENGTH ):
                rc = "AES - Invalid data input length";
                break;

            case -( MBEDTLS_ERR_AES_BAD_INPUT_DATA ):
                rc = "AES - Invalid input data";
                break;

            case -( MBEDTLS_ERR_AES_FEATURE_UNAVAILABLE ):
                rc = "AES - Feature not available. For example, an unsupported AES key size";
                break;

            case -( MBEDTLS_ERR_AES_HW_ACCEL_FAILED ):
                rc = "AES - AES hardware accelerator failed";
                break;
        #endif /* MBEDTLS_AES_C */

        #if defined( MBEDTLS_ARC4_C )
            case -( MBEDTLS_ERR_ARC4_HW_ACCEL_FAILED ):
                rc = "ARC4 - ARC4 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_ARC4_C */

        #if defined( MBEDTLS_ARIA_C )
            case -( MBEDTLS_ERR_ARIA_BAD_INPUT_DATA ):
                rc = "ARIA - Bad input data";
                break;

            case -( MBEDTLS_ERR_ARIA_INVALID_INPUT_LENGTH ):
                rc = "ARIA - Invalid data input length";
                break;

            case -( MBEDTLS_ERR_ARIA_FEATURE_UNAVAILABLE ):
                rc = "ARIA - Feature not available. For example, an unsupported ARIA key size";
                break;

            case -( MBEDTLS_ERR_ARIA_HW_ACCEL_FAILED ):
                rc = "ARIA - ARIA hardware accelerator failed";
                break;
        #endif /* MBEDTLS_ARIA_C */

        #if defined( MBEDTLS_ASN1_PARSE_C )
            case -( MBEDTLS_ERR_ASN1_OUT_OF_DATA ):
                rc = "ASN1 - Out of data when parsing an ASN1 data structure";
                break;

            case -( MBEDTLS_ERR_ASN1_UNEXPECTED_TAG ):
                rc = "ASN1 - ASN1 tag was of an unexpected value";
                break;

            case -( MBEDTLS_ERR_ASN1_INVALID_LENGTH ):
                rc = "ASN1 - Error when trying to determine the length or invalid length";
                break;

            case -( MBEDTLS_ERR_ASN1_LENGTH_MISMATCH ):
                rc = "ASN1 - Actual length differs from expected length";
                break;

            case -( MBEDTLS_ERR_ASN1_INVALID_DATA ):
                rc = "ASN1 - Data is invalid. (not used)";
                break;

            case -( MBEDTLS_ERR_ASN1_ALLOC_FAILED ):
                rc = "ASN1 - Memory allocation failed";
                break;

            case -( MBEDTLS_ERR_ASN1_BUF_TOO_SMALL ):
                rc = "ASN1 - Buffer too small when writing ASN.1 data structure";
                break;
        #endif /* MBEDTLS_ASN1_PARSE_C */

        #if defined( MBEDTLS_BASE64_C )
            case -( MBEDTLS_ERR_BASE64_BUFFER_TOO_SMALL ):
                rc = "BASE64 - Output buffer too small";
                break;

            case -( MBEDTLS_ERR_BASE64_INVALID_CHARACTER ):
                rc = "BASE64 - Invalid character in input";
                break;
        #endif /* MBEDTLS_BASE64_C */

        #if defined( MBEDTLS_BIGNUM_C )
            case -( MBEDTLS_ERR_MPI_FILE_IO_ERROR ):
                rc = "BIGNUM - An error occurred while reading from or writing to a file";
                break;

            case -( MBEDTLS_ERR_MPI_BAD_INPUT_DATA ):
                rc = "BIGNUM - Bad input parameters to function";
                break;

            case -( MBEDTLS_ERR_MPI_INVALID_CHARACTER ):
                rc = "BIGNUM - There is an invalid character in the digit string";
                break;

            case -( MBEDTLS_ERR_MPI_BUFFER_TOO_SMALL ):
                rc = "BIGNUM - The buffer is too small to write to";
                break;

            case -( MBEDTLS_ERR_MPI_NEGATIVE_VALUE ):
                rc = "BIGNUM - The input arguments are negative or result in illegal output";
                break;

            case -( MBEDTLS_ERR_MPI_DIVISION_BY_ZERO ):
                rc = "BIGNUM - The input argument for division is zero, which is not allowed";
                break;

            case -( MBEDTLS_ERR_MPI_NOT_ACCEPTABLE ):
                rc = "BIGNUM - The input arguments are not acceptable";
                break;

            case -( MBEDTLS_ERR_MPI_ALLOC_FAILED ):
                rc = "BIGNUM - Memory allocation failed";
                break;
        #endif /* MBEDTLS_BIGNUM_C */

        #if defined( MBEDTLS_BLOWFISH_C )
            case -( MBEDTLS_ERR_BLOWFISH_BAD_INPUT_DATA ):
                rc = "BLOWFISH - Bad input data";
                break;

            case -( MBEDTLS_ERR_BLOWFISH_INVALID_INPUT_LENGTH ):
                rc = "BLOWFISH - Invalid data input length";
                break;

            case -( MBEDTLS_ERR_BLOWFISH_HW_ACCEL_FAILED ):
                rc = "BLOWFISH - Blowfish hardware accelerator failed";
                break;
        #endif /* MBEDTLS_BLOWFISH_C */

        #if defined( MBEDTLS_CAMELLIA_C )
            case -( MBEDTLS_ERR_CAMELLIA_BAD_INPUT_DATA ):
                rc = "CAMELLIA - Bad input data";
                break;

            case -( MBEDTLS_ERR_CAMELLIA_INVALID_INPUT_LENGTH ):
                rc = "CAMELLIA - Invalid data input length";
                break;

            case -( MBEDTLS_ERR_CAMELLIA_HW_ACCEL_FAILED ):
                rc = "CAMELLIA - Camellia hardware accelerator failed";
                break;
        #endif /* MBEDTLS_CAMELLIA_C */

        #if defined( MBEDTLS_CCM_C )
            case -( MBEDTLS_ERR_CCM_BAD_INPUT ):
                rc = "CCM - Bad input parameters to the function";
                break;

            case -( MBEDTLS_ERR_CCM_AUTH_FAILED ):
                rc = "CCM - Authenticated decryption failed";
                break;

            case -( MBEDTLS_ERR_CCM_HW_ACCEL_FAILED ):
                rc = "CCM - CCM hardware accelerator failed";
                break;
        #endif /* MBEDTLS_CCM_C */

        #if defined( MBEDTLS_CHACHA20_C )
            case -( MBEDTLS_ERR_CHACHA20_BAD_INPUT_DATA ):
                rc = "CHACHA20 - Invalid input parameter(s)";
                break;

            case -( MBEDTLS_ERR_CHACHA20_FEATURE_UNAVAILABLE ):
                rc = "CHACHA20 - Feature not available. For example, s part of the API is not implemented";
                break;

            case -( MBEDTLS_ERR_CHACHA20_HW_ACCEL_FAILED ):
                rc = "CHACHA20 - Chacha20 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_CHACHA20_C */

        #if defined( MBEDTLS_CHACHAPOLY_C )
            case -( MBEDTLS_ERR_CHACHAPOLY_BAD_STATE ):
                rc = "CHACHAPOLY - The requested operation is not permitted in the current state";
                break;

            case -( MBEDTLS_ERR_CHACHAPOLY_AUTH_FAILED ):
                rc = "CHACHAPOLY - Authenticated decryption failed: data was not authentic";
                break;
        #endif /* MBEDTLS_CHACHAPOLY_C */

        #if defined( MBEDTLS_CMAC_C )
            case -( MBEDTLS_ERR_CMAC_HW_ACCEL_FAILED ):
                rc = "CMAC - CMAC hardware accelerator failed";
                break;
        #endif /* MBEDTLS_CMAC_C */

        #if defined( MBEDTLS_CTR_DRBG_C )
            case -( MBEDTLS_ERR_CTR_DRBG_ENTROPY_SOURCE_FAILED ):
                rc = "CTR_DRBG - The entropy source failed";
                break;

            case -( MBEDTLS_ERR_CTR_DRBG_REQUEST_TOO_BIG ):
                rc = "CTR_DRBG - The requested random buffer length is too big";
                break;

            case -( MBEDTLS_ERR_CTR_DRBG_INPUT_TOO_BIG ):
                rc = "CTR_DRBG - The input (entropy + additional data) is too large";
                break;

            case -( MBEDTLS_ERR_CTR_DRBG_FILE_IO_ERROR ):
                rc = "CTR_DRBG - Read or write error in file";
                break;
        #endif /* MBEDTLS_CTR_DRBG_C */

        #if defined( MBEDTLS_DES_C )
            case -( MBEDTLS_ERR_DES_INVALID_INPUT_LENGTH ):
                rc = "DES - The data input has an invalid length";
                break;

            case -( MBEDTLS_ERR_DES_HW_ACCEL_FAILED ):
                rc = "DES - DES hardware accelerator failed";
                break;
        #endif /* MBEDTLS_DES_C */

        #if defined( MBEDTLS_ENTROPY_C )
            case -( MBEDTLS_ERR_ENTROPY_SOURCE_FAILED ):
                rc = "ENTROPY - Critical entropy source failure";
                break;

            case -( MBEDTLS_ERR_ENTROPY_MAX_SOURCES ):
                rc = "ENTROPY - No more sources can be added";
                break;

            case -( MBEDTLS_ERR_ENTROPY_NO_SOURCES_DEFINED ):
                rc = "ENTROPY - No sources have been added to poll";
                break;

            case -( MBEDTLS_ERR_ENTROPY_NO_STRONG_SOURCE ):
                rc = "ENTROPY - No strong sources have been added to poll";
                break;

            case -( MBEDTLS_ERR_ENTROPY_FILE_IO_ERROR ):
                rc = "ENTROPY - Read/write error in file";
                break;
        #endif /* MBEDTLS_ENTROPY_C */

        #if defined( MBEDTLS_GCM_C )
            case -( MBEDTLS_ERR_GCM_AUTH_FAILED ):
                rc = "GCM - Authenticated decryption failed";
                break;

            case -( MBEDTLS_ERR_GCM_HW_ACCEL_FAILED ):
                rc = "GCM - GCM hardware accelerator failed";
                break;

            case -( MBEDTLS_ERR_GCM_BAD_INPUT ):
                rc = "GCM - Bad input parameters to function";
                break;
        #endif /* MBEDTLS_GCM_C */

        #if defined( MBEDTLS_HKDF_C )
            case -( MBEDTLS_ERR_HKDF_BAD_INPUT_DATA ):
                rc = "HKDF - Bad input parameters to function";
                break;
        #endif /* MBEDTLS_HKDF_C */

        #if defined( MBEDTLS_HMAC_DRBG_C )
            case -( MBEDTLS_ERR_HMAC_DRBG_REQUEST_TOO_BIG ):
                rc = "HMAC_DRBG - Too many random requested in single call";
                break;

            case -( MBEDTLS_ERR_HMAC_DRBG_INPUT_TOO_BIG ):
                rc = "HMAC_DRBG - Input too large (Entropy + additional)";
                break;

            case -( MBEDTLS_ERR_HMAC_DRBG_FILE_IO_ERROR ):
                rc = "HMAC_DRBG - Read/write error in file";
                break;

            case -( MBEDTLS_ERR_HMAC_DRBG_ENTROPY_SOURCE_FAILED ):
                rc = "HMAC_DRBG - The entropy source failed";
                break;
        #endif /* MBEDTLS_HMAC_DRBG_C */

        #if defined( MBEDTLS_MD2_C )
            case -( MBEDTLS_ERR_MD2_HW_ACCEL_FAILED ):
                rc = "MD2 - MD2 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_MD2_C */

        #if defined( MBEDTLS_MD4_C )
            case -( MBEDTLS_ERR_MD4_HW_ACCEL_FAILED ):
                rc = "MD4 - MD4 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_MD4_C */

        #if defined( MBEDTLS_MD5_C )
            case -( MBEDTLS_ERR_MD5_HW_ACCEL_FAILED ):
                rc = "MD5 - MD5 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_MD5_C */

        #if defined( MBEDTLS_NET_C )
            case -( MBEDTLS_ERR_NET_SOCKET_FAILED ):
                rc = "NET - Failed to open a socket";
                break;

            case -( MBEDTLS_ERR_NET_CONNECT_FAILED ):
                rc = "NET - The connection to the given server / port failed";
                break;

            case -( MBEDTLS_ERR_NET_BIND_FAILED ):
                rc = "NET - Binding of the socket failed";
                break;

            case -( MBEDTLS_ERR_NET_LISTEN_FAILED ):
                rc = "NET - Could not listen on the socket";
                break;

            case -( MBEDTLS_ERR_NET_ACCEPT_FAILED ):
                rc = "NET - Could not accept the incoming connection";
                break;

            case -( MBEDTLS_ERR_NET_RECV_FAILED ):
                rc = "NET - Reading information from the socket failed";
                break;

            case -( MBEDTLS_ERR_NET_SEND_FAILED ):
                rc = "NET - Sending information through the socket failed";
                break;

            case -( MBEDTLS_ERR_NET_CONN_RESET ):
                rc = "NET - Connection was reset by peer";
                break;

            case -( MBEDTLS_ERR_NET_UNKNOWN_HOST ):
                rc = "NET - Failed to get an IP address for the given hostname";
                break;

            case -( MBEDTLS_ERR_NET_BUFFER_TOO_SMALL ):
                rc = "NET - Buffer is too small to hold the data";
                break;

            case -( MBEDTLS_ERR_NET_INVALID_CONTEXT ):
                rc = "NET - The context is invalid, eg because it was free()ed";
                break;

            case -( MBEDTLS_ERR_NET_POLL_FAILED ):
                rc = "NET - Polling the net context failed";
                break;

            case -( MBEDTLS_ERR_NET_BAD_INPUT_DATA ):
                rc = "NET - Input invalid";
                break;
        #endif /* MBEDTLS_NET_C */

        #if defined( MBEDTLS_OID_C )
            case -( MBEDTLS_ERR_OID_NOT_FOUND ):
                rc = "OID - OID is not found";
                break;

            case -( MBEDTLS_ERR_OID_BUF_TOO_SMALL ):
                rc = "OID - output buffer is too small";
                break;
        #endif /* MBEDTLS_OID_C */

        #if defined( MBEDTLS_PADLOCK_C )
            case -( MBEDTLS_ERR_PADLOCK_DATA_MISALIGNED ):
                rc = "PADLOCK - Input data should be aligned";
                break;
        #endif /* MBEDTLS_PADLOCK_C */

        #if defined( MBEDTLS_PLATFORM_C )
            case -( MBEDTLS_ERR_PLATFORM_HW_ACCEL_FAILED ):
                rc = "PLATFORM - Hardware accelerator failed";
                break;

            case -( MBEDTLS_ERR_PLATFORM_FEATURE_UNSUPPORTED ):
                rc = "PLATFORM - The requested feature is not supported by the platform";
                break;
        #endif /* MBEDTLS_PLATFORM_C */

        #if defined( MBEDTLS_POLY1305_C )
            case -( MBEDTLS_ERR_POLY1305_BAD_INPUT_DATA ):
                rc = "POLY1305 - Invalid input parameter(s)";
                break;

            case -( MBEDTLS_ERR_POLY1305_FEATURE_UNAVAILABLE ):
                rc = "POLY1305 - Feature not available. For example, s part of the API is not implemented";
                break;

            case -( MBEDTLS_ERR_POLY1305_HW_ACCEL_FAILED ):
                rc = "POLY1305 - Poly1305 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_POLY1305_C */

        #if defined( MBEDTLS_RIPEMD160_C )
            case -( MBEDTLS_ERR_RIPEMD160_HW_ACCEL_FAILED ):
                rc = "RIPEMD160 - RIPEMD160 hardware accelerator failed";
                break;
        #endif /* MBEDTLS_RIPEMD160_C */

        #if defined( MBEDTLS_SHA1_C )
            case -( MBEDTLS_ERR_SHA1_HW_ACCEL_FAILED ):
                rc = "SHA1 - SHA-1 hardware accelerator failed";
                break;

            case -( MBEDTLS_ERR_SHA1_BAD_INPUT_DATA ):
                rc = "SHA1 - SHA-1 input data was malformed";
                break;
        #endif /* MBEDTLS_SHA1_C */

        #if defined( MBEDTLS_SHA256_C )
            case -( MBEDTLS_ERR_SHA256_HW_ACCEL_FAILED ):
                rc = "SHA256 - SHA-256 hardware accelerator failed";
                break;

            case -( MBEDTLS_ERR_SHA256_BAD_INPUT_DATA ):
                rc = "SHA256 - SHA-256 input data was malformed";
                break;
        #endif /* MBEDTLS_SHA256_C */

        #if defined( MBEDTLS_SHA512_C )
            case -( MBEDTLS_ERR_SHA512_HW_ACCEL_FAILED ):
                rc = "SHA512 - SHA-512 hardware accelerator failed";
                break;

            case -( MBEDTLS_ERR_SHA512_BAD_INPUT_DATA ):
                rc = "SHA512 - SHA-512 input data was malformed";
                break;
        #endif /* MBEDTLS_SHA512_C */

        #if defined( MBEDTLS_THREADING_C )
            case -( MBEDTLS_ERR_THREADING_FEATURE_UNAVAILABLE ):
                rc = "THREADING - The selected feature is not available";
                break;

            case -( MBEDTLS_ERR_THREADING_BAD_INPUT_DATA ):
                rc = "THREADING - Bad input parameters to function";
                break;

            case -( MBEDTLS_ERR_THREADING_MUTEX_ERROR ):
                rc = "THREADING - Locking / unlocking / free failed with error code";
                break;
        #endif /* MBEDTLS_THREADING_C */

        #if defined( MBEDTLS_XTEA_C )
            case -( MBEDTLS_ERR_XTEA_INVALID_INPUT_LENGTH ):
                rc = "XTEA - The data input has an invalid length";
                break;

            case -( MBEDTLS_ERR_XTEA_HW_ACCEL_FAILED ):
                rc = "XTEA - XTEA hardware accelerator failed";
                break;
        #endif /* MBEDTLS_XTEA_C */
    }

    return rc;
}
