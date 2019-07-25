/* error-ssl.h
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifndef WOLFSSL_ERROR_H
#define WOLFSSL_ERROR_H

#include <wolfssl/wolfcrypt/error-crypt.h>   /* pull in wolfCrypt errors */

#ifdef __cplusplus
    extern "C" {
#endif

enum wolfSSL_ErrorCodes {
    INPUT_CASE_ERROR        = -301,        /* process input state error */
    PREFIX_ERROR            = -302,        /* bad index to key rounds  */
    MEMORY_ERROR            = -303,        /* out of memory            */
    VERIFY_FINISHED_ERROR   = -304,        /* verify problem on finished */
    VERIFY_MAC_ERROR        = -305,        /* verify mac problem       */
    PARSE_ERROR             = -306,        /* parse error on header    */
    UNKNOWN_HANDSHAKE_TYPE  = -307,        /* weird handshake type     */
    SOCKET_ERROR_E          = -308,        /* error state on socket    */
    SOCKET_NODATA           = -309,        /* expected data, not there */
    INCOMPLETE_DATA         = -310,        /* don't have enough data to
                                              complete task            */
    UNKNOWN_RECORD_TYPE     = -311,        /* unknown type in record hdr */
    DECRYPT_ERROR           = -312,        /* error during decryption  */
    FATAL_ERROR             = -313,        /* recvd alert fatal error  */
    ENCRYPT_ERROR           = -314,        /* error during encryption  */
    FREAD_ERROR             = -315,        /* fread problem            */
    NO_PEER_KEY             = -316,        /* need peer's key          */
    NO_PRIVATE_KEY          = -317,        /* need the private key     */
    RSA_PRIVATE_ERROR       = -318,        /* error during rsa priv op */
    NO_DH_PARAMS            = -319,        /* server missing DH params */
    BUILD_MSG_ERROR         = -320,        /* build message failure    */

    BAD_HELLO               = -321,        /* client hello malformed   */
    DOMAIN_NAME_MISMATCH    = -322,        /* peer subject name mismatch */
    WANT_READ               = -323,        /* want read, call again    */
    NOT_READY_ERROR         = -324,        /* handshake layer not ready */
    PMS_VERSION_ERROR       = -325,        /* pre m secret version error */
    VERSION_ERROR           = -326,        /* record layer version error */
    WANT_WRITE              = -327,        /* want write, call again   */
    BUFFER_ERROR            = -328,        /* malformed buffer input   */
    VERIFY_CERT_ERROR       = -329,        /* verify cert error        */
    VERIFY_SIGN_ERROR       = -330,        /* verify sign error        */
    CLIENT_ID_ERROR         = -331,        /* psk client identity error  */
    SERVER_HINT_ERROR       = -332,        /* psk server hint error  */
    PSK_KEY_ERROR           = -333,        /* psk key error  */
    ZLIB_INIT_ERROR         = -334,        /* zlib init error  */
    ZLIB_COMPRESS_ERROR     = -335,        /* zlib compression error  */
    ZLIB_DECOMPRESS_ERROR   = -336,        /* zlib decompression error  */

    GETTIME_ERROR           = -337,        /* gettimeofday failed ??? */
    GETITIMER_ERROR         = -338,        /* getitimer failed ??? */
    SIGACT_ERROR            = -339,        /* sigaction failed ??? */
    SETITIMER_ERROR         = -340,        /* setitimer failed ??? */
    LENGTH_ERROR            = -341,        /* record layer length error */
    PEER_KEY_ERROR          = -342,        /* can't decode peer key */
    ZERO_RETURN             = -343,        /* peer sent close notify */
    SIDE_ERROR              = -344,        /* wrong client/server type */
    NO_PEER_CERT            = -345,        /* peer didn't send key */
    NTRU_KEY_ERROR          = -346,        /* NTRU key error  */
    NTRU_DRBG_ERROR         = -347,        /* NTRU drbg error  */
    NTRU_ENCRYPT_ERROR      = -348,        /* NTRU encrypt error  */
    NTRU_DECRYPT_ERROR      = -349,        /* NTRU decrypt error  */
    ECC_CURVETYPE_ERROR     = -350,        /* Bad ECC Curve Type */
    ECC_CURVE_ERROR         = -351,        /* Bad ECC Curve */
    ECC_PEERKEY_ERROR       = -352,        /* Bad Peer ECC Key */
    ECC_MAKEKEY_ERROR       = -353,        /* Bad Make ECC Key */
    ECC_EXPORT_ERROR        = -354,        /* Bad ECC Export Key */
    ECC_SHARED_ERROR        = -355,        /* Bad ECC Shared Secret */
    NOT_CA_ERROR            = -357,        /* Not a CA cert error */
    BAD_PATH_ERROR          = -358,        /* Bad path for opendir */
    BAD_CERT_MANAGER_ERROR  = -359,        /* Bad Cert Manager */
    OCSP_CERT_REVOKED       = -360,        /* OCSP Certificate revoked */
    CRL_CERT_REVOKED        = -361,        /* CRL Certificate revoked */
    CRL_MISSING             = -362,        /* CRL Not loaded */
    MONITOR_RUNNING_E       = -363,        /* CRL Monitor already running */
    THREAD_CREATE_E         = -364,        /* Thread Create Error */
    OCSP_NEED_URL           = -365,        /* OCSP need an URL for lookup */
    OCSP_CERT_UNKNOWN       = -366,        /* OCSP responder doesn't know */
    OCSP_LOOKUP_FAIL        = -367,        /* OCSP lookup not successful */
    MAX_CHAIN_ERROR         = -368,        /* max chain depth exceeded */
    COOKIE_ERROR            = -369,        /* dtls cookie error */
    SEQUENCE_ERROR          = -370,        /* dtls sequence error */
    SUITES_ERROR            = -371,        /* suites pointer error */
    SSL_NO_PEM_HEADER       = -372,        /* no PEM header found */
    OUT_OF_ORDER_E          = -373,        /* out of order message */
    BAD_KEA_TYPE_E          = -374,        /* bad KEA type found */
    SANITY_CIPHER_E         = -375,        /* sanity check on cipher error */
    RECV_OVERFLOW_E         = -376,        /* RXCB returned more than rqed */
    GEN_COOKIE_E            = -377,        /* Generate Cookie Error */
    NO_PEER_VERIFY          = -378,        /* Need peer cert verify Error */
    FWRITE_ERROR            = -379,        /* fwrite problem */
    CACHE_MATCH_ERROR       = -380,        /* chache hdr match error */
    UNKNOWN_SNI_HOST_NAME_E = -381,        /* Unrecognized host name Error */
    UNKNOWN_MAX_FRAG_LEN_E  = -382,        /* Unrecognized max frag len Error */
    KEYUSE_SIGNATURE_E      = -383,        /* KeyUse digSignature error */
    KEYUSE_ENCIPHER_E       = -385,        /* KeyUse keyEncipher error */
    EXTKEYUSE_AUTH_E        = -386,        /* ExtKeyUse server|client_auth */
    SEND_OOB_READ_E         = -387,        /* Send Cb out of bounds read */
    SECURE_RENEGOTIATION_E  = -388,        /* Invalid Renegotiation Info */
    SESSION_TICKET_LEN_E    = -389,        /* Session Ticket too large */
    SESSION_TICKET_EXPECT_E = -390,        /* Session Ticket missing   */
    SCR_DIFFERENT_CERT_E    = -391,        /* SCR Different cert error  */
    SESSION_SECRET_CB_E     = -392,        /* Session secret Cb fcn failure */
    NO_CHANGE_CIPHER_E      = -393,        /* Finished before change cipher */
    SANITY_MSG_E            = -394,        /* Sanity check on msg order error */
    DUPLICATE_MSG_E         = -395,        /* Duplicate message error */
    SNI_UNSUPPORTED         = -396,        /* SSL 3.0 does not support SNI */
    SOCKET_PEER_CLOSED_E    = -397,        /* Underlying transport closed */

    BAD_TICKET_KEY_CB_SZ    = -398,        /* Bad session ticket key cb size */
    BAD_TICKET_MSG_SZ       = -399,        /* Bad session ticket msg size    */
    BAD_TICKET_ENCRYPT      = -400,        /* Bad user ticket encrypt        */

    DH_KEY_SIZE_E           = -401,        /* DH Key too small */

    /* add strings to SetErrorString !!!!! */

    /* begin negotiation parameter errors */
    UNSUPPORTED_SUITE       = -500,        /* unsupported cipher suite */
    MATCH_SUITE_ERROR       = -501         /* can't match cipher suite */
    /* end negotiation parameter errors only 10 for now */
    /* add strings to SetErrorString !!!!! */

    /* no error stings go down here, add above negotiation errors !!!! */
};


#ifdef WOLFSSL_CALLBACKS
    enum {
        MIN_PARAM_ERR = UNSUPPORTED_SUITE,
        MAX_PARAM_ERR = MIN_PARAM_ERR - 10
    };
#endif


WOLFSSL_LOCAL
void SetErrorString(int err, char* buff);


#ifdef __cplusplus
    }  /* extern "C" */
#endif


#endif /* wolfSSL_ERROR_H */


