/* renesas-tsip-crypt.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */
#ifndef __RENESAS_TSIP_CRYPT_H__
#define __RENESAS_TSIP_CRYPT_H__

#if defined(WOLFSSL_RENESAS_TSIP_IAREWRX)
    #include "r_bsp/mcu/all/r_rx_compiler.h"
    #include "r_bsp/platform.h"
#else
    #include "platform.h"
#endif

#include "r_tsip_rx_if.h"
#include <wolfssl/wolfcrypt/logging.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    tsip_Key_SESSION = 1,
    tsip_Key_AES128  = 2,
    tsip_Key_AES256  = 3,
    tsip_Key_RSA1024 = 4,
    tsip_Key_RSA2048 = 5,
    tsip_Key_tls_Rsa2048 = 6,
    tsip_Key_unknown = -1,
} wolfssl_TSIP_KEY_IV;

enum {
    l_TLS_RSA_WITH_AES_128_CBC_SHA     = 0x2F,
    l_TLS_RSA_WITH_AES_128_CBC_SHA256  = 0x3c,
    l_TLS_RSA_WITH_AES_256_CBC_SHA     = 0x35,
    l_TLS_RSA_WITH_AES_256_CBC_SHA256  = 0x3d,
};

typedef struct
{
    uint8_t                          *encrypted_session_key;
    uint8_t                          *iv;
    uint8_t                          *encrypted_user_tls_key;
    tsip_tls_ca_certification_public_key_index_t  user_rsa2048_tls_pubindex;
} tsip_key_data;

struct WOLFSSL;

int  tsip_Open( );
void tsip_Close( );
int tsip_hw_lock();
void tsip_hw_unlock( void );
int tsip_usable(const struct WOLFSSL *ssl);
void tsip_inform_sflash_signedcacert(const byte *ps_flash, 
    const byte *psigned_ca_cert, word32 len);
void tsip_inform_cert_sign(const byte *sign);
/* set / get key */
void tsip_inform_user_keys(byte *encrypted_session_key, byte *iv,
                           byte *encrypted_user_tls_key);
                           
byte tsip_rootCAverified( );
byte tsip_checkCA(word32 cmIdx);
int tsip_tls_RootCertVerify(const byte *cert  , word32 cert_len,
                            word32 key_n_start, word32 key_n_len,
                            word32 key_e_start, word32 key_e_len,
                            word32 cm_row);
int tsip_tls_CertVerify(const byte *cert, word32 certSz,
                        const byte *signature, word32 sigSz,
                        word32 key_n_start, word32 key_n_len,
                        word32 key_e_start, word32 key_e_len,
                        byte *tsip_encRsaKeyIdx);
void tsip_inform_key_position(const word32 key_n_start, const word32 key_n_len,
                              const word32 key_e_start, const word32 key_e_len);
int tsip_generatePremasterSecret(byte *premaster, word32 preSz);
int tsip_generateEncryptPreMasterSecret(struct WOLFSSL *ssl, byte *out, 
                                        word32 *outSz);
int tsip_generateMasterSecret(const byte *pre, const byte *cr,const byte *sr,
                              byte *ms);
int tsip_generateSeesionKey(struct WOLFSSL *ssl);
int tsip_Sha256Hmac(const struct WOLFSSL *ssl, const byte *myInner, 
            word32 innerSz, const byte *in, word32 sz, byte *digest, 
            word32 verify);
int tsip_Sha1Hmac(const struct WOLFSSL *ssl, const byte *myInner, 
            word32 innerSz, const byte *in, word32 sz, byte *digest, 
            word32 verify);
            
#if (!defined(NO_SHA) || !defined(NO_SHA256)) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_CRYPT_HASH)

typedef enum {
    TSIP_SHA1 = 0,
    TSIP_SHA256 = 1,
} TSIP_SHA_TYPE;

typedef struct {
    byte*  msg;
    void*  heap;
    word32 used;
    word32 len;
    word32 sha_type;
} wolfssl_TSIP_Hash;

/* RAW hash function APIs are not implemented with TSIP */
#define WOLFSSL_NO_HASH_RAW

typedef wolfssl_TSIP_Hash wc_Sha;

#if !defined(NO_SHA256)
    typedef wolfssl_TSIP_Hash wc_Sha256;
#endif

#endif /* NO_SHA */

#if defined(WOLFSSL_RENESAS_TSIP_TLS_AES_CRYPT)
typedef struct {
    tsip_aes_key_index_t tsip_keyIdx;
    word32               keySize;
} TSIP_AES_CTX;
    
    struct Aes;
    int wc_tsip_AesCbcEncrypt(struct Aes* aes, byte* out, const byte* in,
                              word32 sz);
    int wc_tsip_AesCbcDecrypt(struct Aes* aes, byte* out, const byte* in,
                              word32 sz);
    
#endif /* WOLFSSL_RENESAS_TSIP_TLS_AES */

#if defined(WOLFSSL_RENESAS_TSIP_CRYPT_DEBUG)
byte *ret2err(word32 ret);

#endif

#ifdef __cplusplus
}
#endif

#endif  /* __RENESAS_TSIP_CRYPT_H__ */
