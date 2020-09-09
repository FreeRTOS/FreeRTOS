/* wc_encrypt.h
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

/*!
    \file wolfssl/wolfcrypt/wc_encrypt.h
*/


#ifndef WOLF_CRYPT_ENCRYPT_H
#define WOLF_CRYPT_ENCRYPT_H

#include <wolfssl/wolfcrypt/types.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/chacha.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/arc4.h>

#ifdef __cplusplus
    extern "C" {
#endif

/* determine max cipher key size */
#ifndef NO_AES
    #define WC_MAX_SYM_KEY_SIZE     (AES_MAX_KEY_SIZE/8)
#elif defined(HAVE_CHACHA)
    #define WC_MAX_SYM_KEY_SIZE     CHACHA_MAX_KEY_SZ
#elif !defined(NO_DES3)
    #define WC_MAX_SYM_KEY_SIZE     DES3_KEY_SIZE
#elif !defined(NO_RC4)
    #define WC_MAX_SYM_KEY_SIZE     RC4_KEY_SIZE
#else
    #define WC_MAX_SYM_KEY_SIZE     32
#endif


#if !defined(NO_AES) && defined(HAVE_AES_CBC)
WOLFSSL_API int wc_AesCbcEncryptWithKey(byte* out, const byte* in, word32 inSz,
                                        const byte* key, word32 keySz,
                                        const byte* iv);
WOLFSSL_API int wc_AesCbcDecryptWithKey(byte* out, const byte* in, word32 inSz,
                                        const byte* key, word32 keySz,
                                        const byte* iv);
#endif /* !NO_AES */


#ifndef NO_DES3
WOLFSSL_API int wc_Des_CbcDecryptWithKey(byte* out,
                                         const byte* in, word32 sz,
                                         const byte* key, const byte* iv);
WOLFSSL_API int wc_Des_CbcEncryptWithKey(byte* out,
                                         const byte* in, word32 sz,
                                         const byte* key, const byte* iv);
WOLFSSL_API int wc_Des3_CbcEncryptWithKey(byte* out,
                                          const byte* in, word32 sz,
                                          const byte* key, const byte* iv);
WOLFSSL_API int wc_Des3_CbcDecryptWithKey(byte* out,
                                          const byte* in, word32 sz,
                                          const byte* key, const byte* iv);
#endif /* !NO_DES3 */




#ifdef WOLFSSL_ENCRYPTED_KEYS
    struct EncryptedInfo;
    WOLFSSL_API int wc_BufferKeyDecrypt(struct EncryptedInfo* info, byte* der, word32 derSz,
        const byte* password, int passwordSz, int hashType);
    WOLFSSL_API int wc_BufferKeyEncrypt(struct EncryptedInfo* info, byte* der, word32 derSz,
        const byte* password, int passwordSz, int hashType);
#endif /* WOLFSSL_ENCRYPTED_KEYS */

#ifndef NO_PWDBASED
    WOLFSSL_LOCAL int wc_CryptKey(const char* password, int passwordSz, 
        byte* salt, int saltSz, int iterations, int id, byte* input, int length,
        int version, byte* cbcIv, int enc, int shaOid);
#endif

#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* WOLF_CRYPT_ENCRYPT_H */

