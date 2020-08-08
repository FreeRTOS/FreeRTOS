/* aes.h
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



#ifndef NO_AES

#ifndef CTAO_CRYPT_AES_H
#define CTAO_CRYPT_AES_H

#include <wolfssl/wolfcrypt/aes.h>
#define AesSetKey            wc_AesSetKey
#define AesSetIV             wc_AesSetIV
#define AesCbcEncrypt        wc_AesCbcEncrypt
#define AesCbcDecrypt        wc_AesCbcDecrypt
#define AesCbcDecryptWithKey wc_AesCbcDecryptWithKey

/* AES-CTR */
#ifdef WOLFSSL_AES_COUNTER
    #define AesCtrEncrypt wc_AesCtrEncrypt
#endif
/* AES-DIRECT */
#if defined(WOLFSSL_AES_DIRECT)
    #define AesEncryptDirect wc_AesEncryptDirect
    #define AesDecryptDirect wc_AesDecryptDirect
    #define AesSetKeyDirect  wc_AesSetKeyDirect
#endif
#ifdef HAVE_AESGCM
    #define AesGcmSetKey  wc_AesGcmSetKey
    #define AesGcmEncrypt wc_AesGcmEncrypt
    #define AesGcmDecrypt wc_AesGcmDecrypt
    #define GmacSetKey    wc_GmacSetKey
    #define GmacUpdate    wc_GmacUpdate
#endif /* HAVE_AESGCM */
#ifdef HAVE_AESCCM
    #define AesCcmSetKey  wc_AesCcmSetKey
    #define AesCcmEncrypt wc_AesCcmEncrypt
    #define AesCcmDecrypt wc_AesCcmDecrypt
#endif /* HAVE_AESCCM */

#endif /* CTAO_CRYPT_AES_H */
#endif /* NO_AES */

