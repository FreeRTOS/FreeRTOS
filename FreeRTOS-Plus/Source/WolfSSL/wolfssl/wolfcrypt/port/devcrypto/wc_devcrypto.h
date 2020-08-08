/* wc_devcrypto.h
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


#ifndef WOLFSSL_DEVCRYPTO_H
#define WOLFSSL_DEVCRYPTO_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef WOLFSSL_DEVCRYPTO

#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <crypto/cryptodev.h>

typedef struct WC_CRYPTODEV {
    int cfd;
    struct session_op sess;
} WC_CRYPTODEV;

WOLFSSL_LOCAL int wc_DevCryptoCreate(WC_CRYPTODEV* ctx, int type, byte* key, word32 keySz);
WOLFSSL_LOCAL void wc_DevCryptoFree(WC_CRYPTODEV* ctx);
WOLFSSL_LOCAL void wc_SetupCrypt(struct crypt_op* crt, WC_CRYPTODEV* dev,
        byte* src, int srcSz, byte* dst, byte* dig, int flag);
WOLFSSL_LOCAL void wc_SetupCryptSym(struct crypt_op* crt, WC_CRYPTODEV* dev,
        byte* src, word32 srcSz, byte* dst, byte* iv, int flag);
WOLFSSL_LOCAL void wc_SetupCryptAead(struct crypt_auth_op* crt, WC_CRYPTODEV* dev,
         byte* src, word32 srcSz, byte* dst, byte* iv, word32 ivSz, int flag,
         byte* authIn, word32 authInSz, byte* authTag, word32 authTagSz);

#endif /* WOLFSSL_DEVCRYPTO */
#endif /* WOLFSSL_DEVCRYPTO_H */


