/* sha256.h
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





#ifndef NO_SHA256

#ifndef CTAO_CRYPT_SHA256_H
#define CTAO_CRYPT_SHA256_H

#include <wolfssl/wolfcrypt/sha256.h>
#define InitSha256   wc_InitSha256
#define Sha256Update wc_Sha256Update
#define Sha256Final  wc_Sha256Final
#define Sha256Hash   wc_Sha256Hash

#ifdef WOLFSSL_SHA224
    #define InitSha224   wc_InitSha224
    #define Sha224Update wc_Sha224Update
    #define Sha224Final  wc_Sha224Final
    #define Sha224Hash   wc_Sha224Hash
#endif

#endif /* CTAO_CRYPT_SHA256_H */
#endif /* NO_SHA256 */

