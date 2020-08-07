/* sha512.h
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



#ifndef CTAO_CRYPT_SHA512_H
#define CTAO_CRYPT_SHA512_H

#include <wolfssl/wolfcrypt/sha512.h>
#define InitSha512   wc_InitSha512
#define Sha512Update wc_Sha512Update
#define Sha512Final  wc_Sha512Final
#define Sha512Hash   wc_Sha512Hash

#if defined(WOLFSSL_SHA384) || defined(HAVE_AESGCM)
    #define InitSha384   wc_InitSha384
    #define Sha384Update wc_Sha384Update
    #define Sha384Final  wc_Sha384Final
    #define Sha384Hash   wc_Sha384Hash
#endif /* WOLFSSL_SHA384 */

#endif /* CTAO_CRYPT_SHA512_H */

