/* xil-sha3.h
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


#ifndef WOLF_XIL_CRYPT_SHA3_H
#define WOLF_XIL_CRYPT_SHA3_H

#ifdef WOLFSSL_SHA3
#include "xsecure_sha.h"

#ifdef __cplusplus
    extern "C" {
#endif

/* Sha3 digest */
typedef struct Sha3 {
    XSecure_Sha3 hw;
    XCsuDma      dma;
} wc_Sha3;

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLFSSL_SHA3 */
#endif /* WOLF_XIL_CRYPT_SHA3_H */

