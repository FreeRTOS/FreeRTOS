/* compress.h
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

#ifndef WOLF_CRYPT_COMPRESS_H
#define WOLF_CRYPT_COMPRESS_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_LIBZ

#ifdef __cplusplus
    extern "C" {
#endif


#define COMPRESS_FIXED 1


WOLFSSL_API int wc_Compress(byte*, word32, const byte*, word32, word32);
WOLFSSL_API int wc_DeCompress(byte*, word32, const byte*, word32);


#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* HAVE_LIBZ */
#endif /* WOLF_CRYPT_COMPRESS_H */

