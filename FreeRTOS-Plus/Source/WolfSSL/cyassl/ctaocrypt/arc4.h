/* arc4.h
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifndef CTAO_CRYPT_ARC4_H
#define CTAO_CRYPT_ARC4_H


#include <cyassl/ctaocrypt/types.h>


#ifdef __cplusplus
    extern "C" {
#endif


#define CYASSL_ARC4_CAVIUM_MAGIC 0xBEEF0001

enum {
	ARC4_ENC_TYPE   = 4,    /* cipher unique type */
    ARC4_STATE_SIZE = 256
};

/* ARC4 encryption and decryption */
typedef struct Arc4 {
    byte x;
    byte y;
    byte state[ARC4_STATE_SIZE];
#ifdef HAVE_CAVIUM
    int    devId;           /* nitrox device id */
    word32 magic;           /* using cavium magic */
    word64 contextHandle;   /* nitrox context memory handle */
#endif
} Arc4;

CYASSL_API void Arc4Process(Arc4*, byte*, const byte*, word32);
CYASSL_API void Arc4SetKey(Arc4*, const byte*, word32);

#ifdef HAVE_CAVIUM
    CYASSL_API int  Arc4InitCavium(Arc4*, int);
    CYASSL_API void Arc4FreeCavium(Arc4*);
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CTAO_CRYPT_ARC4_H */

