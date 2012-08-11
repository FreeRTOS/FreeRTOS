/* arc4.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef CTAO_CRYPT_ARC4_H
#define CTAO_CRYPT_ARC4_H


#include <cyassl/ctaocrypt/types.h>


#ifdef __cplusplus
    extern "C" {
#endif


enum {
	ARC4_ENC_TYPE   = 4,    /* cipher unique type */
    ARC4_STATE_SIZE = 256
};

/* ARC4 encryption and decryption */
typedef struct Arc4 {
    byte x;
    byte y;
    byte state[ARC4_STATE_SIZE];
} Arc4;

CYASSL_API void Arc4Process(Arc4*, byte*, const byte*, word32);
CYASSL_API void Arc4SetKey(Arc4*, const byte*, word32);


#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CTAO_CRYPT_ARC4_H */

