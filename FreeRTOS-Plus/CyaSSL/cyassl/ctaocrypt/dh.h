/* dh.h
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


#ifndef NO_DH

#ifndef CTAO_CRYPT_DH_H
#define CTAO_CRYPT_DH_H

#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/random.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* Diffie-Hellman Key */
typedef struct DhKey {
    mp_int p, g;                            /* group parameters  */
} DhKey;


CYASSL_API void InitDhKey(DhKey* key);
CYASSL_API void FreeDhKey(DhKey* key);

CYASSL_API int DhGenerateKeyPair(DhKey* key, RNG* rng, byte* priv,
                                 word32* privSz, byte* pub, word32* pubSz);
CYASSL_API int DhAgree(DhKey* key, byte* agree, word32* agreeSz,
                       const byte* priv, word32 privSz, const byte* otherPub,
                       word32 pubSz);

CYASSL_API int DhKeyDecode(const byte* input, word32* inOutIdx, DhKey* key,
                           word32);
CYASSL_API int DhSetKey(DhKey* key, const byte* p, word32 pSz, const byte* g,
                        word32 gSz);
CYASSL_API int DhParamsLoad(const byte* input, word32 inSz, byte* p,
                            word32* pInOutSz, byte* g, word32* gInOutSz);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_DH_H */

#endif /* NO_DH */

