/* rsa.h
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


#ifndef CTAO_CRYPT_RSA_H
#define CTAO_CRYPT_RSA_H

#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/random.h>

#ifdef __cplusplus
    extern "C" {
#endif


enum {
    RSA_PUBLIC   = 0,
    RSA_PRIVATE  = 1
};

/* RSA */
typedef struct RsaKey {
    mp_int n, e, d, p, q, dP, dQ, u;
    int   type;                               /* public or private */
    void* heap;                               /* for user memory overrides */
} RsaKey;


CYASSL_API void InitRsaKey(RsaKey* key, void*);
CYASSL_API void FreeRsaKey(RsaKey* key);

CYASSL_API int  RsaPublicEncrypt(const byte* in, word32 inLen, byte* out,
                                 word32 outLen, RsaKey* key, RNG* rng);
CYASSL_API int  RsaPrivateDecryptInline(byte* in, word32 inLen, byte** out,
                                        RsaKey* key);
CYASSL_API int  RsaPrivateDecrypt(const byte* in, word32 inLen, byte* out,
                                  word32 outLen, RsaKey* key);
CYASSL_API int  RsaSSL_Sign(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key, RNG* rng);
CYASSL_API int  RsaSSL_VerifyInline(byte* in, word32 inLen, byte** out,
                                    RsaKey* key);
CYASSL_API int  RsaSSL_Verify(const byte* in, word32 inLen, byte* out,
                              word32 outLen, RsaKey* key);
CYASSL_API int  RsaEncryptSize(RsaKey* key);

CYASSL_API int RsaPrivateKeyDecode(const byte* input, word32* inOutIdx, RsaKey*,
                                   word32);
CYASSL_API int RsaPublicKeyDecode(const byte* input, word32* inOutIdx, RsaKey*,
                                  word32);
#ifdef CYASSL_KEY_GEN
    CYASSL_API int MakeRsaKey(RsaKey* key, int size, long e, RNG* rng);
    CYASSL_API int RsaKeyToDer(RsaKey*, byte* output, word32 inLen);
#endif



#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_RSA_H */

