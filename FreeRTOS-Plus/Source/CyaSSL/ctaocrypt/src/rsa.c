/* rsa.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/rsa.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/error.h>
#include <cyassl/ctaocrypt/logging.h>

#ifdef SHOW_GEN
    #include <stdio.h>
#endif


enum {
    RSA_PUBLIC_ENCRYPT  = 0,
    RSA_PUBLIC_DECRYPT  = 1,
    RSA_PRIVATE_ENCRYPT = 2,
    RSA_PRIVATE_DECRYPT = 3,

    RSA_BLOCK_TYPE_1 = 1,
    RSA_BLOCK_TYPE_2 = 2,

    RSA_MIN_SIZE = 512,
    RSA_MAX_SIZE = 4096,

    RSA_MIN_PAD_SZ   = 11      /* seperator + 0 + pad value + 8 pads */
};


void InitRsaKey(RsaKey* key, void* heap)
{
    key->type = -1;  /* haven't decided yet */
    key->heap = heap;

/* TomsFastMath doesn't use memory allocation */
#ifndef USE_FAST_MATH
    key->n.dp = key->e.dp = 0;  /* public  alloc parts */

    key->d.dp = key->p.dp  = 0;  /* private alloc parts */
    key->q.dp = key->dP.dp = 0;  
    key->u.dp = key->dQ.dp = 0;
#endif
}


void FreeRsaKey(RsaKey* key)
{
    (void)key;
/* TomsFastMath doesn't use memory allocation */
#ifndef USE_FAST_MATH
    if (key->type == RSA_PRIVATE) {
        mp_clear(&key->u);
        mp_clear(&key->dQ);
        mp_clear(&key->dP);
        mp_clear(&key->q);
        mp_clear(&key->p);
        mp_clear(&key->d);
    }
    mp_clear(&key->e);
    mp_clear(&key->n);
#endif
}

static void RsaPad(const byte* input, word32 inputLen, byte* pkcsBlock,
                   word32 pkcsBlockLen, byte padValue, RNG* rng)
{
    if (inputLen == 0) return;

    pkcsBlock[0] = 0x0;       /* set first byte to zero and advance */
    pkcsBlock++; pkcsBlockLen--;
    pkcsBlock[0] = padValue;  /* insert padValue */

    if (padValue == RSA_BLOCK_TYPE_1)
        /* pad with 0xff bytes */
        XMEMSET(&pkcsBlock[1], 0xFF, pkcsBlockLen - inputLen - 2);
    else {
        /* pad with non-zero random bytes */
        word32 padLen = pkcsBlockLen - inputLen - 1, i;
        RNG_GenerateBlock(rng, &pkcsBlock[1], padLen);

        /* remove zeros */
        for (i = 1; i < padLen; i++)
            if (pkcsBlock[i] == 0) pkcsBlock[i] = 0x01;
    }

    pkcsBlock[pkcsBlockLen-inputLen-1] = 0;     /* separator */
    XMEMCPY(pkcsBlock+pkcsBlockLen-inputLen, input, inputLen);
}


static word32 RsaUnPad(const byte *pkcsBlock, unsigned int pkcsBlockLen,
                       byte **output, byte padValue)
{
    word32 maxOutputLen = (pkcsBlockLen > 10) ? (pkcsBlockLen - 10) : 0,
           invalid = 0,
           i = 1,
           outputLen;

    if (pkcsBlock[0] != 0x0) /* skip past zero */
        invalid = 1;
    pkcsBlock++; pkcsBlockLen--;

    /* Require block type padValue */
    invalid = (pkcsBlock[0] != padValue) || invalid;

    /* skip past the padding until we find the separator */
    while (i<pkcsBlockLen && pkcsBlock[i++]) { /* null body */
        }
    if(!(i==pkcsBlockLen || pkcsBlock[i-1]==0)) {
        CYASSL_MSG("RsaUnPad error, bad formatting");
        return 0;
    }

    outputLen = pkcsBlockLen - i;
    invalid = (outputLen > maxOutputLen) || invalid;

    if (invalid) {
        CYASSL_MSG("RsaUnPad error, bad formatting");
        return 0;
    }

    *output = (byte *)(pkcsBlock + i);
    return outputLen;
}


static int RsaFunction(const byte* in, word32 inLen, byte* out, word32* outLen,
                       int type, RsaKey* key)
{
    #define ERROR_OUT(x) { ret = x; goto done;}

    mp_int tmp;
    int    ret = 0;
    word32 keyLen, len;

    if (mp_init(&tmp) != MP_OKAY)
        return MP_INIT_E;

    if (mp_read_unsigned_bin(&tmp, (byte*)in, inLen) != MP_OKAY)
        ERROR_OUT(MP_READ_E);

    if (type == RSA_PRIVATE_DECRYPT || type == RSA_PRIVATE_ENCRYPT) {
        #ifdef RSA_LOW_MEM      /* half as much memory but twice as slow */
            if (mp_exptmod(&tmp, &key->d, &key->n, &tmp) != MP_OKAY)
                ERROR_OUT(MP_EXPTMOD_E);
        #else
            #define INNER_ERROR_OUT(x) { ret = x; goto inner_done; }

            mp_int tmpa, tmpb;

            if (mp_init(&tmpa) != MP_OKAY)
                ERROR_OUT(MP_INIT_E);

            if (mp_init(&tmpb) != MP_OKAY) {
                mp_clear(&tmpa);
                ERROR_OUT(MP_INIT_E);
            }

            /* tmpa = tmp^dP mod p */
            if (mp_exptmod(&tmp, &key->dP, &key->p, &tmpa) != MP_OKAY)
                INNER_ERROR_OUT(MP_EXPTMOD_E);

            /* tmpb = tmp^dQ mod q */
            if (mp_exptmod(&tmp, &key->dQ, &key->q, &tmpb) != MP_OKAY)
                INNER_ERROR_OUT(MP_EXPTMOD_E);

            /* tmp = (tmpa - tmpb) * qInv (mod p) */
            if (mp_sub(&tmpa, &tmpb, &tmp) != MP_OKAY)
                INNER_ERROR_OUT(MP_SUB_E);

            if (mp_mulmod(&tmp, &key->u, &key->p, &tmp) != MP_OKAY)
                INNER_ERROR_OUT(MP_MULMOD_E);

            /* tmp = tmpb + q * tmp */
            if (mp_mul(&tmp, &key->q, &tmp) != MP_OKAY)
                INNER_ERROR_OUT(MP_MUL_E);

            if (mp_add(&tmp, &tmpb, &tmp) != MP_OKAY)
                INNER_ERROR_OUT(MP_ADD_E);

        inner_done:
            mp_clear(&tmpa);
            mp_clear(&tmpb);

            if (ret != 0) return ret;

        #endif   /* RSA_LOW_MEM */
    }
    else if (type == RSA_PUBLIC_ENCRYPT || type == RSA_PUBLIC_DECRYPT) {
        if (mp_exptmod(&tmp, &key->e, &key->n, &tmp) != MP_OKAY)
            ERROR_OUT(MP_EXPTMOD_E);
    }
    else
        ERROR_OUT(RSA_WRONG_TYPE_E);

    keyLen = mp_unsigned_bin_size(&key->n);
    if (keyLen > *outLen)
        ERROR_OUT(RSA_BUFFER_E);

    len = mp_unsigned_bin_size(&tmp);

    /* pad front w/ zeros to match key length */
    while (len < keyLen) {
        *out++ = 0x00;
        len++;
    }

    *outLen = keyLen;

    /* convert */
    if (mp_to_unsigned_bin(&tmp, out) != MP_OKAY)
        ERROR_OUT(MP_TO_E);
   
done: 
    mp_clear(&tmp);
    return ret;
}


int RsaPublicEncrypt(const byte* in, word32 inLen, byte* out, word32 outLen,
                     RsaKey* key, RNG* rng)
{
    int sz = mp_unsigned_bin_size(&key->n), ret;

    if (sz > (int)outLen)
        return RSA_BUFFER_E;

    if (inLen > (word32)(sz - RSA_MIN_PAD_SZ))
        return RSA_BUFFER_E;

    RsaPad(in, inLen, out, sz, RSA_BLOCK_TYPE_2, rng);

    if ((ret = RsaFunction(out, sz, out, &outLen, RSA_PUBLIC_ENCRYPT, key)) < 0)
        sz = ret;

    return sz;
}


int RsaPrivateDecryptInline(byte* in, word32 inLen, byte** out, RsaKey* key)
{
    int plainLen, ret;

    if ((ret = RsaFunction(in, inLen, in, &inLen, RSA_PRIVATE_DECRYPT, key))
            < 0) {
        return ret;
    }
 
    plainLen = RsaUnPad(in, inLen, out, RSA_BLOCK_TYPE_2);

    return plainLen;
}


int RsaPrivateDecrypt(const byte* in, word32 inLen, byte* out, word32 outLen,
                     RsaKey* key)
{
    int plainLen, ret;
    byte*  tmp;
    byte*  pad = 0;

    tmp = (byte*)XMALLOC(inLen, key->heap, DYNAMIC_TYPE_RSA);
    if (tmp == NULL) {
        return MEMORY_E;
    }

    XMEMCPY(tmp, in, inLen);

    if ((ret = plainLen = RsaPrivateDecryptInline(tmp, inLen, &pad, key))
            < 0) {
        XFREE(tmp, key->heap, DYNAMIC_TYPE_RSA);
        return ret;
    }
    if (plainLen > (int)outLen)
        plainLen = BAD_FUNC_ARG;
    else
        XMEMCPY(out, pad, plainLen);
    XMEMSET(tmp, 0x00, inLen); 

    XFREE(tmp, key->heap, DYNAMIC_TYPE_RSA);
    return plainLen;
}


/* for Rsa Verify */
int RsaSSL_VerifyInline(byte* in, word32 inLen, byte** out, RsaKey* key)
{
    int plainLen, ret;

    if ((ret = RsaFunction(in, inLen, in, &inLen, RSA_PUBLIC_DECRYPT, key))
            < 0) {
        return ret;
    }
  
    plainLen = RsaUnPad(in, inLen, out, RSA_BLOCK_TYPE_1);

    return plainLen;
}


int RsaSSL_Verify(const byte* in, word32 inLen, byte* out, word32 outLen,
                     RsaKey* key)
{
    int plainLen, ret;
    byte*  tmp;
    byte*  pad = 0;

    tmp = (byte*)XMALLOC(inLen, key->heap, DYNAMIC_TYPE_RSA);
    if (tmp == NULL) {
        return MEMORY_E;
    }

    XMEMCPY(tmp, in, inLen);

    if ((ret = plainLen = RsaSSL_VerifyInline(tmp, inLen, &pad, key))
            < 0) {
        XFREE(tmp, key->heap, DYNAMIC_TYPE_RSA);
        return ret;
    }

    if (plainLen > (int)outLen)
        plainLen = BAD_FUNC_ARG;
    else 
        XMEMCPY(out, pad, plainLen);
    XMEMSET(tmp, 0x00, inLen); 

    XFREE(tmp, key->heap, DYNAMIC_TYPE_RSA);
    return plainLen;
}


/* for Rsa Sign */
int RsaSSL_Sign(const byte* in, word32 inLen, byte* out, word32 outLen,
                      RsaKey* key, RNG* rng)
{
    int sz = mp_unsigned_bin_size(&key->n), ret;

    if (sz > (int)outLen)
        return RSA_BUFFER_E;

    if (inLen > (word32)(sz - RSA_MIN_PAD_SZ))
        return RSA_BUFFER_E;

    RsaPad(in, inLen, out, sz, RSA_BLOCK_TYPE_1, rng);

    if ((ret = RsaFunction(out, sz, out, &outLen, RSA_PRIVATE_ENCRYPT,key)) < 0)
        sz = ret;
    
    return sz;
}


int RsaEncryptSize(RsaKey* key)
{
    return mp_unsigned_bin_size(&key->n);
}


#ifdef CYASSL_KEY_GEN

static const int USE_BBS = 1;

static int rand_prime(mp_int* N, int len, RNG* rng, void* heap)
{
    int   err, res, type;
    byte* buf;

    (void)heap;
    if (N == NULL || rng == NULL)
       return BAD_FUNC_ARG; 

    /* get type */
    if (len < 0) {
        type = USE_BBS;
        len = -len;
    } else {
        type = 0;
    }

    /* allow sizes between 2 and 512 bytes for a prime size */
    if (len < 2 || len > 512) { 
        return BAD_FUNC_ARG;
    }
   
    /* allocate buffer to work with */
    buf = (byte*)XMALLOC(len, heap, DYNAMIC_TYPE_RSA);
    if (buf == NULL) {
        return MEMORY_E;
    }
    XMEMSET(buf, 0, len);

    do {
#ifdef SHOW_GEN
        printf(".");
        fflush(stdout);
#endif
        /* generate value */
        RNG_GenerateBlock(rng, buf, len);

        /* munge bits */
        buf[0]     |= 0x80 | 0x40;
        buf[len-1] |= 0x01 | ((type & USE_BBS) ? 0x02 : 0x00);
 
        /* load value */
        if ((err = mp_read_unsigned_bin(N, buf, len)) != MP_OKAY) {
            XFREE(buf, heap, DYNAMIC_TYPE_RSA);
            return err;
        }

        /* test */
        if ((err = mp_prime_is_prime(N, 8, &res)) != MP_OKAY) {
            XFREE(buf, heap, DYNAMIC_TYPE_RSA);
            return err;
        }
    } while (res == MP_NO);

#ifdef LTC_CLEAN_STACK
    XMEMSET(buf, 0, len);
#endif

    XFREE(buf, heap, DYNAMIC_TYPE_RSA);
    return 0;
}


/* Make an RSA key for size bits, with e specified, 65537 is a good e */
int MakeRsaKey(RsaKey* key, int size, long e, RNG* rng)
{
    mp_int p, q, tmp1, tmp2, tmp3;
    int    err;

    if (key == NULL || rng == NULL)
        return BAD_FUNC_ARG;

    if (size < RSA_MIN_SIZE || size > RSA_MAX_SIZE)
        return BAD_FUNC_ARG;

    if (e < 3 || (e & 1) == 0)
        return BAD_FUNC_ARG;

    if ((err = mp_init_multi(&p, &q, &tmp1, &tmp2, &tmp3, NULL)) != MP_OKAY)
        return err;

    err = mp_set_int(&tmp3, e);

    /* make p */
    if (err == MP_OKAY) {
        do {
            err = rand_prime(&p, size/16, rng, key->heap); /* size in bytes/2 */

            if (err == MP_OKAY)
                err = mp_sub_d(&p, 1, &tmp1);  /* tmp1 = p-1 */

            if (err == MP_OKAY)
                err = mp_gcd(&tmp1, &tmp3, &tmp2);  /* tmp2 = gcd(p-1, e) */
        } while (err == MP_OKAY && mp_cmp_d(&tmp2, 1) != 0);  /* e divdes p-1 */
    }

    /* make q */
    if (err == MP_OKAY) {
        do {
            err = rand_prime(&q, size/16, rng, key->heap); /* size in bytes/2 */

            if (err == MP_OKAY)
                err = mp_sub_d(&q, 1, &tmp1);  /* tmp1 = q-1 */

            if (err == MP_OKAY)
                err = mp_gcd(&tmp1, &tmp3, &tmp2);  /* tmp2 = gcd(q-1, e) */
        } while (err == MP_OKAY && mp_cmp_d(&tmp2, 1) != 0);  /* e divdes q-1 */
    }

    if (err == MP_OKAY)
        err = mp_init_multi(&key->n, &key->e, &key->d, &key->p, &key->q, NULL);

    if (err == MP_OKAY)
        err = mp_init_multi(&key->dP, &key->dP, &key->u, NULL, NULL, NULL);

    if (err == MP_OKAY)
        err = mp_sub_d(&p, 1, &tmp2);  /* tmp2 = p-1 */

    if (err == MP_OKAY)
        err = mp_lcm(&tmp1, &tmp2, &tmp1);  /* tmp1 = lcm(p-1, q-1),last loop */

    /* make key */
    if (err == MP_OKAY)
        err = mp_set_int(&key->e, e);  /* key->e = e */

    if (err == MP_OKAY)                /* key->d = 1/e mod lcm(p-1, q-1) */
        err = mp_invmod(&key->e, &tmp1, &key->d);

    if (err == MP_OKAY)
        err = mp_mul(&p, &q, &key->n);  /* key->n = pq */

    if (err == MP_OKAY)
        err = mp_sub_d(&p, 1, &tmp1);

    if (err == MP_OKAY)
        err = mp_sub_d(&q, 1, &tmp2);

    if (err == MP_OKAY)
        err = mp_mod(&key->d, &tmp1, &key->dP);

    if (err == MP_OKAY)
        err = mp_mod(&key->d, &tmp2, &key->dQ);

    if (err == MP_OKAY)
        err = mp_invmod(&q, &p, &key->u);

    if (err == MP_OKAY)
        err = mp_copy(&p, &key->p);

    if (err == MP_OKAY)
        err = mp_copy(&q, &key->q);

    if (err == MP_OKAY)
        key->type = RSA_PRIVATE; 

    mp_clear(&tmp3); 
    mp_clear(&tmp2); 
    mp_clear(&tmp1); 
    mp_clear(&q); 
    mp_clear(&p);

    if (err != MP_OKAY) {
        FreeRsaKey(key);        
        return err;
    }

    return 0;
}


#endif /* CYASLS_KEY_GEN */

