/* curve25519.c
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

 /* Based On Daniel J Bernstein's curve25519 Public Domain ref10 work. */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_CURVE25519

#include <wolfssl/wolfcrypt/curve25519.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif

const curve25519_set_type curve25519_sets[] = {
{
        32,
        "CURVE25519",
}
};



int wc_curve25519_make_key(RNG* rng, int keysize, curve25519_key* key)
{
  unsigned char basepoint[CURVE25519_KEYSIZE] = {9};
  unsigned char n[CURVE25519_KEYSIZE];
  unsigned char p[CURVE25519_KEYSIZE];
  int  i;
  int  ret;

  if (key == NULL || rng == NULL)
      return ECC_BAD_ARG_E;

  /* currently only a key size of 32 bytes is used */
  if (keysize != CURVE25519_KEYSIZE)
      return ECC_BAD_ARG_E;

  /* get random number from RNG */
  ret = wc_RNG_GenerateBlock(rng, n, keysize);
  if (ret != 0)
      return ret;

  for (i = 0; i < keysize; ++i) key->k.point[i] = n[i];
  key->k.point[ 0] &= 248;
  key->k.point[31] &= 127;
  key->k.point[31] |= 64;

  /* compute public key */
  ret = curve25519(p, key->k.point, basepoint);

  /* store keys in big endian format */
  for (i = 0; i < keysize; ++i) n[i] = key->k.point[i];
  for (i = 0; i < keysize; ++i) {
      key->p.point[keysize - i - 1] = p[i];
      key->k.point[keysize - i - 1] = n[i];
  }

  ForceZero(n, keysize);
  ForceZero(p, keysize);

  return ret;
}


int wc_curve25519_shared_secret(curve25519_key* private_key,
                                curve25519_key* public_key,
                                byte* out, word32* outlen)
{
    unsigned char k[CURVE25519_KEYSIZE];
    unsigned char p[CURVE25519_KEYSIZE];
    unsigned char o[CURVE25519_KEYSIZE];
    int ret = 0;
    int i;

    /* sanity check */
    if (private_key == NULL || public_key == NULL || out == NULL ||
            outlen == NULL)
        return BAD_FUNC_ARG;

    /* avoid implementation fingerprinting */
    if (public_key->p.point[0] > 0x7F)
        return ECC_BAD_ARG_E;

    XMEMSET(p,   0, sizeof(p));
    XMEMSET(k,   0, sizeof(k));
    XMEMSET(out, 0, CURVE25519_KEYSIZE);

    for (i = 0; i < CURVE25519_KEYSIZE; ++i) {
        p[i] = public_key->p.point [CURVE25519_KEYSIZE - i - 1];
        k[i] = private_key->k.point[CURVE25519_KEYSIZE - i - 1];
    }

    ret     = curve25519(o , k, p);
    *outlen = CURVE25519_KEYSIZE;

    for (i = 0; i < CURVE25519_KEYSIZE; ++i) {
        out[i] = o[CURVE25519_KEYSIZE - i -1];
    }

    ForceZero(p, sizeof(p));
    ForceZero(k, sizeof(k));
    ForceZero(o, sizeof(o));

    return ret;
}


/* curve25519 uses a serialized string for key representation */
int wc_curve25519_export_public(curve25519_key* key, byte* out, word32* outLen)
{
    word32 keySz;

    if (key == NULL || out == NULL || outLen == NULL)
        return BAD_FUNC_ARG;

    /* check size of outgoing key */
    keySz  = wc_curve25519_size(key);

    /* copy in public key */
    XMEMCPY(out, key->p.point, keySz);
    *outLen = keySz;

    return 0;
}

/* import curve25519 public key
   return 0 on success */
int wc_curve25519_import_public(const byte* in, word32 inLen,
                                curve25519_key* key)
{
    word32 keySz;

    /* sanity check */
    if (key == NULL || in == NULL)
        return ECC_BAD_ARG_E;

    /* check size of incoming keys */
    keySz = wc_curve25519_size(key);
    if (inLen != keySz)
       return ECC_BAD_ARG_E;

    XMEMCPY(key->p.point, in, inLen);

    key->dp = &curve25519_sets[0];

    return 0;
}


/* export curve25519 private key only raw, outLen is in/out size
   return 0 on success */
int wc_curve25519_export_private_raw(curve25519_key* key, byte* out,
                                     word32* outLen)
{
    word32 keySz;

    /* sanity check */
    if (key == NULL || out == NULL || outLen == NULL)
        return ECC_BAD_ARG_E;

    keySz = wc_curve25519_size(key);
    *outLen = keySz;
    XMEMSET(out, 0, keySz);
    XMEMCPY(out, key->k.point, keySz);

    return 0;
}


/* curve25519 private key import.
   Public key to match private key needs to be imported too */
int wc_curve25519_import_private_raw(const byte* priv, word32 privSz,
                             const byte* pub, word32 pubSz, curve25519_key* key)
{
    int ret = 0;
    word32 keySz;

    /* sanity check */
    if (key == NULL || priv == NULL || pub == NULL)
        return ECC_BAD_ARG_E;

    /* check size of incoming keys */
    keySz = wc_curve25519_size(key);
    if (privSz != keySz || pubSz != keySz)
       return ECC_BAD_ARG_E;

    XMEMCPY(key->k.point, priv, privSz);
    XMEMCPY(key->p.point, pub, pubSz);

    return ret;
}


int wc_curve25519_init(curve25519_key* key)
{
    word32 keySz;

    if (key == NULL)
       return ECC_BAD_ARG_E;

    /* currently the format for curve25519 */
    key->dp = &curve25519_sets[0];
    keySz   = key->dp->size;

    XMEMSET(key->k.point, 0, keySz);
    XMEMSET(key->p.point, 0, keySz);

    return 0;
}


/* Clean the memory of a key */
void wc_curve25519_free(curve25519_key* key)
{
   if (key == NULL)
       return;

   key->dp = NULL;
   ForceZero(key->p.point, sizeof(key->p.point));
   ForceZero(key->k.point, sizeof(key->k.point));
}


/* get key size */
int wc_curve25519_size(curve25519_key* key)
{
    if (key == NULL) return 0;

    return key->dp->size;
}

#endif /*HAVE_CURVE25519*/

