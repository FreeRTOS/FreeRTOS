/* crypto.c
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


/* Implements Microchip CRYPTO API layer */



#include "crypto.h"

#include <cyassl/ctaocrypt/settings.h>

#include <cyassl/ctaocrypt/md5.h>
#include <cyassl/ctaocrypt/sha.h>
#include <cyassl/ctaocrypt/sha256.h>
#include <cyassl/ctaocrypt/sha512.h>
#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/compress.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/aes.h>
#include <cyassl/ctaocrypt/rsa.h>
#include <cyassl/ctaocrypt/ecc.h>
#include <cyassl/ctaocrypt/error-crypt.h>


/* Initialize MD5 */
int CRYPT_MD5_Initialize(CRYPT_MD5_CTX* md5)
{
    typedef char md5_test[sizeof(CRYPT_MD5_CTX) >= sizeof(Md5) ? 1 : -1];
    (void)sizeof(md5_test);

    if (md5 == NULL)
        return BAD_FUNC_ARG;

    InitMd5((Md5*)md5);

    return 0;
}


/* Add data to MD5 */
int CRYPT_MD5_DataAdd(CRYPT_MD5_CTX* md5, const unsigned char* input,
                      unsigned int sz)
{
    if (md5 == NULL || input == NULL)
        return BAD_FUNC_ARG;

    Md5Update((Md5*)md5, input, sz);

    return 0;
}


/* Get MD5 Final into digest */
int CRYPT_MD5_Finalize(CRYPT_MD5_CTX* md5, unsigned char* digest)
{
    if (md5 == NULL || digest == NULL)
        return BAD_FUNC_ARG;

    Md5Final((Md5*)md5, digest);

    return 0;
}


/* Initialize SHA */
int CRYPT_SHA_Initialize(CRYPT_SHA_CTX* sha)
{
    typedef char sha_test[sizeof(CRYPT_SHA_CTX) >= sizeof(Sha) ? 1 : -1];
    (void)sizeof(sha_test);

    if (sha == NULL)
        return BAD_FUNC_ARG;

    return InitSha((Sha*)sha);
}


/* Add data to SHA */
int CRYPT_SHA_DataAdd(CRYPT_SHA_CTX* sha, const unsigned char* input,
                       unsigned int sz)
{
    if (sha == NULL || input == NULL)
        return BAD_FUNC_ARG;

    return ShaUpdate((Sha*)sha, input, sz);
}


/* Get SHA Final into digest */
int CRYPT_SHA_Finalize(CRYPT_SHA_CTX* sha, unsigned char* digest)
{
    if (sha == NULL || digest == NULL)
        return BAD_FUNC_ARG;

    return ShaFinal((Sha*)sha, digest);
}


/* Initialize SHA-256 */
int CRYPT_SHA256_Initialize(CRYPT_SHA256_CTX* sha256)
{
    typedef char sha_test[sizeof(CRYPT_SHA256_CTX) >= sizeof(Sha256) ? 1 : -1];
    (void)sizeof(sha_test);

    if (sha256 == NULL)
        return BAD_FUNC_ARG;

    return InitSha256((Sha256*)sha256);
}


/* Add data to SHA-256 */
int CRYPT_SHA256_DataAdd(CRYPT_SHA256_CTX* sha256, const unsigned char* input,
                         unsigned int sz)
{
    if (sha256 == NULL || input == NULL)
        return BAD_FUNC_ARG;

    return Sha256Update((Sha256*)sha256, input, sz);
}


/* Get SHA-256 Final into digest */
int CRYPT_SHA256_Finalize(CRYPT_SHA256_CTX* sha256, unsigned char* digest)
{
    if (sha256 == NULL || digest == NULL)
        return BAD_FUNC_ARG;

    return Sha256Final((Sha256*)sha256, digest);
}


/* Initialize SHA-384 */
int CRYPT_SHA384_Initialize(CRYPT_SHA384_CTX* sha384)
{
    typedef char sha_test[sizeof(CRYPT_SHA384_CTX) >= sizeof(Sha384) ? 1 : -1];
    (void)sizeof(sha_test);

    if (sha384 == NULL)
        return BAD_FUNC_ARG;

    return InitSha384((Sha384*)sha384);
}


/* Add data to SHA-384 */
int CRYPT_SHA384_DataAdd(CRYPT_SHA384_CTX* sha384, const unsigned char* input,
                         unsigned int sz)
{
    if (sha384 == NULL || input == NULL)
        return BAD_FUNC_ARG;

    return Sha384Update((Sha384*)sha384, input, sz);
}


/* Get SHA-384 Final into digest */
int CRYPT_SHA384_Finalize(CRYPT_SHA384_CTX* sha384, unsigned char* digest)
{
    if (sha384 == NULL || digest == NULL)
        return BAD_FUNC_ARG;

    return Sha384Final((Sha384*)sha384, digest);
}


/* Initialize SHA-512 */
int CRYPT_SHA512_Initialize(CRYPT_SHA512_CTX* sha512)
{
    typedef char sha_test[sizeof(CRYPT_SHA512_CTX) >= sizeof(Sha512) ? 1 : -1];
    (void)sizeof(sha_test);

    if (sha512 == NULL)
        return BAD_FUNC_ARG;

    return InitSha512((Sha512*)sha512);
}


/* Add data to SHA-512 */
int CRYPT_SHA512_DataAdd(CRYPT_SHA512_CTX* sha512, const unsigned char* input,
                         unsigned int sz)
{
    if (sha512 == NULL || input == NULL)
        return BAD_FUNC_ARG;

    return Sha512Update((Sha512*)sha512, input, sz);
}


/* Get SHA-512 Final into digest */
int CRYPT_SHA512_Finalize(CRYPT_SHA512_CTX* sha512, unsigned char* digest)
{
    if (sha512 == NULL || digest == NULL)
        return BAD_FUNC_ARG;

    return Sha512Final((Sha512*)sha512, digest);
}


/* Set HMAC key with type */
int CRYPT_HMAC_SetKey(CRYPT_HMAC_CTX* hmac, int type, const unsigned char* key,
                      unsigned int sz)
{
    typedef char hmac_test[sizeof(CRYPT_HMAC_CTX) >= sizeof(Hmac) ? 1 : -1];
    (void)sizeof(hmac_test);

    if (hmac == NULL || key == NULL)
        return BAD_FUNC_ARG;

    if (type != CRYPT_HMAC_SHA && type != CRYPT_HMAC_SHA256 &&
        type != CRYPT_HMAC_SHA384 && type != CRYPT_HMAC_SHA512) {
        return BAD_FUNC_ARG;  /* bad hmac type */
    }

    return HmacSetKey((Hmac*)hmac, type, key, sz);
}


int CRYPT_HMAC_DataAdd(CRYPT_HMAC_CTX* hmac, const unsigned char* input,
                       unsigned int sz)
{
    if (hmac == NULL || input == NULL)
        return BAD_FUNC_ARG;

    return HmacUpdate((Hmac*)hmac, input, sz);
}


/* Get HMAC Final into digest */
int CRYPT_HMAC_Finalize(CRYPT_HMAC_CTX* hmac, unsigned char* digest)
{
    if (hmac == NULL || digest == NULL)
        return BAD_FUNC_ARG;

    return HmacFinal((Hmac*)hmac, digest);
}


/* Huffman Compression, set flag to do static, otherwise dynamic */
/* return compressed size, otherwise < 0 for error */
int CRYPT_HUFFMAN_Compress(unsigned char* out, unsigned int outSz,
                           const unsigned char* in, unsigned int inSz,
                           unsigned int flags)
{
    if (out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return Compress(out, outSz, in, inSz, flags);
}


/* Huffman DeCompression, self determines type */
/* return decompressed size, otherwise < 0 for error */
int CRYPT_HUFFMAN_DeCompress(unsigned char* out, unsigned int outSz,
                             const unsigned char* in, unsigned int inSz)
{
    if (out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return DeCompress(out, outSz, in, inSz);
}


/* RNG Initialize, < 0 on error */
int CRYPT_RNG_Initialize(CRYPT_RNG_CTX* rng)
{
    typedef char rng_test[sizeof(CRYPT_RNG_CTX) >= sizeof(RNG) ? 1 : -1];
    (void)sizeof(rng_test);

    if (rng == NULL)
        return BAD_FUNC_ARG;

    return InitRng((RNG*)rng);
}


/* RNG Get single bytes, < 0 on error */
int CRYPT_RNG_Get(CRYPT_RNG_CTX* rng, unsigned char* b)
{
    if (rng == NULL || b == NULL)
        return BAD_FUNC_ARG;

    return RNG_GenerateByte((RNG*)rng, (byte*)b);
}


/* RNG Block Generation of sz bytes, < 0 on error */
int CRYPT_RNG_BlockGenerate(CRYPT_RNG_CTX* rng, unsigned char* b,
                            unsigned int sz)
{
    if (rng == NULL || b == NULL)
        return BAD_FUNC_ARG;

    return RNG_GenerateBlock((RNG*)rng, b, sz);
}


/* Triple DES Key Set, may have iv, will have direction */
int CRYPT_TDES_KeySet(CRYPT_TDES_CTX* tdes, const unsigned char* key,
                      const unsigned char* iv, int dir)
{
    typedef char tdes_test[sizeof(CRYPT_TDES_CTX) >= sizeof(Des3) ? 1 : -1];
    (void)sizeof(tdes_test);

    if (tdes == NULL || key == NULL)
        return BAD_FUNC_ARG;

    return Des3_SetKey((Des3*)tdes, key, iv, dir);
}


/* Triple DES Iv Set, sometimes added later */
int CRYPT_TDES_IvSet(CRYPT_TDES_CTX* tdes, const unsigned char* iv)
{
    if (tdes == NULL || iv == NULL)
        return BAD_FUNC_ARG;

    return Des3_SetIV((Des3*)tdes, iv);
}


/* Triple DES CBC Encrypt */
int CRYPT_TDES_CBC_Encrypt(CRYPT_TDES_CTX* tdes, unsigned char* out,
                           const unsigned char* in, unsigned int inSz)
{
    if (tdes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return Des3_CbcEncrypt((Des3*)tdes, out, in, inSz);
}


/* Triple DES CBC Decrypt */
int CRYPT_TDES_CBC_Decrypt(CRYPT_TDES_CTX* tdes, unsigned char* out,
                           const unsigned char* in, unsigned int inSz)
{
    if (tdes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return Des3_CbcDecrypt((Des3*)tdes, out, in, inSz);
}


/* AES Key Set, may have iv, will have direction */
int CRYPT_AES_KeySet(CRYPT_AES_CTX* aes, const unsigned char* key,
                     unsigned int keyLen, const unsigned char* iv, int dir)
{
    typedef char aes_test[sizeof(CRYPT_AES_CTX) >= sizeof(Aes) ? 1 : -1];
    (void)sizeof(aes_test);

    if (aes == NULL || key == NULL)
        return BAD_FUNC_ARG;

    return AesSetKey((Aes*)aes, key, keyLen, iv, dir);
}


/* AES Iv Set, sometimes added later */
int CRYPT_AES_IvSet(CRYPT_AES_CTX* aes, const unsigned char* iv)
{
    if (aes == NULL || iv == NULL)
        return BAD_FUNC_ARG;

    return AesSetIV((Aes*)aes, iv);
}


/* AES CBC Encrypt */
int CRYPT_AES_CBC_Encrypt(CRYPT_AES_CTX* aes, unsigned char* out,
                          const unsigned char* in, unsigned int inSz)
{
    if (aes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return AesCbcEncrypt((Aes*)aes, out, in, inSz);
}


/* AES CBC Decrypt */
int CRYPT_AES_CBC_Decrypt(CRYPT_AES_CTX* aes, unsigned char* out,
                          const unsigned char* in, unsigned int inSz)
{
    if (aes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return AesCbcDecrypt((Aes*)aes, out, in, inSz);
}


/* AES CTR Encrypt (used for decrypt too, with ENCRYPT key setup) */
int CRYPT_AES_CTR_Encrypt(CRYPT_AES_CTX* aes, unsigned char* out,
                          const unsigned char* in, unsigned int inSz)
{
    if (aes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    AesCtrEncrypt((Aes*)aes, out, in, inSz);

    return 0;
}


/* AES Direct mode encrypt, one block at a time */
int CRYPT_AES_DIRECT_Encrypt(CRYPT_AES_CTX* aes, unsigned char* out,
                             const unsigned char* in)
{
    if (aes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    AesEncryptDirect((Aes*)aes, out, in);

    return 0;
}


/* AES Direct mode decrypt, one block at a time */
int CRYPT_AES_DIRECT_Decrypt(CRYPT_AES_CTX* aes, unsigned char* out,
                             const unsigned char* in)
{
    if (aes == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    AesDecryptDirect((Aes*)aes, out, in);

    return 0;
}


/* RSA Initialize */
int CRYPT_RSA_Initialize(CRYPT_RSA_CTX* rsa)
{
    if (rsa == NULL)
        return BAD_FUNC_ARG;

    rsa->holder = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL, DYNAMIC_TYPE_RSA);
    if (rsa->holder == NULL)
        return -1;

    return InitRsaKey((RsaKey*)rsa->holder, NULL);
}


/* RSA Free resources */
int CRYPT_RSA_Free(CRYPT_RSA_CTX* rsa)
{
    if (rsa == NULL)
        return BAD_FUNC_ARG;

    FreeRsaKey((RsaKey*)rsa->holder);
    XFREE(rsa->holder, NULL, DYNAMIC_TYPE_RSA);
    rsa->holder = NULL;

    return 0;
}


/* RSA Public key decode ASN.1 */
int CRYPT_RSA_PublicKeyDecode(CRYPT_RSA_CTX* rsa, const unsigned char* in,
                              unsigned int inSz)
{
    unsigned int idx = 0;
    (void)idx;

    if (rsa == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return RsaPublicKeyDecode(in, &idx, (RsaKey*)rsa->holder, inSz);
}


/* RSA Private key decode ASN.1 */
int CRYPT_RSA_PrivateKeyDecode(CRYPT_RSA_CTX* rsa, const unsigned char* in,
                               unsigned int inSz)
{
    unsigned int idx = 0;
    (void)idx;

    if (rsa == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return RsaPrivateKeyDecode(in, &idx, (RsaKey*)rsa->holder, inSz);
}


/* RSA Public Encrypt */
int CRYPT_RSA_PublicEncrypt(CRYPT_RSA_CTX* rsa, unsigned char* out,
                            unsigned int outSz, const unsigned char* in,
                            unsigned int inSz, CRYPT_RNG_CTX* rng)
{
    if (rsa == NULL || in == NULL || out == NULL || rng == NULL)
        return BAD_FUNC_ARG;

    return RsaPublicEncrypt(in, inSz, out, outSz, (RsaKey*)rsa->holder,
                            (RNG*)rng);
}


/* RSA Private Decrypt */
int CRYPT_RSA_PrivateDecrypt(CRYPT_RSA_CTX* rsa, unsigned char* out,
                             unsigned int outSz, const unsigned char* in,
                             unsigned int inSz)
{
    if (rsa == NULL || in == NULL || out == NULL)
        return BAD_FUNC_ARG;

    return RsaPrivateDecrypt(in, inSz, out, outSz, (RsaKey*)rsa->holder);
}


/* RSA Get Encrypt size helper */
int CRYPT_RSA_EncryptSizeGet(CRYPT_RSA_CTX* rsa) 
{
    if (rsa == NULL)
        return BAD_FUNC_ARG;

    return RsaEncryptSize((RsaKey*)rsa->holder);
}    


/* ECC init */
int CRYPT_ECC_Initialize(CRYPT_ECC_CTX* ecc)
{
    if (ecc == NULL)
        return BAD_FUNC_ARG;

    ecc->holder = (ecc_key*)XMALLOC(sizeof(ecc_key), NULL, DYNAMIC_TYPE_ECC);
    if (ecc->holder == NULL)
        return -1;

    ecc_init((ecc_key*)ecc->holder);

    return 0;
}


/* ECC free resources */
int CRYPT_ECC_Free(CRYPT_ECC_CTX* ecc)
{
    if (ecc == NULL)
        return BAD_FUNC_ARG;

    ecc_free((ecc_key*)ecc->holder);
    XFREE(ecc->holder, NULL, DYNAMIC_TYPE_ECC);
    ecc->holder = NULL;

    return 0;
}


/* ECC Public x963 Export */
int CRYPT_ECC_PublicExport(CRYPT_ECC_CTX* ecc, unsigned char* out,
                           unsigned int outSz, unsigned int* usedSz)
{
    int          ret;
    unsigned int inOut = outSz;

    if (ecc == NULL || out == NULL)
        return BAD_FUNC_ARG;

    ret = ecc_export_x963((ecc_key*)ecc->holder, out, &inOut);
    *usedSz = inOut;

    return ret;
}


/* ECC Public x963 Import */
int CRYPT_ECC_PublicImport(CRYPT_ECC_CTX* ecc, const unsigned char* in,
                           unsigned int inSz)
{
    if (ecc == NULL || in == NULL)
        return BAD_FUNC_ARG;

    return ecc_import_x963(in, inSz, (ecc_key*)ecc->holder);
}


/* ECC Private x963 Import */
int CRYPT_ECC_PrivateImport(CRYPT_ECC_CTX* ecc, const unsigned char* priv,
         unsigned int privSz, const unsigned char* pub, unsigned int pubSz)
{
    if (ecc == NULL || priv == NULL || pub == NULL)
        return BAD_FUNC_ARG;

    return ecc_import_private_key(priv, privSz, pub, pubSz,
                                 (ecc_key*)ecc->holder);
}


/* ECC DHE Make key */
int CRYPT_ECC_DHE_KeyMake(CRYPT_ECC_CTX* ecc, CRYPT_RNG_CTX* rng, int keySz)
{
    if (ecc == NULL || rng == NULL)
        return BAD_FUNC_ARG;

    return ecc_make_key((RNG*)rng, keySz, (ecc_key*)ecc->holder);
}


/* ECC DHE Make shared secret with our private and peer public */
int CRYPT_ECC_DHE_SharedSecretMake(CRYPT_ECC_CTX* priv, CRYPT_ECC_CTX* pub,
                  unsigned char* out, unsigned int outSz, unsigned int* usedSz)
{
    int ret;
    unsigned int inOut = outSz;

    if (priv == NULL || pub == NULL || out == NULL || usedSz == NULL)
        return BAD_FUNC_ARG;

    ret = ecc_shared_secret((ecc_key*)priv->holder, (ecc_key*)pub->holder,
                            out, &inOut);
    *usedSz = inOut;

    return ret;
}


/* ECC DSA Hash Sign */
int CRYPT_ECC_DSA_HashSign(CRYPT_ECC_CTX* ecc, CRYPT_RNG_CTX* rng,
                           unsigned char* sig, unsigned int sigSz,
                           unsigned int* usedSz, const unsigned char* in,
                           unsigned int inSz)
{
    int ret;
    unsigned int inOut = sigSz;

    if (ecc == NULL || rng == NULL || sig == NULL || usedSz == NULL ||
                                                                in == NULL)
        return BAD_FUNC_ARG;

    ret = ecc_sign_hash(in, inSz, sig, &inOut, (RNG*)rng,
                       (ecc_key*)ecc->holder);
    *usedSz = inOut;

    return ret;
}


/* ECC DSA Hash Verify */
int CRYPT_ECC_DSA_HashVerify(CRYPT_ECC_CTX* ecc, const unsigned char* sig,
                             unsigned int sigSz, unsigned char* hash,
                             unsigned int hashSz, int* status)
{
    if (ecc == NULL || sig == NULL || hash == NULL || status == NULL)
        return BAD_FUNC_ARG;

    return ecc_verify_hash(sig, sigSz, hash, hashSz, status,
                          (ecc_key*)ecc->holder);
}


/* ECC get key size helper */
int CRYPT_ECC_KeySizeGet(CRYPT_ECC_CTX* ecc)
{
    if (ecc == NULL)
        return BAD_FUNC_ARG;

    return ecc_size((ecc_key*)ecc->holder);
}


/* ECC get signature size helper */
int CRYPT_ECC_SignatureSizeGet(CRYPT_ECC_CTX* ecc)
{
    if (ecc == NULL)
        return BAD_FUNC_ARG;

    return ecc_sig_size((ecc_key*)ecc->holder);
}


/* Save error string from err to str which needs to be >= 80 chars */
int CRYPT_ERROR_StringGet(int err, char* str)
{
    if (str == NULL)
        return BAD_FUNC_ARG;

    CTaoCryptErrorString(err, str);

    return 0;
}

