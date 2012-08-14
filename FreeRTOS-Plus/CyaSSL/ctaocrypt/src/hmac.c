/* hmac.c
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

#ifndef NO_HMAC

#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/error.h>


static int InitHmac(Hmac* hmac, int type)
{
    hmac->innerHashKeyed = 0;
    hmac->macType = (byte)type;

    if (!(type == MD5 || type == SHA || type == SHA256 || type == SHA384))
        return BAD_FUNC_ARG;

    if (type == MD5)
        InitMd5(&hmac->hash.md5);
    else if (type == SHA)
        InitSha(&hmac->hash.sha);
#ifndef NO_SHA256
    else if (type == SHA256)
        InitSha256(&hmac->hash.sha256);
#endif
#ifdef CYASSL_SHA384
    else if (type == SHA384)
        InitSha384(&hmac->hash.sha384);
#endif

    return 0;
}


void HmacSetKey(Hmac* hmac, int type, const byte* key, word32 length)
{
    byte*  ip = (byte*) hmac->ipad;
    byte*  op = (byte*) hmac->opad;
    word32 i, hmac_block_size = MD5_BLOCK_SIZE;

    InitHmac(hmac, type);

    if (hmac->macType == MD5) {
        if (length <= MD5_BLOCK_SIZE) {
            XMEMCPY(ip, key, length);
        }
        else {
            Md5Update(&hmac->hash.md5, key, length);
            Md5Final(&hmac->hash.md5, ip);
            length = MD5_DIGEST_SIZE;
        }
    }
    else if (hmac->macType == SHA) {
		hmac_block_size = SHA_BLOCK_SIZE;
        if (length <= SHA_BLOCK_SIZE) {
            XMEMCPY(ip, key, length);
        }
        else {
            ShaUpdate(&hmac->hash.sha, key, length);
            ShaFinal(&hmac->hash.sha, ip);
            length = SHA_DIGEST_SIZE;
        }
    }
#ifndef NO_SHA256
    else if (hmac->macType == SHA256) {
		hmac_block_size = SHA256_BLOCK_SIZE;
        if (length <= SHA256_BLOCK_SIZE) {
            XMEMCPY(ip, key, length);
        }
        else {
            Sha256Update(&hmac->hash.sha256, key, length);
            Sha256Final(&hmac->hash.sha256, ip);
            length = SHA256_DIGEST_SIZE;
        }
    }
#endif
#ifdef CYASSL_SHA384
    else if (hmac->macType == SHA384) {
        hmac_block_size = SHA384_BLOCK_SIZE;
        if (length <= SHA384_BLOCK_SIZE) {
            XMEMCPY(ip, key, length);
        }
        else {
            Sha384Update(&hmac->hash.sha384, key, length);
            Sha384Final(&hmac->hash.sha384, ip);
            length = SHA384_DIGEST_SIZE;
        }
    }
#endif
    XMEMSET(ip + length, 0, hmac_block_size - length);

    for(i = 0; i < hmac_block_size; i++) {
        op[i] = ip[i] ^ OPAD;
        ip[i] ^= IPAD;
    }
}


static void HmacKeyInnerHash(Hmac* hmac)
{
    if (hmac->macType == MD5)
        Md5Update(&hmac->hash.md5, (byte*) hmac->ipad, MD5_BLOCK_SIZE);
    else if (hmac->macType == SHA)
        ShaUpdate(&hmac->hash.sha, (byte*) hmac->ipad, SHA_BLOCK_SIZE);
#ifndef NO_SHA256
    else if (hmac->macType == SHA256)
        Sha256Update(&hmac->hash.sha256, (byte*) hmac->ipad, SHA256_BLOCK_SIZE);
#endif
#ifdef CYASSL_SHA384
    else if (hmac->macType == SHA384)
        Sha384Update(&hmac->hash.sha384, (byte*) hmac->ipad, SHA384_BLOCK_SIZE);
#endif

    hmac->innerHashKeyed = 1;
}


void HmacUpdate(Hmac* hmac, const byte* msg, word32 length)
{
    if (!hmac->innerHashKeyed)
        HmacKeyInnerHash(hmac);

    if (hmac->macType == MD5)
        Md5Update(&hmac->hash.md5, msg, length);
    else if (hmac->macType == SHA)
        ShaUpdate(&hmac->hash.sha, msg, length);
#ifndef NO_SHA256
    else if (hmac->macType == SHA256)
        Sha256Update(&hmac->hash.sha256, msg, length);
#endif
#ifdef CYASSL_SHA384
    else if (hmac->macType == SHA384)
        Sha384Update(&hmac->hash.sha384, msg, length);
#endif

}


void HmacFinal(Hmac* hmac, byte* hash)
{
    if (!hmac->innerHashKeyed)
        HmacKeyInnerHash(hmac);

    if (hmac->macType == MD5) {
        Md5Final(&hmac->hash.md5, (byte*) hmac->innerHash);

        Md5Update(&hmac->hash.md5, (byte*) hmac->opad, MD5_BLOCK_SIZE);
        Md5Update(&hmac->hash.md5, (byte*) hmac->innerHash, MD5_DIGEST_SIZE);

        Md5Final(&hmac->hash.md5, hash);
    }
    else if (hmac->macType == SHA) {
        ShaFinal(&hmac->hash.sha, (byte*) hmac->innerHash);

        ShaUpdate(&hmac->hash.sha, (byte*) hmac->opad, SHA_BLOCK_SIZE);
        ShaUpdate(&hmac->hash.sha, (byte*) hmac->innerHash, SHA_DIGEST_SIZE);

        ShaFinal(&hmac->hash.sha, hash);
    }
#ifndef NO_SHA256
    else if (hmac->macType == SHA256) {
        Sha256Final(&hmac->hash.sha256, (byte*) hmac->innerHash);

        Sha256Update(&hmac->hash.sha256, (byte*) hmac->opad, SHA256_BLOCK_SIZE);
        Sha256Update(&hmac->hash.sha256, (byte*) hmac->innerHash,
                     SHA256_DIGEST_SIZE);

        Sha256Final(&hmac->hash.sha256, hash);
    }
#endif
#ifdef CYASSL_SHA384
    else if (hmac->macType == SHA384) {
        Sha384Final(&hmac->hash.sha384, (byte*) hmac->innerHash);

        Sha384Update(&hmac->hash.sha384, (byte*) hmac->opad, SHA384_BLOCK_SIZE);
        Sha384Update(&hmac->hash.sha384, (byte*) hmac->innerHash,
                     SHA384_DIGEST_SIZE);

        Sha384Final(&hmac->hash.sha384, hash);
    }
#endif

    hmac->innerHashKeyed = 0;
}


#endif /* NO_HMAC */

