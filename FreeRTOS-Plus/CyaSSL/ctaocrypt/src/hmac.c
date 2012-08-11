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

    if (!(type == MD5 || type == SHA || type == SHA256))
        return BAD_FUNC_ARG;

    if (type == MD5)
        InitMd5(&hmac->hash.md5);
    else if (type == SHA)
        InitSha(&hmac->hash.sha);
#ifndef NO_SHA256
    else if (type == SHA256)
        InitSha256(&hmac->hash.sha256);
#endif

    return 0;
}


void HmacSetKey(Hmac* hmac, int type, const byte* key, word32 length)
{
    byte*  ip = (byte*) hmac->ipad;
    byte*  op = (byte*) hmac->opad;
    word32 i;

    InitHmac(hmac, type);

    if (length <= HMAC_BLOCK_SIZE)
        XMEMCPY(ip, key, length);
    else {
        if (hmac->macType == MD5) {
            Md5Update(&hmac->hash.md5, key, length);
            Md5Final(&hmac->hash.md5, ip);
            length = MD5_DIGEST_SIZE;
        }
        else if (hmac->macType == SHA) {
            ShaUpdate(&hmac->hash.sha, key, length);
            ShaFinal(&hmac->hash.sha, ip);
            length = SHA_DIGEST_SIZE;
        }
#ifndef NO_SHA256
        else if (hmac->macType == SHA256) {
            Sha256Update(&hmac->hash.sha256, key, length);
            Sha256Final(&hmac->hash.sha256, ip);
            length = SHA256_DIGEST_SIZE;
        }
#endif
    }
    XMEMSET(ip + length, 0, HMAC_BLOCK_SIZE - length);

    for(i = 0; i < HMAC_BLOCK_SIZE; i++) {
        op[i] = ip[i] ^ OPAD;
        ip[i] ^= IPAD;
    }
}


static void HmacKeyInnerHash(Hmac* hmac)
{
    if (hmac->macType == MD5)
        Md5Update(&hmac->hash.md5, (byte*) hmac->ipad, HMAC_BLOCK_SIZE);
    else if (hmac->macType == SHA)
        ShaUpdate(&hmac->hash.sha, (byte*) hmac->ipad, HMAC_BLOCK_SIZE);
#ifndef NO_SHA256
    else if (hmac->macType == SHA256)
        Sha256Update(&hmac->hash.sha256, (byte*) hmac->ipad, HMAC_BLOCK_SIZE);
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

}


void HmacFinal(Hmac* hmac, byte* hash)
{
    if (!hmac->innerHashKeyed)
        HmacKeyInnerHash(hmac);

    if (hmac->macType == MD5) {
        Md5Final(&hmac->hash.md5, (byte*) hmac->innerHash);

        Md5Update(&hmac->hash.md5, (byte*) hmac->opad, HMAC_BLOCK_SIZE);
        Md5Update(&hmac->hash.md5, (byte*) hmac->innerHash, MD5_DIGEST_SIZE);

        Md5Final(&hmac->hash.md5, hash);
    }
    else if (hmac->macType ==SHA) {
        ShaFinal(&hmac->hash.sha, (byte*) hmac->innerHash);

        ShaUpdate(&hmac->hash.sha, (byte*) hmac->opad, HMAC_BLOCK_SIZE);
        ShaUpdate(&hmac->hash.sha, (byte*) hmac->innerHash, SHA_DIGEST_SIZE);

        ShaFinal(&hmac->hash.sha, hash);
    }
#ifndef NO_SHA256
    else if (hmac->macType ==SHA256) {
        Sha256Final(&hmac->hash.sha256, (byte*) hmac->innerHash);

        Sha256Update(&hmac->hash.sha256, (byte*) hmac->opad, HMAC_BLOCK_SIZE);
        Sha256Update(&hmac->hash.sha256, (byte*) hmac->innerHash,
                     SHA256_DIGEST_SIZE);

        Sha256Final(&hmac->hash.sha256, hash);
    }
#endif

    hmac->innerHashKeyed = 0;
}


#endif /* NO_HMAC */

