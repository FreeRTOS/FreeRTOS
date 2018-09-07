/* pic32mz-hash.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_PIC32MZ_HASH

#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/md5.h>
#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/sha256.h>

#include <wolfssl/wolfcrypt/port/pic32/pic32mz-crypt.h>

#if !defined(NO_MD5) && !defined(NO_SHA) && !defined(NO_SHA256)

static uint8_t dataBuffer[PIC32MZ_MAX_BD][PIC32_BLOCK_SIZE] __attribute__((aligned (4), coherent));

static void reset_engine(pic32mz_desc *desc, int algo)
{
    int i;
    pic32mz_desc* uc_desc = KVA0_TO_KVA1(desc);

    CECON = 1 << 6;
    while (CECON);

    /* Make sure everything is clear first before we make settings. */
    XMEMSET((void *)&uc_desc->sa, 0, sizeof(uc_desc->sa));

    /* Set up the security association */
    uc_desc->sa.SA_CTRL.ALGO = algo ;
    uc_desc->sa.SA_CTRL.LNC = 1;
    uc_desc->sa.SA_CTRL.FB = 1;
    uc_desc->sa.SA_CTRL.ENCTYPE = 1;
    uc_desc->sa.SA_CTRL.LOADIV = 1;

    /* Set up the buffer descriptor */
    uc_desc->err = 0 ;
    for (i = 0; i < PIC32MZ_MAX_BD; i++)
    {
        XMEMSET((void *)&uc_desc->bd[i], 0, sizeof(uc_desc->bd[i]));
        uc_desc->bd[i].BD_CTRL.LAST_BD = 1;
        uc_desc->bd[i].BD_CTRL.LIFM = 1;
        uc_desc->bd[i].BD_CTRL.PKT_INT_EN = 1;
        uc_desc->bd[i].SA_ADDR = KVA_TO_PA(&uc_desc->sa);
        uc_desc->bd[i].SRCADDR = KVA_TO_PA(&dataBuffer[i]);
        if (PIC32MZ_MAX_BD > i+1)
            uc_desc->bd[i].NXTPTR = KVA_TO_PA(&uc_desc->bd[i+1]);
        else
            uc_desc->bd[i].NXTPTR = KVA_TO_PA(&uc_desc->bd[0]);
        XMEMSET((void *)&dataBuffer[i], 0, PIC32_BLOCK_SIZE);
    }
    uc_desc->bd[0].BD_CTRL.SA_FETCH_EN = 1; // Fetch the security association on the first BD
    desc->dbPtr = 0;
    desc->currBd = 0;
    desc->msgSize = 0;
    desc->processed = 0;
    CEBDPADDR = KVA_TO_PA(&(desc->bd[0]));

    CEPOLLCON = 10;

    CECON = 0x27;
}

#define PIC32MZ_IF_RAM(addr) (KVA_TO_PA(addr) < 0x80000)

static void update_data_size(pic32mz_desc *desc, word32 msgSize)
{
    desc->msgSize = msgSize;
}

static void update_engine(pic32mz_desc *desc, const char *input, word32 len,
                    word32 *hash)
{
   int total ;
    pic32mz_desc    *uc_desc = KVA0_TO_KVA1(desc);

    uc_desc->bd[desc->currBd].UPDPTR = KVA_TO_PA(hash);
    // Add the data to the current buffer. If the buffer fills, start processing it
    // and fill the next one.
    while (len)
    {
        // If the engine is processing the current BD, spin.
//        if (uc_desc->bd[desc->currBd].BD_CTRL.DESC_EN)
//            continue;
        if (desc->msgSize)
        {
            // If we've been given the message size, we can process along the
            // way.
            // Enable the current buffer descriptor if it is full.
            if (desc->dbPtr >= PIC32_BLOCK_SIZE)
            {
                // Wrap up the buffer descriptor and enable it so the engine can process
                uc_desc->bd[desc->currBd].MSGLEN = desc->msgSize;
                uc_desc->bd[desc->currBd].BD_CTRL.BUFLEN = desc->dbPtr;
                uc_desc->bd[desc->currBd].BD_CTRL.LAST_BD = 0;
                uc_desc->bd[desc->currBd].BD_CTRL.LIFM = 0;
                //SYS_DEVCON_DataCacheClean((word32)desc, sizeof(pic32mz_desc));
                uc_desc->bd[desc->currBd].BD_CTRL.DESC_EN = 1;
                // Move to the next buffer descriptor, or wrap around.
                desc->currBd++;
                if (desc->currBd >= PIC32MZ_MAX_BD)
                    desc->currBd = 0;
                // Wait until the engine has processed the new BD.
                while (uc_desc->bd[desc->currBd].BD_CTRL.DESC_EN);
                uc_desc->bd[desc->currBd].UPDPTR = KVA_TO_PA(hash);
                desc->dbPtr = 0;
            }
            if (!PIC32MZ_IF_RAM(input)) // If we're inputting from flash, let the BD have the address and max the buffer size
            {
                uc_desc->bd[desc->currBd].SRCADDR = KVA_TO_PA(input);
                total = (len > PIC32MZ_MAX_BLOCK ? PIC32MZ_MAX_BLOCK : len);
                desc->dbPtr = total;
                len -= total;
                input += total;
            }
            else
            {
                if (len > PIC32_BLOCK_SIZE - desc->dbPtr)
                {
                    // We have more data than can be put in the buffer. Fill what we can.
                    total = PIC32_BLOCK_SIZE - desc->dbPtr;
                    XMEMCPY(&dataBuffer[desc->currBd][desc->dbPtr], input, total);
                    len -= total;
                    desc->dbPtr = PIC32_BLOCK_SIZE;
                    input += total;
                }
                else
                {
                    // Fill up what we have, but don't turn on the engine.
                    XMEMCPY(&dataBuffer[desc->currBd][desc->dbPtr], input, len);
                    desc->dbPtr += len;
                    len = 0;
                }
            }
        }
        else
        {
            // We have to buffer everything and keep track of how much has been
            // added in order to get a total size. If the buffer fills, we move
            // to the next one. If we try to add more when the last buffer is
            // full, we error out.
            if (desc->dbPtr == PIC32_BLOCK_SIZE)
            {
                // We filled the last BD buffer, so move on to the next one
                uc_desc->bd[desc->currBd].BD_CTRL.LAST_BD = 0;
                uc_desc->bd[desc->currBd].BD_CTRL.LIFM = 0;
                uc_desc->bd[desc->currBd].BD_CTRL.BUFLEN = PIC32_BLOCK_SIZE;
                desc->currBd++;
                uc_desc->bd[desc->currBd].UPDPTR = KVA_TO_PA(hash);
                desc->dbPtr = 0;
                if (desc->currBd >= PIC32MZ_MAX_BD)
                {
                    desc->err = 1;
                }
            }
            if (len > PIC32_BLOCK_SIZE - desc->dbPtr)
            {
                // We have more data than can be put in the buffer. Fill what we can.
                total = PIC32_BLOCK_SIZE - desc->dbPtr;
                XMEMCPY(&dataBuffer[desc->currBd][desc->dbPtr], input, total);
                len -= total;
                desc->processed += total;
                desc->dbPtr = PIC32_BLOCK_SIZE;
                input += total;
            }
            else
            {
                // Fill up what we have
                XMEMCPY(&dataBuffer[desc->currBd][desc->dbPtr], input, len);
                desc->dbPtr += len;
                desc->processed += len;
                len = 0;
            }
        }
    }
}

static void start_engine(pic32mz_desc *desc) {
    // Wrap up the last buffer descriptor and enable it
    int i ;
    int bufferLen ;
    pic32mz_desc *uc_desc = KVA0_TO_KVA1(desc);

    bufferLen = desc->dbPtr;
    if (bufferLen % 4)
        bufferLen = (bufferLen + 4) - (bufferLen % 4);
    uc_desc->bd[desc->currBd].BD_CTRL.BUFLEN = bufferLen;
    uc_desc->bd[desc->currBd].BD_CTRL.LAST_BD = 1;
    uc_desc->bd[desc->currBd].BD_CTRL.LIFM = 1;
    if (desc->msgSize == 0)
    {
        // We were not given the size, so now we have to go through every BD
        // and give it what will be processed, and enable them.
        for (i = desc->currBd; i >= 0; i--)
        {
            uc_desc->bd[i].MSGLEN = desc->processed;
            uc_desc->bd[i].BD_CTRL.DESC_EN = 1;
        }
    }
    else
    {
        uc_desc->bd[desc->currBd].BD_CTRL.DESC_EN = 1;
    }
}

void wait_engine(pic32mz_desc *desc, char *hash, int hash_sz) {
    unsigned int i;
    unsigned int *intptr;
    pic32mz_desc *uc_desc = KVA0_TO_KVA1(desc);
    enum {true = 1, false = 0} engineRunning = true;

    while (engineRunning)
    {
        engineRunning = false;
        for (i = 0; i < PIC32MZ_MAX_BD; i++)
            engineRunning = engineRunning || uc_desc->bd[i].BD_CTRL.DESC_EN;
    }
    XMEMCPY(hash, KVA0_TO_KVA1(hash), hash_sz) ;

    #ifdef DEBUG_CYASSL
    print_mem(KVA0_TO_KVA1(hash), hash_sz) ;
    print_mem(             hash , hash_sz) ;
    #endif
    for (i = 0, intptr = (unsigned int *)hash; i < hash_sz/sizeof(unsigned int);
                                                                  i++, intptr++)
    {
        *intptr = ntohl(*intptr);
    }
}

static int fillBuff(char *buff, int *bufflen, const char *data, int len, int blocksz)
{
    int room, copysz ;

    room = blocksz - *bufflen ;
    copysz = (len <= room) ? len : room ;
    XMEMCPY(buff, data, copysz) ;
    *bufflen += copysz ;
    return (*bufflen == blocksz) ? 1 : 0 ;
}

#endif

#ifndef NO_MD5
void wc_InitMd5(Md5* md5)
{
    WOLFSSL_ENTER("InitMd5\n") ;
    XMEMSET((void *)md5, 0xcc, sizeof(Md5)) ;
    XMEMSET((void *)KVA0_TO_KVA1(md5), 0xcc, sizeof(Md5)) ;
    reset_engine(&(md5->desc), PIC32_ALGO_MD5) ;

}

void wc_Md5Update(Md5* md5, const byte* data, word32 len)
{
     WOLFSSL_ENTER("Md5Update\n") ;
     update_engine(&(md5->desc), data, len, md5->digest) ;
}

void wc_Md5Final(Md5* md5, byte* hash)
{
     WOLFSSL_ENTER("Md5Final\n") ;
    start_engine(&(md5->desc)) ;
    wait_engine(&(md5->desc), (char *)md5->digest, MD5_HASH_SIZE) ;
    XMEMCPY(hash, md5->digest, MD5_HASH_SIZE) ;
    wc_InitMd5(md5);  /* reset state */
}

void Md5SizeSet(Md5* md5, word32 len)
{
    WOLFSSL_ENTER("Md5SizeSet\n");
    md5->desc.msgSize = len;
}
#endif

#ifndef NO_SHA
int wc_InitSha(Sha* sha)
{
    WOLFSSL_ENTER("InitSha\n") ;
    XMEMSET((void *)sha, 0xcc, sizeof(Sha)) ;
    XMEMSET((void *)KVA0_TO_KVA1(sha), 0xcc, sizeof(Sha)) ;
    reset_engine(&(sha->desc), PIC32_ALGO_SHA1) ;
    return 0;
}

int wc_ShaUpdate(Sha* sha, const byte* data, word32 len)
{
    WOLFSSL_ENTER("ShaUpdate\n") ;
    update_engine(&(sha->desc), data, len, sha->digest) ;
    return 0;
}

int wc_ShaFinal(Sha* sha, byte* hash)
{
    WOLFSSL_ENTER("ShaFinal\n") ;
    start_engine(&(sha->desc)) ;
    wait_engine(&(sha->desc), (char *)sha->digest, SHA1_HASH_SIZE) ;
    XMEMCPY(hash, sha->digest, SHA1_HASH_SIZE) ;

    wc_InitSha(sha);  /* reset state */
    return 0;
}

void ShaSizeSet(Sha* sha, word32 len)
{
    sha->desc.msgSize = len;
}
#endif /* NO_SHA */

#ifndef NO_SHA256
int wc_InitSha256(Sha256* sha256)
{
    WOLFSSL_ENTER("InitSha256\n") ;
    XMEMSET((void *)sha256, 0xcc, sizeof(Sha256)) ;
    XMEMSET((void *)KVA0_TO_KVA1(sha256), 0xcc, sizeof(Sha256)) ;
    reset_engine(&(sha256->desc), PIC32_ALGO_SHA256) ;
    return 0;
}

int wc_Sha256Update(Sha256* sha256, const byte* data, word32 len)
{
    WOLFSSL_ENTER("Sha256Update\n") ;
    update_engine(&(sha256->desc), data, len, sha256->digest) ;

    return 0;
}

int wc_Sha256Final(Sha256* sha256, byte* hash)
{
    WOLFSSL_ENTER("Sha256Final\n") ;
    start_engine(&(sha256->desc)) ;
    wait_engine(&(sha256->desc), (char *)sha256->digest, SHA256_HASH_SIZE) ;
    XMEMCPY(hash, sha256->digest, SHA256_HASH_SIZE) ;
    wc_InitSha256(sha256);  /* reset state */

    return 0;
}

void Sha256SizeSet(Sha256* sha256, word32 len)
{
    WOLFSSL_ENTER("Sha256SizeSet\n");
    sha256->desc.msgSize = len;
}

#endif /* NO_SHA256 */

#endif

