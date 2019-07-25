/* des3.c
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

#ifndef NO_DES3

#include <wolfssl/wolfcrypt/des3.h>

#ifdef HAVE_FIPS
#ifdef HAVE_CAVIUM
    static int wc_Des3_CaviumSetKey(Des3* des3, const byte* key, const byte* iv);
    static int wc_Des3_CaviumCbcEncrypt(Des3* des3, byte* out, const byte* in,
                                      word32 length);
    static int wc_Des3_CaviumCbcDecrypt(Des3* des3, byte* out, const byte* in,
                                      word32 length);
#endif

int wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
{
    return Des_SetKey(des, key, iv, dir);
}


int wc_Des3_SetKey(Des3* des, const byte* key, const byte* iv, int dir)
{
    return Des3_SetKey_fips(des, key, iv, dir);
}


int wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    return Des_CbcEncrypt(des, out, in, sz);
}


int wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    return Des_CbcDecrypt(des, out, in, sz);
}


int wc_Des3_CbcEncrypt(Des3* des, byte* out, const byte* in, word32 sz)
{
    return Des3_CbcEncrypt_fips(des, out, in, sz);
}


int wc_Des3_CbcDecrypt(Des3* des, byte* out, const byte* in, word32 sz)
{
    return Des3_CbcDecrypt_fips(des, out, in, sz);
}


#ifdef WOLFSSL_DES_ECB

/* One block, compatibility only */
int wc_Des_EcbEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    return Des_EcbEncrypt(des, out, in, sz);
}

#endif /* WOLFSSL_DES_ECB */


void wc_Des_SetIV(Des* des, const byte* iv)
{
    Des_SetIV(des, iv);
}


int wc_Des_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                                                const byte* key, const byte* iv)
{
    return Des_CbcDecryptWithKey(out, in, sz, key, iv);
}


int wc_Des3_SetIV(Des3* des, const byte* iv)
{
    return Des3_SetIV_fips(des, iv);
}


int wc_Des3_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                                                const byte* key, const byte* iv)
{
    return Des3_CbcDecryptWithKey(out, in, sz, key, iv);
}


#ifdef HAVE_CAVIUM

/* Initiliaze Des3 for use with Nitrox device */
int wc_Des3_InitCavium(Des3* des3, int devId)
{
    return Des3_InitCavium(des3, devId);
}


/* Free Des3 from use with Nitrox device */
void wc_Des3_FreeCavium(Des3* des3)
{
    Des3_FreeCavium(des3);
}


#endif /* HAVE_CAVIUM */
#else /* build without fips */

#if defined(WOLFSSL_TI_CRYPT)
    #include <wolfcrypt/src/port/ti/ti-des3.c>
#else

#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif


#ifdef HAVE_CAVIUM
    static int wc_Des3_CaviumSetKey(Des3* des3, const byte* key, const byte* iv);
    static int wc_Des3_CaviumCbcEncrypt(Des3* des3, byte* out, const byte* in,
                                      word32 length);
    static int wc_Des3_CaviumCbcDecrypt(Des3* des3, byte* out, const byte* in,
                                      word32 length);
#endif




#ifdef STM32F2_CRYPTO
    /*
     * STM32F2 hardware DES/3DES support through the STM32F2 standard
     * peripheral library. Documentation located in STM32F2xx Standard
     * Peripheral Library document (See note in README).
     */
    #include "stm32f2xx.h"
		#include "stm32f2xx_cryp.h"

    int wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
    {
        word32 *dkey = des->key;

        XMEMCPY(dkey, key, 8);
        ByteReverseWords(dkey, dkey, 8);

        wc_Des_SetIV(des, iv);

        return 0;
    }

    int wc_Des3_SetKey(Des3* des, const byte* key, const byte* iv, int dir)
    {
        word32 *dkey1 = des->key[0];
        word32 *dkey2 = des->key[1];
        word32 *dkey3 = des->key[2];

        XMEMCPY(dkey1, key, 8);         /* set key 1 */
        XMEMCPY(dkey2, key + 8, 8);     /* set key 2 */
        XMEMCPY(dkey3, key + 16, 8);    /* set key 3 */

        ByteReverseWords(dkey1, dkey1, 8);
        ByteReverseWords(dkey2, dkey2, 8);
        ByteReverseWords(dkey3, dkey3, 8);

        return wc_Des3_SetIV(des, iv);
    }

    void DesCrypt(Des* des, byte* out, const byte* in, word32 sz,
                  int dir, int mode)
    {
        word32 *dkey, *iv;
        CRYP_InitTypeDef DES_CRYP_InitStructure;
        CRYP_KeyInitTypeDef DES_CRYP_KeyInitStructure;
        CRYP_IVInitTypeDef DES_CRYP_IVInitStructure;

        dkey = des->key;
        iv = des->reg;

        /* crypto structure initialization */
        CRYP_KeyStructInit(&DES_CRYP_KeyInitStructure);
        CRYP_StructInit(&DES_CRYP_InitStructure);
        CRYP_IVStructInit(&DES_CRYP_IVInitStructure);

        /* reset registers to their default values */
        CRYP_DeInit();

        /* set direction, mode, and datatype */
        if (dir == DES_ENCRYPTION) {
            DES_CRYP_InitStructure.CRYP_AlgoDir  = CRYP_AlgoDir_Encrypt;
        } else { /* DES_DECRYPTION */
            DES_CRYP_InitStructure.CRYP_AlgoDir  = CRYP_AlgoDir_Decrypt;
        }

        if (mode == DES_CBC) {
            DES_CRYP_InitStructure.CRYP_AlgoMode = CRYP_AlgoMode_DES_CBC;
        } else { /* DES_ECB */
            DES_CRYP_InitStructure.CRYP_AlgoMode = CRYP_AlgoMode_DES_ECB;
        }

        DES_CRYP_InitStructure.CRYP_DataType = CRYP_DataType_8b;
        CRYP_Init(&DES_CRYP_InitStructure);

        /* load key into correct registers */
        DES_CRYP_KeyInitStructure.CRYP_Key1Left  = dkey[0];
        DES_CRYP_KeyInitStructure.CRYP_Key1Right = dkey[1];
        CRYP_KeyInit(&DES_CRYP_KeyInitStructure);

        /* set iv */
        ByteReverseWords(iv, iv, DES_BLOCK_SIZE);
        DES_CRYP_IVInitStructure.CRYP_IV0Left  = iv[0];
        DES_CRYP_IVInitStructure.CRYP_IV0Right = iv[1];
        CRYP_IVInit(&DES_CRYP_IVInitStructure);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        while (sz > 0)
        {
            /* flush IN/OUT FIFOs */
            CRYP_FIFOFlush();

            /* if input and output same will overwrite input iv */
            XMEMCPY(des->tmp, in + sz - DES_BLOCK_SIZE, DES_BLOCK_SIZE);

            CRYP_DataIn(*(uint32_t*)&in[0]);
            CRYP_DataIn(*(uint32_t*)&in[4]);

            /* wait until the complete message has been processed */
            while(CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

            *(uint32_t*)&out[0]  = CRYP_DataOut();
            *(uint32_t*)&out[4]  = CRYP_DataOut();

            /* store iv for next call */
            XMEMCPY(des->reg, des->tmp, DES_BLOCK_SIZE);

            sz  -= DES_BLOCK_SIZE;
            in  += DES_BLOCK_SIZE;
            out += DES_BLOCK_SIZE;
        }

        /* disable crypto processor */
        CRYP_Cmd(DISABLE);
    }

    int wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des, out, in, sz, DES_ENCRYPTION, DES_CBC);
        return 0;
    }

    int wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des, out, in, sz, DES_DECRYPTION, DES_CBC);
        return 0;
    }

    int wc_Des_EcbEncrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des, out, in, sz, DES_ENCRYPTION, DES_ECB);
        return 0;
    }

    void Des3Crypt(Des3* des, byte* out, const byte* in, word32 sz,
                   int dir)
    {
        word32 *dkey1, *dkey2, *dkey3, *iv;
        CRYP_InitTypeDef DES3_CRYP_InitStructure;
        CRYP_KeyInitTypeDef DES3_CRYP_KeyInitStructure;
        CRYP_IVInitTypeDef DES3_CRYP_IVInitStructure;

        dkey1 = des->key[0];
        dkey2 = des->key[1];
        dkey3 = des->key[2];
        iv = des->reg;

        /* crypto structure initialization */
        CRYP_KeyStructInit(&DES3_CRYP_KeyInitStructure);
        CRYP_StructInit(&DES3_CRYP_InitStructure);
        CRYP_IVStructInit(&DES3_CRYP_IVInitStructure);

        /* reset registers to their default values */
        CRYP_DeInit();

        /* set direction, mode, and datatype */
        if (dir == DES_ENCRYPTION) {
            DES3_CRYP_InitStructure.CRYP_AlgoDir  = CRYP_AlgoDir_Encrypt;
        } else {
            DES3_CRYP_InitStructure.CRYP_AlgoDir  = CRYP_AlgoDir_Decrypt;
        }

        DES3_CRYP_InitStructure.CRYP_AlgoMode = CRYP_AlgoMode_TDES_CBC;
        DES3_CRYP_InitStructure.CRYP_DataType = CRYP_DataType_8b;
        CRYP_Init(&DES3_CRYP_InitStructure);

        /* load key into correct registers */
        DES3_CRYP_KeyInitStructure.CRYP_Key1Left  = dkey1[0];
        DES3_CRYP_KeyInitStructure.CRYP_Key1Right = dkey1[1];
        DES3_CRYP_KeyInitStructure.CRYP_Key2Left  = dkey2[0];
        DES3_CRYP_KeyInitStructure.CRYP_Key2Right = dkey2[1];
        DES3_CRYP_KeyInitStructure.CRYP_Key3Left  = dkey3[0];
        DES3_CRYP_KeyInitStructure.CRYP_Key3Right = dkey3[1];
        CRYP_KeyInit(&DES3_CRYP_KeyInitStructure);

        /* set iv */
        ByteReverseWords(iv, iv, DES_BLOCK_SIZE);
        DES3_CRYP_IVInitStructure.CRYP_IV0Left  = iv[0];
        DES3_CRYP_IVInitStructure.CRYP_IV0Right = iv[1];
        CRYP_IVInit(&DES3_CRYP_IVInitStructure);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        while (sz > 0)
        {
            /* flush IN/OUT FIFOs */
            CRYP_FIFOFlush();

            CRYP_DataIn(*(uint32_t*)&in[0]);
            CRYP_DataIn(*(uint32_t*)&in[4]);

            /* wait until the complete message has been processed */
            while(CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

            *(uint32_t*)&out[0]  = CRYP_DataOut();
            *(uint32_t*)&out[4]  = CRYP_DataOut();

            /* store iv for next call */
            XMEMCPY(des->reg, out + sz - DES_BLOCK_SIZE, DES_BLOCK_SIZE);

            sz  -= DES_BLOCK_SIZE;
            in  += DES_BLOCK_SIZE;
            out += DES_BLOCK_SIZE;
        }

        /* disable crypto processor */
        CRYP_Cmd(DISABLE);

    }

    int wc_Des3_CbcEncrypt(Des3* des, byte* out, const byte* in, word32 sz)
    {
        Des3Crypt(des, out, in, sz, DES_ENCRYPTION);
        return 0;
    }

    int wc_Des3_CbcDecrypt(Des3* des, byte* out, const byte* in, word32 sz)
    {
        Des3Crypt(des, out, in, sz, DES_DECRYPTION);
        return 0;
    }

#elif defined(HAVE_COLDFIRE_SEC)

#include <wolfssl/ctaocrypt/types.h>

#include "sec.h"
#include "mcf5475_sec.h"
#include "mcf5475_siu.h"

#if defined (HAVE_THREADX)
#include "memory_pools.h"
extern TX_BYTE_POOL mp_ncached;  /* Non Cached memory pool */
#endif

#define DES_BUFFER_SIZE (DES_BLOCK_SIZE * 64)
static unsigned char *desBuffIn = NULL ;
static unsigned char *desBuffOut = NULL ;
static byte *secIV ; 
static byte *secKey ; 
static volatile SECdescriptorType *secDesc ;

static wolfSSL_Mutex Mutex_DesSEC ;

#define SEC_DESC_DES_CBC_ENCRYPT  0x20500010
#define SEC_DESC_DES_CBC_DECRYPT  0x20400010
#define SEC_DESC_DES3_CBC_ENCRYPT 0x20700010
#define SEC_DESC_DES3_CBC_DECRYPT 0x20600010

#define DES_IVLEN 8
#define DES_KEYLEN 8
#define DES3_IVLEN 8
#define DES3_KEYLEN 24

extern volatile unsigned char __MBAR[];

static void wc_Des_Cbc(byte* out, const byte* in, word32 sz, 
                    byte *key, byte *iv, word32 desc)
{
    #ifdef DEBUG_WOLFSSL
    int ret ;  int stat1,stat2 ; 
	  #endif
    int size ;
    volatile int v ;
 
    LockMutex(&Mutex_DesSEC) ;
    
    secDesc->length1 = 0x0;
    secDesc->pointer1 = NULL;
    if((desc==SEC_DESC_DES_CBC_ENCRYPT)||(desc==SEC_DESC_DES_CBC_DECRYPT)){
        secDesc->length2 = DES_IVLEN ;  
        secDesc->length3 = DES_KEYLEN ;
    } else {
        secDesc->length2 = DES3_IVLEN ; 
        secDesc->length3 = DES3_KEYLEN ;
    }
    secDesc->pointer2 = secIV ;
    secDesc->pointer3 = secKey;
    secDesc->pointer4 = desBuffIn ;
    secDesc->pointer5 = desBuffOut ;
    secDesc->length6 = 0; 
    secDesc->pointer6 = NULL; 
    secDesc->length7 = 0x0;
    secDesc->pointer7 = NULL;
    secDesc->nextDescriptorPtr = NULL ; 
    
    while(sz) {
        XMEMCPY(secIV, iv, secDesc->length2) ;
        if((sz%DES_BUFFER_SIZE) == sz) {
            size = sz ;
            sz = 0 ;
        } else {
            size = DES_BUFFER_SIZE ;
            sz -= DES_BUFFER_SIZE ;
        }
        
        XMEMCPY(desBuffIn, in, size) ;
        XMEMCPY(secKey, key, secDesc->length3) ;
        
        secDesc->header = desc ;
        secDesc->length4 = size;
        secDesc->length5 = size;
        /* Point SEC to the location of the descriptor */
        MCF_SEC_FR0 = (uint32)secDesc;
        /* Initialize SEC and wait for encryption to complete */
        MCF_SEC_CCCR0 = 0x0000001a;
        /* poll SISR to determine when channel is complete */
        v=0 ;
        while((secDesc->header>> 24) != 0xff) {
            if(v++ > 1000)break ;
        }
				
#ifdef DEBUG_WOLFSSL
        ret = MCF_SEC_SISRH;
        stat1 = MCF_SEC_DSR ; 
        stat2 = MCF_SEC_DISR ; 
        if(ret & 0xe0000000) {
            /* db_printf("Des_Cbc(%x):ISRH=%08x, DSR=%08x, DISR=%08x\n", desc, ret, stat1, stat2) ; */
        }
#endif
				
        XMEMCPY(out, desBuffOut, size) ;

        if((desc==SEC_DESC_DES3_CBC_ENCRYPT)||(desc==SEC_DESC_DES_CBC_ENCRYPT)) {
            XMEMCPY((void*)iv, (void*)&(out[size-secDesc->length2]), secDesc->length2) ;
        } else {
            XMEMCPY((void*)iv, (void*)&(in[size-secDesc->length2]), secDesc->length2) ;
        }
        
        in  += size ;   
        out += size ;
                
    }
    UnLockMutex(&Mutex_DesSEC) ;
    
}


int wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    wc_Des_Cbc(out, in, sz,  (byte *)des->key,  (byte *)des->reg, SEC_DESC_DES_CBC_ENCRYPT) ;
    return 0;
}

int wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    wc_Des_Cbc(out, in, sz,   (byte *)des->key,  (byte *)des->reg, SEC_DESC_DES_CBC_DECRYPT) ;
    return 0;
}

int wc_Des3_CbcEncrypt(Des3* des3, byte* out, const byte* in, word32 sz)
{
    wc_Des_Cbc(out, in, sz,  (byte *)des3->key,  (byte *)des3->reg, SEC_DESC_DES3_CBC_ENCRYPT) ;
	  return 0;
}


int wc_Des3_CbcDecrypt(Des3* des3, byte* out, const byte* in, word32 sz)
{
    wc_Des_Cbc(out, in, sz,   (byte *)des3->key,  (byte *)des3->reg, SEC_DESC_DES3_CBC_DECRYPT) ;
	  return 0;
}

static void setParity(byte *buf, int len) 
{
    int i, j ;
    byte v ;
    int bits ;

    for(i=0; i<len; i++) 
    {
        v = buf[i] >> 1 ;
        buf[i] = v << 1 ;
        bits = 0 ;
        for(j=0; j<7; j++)
        {
            bits += (v&0x1) ;
            v = v >> 1 ;
        }
        buf[i] |= (1 - (bits&0x1)) ;
    }
    
}


int wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
{
    if(desBuffIn == NULL) {
        #if defined (HAVE_THREADX)
			  int s1, s2, s3, s4, s5 ;
        s5 = tx_byte_allocate(&mp_ncached,(void *)&secDesc, 
                                                     sizeof(SECdescriptorType), TX_NO_WAIT);
        s1 = tx_byte_allocate(&mp_ncached,(void *)&desBuffIn,  DES_BUFFER_SIZE, TX_NO_WAIT);
        s2 = tx_byte_allocate(&mp_ncached,(void *)&desBuffOut, DES_BUFFER_SIZE, TX_NO_WAIT);
        /* Don't know des or des3 to be used. Allocate larger buffers */
        s3 = tx_byte_allocate(&mp_ncached,(void *)&secKey,     DES3_KEYLEN,TX_NO_WAIT);
        s4 = tx_byte_allocate(&mp_ncached,(void *)&secIV,      DES3_IVLEN,  TX_NO_WAIT);              
        #else
        #warning "Allocate non-Cache buffers"
        #endif
        
        InitMutex(&Mutex_DesSEC) ;
    }
     
    XMEMCPY(des->key, key, DES_KEYLEN);  
    setParity((byte *)des->key, DES_KEYLEN) ;  
		
    if (iv) {
        XMEMCPY(des->reg, iv, DES_IVLEN);
    }   else {
        XMEMSET(des->reg, 0x0, DES_IVLEN) ;
    }
		return 0;
}

int wc_Des3_SetKey(Des3* des3, const byte* key, const byte* iv, int dir)
{
    
    if(desBuffIn == NULL) {
        #if defined (HAVE_THREADX)
			  int s1, s2, s3, s4, s5 ;
        s5 = tx_byte_allocate(&mp_ncached,(void *)&secDesc, 
                                                     sizeof(SECdescriptorType), TX_NO_WAIT);
        s1 = tx_byte_allocate(&mp_ncached,(void *)&desBuffIn,  DES_BUFFER_SIZE, TX_NO_WAIT);
        s2 = tx_byte_allocate(&mp_ncached,(void *)&desBuffOut, DES_BUFFER_SIZE, TX_NO_WAIT);
        s3 = tx_byte_allocate(&mp_ncached,(void *)&secKey,     DES3_KEYLEN,TX_NO_WAIT);
        s4 = tx_byte_allocate(&mp_ncached,(void *)&secIV,      DES3_IVLEN,  TX_NO_WAIT);              
        #else
        #warning "Allocate non-Cache buffers"
        #endif
        
        InitMutex(&Mutex_DesSEC) ;
    }
    
    XMEMCPY(des3->key[0], key, DES3_KEYLEN); 
    setParity((byte *)des3->key[0], DES3_KEYLEN) ;  
		
    if (iv) {
        XMEMCPY(des3->reg, iv, DES3_IVLEN);
    }   else {
        XMEMSET(des3->reg, 0x0, DES3_IVLEN) ;
    }
    return 0;

}

#elif defined FREESCALE_MMCAU
    /*
     * Freescale mmCAU hardware DES/3DES support through the CAU/mmCAU library.
     * Documentation located in ColdFire/ColdFire+ CAU and Kinetis mmCAU
     * Software Library User Guide (See note in README).
     */
    #include "cau_api.h"

    const unsigned char parityLookup[128] =
    {
        1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0,
        0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1,
        0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1,
        1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0
     };

    int wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
    {
        int i = 0;
        byte* dkey = (byte*)des->key;

        XMEMCPY(dkey, key, 8);

        wc_Des_SetIV(des, iv);

        /* fix key parity, if needed */
        for (i = 0; i < 8; i++) {
            dkey[i] = ((dkey[i] & 0xFE) | parityLookup[dkey[i] >> 1]);
        }

        return 0;
    }

    int wc_Des3_SetKey(Des3* des, const byte* key, const byte* iv, int dir)
    {
        int i = 0, ret = 0;
        byte* dkey1 = (byte*)des->key[0];
        byte* dkey2 = (byte*)des->key[1];
        byte* dkey3 = (byte*)des->key[2];

        XMEMCPY(dkey1, key, 8);         /* set key 1 */
        XMEMCPY(dkey2, key + 8, 8);     /* set key 2 */
        XMEMCPY(dkey3, key + 16, 8);    /* set key 3 */

        ret = wc_Des3_SetIV(des, iv);
        if (ret != 0)
            return ret;

        /* fix key parity if needed */
        for (i = 0; i < 8; i++)
           dkey1[i] = ((dkey1[i] & 0xFE) | parityLookup[dkey1[i] >> 1]);

        for (i = 0; i < 8; i++)
           dkey2[i] = ((dkey2[i] & 0xFE) | parityLookup[dkey2[i] >> 1]);

        for (i = 0; i < 8; i++)
           dkey3[i] = ((dkey3[i] & 0xFE) | parityLookup[dkey3[i] >> 1]);

        return ret;
    }

    int wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        int i;
        int offset = 0;
        int len = sz;
        byte *iv;
        byte temp_block[DES_BLOCK_SIZE];

        iv = (byte*)des->reg;

        if ((wolfssl_word)out % WOLFSSL_MMCAU_ALIGNMENT) {
            WOLFSSL_MSG("Bad cau_des_encrypt alignment"); 
            return BAD_ALIGN_E;
        }

        while (len > 0)
        {
            XMEMCPY(temp_block, in + offset, DES_BLOCK_SIZE);

            /* XOR block with IV for CBC */
            for (i = 0; i < DES_BLOCK_SIZE; i++)
                temp_block[i] ^= iv[i];

            cau_des_encrypt(temp_block, (byte*)des->key, out + offset);

            len    -= DES_BLOCK_SIZE;
            offset += DES_BLOCK_SIZE;

            /* store IV for next block */
            XMEMCPY(iv, out + offset - DES_BLOCK_SIZE, DES_BLOCK_SIZE);
        }

        return 0;
    }

    int wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        int i;
        int offset = 0;
        int len = sz;
        byte* iv;
        byte temp_block[DES_BLOCK_SIZE];

        iv = (byte*)des->reg;

        if ((wolfssl_word)out % WOLFSSL_MMCAU_ALIGNMENT) {
            WOLFSSL_MSG("Bad cau_des_decrypt alignment"); 
            return BAD_ALIGN_E;
        }

        while (len > 0)
        {
            XMEMCPY(temp_block, in + offset, DES_BLOCK_SIZE);

            cau_des_decrypt(in + offset, (byte*)des->key, out + offset);

            /* XOR block with IV for CBC */
            for (i = 0; i < DES_BLOCK_SIZE; i++)
                (out + offset)[i] ^= iv[i];

            /* store IV for next block */
            XMEMCPY(iv, temp_block, DES_BLOCK_SIZE);

            len     -= DES_BLOCK_SIZE;
            offset += DES_BLOCK_SIZE;
        }

        return 0;
    }

    int wc_Des3_CbcEncrypt(Des3* des, byte* out, const byte* in, word32 sz)
    {
        int i;
        int offset = 0;
        int len = sz;

        byte *iv;
        byte temp_block[DES_BLOCK_SIZE];

        iv = (byte*)des->reg;

        if ((wolfssl_word)out % WOLFSSL_MMCAU_ALIGNMENT) {
            WOLFSSL_MSG("Bad 3ede cau_des_encrypt alignment"); 
            return BAD_ALIGN_E;
        }

        while (len > 0)
        {
            XMEMCPY(temp_block, in + offset, DES_BLOCK_SIZE);

            /* XOR block with IV for CBC */
            for (i = 0; i < DES_BLOCK_SIZE; i++)
                temp_block[i] ^= iv[i];

            cau_des_encrypt(temp_block  , (byte*)des->key[0], out + offset);
            cau_des_decrypt(out + offset, (byte*)des->key[1], out + offset);
            cau_des_encrypt(out + offset, (byte*)des->key[2], out + offset);

            len    -= DES_BLOCK_SIZE;
            offset += DES_BLOCK_SIZE;

            /* store IV for next block */
            XMEMCPY(iv, out + offset - DES_BLOCK_SIZE, DES_BLOCK_SIZE);
        }

        return 0;
    }

    int wc_Des3_CbcDecrypt(Des3* des, byte* out, const byte* in, word32 sz)
    {
        int i;
        int offset = 0;
        int len = sz;

        byte* iv;
        byte temp_block[DES_BLOCK_SIZE];

        iv = (byte*)des->reg;

        if ((wolfssl_word)out % WOLFSSL_MMCAU_ALIGNMENT) {
            WOLFSSL_MSG("Bad 3ede cau_des_decrypt alignment"); 
            return BAD_ALIGN_E;
        }

        while (len > 0)
        {
            XMEMCPY(temp_block, in + offset, DES_BLOCK_SIZE);

            cau_des_decrypt(in + offset , (byte*)des->key[2], out + offset);
            cau_des_encrypt(out + offset, (byte*)des->key[1], out + offset);
            cau_des_decrypt(out + offset, (byte*)des->key[0], out + offset);

            /* XOR block with IV for CBC */
            for (i = 0; i < DES_BLOCK_SIZE; i++)
                (out + offset)[i] ^= iv[i];

            /* store IV for next block */
            XMEMCPY(iv, temp_block, DES_BLOCK_SIZE);

            len    -= DES_BLOCK_SIZE;
            offset += DES_BLOCK_SIZE;
        }

        return 0;
    }


#elif defined(WOLFSSL_PIC32MZ_CRYPT)

    #include "wolfssl/wolfcrypt/port/pic32/pic32mz-crypt.h"

void wc_Des_SetIV(Des* des, const byte* iv);
int  wc_Des3_SetIV(Des3* des, const byte* iv);

    int wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
    {
        word32 *dkey = des->key ;
        word32 *dreg = des->reg ;

        XMEMCPY((byte *)dkey, (byte *)key, 8);
        ByteReverseWords(dkey, dkey, 8);
        XMEMCPY((byte *)dreg, (byte *)iv, 8);
        ByteReverseWords(dreg, dreg, 8);

        return 0;
    }

    int wc_Des3_SetKey(Des3* des, const byte* key, const byte* iv, int dir)
    {
        word32 *dkey1 = des->key[0];
        word32 *dreg = des->reg ;

        XMEMCPY(dkey1, key, 24);
        ByteReverseWords(dkey1, dkey1, 24);
        XMEMCPY(dreg, iv, 8);
        ByteReverseWords(dreg, dreg, 8) ;

        return 0;
    }

    void DesCrypt(word32 *key, word32 *iv, byte* out, const byte* in, word32 sz,
                  int dir, int algo, int cryptoalgo)
    {
        securityAssociation *sa_p ;
        bufferDescriptor *bd_p ;
        const byte *in_p, *in_l ;
        byte *out_p, *out_l ;
        volatile securityAssociation sa __attribute__((aligned (8)));
        volatile bufferDescriptor bd __attribute__((aligned (8)));
        volatile int k ;
        
        /* get uncached address */

        in_l = in;
        out_l = out ;
        sa_p = KVA0_TO_KVA1(&sa) ; 
        bd_p = KVA0_TO_KVA1(&bd) ;
        in_p = KVA0_TO_KVA1(in_l) ;
        out_p= KVA0_TO_KVA1(out_l);
        
        if(PIC32MZ_IF_RAM(in_p))
            XMEMCPY((void *)in_p, (void *)in, sz);
        XMEMSET((void *)out_p, 0, sz);

        /* Set up the Security Association */
        XMEMSET((byte *)KVA0_TO_KVA1(&sa), 0, sizeof(sa));
        sa_p->SA_CTRL.ALGO = algo ; 
        sa_p->SA_CTRL.LNC = 1;
        sa_p->SA_CTRL.LOADIV = 1;
        sa_p->SA_CTRL.FB = 1;
        sa_p->SA_CTRL.ENCTYPE = dir ; /* Encryption/Decryption */
        sa_p->SA_CTRL.CRYPTOALGO = cryptoalgo;
        sa_p->SA_CTRL.KEYSIZE = 1 ; /* KEY is 192 bits */
        XMEMCPY((byte *)KVA0_TO_KVA1(&sa.SA_ENCKEY[algo==PIC32_ALGO_TDES ? 2 : 6]),
                (byte *)key, algo==PIC32_ALGO_TDES ? 24 : 8);
        XMEMCPY((byte *)KVA0_TO_KVA1(&sa.SA_ENCIV[2]), (byte *)iv, 8);

        XMEMSET((byte *)KVA0_TO_KVA1(&bd), 0, sizeof(bd));
        /* Set up the Buffer Descriptor */
        bd_p->BD_CTRL.BUFLEN = sz;
        bd_p->BD_CTRL.LIFM = 1;
        bd_p->BD_CTRL.SA_FETCH_EN = 1;
        bd_p->BD_CTRL.LAST_BD = 1;
        bd_p->BD_CTRL.DESC_EN = 1;
    
        bd_p->SA_ADDR = (unsigned int)KVA_TO_PA(&sa) ; /* (unsigned int)sa_p; */
        bd_p->SRCADDR = (unsigned int)KVA_TO_PA(in) ; /* (unsigned int)in_p; */
        bd_p->DSTADDR = (unsigned int)KVA_TO_PA(out); /* (unsigned int)out_p; */
        bd_p->NXTPTR = (unsigned int)KVA_TO_PA(&bd);
        bd_p->MSGLEN = sz ;
        
        /* Fire in the hole! */
        CECON = 1 << 6;
        while (CECON);
        
        /* Run the engine */
        CEBDPADDR = (unsigned int)KVA_TO_PA(&bd) ; /* (unsigned int)bd_p ; */
        CEINTEN = 0x07;
        CECON = 0x27;

        WAIT_ENGINE ;

        if((cryptoalgo == PIC32_CRYPTOALGO_CBC) ||
           (cryptoalgo == PIC32_CRYPTOALGO_TCBC)||
           (cryptoalgo == PIC32_CRYPTOALGO_RCBC)) {
            /* set iv for the next call */
            if(dir == PIC32_ENCRYPTION) {
	        XMEMCPY((void *)iv, (void*)&(out_p[sz-DES_IVLEN]), DES_IVLEN) ;
	        } else {
                ByteReverseWords((word32*)iv, (word32 *)&(in_p[sz-DES_IVLEN]),
                                 DES_IVLEN);
	        }

        }

        ByteReverseWords((word32*)out, (word32 *)KVA0_TO_KVA1(out), sz);
    }

    int wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des->key, des->reg, out, in, sz, 
                PIC32_ENCRYPTION, PIC32_ALGO_DES, PIC32_CRYPTOALGO_CBC );
        return 0;
    }

    int wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des->key, des->reg, out, in, sz, 
                PIC32_DECRYPTION, PIC32_ALGO_DES, PIC32_CRYPTOALGO_CBC);
        return 0;
    }

    int wc_Des3_CbcEncrypt(Des3* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des->key[0], des->reg, out, in, sz, 
                PIC32_ENCRYPTION, PIC32_ALGO_TDES, PIC32_CRYPTOALGO_TCBC);
        return 0;
    }

    int wc_Des3_CbcDecrypt(Des3* des, byte* out, const byte* in, word32 sz)
    {
        DesCrypt(des->key[0], des->reg, out, in, sz, 
                PIC32_DECRYPTION, PIC32_ALGO_TDES, PIC32_CRYPTOALGO_TCBC);
        return 0;
    }
    
#else /* CTaoCrypt software implementation */

/* permuted choice table (key) */
static const byte pc1[] = {
       57, 49, 41, 33, 25, 17,  9,
        1, 58, 50, 42, 34, 26, 18,
       10,  2, 59, 51, 43, 35, 27,
       19, 11,  3, 60, 52, 44, 36,

       63, 55, 47, 39, 31, 23, 15,
        7, 62, 54, 46, 38, 30, 22,
       14,  6, 61, 53, 45, 37, 29,
       21, 13,  5, 28, 20, 12,  4
};

/* number left rotations of pc1 */
static const byte totrot[] = {
       1,2,4,6,8,10,12,14,15,17,19,21,23,25,27,28
};

/* permuted choice key (table) */
static const byte pc2[] = {
       14, 17, 11, 24,  1,  5,
        3, 28, 15,  6, 21, 10,
       23, 19, 12,  4, 26,  8,
       16,  7, 27, 20, 13,  2,
       41, 52, 31, 37, 47, 55,
       30, 40, 51, 45, 33, 48,
       44, 49, 39, 56, 34, 53,
       46, 42, 50, 36, 29, 32
};

/* End of DES-defined tables */

/* bit 0 is left-most in byte */
static const int bytebit[] = {
       0200,0100,040,020,010,04,02,01
};

static const word32 Spbox[8][64] = {
{
0x01010400,0x00000000,0x00010000,0x01010404,
0x01010004,0x00010404,0x00000004,0x00010000,
0x00000400,0x01010400,0x01010404,0x00000400,
0x01000404,0x01010004,0x01000000,0x00000004,
0x00000404,0x01000400,0x01000400,0x00010400,
0x00010400,0x01010000,0x01010000,0x01000404,
0x00010004,0x01000004,0x01000004,0x00010004,
0x00000000,0x00000404,0x00010404,0x01000000,
0x00010000,0x01010404,0x00000004,0x01010000,
0x01010400,0x01000000,0x01000000,0x00000400,
0x01010004,0x00010000,0x00010400,0x01000004,
0x00000400,0x00000004,0x01000404,0x00010404,
0x01010404,0x00010004,0x01010000,0x01000404,
0x01000004,0x00000404,0x00010404,0x01010400,
0x00000404,0x01000400,0x01000400,0x00000000,
0x00010004,0x00010400,0x00000000,0x01010004},
{
0x80108020,0x80008000,0x00008000,0x00108020,
0x00100000,0x00000020,0x80100020,0x80008020,
0x80000020,0x80108020,0x80108000,0x80000000,
0x80008000,0x00100000,0x00000020,0x80100020,
0x00108000,0x00100020,0x80008020,0x00000000,
0x80000000,0x00008000,0x00108020,0x80100000,
0x00100020,0x80000020,0x00000000,0x00108000,
0x00008020,0x80108000,0x80100000,0x00008020,
0x00000000,0x00108020,0x80100020,0x00100000,
0x80008020,0x80100000,0x80108000,0x00008000,
0x80100000,0x80008000,0x00000020,0x80108020,
0x00108020,0x00000020,0x00008000,0x80000000,
0x00008020,0x80108000,0x00100000,0x80000020,
0x00100020,0x80008020,0x80000020,0x00100020,
0x00108000,0x00000000,0x80008000,0x00008020,
0x80000000,0x80100020,0x80108020,0x00108000},
{
0x00000208,0x08020200,0x00000000,0x08020008,
0x08000200,0x00000000,0x00020208,0x08000200,
0x00020008,0x08000008,0x08000008,0x00020000,
0x08020208,0x00020008,0x08020000,0x00000208,
0x08000000,0x00000008,0x08020200,0x00000200,
0x00020200,0x08020000,0x08020008,0x00020208,
0x08000208,0x00020200,0x00020000,0x08000208,
0x00000008,0x08020208,0x00000200,0x08000000,
0x08020200,0x08000000,0x00020008,0x00000208,
0x00020000,0x08020200,0x08000200,0x00000000,
0x00000200,0x00020008,0x08020208,0x08000200,
0x08000008,0x00000200,0x00000000,0x08020008,
0x08000208,0x00020000,0x08000000,0x08020208,
0x00000008,0x00020208,0x00020200,0x08000008,
0x08020000,0x08000208,0x00000208,0x08020000,
0x00020208,0x00000008,0x08020008,0x00020200},
{
0x00802001,0x00002081,0x00002081,0x00000080,
0x00802080,0x00800081,0x00800001,0x00002001,
0x00000000,0x00802000,0x00802000,0x00802081,
0x00000081,0x00000000,0x00800080,0x00800001,
0x00000001,0x00002000,0x00800000,0x00802001,
0x00000080,0x00800000,0x00002001,0x00002080,
0x00800081,0x00000001,0x00002080,0x00800080,
0x00002000,0x00802080,0x00802081,0x00000081,
0x00800080,0x00800001,0x00802000,0x00802081,
0x00000081,0x00000000,0x00000000,0x00802000,
0x00002080,0x00800080,0x00800081,0x00000001,
0x00802001,0x00002081,0x00002081,0x00000080,
0x00802081,0x00000081,0x00000001,0x00002000,
0x00800001,0x00002001,0x00802080,0x00800081,
0x00002001,0x00002080,0x00800000,0x00802001,
0x00000080,0x00800000,0x00002000,0x00802080},
{
0x00000100,0x02080100,0x02080000,0x42000100,
0x00080000,0x00000100,0x40000000,0x02080000,
0x40080100,0x00080000,0x02000100,0x40080100,
0x42000100,0x42080000,0x00080100,0x40000000,
0x02000000,0x40080000,0x40080000,0x00000000,
0x40000100,0x42080100,0x42080100,0x02000100,
0x42080000,0x40000100,0x00000000,0x42000000,
0x02080100,0x02000000,0x42000000,0x00080100,
0x00080000,0x42000100,0x00000100,0x02000000,
0x40000000,0x02080000,0x42000100,0x40080100,
0x02000100,0x40000000,0x42080000,0x02080100,
0x40080100,0x00000100,0x02000000,0x42080000,
0x42080100,0x00080100,0x42000000,0x42080100,
0x02080000,0x00000000,0x40080000,0x42000000,
0x00080100,0x02000100,0x40000100,0x00080000,
0x00000000,0x40080000,0x02080100,0x40000100},
{
0x20000010,0x20400000,0x00004000,0x20404010,
0x20400000,0x00000010,0x20404010,0x00400000,
0x20004000,0x00404010,0x00400000,0x20000010,
0x00400010,0x20004000,0x20000000,0x00004010,
0x00000000,0x00400010,0x20004010,0x00004000,
0x00404000,0x20004010,0x00000010,0x20400010,
0x20400010,0x00000000,0x00404010,0x20404000,
0x00004010,0x00404000,0x20404000,0x20000000,
0x20004000,0x00000010,0x20400010,0x00404000,
0x20404010,0x00400000,0x00004010,0x20000010,
0x00400000,0x20004000,0x20000000,0x00004010,
0x20000010,0x20404010,0x00404000,0x20400000,
0x00404010,0x20404000,0x00000000,0x20400010,
0x00000010,0x00004000,0x20400000,0x00404010,
0x00004000,0x00400010,0x20004010,0x00000000,
0x20404000,0x20000000,0x00400010,0x20004010},
{
0x00200000,0x04200002,0x04000802,0x00000000,
0x00000800,0x04000802,0x00200802,0x04200800,
0x04200802,0x00200000,0x00000000,0x04000002,
0x00000002,0x04000000,0x04200002,0x00000802,
0x04000800,0x00200802,0x00200002,0x04000800,
0x04000002,0x04200000,0x04200800,0x00200002,
0x04200000,0x00000800,0x00000802,0x04200802,
0x00200800,0x00000002,0x04000000,0x00200800,
0x04000000,0x00200800,0x00200000,0x04000802,
0x04000802,0x04200002,0x04200002,0x00000002,
0x00200002,0x04000000,0x04000800,0x00200000,
0x04200800,0x00000802,0x00200802,0x04200800,
0x00000802,0x04000002,0x04200802,0x04200000,
0x00200800,0x00000000,0x00000002,0x04200802,
0x00000000,0x00200802,0x04200000,0x00000800,
0x04000002,0x04000800,0x00000800,0x00200002},
{
0x10001040,0x00001000,0x00040000,0x10041040,
0x10000000,0x10001040,0x00000040,0x10000000,
0x00040040,0x10040000,0x10041040,0x00041000,
0x10041000,0x00041040,0x00001000,0x00000040,
0x10040000,0x10000040,0x10001000,0x00001040,
0x00041000,0x00040040,0x10040040,0x10041000,
0x00001040,0x00000000,0x00000000,0x10040040,
0x10000040,0x10001000,0x00041040,0x00040000,
0x00041040,0x00040000,0x10041000,0x00001000,
0x00000040,0x10040040,0x00001000,0x00041040,
0x10001000,0x00000040,0x10000040,0x10040000,
0x10040040,0x10000000,0x00040000,0x10001040,
0x00000000,0x10041040,0x00040040,0x10000040,
0x10040000,0x10001000,0x10001040,0x00000000,
0x10041040,0x00041000,0x00041000,0x00001040,
0x00001040,0x00040040,0x10000000,0x10041000}
};


static INLINE void IPERM(word32* left, word32* right)
{
    word32 work;

    *right = rotlFixed(*right, 4U);
    work = (*left ^ *right) & 0xf0f0f0f0;
    *left ^= work;

    *right = rotrFixed(*right^work, 20U);
    work = (*left ^ *right) & 0xffff0000;
    *left ^= work;

    *right = rotrFixed(*right^work, 18U);
    work = (*left ^ *right) & 0x33333333;
    *left ^= work;

    *right = rotrFixed(*right^work, 6U);
    work = (*left ^ *right) & 0x00ff00ff;
    *left ^= work;

    *right = rotlFixed(*right^work, 9U);
    work = (*left ^ *right) & 0xaaaaaaaa;
    *left = rotlFixed(*left^work, 1U);
    *right ^= work;
}


static INLINE void FPERM(word32* left, word32* right)
{
    word32 work;

    *right = rotrFixed(*right, 1U);
    work = (*left ^ *right) & 0xaaaaaaaa;
    *right ^= work;

    *left = rotrFixed(*left^work, 9U);
    work = (*left ^ *right) & 0x00ff00ff;
    *right ^= work;

    *left = rotlFixed(*left^work, 6U);
    work = (*left ^ *right) & 0x33333333;
    *right ^= work;

    *left = rotlFixed(*left^work, 18U);
    work = (*left ^ *right) & 0xffff0000;
    *right ^= work;

    *left = rotlFixed(*left^work, 20U);
    work = (*left ^ *right) & 0xf0f0f0f0;
    *right ^= work;

    *left = rotrFixed(*left^work, 4U);
}


static int DesSetKey(const byte* key, int dir, word32* out)
{
#ifdef WOLFSSL_SMALL_STACK
    byte* buffer = (byte*)XMALLOC(56+56+8, NULL, DYNAMIC_TYPE_TMP_BUFFER);

    if (buffer == NULL)
        return MEMORY_E;
#else
    byte buffer[56+56+8];
#endif

    {
        byte* const  pc1m = buffer;               /* place to modify pc1 into */
        byte* const  pcr  = pc1m + 56;            /* place to rotate pc1 into */
        byte* const  ks   = pcr  + 56;
        register int i, j, l;
        int          m;

        for (j = 0; j < 56; j++) {             /* convert pc1 to bits of key  */
            l = pc1[j] - 1;                    /* integer bit location        */
            m = l & 07;                        /* find bit                    */
            pc1m[j] = (key[l >> 3] &           /* find which key byte l is in */
                bytebit[m])                    /* and which bit of that byte  */
                ? 1 : 0;                       /* and store 1-bit result      */
        }

        for (i = 0; i < 16; i++) {            /* key chunk for each iteration */
            XMEMSET(ks, 0, 8);                /* Clear key schedule */

            for (j = 0; j < 56; j++)          /* rotate pc1 the right amount  */
                pcr[j] =
                      pc1m[(l = j + totrot[i]) < (j < 28 ? 28 : 56) ? l : l-28];

            /* rotate left and right halves independently */
            for (j = 0; j < 48; j++) {        /* select bits individually     */
                if (pcr[pc2[j] - 1]) {        /* check bit that goes to ks[j] */
                    l= j % 6;                 /* mask it in if it's there     */
                    ks[j/6] |= bytebit[l] >> 2;
                }
            }

            /* Now convert to odd/even interleaved form for use in F */
            out[2*i] = ((word32) ks[0] << 24)
                     | ((word32) ks[2] << 16)
                     | ((word32) ks[4] << 8)
                     | ((word32) ks[6]);

            out[2*i + 1] = ((word32) ks[1] << 24)
                         | ((word32) ks[3] << 16)
                         | ((word32) ks[5] << 8)
                         | ((word32) ks[7]);
        }

        /* reverse key schedule order */
        if (dir == DES_DECRYPTION) {
            for (i = 0; i < 16; i += 2) {
                word32 swap = out[i];
                out[i] = out[DES_KS_SIZE - 2 - i];
                out[DES_KS_SIZE - 2 - i] = swap;
    
                swap = out[i + 1];
                out[i + 1] = out[DES_KS_SIZE - 1 - i];
                out[DES_KS_SIZE - 1 - i] = swap;
            }
        }

#ifdef WOLFSSL_SMALL_STACK
        XFREE(buffer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    }

    return 0;
}


static INLINE int Reverse(int dir)
{
    return !dir;
}


int wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
{
    wc_Des_SetIV(des, iv);

    return DesSetKey(key, dir, des->key);
}


int wc_Des3_SetKey(Des3* des, const byte* key, const byte* iv, int dir)
{
    int ret;

#ifdef HAVE_CAVIUM
    if (des->magic == WOLFSSL_3DES_CAVIUM_MAGIC)
        return wc_Des3_CaviumSetKey(des, key, iv);
#endif

    ret = DesSetKey(key + (dir == DES_ENCRYPTION ? 0:16), dir, des->key[0]);
    if (ret != 0)
        return ret;

    ret = DesSetKey(key + 8, Reverse(dir), des->key[1]);
    if (ret != 0)
        return ret;

    ret = DesSetKey(key + (dir == DES_DECRYPTION ? 0:16), dir, des->key[2]);
    if (ret != 0)
        return ret;

    return wc_Des3_SetIV(des, iv);
}


static void DesRawProcessBlock(word32* lIn, word32* rIn, const word32* kptr)
{
    word32 l = *lIn, r = *rIn, i;

    for (i=0; i<8; i++)
    {
        word32 work = rotrFixed(r, 4U) ^ kptr[4*i+0];
        l ^= Spbox[6][(work) & 0x3f]
          ^  Spbox[4][(work >> 8) & 0x3f]
          ^  Spbox[2][(work >> 16) & 0x3f]
          ^  Spbox[0][(work >> 24) & 0x3f];
        work = r ^ kptr[4*i+1];
        l ^= Spbox[7][(work) & 0x3f]
          ^  Spbox[5][(work >> 8) & 0x3f]
          ^  Spbox[3][(work >> 16) & 0x3f]
          ^  Spbox[1][(work >> 24) & 0x3f];

        work = rotrFixed(l, 4U) ^ kptr[4*i+2];
        r ^= Spbox[6][(work) & 0x3f]
          ^  Spbox[4][(work >> 8) & 0x3f]
          ^  Spbox[2][(work >> 16) & 0x3f]
          ^  Spbox[0][(work >> 24) & 0x3f];
        work = l ^ kptr[4*i+3];
        r ^= Spbox[7][(work) & 0x3f]
          ^  Spbox[5][(work >> 8) & 0x3f]
          ^  Spbox[3][(work >> 16) & 0x3f]
          ^  Spbox[1][(work >> 24) & 0x3f];
    }

    *lIn = l; *rIn = r;
}


static void DesProcessBlock(Des* des, const byte* in, byte* out)
{
    word32 l, r;

    XMEMCPY(&l, in, sizeof(l));
    XMEMCPY(&r, in + sizeof(l), sizeof(r));
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    IPERM(&l,&r);
    
    DesRawProcessBlock(&l, &r, des->key);   

    FPERM(&l,&r);
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    XMEMCPY(out, &r, sizeof(r));
    XMEMCPY(out + sizeof(r), &l, sizeof(l));
}


static void Des3ProcessBlock(Des3* des, const byte* in, byte* out)
{
    word32 l, r;

    XMEMCPY(&l, in, sizeof(l));
    XMEMCPY(&r, in + sizeof(l), sizeof(r));
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    IPERM(&l,&r);
    
    DesRawProcessBlock(&l, &r, des->key[0]);   
    DesRawProcessBlock(&r, &l, des->key[1]);   
    DesRawProcessBlock(&l, &r, des->key[2]);   

    FPERM(&l,&r);
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    XMEMCPY(out, &r, sizeof(r));
    XMEMCPY(out + sizeof(r), &l, sizeof(l));
}


int wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;

    while (blocks--) {
        xorbuf((byte*)des->reg, in, DES_BLOCK_SIZE);
        DesProcessBlock(des, (byte*)des->reg, (byte*)des->reg);
        XMEMCPY(out, des->reg, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
    return 0;
}


int wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;
    byte   hold[DES_BLOCK_SIZE];

    while (blocks--) {
        XMEMCPY(des->tmp, in, DES_BLOCK_SIZE);
        DesProcessBlock(des, (byte*)des->tmp, out);
        xorbuf(out, (byte*)des->reg, DES_BLOCK_SIZE);

        XMEMCPY(hold, des->reg, DES_BLOCK_SIZE);
        XMEMCPY(des->reg, des->tmp, DES_BLOCK_SIZE);
        XMEMCPY(des->tmp, hold, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
    return 0;
}


int wc_Des3_CbcEncrypt(Des3* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks;

#ifdef HAVE_CAVIUM
    if (des->magic == WOLFSSL_3DES_CAVIUM_MAGIC)
        return wc_Des3_CaviumCbcEncrypt(des, out, in, sz);
#endif

    blocks = sz / DES_BLOCK_SIZE;
    while (blocks--) {
        xorbuf((byte*)des->reg, in, DES_BLOCK_SIZE);
        Des3ProcessBlock(des, (byte*)des->reg, (byte*)des->reg);
        XMEMCPY(out, des->reg, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
    return 0;
}


int wc_Des3_CbcDecrypt(Des3* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks;

#ifdef HAVE_CAVIUM
    if (des->magic == WOLFSSL_3DES_CAVIUM_MAGIC)
        return wc_Des3_CaviumCbcDecrypt(des, out, in, sz);
#endif

    blocks = sz / DES_BLOCK_SIZE;
    while (blocks--) {
        XMEMCPY(des->tmp, in, DES_BLOCK_SIZE);
        Des3ProcessBlock(des, (byte*)des->tmp, out);
        xorbuf(out, (byte*)des->reg, DES_BLOCK_SIZE);
        XMEMCPY(des->reg, des->tmp, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
    return 0;
}

#ifdef WOLFSSL_DES_ECB

/* One block, compatibility only */
int wc_Des_EcbEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;

    while (blocks--) {
        DesProcessBlock(des, in, out);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
    return 0;
}

#endif /* WOLFSSL_DES_ECB */

#endif /* STM32F2_CRYPTO */

void wc_Des_SetIV(Des* des, const byte* iv)
{
    if (des && iv)
        XMEMCPY(des->reg, iv, DES_BLOCK_SIZE);
    else if (des)
        XMEMSET(des->reg,  0, DES_BLOCK_SIZE);
}


int wc_Des_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                                                const byte* key, const byte* iv)
{
    int ret  = 0;
#ifdef WOLFSSL_SMALL_STACK
    Des* des = NULL;
#else
    Des  des[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    des = (Des*)XMALLOC(sizeof(Des), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (des == NULL)
        return MEMORY_E;
#endif

    ret = wc_Des_SetKey(des, key, iv, DES_DECRYPTION);
    if (ret == 0)
        ret = wc_Des_CbcDecrypt(des, out, in, sz); 

#ifdef WOLFSSL_SMALL_STACK
    XFREE(des, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


int wc_Des3_SetIV(Des3* des, const byte* iv)
{
    if (des && iv)
        XMEMCPY(des->reg, iv, DES_BLOCK_SIZE);
    else if (des)
        XMEMSET(des->reg,  0, DES_BLOCK_SIZE);

    return 0;
}


int wc_Des3_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                                                const byte* key, const byte* iv)
{
    int ret    = 0;
#ifdef WOLFSSL_SMALL_STACK
    Des3* des3 = NULL;
#else
    Des3  des3[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    des3 = (Des3*)XMALLOC(sizeof(Des3), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (des3 == NULL)
        return MEMORY_E;
#endif

    ret = wc_Des3_SetKey(des3, key, iv, DES_DECRYPTION);
    if (ret == 0)
        ret = wc_Des3_CbcDecrypt(des3, out, in, sz); 

#ifdef WOLFSSL_SMALL_STACK
    XFREE(des3, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


#ifdef HAVE_CAVIUM

#include "cavium_common.h"

/* Initiliaze Des3 for use with Nitrox device */
int wc_Des3_InitCavium(Des3* des3, int devId)
{
    if (des3 == NULL)
        return -1;

    if (CspAllocContext(CONTEXT_SSL, &des3->contextHandle, devId) != 0)
        return -1;

    des3->devId = devId;
    des3->magic = WOLFSSL_3DES_CAVIUM_MAGIC;
   
    return 0;
}


/* Free Des3 from use with Nitrox device */
void wc_Des3_FreeCavium(Des3* des3)
{
    if (des3 == NULL)
        return;

    if (des3->magic != WOLFSSL_3DES_CAVIUM_MAGIC)
        return;

    CspFreeContext(CONTEXT_SSL, des3->contextHandle, des3->devId);
    des3->magic = 0;
}


static int wc_Des3_CaviumSetKey(Des3* des3, const byte* key, const byte* iv)
{
    if (des3 == NULL)
        return -1;

    /* key[0] holds key, iv in reg */
    XMEMCPY(des3->key[0], key, DES_BLOCK_SIZE*3);

    return wc_Des3_SetIV(des3, iv);
}


static int wc_Des3_CaviumCbcEncrypt(Des3* des3, byte* out, const byte* in,
                                  word32 length)
{
    wolfssl_word offset = 0;
    word32 requestId;
   
    while (length > WOLFSSL_MAX_16BIT) {
        word16 slen = (word16)WOLFSSL_MAX_16BIT;
        if (CspEncrypt3Des(CAVIUM_BLOCKING, des3->contextHandle,
                           CAVIUM_NO_UPDATE, slen, (byte*)in + offset,
                           out + offset, (byte*)des3->reg, (byte*)des3->key[0],
                           &requestId, des3->devId) != 0) {
            WOLFSSL_MSG("Bad Cavium 3DES Cbc Encrypt");
            return -1;
        }
        length -= WOLFSSL_MAX_16BIT;
        offset += WOLFSSL_MAX_16BIT;
        XMEMCPY(des3->reg, out + offset - DES_BLOCK_SIZE, DES_BLOCK_SIZE);
    }
    if (length) {
        word16 slen = (word16)length;

        if (CspEncrypt3Des(CAVIUM_BLOCKING, des3->contextHandle,
                           CAVIUM_NO_UPDATE, slen, (byte*)in + offset,
                           out + offset, (byte*)des3->reg, (byte*)des3->key[0],
                           &requestId, des3->devId) != 0) {
            WOLFSSL_MSG("Bad Cavium 3DES Cbc Encrypt");
            return -1;
        }
        XMEMCPY(des3->reg, out+offset+length - DES_BLOCK_SIZE, DES_BLOCK_SIZE);
    }
    return 0;
}

static int wc_Des3_CaviumCbcDecrypt(Des3* des3, byte* out, const byte* in,
                                 word32 length)
{
    word32 requestId;
    wolfssl_word offset = 0;

    while (length > WOLFSSL_MAX_16BIT) {
        word16 slen = (word16)WOLFSSL_MAX_16BIT;
        XMEMCPY(des3->tmp, in + offset + slen - DES_BLOCK_SIZE, DES_BLOCK_SIZE);
        if (CspDecrypt3Des(CAVIUM_BLOCKING, des3->contextHandle,
                           CAVIUM_NO_UPDATE, slen, (byte*)in+offset, out+offset,
                           (byte*)des3->reg, (byte*)des3->key[0], &requestId,
                           des3->devId) != 0) {
            WOLFSSL_MSG("Bad Cavium 3Des Decrypt");
            return -1;
        }
        length -= WOLFSSL_MAX_16BIT;
        offset += WOLFSSL_MAX_16BIT;
        XMEMCPY(des3->reg, des3->tmp, DES_BLOCK_SIZE);
    }
    if (length) {
        word16 slen = (word16)length;
        XMEMCPY(des3->tmp, in + offset + slen - DES_BLOCK_SIZE,DES_BLOCK_SIZE);
        if (CspDecrypt3Des(CAVIUM_BLOCKING, des3->contextHandle,
                           CAVIUM_NO_UPDATE, slen, (byte*)in+offset, out+offset,
                           (byte*)des3->reg, (byte*)des3->key[0], &requestId,
                           des3->devId) != 0) {
            WOLFSSL_MSG("Bad Cavium 3Des Decrypt");
            return -1;
        }
        XMEMCPY(des3->reg, des3->tmp, DES_BLOCK_SIZE);
    }
    return 0;
}

#endif /* HAVE_CAVIUM */
#endif /* WOLFSSL_TI_CRYPT */
#endif /* HAVE_FIPS */
#endif /* NO_DES3 */
