/**************************************************************************//**
 * @file     crypto.c
 * @version  V1.10
 * @brief  Cryptographic Accelerator driver source file
 *
 * @copyright (C) 2017 Nuvoton Technology Corp. All rights reserved.
*****************************************************************************/

#include <stdio.h>
#include <string.h>
#include "M2351.h"

#define ENABLE_DEBUG    0
#define XOM_SUPPORT     0

#if ENABLE_DEBUG
#define CRPT_DBGMSG   printf
#else
#define CRPT_DBGMSG(...)   do { } while (0)       /* disable debug */
#endif

#if defined(__ICCARM__)
# pragma diag_suppress=Pm073, Pm143        /* Misra C rule 14.7 */
#endif


/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup CRYPTO_Driver CRYPTO Driver
  @{
*/


/** @addtogroup CRYPTO_EXPORTED_FUNCTIONS CRYPTO Exported Functions
  @{
*/

/* // @cond HIDDEN_SYMBOLS */

static uint32_t g_AES_CTL[4];
static uint32_t g_TDES_CTL[4];

static char  hex_char_tbl[] = "0123456789abcdef";

static void dump_ecc_reg(char *str, uint32_t volatile regs[], int32_t count);
static char get_Nth_nibble_char(uint32_t val32, uint32_t idx);
static void Hex2Reg(char input[], uint32_t volatile reg[]);
static void Reg2Hex(int32_t count, uint32_t volatile reg[], char output[]);
static char ch2hex(char ch);
static void Hex2RegEx(char input[], uint32_t volatile reg[], int shift);
static int  get_nibble_value(char c);

/* // @endcond HIDDEN_SYMBOLS */

/**
  * @brief  Open PRNG function
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @param[in]  u32KeySize   it is PRNG key size, including:
  *         - \ref PRNG_KEY_SIZE_64
  *         - \ref PRNG_KEY_SIZE_128
  *         - \ref PRNG_KEY_SIZE_192
  *         - \ref PRNG_KEY_SIZE_256
  * @param[in]  u32SeedReload is PRNG seed reload or not, including:
  *         - \ref PRNG_SEED_CONT
  *         - \ref PRNG_SEED_RELOAD
  * @param[in]  u32Seed  The new seed. Only valid when u32SeedReload is PRNG_SEED_RELOAD.
  * @return None
  */
void PRNG_Open(CRPT_T *crpt, uint32_t u32KeySize, uint32_t u32SeedReload, uint32_t u32Seed)
{
    if(u32SeedReload)
    {
        crpt->PRNG_SEED = u32Seed;
    }

    crpt->PRNG_CTL = (u32KeySize << CRPT_PRNG_CTL_KEYSZ_Pos) |
                     (u32SeedReload << CRPT_PRNG_CTL_SEEDRLD_Pos);
}

/**
  * @brief  Start to generate one PRNG key.
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @return None
  */
void PRNG_Start(CRPT_T *crpt)
{
    crpt->PRNG_CTL |= CRPT_PRNG_CTL_START_Msk;
}

/**
  * @brief  Read the PRNG key.
  * @param[in]   crpt         The pointer of CRYPTO module 
  * @param[out]  u32RandKey  The key buffer to store newly generated PRNG key.
  * @return None
  */
void PRNG_Read(CRPT_T *crpt, uint32_t u32RandKey[])
{
    uint32_t  i, wcnt;

    wcnt = (((crpt->PRNG_CTL & CRPT_PRNG_CTL_KEYSZ_Msk) >> CRPT_PRNG_CTL_KEYSZ_Pos) + 1U) * 2U;

    for(i = 0U; i < wcnt; i++)
    {
        u32RandKey[i] = crpt->PRNG_KEY[i];
    }

    crpt->PRNG_CTL &= ~CRPT_PRNG_CTL_SEEDRLD_Msk;
}


/**
  * @brief  Open AES encrypt/decrypt function.
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @param[in]  u32Channel   AES channel. Must be 0~3.
  * @param[in]  u32EncDec    1: AES encode;  0: AES decode
  * @param[in]  u32OpMode    AES operation mode, including:
  *         - \ref AES_MODE_ECB
  *         - \ref AES_MODE_CBC
  *         - \ref AES_MODE_CFB
  *         - \ref AES_MODE_OFB
  *         - \ref AES_MODE_CTR
  *         - \ref AES_MODE_CBC_CS1
  *         - \ref AES_MODE_CBC_CS2
  *         - \ref AES_MODE_CBC_CS3
  * @param[in]  u32KeySize is AES key size, including:
  *         - \ref AES_KEY_SIZE_128
  *         - \ref AES_KEY_SIZE_192
  *         - \ref AES_KEY_SIZE_256
  * @param[in]  u32SwapType is AES input/output data swap control, including:
  *         - \ref AES_NO_SWAP
  *         - \ref AES_OUT_SWAP
  *         - \ref AES_IN_SWAP
  *         - \ref AES_IN_OUT_SWAP
  * @return None
  */
void AES_Open(CRPT_T *crpt, uint32_t u32Channel, uint32_t u32EncDec,
              uint32_t u32OpMode, uint32_t u32KeySize, uint32_t u32SwapType)
{
    crpt->AES_CTL = (u32Channel << CRPT_AES_CTL_CHANNEL_Pos) |
                    (u32EncDec << CRPT_AES_CTL_ENCRPT_Pos) |
                    (u32OpMode << CRPT_AES_CTL_OPMODE_Pos) |
                    (u32KeySize << CRPT_AES_CTL_KEYSZ_Pos) |
                    (u32SwapType << CRPT_AES_CTL_OUTSWAP_Pos);
    g_AES_CTL[u32Channel] = crpt->AES_CTL;
}

/**
  * @brief  Start AES encrypt/decrypt
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  u32DMAMode  AES DMA control, including:
  *         - \ref CRYPTO_DMA_ONE_SHOT   One shop AES encrypt/decrypt.
  *         - \ref CRYPTO_DMA_CONTINUE   Continuous AES encrypt/decrypt.
  *         - \ref CRYPTO_DMA_LAST       Last AES encrypt/decrypt of a series of AES_Start.
  * @return None
  */
void AES_Start(CRPT_T *crpt, int32_t u32Channel, uint32_t u32DMAMode)
{
    crpt->AES_CTL = g_AES_CTL[u32Channel];
    crpt->AES_CTL |= CRPT_AES_CTL_START_Msk | (u32DMAMode << CRPT_AES_CTL_DMALAST_Pos);
}

/**
  * @brief  Set AES keys
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  au32Keys    An word array contains AES keys.
  * @param[in]  u32KeySize is AES key size, including:
  *         - \ref AES_KEY_SIZE_128
  *         - \ref AES_KEY_SIZE_192
  *         - \ref AES_KEY_SIZE_256
  * @return None
  */
void AES_SetKey(CRPT_T *crpt, uint32_t u32Channel, uint32_t au32Keys[], uint32_t u32KeySize)
{
    uint32_t  i, wcnt, key_reg_addr;

    key_reg_addr = (uint32_t)&crpt->AES0_KEY[0] + (u32Channel * 0x3CUL);
    wcnt = 4UL + u32KeySize * 2UL;

    for(i = 0U; i < wcnt; i++)
    {
        outpw(key_reg_addr, au32Keys[i]);
        key_reg_addr += 4UL;
    }
}

/**
  * @brief  Set AES initial vectors
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32Channel  AES channel. Must be 0~3.
  * @param[in]  au32IV      A four entry word array contains AES initial vectors.
  * @return None
  */
void AES_SetInitVect(CRPT_T *crpt, uint32_t u32Channel, uint32_t au32IV[])
{
    uint32_t  i, key_reg_addr;

    key_reg_addr = (uint32_t)&crpt->AES0_IV[0] + (u32Channel * 0x3CUL);

    for(i = 0U; i < 4U; i++)
    {
        outpw(key_reg_addr, au32IV[i]);
        key_reg_addr += 4UL;
    }
}

/**
  * @brief  Set AES DMA transfer configuration.
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @param[in]  u32Channel   AES channel. Must be 0~3.
  * @param[in]  u32SrcAddr   AES DMA source address
  * @param[in]  u32DstAddr   AES DMA destination address
  * @param[in]  u32TransCnt  AES DMA transfer byte count
  * @return None
  */
void AES_SetDMATransfer(CRPT_T *crpt, uint32_t u32Channel, uint32_t u32SrcAddr,
                        uint32_t u32DstAddr, uint32_t u32TransCnt)
{
    uint32_t  reg_addr;

    reg_addr = (uint32_t)&crpt->AES0_SADDR + (u32Channel * 0x3CUL);
    outpw(reg_addr, u32SrcAddr);

    reg_addr = (uint32_t)&crpt->AES0_DADDR + (u32Channel * 0x3CUL);
    outpw(reg_addr, u32DstAddr);

    reg_addr = (uint32_t)&crpt->AES0_CNT + (u32Channel * 0x3CUL);
    outpw(reg_addr, u32TransCnt);
}

/**
  * @brief  Open TDES encrypt/decrypt function.
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @param[in]  u32Channel   TDES channel. Must be 0~3.
  * @param[in]  u32EncDec    1: TDES encode; 0: TDES decode
  * @param[in]  Is3DES       1: TDES; 0: DES
  * @param[in]  Is3Key       1: TDES 3 key mode; 0: TDES 2 key mode
  * @param[in]  u32OpMode    TDES operation mode, including:
  *         - \ref TDES_MODE_ECB
  *         - \ref TDES_MODE_CBC
  *         - \ref TDES_MODE_CFB
  *         - \ref TDES_MODE_OFB
  *         - \ref TDES_MODE_CTR
  * @param[in]  u32SwapType is TDES input/output data swap control and word swap control, including:
  *         - \ref TDES_NO_SWAP
  *         - \ref TDES_WHL_SWAP
  *         - \ref TDES_OUT_SWAP
  *         - \ref TDES_OUT_WHL_SWAP
  *         - \ref TDES_IN_SWAP
  *         - \ref TDES_IN_WHL_SWAP
  *         - \ref TDES_IN_OUT_SWAP
  *         - \ref TDES_IN_OUT_WHL_SWAP
  * @return None
  */
void TDES_Open(CRPT_T *crpt, uint32_t u32Channel, uint32_t u32EncDec, int32_t Is3DES, int32_t Is3Key,
               uint32_t u32OpMode, uint32_t u32SwapType)
{
    g_TDES_CTL[u32Channel] = (u32Channel << CRPT_TDES_CTL_CHANNEL_Pos) |
                             (u32EncDec << CRPT_TDES_CTL_ENCRPT_Pos) |
                             u32OpMode | (u32SwapType << CRPT_TDES_CTL_BLKSWAP_Pos);
    if(Is3DES)
    {
        g_TDES_CTL[u32Channel] |= CRPT_TDES_CTL_TMODE_Msk;
    }
    if(Is3Key)
    {
        g_TDES_CTL[u32Channel] |= CRPT_TDES_CTL_3KEYS_Msk;
    }
}

/**
  * @brief  Start TDES encrypt/decrypt
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  u32DMAMode  TDES DMA control, including:
  *         - \ref CRYPTO_DMA_ONE_SHOT   One shop TDES encrypt/decrypt.
  *         - \ref CRYPTO_DMA_CONTINUE   Continuous TDES encrypt/decrypt.
  *         - \ref CRYPTO_DMA_LAST       Last TDES encrypt/decrypt of a series of TDES_Start.
  * @return None
  */
void TDES_Start(CRPT_T *crpt, int32_t u32Channel, uint32_t u32DMAMode)
{
    g_TDES_CTL[u32Channel] |= CRPT_TDES_CTL_START_Msk | (u32DMAMode << CRPT_TDES_CTL_DMALAST_Pos);
    crpt->TDES_CTL = g_TDES_CTL[u32Channel];
}

/**
  * @brief  Set TDES keys
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  au32Keys    The TDES keys. au32Keys[0][0] is Key0 high word and au32Keys[0][1] is key0 low word.
  * @return None
  */
void TDES_SetKey(CRPT_T *crpt, uint32_t u32Channel, uint32_t au32Keys[3][2])
{
    uint32_t   i, reg_addr;

    reg_addr = (uint32_t)&crpt->TDES0_KEY1H + (0x40UL * u32Channel);

    for(i = 0U; i < 3U; i++)
    {
        outpw(reg_addr, au32Keys[i][0]);   /* TDESn_KEYxH */
        reg_addr += 4UL;
        outpw(reg_addr, au32Keys[i][1]);   /* TDESn_KEYxL */
        reg_addr += 4UL;
    }
}

/**
  * @brief  Set TDES initial vectors
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32Channel  TDES channel. Must be 0~3.
  * @param[in]  u32IVH      TDES initial vector high word.
  * @param[in]  u32IVL      TDES initial vector low word.
  * @return None
  */
void TDES_SetInitVect(CRPT_T *crpt, uint32_t u32Channel, uint32_t u32IVH, uint32_t u32IVL)
{
    uint32_t  reg_addr;

    reg_addr = (uint32_t)&crpt->TDES0_IVH + (u32Channel * 0x40UL);
    outpw(reg_addr, u32IVH);

    reg_addr = (uint32_t)&crpt->TDES0_IVL + (u32Channel * 0x40UL);
    outpw(reg_addr, u32IVL);
}

/**
  * @brief  Set TDES DMA transfer configuration.
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @param[in]  u32Channel   TDES channel. Must be 0~3.
  * @param[in]  u32SrcAddr   TDES DMA source address
  * @param[in]  u32DstAddr   TDES DMA destination address
  * @param[in]  u32TransCnt  TDES DMA transfer byte count
  * @return None
  */
void TDES_SetDMATransfer(CRPT_T *crpt, uint32_t u32Channel, uint32_t u32SrcAddr,
                         uint32_t u32DstAddr, uint32_t u32TransCnt)
{
    uint32_t  reg_addr;

    reg_addr = (uint32_t)&crpt->TDES0_SADDR + (u32Channel * 0x40UL);
    outpw(reg_addr, u32SrcAddr);

    reg_addr = (uint32_t)&crpt->TDES0_DADDR + (u32Channel * 0x40UL);
    outpw(reg_addr, u32DstAddr);

    reg_addr = (uint32_t)&crpt->TDES0_CNT + (u32Channel * 0x40UL);
    outpw(reg_addr, u32TransCnt);
}

/**
  * @brief  Open SHA encrypt function.
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32OpMode   SHA operation mode, including:
  *         - \ref SHA_MODE_SHA1
  *         - \ref SHA_MODE_SHA224
  *         - \ref SHA_MODE_SHA256
  * @param[in]  u32SwapType is SHA input/output data swap control, including:
  *         - \ref SHA_NO_SWAP
  *         - \ref SHA_OUT_SWAP
  *         - \ref SHA_IN_SWAP
  *         - \ref SHA_IN_OUT_SWAP
  * @param[in]  hmac_key_len   HMAC key byte count
  * @return None
  */
void SHA_Open(CRPT_T *crpt, uint32_t u32OpMode, uint32_t u32SwapType, uint32_t hmac_key_len)
{
    crpt->HMAC_CTL = (u32OpMode << CRPT_HMAC_CTL_OPMODE_Pos) |
                     (u32SwapType << CRPT_HMAC_CTL_OUTSWAP_Pos);

    if(hmac_key_len != 0UL)
    {
        crpt->HMAC_KEYCNT = hmac_key_len;
    }
}

/**
  * @brief  Start SHA encrypt
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  u32DMAMode  TDES DMA control, including:
  *         - \ref CRYPTO_DMA_ONE_SHOT   One shop SHA encrypt.
  *         - \ref CRYPTO_DMA_CONTINUE   Continuous SHA encrypt.
  *         - \ref CRYPTO_DMA_LAST       Last SHA encrypt of a series of SHA_Start.
  * @return None
  */
void SHA_Start(CRPT_T *crpt, uint32_t u32DMAMode)
{
    crpt->HMAC_CTL &= ~(0x7UL << CRPT_HMAC_CTL_DMALAST_Pos);
    crpt->HMAC_CTL |= CRPT_HMAC_CTL_START_Msk | (u32DMAMode << CRPT_HMAC_CTL_DMALAST_Pos);
}

/**
  * @brief  Set SHA DMA transfer
  * @param[in]  crpt         The pointer of CRYPTO module 
  * @param[in]  u32SrcAddr   SHA DMA source address
  * @param[in]  u32TransCnt  SHA DMA transfer byte count
  * @return None
  */
void SHA_SetDMATransfer(CRPT_T *crpt, uint32_t u32SrcAddr, uint32_t u32TransCnt)
{
    crpt->HMAC_SADDR = u32SrcAddr;
    crpt->HMAC_DMACNT = u32TransCnt;
}

/**
  * @brief  Read the SHA digest.
  * @param[in]   crpt       The pointer of CRYPTO module 
  * @param[out]  u32Digest  The SHA encrypt output digest.
  * @return None
  */
void SHA_Read(CRPT_T *crpt, uint32_t u32Digest[])
{
    uint32_t  i, wcnt, reg_addr;

    i = (crpt->HMAC_CTL & CRPT_HMAC_CTL_OPMODE_Msk) >> CRPT_HMAC_CTL_OPMODE_Pos;

    if(i == SHA_MODE_SHA1)
    {
        wcnt = 5UL;
    }
    else if(i == SHA_MODE_SHA224)
    {
        wcnt = 7UL;
    }
    else if(i == SHA_MODE_SHA256)
    {
        wcnt = 8UL;
    }
    else if(i == SHA_MODE_SHA384)
    {
        wcnt = 12UL;
    }
    else
    {
        /* SHA_MODE_SHA512 */
        wcnt = 16UL;
    }

    reg_addr = (uint32_t) & (crpt->HMAC_DGST[0]);
    for(i = 0UL; i < wcnt; i++)
    {
        u32Digest[i] = inpw(reg_addr);
        reg_addr += 4UL;
    }
}


/*-----------------------------------------------------------------------------------------------*/
/*                                                                                               */
/*    ECC                                                                                        */
/*                                                                                               */
/*-----------------------------------------------------------------------------------------------*/

#define ECCOP_POINT_MUL     (0x0UL << CRPT_ECC_CTL_ECCOP_Pos)
#define ECCOP_MODULE        (0x1UL << CRPT_ECC_CTL_ECCOP_Pos)
#define ECCOP_POINT_ADD     (0x2UL << CRPT_ECC_CTL_ECCOP_Pos)
#define ECCOP_POINT_DOUBLE  (0x0UL << CRPT_ECC_CTL_ECCOP_Pos)

#define MODOP_DIV           (0x0UL << CRPT_ECC_CTL_MODOP_Pos)
#define MODOP_MUL           (0x1UL << CRPT_ECC_CTL_MODOP_Pos)
#define MODOP_ADD           (0x2UL << CRPT_ECC_CTL_MODOP_Pos)
#define MODOP_SUB           (0x3UL << CRPT_ECC_CTL_MODOP_Pos)

enum
{
    CURVE_GF_P,
    CURVE_GF_2M,
};

/*-----------------------------------------------------*/
/*  Define elliptic curve (EC):                        */
/*-----------------------------------------------------*/
#if !XOM_SUPPORT // Replace with XOM ready curve table
const ECC_CURVE _Curve[] =
{
    {
        /* NIST: Curve P-192 : y^2=x^3-ax+b (mod p) */
        CURVE_P_192,
        48,     /* Echar */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFC",   /* "000000000000000000000000000000000000000000000003" */
        "64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1",
        "188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012",
        "07192b95ffc8da78631011ed6b24cdd573f977a11e794811",
        58,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFF",   /* "6277101735386680763835789423207666416083908700390324961279" */
        58,     /* Eol */
        "FFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831",   /* "6277101735386680763835789423176059013767194773182842284081" */
        192,    /* key_len */
        7,
        2,
        1,
        CURVE_GF_P
    },
    {
        /* NIST: Curve P-224 : y^2=x^3-ax+b (mod p) */
        CURVE_P_224,
        56,     /* Echar */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFE",  /* "00000000000000000000000000000000000000000000000000000003" */
        "b4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4",
        "b70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21",
        "bd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34",
        70,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "0026959946667150639794667015087019630673557916260026308143510066298881" */
        70,     /* Eol */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFF16A2E0B8F03E13DD29455C5C2A3D",  /* "0026959946667150639794667015087019625940457807714424391721682722368061" */
        224,    /* key_len */
        9,
        8,
        3,
        CURVE_GF_P
    },
    {
        /* NIST: Curve P-256 : y^2=x^3-ax+b (mod p) */
        CURVE_P_256,
        64,     /* Echar */
        "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC",  /* "0000000000000000000000000000000000000000000000000000000000000003" */
        "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b",
        "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
        78,     /* Epl */
        "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF",  /* "115792089210356248762697446949407573530086143415290314195533631308867097853951" */
        78,     /* Eol */
        "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",  /* "115792089210356248762697446949407573529996955224135760342422259061068512044369" */
        256,    /* key_len */
        10,
        5,
        2,
        CURVE_GF_P
    },
    {
        /* NIST: Curve P-384 : y^2=x^3-ax+b (mod p) */
        CURVE_P_384,
        96,     /* Echar */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFC",  /* "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003" */
        "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        116,    /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF",  /* "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319" */
        116,    /* Eol */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973",  /* "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643" */
        384,    /* key_len */
        12,
        3,
        2,
        CURVE_GF_P
    },
    {
        /* NIST: Curve P-521 : y^2=x^3-ax+b (mod p)*/
        CURVE_P_521,
        131,    /* Echar */
        "1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC",  /* "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003" */
        "051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00",
        "0c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",
        "11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",
        157,    /* Epl */
        "1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",  /* "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151" */
        157,    /* Eol */
        "1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA51868783BF2F966B7FCC0148F709A5D03BB5C9B8899C47AEBB6FB71E91386409",  /* "6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449" */
        521,    /* key_len */
        32,
        32,
        32,
        CURVE_GF_P
    },
    {
        /* NIST: Curve B-163 : y^2+xy=x^3+ax^2+b */
        CURVE_B_163,
        41,     /* Echar */
        "00000000000000000000000000000000000000001",
        "20a601907b8c953ca1481eb10512f78744a3205fd",
        "3f0eba16286a2d57ea0991168d4994637e8343e36",
        "0d51fbc6c71a0094fa2cdd545b11c5c0c797324f1",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        49,     /* Eol */
        "40000000000000000000292FE77E70C12A4234C33",   /* "5846006549323611672814742442876390689256843201587" */
        163,    /* key_len */
        7,
        6,
        3,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve B-233 : y^2+xy=x^3+ax^2+b */
        CURVE_B_233,
        59,     /* Echar 59 */
        "00000000000000000000000000000000000000000000000000000000001",
        "066647ede6c332c7f8c0923bb58213b333b20e9ce4281fe115f7d8f90ad",
        "0fac9dfcbac8313bb2139f1bb755fef65bc391f8b36f8f8eb7371fd558b",
        "1006a08a41903350678e58528bebf8a0beff867a7ca36716f7e01f81052",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        70,     /* Eol */
        "1000000000000000000000000000013E974E72F8A6922031D2603CFE0D7",  /* "6901746346790563787434755862277025555839812737345013555379383634485463" */
        233,    /* key_len */
        74,
        74,
        74,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve B-283 : y^2+xy=x^3+ax^2+b */
        CURVE_B_283,
        71,     /* Echar */
        "00000000000000000000000000000000000000000000000000000000000000000000001",
        "27b680ac8b8596da5a4af8a19a0303fca97fd7645309fa2a581485af6263e313b79a2f5",
        "5f939258db7dd90e1934f8c70b0dfec2eed25b8557eac9c80e2e198f8cdbecd86b12053",
        "3676854fe24141cb98fe6d4b20d02b4516ff702350eddb0826779c813f0df45be8112f4",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        85,     /* Eol */
        "3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEF90399660FC938A90165B042A7CEFADB307",  /* "7770675568902916283677847627294075626569625924376904889109196526770044277787378692871" */
        283,    /* key_len */
        12,
        7,
        5,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve B-409 : y^2+xy=x^3+ax^2+b */
        CURVE_B_409,
        103,    /* Echar */
        "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "021a5c2c8ee9feb5c4b9a753b7b476b7fd6422ef1f3dd674761fa99d6ac27c8a9a197b272822f6cd57a55aa4f50ae317b13545f",
        "15d4860d088ddb3496b0c6064756260441cde4af1771d4db01ffe5b34e59703dc255a868a1180515603aeab60794e54bb7996a7",
        "061b1cfab6be5f32bbfa78324ed106a7636b9c5a7bd198d0158aa4f5488d08f38514f1fdf4b4f40d2181b3681c364ba0273c706",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        123,    /* Eol */
        "10000000000000000000000000000000000000000000000000001E2AAD6A612F33307BE5FA47C3C9E052F838164CD37D9A21173",  /* "661055968790248598951915308032771039828404682964281219284648798304157774827374805208143723762179110965979867288366567526771" */
        409,    /* key_len */
        87,
        87,
        87,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve B-571 : y^2+xy=x^3+ax^2+b */
        CURVE_B_571,
        143,    /* Echar */
        "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "2f40e7e2221f295de297117b7f3d62f5c6a97ffcb8ceff1cd6ba8ce4a9a18ad84ffabbd8efa59332be7ad6756a66e294afd185a78ff12aa520e4de739baca0c7ffeff7f2955727a",
        "303001d34b856296c16c0d40d3cd7750a93d1d2955fa80aa5f40fc8db7b2abdbde53950f4c0d293cdd711a35b67fb1499ae60038614f1394abfa3b4c850d927e1e7769c8eec2d19",
        "37bf27342da639b6dccfffeb73d69d78c6c27a6009cbbca1980f8533921e8a684423e43bab08a576291af8f461bb2a8b3531d2f0485c19b16e2f1516e23dd3c1a4827af1b8ac15b",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        172,    /* Eol */
        "3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE661CE18FF55987308059B186823851EC7DD9CA1161DE93D5174D66E8382E9BB2FE84E47",  /* "3864537523017258344695351890931987344298927329706434998657235251451519142289560424536143999389415773083133881121926944486246872462816813070234528288303332411393191105285703" */
        571,    /* key_len */
        10,
        5,
        2,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve K-163 : y^2+xy=x^3+ax^2+b */
        CURVE_K_163,
        41,     /* Echar */
        "00000000000000000000000000000000000000001",
        "00000000000000000000000000000000000000001",
        "2fe13c0537bbc11acaa07d793de4e6d5e5c94eee8",
        "289070fb05d38ff58321f2e800536d538ccdaa3d9",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        49,     /* Eol */
        "4000000000000000000020108A2E0CC0D99F8A5EF",  /* "5846006549323611672814741753598448348329118574063" */
        163,    /* key_len */
        7,
        6,
        3,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve K-233 : y^2+xy=x^3+ax^2+b */
        CURVE_K_233,
        59,     /* Echar 59 */
        "00000000000000000000000000000000000000000000000000000000000",
        "00000000000000000000000000000000000000000000000000000000001",
        "17232ba853a7e731af129f22ff4149563a419c26bf50a4c9d6eefad6126",
        "1db537dece819b7f70f555a67c427a8cd9bf18aeb9b56e0c11056fae6a3",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",    /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        70,     /* Eol */
        "8000000000000000000000000000069D5BB915BCD46EFB1AD5F173ABDF",  /* "3450873173395281893717377931138512760570940988862252126328087024741343" */
        233,    /* key_len */
        74,
        74,
        74,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve K-283 : y^2+xy=x^3+ax^2+b */
        CURVE_K_283,
        71,     /* Echar */
        "00000000000000000000000000000000000000000000000000000000000000000000000",
        "00000000000000000000000000000000000000000000000000000000000000000000001",
        "503213f78ca44883f1a3b8162f188e553cd265f23c1567a16876913b0c2ac2458492836",
        "1ccda380f1c9e318d90f95d07e5426fe87e45c0e8184698e45962364e34116177dd2259",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        85,     /* Eol */
        "1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE9AE2ED07577265DFF7F94451E061E163C61",  /* "3885337784451458141838923813647037813284811733793061324295874997529815829704422603873" */
        283,    /* key_len */
        12,
        7,
        5,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve K-409 : y^2+xy=x^3+ax^2+b */
        CURVE_K_409,
        103,    /* Echar */
        "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "060f05f658f49c1ad3ab1890f7184210efd0987e307c84c27accfb8f9f67cc2c460189eb5aaaa62ee222eb1b35540cfe9023746",
        "1e369050b7c4e42acba1dacbf04299c3460782f918ea427e6325165e9ea10e3da5f6c42e9c55215aa9ca27a5863ec48d8e0286b",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        123,    /* Eol */
        "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE5F83B2D4EA20400EC4557D5ED3E3E7CA5B4B5C83B8E01E5FCF",  /* "330527984395124299475957654016385519914202341482140609642324395022880711289249191050673258457777458014096366590617731358671" */
        409,    /* key_len */
        87,
        87,
        87,
        CURVE_GF_2M
    },
    {
        /* NIST: Curve K-571 : y^2+xy=x^3+ax^2+b */
        CURVE_K_571,
        143,    /* Echar */
        "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "26eb7a859923fbc82189631f8103fe4ac9ca2970012d5d46024804801841ca44370958493b205e647da304db4ceb08cbbd1ba39494776fb988b47174dca88c7e2945283a01c8972",
        "349dc807f4fbf374f4aeade3bca95314dd58cec9f307a54ffc61efc006d8a2c9d4979c0ac44aea74fbebbb9f772aedcb620b01a7ba7af1b320430c8591984f601cd4c143ef1c7a3",
        68,     /* Epl */
        "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001",  /* "26959946667150639794667015087019630673557916260026308143510066298881" */
        172,    /* Eol */
        "20000000000000000000000000000000000000000000000000000000000000000000000131850E1F19A63E4B391A8DB917F4138B630D84BE5D639381E91DEB45CFE778F637C1001",  /* "1932268761508629172347675945465993672149463664853217499328617625725759571144780212268133978522706711834706712800825351461273674974066617311929682421617092503555733685276673" */
        571,    /* key_len */
        10,
        5,
        2,
        CURVE_GF_2M
    },
};
#endif


static ECC_CURVE  *pCurve;
static ECC_CURVE  Curve_Copy;

static ECC_CURVE * get_curve(E_ECC_CURVE ecc_curve);
static int32_t ecc_init_curve(CRPT_T *crpt, E_ECC_CURVE ecc_curve);
static void run_ecc_codec(CRPT_T *crpt, uint32_t mode);

static char  temp_hex_str[160];

volatile uint32_t g_ECC_done, g_ECCERR_done;

void ECC_DriverISR(CRPT_T *crpt)
{
    if(crpt->INTSTS & CRPT_INTSTS_ECCIF_Msk)
    {
        g_ECC_done = 1UL;
        crpt->INTSTS = CRPT_INTSTS_ECCIF_Msk;
        /* printf("ECC done IRQ.\n"); */
    }

    if(crpt->INTSTS & CRPT_INTSTS_ECCEIF_Msk)
    {
        g_ECCERR_done = 1UL;
        crpt->INTSTS = CRPT_INTSTS_ECCEIF_Msk;
        /* printf("ECCERRIF is set!!\n"); */
    }
}


#if ENABLE_DEBUG
static void dump_ecc_reg(char *str, uint32_t volatile regs[], int32_t count)
{
    int32_t  i;

    printf("%s => ", str);
    for(i = 0; i < count; i++)
    {
        printf("0x%08x ", regs[i]);
    }
    printf("\n");
}
#else
static void dump_ecc_reg(char *str, uint32_t volatile regs[], int32_t count) { }
#endif
static char  ch2hex(char ch)
{
    if(ch <= '9')
    {
        return ch - '0';
    }
    else if((ch <= 'z') && (ch >= 'a'))
    {
        return ch - 'a' + 10U;
    }
    else
    {
        return ch - 'A' + 10U;
    }
}

static void Hex2Reg(char input[], uint32_t volatile reg[])
{
    char      hex;
    int       si, ri;
    uint32_t  i, val32;

    si = (int)strlen(input) - 1;
    ri = 0;

    while(si >= 0)
    {
        val32 = 0UL;
        for(i = 0UL; (i < 8UL) && (si >= 0); i++)
        {
            hex = ch2hex(input[si]);
            val32 |= (uint32_t)hex << (i * 4UL);
            si--;
        }
        reg[ri++] = val32;
    }
}

static void Hex2RegEx(char input[], uint32_t volatile reg[], int shift)
{
    uint32_t  hex, carry;
    int       si, ri;
    uint32_t  i, val32;

    si = (int)strlen(input) - 1;
    ri = 0;
    carry = 0U;
    while(si >= 0)
    {
        val32 = 0UL;
        for(i = 0UL; (i < 8UL) && (si >= 0); i++)
        {
            hex = (uint32_t)ch2hex(input[si]);
            hex <<= shift;

            val32 |= (uint32_t)((hex & 0xFU) | carry) << (i * 4UL);
            carry = (hex >> 4) & 0xFU;
            si--;
        }
        reg[ri++] = val32;
    }
    if(carry != 0U)
    {
        reg[ri] = carry;
    }
}

/**
  * @brief  Extract specified nibble from an unsigned word in character format.
  *         For example:
  *                Suppose val32 is 0x786543210, get_Nth_nibble_char(val32, 3) will return a '3'.
  * @param[in]  val32   The input unsigned word
  * @param[in]  idx     The Nth nibble to be extracted.
  * @return  The nibble in character format.
  */
static char get_Nth_nibble_char(uint32_t val32, uint32_t idx)
{
    return hex_char_tbl[(val32 >> (idx * 4U)) & 0xfU ];
}


static void Reg2Hex(int32_t count, uint32_t volatile reg[], char output[])
{
    int32_t    idx, ri;
    uint32_t   i;

    output[count] = 0U;
    idx = count - 1;

    for(ri = 0; idx >= 0; ri++)
    {
        for(i = 0UL; (i < 8UL) && (idx >= 0); i++)
        {
            output[idx] = get_Nth_nibble_char(reg[ri], i);
            idx--;
        }
    }
}

static int32_t ecc_init_curve(CRPT_T *crpt, E_ECC_CURVE ecc_curve)
{
    int32_t  i, ret = 0;

    pCurve = get_curve(ecc_curve);
    if(pCurve == NULL)
    {
        CRPT_DBGMSG("Cannot find curve %d!!\n", ecc_curve);
        ret = -1;
    }

    if(ret == 0)
    {
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_A[i] = 0UL;
            crpt->ECC_B[i] = 0UL;
            crpt->ECC_X1[i] = 0UL;
            crpt->ECC_Y1[i] = 0UL;
            crpt->ECC_N[i] = 0UL;
        }

        Hex2Reg(pCurve->Ea, crpt->ECC_A);
        Hex2Reg(pCurve->Eb, crpt->ECC_B);
        Hex2Reg(pCurve->Px, crpt->ECC_X1);
        Hex2Reg(pCurve->Py, crpt->ECC_Y1);

        CRPT_DBGMSG("Key length = %d\n", pCurve->key_len);
        dump_ecc_reg("CRPT_ECC_CURVE_A", crpt->ECC_A, 10);
        dump_ecc_reg("CRPT_ECC_CURVE_B", crpt->ECC_B, 10);
        dump_ecc_reg("CRPT_ECC_POINT_X1", crpt->ECC_X1, 10);
        dump_ecc_reg("CRPT_ECC_POINT_Y1", crpt->ECC_Y1, 10);

        if(pCurve->GF == (int)CURVE_GF_2M)
        {
            crpt->ECC_N[0] = 0x1UL;
            crpt->ECC_N[(pCurve->key_len) / 32] |= (1UL << ((pCurve->key_len) % 32));
            crpt->ECC_N[(pCurve->irreducible_k1) / 32] |= (1UL << ((pCurve->irreducible_k1) % 32));
            crpt->ECC_N[(pCurve->irreducible_k2) / 32] |= (1UL << ((pCurve->irreducible_k2) % 32));
            crpt->ECC_N[(pCurve->irreducible_k3) / 32] |= (1UL << ((pCurve->irreducible_k3) % 32));
        }
        else
        {
            Hex2Reg(pCurve->Pp, crpt->ECC_N);
        }
    }
    dump_ecc_reg("CRPT_ECC_CURVE_N", crpt->ECC_N, 10);
    return ret;
}


static int  get_nibble_value(char c)
{
    char ch;

    if((c >= '0') && (c <= '9'))
    {
        ch = '0';
        return ((int)c - (int)ch);
    }

    if((c >= 'a') && (c <= 'f'))
    {
        ch = 'a';
        return ((int)c - (int)ch + 10);
    }

    if((c >= 'A') && (c <= 'F'))
    {
        ch = 'A';
        return ((int)c - (int)ch + 10);
    }
    return 0;
}


/**
  * @brief  Check if the private key is located in valid range of curve.
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  private_k   The input private key.
  * @return  1    Is valid.
  * @return  0    Is not valid.
  * @return  -1   Invalid curve.
  */
int ECC_IsPrivateKeyValid(CRPT_T *crpt, E_ECC_CURVE ecc_curve,  char private_k[])
{
    uint32_t  i;


    pCurve = get_curve(ecc_curve);
    if(pCurve == NULL)
    {
        return -1;
    }

    if(strlen(private_k) < strlen(pCurve->Eorder))
    {
        return 1;
    }

    if(strlen(private_k) > strlen(pCurve->Eorder))
    {
        return 0;
    }

    for(i = 0U; i < strlen(private_k); i++)
    {
        if(get_nibble_value(private_k[i]) < get_nibble_value(pCurve->Eorder[i]))
        {
            return 1;
        }

        if(get_nibble_value(private_k[i]) > get_nibble_value(pCurve->Eorder[i]))
        {
            return 0;
        }
    }
    return 0;
}


/**
  * @brief  Given a private key and curve to generate the public key pair.
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  private_k   The input private key.
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[out] public_k1   The output publick key 1.
  * @param[out] public_k2   The output publick key 2.
  * @return  0    Success.
  * @return  -1   "ecc_curve" value is invalid.
  */
int32_t  ECC_GeneratePublicKey(CRPT_T *crpt, E_ECC_CURVE ecc_curve, char *private_k, char public_k1[], char public_k2[])
{
    int32_t  ret = 0, i;
    uint32_t u32Tmp;

    if(ecc_init_curve(crpt, ecc_curve) != 0)
    {
        ret = -1;
    }

    if(ret == 0)
    {
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_K[i] = 0UL;
        }

        Hex2Reg(private_k, crpt->ECC_K);

        /* set FSEL (Field selection) */
        if(pCurve->GF == (int)CURVE_GF_2M)
        {
            crpt->ECC_CTL = 0UL;
        }
        else           /*  CURVE_GF_P */
        {
            crpt->ECC_CTL = CRPT_ECC_CTL_FSEL_Msk;
        }

        g_ECC_done = g_ECCERR_done = 0UL;
        crpt->ECC_CTL |= ((uint32_t)pCurve->key_len << CRPT_ECC_CTL_CURVEM_Pos) |
                         ECCOP_POINT_MUL | CRPT_ECC_CTL_START_Msk;

        do
        {
            u32Tmp = g_ECC_done;
            u32Tmp |= g_ECCERR_done;
        }
        while(u32Tmp == 0UL);

        Reg2Hex(pCurve->Echar, crpt->ECC_X1, public_k1);
        Reg2Hex(pCurve->Echar, crpt->ECC_Y1, public_k2);
    }

    return ret;
}


/**
  * @brief  Given a curve parameter, the other party's public key, and one's own private key to generate the secret Z.
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  private_k   One's own private key.
  * @param[in]  public_k1   The other party's publick key 1.
  * @param[in]  public_k2   The other party's publick key 2.
  * @param[out] secret_z    The ECC CDH secret Z.
  * @return  0    Success.
  * @return  -1   "ecc_curve" value is invalid.
  */
int32_t  ECC_GenerateSecretZ(CRPT_T *crpt, E_ECC_CURVE ecc_curve, char *private_k, char public_k1[], char public_k2[], char secret_z[])
{
    int32_t  i, ret = 0;
    uint32_t u32Tmp;

    if(ecc_init_curve(crpt, ecc_curve) != 0)
    {
        ret = -1;
    }

    if(ret == 0)
    {
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_K[i] = 0UL;
            crpt->ECC_X1[i] = 0UL;
            crpt->ECC_Y1[i] = 0UL;
        }

        if((ecc_curve == CURVE_B_163) || (ecc_curve == CURVE_B_233) || (ecc_curve == CURVE_B_283) ||
                (ecc_curve == CURVE_B_409) || (ecc_curve == CURVE_B_571) || (ecc_curve == CURVE_K_163))
        {
            Hex2RegEx(private_k, crpt->ECC_K, 1);
        }
        else if((ecc_curve == CURVE_K_233) || (ecc_curve == CURVE_K_283) ||
                (ecc_curve == CURVE_K_409) || (ecc_curve == CURVE_K_571))
        {
            Hex2RegEx(private_k, crpt->ECC_K, 2);
        }
        else
        {
            Hex2Reg(private_k, crpt->ECC_K);
        }

        Hex2Reg(public_k1, crpt->ECC_X1);
        Hex2Reg(public_k2, crpt->ECC_Y1);

        /* set FSEL (Field selection) */
        if(pCurve->GF == (int)CURVE_GF_2M)
        {
            crpt->ECC_CTL = 0UL;
        }
        else           /*  CURVE_GF_P */
        {
            crpt->ECC_CTL = CRPT_ECC_CTL_FSEL_Msk;
        }
        g_ECC_done = g_ECCERR_done = 0UL;
        crpt->ECC_CTL |= ((uint32_t)pCurve->key_len << CRPT_ECC_CTL_CURVEM_Pos) |
                         ECCOP_POINT_MUL | CRPT_ECC_CTL_START_Msk;

        do
        {
            u32Tmp = g_ECC_done;
            u32Tmp |= g_ECCERR_done;
        }
        while(u32Tmp == 0UL);

        Reg2Hex(pCurve->Echar, crpt->ECC_X1, secret_z);
    }

    return ret;
}

static void run_ecc_codec(CRPT_T *crpt, uint32_t mode)
{
    uint32_t u32Tmp;

    if((mode & CRPT_ECC_CTL_ECCOP_Msk) == ECCOP_MODULE)
    {
        crpt->ECC_CTL = CRPT_ECC_CTL_FSEL_Msk;
    }
    else
    {
        if(pCurve->GF == (int)CURVE_GF_2M)
        {
            /* point */
            crpt->ECC_CTL = 0UL;
        }
        else
        {
            /* CURVE_GF_P */
            crpt->ECC_CTL = CRPT_ECC_CTL_FSEL_Msk;
        }
    }

    g_ECC_done = g_ECCERR_done = 0UL;
    crpt->ECC_CTL |= ((uint32_t)pCurve->key_len << CRPT_ECC_CTL_CURVEM_Pos) | mode | CRPT_ECC_CTL_START_Msk;

    do
    {
        u32Tmp = g_ECC_done;
        u32Tmp |= g_ECCERR_done;
    }
    while(u32Tmp == 0UL);

    while(crpt->ECC_STS & CRPT_ECC_STS_BUSY_Msk) { }
}

/**
  * @brief  ECDSA digital signature generation.
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  message     The hash value of source context.
  * @param[in]  d           The private key.
  * @param[in]  k           The selected random integer.
  * @param[out] R           R of the (R,S) pair digital signature
  * @param[out] S           S of the (R,S) pair digital signature
  * @return  0    Success.
  * @return  -1   "ecc_curve" value is invalid.
  */
int32_t  ECC_GenerateSignature(CRPT_T *crpt, E_ECC_CURVE ecc_curve, char *message,
                               char *d, char *k, char *R, char *S)
{
    uint32_t volatile temp_result1[18], temp_result2[18];
    int32_t  i, ret = 0;

    if(ecc_init_curve(crpt, ecc_curve) != 0)
    {
        ret = -1;
    }

    if(ret == 0)
    {

        /*
         *   1. Calculate e = HASH(m), where HASH is a cryptographic hashing algorithm, (i.e. SHA-1)
         *      (1) Use SHA to calculate e
         */

        /*   2. Select a random integer k form [1, n-1]
         *      (1) Notice that n is order, not prime modulus or irreducible polynomial function
         */

        /*
         *   3. Compute r = x1 (mod n), where (x1, y1) = k * G. If r = 0, go to step 2
         *      (1) Write the curve parameter A, B, and curve length M to corresponding registers
         *      (2) Write the prime modulus or irreducible polynomial function to N registers according
         *      (3) Write the point G(x, y) to X1, Y1 registers
         *      (4) Write the random integer k to K register
         *      (5) Set ECCOP(CRPT_ECC_CTL[10:9]) to 00
         *      (6) Set FSEL(CRPT_ECC_CTL[8]) according to used curve of prime field or binary field
         *      (7) Set START(CRPT_ECC_CTL[0]) to 1
         *      (8) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (9) Write the curve order and curve length to N ,M registers according
         *      (10) Write 0x0 to Y1 registers
         *      (11) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (12) Set MOPOP(CRPT_ECC_CTL[12:11]) to 10
         *      (13) Set START(CRPT_ECC_CTL[0]) to 1         *
         *      (14) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (15) Read X1 registers to get r
         */

        /* 3-(4) Write the random integer k to K register */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_K[i] = 0UL;
        }
        Hex2Reg(k, crpt->ECC_K);

        run_ecc_codec(crpt, ECCOP_POINT_MUL);

        /*  3-(9) Write the curve order to N registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /* 3-(10) Write 0x0 to Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = 0UL;
        }

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_ADD);

        /* 3-(15) Read X1 registers to get r */
        for(i = 0; i < 18; i++)
        {
            temp_result1[i] = crpt->ECC_X1[i];
        }

        Reg2Hex(pCurve->Echar, temp_result1, R);

        /*
         *   4. Compute s = k ? 1 ｝ (e + d ｝ r)(mod n). If s = 0, go to step 2
         *      (1) Write the curve order to N registers according
         *      (2) Write 0x1 to Y1 registers
         *      (3) Write the random integer k to X1 registers according
         *      (4) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (5) Set MOPOP(CRPT_ECC_CTL[12:11]) to 00
         *      (6) Set START(CRPT_ECC_CTL[0]) to 1
         *      (7) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (8) Read X1 registers to get k^-1
         *      (9) Write the curve order and curve length to N ,M registers
         *      (10) Write r, d to X1, Y1 registers
         *      (11) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (12) Set MOPOP(CRPT_ECC_CTL[12:11]) to 01
         *      (13) Set START(CRPT_ECC_CTL[0]) to 1
         *      (14) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (15) Write the curve order to N registers
         *      (16) Write e to Y1 registers
         *      (17) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (18) Set MOPOP(CRPT_ECC_CTL[12:11]) to 10
         *      (19) Set START(CRPT_ECC_CTL[0]) to 1
         *      (20) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (21) Write the curve order and curve length to N ,M registers
         *      (22) Write k^-1 to Y1 registers
         *      (23) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (24) Set MOPOP(CRPT_ECC_CTL[12:11]) to 01
         *      (25) Set START(CRPT_ECC_CTL[0]) to 1
         *      (26) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (27) Read X1 registers to get s
         */

        /* S/W: GFp_add_mod_order(pCurve->key_len+2, 0, x1, a, R); */

        /*  4-(1) Write the curve order to N registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /*  4-(2) Write 0x1 to Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = 0UL;
        }
        crpt->ECC_Y1[0] = 0x1UL;

        /*  4-(3) Write the random integer k to X1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = 0UL;
        }
        Hex2Reg(k, crpt->ECC_X1);

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_DIV);

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, crpt->ECC_X1, temp_hex_str);
        CRPT_DBGMSG("(7) output = %s\n", temp_hex_str);
#endif

        /*  4-(8) Read X1 registers to get k^-1 */

        for(i = 0; i < 18; i++)
        {
            temp_result2[i] = crpt->ECC_X1[i];
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, temp_result2, temp_hex_str);
        CRPT_DBGMSG("k^-1 = %s\n", temp_hex_str);
#endif

        /*  4-(9) Write the curve order and curve length to N ,M registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /*  4-(10) Write r, d to X1, Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = temp_result1[i];
        }

        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = 0UL;
        }
        Hex2Reg(d, crpt->ECC_Y1);

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_MUL);

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, crpt->ECC_X1, temp_hex_str);
        CRPT_DBGMSG("(14) output = %s\n", temp_hex_str);
#endif

        /*  4-(15) Write the curve order to N registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /*  4-(16) Write e to Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = 0UL;
        }

        Hex2Reg(message, crpt->ECC_Y1);

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_ADD);

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, crpt->ECC_X1, temp_hex_str);
        CRPT_DBGMSG("(20) output = %s\n", temp_hex_str);
#endif

        /*  4-(21) Write the curve order and curve length to N ,M registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /*  4-(22) Write k^-1 to Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = temp_result2[i];
        }

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_MUL);

        /*  4-(27) Read X1 registers to get s */
        for(i = 0; i < 18; i++)
        {
            temp_result2[i] = crpt->ECC_X1[i];
        }

        Reg2Hex(pCurve->Echar, temp_result2, S);

    }  /* ret == 0 */

    return ret;
}

/**
  * @brief  ECDSA dogotal signature verification.
  * @param[in]  crpt        The pointer of CRYPTO module 
  * @param[in]  ecc_curve   The pre-defined ECC curve.
  * @param[in]  message     The hash value of source context.
  * @param[in]  public_k1   The public key 1.
  * @param[in]  public_k2   The public key 2.
  * @param[in]  R           R of the (R,S) pair digital signature
  * @param[in]  S           S of the (R,S) pair digital signature
  * @return  0    Success.
  * @return  -1   "ecc_curve" value is invalid.
  * @return  -2   Verification failed.
  */
int32_t  ECC_VerifySignature(CRPT_T *crpt, E_ECC_CURVE ecc_curve, char *message,
                             char *public_k1, char *public_k2, char *R, char *S)
{
    uint32_t  temp_result1[18], temp_result2[18];
    uint32_t  temp_x[18], temp_y[18];
    int32_t   i, ret = 0;

    /*
     *   1. Verify that r and s are integers in the interval [1, n-1]. If not, the signature is invalid
     *   2. Compute e = HASH (m), where HASH is the hashing algorithm in signature generation
     *      (1) Use SHA to calculate e
     */

    /*
     *   3. Compute w = s^-1 (mod n)
     *      (1) Write the curve order to N registers
     *      (2) Write 0x1 to Y1 registers
     *      (3) Write s to X1 registers
     *      (4) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
     *      (5) Set MOPOP(CRPT_ECC_CTL[12:11]) to 00
     *      (6) Set FSEL(CRPT_ECC_CTL[8]) according to used curve of prime field or binary field
     *      (7) Set START(CRPT_ECC_CTL[0]) to 1
     *      (8) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
     *      (9) Read X1 registers to get w
     */

    if(ecc_init_curve(crpt, ecc_curve) != 0)
    {
        ret = -1;
    }

    if(ret == 0)
    {

        /*  3-(1) Write the curve order to N registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /*  3-(2) Write 0x1 to Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = 0UL;
        }
        crpt->ECC_Y1[0] = 0x1UL;

        /*  3-(3) Write s to X1 registers */
        for(i = 0; i < 18; i++)
        {
            CRPT->ECC_X1[i] = 0UL;
        }
        Hex2Reg(S, crpt->ECC_X1);

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_DIV);

        /*  3-(9) Read X1 registers to get w */
        for(i = 0; i < 18; i++)
        {
            temp_result2[i] = crpt->ECC_X1[i];
        }

#if ENABLE_DEBUG
        CRPT_DBGMSG("e = %s\n", message);
        Reg2Hex(pCurve->Echar, temp_result2, temp_hex_str);
        CRPT_DBGMSG("w = %s\n", temp_hex_str);
        CRPT_DBGMSG("o = %s (order)\n", pCurve->Eorder);
#endif

        /*
         *   4. Compute u1 = e ｝ w (mod n) and u2 = r ｝ w (mod n)
         *      (1) Write the curve order and curve length to N ,M registers
         *      (2) Write e, w to X1, Y1 registers
         *      (3) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (4) Set MOPOP(CRPT_ECC_CTL[12:11]) to 01
         *      (5) Set START(CRPT_ECC_CTL[0]) to 1
         *      (6) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (7) Read X1 registers to get u1
         *      (8) Write the curve order and curve length to N ,M registers
         *      (9) Write r, w to X1, Y1 registers
         *      (10) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (11) Set MOPOP(CRPT_ECC_CTL[12:11]) to 01
         *      (12) Set START(CRPT_ECC_CTL[0]) to 1
         *      (13) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (14) Read X1 registers to get u2
         */

        /*  4-(1) Write the curve order and curve length to N ,M registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /* 4-(2) Write e, w to X1, Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = 0UL;
        }
        Hex2Reg(message, crpt->ECC_X1);

        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = temp_result2[i];
        }

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_MUL);

        /*  4-(7) Read X1 registers to get u1 */
        for(i = 0; i < 18; i++)
        {
            temp_result1[i] = crpt->ECC_X1[i];
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, temp_result1, temp_hex_str);
        CRPT_DBGMSG("u1 = %s\n", temp_hex_str);
#endif

        /*  4-(8) Write the curve order and curve length to N ,M registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /* 4-(9) Write r, w to X1, Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = 0UL;
        }
        Hex2Reg(R, crpt->ECC_X1);

        for(i = 0; i < 18; i++)
        {
            crpt->ECC_Y1[i] = temp_result2[i];
        }

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_MUL);

        /*  4-(14) Read X1 registers to get u2 */
        for(i = 0; i < 18; i++)
        {
            temp_result2[i] = crpt->ECC_X1[i];
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, temp_result2, temp_hex_str);
        CRPT_DBGMSG("u2 = %s\n", temp_hex_str);
#endif

        /*
         *   5. Compute X・ (x1・, y1・) = u1 * G + u2 * Q
         *      (1) Write the curve parameter A, B, N, and curve length M to corresponding registers
         *      (2) Write the point G(x, y) to X1, Y1 registers
         *      (3) Write u1 to K registers
         *      (4) Set ECCOP(CRPT_ECC_CTL[10:9]) to 00
         *      (5) Set START(CRPT_ECC_CTL[0]) to 1
         *      (6) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (7) Read X1, Y1 registers to get u1*G
         *      (8) Write the curve parameter A, B, N, and curve length M to corresponding registers
         *      (9) Write the public key Q(x,y) to X1, Y1 registers
         *      (10) Write u2 to K registers
         *      (11) Set ECCOP(CRPT_ECC_CTL[10:9]) to 00
         *      (12) Set START(CRPT_ECC_CTL[0]) to 1
         *      (13) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (14) Write the curve parameter A, B, N, and curve length M to corresponding registers
         *      (15) Write the result data u1*G to X2, Y2 registers
         *      (16) Set ECCOP(CRPT_ECC_CTL[10:9]) to 10
         *      (17) Set START(CRPT_ECC_CTL[0]) to 1
         *      (18) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (19) Read X1, Y1 registers to get X・(x1・, y1・)
         *      (20) Write the curve order and curve length to N ,M registers
         *      (21) Write x1・ to X1 registers
         *      (22) Write 0x0 to Y1 registers
         *      (23) Set ECCOP(CRPT_ECC_CTL[10:9]) to 01
         *      (24) Set MOPOP(CRPT_ECC_CTL[12:11]) to 10
         *      (25) Set START(CRPT_ECC_CTL[0]) to 1
         *      (26) Wait for BUSY(CRPT_ECC_STS[0]) be cleared
         *      (27) Read X1 registers to get x1・ (mod n)
         *
         *   6. The signature is valid if x1・ = r, otherwise it is invalid
         */

        /*
         *  (1) Write the curve parameter A, B, N, and curve length M to corresponding registers
         *  (2) Write the point G(x, y) to X1, Y1 registers
         */
        ecc_init_curve(crpt, ecc_curve);

        /* (3) Write u1 to K registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_K[i] = temp_result1[i];
        }

        run_ecc_codec(crpt, ECCOP_POINT_MUL);

        /* (7) Read X1, Y1 registers to get u1*G */
        for(i = 0; i < 18; i++)
        {
            temp_x[i] = crpt->ECC_X1[i];
            temp_y[i] = crpt->ECC_Y1[i];
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, temp_x, temp_hex_str);
        CRPT_DBGMSG("5-(7) u1*G, x = %s\n", temp_hex_str);
        Reg2Hex(pCurve->Echar, temp_y, temp_hex_str);
        CRPT_DBGMSG("5-(7) u1*G, y = %s\n", temp_hex_str);
#endif

        /* (8) Write the curve parameter A, B, N, and curve length M to corresponding registers */
        ecc_init_curve(crpt, ecc_curve);

        /* (9) Write the public key Q(x,y) to X1, Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = 0UL;
            crpt->ECC_Y1[i] = 0UL;
        }

        Hex2Reg(public_k1, crpt->ECC_X1);
        Hex2Reg(public_k2, crpt->ECC_Y1);

        /* (10) Write u2 to K registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_K[i] = temp_result2[i];
        }

        run_ecc_codec(crpt, ECCOP_POINT_MUL);

        for(i = 0; i < 18; i++)
        {
            temp_result1[i] = crpt->ECC_X1[i];
            temp_result2[i] = crpt->ECC_Y1[i];
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, temp_result1, temp_hex_str);
        CRPT_DBGMSG("5-(13) u2*Q, x = %s\n", temp_hex_str);
        Reg2Hex(pCurve->Echar, temp_result2, temp_hex_str);
        CRPT_DBGMSG("5-(13) u2*Q, y = %s\n", temp_hex_str);
#endif

        /* (14) Write the curve parameter A, B, N, and curve length M to corresponding registers */
        ecc_init_curve(crpt, ecc_curve);

        /* Write the result data u2*Q to X1, Y1 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = temp_result1[i];
            crpt->ECC_Y1[i] = temp_result2[i];
        }

        /* (15) Write the result data u1*G to X2, Y2 registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X2[i] = temp_x[i];
            crpt->ECC_Y2[i] = temp_y[i];
        }

        run_ecc_codec(crpt, ECCOP_POINT_ADD);

        /* (19) Read X1, Y1 registers to get X・(x1・, y1・) */
        for(i = 0; i < 18; i++)
        {
            temp_x[i] = crpt->ECC_X1[i];
            temp_y[i] = crpt->ECC_Y1[i];
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, temp_x, temp_hex_str);
        CRPT_DBGMSG("5-(19) x' = %s\n", temp_hex_str);
        Reg2Hex(pCurve->Echar, temp_y, temp_hex_str);
        CRPT_DBGMSG("5-(19) y' = %s\n", temp_hex_str);
#endif

        /*  (20) Write the curve order and curve length to N ,M registers */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_N[i] = 0UL;
        }
        Hex2Reg(pCurve->Eorder, crpt->ECC_N);

        /*
         *  (21) Write x1・ to X1 registers
         *  (22) Write 0x0 to Y1 registers
         */
        for(i = 0; i < 18; i++)
        {
            crpt->ECC_X1[i] = temp_x[i];
            crpt->ECC_Y1[i] = 0UL;
        }

#if ENABLE_DEBUG
        Reg2Hex(pCurve->Echar, crpt->ECC_X1, temp_hex_str);
        CRPT_DBGMSG("5-(21) x' = %s\n", temp_hex_str);
        Reg2Hex(pCurve->Echar, crpt->ECC_Y1, temp_hex_str);
        CRPT_DBGMSG("5-(22) y' = %s\n", temp_hex_str);
#endif

        run_ecc_codec(crpt, ECCOP_MODULE | MODOP_ADD);

        /*  (27) Read X1 registers to get x1・ (mod n) */
        Reg2Hex(pCurve->Echar, crpt->ECC_X1, temp_hex_str);
        CRPT_DBGMSG("5-(27) x1' (mod n) = %s\n", temp_hex_str);

        /* 6. The signature is valid if x1・ = r, otherwise it is invalid */

        /* Compare with test pattern to check if r is correct or not */
        if(strcasecmp(temp_hex_str, R) != 0)
        {
            CRPT_DBGMSG("x1' (mod n) != R Test filed!!\n");
            CRPT_DBGMSG("Signature R [%s] is not matched with expected R [%s]!\n", temp_hex_str, R);
            ret = -2;
        }
    }  /* ret == 0 */

    return ret;
}

#if XOM_SUPPORT // To support XOM ready curve table

int32_t CurveCpy(unsigned int *p32, E_ECC_CURVE id)
{
    int32_t i;

    switch(id)
    {
        case CURVE_P_192:
            p32[  0] = 0x00000000;
            p32[  1] = 0x00000030;
            for(i = 2; i <= 8; i++)
                p32[i] = 0x46464646;

            p32[  9] = 0x45464646;
            p32[ 10] = 0x46464646;
            p32[ 11] = 0x46464646;
            p32[ 12] = 0x46464646;
            p32[ 13] = 0x43464646;
            for(i = 14; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x31323436;
            p32[ 39] = 0x39313530;
            p32[ 40] = 0x63393565;
            p32[ 41] = 0x37653038;
            p32[ 42] = 0x37616630;
            p32[ 43] = 0x62613965;
            p32[ 44] = 0x34323237;
            p32[ 45] = 0x39343033;
            p32[ 46] = 0x38626566;
            p32[ 47] = 0x63656564;
            p32[ 48] = 0x36343163;
            p32[ 49] = 0x31623962;
            for(i = 50; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x64383831;
            p32[ 75] = 0x65303861;
            p32[ 76] = 0x30333062;
            p32[ 77] = 0x36663039;
            p32[ 78] = 0x66626337;
            p32[ 79] = 0x62653032;
            p32[ 80] = 0x31613334;
            p32[ 81] = 0x30303838;
            p32[ 82] = 0x66663466;
            p32[ 83] = 0x64666130;
            p32[ 84] = 0x66663238;
            p32[ 85] = 0x32313031;
            for(i = 86; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x39313730;
            p32[111] = 0x35396232;
            p32[112] = 0x38636666;
            p32[113] = 0x38376164;
            p32[114] = 0x30313336;
            p32[115] = 0x64653131;
            p32[116] = 0x34326236;
            p32[117] = 0x35646463;
            p32[118] = 0x39663337;
            p32[119] = 0x31613737;
            p32[120] = 0x39376531;
            p32[121] = 0x31313834;
            for(i = 122; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x0000003a;
            for(i = 147; i <= 153; i++)
                p32[i] = 0x46464646;

            p32[154] = 0x45464646;
            for(i = 155; i <= 158; i++)
                p32[i] = 0x46464646;

            for(i = 159; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x0000003a;
            for(i = 192; i <= 197; i++)
                p32[i] = 0x46464646;

            p32[198] = 0x45443939;
            p32[199] = 0x36333846;
            p32[200] = 0x42363431;
            p32[201] = 0x31423943;
            p32[202] = 0x32443442;
            p32[203] = 0x31333832;
            for(i = 204; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x000000c0;
            p32[237] = 0x00000007;
            p32[238] = 0x00000002;
            p32[239] = 0x00000001;
            p32[240] = 0x00000000;
            break;
        case CURVE_P_224:
            p32[  0] = 0x00000001;
            p32[  1] = 0x00000038;
            for(i = 2; i <= 8; i++)
                p32[i] = 0x46464646;

            p32[  9] = 0x45464646;
            for(i = 10; i <= 14; i++)
                p32[i] = 0x46464646;

            p32[ 15] = 0x45464646;
            for(i = 16; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x35303462;
            p32[ 39] = 0x35386130;
            p32[ 40] = 0x34306330;
            p32[ 41] = 0x62613362;
            p32[ 42] = 0x31343566;
            p32[ 43] = 0x36353233;
            p32[ 44] = 0x34343035;
            p32[ 45] = 0x37623062;
            p32[ 46] = 0x66623764;
            p32[ 47] = 0x61623864;
            p32[ 48] = 0x62303732;
            p32[ 49] = 0x33343933;
            p32[ 50] = 0x35353332;
            p32[ 51] = 0x34626666;
            for(i = 52; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x65303762;
            p32[ 75] = 0x64626330;
            p32[ 76] = 0x34626236;
            p32[ 77] = 0x66376662;
            p32[ 78] = 0x33313233;
            p32[ 79] = 0x39623039;
            p32[ 80] = 0x33306134;
            p32[ 81] = 0x33643163;
            p32[ 82] = 0x32633635;
            p32[ 83] = 0x32323131;
            p32[ 84] = 0x32333433;
            p32[ 85] = 0x36643038;
            p32[ 86] = 0x63353131;
            p32[ 87] = 0x31326431;
            for(i = 88; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x37336462;
            p32[111] = 0x38383336;
            p32[112] = 0x37663562;
            p32[113] = 0x62663332;
            p32[114] = 0x32326334;
            p32[115] = 0x36656664;
            p32[116] = 0x33346463;
            p32[117] = 0x30613537;
            p32[118] = 0x37306135;
            p32[119] = 0x34363734;
            p32[120] = 0x35643434;
            p32[121] = 0x39393138;
            p32[122] = 0x30303538;
            p32[123] = 0x34336537;
            for(i = 124; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000046;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000046;
            for(i = 192; i <= 198; i++)
                p32[i] = 0x46464646;

            p32[199] = 0x32413631;
            p32[200] = 0x38423045;
            p32[201] = 0x45333046;
            p32[202] = 0x44443331;
            p32[203] = 0x35343932;
            p32[204] = 0x43354335;
            p32[205] = 0x44334132;
            for(i = 206; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x000000e0;
            p32[237] = 0x00000009;
            p32[238] = 0x00000008;
            p32[239] = 0x00000003;
            p32[240] = 0x00000000;
            break;
        case CURVE_P_256:
            p32[  0] = 0x00000002;
            p32[  1] = 0x00000040;
            p32[  2] = 0x46464646;
            p32[  3] = 0x46464646;
            p32[  4] = 0x30303030;
            p32[  5] = 0x31303030;
            for(i = 6; i <= 11; i++)
                p32[i] = 0x30303030;

            for(i = 12; i <= 16; i++)
                p32[i] = 0x46464646;

            p32[ 17] = 0x43464646;
            for(i = 18; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x36636135;
            p32[ 39] = 0x38643533;
            p32[ 40] = 0x61336161;
            p32[ 41] = 0x37653339;
            p32[ 42] = 0x62653362;
            p32[ 43] = 0x35356462;
            p32[ 44] = 0x38393637;
            p32[ 45] = 0x63623638;
            p32[ 46] = 0x64313536;
            p32[ 47] = 0x30623630;
            p32[ 48] = 0x33356363;
            p32[ 49] = 0x36663062;
            p32[ 50] = 0x65636233;
            p32[ 51] = 0x65336333;
            p32[ 52] = 0x32643732;
            p32[ 53] = 0x62343036;
            for(i = 54; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x37316236;
            p32[ 75] = 0x32663164;
            p32[ 76] = 0x63323165;
            p32[ 77] = 0x37343234;
            p32[ 78] = 0x63623866;
            p32[ 79] = 0x35653665;
            p32[ 80] = 0x34613336;
            p32[ 81] = 0x32663034;
            p32[ 82] = 0x33303737;
            p32[ 83] = 0x31386437;
            p32[ 84] = 0x62656432;
            p32[ 85] = 0x30613333;
            p32[ 86] = 0x31613466;
            p32[ 87] = 0x35343933;
            p32[ 88] = 0x38393864;
            p32[ 89] = 0x36393263;
            for(i = 90; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x33656634;
            p32[111] = 0x32653234;
            p32[112] = 0x61316566;
            p32[113] = 0x62396637;
            p32[114] = 0x37656538;
            p32[115] = 0x61346265;
            p32[116] = 0x66306337;
            p32[117] = 0x36316539;
            p32[118] = 0x65636232;
            p32[119] = 0x37353333;
            p32[120] = 0x31336236;
            p32[121] = 0x65636535;
            p32[122] = 0x36626263;
            p32[123] = 0x38363034;
            p32[124] = 0x66623733;
            p32[125] = 0x35663135;
            for(i = 126; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x0000004e;
            p32[147] = 0x46464646;
            p32[148] = 0x46464646;
            p32[149] = 0x30303030;
            p32[150] = 0x31303030;
            for(i = 151; i <= 156; i++)
                p32[i] = 0x30303030;

            for(i = 157; i <= 162; i++)
                p32[i] = 0x46464646;

            for(i = 163; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x0000004e;
            p32[192] = 0x46464646;
            p32[193] = 0x46464646;
            p32[194] = 0x30303030;
            p32[195] = 0x30303030;
            for(i = 196; i <= 199; i++)
                p32[i] = 0x46464646;

            p32[200] = 0x36454342;
            p32[201] = 0x44414146;
            p32[202] = 0x37313741;
            p32[203] = 0x34384539;
            p32[204] = 0x39423346;
            p32[205] = 0x32434143;
            p32[206] = 0x33364346;
            p32[207] = 0x31353532;
            for(i = 208; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x00000100;
            p32[237] = 0x0000000a;
            p32[238] = 0x00000005;
            p32[239] = 0x00000002;
            p32[240] = 0x00000000;
            break;
        case CURVE_P_384:
            p32[  0] = 0x00000003;
            p32[  1] = 0x00000060;
            for(i = 2; i <= 16; i++)
                p32[i] = 0x46464646;

            p32[ 17] = 0x45464646;
            p32[ 18] = 0x46464646;
            p32[ 19] = 0x46464646;
            for(i = 20; i <= 23; i++)
                p32[i] = 0x30303030;

            p32[ 24] = 0x46464646;
            p32[ 25] = 0x43464646;
            for(i = 26; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x31333362;
            p32[ 39] = 0x37616632;
            p32[ 40] = 0x65333265;
            p32[ 41] = 0x34653765;
            p32[ 42] = 0x65383839;
            p32[ 43] = 0x62363530;
            p32[ 44] = 0x38663365;
            p32[ 45] = 0x39316432;
            p32[ 46] = 0x64313831;
            p32[ 47] = 0x65366339;
            p32[ 48] = 0x31386566;
            p32[ 49] = 0x32313134;
            p32[ 50] = 0x34313330;
            p32[ 51] = 0x66383830;
            p32[ 52] = 0x33313035;
            p32[ 53] = 0x61353738;
            p32[ 54] = 0x36353663;
            p32[ 55] = 0x64383933;
            p32[ 56] = 0x65326138;
            p32[ 57] = 0x64393164;
            p32[ 58] = 0x35386132;
            p32[ 59] = 0x64653863;
            p32[ 60] = 0x63653364;
            p32[ 61] = 0x66656132;
            for(i = 62; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x37386161;
            p32[ 75] = 0x32326163;
            p32[ 76] = 0x62386562;
            p32[ 77] = 0x37333530;
            p32[ 78] = 0x31626538;
            p32[ 79] = 0x65313763;
            p32[ 80] = 0x30323366;
            p32[ 81] = 0x34376461;
            p32[ 82] = 0x64316536;
            p32[ 83] = 0x32366233;
            p32[ 84] = 0x37616238;
            p32[ 85] = 0x38396239;
            p32[ 86] = 0x37663935;
            p32[ 87] = 0x30653134;
            p32[ 88] = 0x34353238;
            p32[ 89] = 0x38336132;
            p32[ 90] = 0x32303535;
            p32[ 91] = 0x64353266;
            p32[ 92] = 0x35356662;
            p32[ 93] = 0x63363932;
            p32[ 94] = 0x34356133;
            p32[ 95] = 0x38336535;
            p32[ 96] = 0x36373237;
            p32[ 97] = 0x37626130;
            for(i = 98; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x37313633;
            p32[111] = 0x61346564;
            p32[112] = 0x36323639;
            p32[113] = 0x66366332;
            p32[114] = 0x65396435;
            p32[115] = 0x66623839;
            p32[116] = 0x32393239;
            p32[117] = 0x39326364;
            p32[118] = 0x34663866;
            p32[119] = 0x64626431;
            p32[120] = 0x61393832;
            p32[121] = 0x63373431;
            p32[122] = 0x61643965;
            p32[123] = 0x33313133;
            p32[124] = 0x30663562;
            p32[125] = 0x30633862;
            p32[126] = 0x30366130;
            p32[127] = 0x65633162;
            p32[128] = 0x65376431;
            p32[129] = 0x64393138;
            p32[130] = 0x33346137;
            p32[131] = 0x63376431;
            p32[132] = 0x61653039;
            p32[133] = 0x66356530;
            for(i = 134; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000074;
            for(i = 147; i <= 161; i++)
                p32[i] = 0x46464646;

            p32[162] = 0x45464646;
            p32[163] = 0x46464646;
            p32[164] = 0x46464646;
            for(i = 165; i <= 168; i++)
                p32[i] = 0x30303030;

            p32[169] = 0x46464646;
            p32[170] = 0x46464646;
            for(i = 171; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000074;
            for(i = 192; i <= 203; i++)
                p32[i] = 0x46464646;

            p32[204] = 0x33363743;
            p32[205] = 0x31384434;
            p32[206] = 0x37333446;
            p32[207] = 0x46444432;
            p32[208] = 0x41313835;
            p32[209] = 0x32424430;
            p32[210] = 0x30423834;
            p32[211] = 0x41373741;
            p32[212] = 0x43454345;
            p32[213] = 0x41363931;
            p32[214] = 0x35434343;
            p32[215] = 0x33373932;
            for(i = 216; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x00000180;
            p32[237] = 0x0000000c;
            p32[238] = 0x00000003;
            p32[239] = 0x00000002;
            p32[240] = 0x00000000;
            break;
        case CURVE_P_521:
            p32[  0] = 0x00000004;
            p32[  1] = 0x00000083;
            p32[  2] = 0x46464631;
            for(i = 3; i <= 33; i++)
                p32[i] = 0x46464646;

            p32[ 34] = 0x00434646;
            p32[ 35] = 0x00000000;
            p32[ 36] = 0x00000000;
            p32[ 37] = 0x00000000;
            p32[ 38] = 0x39313530;
            p32[ 39] = 0x62653335;
            p32[ 40] = 0x38313639;
            p32[ 41] = 0x39633165;
            p32[ 42] = 0x39663161;
            p32[ 43] = 0x32613932;
            p32[ 44] = 0x62306131;
            p32[ 45] = 0x34353836;
            p32[ 46] = 0x61656530;
            p32[ 47] = 0x37616432;
            p32[ 48] = 0x39623532;
            p32[ 49] = 0x31336239;
            p32[ 50] = 0x62336635;
            p32[ 51] = 0x38346238;
            p32[ 52] = 0x38313939;
            p32[ 53] = 0x30316665;
            p32[ 54] = 0x35316539;
            p32[ 55] = 0x33393136;
            p32[ 56] = 0x65313539;
            p32[ 57] = 0x39653763;
            p32[ 58] = 0x31623733;
            p32[ 59] = 0x63323536;
            p32[ 60] = 0x33646230;
            p32[ 61] = 0x62316262;
            p32[ 62] = 0x33373066;
            p32[ 63] = 0x64333735;
            p32[ 64] = 0x33383866;
            p32[ 65] = 0x33633264;
            p32[ 66] = 0x65316634;
            p32[ 67] = 0x31353466;
            p32[ 68] = 0x36346466;
            p32[ 69] = 0x33303562;
            p32[ 70] = 0x00303066;
            p32[ 71] = 0x00000000;
            p32[ 72] = 0x00000000;
            p32[ 73] = 0x00000000;
            p32[ 74] = 0x38366330;
            p32[ 75] = 0x30653835;
            p32[ 76] = 0x30376236;
            p32[ 77] = 0x65343034;
            p32[ 78] = 0x39646339;
            p32[ 79] = 0x63653365;
            p32[ 80] = 0x32363662;
            p32[ 81] = 0x62353933;
            p32[ 82] = 0x39323434;
            p32[ 83] = 0x38343663;
            p32[ 84] = 0x30393331;
            p32[ 85] = 0x62663335;
            p32[ 86] = 0x66313235;
            p32[ 87] = 0x61383238;
            p32[ 88] = 0x36303666;
            p32[ 89] = 0x33643462;
            p32[ 90] = 0x61616264;
            p32[ 91] = 0x35623431;
            p32[ 92] = 0x65373765;
            p32[ 93] = 0x35376566;
            p32[ 94] = 0x66383239;
            p32[ 95] = 0x63643165;
            p32[ 96] = 0x61373231;
            p32[ 97] = 0x61666632;
            p32[ 98] = 0x33656438;
            p32[ 99] = 0x62383433;
            p32[100] = 0x38316333;
            p32[101] = 0x34613635;
            p32[102] = 0x66623932;
            p32[103] = 0x37653739;
            p32[104] = 0x63313365;
            p32[105] = 0x62356532;
            p32[106] = 0x00363664;
            p32[107] = 0x00000000;
            p32[108] = 0x00000000;
            p32[109] = 0x00000000;
            p32[110] = 0x33383131;
            p32[111] = 0x36393239;
            p32[112] = 0x39383761;
            p32[113] = 0x63623361;
            p32[114] = 0x35343030;
            p32[115] = 0x35613863;
            p32[116] = 0x32346266;
            p32[117] = 0x31643763;
            p32[118] = 0x39396462;
            p32[119] = 0x34356638;
            p32[120] = 0x35393434;
            p32[121] = 0x34623937;
            p32[122] = 0x31383634;
            p32[123] = 0x62666137;
            p32[124] = 0x32373164;
            p32[125] = 0x36653337;
            p32[126] = 0x39633236;
            p32[127] = 0x37656537;
            p32[128] = 0x35393932;
            p32[129] = 0x32346665;
            p32[130] = 0x63303436;
            p32[131] = 0x62303535;
            p32[132] = 0x33313039;
            p32[133] = 0x30646166;
            p32[134] = 0x33313637;
            p32[135] = 0x37633335;
            p32[136] = 0x61363830;
            p32[137] = 0x63323732;
            p32[138] = 0x38303432;
            p32[139] = 0x39656238;
            p32[140] = 0x39363734;
            p32[141] = 0x36316466;
            p32[142] = 0x00303536;
            p32[143] = 0x00000000;
            p32[144] = 0x00000000;
            p32[145] = 0x00000000;
            p32[146] = 0x0000009d;
            p32[147] = 0x46464631;
            for(i = 148; i <= 178; i++)
                p32[i] = 0x46464646;

            p32[179] = 0x00464646;
            for(i = 180; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x0000009d;
            p32[192] = 0x46464631;
            for(i = 193; i <= 207; i++)
                p32[i] = 0x46464646;

            p32[208] = 0x35414646;
            p32[209] = 0x38363831;
            p32[210] = 0x42333837;
            p32[211] = 0x39463246;
            p32[212] = 0x37423636;
            p32[213] = 0x30434346;
            p32[214] = 0x46383431;
            p32[215] = 0x41393037;
            p32[216] = 0x33304435;
            p32[217] = 0x43354242;
            p32[218] = 0x38384239;
            p32[219] = 0x34433939;
            p32[220] = 0x42454137;
            p32[221] = 0x42463642;
            p32[222] = 0x39453137;
            p32[223] = 0x36383331;
            p32[224] = 0x00393034;
            for(i = 225; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x00000209;
            p32[237] = 0x00000020;
            p32[238] = 0x00000020;
            p32[239] = 0x00000020;
            p32[240] = 0x00000000;
            break;
        case CURVE_B_163:
            p32[  0] = 0x0000000a;
            p32[  1] = 0x00000029;
            for(i = 2; i <= 11; i++)
                p32[i] = 0x30303030;

            p32[ 12] = 0x00000031;
            for(i = 13; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x36613032;
            p32[ 39] = 0x30393130;
            p32[ 40] = 0x63386237;
            p32[ 41] = 0x63333539;
            p32[ 42] = 0x38343161;
            p32[ 43] = 0x31626531;
            p32[ 44] = 0x32313530;
            p32[ 45] = 0x37383766;
            p32[ 46] = 0x33613434;
            p32[ 47] = 0x66353032;
            p32[ 48] = 0x00000064;
            for(i = 49; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x65306633;
            p32[ 75] = 0x36316162;
            p32[ 76] = 0x61363832;
            p32[ 77] = 0x37356432;
            p32[ 78] = 0x39306165;
            p32[ 79] = 0x36313139;
            p32[ 80] = 0x39346438;
            p32[ 81] = 0x33363439;
            p32[ 82] = 0x33386537;
            p32[ 83] = 0x33653334;
            p32[ 84] = 0x00000036;
            for(i = 85; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x31356430;
            p32[111] = 0x36636266;
            p32[112] = 0x61313763;
            p32[113] = 0x34393030;
            p32[114] = 0x63326166;
            p32[115] = 0x34356464;
            p32[116] = 0x31316235;
            p32[117] = 0x30633563;
            p32[118] = 0x37393763;
            p32[119] = 0x66343233;
            p32[120] = 0x00000031;
            for(i = 121; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000031;
            p32[192] = 0x30303034;
            for(i = 193; i <= 196; i++)
                p32[i] = 0x30303030;

            p32[197] = 0x46323932;
            p32[198] = 0x45373745;
            p32[199] = 0x31433037;
            p32[200] = 0x32344132;
            p32[201] = 0x33433433;
            p32[202] = 0x00000033;
            for(i = 203; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x000000a3;
            p32[237] = 0x00000007;
            p32[238] = 0x00000006;
            p32[239] = 0x00000003;
            p32[240] = 0x00000001;
            break;
        case CURVE_B_233:
            p32[  0] = 0x0000000b;
            p32[  1] = 0x0000003b;
            for(i = 2; i <= 15; i++)
                p32[i] = 0x30303030;

            p32[ 16] = 0x00313030;
            for(i = 17; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x36363630;
            p32[ 39] = 0x64653734;
            p32[ 40] = 0x33633665;
            p32[ 41] = 0x37633233;
            p32[ 42] = 0x30633866;
            p32[ 43] = 0x62333239;
            p32[ 44] = 0x32383562;
            p32[ 45] = 0x33623331;
            p32[ 46] = 0x32623333;
            p32[ 47] = 0x63396530;
            p32[ 48] = 0x38323465;
            p32[ 49] = 0x31656631;
            p32[ 50] = 0x37663531;
            p32[ 51] = 0x39663864;
            p32[ 52] = 0x00646130;
            for(i = 53; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x63616630;
            p32[ 75] = 0x63666439;
            p32[ 76] = 0x38636162;
            p32[ 77] = 0x62333133;
            p32[ 78] = 0x33313262;
            p32[ 79] = 0x62316639;
            p32[ 80] = 0x35353762;
            p32[ 81] = 0x36666566;
            p32[ 82] = 0x33636235;
            p32[ 83] = 0x38663139;
            p32[ 84] = 0x66363362;
            p32[ 85] = 0x65386638;
            p32[ 86] = 0x37333762;
            p32[ 87] = 0x35646631;
            p32[ 88] = 0x00623835;
            for(i = 89; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x36303031;
            p32[111] = 0x61383061;
            p32[112] = 0x30393134;
            p32[113] = 0x30353333;
            p32[114] = 0x65383736;
            p32[115] = 0x32353835;
            p32[116] = 0x62656238;
            p32[117] = 0x30613866;
            p32[118] = 0x66666562;
            p32[119] = 0x61373638;
            p32[120] = 0x33616337;
            p32[121] = 0x36313736;
            p32[122] = 0x30653766;
            p32[123] = 0x31386631;
            p32[124] = 0x00323530;
            for(i = 125; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000046;
            p32[192] = 0x30303031;
            for(i = 193; i <= 198; i++)
                p32[i] = 0x30303030;

            p32[199] = 0x45333130;
            p32[200] = 0x45343739;
            p32[201] = 0x38463237;
            p32[202] = 0x32393641;
            p32[203] = 0x31333032;
            p32[204] = 0x30363244;
            p32[205] = 0x45464333;
            p32[206] = 0x00374430;
            for(i = 207; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x000000e9;
            p32[237] = 0x0000004a;
            p32[238] = 0x0000004a;
            p32[239] = 0x0000004a;
            p32[240] = 0x00000001;
            break;
        case CURVE_B_283:
            p32[  0] = 0x0000000c;
            p32[  1] = 0x00000047;
            for(i = 2; i <= 18; i++)
                p32[i] = 0x30303030;

            p32[ 19] = 0x00313030;
            for(i = 20; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x36623732;
            p32[ 39] = 0x63613038;
            p32[ 40] = 0x35386238;
            p32[ 41] = 0x61643639;
            p32[ 42] = 0x61346135;
            p32[ 43] = 0x31613866;
            p32[ 44] = 0x33306139;
            p32[ 45] = 0x63663330;
            p32[ 46] = 0x66373961;
            p32[ 47] = 0x34363764;
            p32[ 48] = 0x39303335;
            p32[ 49] = 0x61326166;
            p32[ 50] = 0x34313835;
            p32[ 51] = 0x66613538;
            p32[ 52] = 0x33363236;
            p32[ 53] = 0x33313365;
            p32[ 54] = 0x61393762;
            p32[ 55] = 0x00356632;
            for(i = 56; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x33396635;
            p32[ 75] = 0x38353239;
            p32[ 76] = 0x64376264;
            p32[ 77] = 0x65303964;
            p32[ 78] = 0x34333931;
            p32[ 79] = 0x37633866;
            p32[ 80] = 0x64306230;
            p32[ 81] = 0x32636566;
            p32[ 82] = 0x32646565;
            p32[ 83] = 0x35386235;
            p32[ 84] = 0x61653735;
            p32[ 85] = 0x38633963;
            p32[ 86] = 0x65326530;
            p32[ 87] = 0x66383931;
            p32[ 88] = 0x62646338;
            p32[ 89] = 0x38646365;
            p32[ 90] = 0x32316236;
            p32[ 91] = 0x00333530;
            for(i = 92; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x36373633;
            p32[111] = 0x66343538;
            p32[112] = 0x31343265;
            p32[113] = 0x62633134;
            p32[114] = 0x65663839;
            p32[115] = 0x62346436;
            p32[116] = 0x30643032;
            p32[117] = 0x35346232;
            p32[118] = 0x66663631;
            p32[119] = 0x33323037;
            p32[120] = 0x64653035;
            p32[121] = 0x38306264;
            p32[122] = 0x37373632;
            p32[123] = 0x31386339;
            p32[124] = 0x64306633;
            p32[125] = 0x62353466;
            p32[126] = 0x31313865;
            p32[127] = 0x00346632;
            for(i = 128; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000055;
            p32[192] = 0x46464633;
            for(i = 193; i <= 199; i++)
                p32[i] = 0x46464646;

            p32[200] = 0x45464646;
            p32[201] = 0x33303946;
            p32[202] = 0x36363939;
            p32[203] = 0x39434630;
            p32[204] = 0x39413833;
            p32[205] = 0x35363130;
            p32[206] = 0x32343042;
            p32[207] = 0x45433741;
            p32[208] = 0x42444146;
            p32[209] = 0x00373033;
            for(i = 210; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x0000011b;
            p32[237] = 0x0000000c;
            p32[238] = 0x00000007;
            p32[239] = 0x00000005;
            p32[240] = 0x00000001;
            break;
        case CURVE_B_409:
            p32[  0] = 0x0000000d;
            p32[  1] = 0x00000067;
            for(i = 2; i <= 26; i++)
                p32[i] = 0x30303030;

            p32[ 27] = 0x00313030;
            for(i = 28; i <= 37; i++)
                p32[i] = 0x00000000;

            p32[ 38] = 0x61313230;
            p32[ 39] = 0x63326335;
            p32[ 40] = 0x39656538;
            p32[ 41] = 0x35626566;
            p32[ 42] = 0x39623463;
            p32[ 43] = 0x33353761;
            p32[ 44] = 0x34623762;
            p32[ 45] = 0x37623637;
            p32[ 46] = 0x34366466;
            p32[ 47] = 0x66653232;
            p32[ 48] = 0x64336631;
            p32[ 49] = 0x34373664;
            p32[ 50] = 0x66313637;
            p32[ 51] = 0x64393961;
            p32[ 52] = 0x32636136;
            p32[ 53] = 0x61386337;
            p32[ 54] = 0x39316139;
            p32[ 55] = 0x37326237;
            p32[ 56] = 0x32323832;
            p32[ 57] = 0x64633666;
            p32[ 58] = 0x35613735;
            p32[ 59] = 0x34616135;
            p32[ 60] = 0x61303566;
            p32[ 61] = 0x37313365;
            p32[ 62] = 0x35333162;
            p32[ 63] = 0x00663534;
            for(i = 64; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x34643531;
            p32[ 75] = 0x64303638;
            p32[ 76] = 0x64383830;
            p32[ 77] = 0x34336264;
            p32[ 78] = 0x30623639;
            p32[ 79] = 0x36303663;
            p32[ 80] = 0x36353734;
            p32[ 81] = 0x34303632;
            p32[ 82] = 0x64633134;
            p32[ 83] = 0x66613465;
            p32[ 84] = 0x31373731;
            p32[ 85] = 0x62643464;
            p32[ 86] = 0x66663130;
            p32[ 87] = 0x33623565;
            p32[ 88] = 0x39356534;
            p32[ 89] = 0x64333037;
            p32[ 90] = 0x35353263;
            p32[ 91] = 0x38363861;
            p32[ 92] = 0x38313161;
            p32[ 93] = 0x35313530;
            p32[ 94] = 0x61333036;
            p32[ 95] = 0x36626165;
            p32[ 96] = 0x34393730;
            p32[ 97] = 0x62343565;
            p32[ 98] = 0x39393762;
            p32[ 99] = 0x00376136;
            for(i = 100; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x62313630;
            p32[111] = 0x61666331;
            p32[112] = 0x65623662;
            p32[113] = 0x32336635;
            p32[114] = 0x61666262;
            p32[115] = 0x32333837;
            p32[116] = 0x31646534;
            p32[117] = 0x37613630;
            p32[118] = 0x62363336;
            p32[119] = 0x61356339;
            p32[120] = 0x31646237;
            p32[121] = 0x30643839;
            p32[122] = 0x61383531;
            p32[123] = 0x35663461;
            p32[124] = 0x64383834;
            p32[125] = 0x33663830;
            p32[126] = 0x34313538;
            p32[127] = 0x64663166;
            p32[128] = 0x34623466;
            p32[129] = 0x64303466;
            p32[130] = 0x31383132;
            p32[131] = 0x38363362;
            p32[132] = 0x36336331;
            p32[133] = 0x30616234;
            p32[134] = 0x63333732;
            p32[135] = 0x00363037;
            for(i = 136; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x0000007b;
            p32[192] = 0x30303031;
            for(i = 193; i <= 204; i++)
                p32[i] = 0x30303030;

            p32[205] = 0x41324531;
            p32[206] = 0x41364441;
            p32[207] = 0x46323136;
            p32[208] = 0x30333333;
            p32[209] = 0x35454237;
            p32[210] = 0x37344146;
            p32[211] = 0x39433343;
            p32[212] = 0x32353045;
            p32[213] = 0x38333846;
            p32[214] = 0x43343631;
            p32[215] = 0x44373344;
            p32[216] = 0x31324139;
            p32[217] = 0x00333731;
            for(i = 218; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x00000199;
            p32[237] = 0x00000057;
            p32[238] = 0x00000057;
            p32[239] = 0x00000057;
            p32[240] = 0x00000001;
            break;
        case CURVE_B_571:
            p32[  0] = 0x0000000e;
            p32[  1] = 0x0000008f;
            for(i = 2; i <= 36; i++)
                p32[i] = 0x30303030;

            p32[ 37] = 0x00313030;
            p32[ 38] = 0x30346632;
            p32[ 39] = 0x32653765;
            p32[ 40] = 0x66313232;
            p32[ 41] = 0x64353932;
            p32[ 42] = 0x37393265;
            p32[ 43] = 0x62373131;
            p32[ 44] = 0x64336637;
            p32[ 45] = 0x35663236;
            p32[ 46] = 0x39613663;
            p32[ 47] = 0x63666637;
            p32[ 48] = 0x65633862;
            p32[ 49] = 0x63316666;
            p32[ 50] = 0x61623664;
            p32[ 51] = 0x34656338;
            p32[ 52] = 0x31613961;
            p32[ 53] = 0x38646138;
            p32[ 54] = 0x61666634;
            p32[ 55] = 0x38646262;
            p32[ 56] = 0x35616665;
            p32[ 57] = 0x32333339;
            p32[ 58] = 0x61376562;
            p32[ 59] = 0x35373664;
            p32[ 60] = 0x36366136;
            p32[ 61] = 0x34393265;
            p32[ 62] = 0x31646661;
            p32[ 63] = 0x37613538;
            p32[ 64] = 0x31666638;
            p32[ 65] = 0x35616132;
            p32[ 66] = 0x34653032;
            p32[ 67] = 0x33376564;
            p32[ 68] = 0x63616239;
            p32[ 69] = 0x37633061;
            p32[ 70] = 0x66656666;
            p32[ 71] = 0x32663766;
            p32[ 72] = 0x37353539;
            p32[ 73] = 0x00613732;
            p32[ 74] = 0x30333033;
            p32[ 75] = 0x33643130;
            p32[ 76] = 0x35386234;
            p32[ 77] = 0x36393236;
            p32[ 78] = 0x63363163;
            p32[ 79] = 0x30346430;
            p32[ 80] = 0x64633364;
            p32[ 81] = 0x30353737;
            p32[ 82] = 0x64333961;
            p32[ 83] = 0x39326431;
            p32[ 84] = 0x61663535;
            p32[ 85] = 0x61613038;
            p32[ 86] = 0x30346635;
            p32[ 87] = 0x64386366;
            p32[ 88] = 0x32623762;
            p32[ 89] = 0x62646261;
            p32[ 90] = 0x33356564;
            p32[ 91] = 0x66303539;
            p32[ 92] = 0x64306334;
            p32[ 93] = 0x63333932;
            p32[ 94] = 0x31376464;
            p32[ 95] = 0x35336131;
            p32[ 96] = 0x66373662;
            p32[ 97] = 0x39343162;
            p32[ 98] = 0x36656139;
            p32[ 99] = 0x38333030;
            p32[100] = 0x66343136;
            p32[101] = 0x34393331;
            p32[102] = 0x61666261;
            p32[103] = 0x63346233;
            p32[104] = 0x64303538;
            p32[105] = 0x65373239;
            p32[106] = 0x37376531;
            p32[107] = 0x38633936;
            p32[108] = 0x32636565;
            p32[109] = 0x00393164;
            p32[110] = 0x66623733;
            p32[111] = 0x34333732;
            p32[112] = 0x36616432;
            p32[113] = 0x36623933;
            p32[114] = 0x66636364;
            p32[115] = 0x62656666;
            p32[116] = 0x36643337;
            p32[117] = 0x38376439;
            p32[118] = 0x32633663;
            p32[119] = 0x30366137;
            p32[120] = 0x62633930;
            p32[121] = 0x31616362;
            p32[122] = 0x66303839;
            p32[123] = 0x33333538;
            p32[124] = 0x65313239;
            p32[125] = 0x38366138;
            p32[126] = 0x33323434;
            p32[127] = 0x62333465;
            p32[128] = 0x38306261;
            p32[129] = 0x36373561;
            p32[130] = 0x61313932;
            p32[131] = 0x34663866;
            p32[132] = 0x62623136;
            p32[133] = 0x62386132;
            p32[134] = 0x31333533;
            p32[135] = 0x30663264;
            p32[136] = 0x63353834;
            p32[137] = 0x31623931;
            p32[138] = 0x66326536;
            p32[139] = 0x36313531;
            p32[140] = 0x64333265;
            p32[141] = 0x31633364;
            p32[142] = 0x32383461;
            p32[143] = 0x31666137;
            p32[144] = 0x63613862;
            p32[145] = 0x00623531;
            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x000000ac;
            p32[192] = 0x46464633;
            for(i = 193; i <= 208; i++)
                p32[i] = 0x46464646;

            p32[209] = 0x45464646;
            p32[210] = 0x43313636;
            p32[211] = 0x46383145;
            p32[212] = 0x39353546;
            p32[213] = 0x30333738;
            p32[214] = 0x39353038;
            p32[215] = 0x36383142;
            p32[216] = 0x38333238;
            p32[217] = 0x43453135;
            p32[218] = 0x39444437;
            p32[219] = 0x31314143;
            p32[220] = 0x45443136;
            p32[221] = 0x35443339;
            p32[222] = 0x44343731;
            p32[223] = 0x38453636;
            p32[224] = 0x45323833;
            p32[225] = 0x32424239;
            p32[226] = 0x34384546;
            p32[227] = 0x00373445;
            for(i = 228; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x0000023b;
            p32[237] = 0x0000000a;
            p32[238] = 0x00000005;
            p32[239] = 0x00000002;
            p32[240] = 0x00000001;
            break;
        case CURVE_K_163:
            p32[  0] = 0x00000005;
            p32[  1] = 0x00000029;
            for(i = 2; i <= 11; i++)
                p32[i] = 0x30303030;

            p32[ 12] = 0x00000031;
            for(i = 13; i <= 37; i++)
                p32[i] = 0x00000000;

            for(i = 38; i <= 47; i++)
                p32[i] = 0x30303030;

            p32[ 48] = 0x00000031;
            for(i = 49; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x31656632;
            p32[ 75] = 0x35306333;
            p32[ 76] = 0x62623733;
            p32[ 77] = 0x61313163;
            p32[ 78] = 0x30616163;
            p32[ 79] = 0x39376437;
            p32[ 80] = 0x34656433;
            p32[ 81] = 0x35643665;
            p32[ 82] = 0x39633565;
            p32[ 83] = 0x65656534;
            p32[ 84] = 0x00000038;
            for(i = 85; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x30393832;
            p32[111] = 0x62663037;
            p32[112] = 0x33643530;
            p32[113] = 0x35666638;
            p32[114] = 0x31323338;
            p32[115] = 0x38653266;
            p32[116] = 0x33353030;
            p32[117] = 0x33356436;
            p32[118] = 0x64636338;
            p32[119] = 0x64336161;
            p32[120] = 0x00000039;
            for(i = 121; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000031;
            p32[192] = 0x30303034;
            for(i = 193; i <= 196; i++)
                p32[i] = 0x30303030;

            p32[197] = 0x30313032;
            p32[198] = 0x45324138;
            p32[199] = 0x30434330;
            p32[200] = 0x46393944;
            p32[201] = 0x45354138;
            p32[202] = 0x00000046;
            for(i = 203; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x000000a3;
            p32[237] = 0x00000007;
            p32[238] = 0x00000006;
            p32[239] = 0x00000003;
            p32[240] = 0x00000001;
            break;
        case CURVE_K_233:
            p32[  0] = 0x00000006;
            p32[  1] = 0x0000003b;
            for(i = 2; i <= 15; i++)
                p32[i] = 0x30303030;

            p32[ 16] = 0x00303030;
            for(i = 17; i <= 37; i++)
                p32[i] = 0x00000000;

            for(i = 38; i <= 51; i++)
                p32[i] = 0x30303030;

            p32[ 52] = 0x00313030;
            for(i = 53; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x33323731;
            p32[ 75] = 0x38616232;
            p32[ 76] = 0x37613335;
            p32[ 77] = 0x31333765;
            p32[ 78] = 0x32316661;
            p32[ 79] = 0x32326639;
            p32[ 80] = 0x31346666;
            p32[ 81] = 0x36353934;
            p32[ 82] = 0x31346133;
            p32[ 83] = 0x36326339;
            p32[ 84] = 0x30356662;
            p32[ 85] = 0x39633461;
            p32[ 86] = 0x65653664;
            p32[ 87] = 0x36646166;
            p32[ 88] = 0x00363231;
            for(i = 89; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x35626431;
            p32[111] = 0x65643733;
            p32[112] = 0x31386563;
            p32[113] = 0x66376239;
            p32[114] = 0x35663037;
            p32[115] = 0x36613535;
            p32[116] = 0x32346337;
            p32[117] = 0x63386137;
            p32[118] = 0x66623964;
            p32[119] = 0x65613831;
            p32[120] = 0x35623962;
            p32[121] = 0x63306536;
            p32[122] = 0x35303131;
            p32[123] = 0x65616636;
            p32[124] = 0x00336136;
            for(i = 125; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000046;
            p32[192] = 0x30303038;
            for(i = 193; i <= 198; i++)
                p32[i] = 0x30303030;

            p32[199] = 0x44393630;
            p32[200] = 0x39424235;
            p32[201] = 0x43423531;
            p32[202] = 0x45363444;
            p32[203] = 0x41314246;
            p32[204] = 0x31463544;
            p32[205] = 0x42413337;
            p32[206] = 0x00004644;
            for(i = 207; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x000000e9;
            p32[237] = 0x0000004a;
            p32[238] = 0x0000004a;
            p32[239] = 0x0000004a;
            p32[240] = 0x00000001;
            break;
        case CURVE_K_283:
            p32[  0] = 0x00000007;
            p32[  1] = 0x00000047;
            for(i = 2; i <= 18; i++)
                p32[i] = 0x30303030;

            p32[ 19] = 0x00303030;
            for(i = 20; i <= 37; i++)
                p32[i] = 0x00000000;

            for(i = 38; i <= 54; i++)
                p32[i] = 0x30303030;

            p32[ 55] = 0x00313030;
            for(i = 56; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x32333035;
            p32[ 75] = 0x37663331;
            p32[ 76] = 0x34616338;
            p32[ 77] = 0x33383834;
            p32[ 78] = 0x33613166;
            p32[ 79] = 0x36313862;
            p32[ 80] = 0x38316632;
            p32[ 81] = 0x35356538;
            p32[ 82] = 0x32646333;
            p32[ 83] = 0x32663536;
            p32[ 84] = 0x35316333;
            p32[ 85] = 0x31613736;
            p32[ 86] = 0x36373836;
            p32[ 87] = 0x62333139;
            p32[ 88] = 0x61326330;
            p32[ 89] = 0x35343263;
            p32[ 90] = 0x32393438;
            p32[ 91] = 0x00363338;
            for(i = 92; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x64636331;
            p32[111] = 0x30383361;
            p32[112] = 0x39633166;
            p32[113] = 0x38313365;
            p32[114] = 0x66303964;
            p32[115] = 0x30643539;
            p32[116] = 0x34356537;
            p32[117] = 0x65663632;
            p32[118] = 0x34653738;
            p32[119] = 0x65306335;
            p32[120] = 0x34383138;
            p32[121] = 0x65383936;
            p32[122] = 0x36393534;
            p32[123] = 0x34363332;
            p32[124] = 0x31343365;
            p32[125] = 0x37313631;
            p32[126] = 0x32646437;
            p32[127] = 0x00393532;
            for(i = 128; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x00000055;
            p32[192] = 0x46464631;
            for(i = 193; i <= 199; i++)
                p32[i] = 0x46464646;

            p32[200] = 0x45464646;
            p32[201] = 0x32454139;
            p32[202] = 0x37304445;
            p32[203] = 0x32373735;
            p32[204] = 0x46443536;
            p32[205] = 0x39463746;
            p32[206] = 0x31353434;
            p32[207] = 0x31363045;
            p32[208] = 0x33363145;
            p32[209] = 0x00313643;
            for(i = 210; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x0000011b;
            p32[237] = 0x0000000c;
            p32[238] = 0x00000007;
            p32[239] = 0x00000005;
            p32[240] = 0x00000001;
            break;
        case CURVE_K_409:
            p32[  0] = 0x00000008;
            p32[  1] = 0x00000067;
            for(i = 2; i <= 26; i++)
                p32[i] = 0x30303030;

            p32[ 27] = 0x00303030;
            for(i = 28; i <= 37; i++)
                p32[i] = 0x00000000;

            for(i = 38; i <= 62; i++)
                p32[i] = 0x30303030;

            p32[ 63] = 0x00313030;
            for(i = 64; i <= 73; i++)
                p32[i] = 0x00000000;

            p32[ 74] = 0x66303630;
            p32[ 75] = 0x36663530;
            p32[ 76] = 0x34663835;
            p32[ 77] = 0x61316339;
            p32[ 78] = 0x62613364;
            p32[ 79] = 0x30393831;
            p32[ 80] = 0x38313766;
            p32[ 81] = 0x30313234;
            p32[ 82] = 0x30646665;
            p32[ 83] = 0x65373839;
            p32[ 84] = 0x63373033;
            p32[ 85] = 0x32633438;
            p32[ 86] = 0x63636137;
            p32[ 87] = 0x66386266;
            p32[ 88] = 0x37366639;
            p32[ 89] = 0x63326363;
            p32[ 90] = 0x31303634;
            p32[ 91] = 0x62653938;
            p32[ 92] = 0x61616135;
            p32[ 93] = 0x65323661;
            p32[ 94] = 0x32323265;
            p32[ 95] = 0x62316265;
            p32[ 96] = 0x34353533;
            p32[ 97] = 0x65666330;
            p32[ 98] = 0x33323039;
            p32[ 99] = 0x00363437;
            for(i = 100; i <= 109; i++)
                p32[i] = 0x00000000;

            p32[110] = 0x36336531;
            p32[111] = 0x30353039;
            p32[112] = 0x34633762;
            p32[113] = 0x61323465;
            p32[114] = 0x31616263;
            p32[115] = 0x62636164;
            p32[116] = 0x32343066;
            p32[117] = 0x33633939;
            p32[118] = 0x37303634;
            p32[119] = 0x39663238;
            p32[120] = 0x61653831;
            p32[121] = 0x65373234;
            p32[122] = 0x35323336;
            p32[123] = 0x65353631;
            p32[124] = 0x31616539;
            p32[125] = 0x64336530;
            p32[126] = 0x36663561;
            p32[127] = 0x65323463;
            p32[128] = 0x35356339;
            p32[129] = 0x61353132;
            p32[130] = 0x61633961;
            p32[131] = 0x35613732;
            p32[132] = 0x65333638;
            p32[133] = 0x64383463;
            p32[134] = 0x32306538;
            p32[135] = 0x00623638;
            for(i = 136; i <= 145; i++)
                p32[i] = 0x00000000;

            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x0000007b;
            p32[192] = 0x46464637;
            for(i = 193; i <= 203; i++)
                p32[i] = 0x46464646;

            p32[204] = 0x45464646;
            p32[205] = 0x33384635;
            p32[206] = 0x34443242;
            p32[207] = 0x30324145;
            p32[208] = 0x45303034;
            p32[209] = 0x35353443;
            p32[210] = 0x45354437;
            p32[211] = 0x33453344;
            p32[212] = 0x41433745;
            p32[213] = 0x42344235;
            p32[214] = 0x33384335;
            p32[215] = 0x30453842;
            p32[216] = 0x46354531;
            p32[217] = 0x00004643;
            for(i = 218; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x00000199;
            p32[237] = 0x00000057;
            p32[238] = 0x00000057;
            p32[239] = 0x00000057;
            p32[240] = 0x00000001;
            break;
        case CURVE_K_571:
            p32[  0] = 0x00000009;
            p32[  1] = 0x0000008f;
            for(i = 2; i <= 36; i++)
                p32[i] = 0x30303030;

            p32[ 37] = 0x00303030;
            for(i = 38; i <= 72; i++)
                p32[i] = 0x30303030;

            p32[ 73] = 0x00313030;
            p32[ 74] = 0x62653632;
            p32[ 75] = 0x35386137;
            p32[ 76] = 0x33323939;
            p32[ 77] = 0x38636266;
            p32[ 78] = 0x39383132;
            p32[ 79] = 0x66313336;
            p32[ 80] = 0x33303138;
            p32[ 81] = 0x61346566;
            p32[ 82] = 0x61633963;
            p32[ 83] = 0x30373932;
            p32[ 84] = 0x64323130;
            p32[ 85] = 0x36346435;
            p32[ 86] = 0x38343230;
            p32[ 87] = 0x30383430;
            p32[ 88] = 0x31343831;
            p32[ 89] = 0x34346163;
            p32[ 90] = 0x39303733;
            p32[ 91] = 0x39343835;
            p32[ 92] = 0x30326233;
            p32[ 93] = 0x34366535;
            p32[ 94] = 0x33616437;
            p32[ 95] = 0x62643430;
            p32[ 96] = 0x62656334;
            p32[ 97] = 0x62633830;
            p32[ 98] = 0x62316462;
            p32[ 99] = 0x34393361;
            p32[100] = 0x37373439;
            p32[101] = 0x39626636;
            p32[102] = 0x34623838;
            p32[103] = 0x34373137;
            p32[104] = 0x38616364;
            p32[105] = 0x65376338;
            p32[106] = 0x35343932;
            p32[107] = 0x61333832;
            p32[108] = 0x38633130;
            p32[109] = 0x00323739;
            p32[110] = 0x64393433;
            p32[111] = 0x37303863;
            p32[112] = 0x62663466;
            p32[113] = 0x34373366;
            p32[114] = 0x65613466;
            p32[115] = 0x33656461;
            p32[116] = 0x39616362;
            p32[117] = 0x34313335;
            p32[118] = 0x38356464;
            p32[119] = 0x39636563;
            p32[120] = 0x37303366;
            p32[121] = 0x66343561;
            p32[122] = 0x31366366;
            p32[123] = 0x30636665;
            p32[124] = 0x38643630;
            p32[125] = 0x39633261;
            p32[126] = 0x37393464;
            p32[127] = 0x61306339;
            p32[128] = 0x61343463;
            p32[129] = 0x34376165;
            p32[130] = 0x62656266;
            p32[131] = 0x66396262;
            p32[132] = 0x61323737;
            p32[133] = 0x62636465;
            p32[134] = 0x62303236;
            p32[135] = 0x37613130;
            p32[136] = 0x61376162;
            p32[137] = 0x33623166;
            p32[138] = 0x33343032;
            p32[139] = 0x35386330;
            p32[140] = 0x38393139;
            p32[141] = 0x30366634;
            p32[142] = 0x34646331;
            p32[143] = 0x33343163;
            p32[144] = 0x63316665;
            p32[145] = 0x00336137;
            p32[146] = 0x00000044;
            for(i = 147; i <= 154; i++)
                p32[i] = 0x46464646;

            for(i = 155; i <= 159; i++)
                p32[i] = 0x30303030;

            p32[160] = 0x31303030;
            for(i = 161; i <= 190; i++)
                p32[i] = 0x00000000;

            p32[191] = 0x000000ac;
            p32[192] = 0x30303032;
            for(i = 193; i <= 208; i++)
                p32[i] = 0x30303030;

            p32[209] = 0x31303030;
            p32[210] = 0x35383133;
            p32[211] = 0x46314530;
            p32[212] = 0x36413931;
            p32[213] = 0x42344533;
            p32[214] = 0x41313933;
            p32[215] = 0x39424438;
            p32[216] = 0x34463731;
            p32[217] = 0x42383331;
            p32[218] = 0x44303336;
            p32[219] = 0x45423438;
            p32[220] = 0x33364435;
            p32[221] = 0x31383339;
            p32[222] = 0x44313945;
            p32[223] = 0x35344245;
            p32[224] = 0x37454643;
            p32[225] = 0x36463837;
            p32[226] = 0x31433733;
            p32[227] = 0x00313030;
            for(i = 228; i <= 235; i++)
                p32[i] = 0x00000000;

            p32[236] = 0x0000023b;
            p32[237] = 0x0000000a;
            p32[238] = 0x00000005;
            p32[239] = 0x00000002;
            p32[240] = 0x00000001;
            break;
        default:
            return -1;

    }

    return 0;
}



static ECC_CURVE * get_curve(E_ECC_CURVE ecc_curve)
{
    uint32_t   i;
    ECC_CURVE  *ret = NULL;

    if(CurveCpy((unsigned int *)&Curve_Copy, ecc_curve))
        return NULL;
    else
        return &Curve_Copy;

}


#else
static ECC_CURVE * get_curve(E_ECC_CURVE ecc_curve)
{
    uint32_t   i;
    ECC_CURVE  *ret = NULL;

    for(i = 0UL; i < sizeof(_Curve) / sizeof(ECC_CURVE); i++)
    {
        if(ecc_curve == _Curve[i].curve_id)
        {
            memcpy((char *)&Curve_Copy, &_Curve[i], sizeof(ECC_CURVE));
            ret = &Curve_Copy;   /* (ECC_CURVE *)&_Curve[i]; */
        }
        if(ret != NULL)
        {
            break;
        }
    }
    return ret;
}
#endif


/*@}*/ /* end of group CRYPTO_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group CRYPTO_Driver */

/*@}*/ /* end of group Standard_Driver */

/*** (C) COPYRIGHT 2017 Nuvoton Technology Corp. ***/

