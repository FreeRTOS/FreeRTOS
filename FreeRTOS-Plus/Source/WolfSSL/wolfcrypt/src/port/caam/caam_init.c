/* caam_init.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#include <wolfssl/wolfcrypt/settings.h>

#if defined(WOLFSSL_IMX6_CAAM) || defined(WOLFSSL_IMX6_CAAM_RNG) || \
    defined(WOLFSSL_IMX6_CAAM_BLOB)

#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/port/caam/wolfcaam.h>

#define WC_CAAM_BLOB_SZ 48

#ifndef WC_CAAM_PASSWORD
    #define WC_CAAM_PASSWORD "!systempassword"
#endif

#if defined(__INTEGRITY) || defined(INTEGRITY)
    #include <INTEGRITY.h>
    #include <wolfssl/wolfcrypt/port/caam/caam_driver.h>
    static IODevice caam = NULLIODevice;
#endif

#if defined(WOLFSSL_CAAM_PRINT) || defined(WOLFSSL_CAAM_DEBUG)
#include <stdio.h>
#include <wolfssl/version.h>

static void wc_caamBanner(void)
{
    printf("********* wolfSSL Version %s : Printing Out CAAM Information ********\n",
        LIBWOLFSSL_VERSION_STRING);
    printf("CAAM Status [0x%8.8x]   = 0x%8.8x\n",
        CAAM_STATUS, WC_CAAM_READ(CAAM_STATUS));
    printf("CAAM Version MS Register [0x%8.8x]  = 0x%8.8x\n",
        CAAM_VERSION_MS, WC_CAAM_READ(CAAM_VERSION_MS));
    printf("CAAM Version LS Register [0x%8.8x]  = 0x%8.8x\n",
        CAAM_VERSION_LS, WC_CAAM_READ(CAAM_VERSION_LS));
    printf("CAAM Support MS Register [0x%8.8x] = 0x%8.8x\n",
        CAMM_SUPPORT_MS, WC_CAAM_READ(CAMM_SUPPORT_MS));
    printf("CAAM Support LS [0x%8.8x] = 0x%8.8x\n",
        CAMM_SUPPORT_LS, WC_CAAM_READ(CAMM_SUPPORT_LS));
    printf("********************************************************************\n\n");
}
#endif


/* Allow runtime setting for CAAM IODevice in case user wants to use password
 * at run time.
 *
 * returns 0 on success
 *
 * NOTE this is how IODevice is defined in INTEGRITY "typedef struct
 *      IODeviceStruct        *IODevice;"
 */
int wc_caamSetResource(IODevice ioDev)
{
    WOLFSSL_MSG("Setting CAAM driver");
    caam = ioDev;

    return 0;
}

/* Check hardware support
 *
 * returns 0 on success
 */
int wc_caamInit(void)
{
    int    ret;
    word32 reg;

    /* get the driver up */
    if (caam == NULLIODevice) {
        WOLFSSL_MSG("Starting CAAM driver");
        if ((ret = (int)RequestResource((Object *)&caam, "wolfSSL_CAAM_Driver",
            WC_CAAM_PASSWORD)) != (int)Success) {
            WOLFSSL_MSG("Unable to get the CAAM IODevice, check password?");
            WOLFSSL_LEAVE("wc_caamInit: error from driver = ", ret);
            ret = 0; /* not a hard failure because user can set resource */
        }
    }

#if defined(WOLFSSL_CAAM_PRINT) || defined(WOLFSSL_CAAM_DEBUG)
    /* print out CAAM version/info and wolfSSL version */
    wc_caamBanner();
#endif

    /* check that for implemented modules
     * bits 0-3 AES, 4-7 DES, 12-15 Hashing , 16-19 RNG */
    reg = WC_CAAM_READ(CAMM_SUPPORT_LS);

    #ifndef WC_NO_RNG
    if (((reg & 0x000F0000) >> 16) > 0) {
        WOLFSSL_MSG("Found CAAM RNG hardware module");
        if ((WC_CAAM_READ(CAAM_RTMCTL) & 0x40000001) != 0x40000001) {
             WOLFSSL_MSG("Error CAAM RNG has not been set up");
        }
    }
    #endif

    #ifndef NO_SHA256
    if ((reg & 0x0000F000) > 0) {
        WOLFSSL_MSG("Found CAAM MDHA module");
    }
    else {
        WOLFSSL_MSG("Hashing not supported by CAAM");
        return WC_HW_E;
    }
    #endif

    #ifndef NO_AES
    if ((reg & 0x0000000F) > 0) {
        WOLFSSL_MSG("Found CAAM AES module");
    }
    else {
        WOLFSSL_MSG("AES not supported by CAAM");
        return WC_HW_E;
    }
    #endif

    (void)ret;
    return 0;
}


int wc_caamFree(void)
{
    return 0;
}


word32 wc_caamReadRegister(word32 reg)
{
    Value out = 0;

    if (caam == NULLIODevice) {
         WOLFSSL_MSG("Error CAAM IODevice not found! Bad password?");
         return 0;
    }

    if (ReadIODeviceRegister(caam, reg, &out) != Success) {
         WOLFSSL_MSG("Error reading register\n");
    }

    return (word32)out;
}

void wc_caamWriteRegister(word32 reg, word32 value)
{
    if (caam == NULLIODevice) {
         WOLFSSL_MSG("Error CAAM IODevice not found! Bad password?");
         return;
    }

    if (WriteIODeviceRegister(caam, reg, value) != Success) {
         WOLFSSL_MSG("Error writing to register\n");
    }
}


/* return 0 on success and WC_HW_E on failure. Can also return WC_HW_WAIT_E
 * in the case that the driver is waiting for a resource or RAN_BLOCK_E if
 * waiting for entropy. */
int wc_caamAddAndWait(Buffer* buf, word32 arg[4], word32 type)
{
    int ret;
    if (caam == NULLIODevice) {
        WOLFSSL_MSG("Error CAAM IODevice not found! Bad password?");
        return WC_HW_E;
    }

    if ((ret = SynchronousSendIORequest(caam, type, (const Value*)arg, buf))
         != Success) {
    #if defined(WOLFSSL_CAAM_PRINT) || defined(WOLFSSL_CAAM_DEBUG)
        printf("ret of SynchronousSendIORequest = %d type = %d\n", ret, type);
    #endif

        /* if waiting for resource or RNG return waiting */
        if (ret == Waiting) {
            WOLFSSL_MSG("Waiting on entropy from driver");
            return RAN_BLOCK_E;
        }

        if (ret == ResourceNotAvailable) {
            WOLFSSL_MSG("Waiting on CAAM driver");
            return WC_HW_WAIT_E;
        }

        return WC_HW_E;
    }

    (void)ret;
    return 0;
}


int wc_caamCreateBlob(byte* data, word32 dataSz, byte* out, word32* outSz)
{
    Buffer in[3];
    word32 arg[4];
    int ret;
    word32 local[2] = {0,0};

    if (data == NULL || out == NULL || outSz == NULL ||
            *outSz < dataSz + WC_CAAM_BLOB_SZ) {
        return BAD_FUNC_ARG;
    }

    in[0].BufferType = DataBuffer;
    in[0].TheAddress = (Address)local;
    in[0].Length = sizeof(local);

    in[1].BufferType = DataBuffer;
    in[1].TheAddress = (Address)data;
    in[1].Length = dataSz;

    in[2].BufferType = DataBuffer | LastBuffer;
    in[2].TheAddress = (Address)out;
    in[2].Length = dataSz + WC_CAAM_BLOB_SZ;

    arg[2] = dataSz;

    if ((ret = wc_caamAddAndWait(in, arg, CAAM_BLOB_ENCAP)) != 0) {
        WOLFSSL_MSG("Error with CAAM blob create");
        return ret;
    }

    *outSz = dataSz + WC_CAAM_BLOB_SZ;
    return 0;
}


int wc_caamOpenBlob(byte* data, word32 dataSz, byte* out, word32* outSz)
{
    Buffer in[3];
    word32 arg[4];
    int ret;
    word32 local[2] = {0,0};

    if (data == NULL || out == NULL || outSz == NULL ||
            *outSz < dataSz - WC_CAAM_BLOB_SZ) {
        return BAD_FUNC_ARG;
    }

    in[0].BufferType = DataBuffer;
    in[0].TheAddress = (Address)local;
    in[0].Length = sizeof(local);

    in[0].BufferType = DataBuffer;
    in[0].TheAddress = (Address)data;
    in[0].Length = dataSz;

    in[1].BufferType = DataBuffer | LastBuffer;
    in[1].TheAddress = (Address)out;
    in[1].Length = dataSz - WC_CAAM_BLOB_SZ;

    arg[2] = dataSz;

    if ((ret = wc_caamAddAndWait(in, arg, CAAM_BLOB_DECAP)) != 0) {
        WOLFSSL_MSG("Error with CAAM blob create");
        return ret;
    }

    *outSz = dataSz - WC_CAAM_BLOB_SZ;
    return 0;
}

#endif /* WOLFSSL_IMX6_CAAM */

