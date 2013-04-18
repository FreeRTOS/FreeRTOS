/* random.c
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

/* on HPUX 11 you may need to install /dev/random see
   http://h20293.www2.hp.com/portal/swdepot/displayProductInfo.do?productNumber=KRNG11I

*/

#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/error.h>


#if defined(USE_WINDOWS_API)
    #ifndef _WIN32_WINNT
        #define _WIN32_WINNT 0x0400
    #endif
    #include <windows.h>
    #include <wincrypt.h>
#else
    #ifndef NO_DEV_RANDOM
        #include <fcntl.h>
        #include <unistd.h>
    #else
        /* include headers that may be needed to get good seed */
    #endif
#endif /* USE_WINDOWS_API */



/* Get seed and key cipher */
int InitRng(RNG* rng)
{
    byte key[32];
    byte junk[256];

    int  ret = GenerateSeed(&rng->seed, key, sizeof(key));

    if (ret == 0) {
        Arc4SetKey(&rng->cipher, key, sizeof(key));
        RNG_GenerateBlock(rng, junk, sizeof(junk));  /* rid initial state */
    }

    return ret;
}


/* place a generated block in output */
void RNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
    XMEMSET(output, 0, sz);
    Arc4Process(&rng->cipher, output, output, sz);
}


byte RNG_GenerateByte(RNG* rng)
{
    byte b;
    RNG_GenerateBlock(rng, &b, 1);

    return b;
}


#if defined(USE_WINDOWS_API)


int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    if(!CryptAcquireContext(&os->handle, 0, 0, PROV_RSA_FULL,
                            CRYPT_VERIFYCONTEXT))
        return WINCRYPT_E;

    if (!CryptGenRandom(os->handle, sz, output))
        return CRYPTGEN_E;

    CryptReleaseContext(os->handle, 0);

    return 0;
}


#elif defined(THREADX)

#include "rtprand.h"   /* rtp_rand () */
#include "rtptime.h"   /* rtp_get_system_msec() */


int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int i;
    rtp_srand(rtp_get_system_msec());

    for (i = 0; i < sz; i++ ) {
        output[i] = rtp_rand() % 256;
        if ( (i % 8) == 7)
            rtp_srand(rtp_get_system_msec());
    }

    return 0;
}


#elif defined(MICRIUM)

int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
        NetSecure_InitSeed(output, sz);
    #endif
    return 0;
}

#elif defined(MBED)

/* write a real one !!!, just for testing board */
int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int i;
    for (i = 0; i < sz; i++ )
        output[i] = i;

    return 0;
}

#elif defined(NO_DEV_RANDOM)

#error "you need to write an os specific GenerateSeed() here"


#else /* !USE_WINDOWS_API && !THREADX && !MICRIUM && !NO_DEV_RANDOM */


/* may block */
int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int ret = 0;

    os->fd = open("/dev/urandom",O_RDONLY);
    if (os->fd == -1) {
        /* may still have /dev/random */
        os->fd = open("/dev/random",O_RDONLY);
        if (os->fd == -1)
            return OPEN_RAN_E;
    }

    while (sz) {
        int len = read(os->fd, output, sz);
        if (len == -1) { 
            ret = READ_RAN_E;
            break;
        }

        sz     -= len;
        output += len;

        if (sz) {
#ifdef BLOCKING
            sleep(0);             /* context switch */
#else
            ret = RAN_BLOCK_E;
            break;
#endif
        }
    }
    close(os->fd);

    return ret;
}

#endif /* USE_WINDOWS_API */

