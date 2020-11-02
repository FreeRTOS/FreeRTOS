/* fips_test.h
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



#ifndef WOLF_CRYPT_FIPS_TEST_H
#define WOLF_CRYPT_FIPS_TEST_H

#include <wolfssl/wolfcrypt/types.h>


#ifdef __cplusplus
    extern "C" {
#endif

/* Known Answer Test string inputs are hex, internal */
WOLFSSL_LOCAL int DoKnownAnswerTests(char*, int);


/* FIPS failure callback */
typedef void(*wolfCrypt_fips_cb)(int ok, int err, const char* hash);

/* Public set function */
WOLFSSL_API int wolfCrypt_SetCb_fips(wolfCrypt_fips_cb cbf);

/* Public get status functions */
WOLFSSL_API int wolfCrypt_GetStatus_fips(void);
WOLFSSL_API const char* wolfCrypt_GetCoreHash_fips(void);

#ifdef HAVE_FORCE_FIPS_FAILURE
    /* Public function to force failure mode for operational testing */
    WOLFSSL_API int wolfCrypt_SetStatus_fips(int);
#endif


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLF_CRYPT_FIPS_TEST_H */

