/* evp.h
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



/*  evp.h defines mini evp openssl compatibility layer
 *
 */

#ifndef CYASSL_OPENSSL_EVP
#define CYASSL_OPENSSL_EVP

#define CyaSSL_StoreExternalIV       wolfSSL_StoreExternalIV
#define CyaSSL_SetInternalIV         wolfSSL_SetInternalIV
#define CYASSL_EVP_MD                WOLFSSL_EVP_MD
#define CyaSSL_EVP_X_STATE           wolfSSL_EVP_X_STATE
#define CyaSSL_EVP_X_STATE_LEN       wolfSSL_EVP_X_STATE_LEN
#define CyaSSL_3des_iv               wolfSSL_3des_iv
#define CyaSSL_aes_ctr_iv            wolfSSL_aes_ctr_iv

#include <wolfssl/openssl/evp.h>
#endif

