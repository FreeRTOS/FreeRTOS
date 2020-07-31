/* dh.h
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



#ifndef NO_DH

#ifndef CTAO_CRYPT_DH_H
#define CTAO_CRYPT_DH_H

/* for dh reverse compatibility */
#include <wolfssl/wolfcrypt/dh.h>
#define InitDhKey         wc_InitDhKey
#define FreeDhKey         wc_FreeDhKey
#define DhGenerateKeyPair wc_DhGenerateKeyPair
#define DhAgree           wc_DhAgree
#define DhKeyDecode       wc_DhKeyDecode
#define DhSetKey          wc_DhSetKey
#define DhParamsLoad      wc_DhParamsLoad

#endif /* CTAO_CRYPT_DH_H */

#endif /* NO_DH */

