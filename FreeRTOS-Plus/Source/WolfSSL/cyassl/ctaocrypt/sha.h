/* sha.h
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



#ifndef NO_SHA

#ifndef CTAO_CRYPT_SHA_H
#define CTAO_CRYPT_SHA_H

#include <wolfssl/wolfcrypt/sha.h>
#define InitSha   wc_InitSha
#define ShaUpdate wc_ShaUpdate
#define ShaFinal  wc_ShaFinal
#define ShaHash   wc_ShaHash

#endif /* CTAO_CRYPT_SHA_H */
#endif /* NO_SHA */

