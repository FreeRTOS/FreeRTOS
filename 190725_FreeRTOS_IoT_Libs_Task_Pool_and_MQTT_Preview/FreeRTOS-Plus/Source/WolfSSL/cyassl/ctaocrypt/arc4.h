/* arc4.h
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

#ifndef CTAO_CRYPT_ARC4_H
#define CTAO_CRYPT_ARC4_H

/* for arc4 reverse compatibility */
#ifndef NO_RC4
#include <wolfssl/wolfcrypt/arc4.h>
    #define CYASSL_ARC4_CAVIUM_MAGIC WOLFSSL_ARC4_CAVIUM_MAGIC
    #define Arc4Process wc_Arc4Process
    #define Arc4SetKey wc_Arc4SetKey
    #define Arc4InitCavium wc_Arc4InitCavium
    #define Arc4FreeCavium wc_Arc4FreeCavium
#endif

#endif /* CTAO_CRYPT_ARC4_H */

