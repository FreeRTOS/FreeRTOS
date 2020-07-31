/* arc4.h
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


#ifndef CTAO_CRYPT_ARC4_H
#define CTAO_CRYPT_ARC4_H

/* for arc4 reverse compatibility */
#ifndef NO_RC4
#include <wolfssl/wolfcrypt/arc4.h>
    #define Arc4Process wc_Arc4Process
    #define Arc4SetKey wc_Arc4SetKey
    #define Arc4AsyncInit wc_Arc4AsyncInit
    #define Arc4AsyncFree wc_Arc4AsyncFree
#endif

#endif /* CTAO_CRYPT_ARC4_H */

