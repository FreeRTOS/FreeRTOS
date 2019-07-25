/* poly1305.h
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


#ifdef HAVE_POLY1305

#ifndef CTAO_CRYPT_POLY1305_H
#define CTAO_CRYPT_POLY1305_H

#include <wolfssl/wolfcrypt/poly1305.h>

/* for poly1305 reverse compatibility */
#define Poly1305SetKey wc_Poly1305SetKey
#define Poly1305Update wc_Poly1305Update
#define Poly1305Final  wc_Poly1305Final

#endif /* CTAO_CRYPT_POLY1305_H */

#endif /* HAVE_POLY1305 */

