/* hc128.h
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



#ifndef NO_HC128

#ifndef CTAO_CRYPT_HC128_H
#define CTAO_CRYPT_HC128_H

#include <wolfssl/wolfcrypt/hc128.h>

/* for hc128 reverse compatibility */
#ifdef HAVE_HC128
    #define Hc128_Process wc_Hc128_Process
    #define Hc128_SetKey  wc_Hc128_SetKey
#endif

#endif /* CTAO_CRYPT_HC128_H */

#endif /* HAVE_HC128 */

