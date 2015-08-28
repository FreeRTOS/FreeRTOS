/* md2.h
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


/* check for old macro */
#if !defined(CYASSL_MD2) && defined(WOLFSSL_MD2)
    #define CYASSL_MD2
#endif

#ifdef CYASSL_MD2

#ifndef CTAO_CRYPT_MD2_H
#define CTAO_CRYPT_MD2_H

#include <wolfssl/wolfcrypt/md2.h>

#define InitMd2   wc_InitMd2
#define Md2Update wc_Md2Update
#define Md2Final  wc_Md2Final
#define Md2Hash   wc_Md2Hash

#endif /* CTAO_CRYPT_MD2_H */
#endif /* CYASSL_MD2 */

