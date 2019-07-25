/* pwdbased.h
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


#ifndef NO_PWDBASED

#ifndef CTAO_CRYPT_PWDBASED_H
#define CTAO_CRYPT_PWDBASED_H

/* for pwdbased reverse compatibility */
#include <wolfssl/wolfcrypt/pwdbased.h>
#define PBKDF1       wc_PBKDF1
#define PBKDF2       wc_PBKDF2
#define PKCS12_PBKDF wc_PKCS12_PBKDF

#endif /* CTAO_CRYPT_PWDBASED_H */
#endif /* NO_PWDBASED */

