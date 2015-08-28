/* asn.h
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

#ifndef NO_ASN

#ifndef CTAO_CRYPT_ASN_H
#define CTAO_CRYPT_ASN_H

/* pull in compatibility for each include */
#include <cyassl/ctaocrypt/dh.h>
#include <cyassl/ctaocrypt/dsa.h>
#include <cyassl/ctaocrypt/sha.h>
#include <cyassl/ctaocrypt/md5.h>
#include <cyassl/ctaocrypt/asn_public.h>   /* public interface */
#ifdef HAVE_ECC
    #include <cyassl/ctaocrypt/ecc.h>
#endif


#include <wolfssl/wolfcrypt/asn.h>

#ifndef WOLFSSL_PEMCERT_TODER_DEFINED
#ifndef NO_FILESYSTEM
    #define CyaSSL_PemCertToDer wolfSSL_PemCertToDer
#endif
#endif

#endif /* CTAO_CRYPT_ASN_H */

#endif /* !NO_ASN */

