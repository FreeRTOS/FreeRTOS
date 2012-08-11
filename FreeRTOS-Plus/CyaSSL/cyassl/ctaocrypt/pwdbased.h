/* pwdbased.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef NO_PWDBASED

#ifndef CTAO_CRYPT_PWDBASED_H
#define CTAO_CRYPT_PWDBASED_H

#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/md5.h>       /* for hash type */
#include <cyassl/ctaocrypt/sha.h>

#ifdef __cplusplus
    extern "C" {
#endif


CYASSL_API int PBKDF1(byte* output, const byte* passwd, int pLen,
                      const byte* salt, int sLen, int iterations, int kLen,
                      int hashType);
CYASSL_API int PBKDF2(byte* output, const byte* passwd, int pLen,
                      const byte* salt, int sLen, int iterations, int kLen,
                      int hashType);
CYASSL_API int PKCS12_PBKDF(byte* output, const byte* passwd, int pLen,
                            const byte* salt, int sLen, int iterations,
                            int kLen, int hashType, int purpose);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_PWDBASED_H */
#endif /* NO_PWDBASED */
