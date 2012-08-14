/* misc.h
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


#ifndef CTAO_CRYPT_MISC_H
#define CTAO_CRYPT_MISC_H


#include <cyassl/ctaocrypt/types.h>


#ifdef __cplusplus
    extern "C" {
#endif


#ifdef NO_INLINE
CYASSL_LOCAL
word32 rotlFixed(word32, word32);
CYASSL_LOCAL
word32 rotrFixed(word32, word32);

CYASSL_LOCAL
word32 ByteReverseWord32(word32);
CYASSL_LOCAL
void   ByteReverseWords(word32*, const word32*, word32);
CYASSL_LOCAL
void   ByteReverseBytes(byte*, const byte*, word32);

CYASSL_LOCAL
void XorWords(word*, const word*, word32);
CYASSL_LOCAL
void xorbuf(byte*, const byte*, word32);

#ifdef WORD64_AVAILABLE
CYASSL_LOCAL
word64 rotlFixed64(word64, word64);
CYASSL_LOCAL
word64 rotrFixed64(word64, word64);

CYASSL_LOCAL
word64 ByteReverseWord64(word64);
CYASSL_LOCAL
void   ByteReverseWords64(word64*, const word64*, word32);
#endif /* WORD64_AVAILABLE */

#endif /* NO_INLINE */


#ifdef __cplusplus
    }   /* extern "C" */
#endif


#endif /* CTAO_CRYPT_MISC_H */

