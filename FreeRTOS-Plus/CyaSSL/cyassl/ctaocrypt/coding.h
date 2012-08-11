/* coding.h
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


#ifndef CTAO_CRYPT_CODING_H
#define CTAO_CRYPT_CODING_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* decode needed by CyaSSL */
CYASSL_LOCAL int Base64_Decode(const byte* in, word32 inLen, byte* out,
                               word32* outLen);

#if defined(OPENSSL_EXTRA) || defined(SESSION_CERTS) || defined(CYASSL_KEY_GEN)  || defined(CYASSL_CERT_GEN) || defined(HAVE_WEBSERVER)
    /* encode isn't */
    CYASSL_API
    int Base64_Encode(const byte* in, word32 inLen, byte* out,
                                  word32* outLen);
    CYASSL_LOCAL 
    int Base16_Decode(const byte* in, word32 inLen, byte* out, word32* outLen);
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_CODING_H */

