/* crl.h
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


#ifndef CYASSL_CRL_H
#define CYASSL_CRL_H

#include <cyassl/ssl.h>
#include <cyassl/ctaocrypt/asn.h>

#ifdef __cplusplus
    extern "C" {
#endif

typedef struct CYASSL_CRL CYASSL_CRL;

CYASSL_LOCAL int  InitCRL(CYASSL_CRL*, CYASSL_CERT_MANAGER*);
CYASSL_LOCAL void FreeCRL(CYASSL_CRL*);

CYASSL_LOCAL int  LoadCRL(CYASSL_CRL* crl, const char* path, int type, int mon);
CYASSL_LOCAL int  BufferLoadCRL(CYASSL_CRL*, const byte*, long, int);
CYASSL_LOCAL int  CheckCertCRL(CYASSL_CRL*, DecodedCert*);


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* CYASSL_CRL_H */
