/* ssl.h
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


/* CyaSSL OCSP API */

#ifndef CYASSL_OCSP_H
#define CYASSL_OCSP_H


#include <cyassl/ctaocrypt/asn.h>


#ifdef __cplusplus
    extern "C" {
#endif

typedef struct CYASSL_OCSP CYASSL_OCSP;
typedef struct CertStatus CertStatus;

struct CertStatus {
    byte issuerHash[SHA_SIZE];
    byte issuerKeyHash[SHA_SIZE];
    byte serial[EXTERNAL_SERIAL_SIZE];
    int serialSz;
    int status;
};

struct CYASSL_OCSP {
    byte enabled;
    byte useOverrideUrl;
    char overrideName[80];
    char overridePath[80];
    int  overridePort;
    int statusLen;
    CertStatus status[1];
};



CYASSL_LOCAL int  CyaSSL_OCSP_Init(CYASSL_OCSP*);
CYASSL_LOCAL void CyaSSL_OCSP_Cleanup(CYASSL_OCSP*);
CYASSL_LOCAL int  CyaSSL_OCSP_set_override_url(CYASSL_OCSP*, const char*);
CYASSL_LOCAL int  CyaSSL_OCSP_Lookup_Cert(CYASSL_OCSP*, DecodedCert*);


#ifdef __cplusplus
    }  /* extern "C" */
#endif


#endif /* CYASSL_OCSP_H */


