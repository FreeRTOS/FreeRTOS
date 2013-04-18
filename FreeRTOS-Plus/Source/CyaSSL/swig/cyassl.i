/* cyassl.i
 *
 * Copyright (C) 2006-2011 Sawtooth Consulting Ltd.
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

%module cyassl
%{
    #include <cyassl/ssl.h>
    #include <cyassl/ctaocrypt/rsa.h>

    /* defn adds */
    char* CyaSSL_error_string(int err);
    int   CyaSSL_swig_connect(CYASSL*, const char* server, int port);
    RNG*  GetRng(void);
    RsaKey* GetRsaPrivateKey(const char* file);
    void    FillSignStr(unsigned char*, const char*, int);
%}


CYASSL_METHOD* CyaTLSv1_client_method(void);
CYASSL_CTX*    CyaSSL_CTX_new(CYASSL_METHOD*);
int            CyaSSL_CTX_load_verify_locations(CYASSL_CTX*, const char*, const char*);
CYASSL*        CyaSSL_new(CYASSL_CTX*);
int            CyaSSL_get_error(CYASSL*, int);
int            CyaSSL_write(CYASSL*, const char*, int);
int            CyaSSL_Debugging_ON(void);
int            CyaSSL_Init(void);
char*          CyaSSL_error_string(int);
int            CyaSSL_swig_connect(CYASSL*, const char* server, int port);

int         RsaSSL_Sign(const unsigned char* in, int inLen, unsigned char* out, int outLen, RsaKey* key, RNG* rng);

int         RsaSSL_Verify(const unsigned char* in, int inLen, unsigned char* out, int outLen, RsaKey* key);

RNG* GetRng(void);
RsaKey* GetRsaPrivateKey(const char* file);
void    FillSignStr(unsigned char*, const char*, int);

%include carrays.i
%include cdata.i
%array_class(unsigned char, byteArray);
int         CyaSSL_read(CYASSL*, unsigned char*, int);


#define    SSL_FAILURE      0
#define    SSL_SUCCESS      1

