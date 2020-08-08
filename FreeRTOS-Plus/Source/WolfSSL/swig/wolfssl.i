/* wolfssl.i
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


%module wolfssl
%{
    #include <wolfssl/ssl.h>
    #include <wolfssl/wolfcrypt/rsa.h>
    #include <wolfssl/wolfcrypt/pwdbased.h>

    /* defn adds */
    char* wolfSSL_error_string(int err);
    int   wolfSSL_swig_connect(WOLFSSL*, const char* server, int port);
    WC_RNG* GetRng(void);
    RsaKey* GetRsaPrivateKey(const char* file);
    void    FillSignStr(unsigned char*, const char*, int);
%}


WOLFSSL_METHOD* wolfTLSv1_2_client_method(void);
WOLFSSL_CTX*    wolfSSL_CTX_new(WOLFSSL_METHOD*);
int             wolfSSL_CTX_load_verify_locations(WOLFSSL_CTX*, const char*, const char*);
WOLFSSL*        wolfSSL_new(WOLFSSL_CTX*);
int             wolfSSL_get_error(WOLFSSL*, int);
int             wolfSSL_write(WOLFSSL*, const char*, int);
int             wolfSSL_Debugging_ON(void);
int             wolfSSL_Init(void);
char*           wolfSSL_error_string(int);
int             wolfSSL_swig_connect(WOLFSSL*, const char* server, int port);

int         wc_PKCS12_PBKDF(unsigned char* output, const unsigned char* passwd, int pLen, const unsigned char* salt,
                        int sLen, int iterations, int kLen, int hashType, int purpose);

int         wc_RsaSSL_Sign(const unsigned char* in, int inLen, unsigned char* out, int outLen, RsaKey* key, WC_RNG* rng);

int         wc_RsaSSL_Verify(const unsigned char* in, int inLen, unsigned char* out, int outLen, RsaKey* key);

WC_RNG* GetRng(void);
RsaKey* GetRsaPrivateKey(const char* file);
void    FillSignStr(unsigned char*, const char*, int);

%include carrays.i
%include cdata.i
%array_class(unsigned char, byteArray);
int         wolfSSL_read(WOLFSSL*, unsigned char*, int);


#define    SSL_FAILURE      0
#define    SSL_SUCCESS      1

