/* rsa.h for openSSL */


#ifndef CYASSL_RSA_H_
#define CYASSL_RSA_H_

#include <cyassl/openssl/ssl.h>
#include <cyassl/openssl/bn.h>


#ifdef __cplusplus
    extern "C" {
#endif


enum  { 
	RSA_PKCS1_PADDING = 1
 };

struct CYASSL_RSA {
	CYASSL_BIGNUM* n;
	CYASSL_BIGNUM* e;
	CYASSL_BIGNUM* d;
	CYASSL_BIGNUM* p;
	CYASSL_BIGNUM* q;
	CYASSL_BIGNUM* dmp1;      /* dP */
	CYASSL_BIGNUM* dmq1;      /* dQ */
	CYASSL_BIGNUM* iqmp;      /* u */
    void*          internal;  /* our RSA */
    char           inSet;     /* internal set from external ? */
    char           exSet;     /* external set from internal ? */
};


CYASSL_API CYASSL_RSA* CyaSSL_RSA_new(void);
CYASSL_API void        CyaSSL_RSA_free(CYASSL_RSA*);

CYASSL_API int CyaSSL_RSA_generate_key_ex(CYASSL_RSA*, int bits, CYASSL_BIGNUM*,
                                          void* cb);

CYASSL_API int CyaSSL_RSA_blinding_on(CYASSL_RSA*, CYASSL_BN_CTX*);
CYASSL_API int CyaSSL_RSA_public_encrypt(int len, unsigned char* fr,
	                               unsigned char* to, CYASSL_RSA*, int padding);
CYASSL_API int CyaSSL_RSA_private_decrypt(int len, unsigned char* fr,
	                               unsigned char* to, CYASSL_RSA*, int padding);

CYASSL_API int CyaSSL_RSA_size(const CYASSL_RSA*);
CYASSL_API int CyaSSL_RSA_sign(int type, const unsigned char* m,
                               unsigned int mLen, unsigned char* sigRet,
                               unsigned int* sigLen, CYASSL_RSA*);
CYASSL_API int CyaSSL_RSA_public_decrypt(int flen, unsigned char* from,
                                  unsigned char* to, CYASSL_RSA*, int padding);
CYASSL_API int CyaSSL_RSA_GenAdd(CYASSL_RSA*);
CYASSL_API int CyaSSL_RSA_LoadDer(CYASSL_RSA*, const unsigned char*, int sz);


#define RSA_new  CyaSSL_RSA_new
#define RSA_free CyaSSL_RSA_free

#define RSA_generate_key_ex CyaSSL_RSA_generate_key_ex

#define RSA_blinding_on     CyaSSL_RSA_blinding_on
#define RSA_public_encrypt  CyaSSL_RSA_public_encrypt
#define RSA_private_decrypt CyaSSL_RSA_private_decrypt

#define RSA_size           CyaSSL_RSA_size
#define RSA_sign           CyaSSL_RSA_sign
#define RSA_public_decrypt CyaSSL_RSA_public_decrypt


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif

#endif /* header */
