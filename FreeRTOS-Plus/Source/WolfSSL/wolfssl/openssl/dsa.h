/* dsa.h for openSSL */


#ifndef WOLFSSL_DSA_H_
#define WOLFSSL_DSA_H_


#include <wolfssl/openssl/ssl.h>
#include <wolfssl/openssl/bn.h>


#ifdef __cplusplus
    extern "C" {
#endif



struct WOLFSSL_DSA {
	WOLFSSL_BIGNUM* p;
	WOLFSSL_BIGNUM* q;
	WOLFSSL_BIGNUM* g;
	WOLFSSL_BIGNUM* pub_key;      /* our y */
	WOLFSSL_BIGNUM* priv_key;     /* our x */
    void*          internal;     /* our Dsa Key */
    char           inSet;        /* internal set from external ? */
    char           exSet;        /* external set from internal ? */
};


WOLFSSL_API WOLFSSL_DSA* wolfSSL_DSA_new(void);
WOLFSSL_API void        wolfSSL_DSA_free(WOLFSSL_DSA*);

WOLFSSL_API int wolfSSL_DSA_generate_key(WOLFSSL_DSA*);
WOLFSSL_API int wolfSSL_DSA_generate_parameters_ex(WOLFSSL_DSA*, int bits,
                   unsigned char* seed, int seedLen, int* counterRet,
                   unsigned long* hRet, void* cb);

WOLFSSL_API int wolfSSL_DSA_LoadDer(WOLFSSL_DSA*, const unsigned char*, int sz);
WOLFSSL_API int wolfSSL_DSA_do_sign(const unsigned char* d, unsigned char* sigRet,
                                  WOLFSSL_DSA* dsa);

#define DSA_new wolfSSL_DSA_new
#define DSA_free wolfSSL_DSA_free

#define DSA_generate_key           wolfSSL_DSA_generate_key
#define DSA_generate_parameters_ex wolfSSL_DSA_generate_parameters_ex


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif

#endif /* header */
