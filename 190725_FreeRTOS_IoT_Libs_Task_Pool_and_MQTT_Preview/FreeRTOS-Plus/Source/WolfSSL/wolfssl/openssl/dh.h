/* dh.h for openSSL */


#ifndef WOLFSSL_DH_H_
#define WOLFSSL_DH_H_


#include <wolfssl/openssl/ssl.h>
#include <wolfssl/openssl/bn.h>


#ifdef __cplusplus
    extern "C" {
#endif




typedef struct WOLFSSL_DH {
	WOLFSSL_BIGNUM* p;
	WOLFSSL_BIGNUM* g;
    WOLFSSL_BIGNUM* pub_key;      /* openssh deference g^x */
    WOLFSSL_BIGNUM* priv_key;     /* openssh deference x   */
    void*          internal;     /* our DH */
    char           inSet;        /* internal set from external ? */
    char           exSet;        /* external set from internal ? */
} WOLFSSL_DH;


WOLFSSL_API WOLFSSL_DH* wolfSSL_DH_new(void);
WOLFSSL_API void       wolfSSL_DH_free(WOLFSSL_DH*);

WOLFSSL_API int wolfSSL_DH_size(WOLFSSL_DH*);
WOLFSSL_API int wolfSSL_DH_generate_key(WOLFSSL_DH*);
WOLFSSL_API int wolfSSL_DH_compute_key(unsigned char* key, WOLFSSL_BIGNUM* pub,
                                     WOLFSSL_DH*);

typedef WOLFSSL_DH DH;

#define DH_new  wolfSSL_DH_new 
#define DH_free wolfSSL_DH_free

#define DH_size         wolfSSL_DH_size
#define DH_generate_key wolfSSL_DH_generate_key
#define DH_compute_key  wolfSSL_DH_compute_key


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif

#endif /* header */
