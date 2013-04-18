/* dh.h for openSSL */


#ifndef CYASSL_DH_H_
#define CYASSL_DH_H_


#include <cyassl/openssl/ssl.h>
#include <cyassl/openssl/bn.h>


#ifdef __cplusplus
    extern "C" {
#endif




typedef struct CYASSL_DH {
	CYASSL_BIGNUM* p;
	CYASSL_BIGNUM* g;
    CYASSL_BIGNUM* pub_key;      /* openssh deference g^x */
    CYASSL_BIGNUM* priv_key;     /* openssh deference x   */
    void*          internal;     /* our DH */
    char           inSet;        /* internal set from external ? */
    char           exSet;        /* external set from internal ? */
} CYASSL_DH;


CYASSL_API CYASSL_DH* CyaSSL_DH_new(void);
CYASSL_API void       CyaSSL_DH_free(CYASSL_DH*);

CYASSL_API int CyaSSL_DH_size(CYASSL_DH*);
CYASSL_API int CyaSSL_DH_generate_key(CYASSL_DH*);
CYASSL_API int CyaSSL_DH_compute_key(unsigned char* key, CYASSL_BIGNUM* pub,
                                     CYASSL_DH*);

typedef CYASSL_DH DH;

#define DH_new  CyaSSL_DH_new 
#define DH_free CyaSSL_DH_free

#define DH_size         CyaSSL_DH_size
#define DH_generate_key CyaSSL_DH_generate_key
#define DH_compute_key  CyaSSL_DH_compute_key


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif

#endif /* header */
