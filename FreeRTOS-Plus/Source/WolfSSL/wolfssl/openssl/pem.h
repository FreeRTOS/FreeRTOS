/* pem.h for openssl */


#ifndef WOLFSSL_PEM_H_
#define WOLFSSL_PEM_H_

#include <wolfssl/openssl/evp.h>
#include <wolfssl/openssl/bio.h>
#include <wolfssl/openssl/rsa.h>
#include <wolfssl/openssl/dsa.h>

#ifdef __cplusplus
    extern "C" {
#endif


WOLFSSL_API int wolfSSL_PEM_write_bio_RSAPrivateKey(WOLFSSL_BIO* bio, RSA* rsa,
	                                  const EVP_CIPHER* cipher,
	                                  unsigned char* passwd, int len,
	                                  pem_password_cb cb, void* arg);

WOLFSSL_API int wolfSSL_PEM_write_bio_DSAPrivateKey(WOLFSSL_BIO* bio, DSA* rsa,
	                                  const EVP_CIPHER* cipher,
	                                  unsigned char* passwd, int len,
	                                  pem_password_cb cb, void* arg);

WOLFSSL_API WOLFSSL_EVP_PKEY* wolfSSL_PEM_read_bio_PrivateKey(WOLFSSL_BIO* bio,
                        WOLFSSL_EVP_PKEY**, pem_password_cb cb, void* arg); 

#define PEM_write_bio_RSAPrivateKey wolfSSL_PEM_write_bio_RSAPrivateKey
#define PEM_write_bio_DSAPrivateKey wolfSSL_PEM_write_bio_DSAPrivateKey
#define PEM_read_bio_PrivateKey     wolfSSL_PEM_read_bio_PrivateKey


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* WOLFSSL_PEM_H_ */

