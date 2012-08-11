/* pem.h for openssl */


#ifndef CYASSL_PEM_H_
#define CYASSL_PEM_H_

#include <cyassl/openssl/evp.h>
#include <cyassl/openssl/bio.h>
#include <cyassl/openssl/rsa.h>
#include <cyassl/openssl/dsa.h>

#ifdef __cplusplus
    extern "C" {
#endif


CYASSL_API int CyaSSL_PEM_write_bio_RSAPrivateKey(CYASSL_BIO* bio, RSA* rsa,
	                                  const EVP_CIPHER* cipher,
	                                  unsigned char* passwd, int len,
	                                  pem_password_cb cb, void* arg);

CYASSL_API int CyaSSL_PEM_write_bio_DSAPrivateKey(CYASSL_BIO* bio, DSA* rsa,
	                                  const EVP_CIPHER* cipher,
	                                  unsigned char* passwd, int len,
	                                  pem_password_cb cb, void* arg);

CYASSL_API CYASSL_EVP_PKEY* CyaSSL_PEM_read_bio_PrivateKey(CYASSL_BIO* bio,
                        CYASSL_EVP_PKEY**, pem_password_cb cb, void* arg); 

#define PEM_write_bio_RSAPrivateKey CyaSSL_PEM_write_bio_RSAPrivateKey
#define PEM_write_bio_DSAPrivateKey CyaSSL_PEM_write_bio_DSAPrivateKey
#define PEM_read_bio_PrivateKey     CyaSSL_PEM_read_bio_PrivateKey


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* CYASSL_PEM_H_ */

