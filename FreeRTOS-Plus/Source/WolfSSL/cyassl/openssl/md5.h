/* md5.h for openssl */


#ifndef CYASSL_MD5_H_
#define CYASSL_MD5_H_

#include <cyassl/ctaocrypt/settings.h>

#ifdef YASSL_PREFIX
#include "prefix_md5.h"
#endif

#ifdef __cplusplus
    extern "C" {
#endif


typedef struct CYASSL_MD5_CTX {
    int holder[24];   /* big enough to hold ctaocrypt md5, but check on init */
} CYASSL_MD5_CTX;

CYASSL_API void CyaSSL_MD5_Init(CYASSL_MD5_CTX*);
CYASSL_API void CyaSSL_MD5_Update(CYASSL_MD5_CTX*, const void*, unsigned long);
CYASSL_API void CyaSSL_MD5_Final(unsigned char*, CYASSL_MD5_CTX*);


typedef CYASSL_MD5_CTX MD5_CTX;

#define MD5_Init CyaSSL_MD5_Init
#define MD5_Update CyaSSL_MD5_Update
#define MD5_Final CyaSSL_MD5_Final

#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* CYASSL_MD5_H_ */

