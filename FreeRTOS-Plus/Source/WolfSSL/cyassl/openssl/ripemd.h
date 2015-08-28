/* ripemd.h for openssl */


#ifndef CYASSL_RIPEMD_H_
#define CYASSL_RIPEMD_H_

#include <cyassl/ctaocrypt/settings.h>

#ifdef __cplusplus
    extern "C" {
#endif


typedef struct CYASSL_RIPEMD_CTX {
    int holder[32];   /* big enough to hold ctaocrypt, but check on init */
} CYASSL_RIPEMD_CTX;

CYASSL_API void CyaSSL_RIPEMD_Init(CYASSL_RIPEMD_CTX*);
CYASSL_API void CyaSSL_RIPEMD_Update(CYASSL_RIPEMD_CTX*, const void*,
                                     unsigned long);
CYASSL_API void CyaSSL_RIPEMD_Final(unsigned char*, CYASSL_RIPEMD_CTX*);


typedef CYASSL_RIPEMD_CTX RIPEMD_CTX;

#define RIPEMD_Init   CyaSSL_RIPEMD_Init
#define RIPEMD_Update CyaSSL_RIPEMD_Update
#define RIPEMD_Final  CyaSSL_RIPEMD_Final


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* CYASSL_MD5_H_ */

