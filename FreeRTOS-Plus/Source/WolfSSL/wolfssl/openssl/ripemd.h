/* ripemd.h for openssl */


#ifndef WOLFSSL_RIPEMD_H_
#define WOLFSSL_RIPEMD_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifdef __cplusplus
    extern "C" {
#endif


typedef struct WOLFSSL_RIPEMD_CTX {
    int holder[32];   /* big enough to hold wolfcrypt, but check on init */
} WOLFSSL_RIPEMD_CTX;

WOLFSSL_API void wolfSSL_RIPEMD_Init(WOLFSSL_RIPEMD_CTX*);
WOLFSSL_API void wolfSSL_RIPEMD_Update(WOLFSSL_RIPEMD_CTX*, const void*,
                                     unsigned long);
WOLFSSL_API void wolfSSL_RIPEMD_Final(unsigned char*, WOLFSSL_RIPEMD_CTX*);


typedef WOLFSSL_RIPEMD_CTX RIPEMD_CTX;

#define RIPEMD_Init   wolfSSL_RIPEMD_Init
#define RIPEMD_Update wolfSSL_RIPEMD_Update
#define RIPEMD_Final  wolfSSL_RIPEMD_Final


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* WOLFSSL_MD5_H_ */

