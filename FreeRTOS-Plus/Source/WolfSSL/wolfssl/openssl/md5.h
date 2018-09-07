/* md5.h for openssl */


#ifndef WOLFSSL_MD5_H_
#define WOLFSSL_MD5_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_MD5

#ifdef WOLFSSL_PREFIX
#include "prefix_md5.h"
#endif

#ifdef __cplusplus
    extern "C" {
#endif


typedef struct WOLFSSL_MD5_CTX {
    int holder[24];   /* big enough to hold wolfcrypt md5, but check on init */
} WOLFSSL_MD5_CTX;

WOLFSSL_API void wolfSSL_MD5_Init(WOLFSSL_MD5_CTX*);
WOLFSSL_API void wolfSSL_MD5_Update(WOLFSSL_MD5_CTX*, const void*, unsigned long);
WOLFSSL_API void wolfSSL_MD5_Final(unsigned char*, WOLFSSL_MD5_CTX*);


typedef WOLFSSL_MD5_CTX MD5_CTX;

#define MD5_Init wolfSSL_MD5_Init
#define MD5_Update wolfSSL_MD5_Update
#define MD5_Final wolfSSL_MD5_Final

#ifdef __cplusplus
    }  /* extern "C" */ 
#endif

#endif /* NO_MD5 */

#endif /* WOLFSSL_MD5_H_ */

