/* sha.h for openssl */


#ifndef WOLFSSL_SHA_H_
#define WOLFSSL_SHA_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_PREFIX
#include "prefix_sha.h"
#endif

#ifdef __cplusplus
    extern "C" {
#endif


typedef struct WOLFSSL_SHA_CTX {
    int holder[24];   /* big enough to hold wolfcrypt sha, but check on init */
} WOLFSSL_SHA_CTX;

WOLFSSL_API void wolfSSL_SHA_Init(WOLFSSL_SHA_CTX*);
WOLFSSL_API void wolfSSL_SHA_Update(WOLFSSL_SHA_CTX*, const void*, unsigned long);
WOLFSSL_API void wolfSSL_SHA_Final(unsigned char*, WOLFSSL_SHA_CTX*);

/* SHA1 points to above, shouldn't use SHA0 ever */
WOLFSSL_API void wolfSSL_SHA1_Init(WOLFSSL_SHA_CTX*);
WOLFSSL_API void wolfSSL_SHA1_Update(WOLFSSL_SHA_CTX*, const void*, unsigned long);
WOLFSSL_API void wolfSSL_SHA1_Final(unsigned char*, WOLFSSL_SHA_CTX*);

enum {
    SHA_DIGEST_LENGTH = 20
};


typedef WOLFSSL_SHA_CTX SHA_CTX;

#define SHA_Init wolfSSL_SHA_Init
#define SHA_Update wolfSSL_SHA_Update
#define SHA_Final wolfSSL_SHA_Final

#define SHA1_Init wolfSSL_SHA1_Init
#define SHA1_Update wolfSSL_SHA1_Update
#define SHA1_Final wolfSSL_SHA1_Final


typedef struct WOLFSSL_SHA256_CTX {
    int holder[28];   /* big enough to hold wolfcrypt sha, but check on init */
} WOLFSSL_SHA256_CTX;

WOLFSSL_API void wolfSSL_SHA256_Init(WOLFSSL_SHA256_CTX*);
WOLFSSL_API void wolfSSL_SHA256_Update(WOLFSSL_SHA256_CTX*, const void*,
	                                 unsigned long);
WOLFSSL_API void wolfSSL_SHA256_Final(unsigned char*, WOLFSSL_SHA256_CTX*);

enum {
    SHA256_DIGEST_LENGTH = 32 
};


typedef WOLFSSL_SHA256_CTX SHA256_CTX;

#define SHA256_Init   wolfSSL_SHA256_Init
#define SHA256_Update wolfSSL_SHA256_Update
#define SHA256_Final  wolfSSL_SHA256_Final


#ifdef WOLFSSL_SHA384

typedef struct WOLFSSL_SHA384_CTX {
    long long holder[32];   /* big enough, but check on init */
} WOLFSSL_SHA384_CTX;

WOLFSSL_API void wolfSSL_SHA384_Init(WOLFSSL_SHA384_CTX*);
WOLFSSL_API void wolfSSL_SHA384_Update(WOLFSSL_SHA384_CTX*, const void*,
	                                 unsigned long);
WOLFSSL_API void wolfSSL_SHA384_Final(unsigned char*, WOLFSSL_SHA384_CTX*);

enum {
    SHA384_DIGEST_LENGTH = 48 
};


typedef WOLFSSL_SHA384_CTX SHA384_CTX;

#define SHA384_Init   wolfSSL_SHA384_Init
#define SHA384_Update wolfSSL_SHA384_Update
#define SHA384_Final  wolfSSL_SHA384_Final

#endif /* WOLFSSL_SHA384 */

#ifdef WOLFSSL_SHA512

typedef struct WOLFSSL_SHA512_CTX {
    long long holder[36];   /* big enough, but check on init */
} WOLFSSL_SHA512_CTX;

WOLFSSL_API void wolfSSL_SHA512_Init(WOLFSSL_SHA512_CTX*);
WOLFSSL_API void wolfSSL_SHA512_Update(WOLFSSL_SHA512_CTX*, const void*,
	                                 unsigned long);
WOLFSSL_API void wolfSSL_SHA512_Final(unsigned char*, WOLFSSL_SHA512_CTX*);

enum {
    SHA512_DIGEST_LENGTH = 64 
};


typedef WOLFSSL_SHA512_CTX SHA512_CTX;

#define SHA512_Init   wolfSSL_SHA512_Init
#define SHA512_Update wolfSSL_SHA512_Update
#define SHA512_Final  wolfSSL_SHA512_Final

#endif /* WOLFSSL_SHA512 */




#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* WOLFSSL_SHA_H_ */

