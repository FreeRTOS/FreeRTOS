/* sha.h for openssl */


#ifndef CYASSL_SHA_H_
#define CYASSL_SHA_H_

#include <cyassl/ctaocrypt/settings.h>

#ifdef YASSL_PREFIX
#include "prefix_sha.h"
#endif

#ifdef __cplusplus
    extern "C" {
#endif


typedef struct CYASSL_SHA_CTX {
    int holder[24];   /* big enough to hold ctaocrypt sha, but check on init */
} CYASSL_SHA_CTX;

CYASSL_API void CyaSSL_SHA_Init(CYASSL_SHA_CTX*);
CYASSL_API void CyaSSL_SHA_Update(CYASSL_SHA_CTX*, const void*, unsigned long);
CYASSL_API void CyaSSL_SHA_Final(unsigned char*, CYASSL_SHA_CTX*);

/* SHA1 points to above, shouldn't use SHA0 ever */
CYASSL_API void CyaSSL_SHA1_Init(CYASSL_SHA_CTX*);
CYASSL_API void CyaSSL_SHA1_Update(CYASSL_SHA_CTX*, const void*, unsigned long);
CYASSL_API void CyaSSL_SHA1_Final(unsigned char*, CYASSL_SHA_CTX*);

enum {
    SHA_DIGEST_LENGTH = 20
};


typedef CYASSL_SHA_CTX SHA_CTX;

#define SHA_Init CyaSSL_SHA_Init
#define SHA_Update CyaSSL_SHA_Update
#define SHA_Final CyaSSL_SHA_Final

#define SHA1_Init CyaSSL_SHA1_Init
#define SHA1_Update CyaSSL_SHA1_Update
#define SHA1_Final CyaSSL_SHA1_Final


typedef struct CYASSL_SHA256_CTX {
    int holder[28];   /* big enough to hold ctaocrypt sha, but check on init */
} CYASSL_SHA256_CTX;

CYASSL_API void CyaSSL_SHA256_Init(CYASSL_SHA256_CTX*);
CYASSL_API void CyaSSL_SHA256_Update(CYASSL_SHA256_CTX*, const void*,
	                                 unsigned long);
CYASSL_API void CyaSSL_SHA256_Final(unsigned char*, CYASSL_SHA256_CTX*);

enum {
    SHA256_DIGEST_LENGTH = 20
};


typedef CYASSL_SHA256_CTX SHA256_CTX;

#define SHA256_Init   CyaSSL_SHA256_Init
#define SHA256_Update CyaSSL_SHA256_Update
#define SHA256_Final  CyaSSL_SHA256_Final


#ifdef CYASSL_SHA384

typedef struct CYASSL_SHA384_CTX {
    long long holder[32];   /* big enough, but check on init */
} CYASSL_SHA384_CTX;

CYASSL_API void CyaSSL_SHA384_Init(CYASSL_SHA384_CTX*);
CYASSL_API void CyaSSL_SHA384_Update(CYASSL_SHA384_CTX*, const void*,
	                                 unsigned long);
CYASSL_API void CyaSSL_SHA384_Final(unsigned char*, CYASSL_SHA384_CTX*);

enum {
    SHA384_DIGEST_LENGTH = 48 
};


typedef CYASSL_SHA384_CTX SHA384_CTX;

#define SHA384_Init   CyaSSL_SHA384_Init
#define SHA384_Update CyaSSL_SHA384_Update
#define SHA384_Final  CyaSSL_SHA384_Final

#endif /* CYASSL_SHA384 */

#ifdef CYASSL_SHA512

typedef struct CYASSL_SHA512_CTX {
    long long holder[36];   /* big enough, but check on init */
} CYASSL_SHA512_CTX;

CYASSL_API void CyaSSL_SHA512_Init(CYASSL_SHA512_CTX*);
CYASSL_API void CyaSSL_SHA512_Update(CYASSL_SHA512_CTX*, const void*,
	                                 unsigned long);
CYASSL_API void CyaSSL_SHA512_Final(unsigned char*, CYASSL_SHA512_CTX*);

enum {
    SHA512_DIGEST_LENGTH = 64 
};


typedef CYASSL_SHA512_CTX SHA512_CTX;

#define SHA512_Init   CyaSSL_SHA512_Init
#define SHA512_Update CyaSSL_SHA512_Update
#define SHA512_Final  CyaSSL_SHA512_Final

#endif /* CYASSL_SHA512 */




#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* CYASSL_SHA_H_ */

