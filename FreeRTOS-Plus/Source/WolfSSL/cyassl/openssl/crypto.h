/* crypto.h for openSSL */

#ifndef CYASSL_CRYPTO_H_
#define CYASSL_CRYPTO_H_


#include <cyassl/ctaocrypt/settings.h>

#ifdef YASSL_PREFIX
#include "prefix_crypto.h"
#endif


CYASSL_API const char*   CyaSSLeay_version(int type);
CYASSL_API unsigned long CyaSSLeay(void);

#define SSLeay_version CyaSSLeay_version
#define SSLeay CyaSSLeay


#define SSLEAY_VERSION 0x0090600fL
#define SSLEAY_VERSION_NUMBER SSLEAY_VERSION


#endif /* header */

