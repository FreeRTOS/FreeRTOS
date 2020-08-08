/* dsa.h for openSSL */

#ifndef CYASSL_OPENSSL_DSA
#define CYASSL_OPENSSL_DSA

#define CyaSSL_DSA_LoadDer  wolfSSL_DSA_LoadDer
#define CyaSSL_DSA_do_sign  wolfSSL_DSA_do_sign

#include <cyassl/openssl/ssl.h>
#include <wolfssl/openssl/dsa.h>
#endif

