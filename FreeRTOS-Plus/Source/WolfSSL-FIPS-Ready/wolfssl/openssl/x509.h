/* x509.h for openssl */

#include <wolfssl/openssl/ssl.h>
#include <wolfssl/openssl/crypto.h>
#include <wolfssl/openssl/dh.h>
#include <wolfssl/openssl/ec.h>
#include <wolfssl/openssl/ecdsa.h>

/* wolfSSL_X509_print_ex flags */
#define X509_FLAG_COMPAT        (0UL)
#define X509_FLAG_NO_HEADER     (1UL << 0)
#define X509_FLAG_NO_VERSION    (1UL << 1)
#define X509_FLAG_NO_SERIAL     (1UL << 2)
#define X509_FLAG_NO_SIGNAME    (1UL << 3)
#define X509_FLAG_NO_ISSUER     (1UL << 4)
#define X509_FLAG_NO_VALIDITY   (1UL << 5)
#define X509_FLAG_NO_SUBJECT    (1UL << 6)
#define X509_FLAG_NO_PUBKEY     (1UL << 7)
#define X509_FLAG_NO_EXTENSIONS (1UL << 8)
#define X509_FLAG_NO_SIGDUMP    (1UL << 9)
#define X509_FLAG_NO_AUX        (1UL << 10)
#define X509_FLAG_NO_ATTRIBUTES (1UL << 11)
#define X509_FLAG_NO_IDS        (1UL << 12)

#define XN_FLAG_FN_SN           0
#define XN_FLAG_SEP_CPLUS_SPC   2
