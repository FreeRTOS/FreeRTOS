/* bn.h for openssl */


#ifndef WOLFSSL_BN_H_
#define WOLFSSL_BN_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifdef __cplusplus
    extern "C" {
#endif

typedef struct WOLFSSL_BIGNUM {
    int   neg;              /* openssh deference */
    void* internal;         /* our big num */
} WOLFSSL_BIGNUM;


typedef struct WOLFSSL_BN_CTX WOLFSSL_BN_CTX;


WOLFSSL_API WOLFSSL_BN_CTX* wolfSSL_BN_CTX_new(void);
WOLFSSL_API void           wolfSSL_BN_CTX_init(WOLFSSL_BN_CTX*);
WOLFSSL_API void           wolfSSL_BN_CTX_free(WOLFSSL_BN_CTX*);

WOLFSSL_API WOLFSSL_BIGNUM* wolfSSL_BN_new(void);
WOLFSSL_API void           wolfSSL_BN_free(WOLFSSL_BIGNUM*);
WOLFSSL_API void           wolfSSL_BN_clear_free(WOLFSSL_BIGNUM*);


WOLFSSL_API int wolfSSL_BN_sub(WOLFSSL_BIGNUM*, const WOLFSSL_BIGNUM*,
	                         const WOLFSSL_BIGNUM*);
WOLFSSL_API int wolfSSL_BN_mod(WOLFSSL_BIGNUM*, const WOLFSSL_BIGNUM*,
	                         const WOLFSSL_BIGNUM*, const WOLFSSL_BN_CTX*);

WOLFSSL_API const WOLFSSL_BIGNUM* wolfSSL_BN_value_one(void);


WOLFSSL_API int wolfSSL_BN_num_bytes(const WOLFSSL_BIGNUM*);
WOLFSSL_API int wolfSSL_BN_num_bits(const WOLFSSL_BIGNUM*);

WOLFSSL_API int wolfSSL_BN_is_zero(const WOLFSSL_BIGNUM*);
WOLFSSL_API int wolfSSL_BN_is_one(const WOLFSSL_BIGNUM*);
WOLFSSL_API int wolfSSL_BN_is_odd(const WOLFSSL_BIGNUM*);

WOLFSSL_API int wolfSSL_BN_cmp(const WOLFSSL_BIGNUM*, const WOLFSSL_BIGNUM*);

WOLFSSL_API int wolfSSL_BN_bn2bin(const WOLFSSL_BIGNUM*, unsigned char*);
WOLFSSL_API WOLFSSL_BIGNUM* wolfSSL_BN_bin2bn(const unsigned char*, int len,
	                            WOLFSSL_BIGNUM* ret);

WOLFSSL_API int wolfSSL_mask_bits(WOLFSSL_BIGNUM*, int n);

WOLFSSL_API int wolfSSL_BN_rand(WOLFSSL_BIGNUM*, int bits, int top, int bottom);
WOLFSSL_API int wolfSSL_BN_is_bit_set(const WOLFSSL_BIGNUM*, int n);
WOLFSSL_API int wolfSSL_BN_hex2bn(WOLFSSL_BIGNUM**, const char* str);

WOLFSSL_API WOLFSSL_BIGNUM* wolfSSL_BN_dup(const WOLFSSL_BIGNUM*);
WOLFSSL_API WOLFSSL_BIGNUM* wolfSSL_BN_copy(WOLFSSL_BIGNUM*, const WOLFSSL_BIGNUM*);

WOLFSSL_API int wolfSSL_BN_set_word(WOLFSSL_BIGNUM*, unsigned long w);

WOLFSSL_API int   wolfSSL_BN_dec2bn(WOLFSSL_BIGNUM**, const char* str);
WOLFSSL_API char* wolfSSL_BN_bn2dec(const WOLFSSL_BIGNUM*);


typedef WOLFSSL_BIGNUM BIGNUM;
typedef WOLFSSL_BN_CTX BN_CTX;

#define BN_CTX_new        wolfSSL_BN_CTX_new
#define BN_CTX_init       wolfSSL_BN_CTX_init
#define BN_CTX_free       wolfSSL_BN_CTX_free

#define BN_new        wolfSSL_BN_new
#define BN_free       wolfSSL_BN_free
#define BN_clear_free wolfSSL_BN_clear_free

#define BN_num_bytes wolfSSL_BN_num_bytes
#define BN_num_bits  wolfSSL_BN_num_bits

#define BN_is_zero  wolfSSL_BN_is_zero
#define BN_is_one   wolfSSL_BN_is_one
#define BN_is_odd   wolfSSL_BN_is_odd

#define BN_cmp    wolfSSL_BN_cmp

#define BN_bn2bin  wolfSSL_BN_bn2bin
#define BN_bin2bn  wolfSSL_BN_bin2bn

#define BN_mod       wolfSSL_BN_mod
#define BN_sub       wolfSSL_BN_sub
#define BN_value_one wolfSSL_BN_value_one

#define BN_mask_bits wolfSSL_mask_bits

#define BN_rand       wolfSSL_BN_rand
#define BN_is_bit_set wolfSSL_BN_is_bit_set
#define BN_hex2bn     wolfSSL_BN_hex2bn

#define BN_dup  wolfSSL_BN_dup
#define BN_copy wolfSSL_BN_copy

#define BN_set_word wolfSSL_BN_set_word

#define BN_dec2bn wolfSSL_BN_dec2bn
#define BN_bn2dec wolfSSL_BN_bn2dec


#ifdef __cplusplus
    }  /* extern "C" */ 
#endif


#endif /* WOLFSSL__H_ */

