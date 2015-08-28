/* keys.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

/* Name change compatibility layer no longer needs to be included here */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#include <wolfssl/internal.h>
#include <wolfssl/error-ssl.h>
#if defined(SHOW_SECRETS) || defined(CHACHA_AEAD_TEST)
    #ifdef FREESCALE_MQX
        #include <fio.h>
    #else
        #include <stdio.h>
    #endif
#endif


int SetCipherSpecs(WOLFSSL* ssl)
{
#ifndef NO_WOLFSSL_CLIENT
    if (ssl->options.side == WOLFSSL_CLIENT_END) {
        /* server side verified before SetCipherSpecs call */
        if (VerifyClientSuite(ssl) != 1) {
            WOLFSSL_MSG("SetCipherSpecs() client has an unusuable suite");
            return UNSUPPORTED_SUITE;
        }
    }
#endif /* NO_WOLFSSL_CLIENT */

    /* Chacha extensions, 0xcc */
    if (ssl->options.cipherSuite0 == CHACHA_BYTE) {
    
    switch (ssl->options.cipherSuite) {
#ifdef BUILD_TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
    case TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256:
        ssl->specs.bulk_cipher_algorithm = wolfssl_chacha;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CHACHA20_256_KEY_SIZE;
        ssl->specs.block_size            = CHACHA20_BLOCK_SIZE;
        ssl->specs.iv_size               = CHACHA20_IV_SIZE;
        ssl->specs.aead_mac_size         = POLY1305_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256
    case TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256:
        ssl->specs.bulk_cipher_algorithm = wolfssl_chacha;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CHACHA20_256_KEY_SIZE;
        ssl->specs.block_size            = CHACHA20_BLOCK_SIZE;
        ssl->specs.iv_size               = CHACHA20_IV_SIZE;
        ssl->specs.aead_mac_size         = POLY1305_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256
    case TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256:
        ssl->specs.bulk_cipher_algorithm = wolfssl_chacha;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CHACHA20_256_KEY_SIZE;
        ssl->specs.block_size            = CHACHA20_BLOCK_SIZE;
        ssl->specs.iv_size               = CHACHA20_IV_SIZE;
        ssl->specs.aead_mac_size         = POLY1305_AUTH_SZ;

        break;
#endif
    default:
        WOLFSSL_MSG("Unsupported cipher suite, SetCipherSpecs ChaCha");
        return UNSUPPORTED_SUITE;
    }
    }

    /* ECC extensions, or AES-CCM */
    if (ssl->options.cipherSuite0 == ECC_BYTE) {
    
    switch (ssl->options.cipherSuite) {

#ifdef HAVE_ECC

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256
    case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256
    case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256
    case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384
    case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384
    case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384
    case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
    case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
    break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
    case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
    case TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_triple_des;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = DES3_KEY_SIZE;
        ssl->specs.block_size            = DES_BLOCK_SIZE;
        ssl->specs.iv_size               = DES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
    case TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_triple_des;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = DES3_KEY_SIZE;
        ssl->specs.block_size            = DES_BLOCK_SIZE;
        ssl->specs.iv_size               = DES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
    case TLS_ECDHE_RSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
    case TLS_ECDH_RSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
    case TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_triple_des;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = DES3_KEY_SIZE;
        ssl->specs.block_size            = DES_BLOCK_SIZE;
        ssl->specs.iv_size               = DES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
    case TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_triple_des;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = DES3_KEY_SIZE;
        ssl->specs.block_size            = DES_BLOCK_SIZE;
        ssl->specs.iv_size               = DES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
    case TLS_ECDHE_ECDSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
    case TLS_ECDH_ECDSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
    case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
    case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
    case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA
    case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
    case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    case TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
    case TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
    case TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
    case TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256
    case TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384
    case TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256
    case TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384
    case TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 1;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8
    case TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_8_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8
    case TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = ecc_diffie_hellman_kea;
        ssl->specs.sig_algo              = ecc_dsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_8_AUTH_SZ;

        break;
#endif
#endif /* HAVE_ECC */

#ifdef BUILD_TLS_RSA_WITH_AES_128_CCM_8
    case TLS_RSA_WITH_AES_128_CCM_8 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_8_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CCM_8
    case TLS_RSA_WITH_AES_256_CCM_8 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_8_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM_8
    case TLS_PSK_WITH_AES_128_CCM_8 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_8_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM_8
    case TLS_PSK_WITH_AES_256_CCM_8 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_8_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM
    case TLS_PSK_WITH_AES_128_CCM :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_16_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM
    case TLS_PSK_WITH_AES_256_CCM :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_16_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CCM
    case TLS_DHE_PSK_WITH_AES_128_CCM :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_16_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CCM
    case TLS_DHE_PSK_WITH_AES_256_CCM :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_ccm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_CCM_16_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

    default:
        WOLFSSL_MSG("Unsupported cipher suite, SetCipherSpecs ECC");
        return UNSUPPORTED_SUITE;
    }   /* switch */
    }   /* if     */
    if (ssl->options.cipherSuite0 != ECC_BYTE && 
            ssl->options.cipherSuite0 != CHACHA_BYTE) {   /* normal suites */
    switch (ssl->options.cipherSuite) {

#ifdef BUILD_SSL_RSA_WITH_RC4_128_SHA
    case SSL_RSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
    case TLS_NTRU_RSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ntru_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_SSL_RSA_WITH_RC4_128_MD5
    case SSL_RSA_WITH_RC4_128_MD5 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rc4;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = md5_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = MD5_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_MD5;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = RC4_KEY_SIZE;
        ssl->specs.iv_size               = 0;
        ssl->specs.block_size            = 0;

        break;
#endif

#ifdef BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
    case SSL_RSA_WITH_3DES_EDE_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_triple_des;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = DES3_KEY_SIZE;
        ssl->specs.block_size            = DES_BLOCK_SIZE;
        ssl->specs.iv_size               = DES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
    case TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_triple_des;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ntru_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = DES3_KEY_SIZE;
        ssl->specs.block_size            = DES_BLOCK_SIZE;
        ssl->specs.iv_size               = DES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
    case TLS_RSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
    case TLS_RSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA
    case TLS_RSA_WITH_NULL_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA256
    case TLS_RSA_WITH_NULL_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        break;
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
    case TLS_NTRU_RSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ntru_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
    case TLS_RSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
    case TLS_RSA_WITH_AES_256_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
    case TLS_NTRU_RSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = ntru_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256
    case TLS_PSK_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384
    case TLS_PSK_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256
    case TLS_DHE_PSK_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384
    case TLS_DHE_PSK_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA256
    case TLS_PSK_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA384
    case TLS_PSK_WITH_AES_256_CBC_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256
    case TLS_DHE_PSK_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CBC_SHA384
    case TLS_DHE_PSK_WITH_AES_256_CBC_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    case TLS_PSK_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    case TLS_PSK_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA256
    case TLS_PSK_WITH_NULL_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA384
    case TLS_PSK_WITH_NULL_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA
    case TLS_PSK_WITH_NULL_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA256
    case TLS_DHE_PSK_WITH_NULL_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA384
    case TLS_DHE_PSK_WITH_NULL_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_cipher_null;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = dhe_psk_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = 0;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = 0;

        ssl->options.usingPSK_cipher     = 1;
        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    case TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
    case TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    case TLS_DHE_RSA_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    case TLS_DHE_RSA_WITH_AES_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_MD5
    case TLS_RSA_WITH_HC_128_MD5 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_hc128;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = md5_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = MD5_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_MD5;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = HC_128_KEY_SIZE;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = HC_128_IV_SIZE;

        break;
#endif
            
#ifdef BUILD_TLS_RSA_WITH_HC_128_SHA
        case TLS_RSA_WITH_HC_128_SHA :
            ssl->specs.bulk_cipher_algorithm = wolfssl_hc128;
            ssl->specs.cipher_type           = stream;
            ssl->specs.mac_algorithm         = sha_mac;
            ssl->specs.kea                   = rsa_kea;
            ssl->specs.sig_algo              = rsa_sa_algo;
            ssl->specs.hash_size             = SHA_DIGEST_SIZE;
            ssl->specs.pad_size              = PAD_SHA;
            ssl->specs.static_ecdh           = 0;
            ssl->specs.key_size              = HC_128_KEY_SIZE;
            ssl->specs.block_size            = 0;
            ssl->specs.iv_size               = HC_128_IV_SIZE;
            
            break;
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_B2B256
        case TLS_RSA_WITH_HC_128_B2B256:
            ssl->specs.bulk_cipher_algorithm = wolfssl_hc128;
            ssl->specs.cipher_type           = stream;
            ssl->specs.mac_algorithm         = blake2b_mac;
            ssl->specs.kea                   = rsa_kea;
            ssl->specs.sig_algo              = rsa_sa_algo;
            ssl->specs.hash_size             = BLAKE2B_256;
            ssl->specs.pad_size              = PAD_SHA;
            ssl->specs.static_ecdh           = 0;
            ssl->specs.key_size              = HC_128_KEY_SIZE;
            ssl->specs.block_size            = 0;
            ssl->specs.iv_size               = HC_128_IV_SIZE;
            
            break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_B2B256
        case TLS_RSA_WITH_AES_128_CBC_B2B256:
            ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
            ssl->specs.cipher_type           = block;
            ssl->specs.mac_algorithm         = blake2b_mac;
            ssl->specs.kea                   = rsa_kea;
            ssl->specs.sig_algo              = rsa_sa_algo;
            ssl->specs.hash_size             = BLAKE2B_256;
            ssl->specs.pad_size              = PAD_SHA;
            ssl->specs.static_ecdh           = 0;
            ssl->specs.key_size              = AES_128_KEY_SIZE;
            ssl->specs.iv_size               = AES_IV_SIZE;
            ssl->specs.block_size            = AES_BLOCK_SIZE;
            
            break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_B2B256
        case TLS_RSA_WITH_AES_256_CBC_B2B256:
            ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
            ssl->specs.cipher_type           = block;
            ssl->specs.mac_algorithm         = blake2b_mac;
            ssl->specs.kea                   = rsa_kea;
            ssl->specs.sig_algo              = rsa_sa_algo;
            ssl->specs.hash_size             = BLAKE2B_256;
            ssl->specs.pad_size              = PAD_SHA;
            ssl->specs.static_ecdh           = 0;
            ssl->specs.key_size              = AES_256_KEY_SIZE;
            ssl->specs.iv_size               = AES_IV_SIZE;
            ssl->specs.block_size            = AES_BLOCK_SIZE;
            
            break;
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_SHA
    case TLS_RSA_WITH_RABBIT_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_rabbit;
        ssl->specs.cipher_type           = stream;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = RABBIT_KEY_SIZE;
        ssl->specs.block_size            = 0;
        ssl->specs.iv_size               = RABBIT_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256
    case TLS_RSA_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384
    case TLS_RSA_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    case TLS_DHE_RSA_WITH_AES_128_GCM_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    case TLS_DHE_RSA_WITH_AES_256_GCM_SHA384 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes_gcm;
        ssl->specs.cipher_type           = aead;
        ssl->specs.mac_algorithm         = sha384_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA384_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_256_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AEAD_IMP_IV_SZ;
        ssl->specs.aead_mac_size         = AES_GCM_AUTH_SZ;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA
    case TLS_RSA_WITH_CAMELLIA_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_128_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif
    
#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA
    case TLS_RSA_WITH_CAMELLIA_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_256_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256
    case TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_128_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256
    case TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = rsa_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_256_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA
    case TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_128_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA
    case TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_256_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256
    case TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_128_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256
    case TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = wolfssl_camellia;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha256_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = rsa_sa_algo;
        ssl->specs.hash_size             = SHA256_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = CAMELLIA_256_KEY_SIZE;
        ssl->specs.block_size            = CAMELLIA_BLOCK_SIZE;
        ssl->specs.iv_size               = CAMELLIA_IV_SIZE;

        break;
#endif

#ifdef BUILD_TLS_DH_anon_WITH_AES_128_CBC_SHA
    case TLS_DH_anon_WITH_AES_128_CBC_SHA :
        ssl->specs.bulk_cipher_algorithm = wolfssl_aes;
        ssl->specs.cipher_type           = block;
        ssl->specs.mac_algorithm         = sha_mac;
        ssl->specs.kea                   = diffie_hellman_kea;
        ssl->specs.sig_algo              = anonymous_sa_algo;
        ssl->specs.hash_size             = SHA_DIGEST_SIZE;
        ssl->specs.pad_size              = PAD_SHA;
        ssl->specs.static_ecdh           = 0;
        ssl->specs.key_size              = AES_128_KEY_SIZE;
        ssl->specs.block_size            = AES_BLOCK_SIZE;
        ssl->specs.iv_size               = AES_IV_SIZE;

        ssl->options.usingAnon_cipher    = 1;
        break;
#endif

    default:
        WOLFSSL_MSG("Unsupported cipher suite, SetCipherSpecs");
        return UNSUPPORTED_SUITE;
    }  /* switch */
    }  /* if ECC / Normal suites else */

    /* set TLS if it hasn't been turned off */
    if (ssl->version.major == 3 && ssl->version.minor >= 1) {
#ifndef NO_TLS
        ssl->options.tls = 1;
        ssl->hmac = TLS_hmac;
        if (ssl->version.minor >= 2)
            ssl->options.tls1_1 = 1;
#endif
    }

#ifdef WOLFSSL_DTLS
    if (ssl->options.dtls)
        ssl->hmac = TLS_hmac;
#endif

    return 0;
}


enum KeyStuff {
    MASTER_ROUNDS = 3,
    PREFIX        = 3,     /* up to three letters for master prefix */
    KEY_PREFIX    = 7      /* up to 7 prefix letters for key rounds */


};

#ifndef NO_OLD_TLS
/* true or false, zero for error */
static int SetPrefix(byte* sha_input, int idx)
{
    switch (idx) {
    case 0:
        XMEMCPY(sha_input, "A", 1);
        break;
    case 1:
        XMEMCPY(sha_input, "BB", 2);
        break;
    case 2:
        XMEMCPY(sha_input, "CCC", 3);
        break;
    case 3:
        XMEMCPY(sha_input, "DDDD", 4);
        break;
    case 4:
        XMEMCPY(sha_input, "EEEEE", 5);
        break;
    case 5:
        XMEMCPY(sha_input, "FFFFFF", 6);
        break;
    case 6:
        XMEMCPY(sha_input, "GGGGGGG", 7);
        break;
    default:
        WOLFSSL_MSG("Set Prefix error, bad input");
        return 0; 
    }
    return 1;
}
#endif


static int SetKeys(Ciphers* enc, Ciphers* dec, Keys* keys, CipherSpecs* specs,
                   int side, void* heap, int devId)
{
#ifdef BUILD_ARC4
    word32 sz = specs->key_size;
    if (specs->bulk_cipher_algorithm == wolfssl_rc4) {
        if (enc && enc->arc4 == NULL)
            enc->arc4 = (Arc4*)XMALLOC(sizeof(Arc4), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->arc4 == NULL)
            return MEMORY_E;
        if (dec && dec->arc4 == NULL)
            dec->arc4 = (Arc4*)XMALLOC(sizeof(Arc4), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->arc4 == NULL)
            return MEMORY_E;
#ifdef HAVE_CAVIUM
        if (devId != NO_CAVIUM_DEVICE) {
            if (enc) {
                if (Arc4InitCavium(enc->arc4, devId) != 0) {
                    WOLFSSL_MSG("Arc4InitCavium failed in SetKeys");
                    return CAVIUM_INIT_E;
                }
            }
            if (dec) {
                if (Arc4InitCavium(dec->arc4, devId) != 0) {
                    WOLFSSL_MSG("Arc4InitCavium failed in SetKeys");
                    return CAVIUM_INIT_E;
                }
            }
        }
#endif
        if (side == WOLFSSL_CLIENT_END) {
            if (enc)
                wc_Arc4SetKey(enc->arc4, keys->client_write_key, sz);
            if (dec)
                wc_Arc4SetKey(dec->arc4, keys->server_write_key, sz);
        }
        else {
            if (enc)
                wc_Arc4SetKey(enc->arc4, keys->server_write_key, sz);
            if (dec)
                wc_Arc4SetKey(dec->arc4, keys->client_write_key, sz);
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

    
#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
    if (specs->bulk_cipher_algorithm == wolfssl_chacha) {
        int chachaRet;
        if (enc && enc->chacha == NULL)
            enc->chacha =
                    (ChaCha*)XMALLOC(sizeof(ChaCha), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->chacha == NULL)
            return MEMORY_E;
        if (dec && dec->chacha == NULL)
            dec->chacha =
                    (ChaCha*)XMALLOC(sizeof(ChaCha), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->chacha == NULL)
            return MEMORY_E;
        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                chachaRet = wc_Chacha_SetKey(enc->chacha, keys->client_write_key,
                                          specs->key_size);
                XMEMCPY(keys->aead_enc_imp_IV, keys->client_write_IV,
                        AEAD_IMP_IV_SZ);
                if (chachaRet != 0) return chachaRet;
            }
            if (dec) {
                chachaRet = wc_Chacha_SetKey(dec->chacha, keys->server_write_key,
                                          specs->key_size);
                XMEMCPY(keys->aead_dec_imp_IV, keys->server_write_IV,
                        AEAD_IMP_IV_SZ);
                if (chachaRet != 0) return chachaRet;
            }
        }
        else {
            if (enc) {
                chachaRet = wc_Chacha_SetKey(enc->chacha, keys->server_write_key,
                                          specs->key_size);
                XMEMCPY(keys->aead_enc_imp_IV, keys->server_write_IV,
                        AEAD_IMP_IV_SZ);
                if (chachaRet != 0) return chachaRet;
            }
            if (dec) {
                chachaRet = wc_Chacha_SetKey(dec->chacha, keys->client_write_key,
                                          specs->key_size);
                XMEMCPY(keys->aead_dec_imp_IV, keys->client_write_IV,
                        AEAD_IMP_IV_SZ);
                if (chachaRet != 0) return chachaRet;
            }
        }

        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

#ifdef HAVE_HC128
    if (specs->bulk_cipher_algorithm == wolfssl_hc128) {
        int hcRet;
        if (enc && enc->hc128 == NULL)
            enc->hc128 =
                      (HC128*)XMALLOC(sizeof(HC128), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->hc128 == NULL)
            return MEMORY_E;
        if (dec && dec->hc128 == NULL)
            dec->hc128 =
                      (HC128*)XMALLOC(sizeof(HC128), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->hc128 == NULL)
            return MEMORY_E;
        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                hcRet = wc_Hc128_SetKey(enc->hc128, keys->client_write_key,
                                     keys->client_write_IV);
                if (hcRet != 0) return hcRet;
            }
            if (dec) {
                hcRet = wc_Hc128_SetKey(dec->hc128, keys->server_write_key,
                                     keys->server_write_IV);
                if (hcRet != 0) return hcRet;
            }
        }
        else {
            if (enc) {
                hcRet = wc_Hc128_SetKey(enc->hc128, keys->server_write_key,
                                     keys->server_write_IV);
                if (hcRet != 0) return hcRet;
            }
            if (dec) {
                hcRet = wc_Hc128_SetKey(dec->hc128, keys->client_write_key,
                                     keys->client_write_IV);
                if (hcRet != 0) return hcRet;
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif
    
#ifdef BUILD_RABBIT
    if (specs->bulk_cipher_algorithm == wolfssl_rabbit) {
        int rabRet;
        if (enc && enc->rabbit == NULL)
            enc->rabbit =
                    (Rabbit*)XMALLOC(sizeof(Rabbit), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->rabbit == NULL)
            return MEMORY_E;
        if (dec && dec->rabbit == NULL)
            dec->rabbit =
                    (Rabbit*)XMALLOC(sizeof(Rabbit), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->rabbit == NULL)
            return MEMORY_E;
        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                rabRet = wc_RabbitSetKey(enc->rabbit, keys->client_write_key,
                                      keys->client_write_IV);
                if (rabRet != 0) return rabRet;
            }
            if (dec) {
                rabRet = wc_RabbitSetKey(dec->rabbit, keys->server_write_key,
                                      keys->server_write_IV);
                if (rabRet != 0) return rabRet;
            }
        }
        else {
            if (enc) {
                rabRet = wc_RabbitSetKey(enc->rabbit, keys->server_write_key,
                                      keys->server_write_IV);
                if (rabRet != 0) return rabRet;
            }
            if (dec) {
                rabRet = wc_RabbitSetKey(dec->rabbit, keys->client_write_key,
                                      keys->client_write_IV);
                if (rabRet != 0) return rabRet;
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif
    
#ifdef BUILD_DES3
    if (specs->bulk_cipher_algorithm == wolfssl_triple_des) {
        int desRet = 0;

        if (enc && enc->des3 == NULL)
            enc->des3 = (Des3*)XMALLOC(sizeof(Des3), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->des3 == NULL)
            return MEMORY_E;
        if (dec && dec->des3 == NULL)
            dec->des3 = (Des3*)XMALLOC(sizeof(Des3), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->des3 == NULL)
            return MEMORY_E;
#ifdef HAVE_CAVIUM
        if (devId != NO_CAVIUM_DEVICE) {
            if (enc) {
                if (Des3_InitCavium(enc->des3, devId) != 0) {
                    WOLFSSL_MSG("Des3_InitCavium failed in SetKeys");
                    return CAVIUM_INIT_E;
                }
            }
            if (dec) {
                if (Des3_InitCavium(dec->des3, devId) != 0) {
                    WOLFSSL_MSG("Des3_InitCavium failed in SetKeys");
                    return CAVIUM_INIT_E;
                }
            }
        }
#endif
        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                desRet = wc_Des3_SetKey(enc->des3, keys->client_write_key,
                                     keys->client_write_IV, DES_ENCRYPTION);
                if (desRet != 0) return desRet;
            }
            if (dec) {
                desRet = wc_Des3_SetKey(dec->des3, keys->server_write_key,
                                     keys->server_write_IV, DES_DECRYPTION);
                if (desRet != 0) return desRet;
            }
        }
        else {
            if (enc) {
                desRet = wc_Des3_SetKey(enc->des3, keys->server_write_key,
                                     keys->server_write_IV, DES_ENCRYPTION);
                if (desRet != 0) return desRet;
            }
            if (dec) {
                desRet = wc_Des3_SetKey(dec->des3, keys->client_write_key,
                                     keys->client_write_IV, DES_DECRYPTION);
                if (desRet != 0) return desRet;
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

#ifdef BUILD_AES
    if (specs->bulk_cipher_algorithm == wolfssl_aes) {
        int aesRet = 0;

        if (enc && enc->aes == NULL)
            enc->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->aes == NULL)
            return MEMORY_E;
        if (dec && dec->aes == NULL)
            dec->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->aes == NULL)
            return MEMORY_E;
#ifdef HAVE_CAVIUM
        if (devId != NO_CAVIUM_DEVICE) {
            if (enc) {
                if (wc_AesInitCavium(enc->aes, devId) != 0) {
                    WOLFSSL_MSG("AesInitCavium failed in SetKeys");
                    return CAVIUM_INIT_E;
                }
            }
            if (dec) {
                if (wc_AesInitCavium(dec->aes, devId) != 0) {
                    WOLFSSL_MSG("AesInitCavium failed in SetKeys");
                    return CAVIUM_INIT_E;
                }
            }
        }
#endif
        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                aesRet = wc_AesSetKey(enc->aes, keys->client_write_key,
                                   specs->key_size, keys->client_write_IV,
                                   AES_ENCRYPTION);
                if (aesRet != 0) return aesRet;
            }
            if (dec) {
                aesRet = wc_AesSetKey(dec->aes, keys->server_write_key,
                                   specs->key_size, keys->server_write_IV,
                                   AES_DECRYPTION);
                if (aesRet != 0) return aesRet;
            }
        }
        else {
            if (enc) {
                aesRet = wc_AesSetKey(enc->aes, keys->server_write_key,
                                   specs->key_size, keys->server_write_IV,
                                   AES_ENCRYPTION);
                if (aesRet != 0) return aesRet;
            }
            if (dec) {
                aesRet = wc_AesSetKey(dec->aes, keys->client_write_key,
                                   specs->key_size, keys->client_write_IV,
                                   AES_DECRYPTION);
                if (aesRet != 0) return aesRet;
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

#ifdef BUILD_AESGCM
    if (specs->bulk_cipher_algorithm == wolfssl_aes_gcm) {
        int gcmRet;

        if (enc && enc->aes == NULL)
            enc->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->aes == NULL)
            return MEMORY_E;
        if (dec && dec->aes == NULL)
            dec->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->aes == NULL)
            return MEMORY_E;

        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                gcmRet = wc_AesGcmSetKey(enc->aes, keys->client_write_key,
                                      specs->key_size);
                if (gcmRet != 0) return gcmRet;
                XMEMCPY(keys->aead_enc_imp_IV, keys->client_write_IV,
                        AEAD_IMP_IV_SZ);
            }
            if (dec) {
                gcmRet = wc_AesGcmSetKey(dec->aes, keys->server_write_key,
                                      specs->key_size);
                if (gcmRet != 0) return gcmRet;
                XMEMCPY(keys->aead_dec_imp_IV, keys->server_write_IV,
                        AEAD_IMP_IV_SZ);
            }
        }
        else {
            if (enc) {
                gcmRet = wc_AesGcmSetKey(enc->aes, keys->server_write_key,
                                      specs->key_size);
                if (gcmRet != 0) return gcmRet;
                XMEMCPY(keys->aead_enc_imp_IV, keys->server_write_IV,
                        AEAD_IMP_IV_SZ);
            }
            if (dec) {
                gcmRet = wc_AesGcmSetKey(dec->aes, keys->client_write_key,
                                      specs->key_size);
                if (gcmRet != 0) return gcmRet;
                XMEMCPY(keys->aead_dec_imp_IV, keys->client_write_IV,
                        AEAD_IMP_IV_SZ);
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

#ifdef HAVE_AESCCM
    if (specs->bulk_cipher_algorithm == wolfssl_aes_ccm) {
        if (enc && enc->aes == NULL)
            enc->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->aes == NULL)
            return MEMORY_E;
        if (dec && dec->aes == NULL)
            dec->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->aes == NULL)
            return MEMORY_E;

        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                wc_AesCcmSetKey(enc->aes, keys->client_write_key, specs->key_size);
                XMEMCPY(keys->aead_enc_imp_IV, keys->client_write_IV,
                        AEAD_IMP_IV_SZ);
            }
            if (dec) {
                wc_AesCcmSetKey(dec->aes, keys->server_write_key, specs->key_size);
                XMEMCPY(keys->aead_dec_imp_IV, keys->server_write_IV,
                        AEAD_IMP_IV_SZ);
            }
        }
        else {
            if (enc) {
                wc_AesCcmSetKey(enc->aes, keys->server_write_key, specs->key_size);
                XMEMCPY(keys->aead_enc_imp_IV, keys->server_write_IV,
                        AEAD_IMP_IV_SZ);
            }
            if (dec) {
                wc_AesCcmSetKey(dec->aes, keys->client_write_key, specs->key_size);
                XMEMCPY(keys->aead_dec_imp_IV, keys->client_write_IV,
                        AEAD_IMP_IV_SZ);
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

#ifdef HAVE_CAMELLIA
    if (specs->bulk_cipher_algorithm == wolfssl_camellia) {
        int camRet;

        if (enc && enc->cam == NULL)
            enc->cam =
                (Camellia*)XMALLOC(sizeof(Camellia), heap, DYNAMIC_TYPE_CIPHER);
        if (enc && enc->cam == NULL)
            return MEMORY_E;

        if (dec && dec->cam == NULL)
            dec->cam =
                (Camellia*)XMALLOC(sizeof(Camellia), heap, DYNAMIC_TYPE_CIPHER);
        if (dec && dec->cam == NULL)
            return MEMORY_E;

        if (side == WOLFSSL_CLIENT_END) {
            if (enc) {
                camRet = wc_CamelliaSetKey(enc->cam, keys->client_write_key,
                                        specs->key_size, keys->client_write_IV);
                if (camRet != 0) return camRet;
            }
            if (dec) {
                camRet = wc_CamelliaSetKey(dec->cam, keys->server_write_key,
                                        specs->key_size, keys->server_write_IV);
                if (camRet != 0) return camRet;
            }
        }
        else {
            if (enc) {
                camRet = wc_CamelliaSetKey(enc->cam, keys->server_write_key,
                                        specs->key_size, keys->server_write_IV);
                if (camRet != 0) return camRet;
            }
            if (dec) {
                camRet = wc_CamelliaSetKey(dec->cam, keys->client_write_key,
                                        specs->key_size, keys->client_write_IV);
                if (camRet != 0) return camRet;
            }
        }
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

#ifdef HAVE_NULL_CIPHER
    if (specs->bulk_cipher_algorithm == wolfssl_cipher_null) {
        if (enc)
            enc->setup = 1;
        if (dec)
            dec->setup = 1;
    }
#endif

    if (enc)
        keys->sequence_number      = 0;
    if (dec)
        keys->peer_sequence_number = 0;
    (void)side;
    (void)heap;
    (void)enc;
    (void)dec;
    (void)specs;
    (void)devId;

    return 0;
}


#ifdef HAVE_ONE_TIME_AUTH
/* set one time authentication keys */
static int SetAuthKeys(OneTimeAuth* authentication, Keys* keys,
                       CipherSpecs* specs, void* heap, int devId)
{

#ifdef HAVE_POLY1305
        /* set up memory space for poly1305 */
        if (authentication && authentication->poly1305 == NULL)
            authentication->poly1305 =
                (Poly1305*)XMALLOC(sizeof(Poly1305), heap, DYNAMIC_TYPE_CIPHER);
        if (authentication && authentication->poly1305 == NULL)
            return MEMORY_E;
        if (authentication)
            authentication->setup = 1;
#endif
        (void)heap;
        (void)keys;
        (void)specs;
        (void)devId;

        return 0;
}
#endif /* HAVE_ONE_TIME_AUTH */


/* Set wc_encrypt/wc_decrypt or both sides of key setup
 * note: use wc_encrypt to avoid shadowing global encrypt
 * declared in unistd.h
 */
int SetKeysSide(WOLFSSL* ssl, enum encrypt_side side)
{
    int devId = NO_CAVIUM_DEVICE, ret, copy = 0;
    Ciphers* wc_encrypt = NULL;
    Ciphers* wc_decrypt = NULL;
    Keys*    keys    = &ssl->keys;

    (void)copy;

#ifdef HAVE_CAVIUM
    devId = ssl->devId;
#endif

#ifdef HAVE_SECURE_RENEGOTIATION
    if (ssl->secure_renegotiation && ssl->secure_renegotiation->cache_status) {
        keys = &ssl->secure_renegotiation->tmp_keys;
        copy = 1;
    }
#endif /* HAVE_SECURE_RENEGOTIATION */

    switch (side) {
        case ENCRYPT_SIDE_ONLY:
            wc_encrypt = &ssl->encrypt;
            break;

        case DECRYPT_SIDE_ONLY:
            wc_decrypt = &ssl->decrypt;
            break;

        case ENCRYPT_AND_DECRYPT_SIDE:
            wc_encrypt = &ssl->encrypt;
            wc_decrypt = &ssl->decrypt;
            break;

        default:
            return BAD_FUNC_ARG;
    }

#ifdef HAVE_ONE_TIME_AUTH
    if (!ssl->auth.setup && ssl->specs.bulk_cipher_algorithm == wolfssl_chacha){
        ret = SetAuthKeys(&ssl->auth, keys, &ssl->specs, ssl->heap, devId);
        if (ret != 0)
           return ret;
    }
#endif

    ret = SetKeys(wc_encrypt, wc_decrypt, keys, &ssl->specs, ssl->options.side,
                  ssl->heap, devId);

#ifdef HAVE_SECURE_RENEGOTIATION
    if (copy) {
        int clientCopy = 0;

        if (ssl->options.side == WOLFSSL_CLIENT_END && wc_encrypt)
            clientCopy = 1;
        else if (ssl->options.side == WOLFSSL_SERVER_END && wc_decrypt)
            clientCopy = 1;

        if (clientCopy) {
            XMEMCPY(ssl->keys.client_write_MAC_secret,
                    keys->client_write_MAC_secret, MAX_DIGEST_SIZE);
            XMEMCPY(ssl->keys.client_write_key,
                    keys->client_write_key, AES_256_KEY_SIZE);
            XMEMCPY(ssl->keys.client_write_IV,
                    keys->client_write_IV, AES_IV_SIZE);
        } else {
            XMEMCPY(ssl->keys.server_write_MAC_secret,
                    keys->server_write_MAC_secret, MAX_DIGEST_SIZE);
            XMEMCPY(ssl->keys.server_write_key,
                    keys->server_write_key, AES_256_KEY_SIZE);
            XMEMCPY(ssl->keys.server_write_IV,
                    keys->server_write_IV, AES_IV_SIZE);
        }
        if (wc_encrypt) {
            ssl->keys.sequence_number = keys->sequence_number;
            #ifdef HAVE_AEAD
                if (ssl->specs.cipher_type == aead) {
                    /* Initialize the AES-GCM/CCM explicit IV to a zero. */
                    XMEMCPY(ssl->keys.aead_exp_IV, keys->aead_exp_IV,
                            AEAD_EXP_IV_SZ);

                    /* Initialize encrypt implicit IV by encrypt side */
                    if (ssl->options.side == WOLFSSL_CLIENT_END) {
                        XMEMCPY(ssl->keys.aead_enc_imp_IV,
                                keys->client_write_IV, AEAD_IMP_IV_SZ);
                    } else {
                        XMEMCPY(ssl->keys.aead_enc_imp_IV,
                                keys->server_write_IV, AEAD_IMP_IV_SZ);
                    }
                }
            #endif
        }
        if (wc_decrypt) {
            ssl->keys.peer_sequence_number = keys->peer_sequence_number;
            #ifdef HAVE_AEAD
                if (ssl->specs.cipher_type == aead) {
                    /* Initialize decrypt implicit IV by decrypt side */
                    if (ssl->options.side == WOLFSSL_SERVER_END) {
                        XMEMCPY(ssl->keys.aead_dec_imp_IV,
                                keys->client_write_IV, AEAD_IMP_IV_SZ);
                    } else {
                        XMEMCPY(ssl->keys.aead_dec_imp_IV,
                                keys->server_write_IV, AEAD_IMP_IV_SZ);
                    }
                }
            #endif
        }
        ssl->secure_renegotiation->cache_status++;
    }
#endif /* HAVE_SECURE_RENEGOTIATION */

    return ret;
}


/* TLS can call too */
int StoreKeys(WOLFSSL* ssl, const byte* keyData)
{
    int sz, i = 0;
    Keys* keys = &ssl->keys;

#ifdef HAVE_SECURE_RENEGOTIATION
    if (ssl->secure_renegotiation && ssl->secure_renegotiation->cache_status ==
                                                            SCR_CACHE_NEEDED) {
        keys = &ssl->secure_renegotiation->tmp_keys;
        ssl->secure_renegotiation->cache_status++;
    }
#endif /* HAVE_SECURE_RENEGOTIATION */

    if (ssl->specs.cipher_type != aead) {
        sz = ssl->specs.hash_size;
        XMEMCPY(keys->client_write_MAC_secret,&keyData[i], sz);
        i += sz;
        XMEMCPY(keys->server_write_MAC_secret,&keyData[i], sz);
        i += sz;
    }
    sz = ssl->specs.key_size;
    XMEMCPY(keys->client_write_key, &keyData[i], sz);
    i += sz;
    XMEMCPY(keys->server_write_key, &keyData[i], sz);
    i += sz;

    sz = ssl->specs.iv_size;
    XMEMCPY(keys->client_write_IV, &keyData[i], sz);
    i += sz;
    XMEMCPY(keys->server_write_IV, &keyData[i], sz);

#ifdef HAVE_AEAD
    if (ssl->specs.cipher_type == aead) {
        /* Initialize the AES-GCM/CCM explicit IV to a zero. */
        XMEMSET(keys->aead_exp_IV, 0, AEAD_EXP_IV_SZ);
    }
#endif

    return 0;
}

#ifndef NO_OLD_TLS
int DeriveKeys(WOLFSSL* ssl)
{
    int    length = 2 * ssl->specs.hash_size + 
                    2 * ssl->specs.key_size  +
                    2 * ssl->specs.iv_size;
    int    rounds = (length + MD5_DIGEST_SIZE - 1 ) / MD5_DIGEST_SIZE, i;
    int    ret = 0;
    
#ifdef WOLFSSL_SMALL_STACK
    byte*  shaOutput;
    byte*  md5Input;
    byte*  shaInput;
    byte*  keyData;
    Md5*   md5;
    Sha*   sha;
#else
    byte   shaOutput[SHA_DIGEST_SIZE];
    byte   md5Input[SECRET_LEN + SHA_DIGEST_SIZE];
    byte   shaInput[KEY_PREFIX + SECRET_LEN + 2 * RAN_LEN];
    byte   keyData[KEY_PREFIX * MD5_DIGEST_SIZE];
    Md5    md5[1];
    Sha    sha[1];
#endif
    
#ifdef WOLFSSL_SMALL_STACK
    shaOutput = (byte*)XMALLOC(SHA_DIGEST_SIZE, 
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    md5Input  = (byte*)XMALLOC(SECRET_LEN + SHA_DIGEST_SIZE,
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    shaInput  = (byte*)XMALLOC(KEY_PREFIX + SECRET_LEN + 2 * RAN_LEN,
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    keyData   = (byte*)XMALLOC(KEY_PREFIX * MD5_DIGEST_SIZE,
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    md5       =  (Md5*)XMALLOC(sizeof(Md5), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    sha       =  (Sha*)XMALLOC(sizeof(Sha), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    
    if (shaOutput == NULL || md5Input == NULL || shaInput == NULL ||
        keyData   == NULL || md5      == NULL || sha      == NULL) {
        if (shaOutput) XFREE(shaOutput, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (md5Input)  XFREE(md5Input,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (shaInput)  XFREE(shaInput,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (keyData)   XFREE(keyData,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (md5)       XFREE(md5,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (sha)       XFREE(sha,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
        
        return MEMORY_E;
    }
#endif

    wc_InitMd5(md5);

    ret = wc_InitSha(sha);

    if (ret == 0) {
        XMEMCPY(md5Input, ssl->arrays->masterSecret, SECRET_LEN);

        for (i = 0; i < rounds; ++i) {
            int j   = i + 1;
            int idx = j;

            if (!SetPrefix(shaInput, i)) {
                ret = PREFIX_ERROR;
                break;
            }

            XMEMCPY(shaInput + idx, ssl->arrays->masterSecret, SECRET_LEN);
            idx += SECRET_LEN;
            XMEMCPY(shaInput + idx, ssl->arrays->serverRandom, RAN_LEN);
            idx += RAN_LEN;
            XMEMCPY(shaInput + idx, ssl->arrays->clientRandom, RAN_LEN);

            wc_ShaUpdate(sha, shaInput, (KEY_PREFIX + SECRET_LEN + 2 * RAN_LEN)
                                                              - KEY_PREFIX + j);
            wc_ShaFinal(sha, shaOutput);

            XMEMCPY(md5Input + SECRET_LEN, shaOutput, SHA_DIGEST_SIZE);
            wc_Md5Update(md5, md5Input, SECRET_LEN + SHA_DIGEST_SIZE);
            wc_Md5Final(md5, keyData + i * MD5_DIGEST_SIZE);
        }

        if (ret == 0)
            ret = StoreKeys(ssl, keyData);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(shaOutput, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(md5Input,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(shaInput,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(keyData,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(md5,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(sha,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


static int CleanPreMaster(WOLFSSL* ssl)
{
    int i, ret, sz = ssl->arrays->preMasterSz;

    for (i = 0; i < sz; i++)
        ssl->arrays->preMasterSecret[i] = 0;

    ret = wc_RNG_GenerateBlock(ssl->rng, ssl->arrays->preMasterSecret, sz);
    if (ret != 0)
        return ret;

    for (i = 0; i < sz; i++)
        ssl->arrays->preMasterSecret[i] = 0;

    return 0;
}


/* Create and store the master secret see page 32, 6.1 */
static int MakeSslMasterSecret(WOLFSSL* ssl)
{
    int    i, ret;
    word32 idx;
    word32 pmsSz = ssl->arrays->preMasterSz;

#ifdef WOLFSSL_SMALL_STACK
    byte*  shaOutput;
    byte*  md5Input;
    byte*  shaInput;
    Md5*   md5;
    Sha*   sha;
#else
    byte   shaOutput[SHA_DIGEST_SIZE];
    byte   md5Input[ENCRYPT_LEN + SHA_DIGEST_SIZE];
    byte   shaInput[PREFIX + ENCRYPT_LEN + 2 * RAN_LEN];
    Md5    md5[1];
    Sha    sha[1];
#endif

#ifdef SHOW_SECRETS
    {
        word32 j;
        printf("pre master secret: ");
        for (j = 0; j < pmsSz; j++)
            printf("%02x", ssl->arrays->preMasterSecret[j]);
        printf("\n");
    }
#endif
    
#ifdef WOLFSSL_SMALL_STACK
    shaOutput = (byte*)XMALLOC(SHA_DIGEST_SIZE, 
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    md5Input  = (byte*)XMALLOC(ENCRYPT_LEN + SHA_DIGEST_SIZE,
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    shaInput  = (byte*)XMALLOC(PREFIX + ENCRYPT_LEN + 2 * RAN_LEN,
                                            NULL, DYNAMIC_TYPE_TMP_BUFFER);
    md5       =  (Md5*)XMALLOC(sizeof(Md5), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    sha       =  (Sha*)XMALLOC(sizeof(Sha), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    
    if (shaOutput == NULL || md5Input == NULL || shaInput == NULL ||
                             md5      == NULL || sha      == NULL) {
        if (shaOutput) XFREE(shaOutput, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (md5Input)  XFREE(md5Input,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (shaInput)  XFREE(shaInput,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (md5)       XFREE(md5,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (sha)       XFREE(sha,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
        
        return MEMORY_E;
    }
#endif

    wc_InitMd5(md5);
    
    ret = wc_InitSha(sha);
    
    if (ret == 0) {
        XMEMCPY(md5Input, ssl->arrays->preMasterSecret, pmsSz);

        for (i = 0; i < MASTER_ROUNDS; ++i) {
            byte prefix[KEY_PREFIX];      /* only need PREFIX bytes but static */
            if (!SetPrefix(prefix, i)) {  /* analysis thinks will overrun      */
                ret = PREFIX_ERROR;
                break;
            }

            idx = 0;
            XMEMCPY(shaInput, prefix, i + 1);
            idx += i + 1;

            XMEMCPY(shaInput + idx, ssl->arrays->preMasterSecret, pmsSz);
            idx += pmsSz;
            XMEMCPY(shaInput + idx, ssl->arrays->clientRandom, RAN_LEN);
            idx += RAN_LEN;
            XMEMCPY(shaInput + idx, ssl->arrays->serverRandom, RAN_LEN);
            idx += RAN_LEN;
            wc_ShaUpdate(sha, shaInput, idx);
            wc_ShaFinal(sha, shaOutput);

            idx = pmsSz;  /* preSz */
            XMEMCPY(md5Input + idx, shaOutput, SHA_DIGEST_SIZE);
            idx += SHA_DIGEST_SIZE;
            wc_Md5Update(md5, md5Input, idx);
            wc_Md5Final(md5, &ssl->arrays->masterSecret[i * MD5_DIGEST_SIZE]);
        }

#ifdef SHOW_SECRETS
        {
            word32 j;
            printf("master secret: ");
            for (j = 0; j < SECRET_LEN; j++)
                printf("%02x", ssl->arrays->masterSecret[j]);
            printf("\n");
        }
#endif

        if (ret == 0)
            ret = DeriveKeys(ssl);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(shaOutput, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(md5Input,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(shaInput,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(md5,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(sha,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    
    if (ret == 0)
        ret = CleanPreMaster(ssl);
    else
        CleanPreMaster(ssl);

    return ret;
}
#endif


/* Master wrapper, doesn't use SSL stack space in TLS mode */
int MakeMasterSecret(WOLFSSL* ssl)
{
#ifdef NO_OLD_TLS
    return MakeTlsMasterSecret(ssl);
#elif !defined(NO_TLS)
    if (ssl->options.tls) return MakeTlsMasterSecret(ssl);
#endif

#ifndef NO_OLD_TLS
    return MakeSslMasterSecret(ssl);
#endif
}

