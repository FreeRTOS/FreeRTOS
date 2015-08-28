/* keys.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#include <cyassl/internal.h>
#include <cyassl/error-ssl.h>
#ifdef SHOW_SECRETS
    #ifdef FREESCALE_MQX
        #include <fio.h>
    #else
        #include <stdio.h>
    #endif
#endif


int SetCipherSpecs(CYASSL* ssl)
{
#ifndef NO_CYASSL_CLIENT
    if (ssl->options.side == CYASSL_CLIENT_END) {
        /* server side verified before SetCipherSpecs call */
        if (VerifyClientSuite(ssl) != 1) {
            CYASSL_MSG("SetCipherSpecs() client has an unusuable suite");
            return UNSUPPORTED_SUITE;
        }
    }
#endif /* NO_CYASSL_CLIENT */

    /* ECC extensions, or AES-CCM */
    if (ssl->options.cipherSuite0 == ECC_BYTE) {
    
    switch (ssl->options.cipherSuite) {

#ifdef HAVE_ECC

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256 :
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_triple_des;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_triple_des;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_triple_des;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_triple_des;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_ccm;
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
        CYASSL_MSG("Unsupported cipher suite, SetCipherSpecs ECC");
        return UNSUPPORTED_SUITE;
    }   /* switch */
    }   /* if     */
    if (ssl->options.cipherSuite0 != ECC_BYTE) {   /* normal suites */
    switch (ssl->options.cipherSuite) {

#ifdef BUILD_SSL_RSA_WITH_RC4_128_SHA
    case SSL_RSA_WITH_RC4_128_SHA :
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rc4;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_triple_des;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_triple_des;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_cipher_null;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_hc128;
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
            ssl->specs.bulk_cipher_algorithm = cyassl_hc128;
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
            ssl->specs.bulk_cipher_algorithm = cyassl_hc128;
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
            ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
            ssl->specs.bulk_cipher_algorithm = cyassl_aes;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_rabbit;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_aes_gcm;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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
        ssl->specs.bulk_cipher_algorithm = cyassl_camellia;
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

    default:
        CYASSL_MSG("Unsupported cipher suite, SetCipherSpecs");
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

#ifdef CYASSL_DTLS
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
        CYASSL_MSG("Set Prefix error, bad input");
        return 0; 
    }
    return 1;
}
#endif


static int SetKeys(Ciphers* enc, Ciphers* dec, Keys* keys, CipherSpecs* specs,
                   byte side, void* heap, int devId)
{
#ifdef BUILD_ARC4
    word32 sz = specs->key_size;
    if (specs->bulk_cipher_algorithm == cyassl_rc4) {
        if (enc->arc4 == NULL)
            enc->arc4 = (Arc4*)XMALLOC(sizeof(Arc4), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->arc4 == NULL)
            return MEMORY_E;
        if (dec->arc4 == NULL)
            dec->arc4 = (Arc4*)XMALLOC(sizeof(Arc4), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->arc4 == NULL)
            return MEMORY_E;
#ifdef HAVE_CAVIUM
        if (devId != NO_CAVIUM_DEVICE) {
            if (Arc4InitCavium(enc->arc4, devId) != 0) {
                CYASSL_MSG("Arc4InitCavium failed in SetKeys");
                return CAVIUM_INIT_E;
            }
            if (Arc4InitCavium(dec->arc4, devId) != 0) {
                CYASSL_MSG("Arc4InitCavium failed in SetKeys");
                return CAVIUM_INIT_E;
            }
        }
#endif
        if (side == CYASSL_CLIENT_END) {
            Arc4SetKey(enc->arc4, keys->client_write_key, sz);
            Arc4SetKey(dec->arc4, keys->server_write_key, sz);
        }
        else {
            Arc4SetKey(enc->arc4, keys->server_write_key, sz);
            Arc4SetKey(dec->arc4, keys->client_write_key, sz);
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif
    
#ifdef HAVE_HC128
    if (specs->bulk_cipher_algorithm == cyassl_hc128) {
        int hcRet;
        if (enc->hc128 == NULL)
            enc->hc128 =
                      (HC128*)XMALLOC(sizeof(HC128), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->hc128 == NULL)
            return MEMORY_E;
        if (dec->hc128 == NULL)
            dec->hc128 =
                      (HC128*)XMALLOC(sizeof(HC128), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->hc128 == NULL)
            return MEMORY_E;
        if (side == CYASSL_CLIENT_END) {
            hcRet = Hc128_SetKey(enc->hc128, keys->client_write_key,
                                 keys->client_write_IV);
            if (hcRet != 0) return hcRet;
            hcRet = Hc128_SetKey(dec->hc128, keys->server_write_key,
                                  keys->server_write_IV);
            if (hcRet != 0) return hcRet;
        }
        else {
            hcRet = Hc128_SetKey(enc->hc128, keys->server_write_key,
                                  keys->server_write_IV);
            if (hcRet != 0) return hcRet;
            hcRet = Hc128_SetKey(dec->hc128, keys->client_write_key,
                                  keys->client_write_IV);
            if (hcRet != 0) return hcRet;
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif
    
#ifdef BUILD_RABBIT
    if (specs->bulk_cipher_algorithm == cyassl_rabbit) {
        int rabRet;
        if (enc->rabbit == NULL)
            enc->rabbit =
                    (Rabbit*)XMALLOC(sizeof(Rabbit), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->rabbit == NULL)
            return MEMORY_E;
        if (dec->rabbit == NULL)
            dec->rabbit =
                    (Rabbit*)XMALLOC(sizeof(Rabbit), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->rabbit == NULL)
            return MEMORY_E;
        if (side == CYASSL_CLIENT_END) {
            rabRet = RabbitSetKey(enc->rabbit, keys->client_write_key,
                                  keys->client_write_IV);
            if (rabRet != 0) return rabRet;
            rabRet = RabbitSetKey(dec->rabbit, keys->server_write_key,
                                  keys->server_write_IV);
            if (rabRet != 0) return rabRet;
        }
        else {
            rabRet = RabbitSetKey(enc->rabbit, keys->server_write_key,
                                           keys->server_write_IV);
            if (rabRet != 0) return rabRet;
            rabRet = RabbitSetKey(dec->rabbit, keys->client_write_key,
                                           keys->client_write_IV);
            if (rabRet != 0) return rabRet;
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif
    
#ifdef BUILD_DES3
    if (specs->bulk_cipher_algorithm == cyassl_triple_des) {
        int desRet = 0;

        if (enc->des3 == NULL)
            enc->des3 = (Des3*)XMALLOC(sizeof(Des3), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->des3 == NULL)
            return MEMORY_E;
        if (dec->des3 == NULL)
            dec->des3 = (Des3*)XMALLOC(sizeof(Des3), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->des3 == NULL)
            return MEMORY_E;
#ifdef HAVE_CAVIUM
        if (devId != NO_CAVIUM_DEVICE) {
            if (Des3_InitCavium(enc->des3, devId) != 0) {
                CYASSL_MSG("Des3_InitCavium failed in SetKeys");
                return CAVIUM_INIT_E;
            }
            if (Des3_InitCavium(dec->des3, devId) != 0) {
                CYASSL_MSG("Des3_InitCavium failed in SetKeys");
                return CAVIUM_INIT_E;
            }
        }
#endif
        if (side == CYASSL_CLIENT_END) {
            desRet = Des3_SetKey(enc->des3, keys->client_write_key,
                        keys->client_write_IV, DES_ENCRYPTION);
            if (desRet != 0)
                return desRet;
            desRet = Des3_SetKey(dec->des3, keys->server_write_key,
                        keys->server_write_IV, DES_DECRYPTION);
            if (desRet != 0)
                return desRet;
        }
        else {
            desRet = Des3_SetKey(enc->des3, keys->server_write_key,
                        keys->server_write_IV, DES_ENCRYPTION);
            if (desRet != 0)
                return desRet;
            desRet = Des3_SetKey(dec->des3, keys->client_write_key,
                keys->client_write_IV, DES_DECRYPTION);
            if (desRet != 0)
                return desRet;
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif

#ifdef BUILD_AES
    if (specs->bulk_cipher_algorithm == cyassl_aes) {
        int aesRet = 0;

        if (enc->aes == NULL)
            enc->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->aes == NULL)
            return MEMORY_E;
        if (dec->aes == NULL)
            dec->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->aes == NULL)
            return MEMORY_E;
#ifdef HAVE_CAVIUM
        if (devId != NO_CAVIUM_DEVICE) {
            if (AesInitCavium(enc->aes, devId) != 0) {
                CYASSL_MSG("AesInitCavium failed in SetKeys");
                return CAVIUM_INIT_E;
            }
            if (AesInitCavium(dec->aes, devId) != 0) {
                CYASSL_MSG("AesInitCavium failed in SetKeys");
                return CAVIUM_INIT_E;
            }
        }
#endif
        if (side == CYASSL_CLIENT_END) {
            aesRet = AesSetKey(enc->aes, keys->client_write_key,
                               specs->key_size, keys->client_write_IV,
                               AES_ENCRYPTION);
            if (aesRet != 0)
                return aesRet;
            aesRet = AesSetKey(dec->aes, keys->server_write_key,
                               specs->key_size, keys->server_write_IV,
                               AES_DECRYPTION);
            if (aesRet != 0)
                return aesRet;
        }
        else {
            aesRet = AesSetKey(enc->aes, keys->server_write_key,
                               specs->key_size, keys->server_write_IV,
                               AES_ENCRYPTION);
            if (aesRet != 0)
                return aesRet;
            aesRet = AesSetKey(dec->aes, keys->client_write_key,
                               specs->key_size, keys->client_write_IV,
                               AES_DECRYPTION);
            if (aesRet != 0)
                return aesRet;
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif

#ifdef BUILD_AESGCM
    if (specs->bulk_cipher_algorithm == cyassl_aes_gcm) {
        if (enc->aes == NULL)
            enc->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->aes == NULL)
            return MEMORY_E;
        if (dec->aes == NULL)
            dec->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->aes == NULL)
            return MEMORY_E;

        if (side == CYASSL_CLIENT_END) {
            AesGcmSetKey(enc->aes, keys->client_write_key, specs->key_size);
            XMEMCPY(keys->aead_enc_imp_IV,
                                     keys->client_write_IV, AEAD_IMP_IV_SZ);
            AesGcmSetKey(dec->aes, keys->server_write_key, specs->key_size);
            XMEMCPY(keys->aead_dec_imp_IV,
                                     keys->server_write_IV, AEAD_IMP_IV_SZ);
        }
        else {
            AesGcmSetKey(enc->aes, keys->server_write_key, specs->key_size);
            XMEMCPY(keys->aead_enc_imp_IV,
                                     keys->server_write_IV, AEAD_IMP_IV_SZ);
            AesGcmSetKey(dec->aes, keys->client_write_key, specs->key_size);
            XMEMCPY(keys->aead_dec_imp_IV,
                                     keys->client_write_IV, AEAD_IMP_IV_SZ);
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif

#ifdef HAVE_AESCCM
    if (specs->bulk_cipher_algorithm == cyassl_aes_ccm) {
        if (enc->aes == NULL)
            enc->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->aes == NULL)
            return MEMORY_E;
        if (dec->aes == NULL)
            dec->aes = (Aes*)XMALLOC(sizeof(Aes), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->aes == NULL)
            return MEMORY_E;

        if (side == CYASSL_CLIENT_END) {
            AesCcmSetKey(enc->aes, keys->client_write_key, specs->key_size);
            XMEMCPY(keys->aead_enc_imp_IV,
                                     keys->client_write_IV, AEAD_IMP_IV_SZ);
            AesCcmSetKey(dec->aes, keys->server_write_key, specs->key_size);
            XMEMCPY(keys->aead_dec_imp_IV,
                                     keys->server_write_IV, AEAD_IMP_IV_SZ);
        }
        else {
            AesCcmSetKey(enc->aes, keys->server_write_key, specs->key_size);
            XMEMCPY(keys->aead_enc_imp_IV,
                                     keys->server_write_IV, AEAD_IMP_IV_SZ);
            AesCcmSetKey(dec->aes, keys->client_write_key, specs->key_size);
            XMEMCPY(keys->aead_dec_imp_IV,
                                     keys->client_write_IV, AEAD_IMP_IV_SZ);
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif

#ifdef HAVE_CAMELLIA
    if (specs->bulk_cipher_algorithm == cyassl_camellia) {
        int camRet;

        if (enc->cam == NULL)
            enc->cam =
                (Camellia*)XMALLOC(sizeof(Camellia), heap, DYNAMIC_TYPE_CIPHER);
        if (enc->cam == NULL)
            return MEMORY_E;

        if (dec->cam == NULL)
            dec->cam =
                (Camellia*)XMALLOC(sizeof(Camellia), heap, DYNAMIC_TYPE_CIPHER);
        if (dec->cam == NULL)
            return MEMORY_E;

        if (side == CYASSL_CLIENT_END) {
            camRet = CamelliaSetKey(enc->cam, keys->client_write_key,
                      specs->key_size, keys->client_write_IV);
            if (camRet != 0)
                return camRet;

            camRet = CamelliaSetKey(dec->cam, keys->server_write_key,
                      specs->key_size, keys->server_write_IV);
            if (camRet != 0)
                return camRet;
        }
        else {
            camRet = CamelliaSetKey(enc->cam, keys->server_write_key,
                      specs->key_size, keys->server_write_IV);
            if (camRet != 0)
                return camRet;

            camRet = CamelliaSetKey(dec->cam, keys->client_write_key,
                      specs->key_size, keys->client_write_IV);
            if (camRet != 0)
                return camRet;
        }
        enc->setup = 1;
        dec->setup = 1;
    }
#endif

#ifdef HAVE_NULL_CIPHER
    if (specs->bulk_cipher_algorithm == cyassl_cipher_null) {
        enc->setup = 1;
        dec->setup = 1;
    }
#endif

    keys->sequence_number      = 0;
    keys->peer_sequence_number = 0;
    keys->encryptionOn         = 0;
    (void)side;
    (void)heap;
    (void)enc;
    (void)dec;
    (void)specs;
    (void)devId;

    return 0;
}


/* TLS can call too */
int StoreKeys(CYASSL* ssl, const byte* keyData)
{
    int sz, i = 0;
    int devId = NO_CAVIUM_DEVICE;

#ifdef HAVE_CAVIUM
    devId = ssl->devId;
#endif

    if (ssl->specs.cipher_type != aead) {
        sz = ssl->specs.hash_size;
        XMEMCPY(ssl->keys.client_write_MAC_secret,&keyData[i], sz);
        i += sz;
        XMEMCPY(ssl->keys.server_write_MAC_secret,&keyData[i], sz);
        i += sz;
    }
    sz = ssl->specs.key_size;
    XMEMCPY(ssl->keys.client_write_key, &keyData[i], sz);
    i += sz;
    XMEMCPY(ssl->keys.server_write_key, &keyData[i], sz);
    i += sz;

    sz = ssl->specs.iv_size;
    XMEMCPY(ssl->keys.client_write_IV, &keyData[i], sz);
    i += sz;
    XMEMCPY(ssl->keys.server_write_IV, &keyData[i], sz);

#ifdef HAVE_AEAD
    if (ssl->specs.cipher_type == aead) {
        /* Initialize the AES-GCM/CCM explicit IV to a zero. */
        XMEMSET(ssl->keys.aead_exp_IV, 0, AEAD_EXP_IV_SZ);
    }
#endif

    return SetKeys(&ssl->encrypt, &ssl->decrypt, &ssl->keys, &ssl->specs,
                   ssl->options.side, ssl->heap, devId);
}

#ifndef NO_OLD_TLS
int DeriveKeys(CYASSL* ssl)
{
    int length = 2 * ssl->specs.hash_size + 
                 2 * ssl->specs.key_size  +
                 2 * ssl->specs.iv_size;
    int rounds = (length + MD5_DIGEST_SIZE - 1 ) / MD5_DIGEST_SIZE, i;
    int ret = 0;

    byte shaOutput[SHA_DIGEST_SIZE];
    byte md5Input[SECRET_LEN + SHA_DIGEST_SIZE];
    byte shaInput[KEY_PREFIX + SECRET_LEN + 2 * RAN_LEN];
  
    Md5 md5;
    Sha sha;

    byte keyData[KEY_PREFIX * MD5_DIGEST_SIZE];  /* max size */

    InitMd5(&md5);
    ret = InitSha(&sha);
    if (ret != 0) 
        return ret;

    XMEMCPY(md5Input, ssl->arrays->masterSecret, SECRET_LEN);

    for (i = 0; i < rounds; ++i) {
        int j   = i + 1;
        int idx = j;

        if (!SetPrefix(shaInput, i)) {
            return PREFIX_ERROR;
        }

        XMEMCPY(shaInput + idx, ssl->arrays->masterSecret, SECRET_LEN);
        idx += SECRET_LEN;
        XMEMCPY(shaInput + idx, ssl->arrays->serverRandom, RAN_LEN);
        idx += RAN_LEN;
        XMEMCPY(shaInput + idx, ssl->arrays->clientRandom, RAN_LEN);

        ShaUpdate(&sha, shaInput, (word32)sizeof(shaInput) - KEY_PREFIX + j);
        ShaFinal(&sha, shaOutput);

        XMEMCPY(&md5Input[SECRET_LEN], shaOutput, SHA_DIGEST_SIZE);
        Md5Update(&md5, md5Input, sizeof(md5Input));
        Md5Final(&md5, keyData + i * MD5_DIGEST_SIZE);
    }

    return StoreKeys(ssl, keyData);
}


static int CleanPreMaster(CYASSL* ssl)
{
    int i, ret, sz = ssl->arrays->preMasterSz;

    for (i = 0; i < sz; i++)
        ssl->arrays->preMasterSecret[i] = 0;

    ret = RNG_GenerateBlock(ssl->rng, ssl->arrays->preMasterSecret, sz);
    if (ret != 0)
        return ret;

    for (i = 0; i < sz; i++)
        ssl->arrays->preMasterSecret[i] = 0;

    return 0;
}


/* Create and store the master secret see page 32, 6.1 */
static int MakeSslMasterSecret(CYASSL* ssl)
{
    byte   shaOutput[SHA_DIGEST_SIZE];
    byte   md5Input[ENCRYPT_LEN + SHA_DIGEST_SIZE];
    byte   shaInput[PREFIX + ENCRYPT_LEN + 2 * RAN_LEN];
    int    i, ret;
    word32 idx;
    word32 pmsSz = ssl->arrays->preMasterSz;

    Md5 md5;
    Sha sha;

#ifdef SHOW_SECRETS
    {
        word32 j;
        printf("pre master secret: ");
        for (j = 0; j < pmsSz; j++)
            printf("%02x", ssl->arrays->preMasterSecret[j]);
        printf("\n");
    }
#endif

    InitMd5(&md5);
    ret = InitSha(&sha);
    if (ret != 0) 
        return ret;

    XMEMCPY(md5Input, ssl->arrays->preMasterSecret, pmsSz);

    for (i = 0; i < MASTER_ROUNDS; ++i) {
        byte prefix[KEY_PREFIX];      /* only need PREFIX bytes but static */
        if (!SetPrefix(prefix, i)) {  /* analysis thinks will overrun      */
            return PREFIX_ERROR;
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
        ShaUpdate(&sha, shaInput, idx);
        ShaFinal(&sha, shaOutput);

        idx = pmsSz;  /* preSz */
        XMEMCPY(md5Input + idx, shaOutput, SHA_DIGEST_SIZE);
        idx += SHA_DIGEST_SIZE;
        Md5Update(&md5, md5Input, idx);
        Md5Final(&md5, &ssl->arrays->masterSecret[i * MD5_DIGEST_SIZE]);
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

    ret = DeriveKeys(ssl);
    if (ret != 0) {
        /* always try to clean PreMaster */
        CleanPreMaster(ssl);
        return ret;
    }

    return CleanPreMaster(ssl);
}
#endif


/* Master wrapper, doesn't use SSL stack space in TLS mode */
int MakeMasterSecret(CYASSL* ssl)
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

