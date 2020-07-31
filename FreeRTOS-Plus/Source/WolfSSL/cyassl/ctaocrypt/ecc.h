/* ecc.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#ifdef HAVE_ECC

#ifndef CTAO_CRYPT_ECC_H
#define CTAO_CRYPT_ECC_H

#include <wolfssl/wolfcrypt/ecc.h>

/* includes for compatibility */
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/random.h>

/* for ecc reverse compatibility */
#ifdef HAVE_ECC
	#define ecc_make_key      wc_ecc_make_key
	#define ecc_shared_secret wc_ecc_shared_secret
	#define ecc_sign_hash     wc_ecc_sign_hash
	#define ecc_verify_hash   wc_ecc_verify_hash
	#define ecc_init          wc_ecc_init
	#define ecc_free          wc_ecc_free
	#define ecc_fp_free       wc_ecc_fp_free
	#define ecc_export_x963   wc_ecc_export_x963
	#define ecc_size          wc_ecc_size
	#define ecc_sig_size      wc_ecc_sig_size
	#define ecc_export_x963_ex      wc_ecc_export_x963_ex
	#define ecc_import_x963         wc_ecc_import_x963
	#define ecc_import_private_key  wc_ecc_import_private_key
	#define ecc_rs_to_sig           wc_ecc_rs_to_sig
	#define ecc_import_raw          wc_ecc_import_raw
	#define ecc_export_private_only wc_ecc_export_private_only

#ifdef HAVE_ECC_ENCRYPT
	/* ecc encrypt */
	#define ecc_ctx_new           wc_ecc_ctx_new
	#define ecc_ctx_free          wc_ecc_ctx_free
	#define ecc_ctx_reset         wc_ecc_ctx_reset
	#define ecc_ctx_get_own_salt  wc_ecc_ctx_get_own_salt
	#define ecc_ctx_set_peer_salt wc_ecc_ctx_set_peer_salt
	#define ecc_ctx_set_info      wc_ecc_ctx_set_info
	#define ecc_encrypt           wc_ecc_encrypt
	#define ecc_decrypt           wc_ecc_decrypt
#endif /* HAVE_ECC_ENCRYPT */
#endif

#endif /* CTAO_CRYPT_ECC_H */
#endif /* HAVE_ECC */

