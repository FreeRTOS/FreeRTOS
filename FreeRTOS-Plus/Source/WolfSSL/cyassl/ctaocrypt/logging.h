/* logging.h
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


/* submitted by eof */


#ifndef CYASSL_LOGGING_H
#define CYASSL_LOGGING_H

/* for fips compatibility @wc_fips */
#include <wolfssl/wolfcrypt/logging.h>
#define CYASSL_LEAVE WOLFSSL_LEAVE
#define CYASSL_ERROR WOLFSSL_ERROR
#define CYASSL_ENTER WOLFSSL_ENTER
#define CYASSL_MSG   WOLFSSL_MSG
/* check old macros possibly declared */
#if defined(DEBUG_CYASSL) && !defined(DEBUG_WOLFSSL)
    #define DEBUG_WOLFSSL
#endif

#endif /* CYASSL_LOGGING_H */

