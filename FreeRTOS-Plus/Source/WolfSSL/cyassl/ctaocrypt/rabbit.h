/* rabbit.h
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



#ifndef NO_RABBIT

#ifndef CTAO_CRYPT_RABBIT_H
#define CTAO_CRYPT_RABBIT_H

#include <wolfssl/wolfcrypt/rabbit.h>

/* for rabbit reverse compatibility */
#ifndef NO_RABBIT
    #define RabbitProcess wc_RabbitProcess
    #define RabbitSetKey  wc_RabbitSetKey
#endif

#endif /* CTAO_CRYPT_RABBIT_H */

#endif /* NO_RABBIT */

