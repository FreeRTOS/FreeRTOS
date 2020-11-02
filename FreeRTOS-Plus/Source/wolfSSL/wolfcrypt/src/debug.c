/* debug.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/wc_port.h>
#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_STACK_SIZE_VERBOSE
WOLFSSL_API THREAD_LS_T unsigned char *StackSizeCheck_myStack = NULL;
WOLFSSL_API THREAD_LS_T size_t StackSizeCheck_stackSize = 0;
WOLFSSL_API THREAD_LS_T size_t StackSizeCheck_stackSizeHWM = 0;
WOLFSSL_API THREAD_LS_T size_t *StackSizeCheck_stackSizeHWM_ptr = 0;
WOLFSSL_API THREAD_LS_T void *StackSizeCheck_stackOffsetPointer = 0;
#endif
