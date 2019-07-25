/* memory.h
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

/* submitted by eof */


#ifndef WOLFSSL_MEMORY_H
#define WOLFSSL_MEMORY_H

#include <stdlib.h>
#include <wolfssl/wolfcrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif

typedef void *(*wolfSSL_Malloc_cb)(size_t size);
typedef void (*wolfSSL_Free_cb)(void *ptr);
typedef void *(*wolfSSL_Realloc_cb)(void *ptr, size_t size);


/* Public set function */
WOLFSSL_API int wolfSSL_SetAllocators(wolfSSL_Malloc_cb  malloc_function,
                                    wolfSSL_Free_cb    free_function,
                                    wolfSSL_Realloc_cb realloc_function);

/* Public in case user app wants to use XMALLOC/XFREE */
WOLFSSL_API void* wolfSSL_Malloc(size_t size);
WOLFSSL_API void  wolfSSL_Free(void *ptr);
WOLFSSL_API void* wolfSSL_Realloc(void *ptr, size_t size);


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* WOLFSSL_MEMORY_H */

