/* memory.h
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


#ifndef CYASSL_MEMORY_H
#define CYASSL_MEMORY_H


#include <wolfssl/wolfcrypt/memory.h>
#define CyaSSL_Malloc_cb     wolfSSL_Malloc_cb
#define CyaSSL_Free_cb       wolfSSL_Free_cb
#define CyaSSL_Realloc_cb    wolfSSL_Realloc_cb
#define CyaSSL_SetAllocators wolfSSL_SetAllocators

/* Public in case user app wants to use XMALLOC/XFREE */
#define CyaSSL_Malloc  wolfSSL_Malloc
#define CyaSSL_Free    wolfSSL_Free
#define CyaSSL_Realloc wolfSSL_Realloc

#endif /* CYASSL_MEMORY_H */

