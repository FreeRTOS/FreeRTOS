/* xmalloc
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */


#ifndef __XMALLOC_H__
#define __XMALLOC_H__

#include <memory.h>

#ifdef HAVE_LIBC

#include <stdlib.h>
#include <malloc.h>
/* Allocate space for typed object. */
#define _xmalloc(size, align) memalign(align, size)
#define xfree(ptr) free(ptr)

#else

#include <limits.h>

#define DEFAULT_ALIGN (sizeof(unsigned long))

extern void *malloc(size_t size);
extern void *realloc(void *ptr, size_t size);
extern void free(void *ptr);

/* Free memory from any xmalloc*() call. */
extern void xfree(const void *);

/* Underlying functions */
extern void *_xmalloc(size_t size, size_t align);

#endif

static inline void *_xmalloc_array(size_t size, size_t align, size_t num)
{
	/* Check for overflow. */
	if (size && num > UINT_MAX / size)
		return NULL;
	return pvAlignedMalloc(size * num, align);
}

/* Allocate space for typed object. */
#define xmalloc(_type) ((_type *)_xmalloc(sizeof(_type), __alignof__(_type)))

/* Allocate space for array of typed objects. */
#define xmalloc_array(_type, _num) ((_type *)_xmalloc_array(sizeof(_type), __alignof__(_type), _num))

#endif /* __XMALLOC_H__ */
