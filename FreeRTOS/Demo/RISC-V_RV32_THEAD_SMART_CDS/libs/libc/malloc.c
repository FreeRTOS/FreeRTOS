/*
 * Copyright (C) 2016 YunOS Project. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <csi_config.h>
#include <string.h>
#ifndef CONFIG_KERNEL_NONE
#include <csi_kernel.h>
#else
#include <umm_heap.h>
#endif

#ifndef MALLOC_WEAK
#define MALLOC_WEAK __attribute__((weak))
#endif

MALLOC_WEAK void *malloc(size_t size)
{
    void *ret;

#ifdef CONFIG_KERNEL_NONE
    ret = mm_malloc(USR_HEAP, size, __builtin_return_address(0));
#else
    ret = csi_kernel_malloc(size, __builtin_return_address(0));
#endif

    return ret;
}

MALLOC_WEAK void free(void *ptr)
{
#ifdef CONFIG_KERNEL_NONE
    mm_free(USR_HEAP, ptr, __builtin_return_address(0));
#else
    csi_kernel_free(ptr, __builtin_return_address(0));
#endif
}

MALLOC_WEAK void *realloc(void *ptr, size_t size)
{
    void *new_ptr;

#ifdef CONFIG_KERNEL_NONE
    new_ptr = mm_malloc(USR_HEAP, size, __builtin_return_address(0));
#else
    new_ptr = csi_kernel_malloc(size, __builtin_return_address(0));
#endif

    if (new_ptr == NULL) {
        return new_ptr;
    }

    if (ptr) {
        memcpy(new_ptr, ptr, size);

#ifdef CONFIG_KERNEL_NONE
        mm_free(USR_HEAP, ptr, __builtin_return_address(0));
#else
        csi_kernel_free(ptr, __builtin_return_address(0));
#endif
    }

    return new_ptr;
}

MALLOC_WEAK void *calloc(size_t nmemb, size_t size)
{
    void *ptr = NULL;

#ifdef CONFIG_KERNEL_NONE
    ptr = mm_malloc(USR_HEAP, size * nmemb, __builtin_return_address(0));
#else
    ptr = csi_kernel_malloc(size * nmemb, __builtin_return_address(0));
#endif

    if (ptr) {
        memset(ptr, 0, size * nmemb);
    }

    return ptr;
}
