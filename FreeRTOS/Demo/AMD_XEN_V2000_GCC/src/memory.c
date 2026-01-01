/* memory 
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

#include "FreeRTOS.h"
#include "task.h"
#include <memory.h>

/* Wrapper functions for malloc/free used by ACPI library */
void free(void *ptr){
    vPortFree(ptr);
};

void *malloc(unsigned int size){
    return pvPortMalloc(size);
};

void *pvAlignedMalloc(size_t size, size_t alignment) {
    // Make sure alignment is a power of two and is not zero
    if ((alignment & (alignment - (size_t)1)) != (size_t)0 || alignment == (size_t)0) {
        return NULL;
    }

    // Allocate enough memory to store the requested size and alignment overhead
    void *ptr = pvPortMalloc(size + alignment - (size_t)1 + sizeof(void *));
    if (ptr == NULL) {
        return NULL;  // Allocation failed
    }

    // Align the pointer
    void *aligned_ptr = (void *)(((uint64_t) ptr + sizeof(void *) + alignment - (size_t)1) & ~(alignment - (size_t)1));

    // Store the original pointer just before the aligned pointer for later deallocation
    ((void **)aligned_ptr)[-1] = ptr;

    return aligned_ptr;
}
