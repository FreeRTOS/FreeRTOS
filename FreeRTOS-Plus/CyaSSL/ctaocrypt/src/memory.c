/* memory.c 
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* submitted by eof */


#include <cyassl/ctaocrypt/settings.h>

#ifdef USE_CYASSL_MEMORY

#include <cyassl/ctaocrypt/memory.h>
#include <cyassl/ctaocrypt/error.h>


/* Set these to default values initially. */
static CyaSSL_Malloc_cb  malloc_function = 0;
static CyaSSL_Free_cb    free_function = 0;
static CyaSSL_Realloc_cb realloc_function = 0;

int CyaSSL_SetAllocators(CyaSSL_Malloc_cb  mf,
                         CyaSSL_Free_cb    ff,
                         CyaSSL_Realloc_cb rf)
{
    int res = 0;

    if (mf)
        malloc_function = mf;
	else
        res = BAD_FUNC_ARG;

    if (ff)
        free_function = ff;
    else
        res = BAD_FUNC_ARG;

    if (rf)
        realloc_function = rf;
    else
        res = BAD_FUNC_ARG;

    return res;
}


void* CyaSSL_Malloc(size_t size)
{
    void* res = 0;

    if (malloc_function)
        res = malloc_function(size);
    else
        res = malloc(size);

    return res;
}

void CyaSSL_Free(void *ptr)
{
    if (free_function)
        free_function(ptr);
    else
        free(ptr);
}

void* CyaSSL_Realloc(void *ptr, size_t size)
{
    void* res = 0;

    if (realloc_function)
        res = realloc_function(ptr, size);
    else
        res = realloc(ptr, size);

    return res;
}

#endif /* USE_CYASSL_MEMORY */
