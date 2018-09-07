/*-
 * Copyright (c) 2000 The NetBSD Foundation, Inc.
 * All rights reserved.
 *
 * This code is derived from software contributed to The NetBSD Foundation
 * by Dieter Baron and Thomas Klausner.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE NETBSD FOUNDATION, INC. AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */
/** @file
    @brief Interfaces for getopt() and getopt_long() work-alike functions.

    This code was taken from FreeBSD and slightly modified, mostly to rename
    symbols with external linkage to avoid naming conflicts in systems where
    there are real getopt()/getopt_long() implementations.  Changed to use
    fixed-width types to allow code using these interfaces to be consistent
    with the rest of the product.
*/
#ifndef REDGETOPT_H
#define REDGETOPT_H


#define red_no_argument         0
#define red_required_argument   1
#define red_optional_argument   2


/** @brief Specifies a long option.
*/
typedef struct
{
    /* name of long option */
    const char *name;
    /*
     * one of red_no_argument, red_required_argument, and red_optional_argument:
     * whether option takes an argument
     */
    int32_t has_arg;
    /* if not NULL, set *flag to val when option found */
    int32_t *flag;
    /* if flag not NULL, value to set *flag to; else return value */
    int32_t val;
} REDOPTION;


int32_t RedGetopt(int32_t nargc, char * const *nargv, const char *options);
int32_t RedGetoptLong(int32_t nargc, char * const *nargv, const char *options, const REDOPTION *long_options, int32_t *idx);


extern const char *red_optarg;
extern int32_t red_optind;
extern int32_t red_opterr;
extern int32_t red_optopt;
extern int32_t red_optreset;


#endif

