/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#ifndef _BITTYPES_H
#define _BITTYPES_H

#ifndef HAVE_U_INT8_T

    #if SIZEOF_CHAR == 1
        typedef unsigned char   u_int8_t;
        typedef signed char     _int8_t;
    #elif SIZEOF_INT == 1
        typedef unsigned int    u_int8_t;
        typedef signed int      int8_t;
    #else /* XXX */
        #error "there's no appropriate type for u_int8_t"
    #endif
    #define HAVE_U_INT8_T    1
    #define HAVE_INT8_T      1

#endif /* HAVE_U_INT8_T */

#ifndef HAVE_U_INT16_T

    #if SIZEOF_SHORT == 2
        typedef unsigned short   u_int16_t;
        typedef signed short     _int16_t;
    #elif SIZEOF_INT == 2
        typedef unsigned int     u_int16_t;
        typedef signed int       int16_t;
    #elif SIZEOF_CHAR == 2
        typedef unsigned char    u_int16_t;
        typedef signed char      int16_t;
    #else /* XXX */
        #error "there's no appropriate type for u_int16_t"
    #endif /* if SIZEOF_SHORT == 2 */
    #define HAVE_U_INT16_T    1
    #define HAVE_INT16_T      1

#endif /* HAVE_U_INT16_T */

#ifndef HAVE_U_INT32_T

    #if SIZEOF_INT == 4
        typedef unsigned int     u_int32_t;
        typedef signed int       _int32_t;
    #elif SIZEOF_LONG == 4
        typedef unsigned long    u_int32_t;
        typedef signed long      int32_t;
    #elif SIZEOF_SHORT == 4
        typedef unsigned short   u_int32_t;
        typedef signed short     int32_t;
    #else /* XXX */
        #error "there's no appropriate type for u_int32_t"
    #endif /* if SIZEOF_INT == 4 */
    #define HAVE_U_INT32_T    1
    #define HAVE_INT32_T      1

#endif /* HAVE_U_INT32_T */

#ifndef HAVE_U_INT64_T
    #if SIZEOF_LONG_LONG == 8
        typedef unsigned long long   u_int64_t;
        typedef long long            int64_t;
    #elif defined( _MSC_EXTENSIONS )
        typedef unsigned _int64      u_int64_t;
        typedef _int64               int64_t;
    #elif SIZEOF_INT == 8
        typedef unsigned int         u_int64_t;
    #elif SIZEOF_LONG == 8
        typedef unsigned long        u_int64_t;
    #elif SIZEOF_SHORT == 8
        typedef unsigned short       u_int64_t;
    #else /* XXX */
        #error "there's no appropriate type for u_int64_t"
    #endif /* if SIZEOF_LONG_LONG == 8 */

#endif /* HAVE_U_INT64_T */

#ifndef PRId64
    #ifdef _MSC_EXTENSIONS
        #define PRId64    "I64d"
    #else /* _MSC_EXTENSIONS */
        #define PRId64    "lld"
    #endif /* _MSC_EXTENSIONS */
#endif /* PRId64 */

#ifndef PRIo64
    #ifdef _MSC_EXTENSIONS
        #define PRIo64    "I64o"
    #else /* _MSC_EXTENSIONS */
        #define PRIo64    "llo"
    #endif /* _MSC_EXTENSIONS */
#endif /* PRIo64 */

#ifndef PRIx64
    #ifdef _MSC_EXTENSIONS
        #define PRIx64    "I64x"
    #else /* _MSC_EXTENSIONS */
        #define PRIx64    "llx"
    #endif /* _MSC_EXTENSIONS */
#endif /* PRIx64 */

#ifndef PRIu64
    #ifdef _MSC_EXTENSIONS
        #define PRIu64    "I64u"
    #else /* _MSC_EXTENSIONS */
        #define PRIu64    "llu"
    #endif /* _MSC_EXTENSIONS */
#endif /* PRIu64 */

#endif /* _BITTYPES_H */
