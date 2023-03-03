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

#define SIZEOF_CHAR             1
#define SIZEOF_SHORT            2
#define SIZEOF_INT              4
#ifndef _MSC_EXTENSIONS
    #define SIZEOF_LONG_LONG    8
#endif

/*
 * Avoids a compiler warning in case this was already defined
 * (someone defined _WINSOCKAPI_ when including 'windows.h', in order
 * to prevent it from including 'winsock.h')
 */
#ifdef _WINSOCKAPI_
    #undef _WINSOCKAPI_
#endif
#include <winsock2.h>

#include <fcntl.h>

#include "bittypes.h"
#include <time.h>
#include <io.h>

#ifndef __MINGW32__
    #include "IP6_misc.h"
#endif

#define caddr_t          char *

#if _MSC_VER < 1500
    #define snprintf     _snprintf
    #define vsnprintf    _vsnprintf
    #define strdup       _strdup
#endif

#define inline           __inline

#ifdef __MINGW32__
    #include <stdint.h>
#else /*__MINGW32__*/
/* MSVC compiler */
    #ifndef _UINTPTR_T_DEFINED
        #ifdef  _WIN64
            typedef unsigned __int64    uintptr_t;
        #else
            typedef _W64 unsigned int   uintptr_t;
        #endif
        #define _UINTPTR_T_DEFINED
    #endif

    #ifndef _INTPTR_T_DEFINED
        #ifdef  _WIN64
            typedef __int64    intptr_t;
        #else
            typedef _W64 int   intptr_t;
        #endif
        #define _INTPTR_T_DEFINED
    #endif

#endif /*__MINGW32__*/
