/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 ****************************************************************************
 * (C) 2003 - Rolf Neugebauer - Intel Research Cambridge
 ****************************************************************************
 *
 *        File: types.h
 *      Author: Rolf Neugebauer (neugebar@dcs.gla.ac.uk)
 *     Changes: 
 *              
 *        Date: May 2003
 * 
 * Environment: Xen Minimal OS
 * Description: a random collection of type definitions
 *
 ****************************************************************************
 * $Id: h-insert.h,v 1.4 2002/11/08 16:03:55 rn Exp $
 ****************************************************************************
 */

#ifndef _TYPES_H_
#define _TYPES_H_
#include <stddef.h>

/* FreeBSD compat types */
#ifndef HAVE_LIBC
typedef unsigned char       u_char;
typedef unsigned int        u_int;
typedef unsigned long       u_long;
#endif
#if defined(__i386__) || defined(__arm__)
typedef long long           quad_t;
typedef unsigned long long  u_quad_t;
#elif defined(__x86_64__)
typedef long                quad_t;
typedef unsigned long       u_quad_t;
#endif /* __i386__ || __x86_64__ */

#ifdef HAVE_LIBC
#include <stdint.h>
#else
#if defined(__i386__) || defined(__arm__)
typedef unsigned int        uintptr_t;
typedef int                 intptr_t;
#elif defined(__x86_64__) || defined(__aarch64__)
typedef unsigned long       uintptr_t;
typedef long                intptr_t;
#endif /* __i386__ || __x86_64__ */
typedef unsigned char uint8_t;
typedef   signed char int8_t;
typedef unsigned short uint16_t;
typedef   signed short int16_t;
typedef unsigned int uint32_t;
typedef   signed int int32_t;
#if defined(__i386__) || defined(__arm__)
typedef   signed long long int64_t;
typedef unsigned long long uint64_t;
#elif defined(__x86_64__) || defined(__aarch64__)
typedef   signed long int64_t;
typedef unsigned long uint64_t;
typedef  int64_t off_t;
#endif
typedef uint64_t uintmax_t;
typedef  int64_t intmax_t;
#endif

typedef intptr_t            ptrdiff_t;


#if defined(__x86_64__)
typedef long ssize_t;
#endif

#endif /* _TYPES_H_ */
