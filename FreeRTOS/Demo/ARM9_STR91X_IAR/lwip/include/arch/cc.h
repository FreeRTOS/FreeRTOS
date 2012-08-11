/*
 * Copyright (c) 2001-2003 Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 *
 * Author: Adam Dunkels <adam@sics.se>
 * Author: Stefano Oliveri <stefano.oliveri@st.com>
 *
 */
#ifndef __CC_H__
#define __CC_H__

#include "cpu.h"

//#define LWIP_PROVIDE_ERRNO 1
#include "lwip_errno.h"

// Typedefs for the types used by lwip

typedef unsigned   char    u8_t;
typedef signed     char    s8_t;
typedef unsigned   short   u16_t;
typedef signed     short   s16_t;
typedef unsigned   long    u32_t;
typedef signed     long    s32_t;
typedef u32_t mem_ptr_t;
typedef int sys_prot_t;

// Compiler hints for packing lwip's structures

#define PACK_STRUCT_BEGIN
//#define PACK_STRUCT_BEGIN _Pragma("pack(2)")
#define PACK_STRUCT_STRUCT
#define PACK_STRUCT_END
//#define PACK_STRUCT_END _Pragma("pack()")
#define PACK_STRUCT_FIELD(x) x

// Platform specific diagnostic output

// non-fatal, print a message.
#define LWIP_PLATFORM_DIAG(x)
// fatal, print message and abandon execution.
#define LWIP_PLATFORM_ASSERT(x)

// "lightweight" synchronization mechanisms

// declare a protection state variable.
#define SYS_ARCH_DECL_PROTECT(x)
// enter protection mode.
#define SYS_ARCH_PROTECT(x)
// leave protection mode.
#define SYS_ARCH_UNPROTECT(x)


#endif /* __CC_H__ */
