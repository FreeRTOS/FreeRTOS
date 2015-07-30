/*--------------------------------------------------------------------
 Copyright(c) 2015 Intel Corporation. All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:

 * Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 notice, this list of conditions and the following disclaimer in
 the documentation and/or other materials provided with the
 distribution.
 * Neither the name of Intel Corporation nor the names of its
 contributors may be used to endorse or promote products derived
 from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 --------------------------------------------------------------------*/

#ifndef __GALILEO_GEN_DEFS_H__
#define __GALILEO_GEN_DEFS_H__

#ifdef __cplusplus
	extern "C" {
#endif

/*-----------------------------------------------------------------------
 * Any required includes
 *------------------------------------------------------------------------
 */
#include <stdarg.h>
#include "stdint.h"

//---------------------------------------------------------------------
// Printf prototype
//---------------------------------------------------------------------
extern int printf( const char *format, ... );
extern int print( char **out, const char *format, va_list args );
extern int sprintf(char *out, const char *format, ...);

//---------------------------------------------------------------------
// Prototypes (assembly language functions in startup.S)
//---------------------------------------------------------------------
extern void halt( void );
extern int32_t inb( int32_t );
extern int32_t inw( int32_t );
extern int32_t inl( int32_t );
extern int32_t outb( int32_t, int32_t );
extern int32_t outw( int32_t, int32_t );
extern int32_t outl( int32_t, int32_t) ;

//---------------------------------------------------------------------
// GP definitions
//---------------------------------------------------------------------
#ifndef TRUE
	#define TRUE ( 1 )
#endif

#ifndef FALSE
	#define FALSE ( 0 )
#endif

#ifndef true
	#define true  TRUE
#endif

#ifndef false
	#define false FALSE
#endif

#ifndef OK
	#define OK TRUE
#endif

//---------------------------------------------------------------------
// General bit pattern definitions
//---------------------------------------------------------------------
#define BIT0  0x00000001U
#define BIT1  0x00000002U
#define BIT2  0x00000004U
#define BIT3  0x00000008U
#define BIT4  0x00000010U
#define BIT5  0x00000020U
#define BIT6  0x00000040U
#define BIT7  0x00000080U
#define BIT8  0x00000100U
#define BIT9  0x00000200U

//---------------------------------------------------------------------
// MMIO support definitions
//---------------------------------------------------------------------
#define EC_BASE			0xE0000000	/* Base of MMConfig space */
#define MMCONFIG_BASE	EC_BASE
#define MMIO_PCI_ADDRESS(bus,dev,fn,reg) ( \
        (EC_BASE) + \
		((bus) << 20) + \
		((dev) << 15) + \
		((fn)  << 12) + \
		(reg))

//---------------------------------------------------------------------
// MMIO read/write/set/clear/modify macros
//---------------------------------------------------------------------
#define mem_read(base, offset, size) ({ \
	volatile uint32_t a = (base) + (offset); \
	volatile uint64_t v; \
    switch (size) { \
    case 1: \
        v = (uint8_t)(*((uint8_t *)a)); \
        break; \
    case 2: \
        v = (uint16_t)(*((uint16_t *)a)); \
        break; \
    case 4: \
        v = (uint32_t)(*((uint32_t *)a)); \
        break; \
    case 8: \
        v = (uint64_t)(*((uint64_t *)a)); \
        break; \
    default: \
        halt(); \
    } \
    v; \
})

// No cache bypass necessary -- MTRRs should handle this
#define mem_write(base, offset, size, value) { \
	volatile uint32_t a = (base) + (offset); \
    switch (size) { \
    case 1: \
        *((uint8_t *)a) = (uint8_t)(value); \
        break; \
    case 2: \
        *((uint16_t *)a) = (uint16_t)(value); \
        break; \
    case 4: \
        *((uint32_t *)a) = (uint32_t)(value); \
        break; \
    case 8: \
        *((uint64_t *)a) = (uint64_t)(value); \
        break; \
    default: \
        halt(); \
    } \
}

#define mem_set(base, offset, size, smask) { \
	volatile uint32_t a = (base) + (offset); \
    switch (size) { \
    case 1: \
        *((uint8_t *)a) = (uint8_t)((*((uint8_t *)a)) | (smask)); \
        break; \
    case 2: \
        *((uint16_t *)a) = (uint16_t)((*((uint16_t *)a)) | (smask)); \
        break; \
    case 4: \
        *((uint32_t *)a) = (uint32_t)((*((uint32_t *)a)) | (smask)); \
        break; \
    case 8: \
        *((uint64_t *)a) = (uint64_t)((*((uint64_t *)a)) | (smask)); \
        break; \
    } \
}

#define mem_clear(base, offset, size, cmask) { \
	volatile uint32_t a = (base) + (offset); \
    switch (size) { \
    case 1: \
        *((uint8_t *)a) = (uint8_t)((*((uint8_t *)a) & ~(cmask))); \
        break; \
    case 2: \
        *((uint16_t *)a) = (uint16_t)((*((uint16_t *)a) & ~(cmask))); \
        break; \
    case 4: \
        *((uint32_t *)a) = (uint32_t)((*((uint32_t *)a) & ~(cmask))); \
        break; \
    case 8: \
        *((uint64_t *)a) = (uint64_t)((*((uint64_t *)a) & ~(cmask))); \
        break; \
    } \
}

#define mem_modify(base, offset, size, cmask, smask) { \
	volatile uint32_t a = (base) + (offset); \
    switch (size) { \
    case 1: \
        *((uint8_t *)a) = (uint8_t)((*((uint8_t *)a) & ~(cmask)) | (smask)); \
        break; \
    case 2: \
        *((uint16_t *)a) = (uint16_t)((*((uint16_t *)a) & ~(cmask)) | (smask)); \
        break; \
    case 4: \
        *((uint32_t *)a) = (uint32_t)((*((uint32_t *)a) & ~(cmask)) | (smask)); \
        break; \
    case 8: \
        *((uint64_t *)a) = (uint64_t)((*((uint64_t *)a) & ~(cmask)) | (smask)); \
        break; \
    } \

#ifdef __cplusplus
	} /* extern C */
#endif

#endif /* GALILEO_GEN_DEFS */

