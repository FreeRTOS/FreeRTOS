/*
 * File:		common.h
 * Purpose:		File to be included by all project files
 *
 * Notes:
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */

#ifndef _COMMON_H_
#define _COMMON_H_

/********************************************************************/

/*
 * Debug prints ON (#define) or OFF (#undef)
 */
#undef DEBUG_PRINT 
#undef DEBUG_PRINT_D0D1 

/* 
 * Include the generic CPU header file 
 */
#include "mcf5xxx.h"

/* 
 * Include the specific CPU header file 
 */
#include "mcf5225x.h"

#include "mcf5225x_evb.h"

/* 
 * MetroWerks looks for an underscore prepended to C function names 
 */
#define _UNDERSCORE_

/* 
 * The source uses __interrupt__ to identify a function as
 * an interrupt or exception handler.  Codewarrior uses 
 * __declspec(interrupt), so we are appeasing it like this.
 */
#define __interrupt__   __declspec(interrupt)

/* 
 * Force functions to return values in D0 
 */
#pragma pointers_in_D0

/* 
 * Provide a few assembly instructions for C level routines
 */
#define halt()      asm( halt)
#define nop()       asm( nop)
#define tpf()       asm( tpf)
#define stop_2700() asm( stop #0x2700)
#define stop_2600() asm( stop #0x2600)
#define stop_2500() asm( stop #0x2500)
#define stop_2400() asm( stop #0x2400)
#define stop_2300() asm( stop #0x2300)
#define stop_2200() asm( stop #0x2200)
#define stop_2100() asm( stop #0x2100)
#define stop_2000() asm( stop #0x2000)

/* 
 * Define custom sections for relocating code, data, and constants 
 */
#pragma define_section relocate_code ".relocate_code" far_absolute RX
#pragma define_section relocate_data ".relocate_data" far_absolute RW
#pragma define_section relocate_const ".relocate_const" far_absolute R
#define __relocate_code__   __declspec(relocate_code)
#define __relocate_data__   __declspec(relocate_data)
#define __relocate_const__  __declspec(relocate_const)
 
/* 
 * Include common utilities
 */
void assert_failed(char *, int);

#ifdef DEBUG_PRINT
#define ASSERT(expr) \
	if (!(expr)) \
		assert_failed(__FILE__, __LINE__)
#else
#define ASSERT(expr)
#endif
 
//#include "assert.h"
//#include "io.h"
//#include "stdlib.h"


/********************************************************************/

#endif /* _COMMON_H_ */
