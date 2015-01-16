/*
    FreeRTOS V8.2.0 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

	***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
	***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
	the FAQ page "My application does not run, what could be wrong?".  Have you
	defined configASSERT()?

	http://www.FreeRTOS.org/support - In return for receiving this top quality
	embedded software for free we request you assist our global community by
	participating in the support forum.

	http://www.FreeRTOS.org/training - Investing in training allows your team to
	be as productive as possible as early as possible.  Now you can receive
	FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
	Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#ifndef LED_IO_H
#define LED_IO_H

/* Include the register definition file that is correct for the hardware being
used.  The C and assembler pre-processor must have one of the following board
definitions defined to have the correct register definition header file
included.  Alternatively, just manually include the correct files here. */


	#ifdef YRPBRL78G13
		#include "ior5f100le.h"
		#include "ior5f100le_ext.h"
		#define LED_BIT			( P7_bit.no7 )
		#define LED_INIT()		P7 &= 0x7F; PM7 &= 0x7F
	#endif /* YRPBRL78G13 */

	#ifdef YRDKRL78G14
		#include "ior5f104pj.h"
		#include "ior5f104pj_ext.h"
		#define LED_BIT			( P4_bit.no1 )
		#define LED_INIT() 		LED_BIT = 0
	#endif /* YRDKRL78G14 */

	#ifdef RSKRL78G1C
		#include "ior5f10jgc.h"
		#include "ior5f10jgc_ext.h"
		#define LED_BIT			( P0_bit.no1 )
		#define LED_INIT()		P0 &= 0xFD; PM0 &= 0xFD
	#endif /* RSKRL78G1C */

	#ifdef RSKRL78L1C
		#include "ior5f110pj.h"
		#include "ior5f110pj_ext.h"
		#define LED_BIT			( P4_bit.no1 )
		#define LED_INIT()		P4 &= 0xFD; PM4 &= 0xFD
	#endif /* RSKRL78L1C */

	#ifdef RSKRL78L13
		#include "ior5f10wmg.h"
		#include "ior5f10wmg_ext.h"
		#define LED_BIT			( P4_bit.no1 )
		#define LED_INIT() 		P4 &= 0xFD; PM4 &= 0xFD
	#endif /* RSKRL78L13 */

	#ifdef RL78_G1A_TB
		#include "ior5f10ele.h"
		#include "ior5f10ele_ext.h"
		#define LED_BIT			( P6_bit.no2 )
		#define LED_INIT() 		P6 &= 0xFB; PM6 &= 0xFB
	#endif /* RL78_G1A_TB */

	#ifndef LED_BIT
		#error The hardware platform is not defined
	#endif

#endif /* LED_IO_H */

