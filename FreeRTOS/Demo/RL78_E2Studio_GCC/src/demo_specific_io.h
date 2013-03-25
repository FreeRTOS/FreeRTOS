/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems, who sell the code with commercial support,
    indemnification and middleware, under the OpenRTOS brand.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.
*/

#ifndef LED_IO_H
#define LED_IO_H

/* Include the register definition file that is correct for the hardware being
used.  The C and assembler pre-processor must have one of the following board
definitions defined to have the correct register definition header file
included.  Alternatively, just manually include the correct files here. */

	/* Prevent the files being included from the FreeRTOS port layer assembly
	source files. */
	#ifndef __ASSEMBLER__

		#ifdef YRDKRL78G14
			#include "iodefine_RL78G14.h"
			#include "iodefine_RL78G14_ext.h"
			#define LED_BIT			( P4_bit.no1 )
			#define LED_INIT() 		LED_BIT = 0
		#endif /* YRDKRL78G14 */

		#ifdef RSKRL78G1C
			#include "iodefine_RL78G1C.h"
			#include "iodefine_RL78G1C_ext.h"
			#define LED_BIT			( P0_bit.no1 )
			#define LED_INIT()		P0 &= 0xFD; PM0 &= 0xFD
		#endif /* RSKRL78G1C */

		#ifdef RSKRL78L13
			#include "iodefine_RL78L13.h"
			#include "iodefine_RL78L13_ext.h"
			#define LED_BIT			( P4_bit.no1 )
			#define LED_INIT() 		P4 &= 0xFD; PM4 &= 0xFD
		#endif /* RSKRL78L13 */

		#ifdef RL78_G1A_TB
			#include "iodefine_RL78G1A.h"
			#include "iodefine_RL78G1A_ext.h"
			#define LED_BIT			( P6_bit.no2 )
			#define LED_INIT() 		P6 &= 0xFB; PM6 &= 0xFB
		#endif /* RL78_G1A_TB */

		#ifndef LED_BIT
			#error The hardware platform is not defined
		#endif

	#endif /* INCLUDED_FROM_FREERTOS_ASM_FILE */

#endif /* LED_IO_H */

