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

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "regtest.h"

/*
 * Test tasks that sets registers to known values, then checks to ensure the
 * values remain as expected.  Test 1 and test 2 use different values.
 */
static void prvRegisterCheck1( void *pvParameters );
static void prvRegisterCheck2( void *pvParameters );

/* Set to a non zero value should an error be found. */
portBASE_TYPE xRegTestError = pdFALSE;

/*-----------------------------------------------------------*/

void vStartRegTestTasks( void )
{
	xTaskCreate( prvRegisterCheck1, "Reg1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegisterCheck2, "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreRegTestTasksStillRunning( void )
{
portBASE_TYPE xReturn;

	/* If a register was found to contain an unexpected value then the
	xRegTestError variable would have been set to a non zero value. */
	if( xRegTestError == pdFALSE )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvRegisterCheck1( void *pvParameters )
{
	( void ) pvParameters;

	for( ;; )
	{
		asm(	"LDI	r31,	5"		);
		asm( 	"MOV	r0,		r31"	);
		asm(	"LDI	r31,	6"		);
		asm( 	"MOV	r1,		r31"	);
		asm(	"LDI	r31,	7"		);
		asm( 	"MOV	r2,		r31"	);
		asm(	"LDI	r31,	8"		);
		asm( 	"MOV	r3,		r31"	);
		asm(	"LDI	r31,	9"		);
		asm( 	"MOV	r4,		r31"	);
		asm(	"LDI	r31,	10"		);
		asm( 	"MOV	r5,		r31"	);
		asm(	"LDI	r31,	11"		);
		asm( 	"MOV	r6,		r31"	);
		asm(	"LDI	r31,	12"		);
		asm( 	"MOV	r7,		r31"	);
		asm(	"LDI	r31,	13"		);
		asm( 	"MOV	r8,		r31"	);
		asm(	"LDI	r31,	14"		);
		asm( 	"MOV	r9,		r31"	);
		asm(	"LDI	r31,	15"		);
		asm( 	"MOV	r10,	r31"	);
		asm(	"LDI	r31,	16"		);
		asm( 	"MOV	r11,	r31"	);
		asm(	"LDI	r31,	17"		);
		asm( 	"MOV	r12,	r31"	);
		asm(	"LDI	r31,	18"		);
		asm( 	"MOV	r13,	r31"	);
		asm(	"LDI	r31,	19"		);
		asm( 	"MOV	r14,	r31"	);
		asm(	"LDI	r31,	20"		);
		asm( 	"MOV	r15,	r31"	);
		asm(	"LDI	r16,	21"		);
		asm(	"LDI	r17,	22"		);
		asm(	"LDI	r18,	23"		);
		asm(	"LDI	r19,	24"		);
		asm(	"LDI	r20,	25"		);
		asm(	"LDI	r21,	26"		);
		asm(	"LDI	r22,	27"		);
		asm(	"LDI	r23,	28"		);
		asm(	"LDI	r24,	29"		);
		asm(	"LDI	r25,	30"		);
		asm(	"LDI	r26,	31"		);
		asm(	"LDI	r27,	32"		);
		asm(	"LDI	r30,	33"		);

		asm(	"LDI	r31,	5"			);
		asm(	"CPSE	r31,	r0"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	6"			);
		asm(	"CPSE	r31,	r1"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	7"			);
		asm(	"CPSE	r31,	r2"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	8"			);
		asm(	"CPSE	r31,	r3"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	9"			);
		asm(	"CPSE	r31,	r4"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	10"			);
		asm(	"CPSE	r31,	r5"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	11"			);
		asm(	"CPSE	r31,	r6"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	12"			);
		asm(	"CPSE	r31,	r7"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	13"			);
		asm(	"CPSE	r31,	r8"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	14"			);
		asm(	"CPSE	r31,	r9"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	15"			);
		asm(	"CPSE	r31,	r10"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	16"			);
		asm(	"CPSE	r31,	r11"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	17"			);
		asm(	"CPSE	r31,	r12"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	18"			);
		asm(	"CPSE	r31,	r13"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	19"			);
		asm(	"CPSE	r31,	r14"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	20"			);
		asm(	"CPSE	r31,	r15"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	21"			);
		asm(	"CPSE	r31,	r16"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	22"			);
		asm(	"CPSE	r31,	r17"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	23"			);
		asm(	"CPSE	r31,	r18"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	24"			);
		asm(	"CPSE	r31,	r19"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	25"			);
		asm(	"CPSE	r31,	r20"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	26"			);
		asm(	"CPSE	r31,	r21"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	27"			);
		asm(	"CPSE	r31,	r22"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	28"			);
		asm(	"CPSE	r31,	r23"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	29"			);
		asm(	"CPSE	r31,	r24"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	30"			);
		asm(	"CPSE	r31,	r25"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	31"			);
		asm(	"CPSE	r31,	r26"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	32"			);
		asm(	"CPSE	r31,	r27"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	33"			);
		asm(	"CPSE	r31,	r30"		);
		asm(	"STS	xRegTestError, r0"	);
	}
}
/*-----------------------------------------------------------*/

static void prvRegisterCheck2( void *pvParameters )
{
	( void ) pvParameters;

	for( ;; )
	{
		asm(	"LDI	r31,	1"		);
		asm( 	"MOV	r0,		r31"	);
		asm(	"LDI	r31,	2"		);
		asm( 	"MOV	r1,		r31"	);
		asm(	"LDI	r31,	3"		);
		asm( 	"MOV	r2,		r31"	);
		asm(	"LDI	r31,	4"		);
		asm( 	"MOV	r3,		r31"	);
		asm(	"LDI	r31,	5"		);
		asm( 	"MOV	r4,		r31"	);
		asm(	"LDI	r31,	6"		);
		asm( 	"MOV	r5,		r31"	);
		asm(	"LDI	r31,	7"		);
		asm( 	"MOV	r6,		r31"	);
		asm(	"LDI	r31,	8"		);
		asm( 	"MOV	r7,		r31"	);
		asm(	"LDI	r31,	9"		);
		asm( 	"MOV	r8,		r31"	);
		asm(	"LDI	r31,	10"		);
		asm( 	"MOV	r9,		r31"	);
		asm(	"LDI	r31,	11"		);
		asm( 	"MOV	r10,	r31"	);
		asm(	"LDI	r31,	12"		);
		asm( 	"MOV	r11,	r31"	);
		asm(	"LDI	r31,	13"		);
		asm( 	"MOV	r12,	r31"	);
		asm(	"LDI	r31,	14"		);
		asm( 	"MOV	r13,	r31"	);
		asm(	"LDI	r31,	15"		);
		asm( 	"MOV	r14,	r31"	);
		asm(	"LDI	r31,	16"		);
		asm( 	"MOV	r15,	r31"	);
		asm(	"LDI	r16,	17"		);
		asm(	"LDI	r17,	18"		);
		asm(	"LDI	r18,	19"		);
		asm(	"LDI	r19,	20"		);
		asm(	"LDI	r20,	21"		);
		asm(	"LDI	r21,	22"		);
		asm(	"LDI	r22,	23"		);
		asm(	"LDI	r23,	24"		);
		asm(	"LDI	r24,	25"		);
		asm(	"LDI	r25,	26"		);
		asm(	"LDI	r26,	27"		);
		asm(	"LDI	r27,	28"		);
		asm(	"LDI	r30,	29"		);

		asm(	"LDI	r31,	1"			);
		asm(	"CPSE	r31,	r0"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	2"			);
		asm(	"CPSE	r31,	r1"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	3"			);
		asm(	"CPSE	r31,	r2"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	4"			);
		asm(	"CPSE	r31,	r3"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	5"			);
		asm(	"CPSE	r31,	r4"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	6"			);
		asm(	"CPSE	r31,	r5"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	7"			);
		asm(	"CPSE	r31,	r6"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	8"			);
		asm(	"CPSE	r31,	r7"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	9"			);
		asm(	"CPSE	r31,	r8"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	10"			);
		asm(	"CPSE	r31,	r9"			);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	11"			);
		asm(	"CPSE	r31,	r10"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	12"			);
		asm(	"CPSE	r31,	r11"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	13"			);
		asm(	"CPSE	r31,	r12"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	14"			);
		asm(	"CPSE	r31,	r13"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	15"			);
		asm(	"CPSE	r31,	r14"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	16"			);
		asm(	"CPSE	r31,	r15"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	17"			);
		asm(	"CPSE	r31,	r16"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	18"			);
		asm(	"CPSE	r31,	r17"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	19"			);
		asm(	"CPSE	r31,	r18"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	20"			);
		asm(	"CPSE	r31,	r19"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	21"			);
		asm(	"CPSE	r31,	r20"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	22"			);
		asm(	"CPSE	r31,	r21"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	23"			);
		asm(	"CPSE	r31,	r22"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	24"			);
		asm(	"CPSE	r31,	r23"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	25"			);
		asm(	"CPSE	r31,	r24"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	26"			);
		asm(	"CPSE	r31,	r25"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	27"			);
		asm(	"CPSE	r31,	r26"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	28"			);
		asm(	"CPSE	r31,	r27"		);
		asm(	"STS	xRegTestError, r0"	);
		asm(	"LDI	r31,	29"			);
		asm(	"CPSE	r31,	r30"		);
		asm(	"STS	xRegTestError, r0"	);
	}
}

