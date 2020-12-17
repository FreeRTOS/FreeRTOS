/*
 * FreeRTOS V202012.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "regtest.h"

/* The minimum stack size required by a register test task. 
 * 
 * The value should be at least the sum of: 
 * - Number of bytes used to save register context. 
 *   Refer to port.c, r0-r31 and/or RAMPZ and/or EIND.
 * - Number of bytes used in nested function call.
 *   Refer to GCC Developer Option -fstack-usage. 
 */
#define REGTEST_MIN_STACK_SIZE		( ( unsigned short ) 50 )

/*
 * Test tasks that sets registers to known values, then checks to ensure the
 * values remain as expected.  Test 1 and test 2 use different values.
 */
static void prvRegisterCheck1( void *pvParameters );
static void prvRegisterCheck2( void *pvParameters );

/* Set to a none zero value should an error be found. 
 * Using two variables to identify offending task and register combination. 
 */
UBaseType_t uxRegTestError1 = 0;
UBaseType_t uxRegTestError2 = 0;

/*-----------------------------------------------------------*/

void vStartRegTestTasks( void )
{
	/* Create register check tasks with lowest priority. These tasks will be
	 * interrupted as much as possible by higher priority tasks. Thus if task
	 * context is not restored correctly, error is more likely to be caught.
	 */
	xTaskCreate( prvRegisterCheck1, "Reg1", REGTEST_MIN_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegisterCheck2, "Reg2", REGTEST_MIN_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );		
}
/*-----------------------------------------------------------*/

BaseType_t xAreRegTestTasksStillRunning( void )
{
BaseType_t xReturn;

	/* If a register was found to contain an unexpected value then the
	 * uxRegTestError variable would have been set to a none zero value. 
	 *
	 * This check guarantees no false positive, but does not guarantee test
	 * has actually run. Could have a counter to track how many times the loop
	 * has been entered and ensure that the number is monotonically incrementing.  
	 * And then it'll subject to integer overflow issue. To make things simple 
	 * straight forward, set a breakpoint at the end of the loop in prvRegisterCheck1() 
	 * and prvRegisterCheck2(). Make sure both can be hit. 
	 */
	if( uxRegTestError1 == 0 && uxRegTestError2 == 0 )
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
		/* Load register r0-r30 with known value. 
		 * r31 is used to first load immediate value then copy into r0-15. 
		 *
		 * LDI Rd,K
		 * Rd<--K (16 <= d <= 31, 0 <= K <= 255)
		 */
		asm(	"LDI	r31,	0x80"		);		
		asm( 	"MOV	r0,		r31"		);
		asm(	"LDI	r31,	0x81"		);
		asm( 	"MOV	r1,		r31"		);
		asm(	"LDI	r31,	0x82"		);
		asm( 	"MOV	r2,		r31"		);
		asm(	"LDI	r31,	0x83"		);
		asm( 	"MOV	r3,		r31"		);
		asm(	"LDI	r31,	0x84"		);
		asm( 	"MOV	r4,		r31"		);
		asm(	"LDI	r31,	0x85"		);
		asm( 	"MOV	r5,		r31"		);
		asm(	"LDI	r31,	0x86"		);
		asm( 	"MOV	r6,		r31"		);
		asm(	"LDI	r31,	0x87"		);
		asm( 	"MOV	r7,		r31"		);
		asm(	"LDI	r31,	0x88"		);
		asm( 	"MOV	r8,		r31"		);
		asm(	"LDI	r31,	0x89"		);
		asm( 	"MOV	r9,		r31"		);
		asm(	"LDI	r31,	0x8A"		);
		asm( 	"MOV	r10,	r31"		);
		asm(	"LDI	r31,	0x8B"		);
		asm( 	"MOV	r11,	r31"		);
		asm(	"LDI	r31,	0x8C"		);
		asm( 	"MOV	r12,	r31"		);
		asm(	"LDI	r31,	0x8D"		);
		asm( 	"MOV	r13,	r31"		);
		asm(	"LDI	r31,	0x8E"		);
		asm( 	"MOV	r14,	r31"		);
		asm(	"LDI	r31,	0x8F"		);
		asm( 	"MOV	r15,	r31"		);
		asm(	"LDI	r16,	0x90"		);
		asm(	"LDI	r17,	0x91"		);
		asm(	"LDI	r18,	0x92"		);
		asm(	"LDI	r19,	0x93"		);
		asm(	"LDI	r20,	0x94"		);
		asm(	"LDI	r21,	0x95"		);
		asm(	"LDI	r22,	0x96"		);
		asm(	"LDI	r23,	0x97"		);
		asm(	"LDI	r24,	0x98"		);
		asm(	"LDI	r25,	0x99"		);
		asm(	"LDI	r26,	0x9A"		);
		asm(	"LDI	r27,	0x9B"		);
		asm(	"LDI	r28,	0x9C"		);
		asm(	"LDI	r29,	0x9D"		);
		asm(	"LDI	r30,	0x9E"		);

		/* Check whether register r0-30 still contain known good values.
		 * If not, update uxRegTestError1 with the unique value. 
		 */
		asm(	"LDI	r31,	0x80"			);
		asm(	"CPSE	r31,	r0"				);
		asm(	"STS	uxRegTestError1, r0"	);
		asm(	"LDI	r31,	0x81"			);
		asm(	"CPSE	r31,	r1"				);
		asm(	"STS	uxRegTestError1, r1"	);
		asm(	"LDI	r31,	0x82"			);
		asm(	"CPSE	r31,	r2"				);
		asm(	"STS	uxRegTestError1, r2"	);
		asm(	"LDI	r31,	0x83"			);
		asm(	"CPSE	r31,	r3"				);
		asm(	"STS	uxRegTestError1, r3"	);
		asm(	"LDI	r31,	0x84"			);
		asm(	"CPSE	r31,	r4"				);
		asm(	"STS	uxRegTestError1, r4"	);
		asm(	"LDI	r31,	0x85"			);
		asm(	"CPSE	r31,	r5"				);
		asm(	"STS	uxRegTestError1, r5"	);
		asm(	"LDI	r31,	0x86"			);
		asm(	"CPSE	r31,	r6"				);
		asm(	"STS	uxRegTestError1, r6"	);
		asm(	"LDI	r31,	0x87"			);
		asm(	"CPSE	r31,	r7"				);
		asm(	"STS	uxRegTestError1, r7"	);
		asm(	"LDI	r31,	0x88"			);
		asm(	"CPSE	r31,	r8"				);
		asm(	"STS	uxRegTestError1, r8"	);
		asm(	"LDI	r31,	0x89"			);
		asm(	"CPSE	r31,	r9"				);
		asm(	"STS	uxRegTestError1, r9"	);
		asm(	"LDI	r31,	0x8A"			);
		asm(	"CPSE	r31,	r10"			);
		asm(	"STS	uxRegTestError1, r10"	);
		asm(	"LDI	r31,	0x8B"			);
		asm(	"CPSE	r31,	r11"			);
		asm(	"STS	uxRegTestError1, r11"	);
		asm(	"LDI	r31,	0x8C"			);
		asm(	"CPSE	r31,	r12"			);
		asm(	"STS	uxRegTestError1, r12"	);
		asm(	"LDI	r31,	0x8D"			);
		asm(	"CPSE	r31,	r13"			);
		asm(	"STS	uxRegTestError1, r13"	);
		asm(	"LDI	r31,	0x8E"			);
		asm(	"CPSE	r31,	r14"			);
		asm(	"STS	uxRegTestError1, r14"	);
		asm(	"LDI	r31,	0x8F"			);
		asm(	"CPSE	r31,	r15"			);
		asm(	"STS	uxRegTestError1, r15"	);
		asm(	"LDI	r31,	0x90"			);
		asm(	"CPSE	r31,	r16"			);
		asm(	"STS	uxRegTestError1, r16"	);
		asm(	"LDI	r31,	0x91"			);
		asm(	"CPSE	r31,	r17"			);
		asm(	"STS	uxRegTestError1, r17"	);
		asm(	"LDI	r31,	0x92"			);
		asm(	"CPSE	r31,	r18"			);
		asm(	"STS	uxRegTestError1, r18"	);
		asm(	"LDI	r31,	0x93"			);
		asm(	"CPSE	r31,	r19"			);
		asm(	"STS	uxRegTestError1, r19"	);
		asm(	"LDI	r31,	0x94"			);
		asm(	"CPSE	r31,	r20"			);
		asm(	"STS	uxRegTestError1, r20"	);
		asm(	"LDI	r31,	0x95"			);
		asm(	"CPSE	r31,	r21"			);
		asm(	"STS	uxRegTestError1, r21"	);
		asm(	"LDI	r31,	0x96"			);
		asm(	"CPSE	r31,	r22"			);
		asm(	"STS	uxRegTestError1, r22"	);
		asm(	"LDI	r31,	0x97"			);
		asm(	"CPSE	r31,	r23"			);
		asm(	"STS	uxRegTestError1, r23"	);
		asm(	"LDI	r31,	0x98"			);
		asm(	"CPSE	r31,	r24"			);
		asm(	"STS	uxRegTestError1, r24"	);
		asm(	"LDI	r31,	0x99"			);
		asm(	"CPSE	r31,	r25"			);
		asm(	"STS	uxRegTestError1, r25"	);
		asm(	"LDI	r31,	0x9A"			);
		asm(	"CPSE	r31,	r26"			);
		asm(	"STS	uxRegTestError1, r26"	);
		asm(	"LDI	r31,	0x9B"			);
		asm(	"CPSE	r31,	r27"			);
		asm(	"STS	uxRegTestError1, r27"	);
		asm(	"LDI	r31,	0x9C"			);
		asm(	"CPSE	r31,	r28"			);
		asm(	"STS	uxRegTestError1, r28"	);
		asm(	"LDI	r31,	0x9D"			);
		asm(	"CPSE	r31,	r29"			);
		asm(	"STS	uxRegTestError1, r29"	);
		asm(	"LDI	r31,	0x9E"			);
		asm(	"CPSE	r31,	r30"			);
		asm(	"STS	uxRegTestError1, r30"	);
		
		/* Give other tasks of the same priority a chance to run. */
		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

static void prvRegisterCheck2( void *pvParameters )
{
	( void ) pvParameters;

	for( ;; )
	{
		/* Load register r0-r30 with known value. 
		 * r31 is used to first load immediate value then copy into r0-15. 
		 *
		 * LDI Rd,K
		 * Rd<--K (16 <= d <= 31, 0 <= K <= 255)
		 */
		asm(	"LDI	r31,	0"		);		
		asm( 	"MOV	r0,		r31"	);
		asm(	"LDI	r31,	1"		);
		asm( 	"MOV	r1,		r31"	);
		asm(	"LDI	r31,	2"		);
		asm( 	"MOV	r2,		r31"	);
		asm(	"LDI	r31,	3"		);
		asm( 	"MOV	r3,		r31"	);
		asm(	"LDI	r31,	4"		);
		asm( 	"MOV	r4,		r31"	);
		asm(	"LDI	r31,	5"		);
		asm( 	"MOV	r5,		r31"	);
		asm(	"LDI	r31,	6"		);
		asm( 	"MOV	r6,		r31"	);
		asm(	"LDI	r31,	7"		);
		asm( 	"MOV	r7,		r31"	);
		asm(	"LDI	r31,	8"		);
		asm( 	"MOV	r8,		r31"	);
		asm(	"LDI	r31,	9"		);
		asm( 	"MOV	r9,		r31"	);
		asm(	"LDI	r31,	10"		);
		asm( 	"MOV	r10,	r31"	);
		asm(	"LDI	r31,	11"		);
		asm( 	"MOV	r11,	r31"	);
		asm(	"LDI	r31,	12"		);
		asm( 	"MOV	r12,	r31"	);
		asm(	"LDI	r31,	13"		);
		asm( 	"MOV	r13,	r31"	);
		asm(	"LDI	r31,	14"		);
		asm( 	"MOV	r14,	r31"	);
		asm(	"LDI	r31,	15"		);
		asm( 	"MOV	r15,	r31"	);
		asm(	"LDI	r16,	16"		);
		asm(	"LDI	r17,	17"		);
		asm(	"LDI	r18,	18"		);
		asm(	"LDI	r19,	19"		);
		asm(	"LDI	r20,	20"		);
		asm(	"LDI	r21,	21"		);
		asm(	"LDI	r22,	22"		);
		asm(	"LDI	r23,	23"		);
		asm(	"LDI	r24,	24"		);
		asm(	"LDI	r25,	25"		);
		asm(	"LDI	r26,	26"		);
		asm(	"LDI	r27,	27"		);
		asm(	"LDI	r28,	28"		);
		asm(	"LDI	r29,	29"		);
		asm(	"LDI	r30,	30"		);
		
		/* Check whether register r0-30 still contain known good values.
		 * If not, update uxRegTestError2 with the unique value. 
		 */
		asm(	"LDI	r31,	0"				);
		asm(	"CPSE	r31,	r0"				);
		asm(	"STS	uxRegTestError2, r0"	);
		asm(	"LDI	r31,	1"				);
		asm(	"CPSE	r31,	r1"				);
		asm(	"STS	uxRegTestError2, r1"	);
		asm(	"LDI	r31,	2"				);
		asm(	"CPSE	r31,	r2"				);
		asm(	"STS	uxRegTestError2, r2"	);
		asm(	"LDI	r31,	3"				);
		asm(	"CPSE	r31,	r3"				);
		asm(	"STS	uxRegTestError2, r3"	);
		asm(	"LDI	r31,	4"				);
		asm(	"CPSE	r31,	r4"				);
		asm(	"STS	uxRegTestError2, r4"	);
		asm(	"LDI	r31,	5"				);
		asm(	"CPSE	r31,	r5"				);
		asm(	"STS	uxRegTestError2, r5"	);
		asm(	"LDI	r31,	6"				);
		asm(	"CPSE	r31,	r6"				);
		asm(	"STS	uxRegTestError2, r6"	);
		asm(	"LDI	r31,	7"				);
		asm(	"CPSE	r31,	r7"				);
		asm(	"STS	uxRegTestError2, r7"	);
		asm(	"LDI	r31,	8"				);
		asm(	"CPSE	r31,	r8"				);
		asm(	"STS	uxRegTestError2, r8"	);
		asm(	"LDI	r31,	9"				);
		asm(	"CPSE	r31,	r9"				);
		asm(	"STS	uxRegTestError2, r9"	);
		asm(	"LDI	r31,	10"				);
		asm(	"CPSE	r31,	r10"			);
		asm(	"STS	uxRegTestError2, r10"	);
		asm(	"LDI	r31,	11"				);
		asm(	"CPSE	r31,	r11"			);
		asm(	"STS	uxRegTestError2, r11"	);
		asm(	"LDI	r31,	12"				);
		asm(	"CPSE	r31,	r12"			);
		asm(	"STS	uxRegTestError2, r12"	);
		asm(	"LDI	r31,	13"				);
		asm(	"CPSE	r31,	r13"			);
		asm(	"STS	uxRegTestError2, r13"	);
		asm(	"LDI	r31,	14"				);
		asm(	"CPSE	r31,	r14"			);
		asm(	"STS	uxRegTestError2, r14"	);
		asm(	"LDI	r31,	15"				);
		asm(	"CPSE	r31,	r15"			);
		asm(	"STS	uxRegTestError2, r15"	);
		asm(	"LDI	r31,	16"				);
		asm(	"CPSE	r31,	r16"			);
		asm(	"STS	uxRegTestError2, r16"	);
		asm(	"LDI	r31,	17"				);
		asm(	"CPSE	r31,	r17"			);
		asm(	"STS	uxRegTestError2, r17"	);
		asm(	"LDI	r31,	18"				);
		asm(	"CPSE	r31,	r18"			);
		asm(	"STS	uxRegTestError2, r18"	);
		asm(	"LDI	r31,	19"				);
		asm(	"CPSE	r31,	r19"			);
		asm(	"STS	uxRegTestError2, r19"	);
		asm(	"LDI	r31,	20"				);
		asm(	"CPSE	r31,	r20"			);
		asm(	"STS	uxRegTestError2, r20"	);
		asm(	"LDI	r31,	21"				);
		asm(	"CPSE	r31,	r21"			);
		asm(	"STS	uxRegTestError2, r21"	);
		asm(	"LDI	r31,	22"				);
		asm(	"CPSE	r31,	r22"			);
		asm(	"STS	uxRegTestError2, r22"	);
		asm(	"LDI	r31,	23"				);
		asm(	"CPSE	r31,	r23"			);
		asm(	"STS	uxRegTestError2, r23"	);
		asm(	"LDI	r31,	24"				);
		asm(	"CPSE	r31,	r24"			);
		asm(	"STS	uxRegTestError2, r24"	);
		asm(	"LDI	r31,	25"				);
		asm(	"CPSE	r31,	r25"			);
		asm(	"STS	uxRegTestError2, r25"	);
		asm(	"LDI	r31,	26"				);
		asm(	"CPSE	r31,	r26"			);
		asm(	"STS	uxRegTestError2, r26"	);
		asm(	"LDI	r31,	27"				);
		asm(	"CPSE	r31,	r27"			);
		asm(	"STS	uxRegTestError2, r27"	);
		asm(	"LDI	r31,	28"				);
		asm(	"CPSE	r31,	r28"			);
		asm(	"STS	uxRegTestError2, r28"	);
		asm(	"LDI	r31,	29"				);
		asm(	"CPSE	r31,	r29"			);
		asm(	"STS	uxRegTestError2, r29"	);
		asm(	"LDI	r31,	30"				);
		asm(	"CPSE	r31,	r30"			);
		asm(	"STS	uxRegTestError2, r30"	);
		
		/* Give other tasks of the same priority a chance to run. */
		taskYIELD();
	}
}
