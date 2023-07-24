// Copyright (c) 2020, XMOS Ltd, All rights reserved

/*
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so they get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
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
BaseType_t xRegTestError = pdFALSE;

/*-----------------------------------------------------------*/

void vStartRegTestTasks( UBaseType_t uxPriority )
{
    xTaskCreate( prvRegisterCheck1, "Reg1", configMINIMAL_STACK_SIZE, NULL, uxPriority, NULL );
    xTaskCreate( prvRegisterCheck2, "Reg2", configMINIMAL_STACK_SIZE, NULL, uxPriority, NULL );
}
/*-----------------------------------------------------------*/

BaseType_t xAreRegTestTasksStillRunning( void )
{
BaseType_t xReturn;

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
    prvRegisterCheck_asm1();
    xRegTestError = pdTRUE;
    for(;;);
    /* If we get here, then the check has failed */
}

static void prvRegisterCheck2( void *pvParameters )
{
	( void ) pvParameters;
    prvRegisterCheck_asm2();
    xRegTestError = pdTRUE;
    for(;;);
    /* If we get here, then the check has failed */
}

