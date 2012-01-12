#ifndef TIMER_TEST_H
#define TIMER_TEST_H

#define tmrtestNUM_TIMERS 15


extern portTickType xTickCount;
extern xTaskHandle pxCurrentTCB;
extern portTickType xNumOfOverflows;

static void vTimerTest_Initialise( void );
static portBASE_TYPE xTimerTest1_xTimeStartAndResetWakeTimeCalculation( void );
portBASE_TYPE xTimerTest2_xTestFreeRunningBehaviour( unsigned portBASE_TYPE uxPeriodMultiplier );

static void prvCheckServiceTaskBehaviour( portBASE_TYPE x, portBASE_TYPE xExpireTimeHasOverflowed, portBASE_TYPE xTickCountOverflowed );

static void prvTestFailed( void );

xTIMER *xAutoReloadTimers[ tmrtestNUM_TIMERS ];
unsigned portBASE_TYPE uxAutoReloadTimerCounters[ tmrtestNUM_TIMERS ];
portBASE_TYPE xTestStatus = pdPASS;
xTaskHandle xTestTask1 = NULL, xTestTask2 = NULL;

struct xTestData
{
	portTickType xStartTickCount;
	portTickType xTimerPeriod;
	portTickType xTickIncrementBetweenCommandAndProcessing;
	portTickType xExpectedCalculatedExpiryTime;
	xList * pxExpectedList;
	unsigned portBASE_TYPE uxExpectedCallbackCount;
};

const struct xTestData xTestCase[] =
{
	/* xStartTickCount,		xTimerPeriod,		Tck Inc,	Expected Expire Time,		Expected list,   Expected callback count, Second tick inc */

	/* Test cases when the command to start a timer and the processing of the
	start command execute without the tick count incrementing in between. */
	{ portMAX_DELAY - 8,	2,					0,		( portMAX_DELAY - 8 ) + 2,			&xActiveTimerList1, 0 },		/* Expire before an overflow. */
	{ portMAX_DELAY - 8,	8,					0,		( portMAX_DELAY - 8 ) + 8,			&xActiveTimerList1, 0 },		/* Expire immediately before and overflow. */
	{ portMAX_DELAY - 8,	9,					0,		0,									&xActiveTimerList2, 0 },		/* Expire on an overflow. */
	{ portMAX_DELAY - 8,	portMAX_DELAY,		0,		( ( portMAX_DELAY - 8 ) - 1 ),		&xActiveTimerList2, 0 },		/* Delay for the longest possible time. */
	{ portMAX_DELAY,		portMAX_DELAY,		0,		( portMAX_DELAY - 1 ),				&xActiveTimerList2, 0 },		/* Delay for the longest possible time starting from the maximum tick count. */
	{ 0,					portMAX_DELAY,		0,		( portMAX_DELAY ),					&xActiveTimerList1, 0 },		/* Delay for the maximum ticks, starting with from the minimum tick count. */

	/* Test cases when the command to start a timer and the processing of the
	start command execute at different tick count values. */
	{ portMAX_DELAY - 8,	2,					1,		( portMAX_DELAY - 8 ) + 2,			&xActiveTimerList1, 0 },		/* The expire time does not overflow, and the tick count does not overflow between the command and processing the command. */
	{ portMAX_DELAY - 8,	8,					2,		( portMAX_DELAY - 8 ) + 8,			&xActiveTimerList1, 0 },		/* The expire time does not overflow but is on the portMAX_DELAY limit, and the tick count does not overflow between the command and processing the command. */
	{ portMAX_DELAY - 8,	9,					3,		0,									&xActiveTimerList2, 0 },		/* The expire time overflows to 0, and the tick count does not overflow between the command and processing the command. */
	{ portMAX_DELAY - 2,	9,					1,		( portMAX_DELAY - 2 ) + 9,			&xActiveTimerList2, 0 },		/* The expire time overflows, but the tick count does not overflow between the command and processing the command. */
	{ portMAX_DELAY - 2,	9,					3,		( portMAX_DELAY - 2 ) + 9,			&xActiveTimerList2, 0 },		/* The timer overflows between the command and processing the command.  The expire time also overflows. */

	/* Add tests where the timer should have expired by the time the command is processed. */
	{ 10,					9,					10,		( 10 + ( 2 * 9 ) ),					&xActiveTimerList1, 1 },		/* Nothing overflows, but the time between the timer being set and the command being processed is greater than the timers expiry time.  The timer should get processed immediately, so the expected expire time is twice the period as the timer will get auto-reloaded. */
	{ portMAX_DELAY - 2,	9,					10,		( portMAX_DELAY - 2 ) + ( 2 * 9 ),	&xActiveTimerList2, 1 },		/* The timer overflows between the command and processing the command.  The expire time also overflows and the number of ticks that occur between the command and the processing exceeds the timer expiry period. The timer should get processed immediately, so the expected expire time is twice the period as the timer will get auto-reloaded.*/
	{ portMAX_DELAY - 2,	9,					9,		( portMAX_DELAY - 2 ) + ( 2 * 9 ),	&xActiveTimerList2, 1 },		/* The timer overflows between the command and processing the command.  The expire time also overflows and the number of ticks between command and processing equals the timer expiry period. The timer should get processed immediately, so the expected expire time is twice the period as the timer will get auto-reloaded.*/

	{ portMAX_DELAY - 20,	9,					21,		( portMAX_DELAY - 20 ) + ( 3 * 9 ),	&xActiveTimerList2, 2 },		/* The tick count has overflowed but the timer expire time has not overflowed.  The tick count overflows to 0.  The timer should get processed immediately, so the expected expire time is twice the period as the timer will get auto-reloaded.*/
	{ portMAX_DELAY - 20,	9,					22,		( portMAX_DELAY - 20 ) + ( 3 * 9 ),	&xActiveTimerList2, 2 },		/* The tick count has overflowed but the timer expire time has not overflowed.  The tick count overflows to greater than 0. The timer should get processed immediately, so the expected expire time is twice the period as the timer will get auto-reloaded.*/
	{ portMAX_DELAY - 5,	2,					20,		( portMAX_DELAY - 5 ) + ( 11 * 2 ),	&xActiveTimerList2, 10 },		/* The tick and expire time overflow, but the first expire time overflow results in a time that is less than the tick count. */
};

typedef struct tskTaskControlBlockx
{
	volatile portSTACK_TYPE	*pxTopOfStack;		/*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE STRUCT. */

	#if ( portUSING_MPU_WRAPPERS == 1 )
		xMPU_SETTINGS xMPUSettings;				/*< The MPU settings are defined as part of the port layer.  THIS MUST BE THE SECOND MEMBER OF THE STRUCT. */
	#endif	
	
	xListItem				xGenericListItem;	/*< List item used to place the TCB in ready and blocked queues. */
	xListItem				xEventListItem;		/*< List item used to place the TCB in event lists. */
	unsigned portBASE_TYPE	uxPriority;			/*< The priority of the task where 0 is the lowest priority. */
	portSTACK_TYPE			*pxStack;			/*< Points to the start of the stack. */
	signed char				pcTaskName[ configMAX_TASK_NAME_LEN ];/*< Descriptive name given to the task when created.  Facilitates debugging only. */

	#if ( portSTACK_GROWTH > 0 )
		portSTACK_TYPE *pxEndOfStack;			/*< Used for stack overflow checking on architectures where the stack grows up from low memory. */
	#endif

	#if ( portCRITICAL_NESTING_IN_TCB == 1 )
		unsigned portBASE_TYPE uxCriticalNesting;
	#endif

	#if ( configUSE_TRACE_FACILITY == 1 )
		unsigned portBASE_TYPE	uxTCBNumber;	/*< This is used for tracing the scheduler and making debugging easier only. */
	#endif

	#if ( configUSE_MUTEXES == 1 )
		unsigned portBASE_TYPE uxBasePriority;	/*< The priority last assigned to the task - used by the priority inheritance mechanism. */
	#endif

	#if ( configUSE_APPLICATION_TASK_TAG == 1 )
		pdTASK_HOOK_CODE pxTaskTag;
	#endif

	#if ( configGENERATE_RUN_TIME_STATS == 1 )
		unsigned long ulRunTimeCounter;		/*< Used for calculating how much CPU time each task is utilising. */
	#endif

} tskTCBx;

/*-----------------------------------------------------------*/

static void vAutoReloadTimerCallback( xTIMER *pxTimer )
{
portBASE_TYPE xTimerID = ( portBASE_TYPE ) pxTimer->pvTimerID;

	if( xTimerID < tmrtestNUM_TIMERS )
	{
		( uxAutoReloadTimerCounters[ xTimerID ] )++;
	}
	else
	{
		prvTestFailed();
	}
}
/*-----------------------------------------------------------*/

static void vTimerTest_Initialise( void )
{
portBASE_TYPE xTimerNumber;
extern void prvInitialiseTaskLists( void );
extern portBASE_TYPE xSchedulerRunning;

	prvInitialiseTaskLists();
	xTimerQueue = NULL;
	xSchedulerRunning = pdTRUE;

	for( xTimerNumber = 0; xTimerNumber < tmrtestNUM_TIMERS; xTimerNumber++ )
	{
		/* Delete any existing timers. */
		if( xAutoReloadTimers[ xTimerNumber ] != NULL )
		{
			vPortFree( xAutoReloadTimers[ xTimerNumber ] );
		}

		/* Create new autoreload timers. */
		xAutoReloadTimers[ xTimerNumber ] = xTimerCreate( "Timer", 0xffff, pdTRUE, ( void * ) xTimerNumber, vAutoReloadTimerCallback );
		uxAutoReloadTimerCounters[ xTimerNumber ] = 0;
		if( xAutoReloadTimers == NULL )
		{
			prvTestFailed();
		}
	}

	/* Initialise lists so they are empty. */
	vListInitialise( &xActiveTimerList1 );
	vListInitialise( &xActiveTimerList2 );

	/* Call prvSampleTimeNow with a tick count of zero so it sets its 
	internal static "last time" variable to zero. */
	xTickCount = 0;
	xNumOfOverflows = 0;
	prvSampleTimeNow( &xTimerNumber );

	/* Initialise the list pointers in case prvSampleTimeNow() changed them. */
	pxCurrentTimerList = &xActiveTimerList1;
	pxOverflowTimerList = &xActiveTimerList2;

//	if( xTestTask1 == NULL )
	{
		xTaskCreate( (pdTASK_CODE)prvTestFailed, "Task1",  configMINIMAL_STACK_SIZE, NULL, 0, &xTestTask1 );
	}

//	if( xTestTask2 == NULL )
	{
		xTaskCreate( (pdTASK_CODE)prvTestFailed, "Task1",  configMINIMAL_STACK_SIZE, NULL, 0, &xTestTask2 );
	}

	pxCurrentTCB = xTestTask1;
}
/*-----------------------------------------------------------*/

static void prvTestFailed( void )
{
static unsigned long ulFailures = 0;

	ulFailures++;
	xTestStatus = pdFAIL;
}
/*-----------------------------------------------------------*/

static void prvCheckServiceTaskBehaviour( portBASE_TYPE x, portBASE_TYPE xExpireTimeHasOverflowed, portBASE_TYPE xTickCountOverflowed )
{
portBASE_TYPE xListWasEmpty;
portTickType xNextExpireTime;
extern xList * volatile pxOverflowDelayedTaskList, *pxDelayedTaskList;
extern xList pxReadyTasksLists[];

	xListWasEmpty = portMAX_DELAY;
	xNextExpireTime = prvGetNextExpireTime( &xListWasEmpty );

	/* If the timer expire time has overflowed it should be present in the overflow 
	list of active timers, unless the tick count has also overflowed and the expire
	time has not passed.  If the expire time has not overflowed it should be 
	present in the current list of active timers.  Either way, its expire time should 
	equal the expected expire time. */
	if( ( xExpireTimeHasOverflowed == pdTRUE ) && ( xTickCountOverflowed == pdFALSE ) )
	{	
		/* The timer will be in the overflow list, so prvGetNextExpireTime()
		should not have found it, but instead returned an expire time that
		will ensure the timer service task will unblock when the lists need
		switching. */
		if( ( xNextExpireTime != 0 ) || ( xListWasEmpty == pdFALSE ) )
		{
			prvTestFailed();
		}
	}
	else
	{
		if( ( xNextExpireTime != xTestCase[ x ].xExpectedCalculatedExpiryTime ) || ( xListWasEmpty != pdFALSE ) )
		{
			prvTestFailed();
		}
	}

	prvProcessTimerOrBlockTask( xNextExpireTime, xListWasEmpty );

	/* Has the timer expired the expected number of times? */
	if( uxAutoReloadTimerCounters[ 0 ] != xTestCase[ x ].uxExpectedCallbackCount )
	{
		prvTestFailed();
	}

	/* The task should now be blocked.  It should only appear in the overflow
	delayed task list if xNextExpireTime is equal to 0. */
	if( xNextExpireTime == 0 )
	{
		if( listIS_CONTAINED_WITHIN( pxOverflowDelayedTaskList, &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) ) == pdFALSE )
		{
			prvTestFailed();
		}

		if( listGET_LIST_ITEM_VALUE( &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) ) != 0 )
		{
			prvTestFailed();
		}
	}
	else
	{
		if( listIS_CONTAINED_WITHIN( pxDelayedTaskList, &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) ) == pdFALSE )
		{
			prvTestFailed();
		}

		if( listGET_LIST_ITEM_VALUE( &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) ) != xTestCase[ x ].xExpectedCalculatedExpiryTime )
		{
			prvTestFailed();
		}
	}

	/* The timer should have be re-loaded, and still be referenced from one
	or other of the active lists. */
	if( listGET_LIST_ITEM_VALUE( &( xAutoReloadTimers[ 0 ]->xTimerListItem ) ) != xTestCase[ x ].xExpectedCalculatedExpiryTime )
	{
		prvTestFailed();
	}
	if( listIS_CONTAINED_WITHIN( NULL, &( xAutoReloadTimers[ 0 ]->xTimerListItem ) ) == pdTRUE )
	{
		prvTestFailed();
	}

	/* Move the task back to the ready list from the delayed list. */
	vListRemove( &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) );
	vListInsertEnd( ( xList * ) &( pxReadyTasksLists[ 0 ] ), &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) );
}
/*-----------------------------------------------------------*/

static portBASE_TYPE xTimerTest1_xTimeStartAndResetWakeTimeCalculation( void )
{
portBASE_TYPE x, xListWasEmpty;
portTickType xNextExpireTime;

	if( sizeof( portTickType ) != 2 )
	{
		/* This test should be performed using 16bit ticks. */
		prvTestFailed();
	}

	for( x = 0; x < ( sizeof( xTestCase ) / sizeof( struct xTestData ) ); x++ )
	{
		/* Set everything back to its start condition. */
		vTimerTest_Initialise();

		/* Load the tick count with the test case data. */
		xTickCount = xTestCase[ x ].xStartTickCount;

		/* Query the timers list to see if it contains any timers, and if so,
		obtain the time at which the next timer will expire.  The list should be
		empty, so 0 should be returned (to cause the task to unblock when a
		tick overflow occurs.  Likewise xListWasEmpty should be set to pdTRUE. */
		xListWasEmpty = portMAX_DELAY;
		xNextExpireTime = prvGetNextExpireTime( &xListWasEmpty );

		if( ( xListWasEmpty != pdTRUE ) || ( xNextExpireTime != ( portTickType ) 0 ) )
		{
			prvTestFailed();
		}



		/* Call prvProcessReceivedCommands() just so the code under test knows
		what the tick count is in the pre-condition state. */
		prvProcessReceivedCommands();

		xAutoReloadTimers[ 0 ]->xTimerPeriodInTicks = xTestCase[ x ].xTimerPeriod;
		xTimerStart( xAutoReloadTimers[ 0 ], 0 );

		/* Move the tick count on to the time at which the command should be 
		processed. */
		xTickCount += xTestCase[ x ].xTickIncrementBetweenCommandAndProcessing;

		/* Process the sent command with the updated tick count. */
		prvProcessReceivedCommands();

		if( listGET_LIST_ITEM_VALUE( &( xAutoReloadTimers[ 0 ]->xTimerListItem ) ) != xTestCase[ x ].xExpectedCalculatedExpiryTime )
		{
			prvTestFailed();
		}
		if( listIS_CONTAINED_WITHIN( xTestCase[ x ].pxExpectedList, &( xAutoReloadTimers[ 0 ]->xTimerListItem ) ) == pdFALSE )
		{
			prvTestFailed();
		}
		if( uxAutoReloadTimerCounters[ 0 ] != xTestCase[ x ].uxExpectedCallbackCount )
		{
			prvTestFailed();
		}

		if( xTickCount < xTestCase[ x ].xStartTickCount ) /* The tick count has overflowed */
		{
			if(  xTestCase[ x ].pxExpectedList == &xActiveTimerList2 ) /* The timer expire time has overflowed. */
			{
				if( xTestCase[ x ].xExpectedCalculatedExpiryTime <= xTickCount ) /* The timer expire time has passed  */
				{
					/* The expire time should never have passed when here is
					reached because the timer whould have been processed enough
					times to make the expire time catch up. */
					prvTestFailed();
				}
				else /* The timer expire time has not passed. */
				{
					prvCheckServiceTaskBehaviour( x, pdTRUE, pdTRUE );
				}
			}
			else /* The timer expire time has not overflowed. */
			{
				/* If the timer expire time has not overflowed but the tick count has 
				overflowed, then the timer expire time must have been passed.  The 
				expire time should never have passed when here is reached because 
				the timer whould have been processed enough	times to make the expire 
				time catch up. */
				prvTestFailed();
			}
		}
		else /* The tick count has not overflowed. */
		{
			if( xTestCase[ x ].pxExpectedList == &xActiveTimerList2 ) /* The timer expire time has overflowed */
			{
				/* If the expire time has overflowed, but the tick count has not
				overflowed, then the timer expire time cannot have been passed. */
				prvCheckServiceTaskBehaviour( x, pdTRUE, pdFALSE );
			}
			else /* The timer expire time has not overflowed. */
			{
				if( xTickCount >= xTestCase[ x ].xExpectedCalculatedExpiryTime ) /* The timer expire time has passed */
				{
					/* The expire time should never have passed when here is
					reached because the timer whould have been processed enough
					times to make the expire time catch up. */
					prvTestFailed();
				}
				else /* The timer expire time has not passed. */
				{
					prvCheckServiceTaskBehaviour( x, pdFALSE, pdFALSE );
				}
			}
		}
	}

	return xTestStatus;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xTimerTest2_xTestFreeRunningBehaviour( unsigned portBASE_TYPE uxPeriodMultiplier )
{
unsigned portBASE_TYPE uxExpectedIncrements, x, uxMix = 0, uxPeriod;
const unsigned portBASE_TYPE uxMaxIterations = 0x1fffff;
extern xList pxReadyTasksLists[];
portTickType xNextExpireTime;
portBASE_TYPE xListWasEmpty;
extern xTaskHandle pxCurrentTCB;

	if( sizeof( portTickType ) != 2 )
	{
		/* This test should be performed using 16bit ticks. */
		prvTestFailed();
	}

	/* Initialise the test.  This will create tmrtestNUM_TIMERS timers. */
	vTimerTest_Initialise();

	/* Give each timer a period, then start it running. */
	for( x = 0; x < tmrtestNUM_TIMERS; x++ )
	{
		uxPeriod = ( x + ( unsigned portBASE_TYPE ) 1 ) * uxPeriodMultiplier;
		xTimerChangePeriod( xAutoReloadTimers[ x ], ( portTickType ) uxPeriod, 0 );
		xTimerStart( xAutoReloadTimers[ x ], 0 );
		prvProcessReceivedCommands();
	}

	xTickCount = 1;
	x = 1;

	/* Simulate the task running. */
	while( x <= uxMaxIterations )
	{
		/* Query the timers list to see if it contains any timers, and if so,
		obtain the time at which the next timer will expire. */
		xNextExpireTime = prvGetNextExpireTime( &xListWasEmpty );

		/* It is legitimate for tick increments to occur here. */
		if( ( uxMix < 2 ) && ( x < uxMaxIterations - 5 ) )
		{
			vTaskIncrementTick();
			x++;
			vTaskIncrementTick();
			x++;
			vTaskIncrementTick();
			x++;
		}

		/* If a timer has expired, process it.  Otherwise, block this task
		until either a timer does expire, or a command is received. */
		prvProcessTimerOrBlockTask( xNextExpireTime, xListWasEmpty );
		
		/* If the task blocked, increment the tick until it unblocks. */
		while( listIS_CONTAINED_WITHIN( ( xList * ) &( pxReadyTasksLists[ 0 ] ), &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) ) == pdFALSE )
		{
			if( ( uxMix == 1 ) && ( x < ( uxMaxIterations + 3 ) ) )
			{
				vTaskIncrementTick();
				x++;
				vTaskIncrementTick();
				x++;
				vTaskIncrementTick();
				x++;
			}
			if( ( uxMix == 2 ) && ( x < ( uxMaxIterations + 2 ) ) )
			{
				vTaskIncrementTick();
				x++;
				vTaskIncrementTick();
				x++;
			}
			else
			{
				vTaskIncrementTick();
				x++;
			}
		}

		uxMix++;
		if( uxMix > 8 )
		{
			uxMix = 0;
		}

		/* Make sure time does not go past that expected. */
		if( x > uxMaxIterations )
		{
			xTickCount -= ( portTickType ) ( x - uxMaxIterations );
		}

		/* Empty the command queue. */
		prvProcessReceivedCommands();		
	}

	/* Catch up with the tick count, if it was incremented more than once in one
	go. */
	xNextExpireTime = prvGetNextExpireTime( &xListWasEmpty );
	prvProcessTimerOrBlockTask( xNextExpireTime, xListWasEmpty );
		
	/* This time, if the task blocked, there is nothing left to do.  If it didn't
	block then empty the command queue for good measure. */
	if( listIS_CONTAINED_WITHIN( ( xList * ) &( pxReadyTasksLists[ 0 ] ), &( ( ( tskTCBx * ) pxCurrentTCB )->xGenericListItem ) ) != pdFALSE )
	{
		/* Empty the command queue. */
		prvProcessReceivedCommands();		
	}

	/* Check each timer has incremented the expected number of times. */
	for( x = 0; x < tmrtestNUM_TIMERS; x++ )
	{
		uxPeriod = ( x + ( unsigned portBASE_TYPE ) 1 ) * uxPeriodMultiplier;
		uxExpectedIncrements = ( uxMaxIterations / ( unsigned portBASE_TYPE ) uxPeriod );
	
		if( ( uxExpectedIncrements - uxAutoReloadTimerCounters[ x ] ) > 1 )
		{
			prvTestFailed();
		}
	}

	return xTestStatus;
}

/*-----------------------------------------------------------*/

void vRunTimerModuleTests( void )
{
unsigned long x;

	xTimerTest1_xTimeStartAndResetWakeTimeCalculation();

	for( x = 1; x < 1000; x++ )
	{
		xTimerTest2_xTestFreeRunningBehaviour( x );
	}

	for( ;; );
}

#endif TIMER_TEST_H

