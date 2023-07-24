// Copyright (c) 2019, XMOS Ltd, All rights reserved

#include <stdlib.h>

#include "FreeRTOS.h"
#include "task.h"
#include <xcore/chanend.h>

#include "limits.h"
#include "testing_main.h"

/* Includes for actual tests */
#include "AbortDelay.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "countsem.h"
#include "blocktim.h"
#include "death.h"
#include "EventGroupsDemo.h"
#include "flop.h"
#include "GenQTest.h"
#include "integer.h"
#include "IntQueue.h"
#include "IntSemTest.h"
#include "MessageBufferDemo.h"
#include "partest.h"
#include "PollQ.h"
#include "QPeek.h"
#include "QueueOverwrite.h"
#include "QueueSet.h"
#include "QueueSetPolling.h"
#include "recmutex.h"
#include "semtest.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"
#include "TaskNotify.h"
#include "TaskNotifyArray.h"
#include "TimerDemo.h"
#include "regtest.h"

void vParTestInitialiseXCORE( int tile, chanend_t xTile0Chan, chanend_t xTile1Chan, chanend_t xTile2Chan, chanend_t xTile3Chan );
#define vParTestInitialise vParTestInitialiseXCORE

/* Flag for errors occuring locally */
static BaseType_t xMallocError = pdFALSE;
static BaseType_t xIdleError = pdFALSE;
static BaseType_t xStackOverflowError = pdFALSE;

/* The xcore tile this instance is running on */
static int tile_g;

/* Idle hook counter */
static unsigned long ulCnt = 0;

#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	/*
	* The 'Check' task function.  Which verifies that no errors are present.
	*/
	static void vErrorChecks( void *pvParameters );
#endif

#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	/*
	* The task that implements the Blinky demo.
	*/
	static void vBlinkyDemo( void *pvParameters );
#endif

/*
 * The idle task hook - in which the integer task is implemented.  See the
 * explanation at the top of the file.
 */
void vApplicationIdleHook( void );

#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	/*
	* Checks the unique counts of other tasks to ensure they are still operational.
	*/
	static uint32_t prvCheckTasks( int tile, uint32_t ulErrorFound );
#endif

/*
 * Setup the hardware.
 */
static void prvSetupHardware( int tile, chanend_t xTile0Chan, chanend_t xTile1Chan, chanend_t xTile2Chan, chanend_t xTile3Chan );

/*-----------------------------------------------------------*/

void vApplicationGetIdleTaskMemory(StaticTask_t **ppxIdleTaskTCBBuffer,
                                    StackType_t **ppxIdleTaskStackBuffer,
                                    uint32_t *pulIdleTaskStackSize )
{
	static StaticTask_t xIdleTaskTCB;
	static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

    *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

    *ppxIdleTaskStackBuffer = uxIdleTaskStack;

    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}

/*-----------------------------------------------------------*/

void vApplicationGetTimerTaskMemory(StaticTask_t **ppxTimerTaskTCBBuffer,
                                    		StackType_t **ppxTimerTaskStackBuffer,
                                    		uint32_t *pulTimerTaskStackSize )
{
	static StaticTask_t xTimerTaskTCB;
	static StackType_t uxTimerTaskStack[ configMINIMAL_STACK_SIZE ];

    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

    *ppxTimerTaskStackBuffer = uxTimerTaskStack;

    *pulTimerTaskStackSize = configMINIMAL_STACK_SIZE;
}

/*-----------------------------------------------------------*/

int c_main( int tile, chanend_t xTile0Chan, chanend_t xTile1Chan, chanend_t xTile2Chan, chanend_t xTile3Chan )
{
	prvSetupHardware( tile, xTile0Chan, xTile1Chan, xTile2Chan, xTile3Chan );

	tile_g = tile;

	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		switch( tile )
		{
			case 0:
				xTaskCreate( vBlinkyDemo, "Blinky", portTASK_STACK_DEPTH( vBlinkyDemo ), &tile, tskIDLE_PRIORITY, NULL );
				break;
			case 1:
				xTaskCreate( vBlinkyDemo, "Blinky", portTASK_STACK_DEPTH( vBlinkyDemo ), &tile, tskIDLE_PRIORITY + 1, NULL );
				break;
			default:
				_Exit(0);	/* Invalid tile */
				break;
		}
	}
	#else
	{
		/* Create the standard demo tasks */
		switch( tile )
		{
			case 0:
				/* Tasks to only run on tile 0 go here */
				#if( testingmainENABLE_ABORT_DELAY_TASKS == 1 )
					vCreateAbortDelayTasks();
				#endif

				#if( testingmainENABLE_BLOCKING_QUEUE_TASKS == 1 )
					vStartBlockingQueueTasks( mainBLOCKING_Q_TASKS_PRIORITY );
				#endif

				#if( testingmainENABLE_BLOCK_TIME_TASKS == 1 )
					vCreateBlockTimeTasks();
				#endif

				#if( testingmainENABLE_COUNT_SEMAPHORE_TASKS == 1 )
					vStartCountingSemaphoreTasks();
				#endif

				#if( testingmainENABLE_DYNAMIC_PRIORITY_TASKS == 1 )
					vStartDynamicPriorityTasks();
				#endif

				#if( testingmainENABLE_EVENT_GROUP_TASKS == 1 )
					vStartEventGroupTasks();
				#endif

				#if( testingmainENABLE_INTERRUPT_QUEUE_TASKS == 1 )
					vStartInterruptQueueTasks();
				#endif

				#if( testingmainENABLE_FLOP_MATH_TASKS == 1 )
					vStartMathTasks( mainFLOP_TASKS_PRIORITY );
				#endif

				#if( testingmainENABLE_INT_MATH_TASKS == 1 )
					vStartIntegerMathTasks( mainINT_MATH_PRIORITY );
				#endif
				/* End tile 0 tasks */
	#if ( testingmainNUM_TILES > 1 )
				break;
			case 1:
	#endif
				/* Tasks to only run on tile 1 go here,
				but will run on tile 0 if tiles < 2 */

				#if( testingmainENABLE_GENERIC_QUEUE_TASKS == 1 )
					vStartGenericQueueTasks( mainGENERIC_Q_TASKS_PRIORITY );
				#endif

				#if( testingmainENABLE_INTERRUPT_SEMAPHORE_TASKS == 1 )
					vStartInterruptSemaphoreTasks();
				#endif

				#if( testingmainENABLE_MESSAGE_BUFFER_TASKS == 1 )
					vStartMessageBufferTasks( mainMESSAGE_BUFFER_STACK_SIZE );
				#endif

				#if( testingmainENABLE_POLLED_QUEUE_TASKS == 1 )
					vStartPolledQueueTasks( mainPOLLED_QUEUE_TASKS_PRIORITY );
				#endif

				#if( testingmainENABLE_QUEUE_PEEK_TASKS == 1 )
					vStartQueuePeekTasks();
				#endif

				#if( testingmainENABLE_QUEUE_OVERWRITE_TASKS == 1 )
					vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_TASKS_PRIORITY );
				#endif

				#if( testingmainENABLE_QUEUE_SET_TASKS == 1 )
					vStartQueueSetTasks();
				#endif

				#if( testingmainENABLE_QUEUE_SET_POLLING_TASKS == 1 )
					vStartQueueSetPollingTask();
				#endif

				#if( testingmainENABLE_RECURSIVE_MUTEX_TASKS == 1 )
					vStartRecursiveMutexTasks();
				#endif

				#if( testingmainENABLE_SEMAPHORE_TASKS == 1 )
					vStartSemaphoreTasks( mainSEMAPHORE_TASKS_PRIORITY );
				#endif

				#if( testingmainENABLE_STREAMBUFFER_TASKS == 1 )
					vStartStreamBufferTasks();
				#endif

				#if( testingmainENABLE_STREAMBUFFER_INTERRUPT_TASKS == 1 )
					vStartStreamBufferInterruptDemo();
				#endif

				#if( testingmainENABLE_TASK_NOTIFY_TASKS == 1 )
					vStartTaskNotifyTask();
				#endif

				#if( testingmainENABLE_TASK_NOTIFY_ARRAY_TASKS == 1 )
					vStartTaskNotifyArrayTask();
				#endif

				#if( testingmainENABLE_TIMER_DEMO_TASKS == 1 )
					vStartTimerDemoTask( mainTIMER_DEMO_TASK_FREQ );
				#endif

				/* End tile 1 tasks */
				break;
			default:
				_Exit(0);	/* Invalid tile */
				break;
		}

		/* Tasks below here should be run on every tile */
		#if( testingmainENABLE_REG_TEST_TASKS == 1 )
			vStartRegTestTasks( mainREGTEST_PRIORITY );
		#endif

		/* Start the locally defined tasks.  There is also a task implemented as
		the idle hook. */
		xTaskCreate( vErrorChecks, "Check", portTASK_STACK_DEPTH( vErrorChecks ), &tile, mainCHECK_TASK_PRIORITY, NULL );

		/* Must be the last demo created. */
		#if( testingmainENABLE_DEATH_TASKS == 1 )
			vCreateSuicidalTasks( mainDEATH_PRIORITY );
		#endif
	}
	#endif /* #if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 ) */

	/* All the tasks have been created - start the scheduler. */
	rtos_printf( "Starting Scheduler\n" );
	vTaskStartScheduler();

	/* Should not reach here! */
	for( ;; );
}

/*-----------------------------------------------------------*/

#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	static void vBlinkyDemo( void *pvParameters )
	{
	int tile = ( ( int * ) pvParameters )[0];

		for( ;; )
		{
			/* Wait for a second. */
			vTaskDelay( pdMS_TO_TICKS( 1000 ));

			/* Toggle the LED each cycle round. */
			vParTestToggleLED( tile );
		}
	}
#endif

/*-----------------------------------------------------------*/

#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	static void vErrorChecks( void *pvParameters )
	{
	TickType_t xDelayPeriod = mainCHECK_PERIOD;
	TickType_t xLastExecutionTime;
	uint32_t ulErrorFound = 0, ulLastErrorFound = 0;
	int tile = ( ( int * ) pvParameters )[0];
	int i = 0;

		xLastExecutionTime = xTaskGetTickCount();

		for( ;; )
		{
			/* Delay until it is time to execute again.  The delay period is
			shorter following an error. */
			vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

			if( xDelayPeriod == mainERROR_CHECK_PERIOD )
			{
				i++;
				if( i == mainCHECK_PERIOD / mainERROR_CHECK_PERIOD )
				{
					i = 0;
				}
			}

			if( i == 0)
			{
				/* Check all the demo application tasks are executing without
				error. If an error is found the delay period is shortened - this
				has the effect of increasing the flash rate of the 'check' task
				LED. */
				ulErrorFound = prvCheckTasks( tile, ulErrorFound );
				if( ulLastErrorFound != ulErrorFound )
				{
					/* An error has been detected in one of the tasks - flash faster. */
					xDelayPeriod = mainERROR_CHECK_PERIOD;
					rtos_printf("An Error has occured on tile %d - %08x\n", tile, ulErrorFound);
					ulLastErrorFound = ulErrorFound;
				}
			}

			/* Toggle the LED each cycle round. */
			vParTestToggleLED( tile );
		}
	}
#endif
/*-----------------------------------------------------------*/

/* Setup any hardware specific to tests here */
static void prvSetupHardware( int tile, chanend_t xTile0Chan, chanend_t xTile1Chan, chanend_t xTile2Chan, chanend_t xTile3Chan )
{
	vParTestInitialise( tile, xTile0Chan, xTile1Chan, xTile2Chan, xTile3Chan );
}

/*-----------------------------------------------------------*/

#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	static uint32_t prvCheckTasks( int tile, uint32_t ulErrorFound )
	{
		switch( tile )
		{
			case 0:
				/* Checks to only run on tile 0 go here */
				#if( testingmainENABLE_ABORT_DELAY_TASKS == 1 )
					if( xAreAbortDelayTestTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Abort delay task failed\n" );
						ulErrorFound |= 1UL << 0UL;
					}
				#endif

				#if( testingmainENABLE_BLOCKING_QUEUE_TASKS == 1 )
					if( xAreBlockingQueuesStillRunning() != pdTRUE )
					{
						rtos_printf( "Blocking queues task failed\n" );
						ulErrorFound |= 1UL << 1UL;
					}
				#endif

				#if( testingmainENABLE_BLOCK_TIME_TASKS == 1 )
					if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Block time task failed\n" );
						ulErrorFound |= 1UL << 2UL;
					}
				#endif

				#if( testingmainENABLE_COUNT_SEMAPHORE_TASKS == 1 )
					if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Counting semaphore task failed\n" );
						ulErrorFound |= 1UL << 3UL;
					}
				#endif

				#if( testingmainENABLE_DYNAMIC_PRIORITY_TASKS == 1 )
					if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Dynamic priority task failed\n" );
						ulErrorFound |= 1UL << 4UL;
					}
				#endif

				#if( testingmainENABLE_EVENT_GROUP_TASKS == 1 )
					if( xAreEventGroupTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Event groups task failed\n" );
						ulErrorFound |= 1UL << 5UL;
					}
				#endif

				#if( testingmainENABLE_INTERRUPT_QUEUE_TASKS == 1 )
					if( xAreIntQueueTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Interrupt queue task failed\n" );
						ulErrorFound |= 1UL << 6UL;
					}
				#endif

				#if( testingmainENABLE_FLOP_MATH_TASKS == 1 )
					if( xAreMathsTaskStillRunning() != pdTRUE )
					{
						rtos_printf( "Float math task failed\n" );
						ulErrorFound |= 1UL << 21UL;
					}
				#endif

				#if( testingmainENABLE_INT_MATH_TASKS == 1 )
					if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
					{
						rtos_printf( "Integer math task failed\n" );
						ulErrorFound |= 1UL << 22UL;
					}
				#endif
				/* End tile 0 checks */
	#if ( testingmainNUM_TILES > 1 )
				break;
			case 1:
	#endif
				/* Checks to only run on tile 1 go here,
				but will run on tile 0 if tiles < 2 */
				#if( testingmainENABLE_GENERIC_QUEUE_TASKS == 1 )
					if( xAreGenericQueueTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Generic queue task failed\n" );
						ulErrorFound |= 1UL << 7UL;
					}
				#endif

				#if( testingmainENABLE_INTERRUPT_SEMAPHORE_TASKS == 1 )
					if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Interrupt semaphore task failed\n" );
						ulErrorFound |= 1UL << 8UL;
					}
				#endif

				#if( testingmainENABLE_MESSAGE_BUFFER_TASKS == 1 )
					if( xAreMessageBufferTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Message buffer task failed\n" );
						ulErrorFound |= 1UL << 9UL;
					}
				#endif

				#if( testingmainENABLE_POLLED_QUEUE_TASKS == 1 )
					if( xArePollingQueuesStillRunning() != pdTRUE )
					{
						rtos_printf( "Polling queues task failed\n" );
						ulErrorFound |= 1UL << 10UL;
					}
				#endif

				#if( testingmainENABLE_QUEUE_PEEK_TASKS == 1 )
					if( xAreQueuePeekTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Queue peek task failed\n" );
						ulErrorFound |= 1UL << 11UL;
					}
				#endif

				#if( testingmainENABLE_QUEUE_OVERWRITE_TASKS == 1 )
					if( xIsQueueOverwriteTaskStillRunning() != pdTRUE )
					{
						rtos_printf( "Queue overwrite task failed\n" );
						ulErrorFound |= 1UL << 12UL;
					}
				#endif

				#if( testingmainENABLE_QUEUE_SET_TASKS == 1 )
					if( xAreQueueSetTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Queue set task failed\n" );
						ulErrorFound |= 1UL << 13UL;
					}
				#endif

				#if( testingmainENABLE_QUEUE_SET_POLLING_TASKS == 1 )
					if( xAreQueueSetPollTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Queue set poll task failed\n" );
						ulErrorFound |= 1UL << 14UL;
					}
				#endif

				#if( testingmainENABLE_RECURSIVE_MUTEX_TASKS == 1 )
					if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Recursive mutex task failed\n" );
						ulErrorFound |= 1UL << 15UL;
					}
				#endif

				#if( testingmainENABLE_SEMAPHORE_TASKS == 1 )
					if( xAreSemaphoreTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Semaphore task failed\n" );
						ulErrorFound |= 1UL << 16UL;
					}
				#endif

				#if( testingmainENABLE_STREAMBUFFER_TASKS == 1 )
					if( xAreStreamBufferTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Streambuffer task failed\n" );
						ulErrorFound |= 1UL << 17UL;
					}
				#endif

				#if( testingmainENABLE_STREAMBUFFER_INTERRUPT_TASKS == 1 )
					if( xIsInterruptStreamBufferDemoStillRunning() != pdTRUE )
					{
						rtos_printf( "ISR Streambuffer task failed\n" );
						ulErrorFound |= 1UL << 18UL;
					}
				#endif

				#if( testingmainENABLE_TASK_NOTIFY_TASKS == 1 )
					if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Task notification task failed\n" );
						ulErrorFound |= 1UL << 19UL;
					}
				#endif

				#if( testingmainENABLE_TASK_NOTIFY_ARRAY_TASKS == 1 )
					if( xAreTaskNotificationArrayTasksStillRunning() != pdTRUE )
					{
						rtos_printf( "Task notification array task failed\n" );
						ulErrorFound |= 1UL << 28UL;
					}
				#endif

				#if( testingmainENABLE_TIMER_DEMO_TASKS == 1 )
					if( xAreTimerDemoTasksStillRunning( mainTIMER_DEMO_TASK_FREQ ) != pdTRUE )
					{
						rtos_printf( "Timer demo task failed\n" );
						ulErrorFound |= 1UL << 20UL;
					}
				#endif

				/* End tile 1 checks */
				break;
			default:
				_Exit(0);	/* Invalid tile */
				break;
		}

		/* Tasks below here should be run on every tile */
		#if( testingmainENABLE_DEATH_TASKS == 1 )
			if( xIsCreateTaskStillRunning() != pdTRUE )
			{
				ulErrorFound |= 1UL << 23UL;
				rtos_printf( "Death task failed\n" );
			}
		#endif

		#if( testingmainENABLE_REG_TEST_TASKS == 1 )
			if( xAreRegTestTasksStillRunning() != pdTRUE )
			{
				ulErrorFound |= 1UL << 24UL;
				rtos_printf( "Regtest task failed\n" );
			}
		#endif

		if( xMallocError != pdFALSE )
		{
			ulErrorFound |= 1UL << 25UL;
			rtos_printf( "Malloc failed\n" );
		}

		if( xStackOverflowError != pdFALSE )
		{
			ulErrorFound |= 1UL << 26UL;
			rtos_printf( "Stack overflow detected\n" );
		}

		if( xIdleError != pdFALSE )
		{
			ulErrorFound |= 1UL << 27UL;
			rtos_printf( "Idle task math failed\n" );
		}

		return ulErrorFound;
	}
#endif

/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */

	rtos_printf( "Malloc Failed\n" );
	uint32_t ulState = portDISABLE_INTERRUPTS();
	xMallocError = pdTRUE;
	portRESTORE_INTERRUPTS( ulState );
	for( ;; );
}

/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */

	rtos_printf("Stack Overflow %s\n", pcTaskName );
	uint32_t ulState = portDISABLE_INTERRUPTS();
	xStackOverflowError = pdTRUE;
	portRESTORE_INTERRUPTS( ulState );
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMinimalIdleHook( void )
{
	//TaskStatus_t status;
	//vTaskGetInfo(NULL, &status, pdTRUE, eInvalid);
	//rtos_printf("%s on Core %u\n", status.pcTaskName,  portGET_CORE_ID());
}

/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile BaseType_t xValue;
uint32_t ulState;

	xValue = intCONST1;
	xValue += intCONST2;
	xValue *= intCONST3;
	xValue /= intCONST4;

	if( xValue != intEXPECTED_ANSWER )
	{
		rtos_printf("Error Occured at Idle Count: %u\n", ulCnt);
		xIdleError = pdTRUE;
	}

	#if( configUSE_PREEMPTION == 0 )
	{
		taskYIELD();
	}
	#endif

	ulState = portDISABLE_INTERRUPTS();
	ulCnt++;
	portRESTORE_INTERRUPTS(ulState);
}

/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	{
		switch (tile_g)
		{
		case 0:
			#if( testingmainENABLE_EVENT_GROUP_TASKS == 1 )
				/* Call the periodic event group from ISR demo. */
				vPeriodicEventGroupsProcessing();
			#endif

	#if ( testingmainNUM_TILES > 1 )
			break;
		case 1:
	#endif
			#if( testingmainENABLE_QUEUE_OVERWRITE_TASKS == 1 )
				/* Call the periodic queue overwrite from ISR demo. */
				vQueueOverwritePeriodicISRDemo();
			#endif

			#if( testingmainENABLE_INTERRUPT_SEMAPHORE_TASKS == 1 )
				/* Use mutexes from interrupts. */
				vInterruptSemaphorePeriodicTest();
			#endif

			#if( testingmainENABLE_QUEUE_SET_TASKS == 1 )
				/* Use queue sets from interrupts. */
				vQueueSetAccessQueueSetFromISR();
			#endif

			#if( testingmainENABLE_QUEUE_SET_POLLING_TASKS == 1 )
				/* Use queue sets from interrupts. */
				vQueueSetPollingInterruptAccess();
			#endif

			#if( testingmainENABLE_TIMER_DEMO_TASKS == 1 )
				/* The full demo includes a software timer demo/test that requires
				prodding periodically from the tick interrupt. */
				vTimerPeriodicISRTests();
			#endif

			#if( testingmainENABLE_TASK_NOTIFY_TASKS == 1 )
				/* Use task notifications from an interrupt. */
				xNotifyTaskFromISR();
			#endif

			#if( testingmainENABLE_TASK_NOTIFY_ARRAY_TASKS == 1 )
				/* Use task notifications from an interrupt. */
				xNotifyArrayTaskFromISR();
			#endif

			#if( testingmainENABLE_STREAMBUFFER_TASKS == 1 )
				/* Writes to stream buffer byte by byte to test the stream buffer trigger
				level functionality. */
				vPeriodicStreamBufferProcessing();
			#endif

			#if( testingmainENABLE_STREAMBUFFER_INTERRUPT_TASKS == 1 )
				/* Writes a string to a string buffer four bytes at a time to demonstrate
				a stream being sent from an interrupt to a task. */
				vBasicStreamBufferSendFromISR();
			#endif

			break;
		}
	}
	#endif /* #if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 ) */
}

/*-----------------------------------------------------------*/
