// Copyright (c) 2019, XMOS Ltd, All rights reserved

#ifndef TESTING_MAIN_H_
#define TESTING_MAIN_H_

/* Controls whether to create blinky demo or the full demo. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY  0

#define testingmainNUM_TILES				2
#define testingmainENABLE_XC_TASKS			1

/* TODO: Update to be package specific check */
#if ( testingmainNUM_TILES > 2 )
#error Tiles must be less than 3.
#endif

/* Tests to be run */

/*** These tests run on all tiles ***/
#define testingmainENABLE_REG_TEST_TASKS				1

/* Death cannot be run with any demo that creates or destroys tasks */
#define testingmainENABLE_DEATH_TASKS					1

/*** These tests run on tile 0 ***/
#define testingmainENABLE_ABORT_DELAY_TASKS				1
#define testingmainENABLE_BLOCKING_QUEUE_TASKS			1
#define testingmainENABLE_BLOCK_TIME_TASKS				1
#define testingmainENABLE_COUNT_SEMAPHORE_TASKS			1
#define testingmainENABLE_DYNAMIC_PRIORITY_TASKS		1
#define testingmainENABLE_EVENT_GROUP_TASKS				1
#define testingmainENABLE_INTERRUPT_QUEUE_TASKS         1
#define testingmainENABLE_FLOP_MATH_TASKS				1
#define testingmainENABLE_INT_MATH_TASKS				1

/*** These tests run on tile 1 ***/
#define testingmainENABLE_GENERIC_QUEUE_TASKS			1
#define testingmainENABLE_INTERRUPT_SEMAPHORE_TASKS		1
#define testingmainENABLE_MESSAGE_BUFFER_TASKS			1
#define testingmainENABLE_POLLED_QUEUE_TASKS			1
#define testingmainENABLE_QUEUE_PEEK_TASKS				1
#define testingmainENABLE_QUEUE_OVERWRITE_TASKS			1
#define testingmainENABLE_QUEUE_SET_TASKS				1
#define testingmainENABLE_QUEUE_SET_POLLING_TASKS		1
#define testingmainENABLE_RECURSIVE_MUTEX_TASKS			1
#define testingmainENABLE_SEMAPHORE_TASKS				1
#define testingmainENABLE_STREAMBUFFER_TASKS			1
#define testingmainENABLE_STREAMBUFFER_INTERRUPT_TASKS	1
#define testingmainENABLE_TASK_NOTIFY_TASKS				1
#define testingmainENABLE_TASK_NOTIFY_ARRAY_TASKS	    1
#define testingmainENABLE_TIMER_DEMO_TASKS				1

/*** These tests run on all tiles ***/
#define mainREGTEST_PRIORITY				( tskIDLE_PRIORITY + 0 )

/* Death cannot be run with any demo that creates or destroys tasks */
#define mainDEATH_PRIORITY					( tskIDLE_PRIORITY + 1 )

/* Priorities assigned to demo application tasks. */
#define mainCHECK_TASK_PRIORITY 			( configMAX_PRIORITIES - 1 )

/*** These tests run on tile 0 ***/
#define mainBLOCKING_Q_TASKS_PRIORITY 		( tskIDLE_PRIORITY + 2 )
#define mainINT_MATH_PRIORITY				( tskIDLE_PRIORITY + 0 )
#define mainFLOP_TASKS_PRIORITY 			( tskIDLE_PRIORITY + 0 )

/*** These tests run on tile 1 ***/
#define mainGENERIC_Q_TASKS_PRIORITY 		( tskIDLE_PRIORITY + 0 )
#define mainPOLLED_QUEUE_TASKS_PRIORITY 	( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_OVERWRITE_TASKS_PRIORITY 	( tskIDLE_PRIORITY + 0 )
#define mainSEMAPHORE_TASKS_PRIORITY 		( tskIDLE_PRIORITY + 2 )

/* Other demo application specific defines */
#define mainMESSAGE_BUFFER_STACK_SIZE 		configMINIMAL_STACK_SIZE
#define mainTIMER_DEMO_TASK_FREQ 			( ( TickType_t ) 10000 / configTICK_RATE_HZ )
#define tmrTIMER_TEST_TASK_STACK_SIZE 		portTASK_STACK_DEPTH(prvTimerTestTask)

/* The constants used in the idle task calculation. */
#define intCONST1				( ( BaseType_t ) 346 )
#define intCONST2				( ( BaseType_t ) 74324 )
#define intCONST3				( ( BaseType_t ) -2 )
#define intCONST4				( ( BaseType_t ) 9 )
#define intEXPECTED_ANSWER		( ( BaseType_t ) ( ( intCONST1 + intCONST2 ) * intCONST3 ) / intCONST4 )

/* The check task periodically checks that all the other tasks
are operating without error.  If no errors are found the LED
is toggled with mainCHECK_PERIOD frequency.  If an error is found
then the toggle rate changes to mainERROR_CHECK_PERIOD. */
#define mainCHECK_PERIOD			pdMS_TO_TICKS(3000)
#define mainERROR_CHECK_PERIOD		pdMS_TO_TICKS(200)

#endif /* TESTING_MAIN_H_ */
