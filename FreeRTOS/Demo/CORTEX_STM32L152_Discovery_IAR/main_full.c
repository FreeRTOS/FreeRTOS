/*
 * FreeRTOS V202112.00
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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A low power tickless
 * project, and a more comprehensive test and demo application.  The
 * configCREATE_LOW_POWER_DEMO setting in FreeRTOSConfig.h is used to
 * select between the two.  See the notes on using
 * configCREATE_LOW_POWER_DEMO in FreeRTOSConfig.h.  This file implements
 * the comprehensive test and demo version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and a software timer, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks are not only still executing, but
 * are executing without reporting any errors.  If the check software timer
 * discovers that a task has either stalled, or reported an error, then it
 * changes its own execution period from the initial three seconds, to just
 * 200ms.  The check software timer callback function also toggles an LED each
 * time it is called.  This provides a visual indication of the system status:
 * If the LED toggles every three seconds, then no issues have been discovered.
 * If the LED toggles every 200ms, then an issue has been discovered with at
 * least one task.
 *
 * See the documentation page for this demo on the FreeRTOS.org web site for
 * full information, including hardware setup requirements.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo application includes. */
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"

/* ST library functions. */
#include "stm32l1xx.h"
#include "discover_board.h"
#include "stm32l_discovery_lcd.h"

/* Priorities for the demo application tasks. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire providing no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * Configure the LCD, then write welcome message.
 */
static void prvConfigureLCD( void );

/*-----------------------------------------------------------*/

void main_full( void )
{
TimerHandle_t xCheckTimer = NULL;

	/* The LCD is only used in the Full demo. */
	prvConfigureLCD();

	/* Start all the other standard demo/test tasks.  They have no particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
								pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,					/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
							  );

	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK );
	}

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo tasks to ensure they are all still running, and that
	none have detected an error. */

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	GPIO_TOGGLE( LD_GPIO_PORT, LD_GREEN_GPIO_PIN );

	/* Have any errors been latch in ulErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( ulErrorFound != pdFALSE )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvConfigureLCD( void )
{
GPIO_InitTypeDef GPIO_InitStructure;

	/* Enable necessary clocks. */
	RCC_AHBPeriphClockCmd( RCC_AHBPeriph_GPIOA | RCC_AHBPeriph_GPIOB | RCC_AHBPeriph_GPIOC, ENABLE );
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_LCD, ENABLE );
	PWR_RTCAccessCmd( ENABLE );
	RCC_LSEConfig( ENABLE );
	RCC_RTCCLKConfig( RCC_RTCCLKSource_LSE );
	RCC_RTCCLKCmd( ENABLE );

	/* Configure Port A LCD Output pins as alternate function. */
	GPIO_InitStructure.GPIO_Pin = GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_8 | GPIO_Pin_9 |GPIO_Pin_10 |GPIO_Pin_15;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
	GPIO_Init( GPIOA, &GPIO_InitStructure );

	/* Select LCD alternate function for Port A LCD Output pins. */
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource1, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource2, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource3, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource8, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource9, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource10, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOA, GPIO_PinSource15, GPIO_AF_LCD );

	/* Configure Port B LCD Output pins as alternate function */
	GPIO_InitStructure.GPIO_Pin = GPIO_Pin_3 | GPIO_Pin_4 | GPIO_Pin_5 | GPIO_Pin_8 | GPIO_Pin_9 | GPIO_Pin_10 | GPIO_Pin_11 | GPIO_Pin_12 | GPIO_Pin_13 | GPIO_Pin_14 | GPIO_Pin_15;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
	GPIO_Init( GPIOB, &GPIO_InitStructure );

	/* Select LCD alternate function for Port B LCD Output pins */
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource3, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource4, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource5, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource8, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource9, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource10, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource11, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource12, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource13, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource14, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOB, GPIO_PinSource15, GPIO_AF_LCD );

	/* Configure Port C LCD Output pins as alternate function */
	GPIO_InitStructure.GPIO_Pin = GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_6 | GPIO_Pin_7 | GPIO_Pin_8 | GPIO_Pin_9 | GPIO_Pin_10 |GPIO_Pin_11 ;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
	GPIO_Init( GPIOC, &GPIO_InitStructure );

	/* Select LCD alternate function for Port B LCD Output pins */
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource0, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource1, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource2, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource3, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource6, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource7, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource8, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource9, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource10, GPIO_AF_LCD );
	GPIO_PinAFConfig( GPIOC, GPIO_PinSource11, GPIO_AF_LCD );

	LCD_GLASS_Init();
	LCD_GLASS_DisplayString( "F'RTOS" );
}

