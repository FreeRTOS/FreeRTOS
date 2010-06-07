/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks
 * (which just exist to test the kernel port and provide an example of how to use
 * each FreeRTOS API function).
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" task -  This only executes every five seconds but has the highest
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the standard demo tasks are still operational. The check task
 * will toggle LED 7 (PB15) every five seconds so long as no errors have been
 * detected.  The toggle rate will increase to half a second if an error has 
 * been found in any task.
 *
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Library includes. */
#include "stm32f10x_it.h"
#include "stm32f10x_tim.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "integer.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"


/* The time between cycles of the 'check' task - which depends on whether the
check task has detected an error or not. */
#define mainCHECK_DELAY_NO_ERROR			( ( portTickType ) 5000 / portTICK_RATE_MS )
#define mainCHECK_DELAY_ERROR				( ( portTickType ) 500 / portTICK_RATE_MS )

/* The LED controlled by the 'check' task. */
#define mainCHECK_LED						( 3 )

/* Task priorities. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/*-----------------------------------------------------------*/

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/* The 'check' task as described at the top of this file. */
static void prvCheckTask( void *pvParameters );

/*-----------------------------------------------------------*/

int main( void )
{
#ifdef DEBUG
  debug();
#endif

	/* Set up the clocks and memory interface. */
	prvSetupHardware();

	/* Start the standard demo tasks.  These are just here to exercise the
	kernel port and provide examples of how the FreeRTOS API can be used. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
    vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();

	/* Create the 'check' task, which is defined within this file. */
	xTaskCreate( prvCheckTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

    /* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task.  The idle task is created within vTaskStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
portTickType xLastExecutionTime;
unsigned long ulTicksToWait = mainCHECK_DELAY_NO_ERROR;

	/* Just to remove the compiler warning about the unused parameter. */
	( void ) pvParameters;

	/* Initialise the variable used to control our iteration rate prior to
	its first use. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time to run the tests again. */
		vTaskDelayUntil( &xLastExecutionTime, ulTicksToWait );

		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			/* Reduce the time between cycles of this task - which has the
			effect of increasing the rate at which the 'check' LED toggles to
			indicate the existence of an error to an observer. */
			ulTicksToWait = mainCHECK_DELAY_ERROR;
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainCHECK_DELAY_ERROR;
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulTicksToWait = mainCHECK_DELAY_ERROR;
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	        ulTicksToWait = mainCHECK_DELAY_ERROR;
	    }
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
	        ulTicksToWait = mainCHECK_DELAY_ERROR;
	    }
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	ulTicksToWait = mainCHECK_DELAY_ERROR;
	    }

		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* RCC system reset(for debug purpose). */
	RCC_DeInit ();                        

    /* Enable HSE. */
	RCC_HSEConfig( RCC_HSE_ON );           
	
	/* Wait till HSE is ready. */
	while (RCC_GetFlagStatus(RCC_FLAG_HSERDY) == RESET);
	
    /* HCLK = SYSCLK. */
	RCC_HCLKConfig( RCC_SYSCLK_Div1 );   

    /* PCLK2  = HCLK. */
	RCC_PCLK2Config( RCC_HCLK_Div1 );     

    /* PCLK1  = HCLK/2. */
	RCC_PCLK1Config( RCC_HCLK_Div2 );     

	/* ADCCLK = PCLK2/4. */
	RCC_ADCCLKConfig( RCC_PCLK2_Div4 );    
	
    /* Flash 2 wait state. */
	*( volatile unsigned long  * )0x40022000 = 0x01;           
	
	/* PLLCLK = 8MHz * 9 = 72 MHz */
	RCC_PLLConfig( RCC_PLLSource_HSE_Div1, RCC_PLLMul_9 );
	
    /* Enable PLL. */
	RCC_PLLCmd( ENABLE );
	
	/* Wait till PLL is ready. */
	while (RCC_GetFlagStatus(RCC_FLAG_PLLRDY) == RESET);
	
	/* Select PLL as system clock source. */
	RCC_SYSCLKConfig (RCC_SYSCLKSource_PLLCLK);
	
	/* Wait till PLL is used as system clock source. */
	while (RCC_GetSYSCLKSource() != 0x08);

	/* Enable GPIOA, GPIOB, GPIOC, GPIOD, GPIOE and AFIO clocks */
	RCC_APB2PeriphClockCmd(	RCC_APB2Periph_GPIOA | RCC_APB2Periph_GPIOB |RCC_APB2Periph_GPIOC
							| RCC_APB2Periph_GPIOD | RCC_APB2Periph_GPIOE | RCC_APB2Periph_AFIO, ENABLE );

	/* Set the Vector Table base address at 0x08000000. */
	NVIC_SetVectorTable( NVIC_VectTab_FLASH, 0x0 );

	NVIC_PriorityGroupConfig( NVIC_PriorityGroup_4 );

	/* Configure HCLK clock as SysTick clock source. */
	SysTick_CLKSourceConfig( SysTick_CLKSource_HCLK );

	/* Initialise the IO used for the LED outputs. */
	vParTestInitialise();

	/* SPI2 Periph clock enable */
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_SPI2, ENABLE );

	/* Initialize the SPI FLASH driver */
	SPI_FLASH_Init();
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	/* This function will get called if a task overflows its stack.   If the
	parameters are corrupt then inspect pxCurrentTCB to find which was the
	offending task. */

	( void ) pxTask;
	( void ) pcTaskName;

	for( ;; );
}
/*-----------------------------------------------------------*/

void assert_failed( unsigned char *pucFile, unsigned long ulLine )
{
	( void ) pucFile;
	( void ) ulLine;

	for( ;; );
}

