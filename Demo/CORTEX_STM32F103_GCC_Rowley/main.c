/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
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
 * "Check" task - This only executes every five seconds but has the highest
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the standard demo tasks are still operational. The check task
 * will toggle LED 3 (PB11) every five seconds so long as no errors have been
 * detected.  The toggle rate will increase to half a second if an error has 
 * been found in any task.
 *
 * "Echo" task - This is a very basic task that simply echoes any characters 
 * received on COM0 (USART1).  This can be tested by transmitting a text file
 * from a dumb terminal to the STM32 USART then observing or capturing the text
 * that is echoed back.  Missing characters will be all the more obvious if the 
 * file contains a simple repeating string of fixed width.
 *
 * Currently this demo does not include interrupt nesting examples.  High 
 * frequency timer and simpler nesting examples can be found in most Cortex-M3
 * demo applications.
 *
 * The functions used to initialise, set and clear LED outputs are normally 
 * defined in partest.c.  This demo includes two partest files, one that is 
 * configured for use with the Keil MCBSTM32 evaluation board (called 
 * ParTest_MCBSTM32.c) and one that is configured for use with the official
 * ST Eval board (called ParTest_ST_Eval.c).  One one of these files should be
 * included in the build at any one time, as appropriate for the hardware 
 * actually being used.
 */

/* Standard includes. */
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Library includes. */
#include "stm32f10x_it.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "integer.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"

/* Driver includes. */
#include "STM32_USART.h"


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
#define mainECHO_TASK_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* COM port and baud rate used by the echo task. */
#define mainCOM0							( 0 )
#define mainBAUD_RATE						( 115200 )

/*-----------------------------------------------------------*/

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/* The 'check' task as described at the top of this file. */
static void prvCheckTask( void *pvParameters );

/* A simple task that echoes all the characters that are received on COM0 
(USART1). */
static void prvUSARTEchoTask( void *pvParameters );

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

	/* Create the 'echo' task, which is also defined within this file. */
	xTaskCreate( prvUSARTEchoTask, ( signed char * ) "Echo", configMINIMAL_STACK_SIZE, NULL, mainECHO_TASK_PRIORITY, NULL );

	/* Create the 'check' task, which is also defined within this file. */
	xTaskCreate( prvCheckTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

    /* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task.  The idle task is created within vTaskStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

/* Described at the top of this file. */
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

/* Described at the top of this file. */
static void prvUSARTEchoTask( void *pvParameters )
{
signed char cChar;

/* String declared static to ensure it does not end up on the stack, no matter
what the optimisation level. */
static const char *pcLongishString = 
"ABBA was a Swedish pop music group formed in Stockholm in 1972, consisting of Anni-Frid Frida Lyngstad, "
"Björn Ulvaeus, Benny Andersson and Agnetha Fältskog. Throughout the band's existence, Fältskog and Ulvaeus "
"were a married couple, as were Lyngstad and Andersson - although both couples later divorced. They became one "
"of the most commercially successful acts in the history of popular music, and they topped the charts worldwide "
"from 1972 to 1983.  ABBA gained international popularity employing catchy song hooks, simple lyrics, sound "
"effects (reverb, phasing) and a Wall of Sound achieved by overdubbing the female singers' voices in multiple "
"harmonies. As their popularity grew, they were sought after to tour Europe, Australia, and North America, drawing "
"crowds of ardent fans, notably in Australia. Touring became a contentious issue, being particularly cumbersome for "
"Fältskog, but they continued to release studio albums to widespread commercial success. At the height of their "
"popularity, however, both relationships began suffering strain that led ultimately to the collapse of first the "
"Ulvaeus-Fältskog marriage (in 1979) and then of the Andersson-Lyngstad marriage in 1981. In the late 1970s and early "
"1980s these relationship changes began manifesting in the group's music, as they produced more thoughtful, "
"introspective lyrics with different compositions.";

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	/* Initialise COM0, which is USART1 according to the STM32 libraries. */
	lCOMPortInit( mainCOM0, mainBAUD_RATE );

	/* Try sending out a string all in one go, as a very basic test of the
    lSerialPutString() function. */
    lSerialPutString( mainCOM0, pcLongishString, strlen( pcLongishString ) );

	for( ;; )
	{
		/* Block to wait for a character to be received on COM0. */
		xSerialGetChar( mainCOM0, &cChar, portMAX_DELAY );

		/* Write the received character back to COM0. */
		xSerialPutChar( mainCOM0, cChar, 0 );
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

