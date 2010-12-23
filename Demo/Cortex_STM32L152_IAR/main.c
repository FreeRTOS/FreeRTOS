/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

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

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "dynamic.h"
#include "comtest2.h"
#include "GenQTest.h"

/* ST driver includes. */
#include "stm32l1xx_usart.h"

/* Eval board includes. */
#include "stm32_eval.h"
#include "stm32l152_eval_lcd.h"

#define mainFLASH_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainLCD_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainGENERIC_QUEUE_TEST_PRIORITY	( tskIDLE_PRIORITY )

#define mainLCD_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE * 2 )

#define mainQUEUE_LENGTH				( 5 )

#define mainMESSAGE_BUTTON_UP			( 1 )
#define mainMESSAGE_BUTTON_DOWN			( 2 )
#define mainMESSAGE_BUTTON_LEFT			( 3 )
#define mainMESSAGE_BUTTON_RIGHT		( 4 )
#define mainMESSAGE_BUTTON_SEL			( 5 )
#define mainMESSAGE_STATUS				( 6 )

#define mainERROR_DYNAMIC_TASKS			( 2 )
#define mainERROR_COM_TEST				( 3 )
#define mainERROR_GEN_QUEUE_TEST		( 4 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE		( 9600 )

/* The LED used by the comtest tasks. See the comtest.c file for more
information. */
#define mainCOM_TEST_LED			( 3 )


/*
 * System configuration is performed prior to main() being called, this function
 * configures the peripherals used by the demo application.
 */
static void prvSetupHardware( void );
static void prvLCDTask( void *pvParameters );
static void vTempTask( void *pv );
static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue );

unsigned long ulTIM6_OverflowCount = 0UL;

static xQueueHandle xLCDQueue = NULL;

typedef struct
{
	char cMessageID;
	long lMessageValue;
} xQueueMessage;

void main( void )
{
	prvSetupHardware();
	
	/* Create the queue used by tasks and interrupts to send strings to the LCD
	task. */
	xLCDQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( xQueueMessage ) );
	
	if( xLCDQueue != NULL )
	{
		vQueueAddToRegistry( xLCDQueue, "LCDQueue" );
		xTaskCreate( prvLCDTask, ( signed char * ) "LCD", mainLCD_TASK_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( vTempTask, ( signed char * ) "Temp", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
		vStartDynamicPriorityTasks();
		vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );
		
		vTaskStartScheduler();
	}
	
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLCDTask( void *pvParameters )
{
xQueueMessage xReceivedMessage;
long lLine = Line1;
const long lFontHeight = (((sFONT *)LCD_GetFont())->Height);
static char cBuffer[ 512 ];

	/* This function is the only function that uses printf().  If printf() is
	used from any other function then some sort of mutual exclusion on stdout
	will be necessary. */

	printf( "%d bytes of heap space remain unallocated\n", xPortGetFreeHeapSize() );

	for( ;; )
	{
		xQueueReceive( xLCDQueue, &xReceivedMessage, portMAX_DELAY );

		if( lLine > Line9 )
		{
			LCD_Clear( Blue );
			lLine = 0;
		}
				
		switch( xReceivedMessage.cMessageID )
		{
			case mainMESSAGE_BUTTON_UP		:	sprintf( cBuffer, "Button up = %d", xReceivedMessage.lMessageValue );
												break;
			case mainMESSAGE_BUTTON_DOWN	:	sprintf( cBuffer, "Button down = %d", xReceivedMessage.lMessageValue );
												break;
			case mainMESSAGE_BUTTON_LEFT	:	sprintf( cBuffer, "Button left = %d", xReceivedMessage.lMessageValue );
												break;
			case mainMESSAGE_BUTTON_RIGHT	:	sprintf( cBuffer, "Button right = %d", xReceivedMessage.lMessageValue );
												break;
			case mainMESSAGE_BUTTON_SEL		:	printf( "\nTask\t     Abs Time\t     %%Time\n*****************************************" );
												vTaskGetRunTimeStats( ( signed char * ) cBuffer );
												printf( cBuffer );
												
												/* The select button passes its
												own string to print out. */
												sprintf( cBuffer, "%s", ( char * ) xReceivedMessage.lMessageValue );
												break;
			case mainMESSAGE_STATUS			:	prvGenerateStatusMessage( cBuffer, xReceivedMessage.lMessageValue );
												break;
			default							:	sprintf( cBuffer, "Unknown message" );
												break;
		}
		
		LCD_DisplayStringLine( lLine, ( uint8_t * ) cBuffer );
		lLine += lFontHeight;
	}
}
/*-----------------------------------------------------------*/

static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue )
{
	switch( lStatusValue )
	{
		case pdPASS						:	sprintf( pcBuffer, "Task status = PASS" );
											break;
		case mainERROR_DYNAMIC_TASKS	:	sprintf( pcBuffer, "Error: Dynamic tasks" );
											break;
		case mainERROR_COM_TEST			:	sprintf( pcBuffer, "Error: COM test" );
											break;
		case mainERROR_GEN_QUEUE_TEST 	:	sprintf( pcBuffer, "Error: Gen Q test" );
											break;
		default							:	sprintf( pcBuffer, "Unknown status" );
											break;
	}
}
/*-----------------------------------------------------------*/

void EXTI9_5_IRQHandler( void )
{
const xQueueMessage xMessage = { mainMESSAGE_BUTTON_SEL, ( unsigned long ) "Select Interrupt!" };
long lHigherPriorityTaskWoken = pdFALSE;

	xQueueSendFromISR( xLCDQueue, &xMessage, &lHigherPriorityTaskWoken );
	EXTI_ClearITPendingBit( SEL_BUTTON_EXTI_LINE );
	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned long ulCounter = 0;
static const unsigned long ulCheckFrequency = 5000UL / portTICK_RATE_MS;
static xQueueMessage xStatusMessage = { mainMESSAGE_STATUS, pdPASS };
long lHigherPriorityTaskWoken = pdFALSE; /* Not used in this case as this is the tick hook. */

	ulCounter++;
	if( ulCounter >= ulCheckFrequency )
	{
		if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
		{
			xStatusMessage.lMessageValue = mainERROR_DYNAMIC_TASKS;
		}
		
		if( xAreComTestTasksStillRunning() != pdPASS )
		{
			xStatusMessage.lMessageValue = mainERROR_COM_TEST;
		}
		
		if( xAreGenericQueueTasksStillRunning() != pdPASS )
		{
			xStatusMessage.lMessageValue = mainERROR_GEN_QUEUE_TEST;
		}
		
		xQueueSendFromISR( xLCDQueue, &xStatusMessage, &lHigherPriorityTaskWoken );
		ulCounter = 0;
	}
}
/*-----------------------------------------------------------*/

static void vTempTask( void *pv )
{
long lLastState = pdTRUE;
long lState;
xQueueMessage xMessage;

	for( ;; )
	{
		lState = STM_EVAL_PBGetState( BUTTON_UP );
		if( lState != lLastState )
		{
			xMessage.cMessageID = mainMESSAGE_BUTTON_UP;
			xMessage.lMessageValue = lState;
			lLastState = lState;
			xQueueSend( xLCDQueue, &xMessage, portMAX_DELAY );
			vTaskDelay( 10 );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	NVIC_PriorityGroupConfig( NVIC_PriorityGroup_4 );
	
	/* Initialise the LEDs. */
	vParTestInitialise();

	/* Initialise the joystick inputs. */
	STM_EVAL_PBInit( BUTTON_UP, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_DOWN, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_LEFT, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_RIGHT, BUTTON_MODE_GPIO );
	
	/* The select button in the middle of the joystick is configured to generate
	an interrupt.  The Eval board library will configure the interrupt
	priority to be the lowest priority available - this is important as the
	interrupt service routine makes use of a FreeRTOS API function so must
	therefore use a priority equal to or below that set by the
	configMAX_SYSCALL_INTERRUPT_PRIORITY() value set in FreeRTOSConfig.h. */
	STM_EVAL_PBInit( BUTTON_SEL, BUTTON_MODE_EXTI );

	/* Initialize the LCD */
	STM32L152_LCD_Init();
	
	LCD_Clear(Blue);
	LCD_SetBackColor(Blue);
	LCD_SetTextColor(White);
	LCD_DisplayStringLine(Line0, "  www.FreeRTOS.org");
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
TIM_TimeBaseInitTypeDef  TIM_TimeBaseStructure;
NVIC_InitTypeDef NVIC_InitStructure;

	/* TIM6 clock enable */
	RCC_APB1PeriphClockCmd(RCC_APB1Periph_TIM6, ENABLE);

	/* The 32MHz clock divided by 5000 should tick (very) approximately every
	150uS and overflow a 16bit timer (very) approximately every 10 seconds. */
	TIM_TimeBaseStructure.TIM_Period = 65535;
	TIM_TimeBaseStructure.TIM_Prescaler = 5000;
	TIM_TimeBaseStructure.TIM_ClockDivision = TIM_CKD_DIV1;
	TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_Up;
	
	TIM_TimeBaseInit( TIM6, &TIM_TimeBaseStructure );
	
	/* Only interrupt on overflow events. */
	TIM6->CR1 |= TIM_CR1_URS;
	
	TIM_ITConfig( TIM6, TIM_IT_Update, ENABLE );
	
	/* Enable the TIM6 gloabal Interrupt */
	NVIC_InitStructure.NVIC_IRQChannel = TIM6_IRQn;
	NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = configLIBRARY_LOWEST_INTERRUPT_PRIORITY;
	NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0x00; /* Not used as 4 bits are used for the pre-emption priority. */
	NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
	
	TIM_ClearITPendingBit( TIM6, TIM_IT_Update );
	NVIC_Init(&NVIC_InitStructure);
	TIM_Cmd( TIM6, ENABLE );
}
/*-----------------------------------------------------------*/

void TIM6_IRQHandler( void )
{
	if( TIM_GetITStatus( TIM6, TIM_IT_Update) != RESET)
	{
		ulTIM6_OverflowCount++;
		TIM_ClearITPendingBit( TIM6, TIM_IT_Update );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;
	
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	for( ;; );
}


