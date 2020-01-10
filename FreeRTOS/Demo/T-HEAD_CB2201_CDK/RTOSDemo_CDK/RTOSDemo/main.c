/*============================================================================
 * Name        : main.c
 * Author      : $(username)
 * Version     : 0.0.0
 * Copyright   : Your copyright notice
 * Description : Simple function in C, Ansi-style
 *============================================================================
 */


#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

extern void SystemInit(void);

#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

#define mainQUEUE_SEND_FREQUENCY_MS			( 200 / portTICK_PERIOD_MS )


/* The number of items the queue can hold.  This is 1 as the receive task

will remove items as they are added, meaning the send task should always find

the queue empty. */

#define mainQUEUE_LENGTH					( 1 )

static QueueHandle_t xQueue = NULL;

static void prvQueueSendTask( void *pvParameters )
{
	TickType_t xNextWakeTime;
	const unsigned long ulValueToSend = 100UL;


	/* Initialise xNextWakeTime - this only needs to be done once. */

	xNextWakeTime = xTaskGetTickCount();

	for( ;; )

	{

		/* Place this task in the blocked state until it is time to run again.

		The block time is specified in ticks, the constant used converts ticks

		to ms.  While in the Blocked state this task will not consume any CPU

		time. */

		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );


		/* Send to the queue - causing the queue receive task to unblock and

		toggle an LED.  0 is used as the block time so the sending operation

		will not block - it shouldn't need to block as the queue should always

		be empty at this point in the code. */

		xQueueSend( xQueue, &ulValueToSend, 0 );

	}

}

static void prvQueueReceiveTask( void *pvParameters )
{
	unsigned int ulReceivedValue;

	for( ;; )
	{

		/* Wait until something arrives in the queue - this task will block

		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in

		FreeRTOSConfig.h. */

		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );



		/*  To get here something must have been received from the queue, but

		is it the expected value?  If it is, toggle the green LED. */

		if( ulReceivedValue == 100UL )
		{
			printf("Recieve expected value : %d\n", ulReceivedValue);
		} 
		else 
		{
			printf("Recieve unexpected value : %d\n", ulReceivedValue);
		}

	}

}
 
int main()
{
	SystemInit();

	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );
	if (xQueue != NULL)
	{
		xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );

		xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );
		
		vTaskStartScheduler();
	}
	

    return 0;
}
