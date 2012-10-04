/* main.c 
 *
 * "Check" callback function - Called each time the 'check' timer expires.  The
 * check timer executes every five seconds.  Its main function is to check that 
 * all the standard demo tasks are still operational.  Each time it executes it 
 * sends a status code to the LCD task.  The LCD task interprets the code and 
 * displays an appropriate message - which will be PASS if no tasks have 
 * reported any errors, or a message stating which task has reported an error.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check timer callback (described a above) to 
 * determine that an error has occurred.  The nature of the reg test tasks 
 * necessitates that they are written in assembly code.
 *
 * Tick hook function - called inside the RTOS tick function, this simple 
 * example does nothing but toggle an LED.
 *
 */

#include <stdio.h>
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "queue.h"
#include "gio.h"
#include "TimerDemo.h"
#include "countsem.h"
#include "GenQTest.h"
#include "dynamic.h"


/* ----------------------------------------------------------------------------------------------------------- */

/* Codes sent within messages to the LCD task so the LCD task can interpret
exactly what the message it just received was.  These are sent in the
cMessageID member of the message structure (defined below). */
//#define mainMESSAGE_BUTTON_UP			( 1 )
//#define mainMESSAGE_BUTTON_SEL		( 2 )
#define mainMESSAGE_STATUS				( 3 )

/* When the cMessageID member of the message sent to the MSG task is
mainMESSAGE_STATUS then these definitions are sent in the ulMessageValue member
of the same message and indicate what the status actually is. */
#define mainERROR_DYNAMIC_TASKS			( pdPASS + 1 )
#define mainERROR_COM_TEST				( pdPASS + 2 )
#define mainERROR_GEN_QUEUE_TEST		( pdPASS + 3 )
#define mainERROR_REG_TEST				( pdPASS + 4 )
#define mainERROR_TIMER_TEST			( pdPASS + 5 )
#define mainERROR_COUNT_SEM_TEST		( pdPASS + 6 )

/* Priorities used by the test and demo tasks. */
#define mainMSG_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainGENERIC_QUEUE_TEST_PRIORITY	( tskIDLE_PRIORITY )

/* Just used to ensure parameters are passed into tasks correctly. */
#define mainTASK_PARAMETER_CHECK_VALUE	((void *)0xDEAD)

/* The length of the queue (the number of items the queue can hold) that is used
to send messages from tasks and interrupts the the MSG task. */
#define mainQUEUE_LENGTH				( 5 )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD			( 50 )

/* The frequency at which the check timer (described in the comments at the top
of this file) will call its callback function. */
#define mainCHECK_TIMER_PERIOD			( 5000UL / ( unsigned long ) portTICK_RATE_MS )

/* Misc. */
#define mainDONT_BLOCK					( 0 )


/* ----------------------------------------------------------------------------------------------------------- */
/* external regsiter check tasks, this checks that the context store/restore works                             */

extern void vRegTestTask1(void *pvParameters); 
extern void vRegTestTask2(void *pvParameters); 

/*
 * Definition of the MSG/controller task described in the comments at the top
 * of this file.
 */
static void prvMsgTask( void *pvParameters );

/*
 * Converts a status message value into an appropriate string for display on
 * the LCD.  The string is written to pcBuffer.
 */
static void prvGenerateStatusMessage( char *pcBuffer, unsigned long ulStatusValue );

/*
 * Defines the 'check' functionality as described at the top of this file.  This
 * function is the callback function for the 'check' timer. */
static void vCheckTimerCallback( xTimerHandle xTimer );


/* ----------------------------------------------------------------------------------------------------------- */

static signed char buffer[1024];

void vStatsTask(void *pvParameters)
{
	printf("**** Task Statistics Started\n");
	for (;;)
	{
		vTaskDelay(15000);
		vTaskGetRunTimeStats(buffer);
		printf("%s\n", buffer);
	}
}


/* ----------------------------------------------------------------------------------------------------------- */

/* variable incremente in the IDLE hook */
volatile unsigned usIdleCounter = 0;

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
volatile unsigned usRegTest1Counter = 0, usRegTest2Counter = 0;

/* The handle of the queue used to send messages from tasks and interrupts to
   the MSG task. */
static xQueueHandle xMsgQueue = NULL;

/* The 'check' timer, as described at the top of this file. */
static xTimerHandle xCheckTimer = NULL;

/* The definition of each message sent from tasks and interrupts to the MSG
task. */
typedef struct
{
	char     cMessageID;		/* << States what the message is. */
	unsigned ulMessageValue; 	/* << States the message value (can be an integer, string pointer, etc. depending on the value of cMessageID). */
} xQueueMessage;


/* ----------------------------------------------------------------------------------------------------------- */

void main()
{
	/* initalise DIO ports */
	gioInit();
	
	gioSetBit(gioPORTA, 0, 1);
	gioSetBit(gioPORTA, 0, 0);


	/* Create the queue used by tasks and interrupts to send strings to the MSG task. */
	xMsgQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( xQueueMessage ) );

	/* If the queue could not be created then don't create any tasks that might
	attempt to use the queue. */
	if( xMsgQueue != NULL )
	{
		/* Create STATS task, this prints out a summary of running tasks every 15s */
		xTaskCreate(vStatsTask, (signed char *)"STATS..", 600, NULL, 6, NULL);

		/* Create the standard demo tasks. */
		vStartDynamicPriorityTasks();
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );
		vStartCountingSemaphoreTasks();
		
		/* Note that creating the timer test/demo tasks will fill the timer
		command queue.  This is intentional, and forms part of the test the tasks
		perform.  It does mean however that, after this function is called, no
		more timer commands can be sent until after the scheduler has been
		started (at which point the timer daemon will drained the timer command
		queue, freeing up space for more commands to be received). */
		vStartTimerDemoTask(mainTIMER_TEST_PERIOD);
		
		/* Create the MSGl and register test tasks. */
		xTaskCreate(prvMsgTask,    (signed char *)"MSG....",  500, mainTASK_PARAMETER_CHECK_VALUE, mainMSG_TASK_PRIORITY, NULL );
		xTaskCreate(vRegTestTask1, (signed char *)"REG1...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL);
		xTaskCreate(vRegTestTask2, (signed char *)"REG2...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL);
		
		
		/* Create the 'check' timer - the timer that periodically calls the
		check function as described at the top of this file.  Note that, for
		the reasons stated in the comments above the call to 
		vStartTimerDemoTask(), that the check timer is not actually started 
		until after the scheduler has been started. */
		xCheckTimer = xTimerCreate( ( const signed char * ) "Check Timer", mainCHECK_TIMER_PERIOD, pdTRUE, ( void * ) 0, vCheckTimerCallback ); 
		
		/* start FreeRTOS Scheduler */
		vTaskStartScheduler();
	}
	
	/* If all is well then this line will never be reached.  If it is reached
	then it is likely that there was insufficient (FreeRTOS) heap memory space
	to create the idle task.  This may have been trapped by the malloc() failed
	hook function, if one is configured. */	
	for (;;);
}


/* ----------------------------------------------------------------------------------------------------------- */

static void prvMsgTask( void *pvParameters )
{
	xQueueMessage xReceivedMessage;
	static char   cBuffer[50];  

	printf("**** Msg Task Started\n");

	/* Now the scheduler has been started (it must have been for this task to
	be running), start the check timer too.  The call to xTimerStart() will
	block until the command has been accepted. */
	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, portMAX_DELAY );
	}

	/*	First print out the number of bytes that remain in the FreeRTOS heap.  This
	is done after a short delay to ensure all the demo tasks have created all
	the objects they are going to use.  */
	vTaskDelay( mainTIMER_TEST_PERIOD * 10 );
	printf("**** %d heap free\n", (int)xPortGetFreeHeapSize());
	
	/* Just as a test of the port, and for no functional reason, check the task
	parameter contains its expected value. */
	if( pvParameters != mainTASK_PARAMETER_CHECK_VALUE )
	{
		printf("**** Invalid parameter ****\n\n");
	}

	for( ;; )
	{
		/* Wait for a message to be received.  Using portMAX_DELAY as the block
		time will result in an indefinite wait provided INCLUDE_vTaskSuspend is
		set to 1 in FreeRTOSConfig.h, therefore there is no need to check the
		function return value and the function will only return when a value
		has been received. */
		xQueueReceive( xMsgQueue, &xReceivedMessage, portMAX_DELAY );

		/* What is this message?  What does it contain? */
		switch( xReceivedMessage.cMessageID )
		{
#if 0			
			case mainMESSAGE_BUTTON_UP		:	/* The button poll task has just
												informed this task that the up
												button on the joystick input has
												been pressed or released. */
												sprintf( cBuffer, "Button up = %d", ( int ) xReceivedMessage.ulMessageValue );
												break;

			case mainMESSAGE_BUTTON_SEL		:	/* The select button interrupt
												just informed this task that the
												select button has been pressed.
												In this case the pointer to the 
												string to print is sent directly 
												in the ulMessageValue member of 
												the	message.  This just 
												demonstrates a different 
												communication technique. */
												sprintf( cBuffer, "%s", ( char * ) xReceivedMessage.ulMessageValue );
												break;
#endif												
			case mainMESSAGE_STATUS			:	/* The tick interrupt hook
												function has just informed this
												task of the system status.
												Generate a string in accordance
												with the status value. */
												prvGenerateStatusMessage( cBuffer, xReceivedMessage.ulMessageValue );
												break;
												
			default							:	sprintf( cBuffer, "Unknown message" );
												break;
		}
		/* Output the message that was placed into the cBuffer array within the
		switch statement above, then move onto the next line ready for the next
		message to arrive on the queue. */
		printf("**** Message Received: %s\n", cBuffer);
	}		
}

static void prvGenerateStatusMessage(char *pcBuffer, unsigned long ulStatusValue)
{
	/* Just a utility function to convert a status value into a meaningful
	string for output. */
	switch( ulStatusValue )
	{
		case pdPASS						:	sprintf( pcBuffer, "Status = PASS" );
											break;
		case mainERROR_DYNAMIC_TASKS	:	sprintf( pcBuffer, "Err: Dynamic tsks" );
											break;
		case mainERROR_COM_TEST			:	sprintf( pcBuffer, "Err: COM test" );
											break;
		case mainERROR_GEN_QUEUE_TEST 	:	sprintf( pcBuffer, "Error: Gen Q test" );
											break;
		case mainERROR_REG_TEST			:	sprintf( pcBuffer, "Error: Reg test" );
											break;
		case mainERROR_TIMER_TEST		:	sprintf( pcBuffer, "Error: Tmr test" );
											break;
		case mainERROR_COUNT_SEM_TEST	:	sprintf( pcBuffer, "Error: Count sem" );
											break;
		default							:	sprintf( pcBuffer, "Unknown status" );
											break;
	}
}

/* ----------------------------------------------------------------------------------------------------------- */

static void vCheckTimerCallback( xTimerHandle xTimer )
{
	static unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;

	/* Define the status message that is sent to the LCD task.  By default the
	   status is PASS. */
	static xQueueMessage xStatusMessage = { mainMESSAGE_STATUS, pdPASS };

	/* This is the callback function used by the 'check' timer, as described
	at the top of this file. */

	/* The parameter is not used. */
	( void ) xTimer;
	
	/* See if the standard demo tasks are executing as expected, changing
	the message that is sent to the LCD task from PASS to an error code if
	any tasks set reports an error. */
#if 0	
	if( xAreComTestTasksStillRunning() != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_COM_TEST;
	}
#endif
	if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_DYNAMIC_TASKS;
	}
	
	if( xAreGenericQueueTasksStillRunning() != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_GEN_QUEUE_TEST;
	}			
	
	if( xAreCountingSemaphoreTasksStillRunning() != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_COUNT_SEM_TEST;
	}
	
	if( xAreTimerDemoTasksStillRunning( ( portTickType ) mainCHECK_TIMER_PERIOD ) != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_TIMER_TEST;
	}

	/* Check the reg test tasks are still cycling.  They will stop
	incrementing their loop counters if they encounter an error. */
	if( usRegTest1Counter == usLastRegTest1Counter )
	{
		xStatusMessage.ulMessageValue = mainERROR_REG_TEST;
	}

	if( usRegTest2Counter == usLastRegTest2Counter )
	{
		xStatusMessage.ulMessageValue = mainERROR_REG_TEST;
	}

	usLastRegTest1Counter = usRegTest1Counter;
	usLastRegTest2Counter = usRegTest2Counter;
	
	/* This is called from a timer callback so must not block! */
	xQueueSendToBack( xMsgQueue, &xStatusMessage, mainDONT_BLOCK );
}


/* ----------------------------------------------------------------------------------------------------------- */

void vApplicationTickHook( void )
{
	static unsigned long ulCounter = 0;

	/* Is it time to toggle the pin again? */
	ulCounter++;

	/* Just periodically toggle a pin to show that the tick interrupt is
	running.  */
	if( ( ulCounter & 0xff ) == 0 )
	{
		gioSetBit(gioPORTA, 0, 1);
		gioSetBit(gioPORTA, 0, 0);
	}
}


/* ----------------------------------------------------------------------------------------------------------- */

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues or
	semaphores. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}

/* ----------------------------------------------------------------------------------------------------------- */
 
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}

/* ----------------------------------------------------------------------------------------------------------- */

void vApplicationIdleHook(void)
{
	usIdleCounter++;	
}


/* ----------------------------------------------------------------------------------------------------------- */



