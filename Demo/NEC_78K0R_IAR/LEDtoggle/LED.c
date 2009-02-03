/*
	FreeRTOS.org V5.0.2 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/**
 * This is a simple LED toggle test for the 78K0R/Kx3 Target Board (QB-78K0RKG3-TB).
 *
 * Creates two task that control one LED each. 
 *
 * The first task toggles a LED with a frequency of 1Hz by using the vTaskDelay 
 * function. So the task is yielded for 1 seconed after each LED switch.
 *
 * The second LED can be toggled by a switch within the second task.
 * When the switch is pushed it is detected by an interrupt. When the interrupt
 * occurs a flag is set in the ISR and sent to the second task by using a queue. 
 * Therefore the  xQueueSendFromISR() function is called from within the ISR to
 * write the flag value to the queue. The task uses the xQueueReceive() function
 * to read the flag value from the queue.
 * If the flag value changed from the last task activation the LED is toggled.
 * 
 * Also a check function is implemented to check if the task still run properly
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "LED.h"
#include "queue.h"
#include "print.h"

#define LEDToggleSTACK_SIZE (( unsigned portSHORT ) configMINIMAL_STACK_SIZE)
#define LED_NUMBER_OF_TASKS   2 

/* LED toggle wait time and check definitions */
#define LED1_Wait_Time  1000
#define LED2_Wait_Time  100

/* Task function prototypes */
static void vLEDToggleTask1( void *pvParameters);
static void vLEDToggleTask2( void *pvParameters);

/* Port Initialization for LED's and Switch */
static void prvLEDInit(void);

/* Switch press counter */
static unsigned portSHORT usClick = 0;

/* Queue used for LED02 toggle*/ 
static xQueueHandle xLEDQueue;

/*xQUEUE *xLEDQueue;*/ 

static volatile unsigned portSHORT usTask1Check = 0, usTask2Check = 0, usLEDQueue = 0;

void vStartLEDToggleTasks( unsigned portBASE_TYPE uxPriority )
{

const unsigned portBASE_TYPE uxQueueSize = 4;

        prvLEDInit();

	/* Create the queue used by the Switch ISR and the second task. */
	xLEDQueue = xQueueCreate( uxQueueSize, ( unsigned portBASE_TYPE ) sizeof( unsigned portSHORT ) );
        /* create 2 LED toggle Tasks */
        xTaskCreate(vLEDToggleTask1, "LEDTog1", LEDToggleSTACK_SIZE, ( void * ) &(usTask1Check), uxPriority, NULL );
        xTaskCreate(vLEDToggleTask2, "LEDTog2", LEDToggleSTACK_SIZE, ( void * ) &xLEDQueue, uxPriority, NULL );  
}
/*-----------------------------------------------------------*/

static void vLEDToggleTask1( void *pvParameters)
{
static portCHAR pcLED1old;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const portCHAR * const pcTaskFailMsg = "ERROR: LED toggle failed.\r\n";
  
        pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;  
        for(;;)
        {
                pcLED1old = LED01;
                
                vTaskDelay( LED1_Wait_Time );
                /* toggle the LED01 */
                LED01 = ~LED01;

                if(pcLED1old == LED01)
                {
                        /* an error has occured */
                        vPrintDisplayMessage( &pcTaskFailMsg );
                        sError = pdTRUE;
                }
                
                if(sError != pdTRUE)
                {
			/* If a LED toggle has been made, increment the check
			variable so we know this task is still running okay. */
			( *pusTaskCheckVariable )++;
                }
        }              
} 
/*-----------------------------------------------------------*/

static void vLEDToggleTask2( void *pvParameters)
{
unsigned portSHORT usData, usDataOld = 0;
xQueueHandle *pxQueue;
 
        pxQueue = ( xQueueHandle * ) pvParameters;
        for(;;)
        {
                if( xQueueReceive( *pxQueue, &usData, ( portTickType ) 0 ) == pdPASS )
                {
                        if (usData != usDataOld)
                        {
                                LED02 = ~LED02;
                        }
                        usDataOld = usData;
                }
                vTaskDelay( LED2_Wait_Time );
                /* increment check variable whenever the task gets active */
                usTask2Check++;
        }              
}

portBASE_TYPE xAreLEDToggleTaskStillRunning( void )
{
/* 
 * Keep a history of the check variables so we know if they have been incremented 
 * since the last call.
 */
static unsigned portSHORT usLastTask1Check = 0;
static unsigned portSHORT usLastTask2Check = 0;
portBASE_TYPE xReturn = pdTRUE;

	/* Check the LED toggle tasks are still running by ensuring their check variables 
	 * are still incrementing. 
         */
	if(( usTask1Check == usLastTask1Check )||(usLastTask2Check == usTask2Check))
	{
		/* The check has not incremented so an error exists. */
		xReturn = pdFALSE;
	}

	usLastTask1Check = usTask1Check;
      	usLastTask2Check = usTask2Check;

        return xReturn;
}
/*-----------------------------------------------------------*/

static void prvLEDInit(void)
{
/* LED Port Initialization */
        /* set Port Register */
        P7  = 0x80;
        /* set Port Mode Register */
        PM7 = 0x3F;  

/* Switch Pin Initialization */        
        /* enable pull-up resistor */ 
        PU12_bit.no0  = 1;               
        /* INTP0 disable */
	PMK0 = 1;			
        /* INTP0 IF clear */
	PIF0 = 0;			
	EGN0_bit.no0  = 1;
	/* INTP0 priority low */
	PPR10 = 0;
	PPR00 = 1;
        /* enable ext. INTP0 interrupt */
        PMK0  = 0; 
}
/*-----------------------------------------------------------*/

/* Switch ISR */

#pragma vector=INTP0_vect
__interrupt void P0_isr (void)
{
        /* Increment Switch pressed counter */
        usClick++;
        /* Use usClick to signalize a detected Interrupt for the vLEDToggleTask2
         * to toggle the LED02.
         */
        xQueueSendFromISR( xLEDQueue, &usClick, pdFALSE );
}
/*-----------------------------------------------------------*/