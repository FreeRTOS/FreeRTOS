/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

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
 * This is a simple LED toggle test for the V850ES/Fx3.
 *
 * Creates two task that control one LED each. 
 *
 * The first task toggles a LED with a frequency of 1Hz by using the vTaskDelay 
 * function. So the task is yielded for 1 seconed after each LED switch.
 *
 * The second LED also starts with a toggling frequency of 1Hz but this frequency
 * can be increased by pushing the switch button conected to pin INTP0. 
 * When the switch is pushed it is detected by an interrupt. When the interrupt
 * occurs a flag is set in the ISR and sent to the third task by using a queue. 
 * Therefore the  xQueueSendFromISR() function is called from within the ISR to
 * write the flag value to the queue. The task uses the xQueueReceive() function
 * to read the flag value from the queue.
 * If the flag value changed from the last task activation the yield time for the
 * second LED is incremented by 100ms. If the yield time reaches a time greater
 * then 3 seconds it is set back to 1 second within task 3.
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
#define SwitchSTACK_SIZE    (( unsigned portSHORT ) configMINIMAL_STACK_SIZE)
#define LED_NUMBER_OF_TASKS   2 

/* LED toggle wait time and check definitions */
static portTickType LED1_Wait_Time   = 1000;
static portTickType LED2_Wait_Time   = 1000;
static portTickType SWITCH_Wait_Time = 50;

/* Task function prototypes */
static void vLEDToggleTask1  ( void *pvParameters );
static void vLEDToggleTask2  ( void *pvParameters );
static void vSWITCHDelayTask ( void *pvParameters );

/* Port Initialization for LED's and Switch */
static void prvLEDInit(void);

/* Switch press counter */
static unsigned portSHORT usClick = 0;
/* Queue used for LED02 toggle*/ 
static xQueueHandle xSwitchQueue;

/*xQUEUE *xLEDQueue;*/ 

static volatile unsigned portSHORT usTask1Check = 0, usTask2Check = 0, usTask3Check = 0, usLEDQueue = 0;

void vStartLEDToggleTasks( unsigned portBASE_TYPE uxPriority )
{

const unsigned portBASE_TYPE uxQueueSize = 4;

        prvLEDInit();

	/* Create the queue used by the Switch ISR and the second task. */
	xSwitchQueue = xQueueCreate( uxQueueSize, ( unsigned portBASE_TYPE ) sizeof( unsigned portSHORT ) );
        /* create 2 LED toggle Tasks */
        xTaskCreate(vLEDToggleTask1, "LEDTog1", LEDToggleSTACK_SIZE, ( void * ) &(usTask1Check), uxPriority, NULL );
        xTaskCreate(vLEDToggleTask2, "LEDTog2", LEDToggleSTACK_SIZE, ( void * ) &(usTask2Check), uxPriority, NULL );  
        xTaskCreate(vSWITCHDelayTask, "SWITCH", SwitchSTACK_SIZE, ( void * ) &xSwitchQueue, (uxPriority+1), NULL );  
}
/*---------------------------------------------------------------------------*/
static void vLEDToggleTask1( void *pvParameters)
{
static portCHAR pcLED1old;
static portCHAR LEDcounter1 = 0;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const portCHAR * const pcTaskFailMsg = "ERROR: LED toggle failed.\r\n";
  
        pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;  
        for(;;)
        {
                pcLED1old = LED01;
                LED01 = ~LED01;
                LEDcounter1++;
                vTaskDelay( LED1_Wait_Time );
                /* toggle the LED01 */
                
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
static portCHAR pcLED2old;
portSHORT sError = pdFALSE;
volatile unsigned portSHORT *pusTaskCheckVariable;
const portCHAR * const pcTaskFailMsg = "ERROR: LED toggle failed.\r\n";
  
        pusTaskCheckVariable = ( unsigned portSHORT * ) pvParameters;  
        for(;;)
        {
                pcLED2old = LED02;
                /* toggle the LED02 */
                LED02 = ~LED02;
                vTaskDelay( LED2_Wait_Time );             
                if(pcLED2old == LED02)
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

static void vSWITCHDelayTask( void *pvParameters)
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
                                LED2_Wait_Time += 100;
                                if(LED2_Wait_Time >= 3000)
                                {
                                    LED2_Wait_Time = 1000;
                                }
                        }
                        usDataOld = usData;
                }
                vTaskDelay( SWITCH_Wait_Time );
                /* increment check variable whenever the task gets active */
                usTask3Check++;
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
static unsigned portSHORT usLastTask3Check = 0;
portBASE_TYPE xReturn = pdTRUE;

	/* Check the LED toggle tasks are still running by ensuring their check variables 
	 * are still incrementing. 
         */
	if(( usTask1Check == usLastTask1Check )||(usLastTask2Check == usTask2Check)||(usLastTask3Check == usTask3Check))
	{
		/* The check has not incremented so an error exists. */
		xReturn = pdFALSE;
	}

	usLastTask1Check = usTask1Check;
      	usLastTask2Check = usTask2Check;
      	usLastTask3Check = usTask3Check;
        
        return xReturn;
}
/*-----------------------------------------------------------*/

static void prvLEDInit(void)
{
  
	INTR0 = 0x00;
	INTR1 = 0x00;
	INTR3L = 0x00;
	INTR3H = 0x00;
	INTR4 = 0x00;
	INTR6L = 0x00;
	INTR6H = 0x00;
	INTR8 = 0x00;
	INTR9H = 0x00;
	
	INTF0 = 0x00;
	INTF1 = 0x00;
	INTF3L = 0x00;
	INTF3H = 0x00;
	INTF4 = 0x00;
	INTF6L = 0x00;
	INTF6H = 0x00;	
	INTF8 = 0x00;
	INTF9H = 0x00;  
  
/* LED Port Initialization */
//        PCM = 0x00; 
	PMCM  = 0xF2;
	PMCCM = 0x00;

/* Switch Pin Initialization */        
	/* INTP0 Setting */
	PMK0 = 1;	/* INTP0 disable */
	PIF0 = 0;	/* INTP0 IF clear */
	/* Set INTP0 lowest priority */
	PIC0 |= 0x07;
	INTR0 |= 0x00;
	INTF0 |= 0x08;
	/* INTP0 pin set */
	PFC0 &= 0xF7;
        PFCE0 &= 0xF7;
	PMC0 |= 0x08;
	
	PIF0 = 0;		/* INTP0 IF clear */
	PMK0 = 0;		/* INTP0 enable */
}
/*-----------------------------------------------------------*/

/* Switch ISR */

#pragma vector=INTP0_vector
__interrupt void MD_INTP0(void)
{
        /* Increment Switch pressed counter */
        usClick++;
        /* Use usClick to signalize a detected Interrupt for the vLEDToggleTask2
         * to toggle the LED02.
         */
        xQueueSendFromISR( xSwitchQueue, &usClick, pdFALSE );
}
/*-----------------------------------------------------------*/