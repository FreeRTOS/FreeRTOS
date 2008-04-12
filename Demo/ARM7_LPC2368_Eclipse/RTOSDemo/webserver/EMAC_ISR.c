#include "FreeRTOS.h"
#include "Semphr.h"
#include "task.h"

/* The interrupt entry point. */
void vEMAC_ISR_Wrapper( void ) __attribute__((naked));

/* The handler that does the actual work. */
void vEMAC_ISR_Handler( void );

extern xSemaphoreHandle xEMACSemaphore;


void vEMAC_ISR_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

    /* Clear the interrupt. */
    MAC_INTCLEAR = 0xffff;
    VICVectAddr = 0;

    /* Ensure the uIP task is not blocked as data has arrived. */
    xSemaphoreGiveFromISR( xEMACSemaphore, &xHigherPriorityTaskWoken );

	if( xHigherPriorityTaskWoken )
    {
    	/* Giving the semaphore woke a task. */
        portYIELD_FROM_ISR();
    }
}
/*-----------------------------------------------------------*/

void vEMAC_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
    portSAVE_CONTEXT();
    
    /* Call the handler.  This must be a separate function unless you can
    guarantee that no stack will be used. */
    vEMAC_ISR_Handler();
    
    /* Restore the context of whichever task is going to run next. */
    portRESTORE_CONTEXT();
}

