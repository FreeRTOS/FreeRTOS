#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* The interrupt entry point. */
void vEMAC_ISR_Wrapper( void ) __attribute__((naked));

/* The function that actually performs the interrupt processing.  This must be 
separate to the wrapper to ensure the correct stack frame is set up. */
void vEMAC_ISR_Handler( void ) __attribute__((noinline));

extern xSemaphoreHandle xEMACSemaphore;

void vEMAC_ISR_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

    /* Clear the interrupt. */
    IntClear = 0xffff;
    VICVectAddr = 0;

    /* Ensure the uIP task is not blocked as data has arrived. */
    xSemaphoreGiveFromISR( xEMACSemaphore, &xHigherPriorityTaskWoken );

	if( xHigherPriorityTaskWoken )
    {
		/* If the uIP task was unblocked then calling "Yield from ISR" here
		will ensure the interrupt returns directly to the uIP task, if it
		is the highest priority read task. */
        portYIELD_FROM_ISR();
    }
}
/*-----------------------------------------------------------*/

void vEMAC_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler function.  This must be separate from the wrapper
	function to ensure the correct stack frame is set up. */
	__asm volatile( "bl vEMAC_ISR_Handler" );

	/* Restore the context of whichever task is going to run next. */
	portRESTORE_CONTEXT();
}




