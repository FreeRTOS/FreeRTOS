/*
	FreeRTOS.org V4.7.0 - Copyright (C) 2003-2007 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
	***************************************************************************
*/

#ifndef SEMAPHORE_H
#define SEMAPHORE_H

#include "queue.h"

typedef xQueueHandle xSemaphoreHandle;

#define semBINARY_SEMAPHORE_QUEUE_LENGTH	( ( unsigned portCHAR ) 1 )
#define semSEMAPHORE_QUEUE_ITEM_LENGTH		( ( unsigned portCHAR ) 0 )
#define semGIVE_BLOCK_TIME					( ( portTickType ) 0 )


/**
 * semphr. h
 * <pre>vSemaphoreCreateBinary( xSemaphoreHandle xSemaphore )</pre>
 *
 * <i>Macro</i> that implements a semaphore by using the existing queue mechanism.
 * The queue length is 1 as this is a binary semaphore.  The data size is 0
 * as we don't want to actually store any data - we just want to know if the
 * queue is empty or full.
 *
 * This type of semaphore can be used for pure synchronisation between tasks or
 * between an interrupt and a task.  The semaphore need not be given back once
 * obtained, so one task/interrupt can continuously 'give' the semaphore while
 * another continuously 'takes' the semaphore.  For this reason this type of
 * semaphore does not use a priority inheritance mechanism.  For an alternative
 * that does use priority inheritance see xSemaphoreCreateMutex().
 *
 * @param xSemaphore Handle to the created semaphore.  Should be of type xSemaphoreHandle.
 *
 * Example usage:
 <pre>
 xSemaphoreHandle xSemaphore;

 void vATask( void * pvParameters )
 {
    // Semaphore cannot be used before a call to vSemaphoreCreateBinary ().
    // This is a macro so pass the variable in directly.
    vSemaphoreCreateBinary( xSemaphore );

    if( xSemaphore != NULL )
    {
        // The semaphore was created successfully.
        // The semaphore can now be used.  
    }
 }
 </pre>
 * \defgroup vSemaphoreCreateBinary vSemaphoreCreateBinary
 * \ingroup Semaphores
 */
#define vSemaphoreCreateBinary( xSemaphore )		{																								\
														xSemaphore = xQueueCreate( ( unsigned portBASE_TYPE ) 1, semSEMAPHORE_QUEUE_ITEM_LENGTH );	\
														if( xSemaphore != NULL )																	\
														{																							\
															xSemaphoreGive( xSemaphore );															\
														}																							\
													}

/**
 * semphr. h
 * xSemaphoreTake( 
 *                   xSemaphoreHandle xSemaphore, 
 *                   portTickType xBlockTime 
 *               )</pre>
 *
 * <i>Macro</i> to obtain a semaphore.  The semaphore must of been created using 
 * vSemaphoreCreateBinary ().
 *
 * @param xSemaphore A handle to the semaphore being obtained.  This is the
 * handle returned by vSemaphoreCreateBinary ();
 *
 * @param xBlockTime The time in ticks to wait for the semaphore to become
 * available.  The macro portTICK_RATE_MS can be used to convert this to a
 * real time.  A block time of zero can be used to poll the semaphore.
 *
 * @return pdTRUE if the semaphore was obtained.  pdFALSE if xBlockTime
 * expired without the semaphore becoming available.
 *
 * Example usage:
 <pre>
 xSemaphoreHandle xSemaphore = NULL;

 // A task that creates a semaphore.
 void vATask( void * pvParameters )
 {
    // Create the semaphore to guard a shared resource.
    vSemaphoreCreateBinary( xSemaphore );
 }

 // A task that uses the semaphore.
 void vAnotherTask( void * pvParameters )
 {
    // ... Do other things.

    if( xSemaphore != NULL )
    {
        // See if we can obtain the semaphore.  If the semaphore is not available
        // wait 10 ticks to see if it becomes free.	
        if( xSemaphoreTake( xSemaphore, ( portTickType ) 10 ) == pdTRUE )
        {
            // We were able to obtain the semaphore and can now access the
            // shared resource.

            // ...

            // We have finished accessing the shared resource.  Release the 
            // semaphore.
            xSemaphoreGive( xSemaphore );
        }
        else
        {
            // We could not obtain the semaphore and can therefore not access
            // the shared resource safely.
        }
    }
 }
 </pre>
 * \defgroup xSemaphoreTake xSemaphoreTake
 * \ingroup Semaphores
 */
#define xSemaphoreTake( xSemaphore, xBlockTime )		xQueueGenericReceive( ( xQueueHandle ) xSemaphore, NULL, xBlockTime, pdFALSE )
#define xSemaphoreAltTake( xSemaphore, xBlockTime )		xQueueAltGenericReceive( ( xQueueHandle ) xSemaphore, NULL, xBlockTime, pdFALSE )

/**
 * semphr. h
 * <pre>xSemaphoreGive( xSemaphoreHandle xSemaphore )</pre>
 *
 * <i>Macro</i> to release a semaphore.  The semaphore must of been created using 
 * vSemaphoreCreateBinary (), and obtained using sSemaphoreTake ().
 *
 * This must not be used from an ISR.  See xSemaphoreGiveFromISR () for
 * an alternative which can be used from an ISR.
 *
 * @param xSemaphore A handle to the semaphore being released.  This is the
 * handle returned by vSemaphoreCreateBinary ();
 *
 * @return pdTRUE if the semaphore was released.  pdFALSE if an error occurred.
 * Semaphores are implemented using queues.  An error can occur if there is
 * no space on the queue to post a message - indicating that the 
 * semaphore was not first obtained correctly.
 *
 * Example usage:
 <pre>
 xSemaphoreHandle xSemaphore = NULL;

 void vATask( void * pvParameters )
 {
    // Create the semaphore to guard a shared resource.
    vSemaphoreCreateBinary( xSemaphore );

    if( xSemaphore != NULL )
    {
        if( xSemaphoreGive( xSemaphore ) != pdTRUE )
        {
            // We would expect this call to fail because we cannot give
            // a semaphore without first "taking" it!
        }

        // Obtain the semaphore - don't block if the semaphore is not
        // immediately available.
        if( xSemaphoreTake( xSemaphore, ( portTickType ) 0 ) )
        {
            // We now have the semaphore and can access the shared resource.

            // ...

            // We have finished accessing the shared resource so can free the
            // semaphore.
            if( xSemaphoreGive( xSemaphore ) != pdTRUE )
            {
                // We would not expect this call to fail because we must have
                // obtained the semaphore to get here.
            }
        }
    }
 }
 </pre>
 * \defgroup xSemaphoreGive xSemaphoreGive
 * \ingroup Semaphores
 */
#define xSemaphoreGive( xSemaphore )		xQueueGenericSend( ( xQueueHandle ) xSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK )
#define xSemaphoreAltGive( xSemaphore )		xQueueAltGenericSend( ( xQueueHandle ) xSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK )

/**
 * semphr. h
 * <pre>
 xSemaphoreGiveFromISR( 
                          xSemaphoreHandle xSemaphore, 
                          portSHORT sTaskPreviouslyWoken 
                      )</pre>
 *
 * <i>Macro</i> to  release a semaphore.  The semaphore must of been created using 
 * vSemaphoreCreateBinary (), and obtained using xSemaphoreTake ().
 *
 * Mutex type semaphores (those created using a call to xSemaphoreCreateMutex())
 * must not be used with this macro.
 *
 * This macro can be used from an ISR.
 *
 * @param xSemaphore A handle to the semaphore being released.  This is the
 * handle returned by vSemaphoreCreateBinary ();
 *
 * @param sTaskPreviouslyWoken This is included so an ISR can make multiple calls
 * to xSemaphoreGiveFromISR () from a single interrupt.  The first call
 * should always pass in pdFALSE.  Subsequent calls should pass in
 * the value returned from the previous call.  See the file serial .c in the
 * PC port for a good example of using xSemaphoreGiveFromISR ().
 *
 * @return pdTRUE if a task was woken by releasing the semaphore.  This is 
 * used by the ISR to determine if a context switch may be required following
 * the ISR.
 *
 * Example usage:
 <pre>
 #define LONG_TIME 0xffff
 #define TICKS_TO_WAIT	10
 xSemaphoreHandle xSemaphore = NULL;

 // Repetitive task.
 void vATask( void * pvParameters )
 {
    for( ;; )
    {
        // We want this task to run every 10 ticks or a timer.  The semaphore 
        // was created before this task was started

        // Block waiting for the semaphore to become available.
        if( xSemaphoreTake( xSemaphore, LONG_TIME ) == pdTRUE )
        {
            // It is time to execute.

            // ...

            // We have finished our task.  Return to the top of the loop where
            // we will block on the semaphore until it is time to execute 
            // again.
        }
    }
 }

 // Timer ISR
 void vTimerISR( void * pvParameters )
 {
 static unsigned portCHAR ucLocalTickCount = 0;

    // A timer tick has occurred.

    // ... Do other time functions.

    // Is it time for vATask () to run?
    ucLocalTickCount++;
    if( ucLocalTickCount >= TICKS_TO_WAIT )
    {
        // Unblock the task by releasing the semaphore.
        xSemaphoreGive( xSemaphore );

        // Reset the count so we release the semaphore again in 10 ticks time.
        ucLocalTickCount = 0;
    }
 }
 </pre>
 * \defgroup xSemaphoreGiveFromISR xSemaphoreGiveFromISR
 * \ingroup Semaphores
 */
#define xSemaphoreGiveFromISR( xSemaphore, xTaskPreviouslyWoken )			xQueueGenericSendFromISR( ( xQueueHandle ) xSemaphore, NULL, xTaskPreviouslyWoken, queueSEND_TO_BACK )

/**
 * semphr. h
 * <pre>xSemaphoreCreateMutex( xSemaphoreHandle xSemaphore )</pre>
 *
 * <i>Macro</i> that implements a mutex semaphore by using the existing queue 
 * mechanism.
 *
 * This type of semaphore uses a priority inheritance mechanism so a task 
 * 'taking' a semaphore MUST ALWAYS 'give' the semaphore back once the 
 * semaphore it is no longer required.  
 *
 * Mutex type semaphores cannot be used from within interrupt service routines.  
 *
 * See xSemaphoreCreateBinary() for an alternative implemnetation that can be 
 * used for pure synchronisation (where one task or interrupt always 'gives' the 
 * semaphore and another always 'takes' the semaphore) and from within interrupt 
 * service routines.
 *
 * @param xSemaphore Handle to the created mutex semaphore.  Should be of type 
 *		xSemaphoreHandle.
 *
 * Example usage:
 <pre>
 xSemaphoreHandle xSemaphore;

 void vATask( void * pvParameters )
 {
    // Semaphore cannot be used before a call to vSemaphoreCreateBinary ().
    // This is a macro so pass the variable in directly.
    vSemaphoreCreateMutex( xSemaphore );

    if( xSemaphore != NULL )
    {
        // The semaphore was created successfully.
        // The semaphore can now be used.  
    }
 }
 </pre>
 * \defgroup vSemaphoreCreateMutex vSemaphoreCreateMutex
 * \ingroup Semaphores
 */
#define xSemaphoreCreateMutex() xQueueCreateMutex()

/**
 * semphr. h
 * <pre>vSemaphoreCreateCounting( xSemaphoreHandle xSemaphore, unsigned portBASE_TYPE uxMaxCount )</pre>
 *
 * <i>Macro</i> that creates a counting semaphore by using the existing 
 * queue mechanism.  The queue length is used as the maximum count.  The data 
 * size is 0 as we don't want to actually store any data - we just want to 
 * know if the queue is empty or full.
 *
 * Counting semaphores are typically used for two things:
 *
 * 1) Counting events.  
 *
 *    In this usage scenario an event handler will 'give' a semphore each time
 *    an event occurs (incrementing the semaphore count value), and a handler 
 *    task will 'take' a semaphore each time it processes an event 
 *    (decrementing the semaphore count value).  The count value is therefore 
 *    the difference between the number of events that have occurred and the 
 *    number that have been processed.  In this case it is desirable for the 
 *    initial count value to be zero.
 *
 * 2) Resource management.
 *
 *    In this usage scenario the count value indicates the number of resources
 *    available.  To obtain control of a resource a task must first obtain a 
 *    semphoare - decrementing the semaphore count value.  When the count value
 *    reaches zero there are no free resources.  When a task finishes with the
 *    resource it 'gives' the semahore back - incrementing the semaphore count
 *    value.  In this case it is desirable for the initial count value to be
 *    equal to the maximum count value, indicating that all resources are free.
 *
 * @param uxMaxCount The maximum count value that can be reached.  When the 
 *        semaphore reaches this value it can nolonger be 'given'.
 * @param uxInitialCount
 *
 * @return Handle to the created semaphore.  Should be of type xSemaphoreHandle.
 * 
 * Example usage:
 <pre>
 xSemaphoreHandle xSemaphore;

 void vATask( void * pvParameters )
 {
 xSemaphoreHandle xSemaphore = NULL;

    // Semaphore cannot be used before a call to vSemaphoreCreateCounting().
    // This is a macro so pass the variable in directly.
    vSemaphoreCreateBinary( xSemaphore,  );

    if( xSemaphore != NULL )
    {
        // The semaphore was created successfully.
        // The semaphore can now be used.  
    }
 }
 </pre>
 * \defgroup xSemaphoreCreateCounting xSemaphoreCreateCounting
 * \ingroup Semaphores
 */
#define xSemaphoreCreateCounting( uxCountValue, uxInitialCount ) xQueueCreateCountingSemaphore( uxCountValue, uxInitialCount )

#endif /* SEMAPHORE_H */


