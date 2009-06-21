/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

#ifndef INC_FREERTOS_H
	#error "#include FreeRTOS.h" must appear in source files before "#include queue.h"
#endif




#ifndef QUEUE_H
#define QUEUE_H

#ifdef __cplusplus
extern "C" {
#endif
typedef void * xQueueHandle;

/* For internal use only. */
#define	queueSEND_TO_BACK	( 0 )
#define	queueSEND_TO_FRONT	( 1 )


/**
 * queue. h
 * <pre>
 xQueueHandle xQueueCreate(
                              unsigned portBASE_TYPE uxQueueLength,
                              unsigned portBASE_TYPE uxItemSize
                          );
 * </pre>
 *
 * Creates a new queue instance.  This allocates the storage required by the
 * new queue and returns a handle for the queue.
 *
 * @param uxQueueLength The maximum number of items that the queue can contain.
 *
 * @param uxItemSize The number of bytes each item in the queue will require.
 * Items are queued by copy, not by reference, so this is the number of bytes
 * that will be copied for each posted item.  Each item on the queue must be
 * the same size.
 *
 * @return If the queue is successfully create then a handle to the newly
 * created queue is returned.  If the queue cannot be created then 0 is
 * returned.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 };

 void vATask( void *pvParameters )
 {
 xQueueHandle xQueue1, xQueue2;

    // Create a queue capable of containing 10 unsigned long values.
    xQueue1 = xQueueCreate( 10, sizeof( unsigned portLONG ) );
    if( xQueue1 == 0 )
    {
        // Queue was not created and must not be used.
    }

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue2 = xQueueCreate( 10, sizeof( struct AMessage * ) );
    if( xQueue2 == 0 )
    {
        // Queue was not created and must not be used.
    }

    // ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueCreate xQueueCreate
 * \ingroup QueueManagement
 */
xQueueHandle xQueueCreate( unsigned portBASE_TYPE uxQueueLength, unsigned portBASE_TYPE uxItemSize );

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueSendToToFront(
                                   xQueueHandle xQueue,
                                   const void * pvItemToQueue,
                                   portTickType xTicksToWait
                               );
 * </pre>
 *
 * This is a macro that calls xQueueGenericSend().
 *
 * Post an item to the front of a queue.  The item is queued by copy, not by
 * reference.  This function must not be called from an interrupt service
 * routine.  See xQueueSendFromISR () for an alternative which may be used
 * in an ISR.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for space to become available on the queue, should it already
 * be full.  The call will return immediately if this is set to 0 and the
 * queue is full.  The time is defined in tick periods so the constant 
 * portTICK_RATE_MS should be used to convert to real time if this is required.
 *
 * @return pdTRUE if the item was successfully posted, otherwise errQUEUE_FULL.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 unsigned portLONG ulVar = 10UL;

 void vATask( void *pvParameters )
 {
 xQueueHandle xQueue1, xQueue2;
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 unsigned long values.
    xQueue1 = xQueueCreate( 10, sizeof( unsigned portLONG ) );

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue2 = xQueueCreate( 10, sizeof( struct AMessage * ) );

    // ...

    if( xQueue1 != 0 )
    {
        // Send an unsigned long.  Wait for 10 ticks for space to become
        // available if necessary.
        if( xQueueSendToFront( xQueue1, ( void * ) &ulVar, ( portTickType ) 10 ) != pdPASS )
        {
            // Failed to post the message, even after 10 ticks.
        }
    }

    if( xQueue2 != 0 )
    {
        // Send a pointer to a struct AMessage object.  Don't block if the
        // queue is already full.
        pxMessage = & xMessage;
        xQueueSendToFront( xQueue2, ( void * ) &pxMessage, ( portTickType ) 0 );
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueSend xQueueSend
 * \ingroup QueueManagement
 */
#define xQueueSendToFront( xQueue, pvItemToQueue, xTicksToWait ) xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_FRONT )

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueSendToBack(
                                   xQueueHandle xQueue,
                                   const void * pvItemToQueue,
                                   portTickType xTicksToWait
                               );
 * </pre>
 *
 * This is a macro that calls xQueueGenericSend().
 *
 * Post an item to the back of a queue.  The item is queued by copy, not by
 * reference.  This function must not be called from an interrupt service
 * routine.  See xQueueSendFromISR () for an alternative which may be used
 * in an ISR.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for space to become available on the queue, should it already
 * be full.  The call will return immediately if this is set to 0 and the queue
 * is full.  The  time is defined in tick periods so the constant 
 * portTICK_RATE_MS should be used to convert to real time if this is required.
 *
 * @return pdTRUE if the item was successfully posted, otherwise errQUEUE_FULL.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 unsigned portLONG ulVar = 10UL;

 void vATask( void *pvParameters )
 {
 xQueueHandle xQueue1, xQueue2;
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 unsigned long values.
    xQueue1 = xQueueCreate( 10, sizeof( unsigned portLONG ) );

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue2 = xQueueCreate( 10, sizeof( struct AMessage * ) );

    // ...

    if( xQueue1 != 0 )
    {
        // Send an unsigned long.  Wait for 10 ticks for space to become
        // available if necessary.
        if( xQueueSendToBack( xQueue1, ( void * ) &ulVar, ( portTickType ) 10 ) != pdPASS )
        {
            // Failed to post the message, even after 10 ticks.
        }
    }

    if( xQueue2 != 0 )
    {
        // Send a pointer to a struct AMessage object.  Don't block if the
        // queue is already full.
        pxMessage = & xMessage;
        xQueueSendToBack( xQueue2, ( void * ) &pxMessage, ( portTickType ) 0 );
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueSend xQueueSend
 * \ingroup QueueManagement
 */
#define xQueueSendToBack( xQueue, pvItemToQueue, xTicksToWait ) xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_BACK )

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueSend(
                              xQueueHandle xQueue,
                              const void * pvItemToQueue,
                              portTickType xTicksToWait
                         );
 * </pre>
 *
 * This is a macro that calls xQueueGenericSend().  It is included for
 * backward compatibility with versions of FreeRTOS.org that did not
 * include the xQueueSendToFront() and xQueueSendToBack() macros.  It is
 * equivalent to xQueueSendToBack().
 *
 * Post an item on a queue.  The item is queued by copy, not by reference.
 * This function must not be called from an interrupt service routine.
 * See xQueueSendFromISR () for an alternative which may be used in an ISR.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for space to become available on the queue, should it already
 * be full.  The call will return immediately if this is set to 0 and the
 * queue is full.  The time is defined in tick periods so the constant 
 * portTICK_RATE_MS should be used to convert to real time if this is required.
 *
 * @return pdTRUE if the item was successfully posted, otherwise errQUEUE_FULL.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 unsigned portLONG ulVar = 10UL;

 void vATask( void *pvParameters )
 {
 xQueueHandle xQueue1, xQueue2;
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 unsigned long values.
    xQueue1 = xQueueCreate( 10, sizeof( unsigned portLONG ) );

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue2 = xQueueCreate( 10, sizeof( struct AMessage * ) );

    // ...

    if( xQueue1 != 0 )
    {
        // Send an unsigned long.  Wait for 10 ticks for space to become
        // available if necessary.
        if( xQueueSend( xQueue1, ( void * ) &ulVar, ( portTickType ) 10 ) != pdPASS )
        {
            // Failed to post the message, even after 10 ticks.
        }
    }

    if( xQueue2 != 0 )
    {
        // Send a pointer to a struct AMessage object.  Don't block if the
        // queue is already full.
        pxMessage = & xMessage;
        xQueueSend( xQueue2, ( void * ) &pxMessage, ( portTickType ) 0 );
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueSend xQueueSend
 * \ingroup QueueManagement
 */
#define xQueueSend( xQueue, pvItemToQueue, xTicksToWait ) xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_BACK )


/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueGenericSend(
									xQueueHandle xQueue,
									const void * pvItemToQueue,
									portTickType xTicksToWait
									portBASE_TYPE xCopyPosition
								);
 * </pre>
 *
 * It is preferred that the macros xQueueSend(), xQueueSendToFront() and
 * xQueueSendToBack() are used in place of calling this function directly.
 *
 * Post an item on a queue.  The item is queued by copy, not by reference.
 * This function must not be called from an interrupt service routine.
 * See xQueueSendFromISR () for an alternative which may be used in an ISR.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for space to become available on the queue, should it already
 * be full.  The call will return immediately if this is set to 0 and the
 * queue is full.  The time is defined in tick periods so the constant 
 * portTICK_RATE_MS should be used to convert to real time if this is required.
 *
 * @param xCopyPosition Can take the value queueSEND_TO_BACK to place the
 * item at the back of the queue, or queueSEND_TO_FRONT to place the item
 * at the front of the queue (for high priority messages).
 *
 * @return pdTRUE if the item was successfully posted, otherwise errQUEUE_FULL.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 unsigned portLONG ulVar = 10UL;

 void vATask( void *pvParameters )
 {
 xQueueHandle xQueue1, xQueue2;
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 unsigned long values.
    xQueue1 = xQueueCreate( 10, sizeof( unsigned portLONG ) );

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue2 = xQueueCreate( 10, sizeof( struct AMessage * ) );

    // ...

    if( xQueue1 != 0 )
    {
        // Send an unsigned long.  Wait for 10 ticks for space to become
        // available if necessary.
        if( xQueueGenericSend( xQueue1, ( void * ) &ulVar, ( portTickType ) 10, queueSEND_TO_BACK ) != pdPASS )
        {
            // Failed to post the message, even after 10 ticks.
        }
    }

    if( xQueue2 != 0 )
    {
        // Send a pointer to a struct AMessage object.  Don't block if the
        // queue is already full.
        pxMessage = & xMessage;
        xQueueGenericSend( xQueue2, ( void * ) &pxMessage, ( portTickType ) 0, queueSEND_TO_BACK );
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueSend xQueueSend
 * \ingroup QueueManagement
 */
signed portBASE_TYPE xQueueGenericSend( xQueueHandle xQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueuePeek(
                             xQueueHandle xQueue,
                             void *pvBuffer,
                             portTickType xTicksToWait
                         );</pre>
 *
 * This is a macro that calls the xQueueGenericReceive() function.
 *
 * Receive an item from a queue without removing the item from the queue.
 * The item is received by copy so a buffer of adequate size must be
 * provided.  The number of bytes copied into the buffer was defined when
 * the queue was created.
 *
 * Successfully received items remain on the queue so will be returned again
 * by the next call, or a call to xQueueReceive().
 *
 * This macro must not be used in an interrupt service routine.
 *
 * @param pxQueue The handle to the queue from which the item is to be
 * received.
 *
 * @param pvBuffer Pointer to the buffer into which the received item will
 * be copied.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for an item to receive should the queue be empty at the time
 * of the call.    The time is defined in tick periods so the constant
 * portTICK_RATE_MS should be used to convert to real time if this is required.
 * xQueuePeek() will return immediately if xTicksToWait is 0 and the queue
 * is empty.
 *
 * @return pdTRUE if an item was successfully received from the queue,
 * otherwise pdFALSE.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 xQueueHandle xQueue;

 // Task to create a queue and post a value.
 void vATask( void *pvParameters )
 {
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue = xQueueCreate( 10, sizeof( struct AMessage * ) );
    if( xQueue == 0 )
    {
        // Failed to create the queue.
    }

    // ...

    // Send a pointer to a struct AMessage object.  Don't block if the
    // queue is already full.
    pxMessage = & xMessage;
    xQueueSend( xQueue, ( void * ) &pxMessage, ( portTickType ) 0 );

	// ... Rest of task code.
 }

 // Task to peek the data from the queue.
 void vADifferentTask( void *pvParameters )
 {
 struct AMessage *pxRxedMessage;

    if( xQueue != 0 )
    {
        // Peek a message on the created queue.  Block for 10 ticks if a
        // message is not immediately available.
        if( xQueuePeek( xQueue, &( pxRxedMessage ), ( portTickType ) 10 ) )
        {
            // pcRxedMessage now points to the struct AMessage variable posted
            // by vATask, but the item still remains on the queue.
        }
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueReceive xQueueReceive
 * \ingroup QueueManagement
 */
#define xQueuePeek( xQueue, pvBuffer, xTicksToWait ) xQueueGenericReceive( xQueue, pvBuffer, xTicksToWait, pdTRUE )

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueReceive(
                                 xQueueHandle xQueue,
                                 void *pvBuffer,
                                 portTickType xTicksToWait
                            );</pre>
 *
 * This is a macro that calls the xQueueGenericReceive() function.
 *
 * Receive an item from a queue.  The item is received by copy so a buffer of
 * adequate size must be provided.  The number of bytes copied into the buffer
 * was defined when the queue was created.
 *
 * Successfully received items are removed from the queue.
 *
 * This function must not be used in an interrupt service routine.  See
 * xQueueReceiveFromISR for an alternative that can.
 *
 * @param pxQueue The handle to the queue from which the item is to be
 * received.
 *
 * @param pvBuffer Pointer to the buffer into which the received item will
 * be copied.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for an item to receive should the queue be empty at the time
 * of the call.    xQueueReceive() will return immediately if xTicksToWait
 * is zero and the queue is empty.  The time is defined in tick periods so the 
 * constant portTICK_RATE_MS should be used to convert to real time if this is 
 * required.
 *
 * @return pdTRUE if an item was successfully received from the queue,
 * otherwise pdFALSE.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 xQueueHandle xQueue;

 // Task to create a queue and post a value.
 void vATask( void *pvParameters )
 {
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue = xQueueCreate( 10, sizeof( struct AMessage * ) );
    if( xQueue == 0 )
    {
        // Failed to create the queue.
    }

    // ...

    // Send a pointer to a struct AMessage object.  Don't block if the
    // queue is already full.
    pxMessage = & xMessage;
    xQueueSend( xQueue, ( void * ) &pxMessage, ( portTickType ) 0 );

	// ... Rest of task code.
 }

 // Task to receive from the queue.
 void vADifferentTask( void *pvParameters )
 {
 struct AMessage *pxRxedMessage;

    if( xQueue != 0 )
    {
        // Receive a message on the created queue.  Block for 10 ticks if a
        // message is not immediately available.
        if( xQueueReceive( xQueue, &( pxRxedMessage ), ( portTickType ) 10 ) )
        {
            // pcRxedMessage now points to the struct AMessage variable posted
            // by vATask.
        }
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueReceive xQueueReceive
 * \ingroup QueueManagement
 */
#define xQueueReceive( xQueue, pvBuffer, xTicksToWait ) xQueueGenericReceive( xQueue, pvBuffer, xTicksToWait, pdFALSE )


/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueGenericReceive(
                                       xQueueHandle xQueue,
                                       void *pvBuffer,
                                       portTickType xTicksToWait
                                       portBASE_TYPE xJustPeek
                                    );</pre>
 *
 * It is preferred that the macro xQueueReceive() be used rather than calling
 * this function directly.
 *
 * Receive an item from a queue.  The item is received by copy so a buffer of
 * adequate size must be provided.  The number of bytes copied into the buffer
 * was defined when the queue was created.
 *
 * This function must not be used in an interrupt service routine.  See
 * xQueueReceiveFromISR for an alternative that can.
 *
 * @param pxQueue The handle to the queue from which the item is to be
 * received.
 *
 * @param pvBuffer Pointer to the buffer into which the received item will
 * be copied.
 *
 * @param xTicksToWait The maximum amount of time the task should block
 * waiting for an item to receive should the queue be empty at the time
 * of the call.    The time is defined in tick periods so the constant
 * portTICK_RATE_MS should be used to convert to real time if this is required.
 * xQueueGenericReceive() will return immediately if the queue is empty and
 * xTicksToWait is 0.
 *
 * @param xJustPeek When set to true, the item received from the queue is not
 * actually removed from the queue - meaning a subsequent call to
 * xQueueReceive() will return the same item.  When set to false, the item
 * being received from the queue is also removed from the queue.
 *
 * @return pdTRUE if an item was successfully received from the queue,
 * otherwise pdFALSE.
 *
 * Example usage:
   <pre>
 struct AMessage
 {
    portCHAR ucMessageID;
    portCHAR ucData[ 20 ];
 } xMessage;

 xQueueHandle xQueue;

 // Task to create a queue and post a value.
 void vATask( void *pvParameters )
 {
 struct AMessage *pxMessage;

    // Create a queue capable of containing 10 pointers to AMessage structures.
    // These should be passed by pointer as they contain a lot of data.
    xQueue = xQueueCreate( 10, sizeof( struct AMessage * ) );
    if( xQueue == 0 )
    {
        // Failed to create the queue.
    }

    // ...

    // Send a pointer to a struct AMessage object.  Don't block if the
    // queue is already full.
    pxMessage = & xMessage;
    xQueueSend( xQueue, ( void * ) &pxMessage, ( portTickType ) 0 );

	// ... Rest of task code.
 }

 // Task to receive from the queue.
 void vADifferentTask( void *pvParameters )
 {
 struct AMessage *pxRxedMessage;

    if( xQueue != 0 )
    {
        // Receive a message on the created queue.  Block for 10 ticks if a
        // message is not immediately available.
        if( xQueueGenericReceive( xQueue, &( pxRxedMessage ), ( portTickType ) 10 ) )
        {
            // pcRxedMessage now points to the struct AMessage variable posted
            // by vATask.
        }
    }

	// ... Rest of task code.
 }
 </pre>
 * \defgroup xQueueReceive xQueueReceive
 * \ingroup QueueManagement
 */
signed portBASE_TYPE xQueueGenericReceive( xQueueHandle xQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeek );

/**
 * queue. h
 * <pre>unsigned portBASE_TYPE uxQueueMessagesWaiting( const xQueueHandle xQueue );</pre>
 *
 * Return the number of messages stored in a queue.
 *
 * @param xQueue A handle to the queue being queried.
 *
 * @return The number of messages available in the queue.
 *
 * \page uxQueueMessagesWaiting uxQueueMessagesWaiting
 * \ingroup QueueManagement
 */
unsigned portBASE_TYPE uxQueueMessagesWaiting( const xQueueHandle xQueue );

/**
 * queue. h
 * <pre>void vQueueDelete( xQueueHandle xQueue );</pre>
 *
 * Delete a queue - freeing all the memory allocated for storing of items
 * placed on the queue.
 *
 * @param xQueue A handle to the queue to be deleted.
 *
 * \page vQueueDelete vQueueDelete
 * \ingroup QueueManagement
 */
void vQueueDelete( xQueueHandle xQueue );

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueSendToFrontFromISR(
                                         xQueueHandle pxQueue,
                                         const void *pvItemToQueue,
                                         portBASE_TYPE *pxHigherPriorityTaskWoken
                                      );
 </pre>
 *
 * This is a macro that calls xQueueGenericSendFromISR().
 *
 * Post an item to the front of a queue.  It is safe to use this macro from
 * within an interrupt service routine.
 *
 * Items are queued by copy not reference so it is preferable to only
 * queue small items, especially when called from an ISR.  In most cases
 * it would be preferable to store a pointer to the item being queued.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param pxHigherPriorityTaskWoken xQueueSendToFrontFromISR() will set
 * *pxHigherPriorityTaskWoken to pdTRUE if sending to the queue caused a task
 * to unblock, and the unblocked task has a priority higher than the currently
 * running task.  If xQueueSendToFromFromISR() sets this value to pdTRUE then
 * a context switch should be requested before the interrupt is exited.
 *
 * @return pdTRUE if the data was successfully sent to the queue, otherwise
 * errQUEUE_FULL.
 *
 * Example usage for buffered IO (where the ISR can obtain more than one value
 * per call):
   <pre>
 void vBufferISR( void )
 {
 portCHAR cIn;
 portBASE_TYPE xHigherPrioritTaskWoken;

    // We have not woken a task at the start of the ISR.
    xHigherPriorityTaskWoken = pdFALSE;

    // Loop until the buffer is empty.
    do
    {
        // Obtain a byte from the buffer.
        cIn = portINPUT_BYTE( RX_REGISTER_ADDRESS );						

        // Post the byte.  
        xQueueSendToFrontFromISR( xRxQueue, &cIn, &xHigherPriorityTaskWoken );

    } while( portINPUT_BYTE( BUFFER_COUNT ) );

    // Now the buffer is empty we can switch context if necessary.
    if( xHigherPriorityTaskWoken )
    {
        taskYIELD ();
    }
 }
 </pre>
 *
 * \defgroup xQueueSendFromISR xQueueSendFromISR
 * \ingroup QueueManagement
 */
#define xQueueSendToFrontFromISR( pxQueue, pvItemToQueue, pxHigherPriorityTaskWoken ) xQueueGenericSendFromISR( pxQueue, pvItemToQueue, pxHigherPriorityTaskWoken, queueSEND_TO_FRONT )


/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueSendToBackFromISR(
                                         xQueueHandle pxQueue,
                                         const void *pvItemToQueue,
                                         portBASE_TYPE *pxHigherPriorityTaskWoken
                                      );
 </pre>
 *
 * This is a macro that calls xQueueGenericSendFromISR().
 *
 * Post an item to the back of a queue.  It is safe to use this macro from
 * within an interrupt service routine.
 *
 * Items are queued by copy not reference so it is preferable to only
 * queue small items, especially when called from an ISR.  In most cases
 * it would be preferable to store a pointer to the item being queued.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param pxHigherPriorityTaskWoken xQueueSendToBackFromISR() will set
 * *pxHigherPriorityTaskWoken to pdTRUE if sending to the queue caused a task
 * to unblock, and the unblocked task has a priority higher than the currently
 * running task.  If xQueueSendToBackFromISR() sets this value to pdTRUE then
 * a context switch should be requested before the interrupt is exited.
 *
 * @return pdTRUE if the data was successfully sent to the queue, otherwise
 * errQUEUE_FULL.
 *
 * Example usage for buffered IO (where the ISR can obtain more than one value
 * per call):
   <pre>
 void vBufferISR( void )
 {
 portCHAR cIn;
 portBASE_TYPE xHigherPriorityTaskWoken;

    // We have not woken a task at the start of the ISR.
    xHigherPriorityTaskWoken = pdFALSE;

    // Loop until the buffer is empty.
    do
    {
        // Obtain a byte from the buffer.
        cIn = portINPUT_BYTE( RX_REGISTER_ADDRESS );						

        // Post the byte.
        xQueueSendToBackFromISR( xRxQueue, &cIn, &xHigherPriorityTaskWoken );

    } while( portINPUT_BYTE( BUFFER_COUNT ) );

    // Now the buffer is empty we can switch context if necessary.
    if( xHigherPriorityTaskWoken )
    {
        taskYIELD ();
    }
 }
 </pre>
 *
 * \defgroup xQueueSendFromISR xQueueSendFromISR
 * \ingroup QueueManagement
 */
#define xQueueSendToBackFromISR( pxQueue, pvItemToQueue, pxHigherPriorityTaskWoken ) xQueueGenericSendFromISR( pxQueue, pvItemToQueue, pxHigherPriorityTaskWoken, queueSEND_TO_BACK )

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueSendFromISR(
                                     xQueueHandle pxQueue,
                                     const void *pvItemToQueue,
                                     portBASE_TYPE *pxHigherPriorityTaskWoken
                                );
 </pre>
 *
 * This is a macro that calls xQueueGenericSendFromISR().  It is included
 * for backward compatibility with versions of FreeRTOS.org that did not
 * include the xQueueSendToBackFromISR() and xQueueSendToFrontFromISR()
 * macros.
 *
 * Post an item to the back of a queue.  It is safe to use this function from
 * within an interrupt service routine.
 *
 * Items are queued by copy not reference so it is preferable to only
 * queue small items, especially when called from an ISR.  In most cases
 * it would be preferable to store a pointer to the item being queued.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param pxHigherPriorityTaskWoken xQueueSendFromISR() will set
 * *pxHigherPriorityTaskWoken to pdTRUE if sending to the queue caused a task
 * to unblock, and the unblocked task has a priority higher than the currently
 * running task.  If xQueueSendFromISR() sets this value to pdTRUE then
 * a context switch should be requested before the interrupt is exited.
 *
 * @return pdTRUE if the data was successfully sent to the queue, otherwise
 * errQUEUE_FULL.
 *
 * Example usage for buffered IO (where the ISR can obtain more than one value
 * per call):
   <pre>
 void vBufferISR( void )
 {
 portCHAR cIn;
 portBASE_TYPE xHigherPriorityTaskWoken;

    // We have not woken a task at the start of the ISR.
    xHigherPriorityTaskWoken = pdFALSE;

    // Loop until the buffer is empty.
    do
    {
        // Obtain a byte from the buffer.
        cIn = portINPUT_BYTE( RX_REGISTER_ADDRESS );						

        // Post the byte.  
        xQueueSendFromISR( xRxQueue, &cIn, &xHigherPriorityTaskWoken );

    } while( portINPUT_BYTE( BUFFER_COUNT ) );

    // Now the buffer is empty we can switch context if necessary.
    if( xHigherPriorityTaskWoken )
    {
        // Actual macro used here is port specific.
        taskYIELD_FROM_ISR ();
    }
 }
 </pre>
 *
 * \defgroup xQueueSendFromISR xQueueSendFromISR
 * \ingroup QueueManagement
 */
#define xQueueSendFromISR( pxQueue, pvItemToQueue, pxHigherPriorityTaskWoken ) xQueueGenericSendFromISR( pxQueue, pvItemToQueue, pxHigherPriorityTaskWoken, queueSEND_TO_BACK )

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueGenericSendFromISR(
                                           xQueueHandle pxQueue,
                                           const void *pvItemToQueue,
                                           portBASE_TYPE *pxHigherPriorityTaskWoken,
										   portBASE_TYPE xCopyPosition
                                       );
 </pre>
 *
 * It is preferred that the macros xQueueSendFromISR(),
 * xQueueSendToFrontFromISR() and xQueueSendToBackFromISR() be used in place
 * of calling this function directly.
 *
 * Post an item on a queue.  It is safe to use this function from within an
 * interrupt service routine.
 *
 * Items are queued by copy not reference so it is preferable to only
 * queue small items, especially when called from an ISR.  In most cases
 * it would be preferable to store a pointer to the item being queued.
 *
 * @param xQueue The handle to the queue on which the item is to be posted.
 *
 * @param pvItemToQueue A pointer to the item that is to be placed on the
 * queue.  The size of the items the queue will hold was defined when the
 * queue was created, so this many bytes will be copied from pvItemToQueue
 * into the queue storage area.
 *
 * @param pxHigherPriorityTaskWoken xQueueGenericSendFromISR() will set
 * *pxHigherPriorityTaskWoken to pdTRUE if sending to the queue caused a task
 * to unblock, and the unblocked task has a priority higher than the currently
 * running task.  If xQueueGenericSendFromISR() sets this value to pdTRUE then
 * a context switch should be requested before the interrupt is exited.
 *
 * @param xCopyPosition Can take the value queueSEND_TO_BACK to place the
 * item at the back of the queue, or queueSEND_TO_FRONT to place the item
 * at the front of the queue (for high priority messages).
 *
 * @return pdTRUE if the data was successfully sent to the queue, otherwise
 * errQUEUE_FULL.
 *
 * Example usage for buffered IO (where the ISR can obtain more than one value
 * per call):
   <pre>
 void vBufferISR( void )
 {
 portCHAR cIn;
 portBASE_TYPE xHigherPriorityTaskWokenByPost;

    // We have not woken a task at the start of the ISR.
    xHigherPriorityTaskWokenByPost = pdFALSE;

    // Loop until the buffer is empty.
    do
    {
        // Obtain a byte from the buffer.
        cIn = portINPUT_BYTE( RX_REGISTER_ADDRESS );						

        // Post each byte.
        xQueueGenericSendFromISR( xRxQueue, &cIn, &xHigherPriorityTaskWokenByPost, queueSEND_TO_BACK );

    } while( portINPUT_BYTE( BUFFER_COUNT ) );

    // Now the buffer is empty we can switch context if necessary.  Note that the
    // name of the yield function required is port specific.
    if( xHigherPriorityTaskWokenByPost )
    {
        taskYIELD_YIELD_FROM_ISR();
    }
 }
 </pre>
 *
 * \defgroup xQueueSendFromISR xQueueSendFromISR
 * \ingroup QueueManagement
 */
signed portBASE_TYPE xQueueGenericSendFromISR( xQueueHandle pxQueue, const void * const pvItemToQueue, signed portBASE_TYPE *pxHigherPriorityTaskWoken, portBASE_TYPE xCopyPosition );

/**
 * queue. h
 * <pre>
 portBASE_TYPE xQueueReceiveFromISR(
                                       xQueueHandle pxQueue,
                                       void *pvBuffer,
                                       portBASE_TYPE *pxTaskWoken
                                   );
 * </pre>
 *
 * Receive an item from a queue.  It is safe to use this function from within an
 * interrupt service routine.
 *
 * @param pxQueue The handle to the queue from which the item is to be
 * received.
 *
 * @param pvBuffer Pointer to the buffer into which the received item will
 * be copied.
 *
 * @param pxTaskWoken A task may be blocked waiting for space to become
 * available on the queue.  If xQueueReceiveFromISR causes such a task to
 * unblock *pxTaskWoken will get set to pdTRUE, otherwise *pxTaskWoken will
 * remain unchanged.
 *
 * @return pdTRUE if an item was successfully received from the queue,
 * otherwise pdFALSE.
 *
 * Example usage:
   <pre>

 xQueueHandle xQueue;

 // Function to create a queue and post some values.
 void vAFunction( void *pvParameters )
 {
 portCHAR cValueToPost;
 const portTickType xBlockTime = ( portTickType )0xff;

    // Create a queue capable of containing 10 characters.
    xQueue = xQueueCreate( 10, sizeof( portCHAR ) );
    if( xQueue == 0 )
    {
        // Failed to create the queue.
    }

    // ...

    // Post some characters that will be used within an ISR.  If the queue
    // is full then this task will block for xBlockTime ticks.
    cValueToPost = 'a';
    xQueueSend( xQueue, ( void * ) &cValueToPost, xBlockTime );
    cValueToPost = 'b';
    xQueueSend( xQueue, ( void * ) &cValueToPost, xBlockTime );

    // ... keep posting characters ... this task may block when the queue
    // becomes full.

    cValueToPost = 'c';
    xQueueSend( xQueue, ( void * ) &cValueToPost, xBlockTime );
 }

 // ISR that outputs all the characters received on the queue.
 void vISR_Routine( void )
 {
 portBASE_TYPE xTaskWokenByReceive = pdFALSE;
 portCHAR cRxedChar;

    while( xQueueReceiveFromISR( xQueue, ( void * ) &cRxedChar, &xTaskWokenByReceive) )
    {
        // A character was received.  Output the character now.
        vOutputCharacter( cRxedChar );

        // If removing the character from the queue woke the task that was
        // posting onto the queue cTaskWokenByReceive will have been set to
        // pdTRUE.  No matter how many times this loop iterates only one
        // task will be woken.
    }

    if( cTaskWokenByPost != ( portCHAR ) pdFALSE;
    {
        taskYIELD ();
    }
 }
 </pre>
 * \defgroup xQueueReceiveFromISR xQueueReceiveFromISR
 * \ingroup QueueManagement
 */
signed portBASE_TYPE xQueueReceiveFromISR( xQueueHandle pxQueue, void * const pvBuffer, signed portBASE_TYPE *pxTaskWoken );

/*
 * Utilities to query queue that are safe to use from an ISR.  These utilities
 * should be used only from witin an ISR, or within a critical section.
 */
signed portBASE_TYPE xQueueIsQueueEmptyFromISR( const xQueueHandle pxQueue );
signed portBASE_TYPE xQueueIsQueueFullFromISR( const xQueueHandle pxQueue );
unsigned portBASE_TYPE uxQueueMessagesWaitingFromISR( const xQueueHandle pxQueue );


/* 
 * xQueueAltGenericSend() is an alternative version of xQueueGenericSend().
 * Likewise xQueueAltGenericReceive() is an alternative version of
 * xQueueGenericReceive().
 *
 * The source code that implements the alternative (Alt) API is much 
 * simpler	because it executes everything from within a critical section.  
 * This is	the approach taken by many other RTOSes, but FreeRTOS.org has the 
 * preferred fully featured API too.  The fully featured API has more 
 * complex	code that takes longer to execute, but makes much less use of 
 * critical sections.  Therefore the alternative API sacrifices interrupt 
 * responsiveness to gain execution speed, whereas the fully featured API
 * sacrifices execution speed to ensure better interrupt responsiveness.
 */
signed portBASE_TYPE xQueueAltGenericSend( xQueueHandle pxQueue, const void * const pvItemToQueue, portTickType xTicksToWait, portBASE_TYPE xCopyPosition );
signed portBASE_TYPE xQueueAltGenericReceive( xQueueHandle pxQueue, void * const pvBuffer, portTickType xTicksToWait, portBASE_TYPE xJustPeeking );
#define xQueueAltSendToFront( xQueue, pvItemToQueue, xTicksToWait ) xQueueAltGenericSend( xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_FRONT )
#define xQueueAltSendToBack( xQueue, pvItemToQueue, xTicksToWait ) xQueueAltGenericSend( xQueue, pvItemToQueue, xTicksToWait, queueSEND_TO_BACK )
#define xQueueAltReceive( xQueue, pvBuffer, xTicksToWait ) xQueueAltGenericReceive( xQueue, pvBuffer, xTicksToWait, pdFALSE )
#define xQueueAltPeek( xQueue, pvBuffer, xTicksToWait ) xQueueAltGenericReceive( xQueue, pvBuffer, xTicksToWait, pdTRUE )

/*
 * The functions defined above are for passing data to and from tasks.  The
 * functions below are the equivalents for passing data to and from
 * co-routines.
 *
 * These functions are called from the co-routine macro implementation and
 * should not be called directly from application code.  Instead use the macro
 * wrappers defined within croutine.h.
 */
signed portBASE_TYPE xQueueCRSendFromISR( xQueueHandle pxQueue, const void *pvItemToQueue, signed portBASE_TYPE xCoRoutinePreviouslyWoken );
signed portBASE_TYPE xQueueCRReceiveFromISR( xQueueHandle pxQueue, void *pvBuffer, signed portBASE_TYPE *pxTaskWoken );
signed portBASE_TYPE xQueueCRSend( xQueueHandle pxQueue, const void *pvItemToQueue, portTickType xTicksToWait );
signed portBASE_TYPE xQueueCRReceive( xQueueHandle pxQueue, void *pvBuffer, portTickType xTicksToWait );

/*
 * For internal use only.  Use xSemaphoreCreateMutex() or
 * xSemaphoreCreateCounting() instead of calling these functions directly.
 */
xQueueHandle xQueueCreateMutex( void );
xQueueHandle xQueueCreateCountingSemaphore( unsigned portBASE_TYPE uxCountValue, unsigned portBASE_TYPE uxInitialCount );

/*
 * For internal use only.  Use xSemaphoreTakeMutexRecursive() or
 * xSemaphoreGiveMutexRecursive() instead of calling these functions directly.
 */
portBASE_TYPE xQueueTakeMutexRecursive( xQueueHandle xMutex, portTickType xBlockTime );
portBASE_TYPE xQueueGiveMutexRecursive( xQueueHandle xMutex );

/*
 * The registry is provided as a means for kernel aware debuggers to
 * locate queues, semaphores and mutexes.  Call vQueueAddToRegistry() add
 * a queue, semaphore or mutex handle to the registry if you want the handle 
 * to be available to a kernel aware debugger.  If you are not using a kernel 
 * aware debugger then this function can be ignored.
 *
 * configQUEUE_REGISTRY_SIZE defines the maximum number of handles the
 * registry can hold.  configQUEUE_REGISTRY_SIZE must be greater than 0 
 * within FreeRTOSConfig.h for the registry to be available.  Its value
 * does not effect the number of queues, semaphores and mutexes that can be 
 * created - just the number that the registry can hold.
 *
 * @param xQueue The handle of the queue being added to the registry.  This
 * is the handle returned by a call to xQueueCreate().  Semaphore and mutex
 * handles can also be passed in here.
 *
 * @param pcName The name to be associated with the handle.  This is the
 * name that the kernel aware debugger will display.
 */
#if configQUEUE_REGISTRY_SIZE > 0
	void vQueueAddToRegistry( xQueueHandle xQueue, signed portCHAR *pcName );
#endif




#ifdef __cplusplus
}
#endif

#endif /* QUEUE_H */

