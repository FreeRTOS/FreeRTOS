/*
    FreeRTOS V7.5.3 - Copyright (C) 2013 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/


#ifndef TIMERS_H
#define TIMERS_H

#ifndef INC_FREERTOS_H
	#error "include FreeRTOS.h must appear in source files before include timers.h"
#endif

/*lint -e537 This headers are only multiply included if the application code
happens to also be including task.h. */
#include "task.h"
/*lint +e956 */

#ifdef __cplusplus
extern "C" {
#endif

/* IDs for commands that can be sent/received on the timer queue.  These are to
be used solely through the macros that make up the public software timer API,
as defined below. */
#define tmrCOMMAND_START					( ( portBASE_TYPE ) 0 )
#define tmrCOMMAND_STOP						( ( portBASE_TYPE ) 1 )
#define tmrCOMMAND_CHANGE_PERIOD			( ( portBASE_TYPE ) 2 )
#define tmrCOMMAND_DELETE					( ( portBASE_TYPE ) 3 )

/*-----------------------------------------------------------
 * MACROS AND DEFINITIONS
 *----------------------------------------------------------*/

 /**
 * Type by which software timers are referenced.  For example, a call to
 * xTimerCreate() returns an xTimerHandle variable that can then be used to
 * reference the subject timer in calls to other software timer API functions
 * (for example, xTimerStart(), xTimerReset(), etc.).
 */
typedef void * xTimerHandle;

/* Define the prototype to which timer callback functions must conform. */
typedef void (*tmrTIMER_CALLBACK)( xTimerHandle xTimer );

/**
 * xTimerHandle xTimerCreate( 	const signed char *pcTimerName,
 * 								portTickType xTimerPeriodInTicks,
 * 								unsigned portBASE_TYPE uxAutoReload,
 * 								void * pvTimerID,
 * 								tmrTIMER_CALLBACK pxCallbackFunction );
 *
 * Creates a new software timer instance.  This allocates the storage required
 * by the new timer, initialises the new timers internal state, and returns a
 * handle by which the new timer can be referenced.
 *
 * Timers are created in the dormant state.  The xTimerStart(), xTimerReset(),
 * xTimerStartFromISR(), xTimerResetFromISR(), xTimerChangePeriod() and
 * xTimerChangePeriodFromISR() API functions can all be used to transition a timer into the
 * active state.
 *
 * @param pcTimerName A text name that is assigned to the timer.  This is done
 * purely to assist debugging.  The kernel itself only ever references a timer by
 * its handle, and never by its name.
 *
 * @param xTimerPeriodInTicks The timer period.  The time is defined in tick periods so
 * the constant portTICK_RATE_MS can be used to convert a time that has been
 * specified in milliseconds.  For example, if the timer must expire after 100
 * ticks, then xTimerPeriodInTicks should be set to 100.  Alternatively, if the timer
 * must expire after 500ms, then xPeriod can be set to ( 500 / portTICK_RATE_MS )
 * provided configTICK_RATE_HZ is less than or equal to 1000.
 *
 * @param uxAutoReload If uxAutoReload is set to pdTRUE then the timer will
 * expire repeatedly with a frequency set by the xTimerPeriodInTicks parameter.  If
 * uxAutoReload is set to pdFALSE then the timer will be a one-shot timer and
 * enter the dormant state after it expires.
 *
 * @param pvTimerID An identifier that is assigned to the timer being created.
 * Typically this would be used in the timer callback function to identify which
 * timer expired when the same callback function is assigned to more than one
 * timer.
 *
 * @param pxCallbackFunction The function to call when the timer expires.
 * Callback functions must have the prototype defined by tmrTIMER_CALLBACK,
 * which is	"void vCallbackFunction( xTimerHandle xTimer );".
 *
 * @return If the timer is successfully create then a handle to the newly
 * created timer is returned.  If the timer cannot be created (because either
 * there is insufficient FreeRTOS heap remaining to allocate the timer
 * structures, or the timer period was set to 0) then 0 is returned.
 *
 * Example usage:
 * @verbatim
 * #define NUM_TIMERS 5
 *
 * // An array to hold handles to the created timers.
 * xTimerHandle xTimers[ NUM_TIMERS ];
 *
 * // An array to hold a count of the number of times each timer expires.
 * long lExpireCounters[ NUM_TIMERS ] = { 0 };
 *
 * // Define a callback function that will be used by multiple timer instances.
 * // The callback function does nothing but count the number of times the
 * // associated timer expires, and stop the timer once the timer has expired
 * // 10 times.
 * void vTimerCallback( xTimerHandle pxTimer )
 * {
 * long lArrayIndex;
 * const long xMaxExpiryCountBeforeStopping = 10;
 *
 * 	   // Optionally do something if the pxTimer parameter is NULL.
 * 	   configASSERT( pxTimer );
 * 	
 *     // Which timer expired?
 *     lArrayIndex = ( long ) pvTimerGetTimerID( pxTimer );
 *
 *     // Increment the number of times that pxTimer has expired.
 *     lExpireCounters[ lArrayIndex ] += 1;
 *
 *     // If the timer has expired 10 times then stop it from running.
 *     if( lExpireCounters[ lArrayIndex ] == xMaxExpiryCountBeforeStopping )
 *     {
 *         // Do not use a block time if calling a timer API function from a
 *         // timer callback function, as doing so could cause a deadlock!
 *         xTimerStop( pxTimer, 0 );
 *     }
 * }
 *
 * void main( void )
 * {
 * long x;
 *
 *     // Create then start some timers.  Starting the timers before the scheduler
 *     // has been started means the timers will start running immediately that
 *     // the scheduler starts.
 *     for( x = 0; x < NUM_TIMERS; x++ )
 *     {
 *         xTimers[ x ] = xTimerCreate(     "Timer",         // Just a text name, not used by the kernel.
 *                                         ( 100 * x ),     // The timer period in ticks.
 *                                         pdTRUE,         // The timers will auto-reload themselves when they expire.
 *                                         ( void * ) x,     // Assign each timer a unique id equal to its array index.
 *                                         vTimerCallback     // Each timer calls the same callback when it expires.
 *                                     );
 *
 *         if( xTimers[ x ] == NULL )
 *         {
 *             // The timer was not created.
 *         }
 *         else
 *         {
 *             // Start the timer.  No block time is specified, and even if one was
 *             // it would be ignored because the scheduler has not yet been
 *             // started.
 *             if( xTimerStart( xTimers[ x ], 0 ) != pdPASS )
 *             {
 *                 // The timer could not be set into the Active state.
 *             }
 *         }
 *     }
 *
 *     // ...
 *     // Create tasks here.
 *     // ...
 *
 *     // Starting the scheduler will start the timers running as they have already
 *     // been set into the active state.
 *     xTaskStartScheduler();
 *
 *     // Should not reach here.
 *     for( ;; );
 * }
 * @endverbatim
 */
xTimerHandle xTimerCreate( const signed char * const pcTimerName, portTickType xTimerPeriodInTicks, unsigned portBASE_TYPE uxAutoReload, void * pvTimerID, tmrTIMER_CALLBACK pxCallbackFunction ) PRIVILEGED_FUNCTION;

/**
 * void *pvTimerGetTimerID( xTimerHandle xTimer );
 *
 * Returns the ID assigned to the timer.
 *
 * IDs are assigned to timers using the pvTimerID parameter of the call to
 * xTimerCreated() that was used to create the timer.
 *
 * If the same callback function is assigned to multiple timers then the timer
 * ID can be used within the callback function to identify which timer actually
 * expired.
 *
 * @param xTimer The timer being queried.
 *
 * @return The ID assigned to the timer being queried.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 */
void *pvTimerGetTimerID( xTimerHandle xTimer ) PRIVILEGED_FUNCTION;

/**
 * portBASE_TYPE xTimerIsTimerActive( xTimerHandle xTimer );
 *
 * Queries a timer to see if it is active or dormant.
 *
 * A timer will be dormant if:
 *     1) It has been created but not started, or
 *     2) It is an expired on-shot timer that has not been restarted.
 *
 * Timers are created in the dormant state.  The xTimerStart(), xTimerReset(),
 * xTimerStartFromISR(), xTimerResetFromISR(), xTimerChangePeriod() and
 * xTimerChangePeriodFromISR() API functions can all be used to transition a timer into the
 * active state.
 *
 * @param xTimer The timer being queried.
 *
 * @return pdFALSE will be returned if the timer is dormant.  A value other than
 * pdFALSE will be returned if the timer is active.
 *
 * Example usage:
 * @verbatim
 * // This function assumes xTimer has already been created.
 * void vAFunction( xTimerHandle xTimer )
 * {
 *     if( xTimerIsTimerActive( xTimer ) != pdFALSE ) // or more simply and equivalently "if( xTimerIsTimerActive( xTimer ) )"
 *     {
 *         // xTimer is active, do something.
 *     }
 *     else
 *     {
 *         // xTimer is not active, do something else.
 *     }
 * }
 * @endverbatim
 */
portBASE_TYPE xTimerIsTimerActive( xTimerHandle xTimer ) PRIVILEGED_FUNCTION;

/**
 * xTimerGetTimerDaemonTaskHandle() is only available if 
 * INCLUDE_xTimerGetTimerDaemonTaskHandle is set to 1 in FreeRTOSConfig.h.
 *
 * Simply returns the handle of the timer service/daemon task.  It it not valid
 * to call xTimerGetTimerDaemonTaskHandle() before the scheduler has been started.
 */
xTaskHandle xTimerGetTimerDaemonTaskHandle( void );

/**
 * portBASE_TYPE xTimerStart( xTimerHandle xTimer, portTickType xBlockTime );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * though a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerStart() starts a timer that was previously created using the
 * xTimerCreate() API function.  If the timer had already been started and was
 * already in the active state, then xTimerStart() has equivalent functionality
 * to the xTimerReset() API function.
 *
 * Starting a timer ensures the timer is in the active state.  If the timer
 * is not stopped, deleted, or reset in the mean time, the callback function
 * associated with the timer will get called 'n' ticks after xTimerStart() was
 * called, where 'n' is the timers defined period.
 *
 * It is valid to call xTimerStart() before the scheduler has been started, but
 * when this is done the timer will not actually start until the scheduler is
 * started, and the timers expiry time will be relative to when the scheduler is
 * started, not relative to when xTimerStart() was called.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for xTimerStart()
 * to be available.
 *
 * @param xTimer The handle of the timer being started/restarted.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the start command to be successfully
 * sent to the timer command queue, should the queue already be full when
 * xTimerStart() was called.  xBlockTime is ignored if xTimerStart() is called
 * before the scheduler is started.
 *
 * @return pdFAIL will be returned if the start command could not be sent to
 * the timer command queue even after xBlockTime ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system, although the
 * timers expiry time is relative to when xTimerStart() is actually called.  The
 * timer service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 *
 */
#define xTimerStart( xTimer, xBlockTime ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_START, ( xTaskGetTickCount() ), NULL, ( xBlockTime ) )

/**
 * portBASE_TYPE xTimerStop( xTimerHandle xTimer, portTickType xBlockTime );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * though a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerStop() stops a timer that was previously started using either of the
 * The xTimerStart(), xTimerReset(), xTimerStartFromISR(), xTimerResetFromISR(),
 * xTimerChangePeriod() or xTimerChangePeriodFromISR() API functions.
 *
 * Stopping a timer ensures the timer is not in the active state.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for xTimerStop()
 * to be available.
 *
 * @param xTimer The handle of the timer being stopped.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the stop command to be successfully
 * sent to the timer command queue, should the queue already be full when
 * xTimerStop() was called.  xBlockTime is ignored if xTimerStop() is called
 * before the scheduler is started.
 *
 * @return pdFAIL will be returned if the stop command could not be sent to
 * the timer command queue even after xBlockTime ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system.  The timer
 * service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 *
 */
#define xTimerStop( xTimer, xBlockTime ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_STOP, 0U, NULL, ( xBlockTime ) )

/**
 * portBASE_TYPE xTimerChangePeriod( 	xTimerHandle xTimer,
 *										portTickType xNewPeriod,
 *										portTickType xBlockTime );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * though a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerChangePeriod() changes the period of a timer that was previously
 * created using the xTimerCreate() API function.
 *
 * xTimerChangePeriod() can be called to change the period of an active or
 * dormant state timer.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for
 * xTimerChangePeriod() to be available.
 *
 * @param xTimer The handle of the timer that is having its period changed.
 *
 * @param xNewPeriod The new period for xTimer. Timer periods are specified in
 * tick periods, so the constant portTICK_RATE_MS can be used to convert a time
 * that has been specified in milliseconds.  For example, if the timer must
 * expire after 100 ticks, then xNewPeriod should be set to 100.  Alternatively,
 * if the timer must expire after 500ms, then xNewPeriod can be set to
 * ( 500 / portTICK_RATE_MS ) provided configTICK_RATE_HZ is less than
 * or equal to 1000.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the change period command to be
 * successfully sent to the timer command queue, should the queue already be
 * full when xTimerChangePeriod() was called.  xBlockTime is ignored if
 * xTimerChangePeriod() is called before the scheduler is started.
 *
 * @return pdFAIL will be returned if the change period command could not be
 * sent to the timer command queue even after xBlockTime ticks had passed.
 * pdPASS will be returned if the command was successfully sent to the timer
 * command queue.  When the command is actually processed will depend on the
 * priority of the timer service/daemon task relative to other tasks in the
 * system.  The timer service/daemon task priority is set by the
 * configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This function assumes xTimer has already been created.  If the timer
 * // referenced by xTimer is already active when it is called, then the timer
 * // is deleted.  If the timer referenced by xTimer is not active when it is
 * // called, then the period of the timer is set to 500ms and the timer is
 * // started.
 * void vAFunction( xTimerHandle xTimer )
 * {
 *     if( xTimerIsTimerActive( xTimer ) != pdFALSE ) // or more simply and equivalently "if( xTimerIsTimerActive( xTimer ) )"
 *     {
 *         // xTimer is already active - delete it.
 *         xTimerDelete( xTimer );
 *     }
 *     else
 *     {
 *         // xTimer is not active, change its period to 500ms.  This will also
 *         // cause the timer to start.  Block for a maximum of 100 ticks if the
 *         // change period command cannot immediately be sent to the timer
 *         // command queue.
 *         if( xTimerChangePeriod( xTimer, 500 / portTICK_RATE_MS, 100 ) == pdPASS )
 *         {
 *             // The command was successfully sent.
 *         }
 *         else
 *         {
 *             // The command could not be sent, even after waiting for 100 ticks
 *             // to pass.  Take appropriate action here.
 *         }
 *     }
 * }
 * @endverbatim
 */
 #define xTimerChangePeriod( xTimer, xNewPeriod, xBlockTime ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_CHANGE_PERIOD, ( xNewPeriod ), NULL, ( xBlockTime ) )

/**
 * portBASE_TYPE xTimerDelete( xTimerHandle xTimer, portTickType xBlockTime );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * though a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerDelete() deletes a timer that was previously created using the
 * xTimerCreate() API function.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for
 * xTimerDelete() to be available.
 *
 * @param xTimer The handle of the timer being deleted.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the delete command to be
 * successfully sent to the timer command queue, should the queue already be
 * full when xTimerDelete() was called.  xBlockTime is ignored if xTimerDelete()
 * is called before the scheduler is started.
 *
 * @return pdFAIL will be returned if the delete command could not be sent to
 * the timer command queue even after xBlockTime ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system.  The timer
 * service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 *
 * See the xTimerChangePeriod() API function example usage scenario.
 */
#define xTimerDelete( xTimer, xBlockTime ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_DELETE, 0U, NULL, ( xBlockTime ) )

/**
 * portBASE_TYPE xTimerReset( xTimerHandle xTimer, portTickType xBlockTime );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * though a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerReset() re-starts a timer that was previously created using the
 * xTimerCreate() API function.  If the timer had already been started and was
 * already in the active state, then xTimerReset() will cause the timer to
 * re-evaluate its expiry time so that it is relative to when xTimerReset() was
 * called.  If the timer was in the dormant state then xTimerReset() has
 * equivalent functionality to the xTimerStart() API function.
 *
 * Resetting a timer ensures the timer is in the active state.  If the timer
 * is not stopped, deleted, or reset in the mean time, the callback function
 * associated with the timer will get called 'n' ticks after xTimerReset() was
 * called, where 'n' is the timers defined period.
 *
 * It is valid to call xTimerReset() before the scheduler has been started, but
 * when this is done the timer will not actually start until the scheduler is
 * started, and the timers expiry time will be relative to when the scheduler is
 * started, not relative to when xTimerReset() was called.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for xTimerReset()
 * to be available.
 *
 * @param xTimer The handle of the timer being reset/started/restarted.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the reset command to be successfully
 * sent to the timer command queue, should the queue already be full when
 * xTimerReset() was called.  xBlockTime is ignored if xTimerReset() is called
 * before the scheduler is started.
 *
 * @return pdFAIL will be returned if the reset command could not be sent to
 * the timer command queue even after xBlockTime ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system, although the
 * timers expiry time is relative to when xTimerStart() is actually called.  The
 * timer service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 * @verbatim
 * // When a key is pressed, an LCD back-light is switched on.  If 5 seconds pass
 * // without a key being pressed, then the LCD back-light is switched off.  In
 * // this case, the timer is a one-shot timer.
 *
 * xTimerHandle xBacklightTimer = NULL;
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( xTimerHandle pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD back-light.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press event handler.
 * void vKeyPressEventHandler( char cKey )
 * {
 *     // Ensure the LCD back-light is on, then reset the timer that is
 *     // responsible for turning the back-light off after 5 seconds of
 *     // key inactivity.  Wait 10 ticks for the command to be successfully sent
 *     // if it cannot be sent immediately.
 *     vSetBacklightState( BACKLIGHT_ON );
 *     if( xTimerReset( xBacklightTimer, 100 ) != pdPASS )
 *     {
 *         // The reset command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // Perform the rest of the key processing here.
 * }
 *
 * void main( void )
 * {
 * long x;
 *
 *     // Create then start the one-shot timer that is responsible for turning
 *     // the back-light off if no keys are pressed within a 5 second period.
 *     xBacklightTimer = xTimerCreate( "BacklightTimer",           // Just a text name, not used by the kernel.
 *                                     ( 5000 / portTICK_RATE_MS), // The timer period in ticks.
 *                                     pdFALSE,                    // The timer is a one-shot timer.
 *                                     0,                          // The id is not used by the callback so can take any value.
 *                                     vBacklightTimerCallback     // The callback function that switches the LCD back-light off.
 *                                   );
 *
 *     if( xBacklightTimer == NULL )
 *     {
 *         // The timer was not created.
 *     }
 *     else
 *     {
 *         // Start the timer.  No block time is specified, and even if one was
 *         // it would be ignored because the scheduler has not yet been
 *         // started.
 *         if( xTimerStart( xBacklightTimer, 0 ) != pdPASS )
 *         {
 *             // The timer could not be set into the Active state.
 *         }
 *     }
 *
 *     // ...
 *     // Create tasks here.
 *     // ...
 *
 *     // Starting the scheduler will start the timer running as it has already
 *     // been set into the active state.
 *     xTaskStartScheduler();
 *
 *     // Should not reach here.
 *     for( ;; );
 * }
 * @endverbatim
 */
#define xTimerReset( xTimer, xBlockTime ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_START, ( xTaskGetTickCount() ), NULL, ( xBlockTime ) )

/**
 * portBASE_TYPE xTimerStartFromISR( 	xTimerHandle xTimer,
 *										portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerStart() that can be called from an interrupt service
 * routine.
 *
 * @param xTimer The handle of the timer being started/restarted.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerStartFromISR() writes a message to the timer
 * command queue, so has the potential to transition the timer service/daemon
 * task out of the Blocked state.  If calling xTimerStartFromISR() causes the
 * timer service/daemon task to leave the Blocked state, and the timer service/
 * daemon task has a priority equal to or greater than the currently executing
 * task (the task that was interrupted), then *pxHigherPriorityTaskWoken will
 * get set to pdTRUE internally within the xTimerStartFromISR() function.  If
 * xTimerStartFromISR() sets this value to pdTRUE then a context switch should
 * be performed before the interrupt exits.
 *
 * @return pdFAIL will be returned if the start command could not be sent to
 * the timer command queue.  pdPASS will be returned if the command was
 * successfully sent to the timer command queue.  When the command is actually
 * processed will depend on the priority of the timer service/daemon task
 * relative to other tasks in the system, although the timers expiry time is
 * relative to when xTimerStartFromISR() is actually called.  The timer service/daemon
 * task priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xBacklightTimer has already been created.  When a
 * // key is pressed, an LCD back-light is switched on.  If 5 seconds pass
 * // without a key being pressed, then the LCD back-light is switched off.  In
 * // this case, the timer is a one-shot timer, and unlike the example given for
 * // the xTimerReset() function, the key press event handler is an interrupt
 * // service routine.
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( xTimerHandle pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD back-light.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press interrupt service routine.
 * void vKeyPressEventInterruptHandler( void )
 * {
 * portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // Ensure the LCD back-light is on, then restart the timer that is
 *     // responsible for turning the back-light off after 5 seconds of
 *     // key inactivity.  This is an interrupt service routine so can only
 *     // call FreeRTOS API functions that end in "FromISR".
 *     vSetBacklightState( BACKLIGHT_ON );
 *
 *     // xTimerStartFromISR() or xTimerResetFromISR() could be called here
 *     // as both cause the timer to re-calculate its expiry time.
 *     // xHigherPriorityTaskWoken was initialised to pdFALSE when it was
 *     // declared (in this function).
 *     if( xTimerStartFromISR( xBacklightTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The start command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // Perform the rest of the key processing here.
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used.
 *     }
 * }
 * @endverbatim
 */
#define xTimerStartFromISR( xTimer, pxHigherPriorityTaskWoken ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_START, ( xTaskGetTickCountFromISR() ), ( pxHigherPriorityTaskWoken ), 0U )

/**
 * portBASE_TYPE xTimerStopFromISR( 	xTimerHandle xTimer,
 *										portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerStop() that can be called from an interrupt service
 * routine.
 *
 * @param xTimer The handle of the timer being stopped.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerStopFromISR() writes a message to the timer
 * command queue, so has the potential to transition the timer service/daemon
 * task out of the Blocked state.  If calling xTimerStopFromISR() causes the
 * timer service/daemon task to leave the Blocked state, and the timer service/
 * daemon task has a priority equal to or greater than the currently executing
 * task (the task that was interrupted), then *pxHigherPriorityTaskWoken will
 * get set to pdTRUE internally within the xTimerStopFromISR() function.  If
 * xTimerStopFromISR() sets this value to pdTRUE then a context switch should
 * be performed before the interrupt exits.
 *
 * @return pdFAIL will be returned if the stop command could not be sent to
 * the timer command queue.  pdPASS will be returned if the command was
 * successfully sent to the timer command queue.  When the command is actually
 * processed will depend on the priority of the timer service/daemon task
 * relative to other tasks in the system.  The timer service/daemon task
 * priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xTimer has already been created and started.  When
 * // an interrupt occurs, the timer should be simply stopped.
 *
 * // The interrupt service routine that stops the timer.
 * void vAnExampleInterruptServiceRoutine( void )
 * {
 * portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // The interrupt has occurred - simply stop the timer.
 *     // xHigherPriorityTaskWoken was set to pdFALSE where it was defined
 *     // (within this function).  As this is an interrupt service routine, only
 *     // FreeRTOS API functions that end in "FromISR" can be used.
 *     if( xTimerStopFromISR( xTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The stop command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used.
 *     }
 * }
 * @endverbatim
 */
#define xTimerStopFromISR( xTimer, pxHigherPriorityTaskWoken ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_STOP, 0, ( pxHigherPriorityTaskWoken ), 0U )

/**
 * portBASE_TYPE xTimerChangePeriodFromISR( xTimerHandle xTimer,
 *											portTickType xNewPeriod,
 *											portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerChangePeriod() that can be called from an interrupt
 * service routine.
 *
 * @param xTimer The handle of the timer that is having its period changed.
 *
 * @param xNewPeriod The new period for xTimer. Timer periods are specified in
 * tick periods, so the constant portTICK_RATE_MS can be used to convert a time
 * that has been specified in milliseconds.  For example, if the timer must
 * expire after 100 ticks, then xNewPeriod should be set to 100.  Alternatively,
 * if the timer must expire after 500ms, then xNewPeriod can be set to
 * ( 500 / portTICK_RATE_MS ) provided configTICK_RATE_HZ is less than
 * or equal to 1000.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerChangePeriodFromISR() writes a message to the
 * timer command queue, so has the potential to transition the timer service/
 * daemon task out of the Blocked state.  If calling xTimerChangePeriodFromISR()
 * causes the timer service/daemon task to leave the Blocked state, and the
 * timer service/daemon task has a priority equal to or greater than the
 * currently executing task (the task that was interrupted), then
 * *pxHigherPriorityTaskWoken will get set to pdTRUE internally within the
 * xTimerChangePeriodFromISR() function.  If xTimerChangePeriodFromISR() sets
 * this value to pdTRUE then a context switch should be performed before the
 * interrupt exits.
 *
 * @return pdFAIL will be returned if the command to change the timers period
 * could not be sent to the timer command queue.  pdPASS will be returned if the
 * command was successfully sent to the timer command queue.  When the command
 * is actually processed will depend on the priority of the timer service/daemon
 * task relative to other tasks in the system.  The timer service/daemon task
 * priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xTimer has already been created and started.  When
 * // an interrupt occurs, the period of xTimer should be changed to 500ms.
 *
 * // The interrupt service routine that changes the period of xTimer.
 * void vAnExampleInterruptServiceRoutine( void )
 * {
 * portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // The interrupt has occurred - change the period of xTimer to 500ms.
 *     // xHigherPriorityTaskWoken was set to pdFALSE where it was defined
 *     // (within this function).  As this is an interrupt service routine, only
 *     // FreeRTOS API functions that end in "FromISR" can be used.
 *     if( xTimerChangePeriodFromISR( xTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The command to change the timers period was not executed
 *         // successfully.  Take appropriate action here.
 *     }
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used.
 *     }
 * }
 * @endverbatim
 */
#define xTimerChangePeriodFromISR( xTimer, xNewPeriod, pxHigherPriorityTaskWoken ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_CHANGE_PERIOD, ( xNewPeriod ), ( pxHigherPriorityTaskWoken ), 0U )

/**
 * portBASE_TYPE xTimerResetFromISR( 	xTimerHandle xTimer,
 *										portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerReset() that can be called from an interrupt service
 * routine.
 *
 * @param xTimer The handle of the timer that is to be started, reset, or
 * restarted.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerResetFromISR() writes a message to the timer
 * command queue, so has the potential to transition the timer service/daemon
 * task out of the Blocked state.  If calling xTimerResetFromISR() causes the
 * timer service/daemon task to leave the Blocked state, and the timer service/
 * daemon task has a priority equal to or greater than the currently executing
 * task (the task that was interrupted), then *pxHigherPriorityTaskWoken will
 * get set to pdTRUE internally within the xTimerResetFromISR() function.  If
 * xTimerResetFromISR() sets this value to pdTRUE then a context switch should
 * be performed before the interrupt exits.
 *
 * @return pdFAIL will be returned if the reset command could not be sent to
 * the timer command queue.  pdPASS will be returned if the command was
 * successfully sent to the timer command queue.  When the command is actually
 * processed will depend on the priority of the timer service/daemon task
 * relative to other tasks in the system, although the timers expiry time is
 * relative to when xTimerResetFromISR() is actually called.  The timer service/daemon
 * task priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xBacklightTimer has already been created.  When a
 * // key is pressed, an LCD back-light is switched on.  If 5 seconds pass
 * // without a key being pressed, then the LCD back-light is switched off.  In
 * // this case, the timer is a one-shot timer, and unlike the example given for
 * // the xTimerReset() function, the key press event handler is an interrupt
 * // service routine.
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( xTimerHandle pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD back-light.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press interrupt service routine.
 * void vKeyPressEventInterruptHandler( void )
 * {
 * portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // Ensure the LCD back-light is on, then reset the timer that is
 *     // responsible for turning the back-light off after 5 seconds of
 *     // key inactivity.  This is an interrupt service routine so can only
 *     // call FreeRTOS API functions that end in "FromISR".
 *     vSetBacklightState( BACKLIGHT_ON );
 *
 *     // xTimerStartFromISR() or xTimerResetFromISR() could be called here
 *     // as both cause the timer to re-calculate its expiry time.
 *     // xHigherPriorityTaskWoken was initialised to pdFALSE when it was
 *     // declared (in this function).
 *     if( xTimerResetFromISR( xBacklightTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The reset command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // Perform the rest of the key processing here.
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used.
 *     }
 * }
 * @endverbatim
 */
#define xTimerResetFromISR( xTimer, pxHigherPriorityTaskWoken ) xTimerGenericCommand( ( xTimer ), tmrCOMMAND_START, ( xTaskGetTickCountFromISR() ), ( pxHigherPriorityTaskWoken ), 0U )

/*
 * Functions beyond this part are not part of the public API and are intended
 * for use by the kernel only.
 */
portBASE_TYPE xTimerCreateTimerTask( void ) PRIVILEGED_FUNCTION;
portBASE_TYPE xTimerGenericCommand( xTimerHandle xTimer, portBASE_TYPE xCommandID, portTickType xOptionalValue, signed portBASE_TYPE *pxHigherPriorityTaskWoken, portTickType xBlockTime ) PRIVILEGED_FUNCTION;

#ifdef __cplusplus
}
#endif
#endif /* TIMERS_H */



