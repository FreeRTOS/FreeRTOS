/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

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


#ifndef TIMERS_H
#define TIMERS_H

#ifndef INC_FREERTOS_H
	#error "include FreeRTOS.h must appear in source files before include timers.h"
#endif

#include "portable.h"
#include "list.h"

#ifdef __cplusplus
extern "C" {
#endif

/* IDs for commands that can be sent/received on the timer queue.  These are to
be used solely through the macros that make up the public software timer API,
as defined below. */
#define tmrCOMMAND_START					0
#define tmrCOMMAND_STOP						1
#define tmrCOMMAND_CHANGE_PERIOD			2
#define tmrCOMMAND_DELETE					3

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
 * 								portTickType xTimerPeriod, 
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
 * xTimerChangePeriodFromISR() can all be used to transition a timer into the
 * active state.
 *
 * @param pcTimerName A text name that is assigned to the timer.  This is done
 * purely to assist debugging.  The kernel itself only ever references a timer by
 * its handle, and never by its name.
 *
 * @param xTimerPeriod The timer period.  The time is defined in tick periods so 
 * the constant portTICK_RATE_MS can be used to convert a time that has been
 * specified in milliseconds.  For example, if the timer must expire after 100
 * ticks, then xTimerPeriod should be set to 100.  Alternatively, if the timer
 * must expire after 500ms, then xPeriod can be set to ( 500 / portTICK_RATE_MS )
 * provided configTICK_RATE_HZ is set to less than or equal to 1000.
 *
 * @param uxAutoReload If uxAutoReload is set to pdTRUE then the timer will
 * expire repeatedly with a frequency set by the xTimerPeriod parameter.  If
 * uxAutoReload is set to pdFALSE then the timer will be a one-shot timer and
 * will expire once only xTimerPeriod ticks from the time it is started.
 *
 * @param pvTimerID An identifier to assign to the timer being created.  
 * Typically this would be used to identify the timer that expired within the
 * timers callback function when multiple timers are assigned the same callback
 * function.
 *
 * @param pxCallbackFunction The function to call when the timer expires.
 *
 * @return If the timer is successfully create then a handle to the newly
 * created timer is returned.  If the timer cannot be created (because either
 * there is insufficient FreeRTOS heap remaining to allocate the timer 
 * structures, or the timer period was set to 0) then 0 is returned.
 *
 * Example usage:
 *
 * 
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
 * void vTimerCallback( xTIMER *pxTimer )
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
 */
xTimerHandle xTimerCreate( const signed char *pcTimerName, portTickType xTimerPeriod, unsigned portBASE_TYPE uxAutoReload, void * pvTimerID, tmrTIMER_CALLBACK pxCallbackFunction ) PRIVILEGED_FUNCTION;

/**
 * void *pvTimerGetTimerID( xTimerHandle xTimer );
 *
 * Returns the ID assigned to the xTimer parameter.  
 * 
 * IDs are assigned to timers using the pvTimerID parameter of the call to
 * xTimerCreated() used to create the timer.
 *
 * If the same callback function is assigned to multiple tasks then the timer
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
 * A timer will be ormant if:
 *     1) It has been created but not started, or 
 *     2) It is an expired on-shot timer that has not been restarted.
 *
 * Timers can be started using the xTimerStart(), xTimerReset(),
 * xTimerStartFromISR(), xTimerResetFromISR(), xTimerChangePeriod() and
 * xTimerChangePeriodFromISR() API functions.
 *
 * @param xTimer The timer being queried.
 *
 * @return pdFALSE will be returned if the timer is dormant.  A value other than
 * pdFALSE will be returned if the timer is active.
 *
 * Example usage:
 *
 * // This function assumes xTimer has already been created.
 * void vAFunction( xTimerHandle xTimer )
 * {
 *     if( xTimerIsTimerActive( xTimer ) != pdFALSE ) // or more simply and equivalently "if( xTimerIsTimerActive( xTimer )" )
 *     {
 *         // xTimer is active, do something.
 *     }
 *     else
 *     {
 *         // xTimer is not active, do something else.
 *     } 
 * }
 */
portBASE_TYPE xTimerIsTimerActive( xTimerHandle xTimer ) PRIVILEGED_FUNCTION;

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
 * already in the active state, then xTimerStart() has equaivalent functionality
 * to the xTimerReset() API function.
 *
 * Starting a timer ensures the timer is in the active state.  If the timer
 * is not stopped, deleted, or reset in the mean time, the callback function
 * associated with the timer will get called 'n 'ticks after xTimerStart() was 
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
 * be returned if the command was successfully send to the timer command queue.
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
#define xTimerStart( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_START, xTaskGetTickCount(), NULL, xBlockTime )

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
 * be returned if the command was successfully send to the timer command queue.
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
#define xTimerStop( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_STOP, 0, NULL, xBlockTime )

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
 * @param xTimer The handle of the timer being stopped.
 *
 * @param xNewPeriod The new period for xTimer. Timer periods are specified in 
 * tick periods, so the constant portTICK_RATE_MS can be used to convert a time 
 * that has been specified in milliseconds.  For example, if the timer must 
 * expire after 100 ticks, then xNewPeriod should be set to 100.  Alternatively, 
 * if the timer must expire after 500ms, then xNewPeriod can be set to 
 * ( 500 / portTICK_RATE_MS ) provided configTICK_RATE_HZ is set to less than
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
 * pdPASS will be returned if the command was successfully send to the timer 
 * command queue.  When the command is actually processed will depend on the 
 * priority of the timer service/daemon task relative to other tasks in the 
 * system.  The timer service/daemon task priority is set by the 
 * configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 *
 * // This function assumes xTimer has already been created.  If the timer
 * // referenced by xTimer is already active when it is called, then the timer 
 * // is deleted.  If the timer referenced by xTimer is not active when it is
 * // called, then the period of the timer is set to 500ms and the timer is
 * // started.
 * void vAFunction( xTimerHandle xTimer )
 * {
 *     if( xTimerIsTimerActive( xTimer ) != pdFALSE ) // or more simply and equivalently "if( xTimerIsTimerActive( xTimer )" )
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
 *         {
 *     } 
 * }
 */
 #define xTimerChangePeriod( xTimer, xNewPeriod, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_CHANGE_PERIOD, xNewPeriod, NULL, xBlockTime )

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
 * @param xTimer The handle of the timer being stopped.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the delete command to be 
 * successfully sent to the timer command queue, should the queue already be 
 * full when xTimerDelete() was called.  xBlockTime is ignored if xTimerDelete() 
 * is called before the scheduler is started.  
 *
 * @return pdFAIL will be returned if the delete command could not be sent to 
 * the timer command queue even after xBlockTime ticks had passed.  pdPASS will
 * be returned if the command was successfully send to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system.  The timer 
 * service/daemon task priority is set by the configTIMER_TASK_PRIORITY 
 * configuration constant.
 *
 * Example usage:
 * 
 * See the xTimerChangePeriod() API function example usage scenario.
 */
#define xTimerDelete( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_DELETE, 0, NULL, xBlockTime )

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
 * equaivalent functionality to the xTimerStart() API function.
 *
 * Resetting a timer ensures the timer is in the active state.  If the timer
 * is not stopped, deleted, or reset in the mean time, the callback function
 * associated with the timer will get called 'n 'ticks after xTimerReset() was 
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
 * @param xTimer The handle of the timer being started/restarted.
 *
 * @param xBlockTime Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the reset command to be successfully
 * sent to the timer command queue, should the queue already be full when 
 * xTimerReset() was called.  xBlockTime is ignored if xTimerReset() is called
 * before the scheduler is started.  
 *
 * @return pdFAIL will be returned if the reset command could not be sent to 
 * the timer command queue even after xBlockTime ticks had passed.  pdPASS will
 * be returned if the command was successfully send to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system, although the
 * timers expiry time is relative to when xTimerStart() is actually called.  The 
 * timer service/daemon task priority is set by the configTIMER_TASK_PRIORITY 
 * configuration constant.
 *
 * Example usage:
 * 
 * // This scenario assumes xTimer has already been created.  When a key is 
 * // pressed, an LCD backlight is switched on.  If 5 seconds pass without a key 
 * // being pressed, then the LCD backlight is switched off.  In this case, the 
 * // timer is a one-shot timer.
 *
 * xTimerHandle xBacklightTimer = NULL;
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( xTIMER *pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD backlight.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press event handler.
 * void vKeyPressEventHandler( char cKey )
 * {
 *     // Ensure the LCD backlight is on, then reset the timer that is
 *     // responsible for turning the backlight off after 5 seconds of 
 *     // key inactivity.  Wait 10 ticks for the command to be successfully sent
 *     // if it cannot be sent immediately.
 *     vSetBacklightState( BACKLIGHT_ON );
 *     if( vTimerReset( xBacklightTimer, 100 ) != pdPASS )
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
 *     // the backlight off if no keys are pressed within a 5 second period.
 *     xBacklightTimer = xTimerCreate( "BacklightTimer",           // Just a text name, not used by the kernel.
 *                                     ( 5000 / portTICK_RATE_MS), // The timer period in ticks.
 *                                     pdFALSE,                    // The timer is a one-shot timer.
 *                                     0,                          // The id is not used by the callback so can take any value.
 *                                     vBacklightTimerCallback     // The callback function that switches the LCD backlight off.
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
 */
#define xTimerReset( xTimer, xBlockTime ) xTimerGenericCommand( xTimer, tmrCOMMAND_START, xTaskGetTickCount(), NULL, xBlockTime )

/**
 * portBASE_TYPE xTimerStartFromISR( 	xTimerHandle xTimer, 
 *										portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * Description goes here ####
 *
 * @param xTimer
 *
 * @return 
 *
 * Example usage:
 */
#define xTimerStartFromISR( xTimer, pxHigherPriorityTaskWoken ) xTimerGenericCommand( xTimer, tmrCOMMAND_START, xTaskGetTickCountFromISR(), pxHigherPriorityTaskWoken, 0 )

/**
 * portBASE_TYPE xTimerStopFromISR( 	xTimerHandle xTimer, 
 *										portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * Description goes here ####
 *
 * @param xTimer
 *
 * @return 
 *
 * Example usage:
 */
#define xTimerStopFromISR( xTimer, pxHigherPriorityTaskWoken ) xTimerGenericCommand( xTimer, tmrCOMMAND_STOP, 0, pxHigherPriorityTaskWoken, 0 )

/**
 * portBASE_TYPE xTimerChangePeriodFromISR( xTimerHandle xTimer, 
 *											portTickType xNewPeriod,
 *											portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * Description goes here ####
 *
 * @param xTimer
 *
 * @return 
 *
 * Example usage:
 */
#define xTimerChangePeriodFromISR( xTimer, xNewPeriod, pxHigherPriorityTaskWoken ) xTimerGenericCommand( xTimer, tmrCOMMAND_CHANGE_PERIOD, xNewPeriod, pxHigherPriorityTaskWoken, 0 )

/**
 * portBASE_TYPE xTimerResetFromISR( 	xTimerHandle xTimer, 
 *										portBASE_TYPE *pxHigherPriorityTaskWoken );
 *
 * Description goes here ####
 *
 * @param xTimer
 *
 * @return 
 *
 * Example usage:
 */
#define xTimerResetFromISR( xTimer, pxHigherPriorityTaskWoken ) xTimerGenericCommand( xTimer, tmrCOMMAND_START, xTaskGetTickCountFromISR(), pxHigherPriorityTaskWoken, 0 )

/*
 * Functions beyond this part are not part of the public API and are intended
 * for use by the kernel only.
 */
portBASE_TYPE xTimerCreateTimerTask( void ) PRIVILEGED_FUNCTION;
portBASE_TYPE xTimerGenericCommand( xTimerHandle xTimer, portBASE_TYPE xCommandID, portTickType xOptionalValue, portBASE_TYPE *pxHigherPriorityTaskWoken, portTickType xBlockTime ) PRIVILEGED_FUNCTION;

#ifdef __cplusplus
}
#endif
#endif /* TIMERS_H */



