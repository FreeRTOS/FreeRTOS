/*
 * Copyright (c) 2016, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/** ============================================================================
 *  @file       ClockP.h
 *
 *  @brief      Clock interface for the RTOS Porting Interface
 *
 *  The ClockP module can be used to schedule functions that run at intervals
 *  specified in the underlying kernel's system ticks.  ClockP instances are
 *  one-shot.  The one-shot function will be run once
 *  after the specified period has elapsed since calling ClockP_start().
 *
 *  The ClockP module can also be used to obtain the period of the kernel's
 *  system tick in microseconds.  This is useful for determining the number of
 *  ticks needed for setting a Clock object's period.
 *
 *  When using the TI-RTOS kernel, ClockP functions are run at software
 *  interrupt level. With FreeRTOS, the ClockP functions are run by a timer
 *  service task with priority configured by the application.
 *
 *  A common use case is to post a semaphore in the clock function. There is a
 *  specific API for this: Semaphore_postFromClock(). This must be used in a
 *  clock function (instead of Semaphore_post).
 *
 *  ============================================================================
 */

#ifndef ti_dpl_ClockP__include
    #define ti_dpl_ClockP__include

    #ifdef __cplusplus
    extern "C" {
    #endif

    #include <stdint.h>
    #include <stdbool.h>
    #include <stddef.h>

/*!
 *  @brief  Frequency-in-hertz struct
 */
    typedef struct ClockP_FreqHz
    {
        uint32_t hi;  /*! most significant 32-bits of frequency */
        uint32_t lo;  /*! least significant 32-bits of frequency */
    } ClockP_FreqHz;

/*!
 *  @brief    Status codes for ClockP APIs
 */
    typedef enum ClockP_Status
    {
        ClockP_OK = 0,
        ClockP_FAILURE = -1
    } ClockP_Status;

/*!
 *  @brief    Opaque client reference to an instance of a ClockP
 *
 *  A ClockP_Handle returned from the ::ClockP_create represents that instance.
 *  and then is used in the other instance based functions (e.g. ::ClockP_start,
 *  ::ClockP_stop, etc.).
 */
    typedef  void * ClockP_Handle;

/*!
 *  @brief  Prototype for a ClockP function.
 */
    typedef void (* ClockP_Fxn)( uintptr_t arg );

/*!
 *  @brief    Basic ClockP Parameters
 *
 *  Structure that contains the parameters passed into ::ClockP_create
 *  when creating a ClockP instance. The ::ClockP_Params_init function should
 *  be used to initialize the fields to default values before the application sets
 *  the fields manually. The ClockP default parameters are noted in
 *  ClockP_Params_init.
 */
    typedef struct ClockP_Params
    {
        char * name;    /*!< Name of the clock instance. Memory must
                         *   persist for the life of the clock instance.
                         *   This can be used for debugging purposes, or
                         *   set to NULL if not needed. */
        uintptr_t arg;  /*!< Argument passed into the clock function. */
    } ClockP_Params;

/*!
 *  @brief  Function to create a clock object.
 *
 *  @param  clockFxn  Function called when timeout or period expires.
 *
 *  @param  params    Pointer to the instance configuration parameters. NULL
 *                    denotes to use the default parameters. The ClockP default
 *                    parameters are noted in ::ClockP_Params_init.
 *
 *  @return A ClockP_Handle on success or a NULL on an error.  This handle can
 *          be passed to ClockP_start()
 */
    extern ClockP_Handle ClockP_create( ClockP_Fxn clockFxn,
                                        ClockP_Params * params );

/*!
 *  @brief  Function to delete a clock.
 *
 *  @param  handle  A ClockP_Handle returned from ::ClockP_create
 *
 *  @return Status of the function.
 *    - ClockP_OK: Deleted the clock instance
 *    - ClockP_FAILURE: Timed out waiting to delete the clock object.
 */
    extern ClockP_Status ClockP_delete( ClockP_Handle handle );

/*!
 *  @brief  Get CPU frequency in Hz
 *
 *  @param  freq  Pointer to the FreqHz structure
 */
    extern void ClockP_getCpuFreq( ClockP_FreqHz * freq );

/*!
 *  @brief  Get the system tick period in microseconds.
 *
 *  @return The kernel's system tick period in microseconds.
 */
    extern uint32_t ClockP_getSystemTickPeriod();

/*!
 *  @brief  Get the current tick value
 *
 *  The value returned will wrap back to zero after it reaches the max
 *  value that can be stored in 32 bits.
 *
 *  @return Time in system clock ticks
 */
    extern uint32_t ClockP_getSystemTicks();

/*!
 *  @brief  Initialize params structure to default values.
 *
 *  The default parameters are:
 *   - name: NULL
 *   - arg: 0
 *
 *  @param params  Pointer to the instance configuration parameters.
 */
    extern void ClockP_Params_init( ClockP_Params * params );

/*!
 *  @brief  Function to start a clock.
 *
 *  @param  handle  A ClockP_Handle returned from ::ClockP_create
 *
 *  @param  timeout   The timeout used for a one-shot clock object.  The
 *                    value of timeout must not be 0.
 *
 *  @return Status of the functions
 *    - ClockP_OK: Scheduled the clock function successfully
 *    - ClockP_FAILURE: The API failed.
 */
    extern ClockP_Status ClockP_start( ClockP_Handle handle,
                                       uint32_t timeout );

/*!
 *  @brief  Function to start a clock from an interrupt.
 *
 *  @param  handle  A ClockP_Handle returned from ::ClockP_create
 *
 *  @param  timeout   The timeout used for a one-shot clock object.  The
 *                    value of timeout must not be 0.
 *
 *  @return Status of the functions
 *    - ClockP_OK: Scheduled the clock function successfully
 *    - ClockP_FAILURE: The API failed.
 */
    extern ClockP_Status ClockP_startFromISR( ClockP_Handle handle,
                                              uint32_t timeout );

/*!
 *  @brief  Function to stop a clock.
 *
 *  @param  handle  A ClockP_Handle returned from ::ClockP_create
 *
 *  It is ok to call ClockP_stop() for a clock that has not been started.
 *
 *  @return Status of the functions
 *    - ClockP_OK: Stopped the clock function successfully
 *    - ClockP_FAILURE: The API failed.
 */
    extern ClockP_Status ClockP_stop( ClockP_Handle handle );

/*!
 *  @brief  Function to stop a clock from an interrupt.
 *
 *  @param  handle  A ClockP_Handle returned from ::ClockP_create
 *
 *  @return Status of the functions
 *    - ClockP_OK: Stopped the clock function successfully
 *    - ClockP_FAILURE: The API failed.
 */
    extern ClockP_Status ClockP_stopFromISR( ClockP_Handle handle );

    extern ClockP_Status ClockP_timestamp( ClockP_Handle handle );

/*!
 *  @brief  Set delay in microseconds
 *
 *  @param  usec  A duration in micro seconds
 *
 *  @return ClockP_OK
 */
    extern ClockP_Status ClockP_usleep( uint32_t usec );

/*!
 *  @brief  Set delay in seconds
 *
 *  @param  sec  A duration in seconds
 *
 *  @return ClockP_OK
 */
    extern ClockP_Status ClockP_sleep( uint32_t sec );

    #ifdef __cplusplus
}
    #endif

#endif /* ti_dpl_ClockP__include */
