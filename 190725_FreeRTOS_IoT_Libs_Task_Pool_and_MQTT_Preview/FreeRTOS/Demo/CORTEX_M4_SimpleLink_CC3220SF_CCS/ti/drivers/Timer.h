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
 *  @file       Timer.h
 *
 *  @brief      Timer driver interface
 *
 *  The Timer header file should be included in an application as follows:
 *  @code
 *  #include <ti/drivers/Timer.h>
 *  @endcode
 *
 *  # Operation #
 *  The Timer driver operates as a generic timer interface for timing interval
 *  handling. It can be configured to run in one-shot blocking mode,
 *  one-shot callback mode, continuous callback mode, or free-run mode. This
 *  driver does not have PWM or capture functionalities. These functionalities
 *  are addressed in both the Capture and PWM driver modules.
 *
 *  The Timer driver also handles the general purpose timer resource allocation.
 *  For the driver that requires to use the general purpose timer, it calls
 *  Timer_open() to occupy the specified timer, and calls Timer_close() to release
 *  the occupied timer resource.
 *
 *  ## Opening the Driver ##
 *
 *  @code
 *  Timer_Handle      handle;
 *  Timer_Params      params;
 *
 *  Timer_Params_init(&params);
 *  params.mode  = TIMER_MODE_CONTINUOUS_CALLBACK;
 *  params.callbackFxn = someTimerCallbackFunction;
 *  params.periodUnit = TIMER_PERIOD_US;
 *  params.period = 5000000
 *  handle = Timer_open(someTimer_configIndexValue, &params);
 *  if (!handle)
 *  {
 *      System_printf("Timer did not open");
 *  }
 *
 *  ## Starting the Driver ##

 *  @code
 *  status = Timer_start(handle);
 *  if (status == TIMER_STATUS_ERROR)
 *  {
 *      System_printf("Timer cannot start at specified period");
 *  }
 *  @endcode
 *
 *  ## Stopping the driver ##
 *
 *  @code
 *  Timer_stop(handle);
 *  @endcode
 *
 *  ## closing the driver ##
 *
 *  @code
 *  Timer_close(handle);
 *  @endcode
 *
 *  # Implementation #
 *
 *  This module serves as the main interface for TI Drivers
 *  applications. Its purpose is to redirect the module's APIs to specific
 *  peripheral implementations which are specified using a pointer to a
 *  Timer_FxnTable.
 *
 *  The Timer driver interface module is joined (at link time) to a
 *  NULL-terminated array of Timer_Config data structures named *Timer_config*.
 *  *Timer_config* is implemented in the application with each entry being an
 *  instance of a Timer peripheral. Each entry in *Timer_config* contains a:
 *  - (Timer_FxnTable *) to a set of functions that implement a Timer peripheral
 *  - (void *) data object that is associated with the Timer_FxnTable
 *  - (void *) hardware attributes that are associated to the Timer_FxnTable
 *
 *  # Instrumentation #
 *  The Timer driver interface produces log statements if instrumentation is
 *  enabled.
 *
 *  ============================================================================
 */
#ifndef ti_drivers_Timer__include
#define ti_drivers_Timer__include

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

/*!
 *  @brief      A handle that is returned from a Timer_open() call.
 */
typedef struct Timer_Config_ *Timer_Handle;

/*!
 * Common Timer_control command code reservation offset.
 * Timer driver implementations should offset command codes with TIMER_CMD_RESERVED
 * growing positively
 *
 * Example implementation specific command codes:
 * @code
 * #define TIMERXYZ_CMD_COMMAND0      TIMER_CMD_RESERVED + 0
 * #define TIMERXYZ_CMD_COMMAND1      TIMER_CMD_RESERVED + 1
 * @endcode
 */
#define TIMER_CMD_RESERVED                (32)

/*!
 * Common Timer_control status code reservation offset.
 * Timer driver implementations should offset status codes with
 * TIMER_STATUS_RESERVED growing negatively.
 *
 * Example implementation specific status codes:
 * @code
 * #define TIMERXYZ_STATUS_ERROR0     TIMER_STATUS_RESERVED - 0
 * #define TIMERXYZ_STATUS_ERROR1     TIMER_STATUS_RESERVED - 1
 * #define TIMERXYZ_STATUS_ERROR2     TIMER_STATUS_RESERVED - 2
 * @endcode
 */
#define TIMER_STATUS_RESERVED            (-32)

/*!
 * @brief   Successful status code returned by Timer_control().
 *
 * Timer_control() returns TIMER_STATUS_SUCCESS if the control code was executed
 * successfully.
 */
#define TIMER_STATUS_SUCCESS               (0)

/*!
 * @brief   Generic error status code returned by Timer_control().
 *
 * Timer_control() returns TIMER_STATUS_ERROR if the control code was not executed
 * successfully.
 */
#define TIMER_STATUS_ERROR                (-1)

/*!
 * @brief   An error status code returned by Timer_control() for undefined
 * command codes.
 *
 * Timer_control() returns TIMER_STATUS_UNDEFINEDCMD if the control code is not
 * recognized by the driver implementation.
 */
#define TIMER_STATUS_UNDEFINEDCMD         (-2)

/*!
 *  @brief Timer mode enum
 *
 *  The Timer mode needs to be passed in Timer_open() to specify the timer running
 *  mode which handles the interrupt differently.
 *
 */
typedef enum Timer_Mode_
{
    TIMER_ONESHOT_CB, /*!< User routine doesn't get blocked and user-specified
     callback function is invoked once the timer interrupt happens for only one time */
    TIMER_ONESHOT_BLOCK, /*!< User routine gets blocked until timer interrupt
     happens for only one time */
    TIMER_CONTINUOUS_CB, /*!< User routine doesn't get blocked and user-specified
     callback function is invoked every time the timer interrupt happens */
    TIMER_MODE_FREE_RUNNING
} Timer_Mode;

/*!
 *  @brief Timer period unit enum
 *
 *  The Timer period unit needs to be passed in Timer_open() to
 *  specify the unit of timing interval.
 *
 */
typedef enum Timer_Period_Units_
{
    TIMER_PERIOD_US, /* Period in microseconds */
    TIMER_PERIOD_HZ, /* Period in frequency */
    TIMER_PERIOD_COUNTS /* Period in counts */
} Timer_Period_Units;

/*!
 *  @brief  Timer callback function
 *
 *  User definable callback function prototype. The Timer driver will call the
 *  defined function and pass in the Timer driver's handle and the pointer to the
 *  user-specified the argument.
 *
 *  @param  handle         Timer_Handle
 */
typedef void (*Timer_CallBackFxn)(Timer_Handle handle);

/*!
 *  @brief Timer Parameters
 *
 *  Timer parameters are used to with the Timer_open() call. Default values for
 *  these parameters are set using Timer_Params_init().
 *
 */
typedef struct Timer_Params_
{
    Timer_Mode timerMode;
    Timer_Period_Units periodUnits;
    Timer_CallBackFxn timerCallback;
    uint32_t period;
} Timer_Params;

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_control().
 */
typedef int_fast16_t (*Timer_ControlFxn)(Timer_Handle handle, uint_fast16_t cmd,
        void *arg);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_close().
 */
typedef void (*Timer_CloseFxn)(Timer_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_getCount().
 */
typedef uint32_t (*Timer_GetCountFxn)(Timer_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_init().
 */
typedef void (*Timer_InitFxn)(Timer_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_open().
 */
typedef Timer_Handle (*Timer_OpenFxn)(Timer_Handle handle,
        Timer_Params *params);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_start().
 */
typedef void (*Timer_StartFxn)(Timer_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Timer_stop().
 */
typedef void (*Timer_StopFxn)(Timer_Handle handle);

/*!
 *  @brief      The definition of a Timer function table that contains the
 *              required set of functions to control a specific Timer driver
 *              implementation.
 */
typedef struct Timer_FxnTable_
{
    /*! Function to close the specified instance */
    Timer_CloseFxn closeFxn;
    /*! Function to send contorl commands to the counter for a specific instance */
    Timer_ControlFxn controlFxn;
    /*! Function to get the count of the timer for a specific instance */
    Timer_GetCountFxn getCountFxn;
    /*! Function to open the specified instance */
    Timer_InitFxn initFxn;
    /*! Function to open the specified instance */
    Timer_OpenFxn openFxn;
    /*! Function to start the timer for a specific instance */
    Timer_StartFxn startFxn;
    /*! Function to stop the timer for a specific instance */
    Timer_StopFxn stopFxn;
} Timer_FxnTable;

typedef struct Timer_Config_
{
    Timer_FxnTable const *fxnTablePtr;
    void *object;
    void const *hwAttrs;
} Timer_Config;

/*!
 *  @brief  Function performs implementation specific features on a given
 *          Timer_Handle.
 *
 *  @pre    Timer_open() must have been called first.
 *
 *  @param  handle      A Timer_Handle returned from Timer_open().
 *
 *  @param  cmd         A command value defined by the driver specific
 *                      implementation.
 *
 *  @param  arg         A pointer to an optional R/W (read/write) argument that
 *                      is accompanied with cmd.
 *
 *  @return A Timer_Status describing an error or success state. Negative values
 *          indicate an error occurred.
 *
 *  @sa     Timer_open()
 */
extern int_fast16_t Timer_control(Timer_Handle handle, uint_fast16_t cmd,
                                  void *arg);


/*!
 *  @brief  Function to close a Timer peripheral specified by the Timer handle
 *
 *  The function takes care of timer resource allocation. The corresponding timer
 *  resource to the Timer_Handle is released to be an available timer resource.
 *
 *  @pre    Timer_open() had to be called first.
 *
 *  @param  handle  A Timer_Handle returned from Timer_open
 *
 *  @sa     Timer_open()
 */
extern void Timer_close(Timer_Handle handle);

/*!
 *  @brief  Function to get the current count of a started timer
 *
 *  @pre    Timer_open() had to be called first.
 *
 *  @param  handle  A Timer_Handle returned from Timer_open
 *
 *  @sa     Timer_open()
 *
 *  @return The current count of the specified Timer
 *
 */
extern uint32_t Timer_getCount(Timer_Handle handle);


/*!
 *  @brief  Function to initialize a timer module. This function will go through
 *  all available hardware resources and mark them as "available"
 *
 *  @sa     Timer_open()
 */
extern void Timer_init(void);

/*!
 *  @brief  Function to initialize a given Timer peripheral specified by the
 *          particular index value. The parameter specifies which mode the Timer
 *          will operate.
 *
 *  The function takes care of timer resource allocation. If the particular timer
 *  passed by user has already been used by other modules, the return value is NULL.
 *  If the particular timer is available to use, Timer module owns it and returns
 *  a Timer_Handle.
 *
 *  @param  index         Logical peripheral number for the Timer indexed into
 *                        the Timer_config table
 *
 *  @param  params        Pointer to an parameter block, if NULL it will use
 *                        default values. All the fields in this structure are
 *                        RO (read-only).
 *
 *  @return A Timer_Handle on success or a NULL on an error if it has been
 *          opened already or used by other modules.
 *
 *  @sa     Timer_init()
 *  @sa     Timer_close()
 */
extern Timer_Handle Timer_open(uint_least8_t index, Timer_Params *params);

/*!
 *  @brief  Function to initialize the Timer_Params struct to its defaults
 *
 *  @param  params      An pointer to Timer_Params structure for
 *                      initialization
 *
 *  Defaults values are:
 *      mode = TIMER_MODE_ONESHOT_BLOCKING
 *      callbackFxn = NULL
 *      periodUnit = TIMER_PERIOD_US
 *      period = 0xFFFF
 */
extern void Timer_Params_init(Timer_Params *params);

/*!
 *  @brief  Function to start Timer with the given period. The timer running mode
 *          and interval period unit are specified in the Timer_Params when calling
 *          Timer_open().
 *
 *  @param  handle        Timer_Handle
 *
 *  @return TIMER_STATUS_SUCCESS if timer starts successfully.
 *          TIMER_STATUS_ERROR if timer fails to start.
 *
 */
extern void Timer_start(Timer_Handle handle);

/*!
 *  @brief  Function to stop timer after Timer_start() is called with success.
 *
 *  @param  handle        Timer_Handle
 *
 */
extern void Timer_stop(Timer_Handle handle);

#ifdef __cplusplus
}
#endif

#endif /* ti_driver_Timer__include */
