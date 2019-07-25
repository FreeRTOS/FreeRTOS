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
 *  @file       Capture.h
 *
 *  @brief      Capture driver interface
 *
 *  The Capture header file should be included in an application as follows:
 *  @code
 *  #include <ti/drivers/Capture.h>
 *  @endcode
 *
 *  # Operation #
 *  The Capture driver facilitates the capture routines by using general purpose
 *  timers. Capture instances must be opened by calling Capture_open() while
 *  passing in a Capture index and parameters data structure.
 *
 *  When a capture instance is opened, the capture triggering edge and callback
 *  function are configured. The capture is stopped after calling Capture_open()
 *  until Capture_start() is called.
 *
 *  When Capture_open() is called, it tries to occupy the user-specified timer by
 *  calling Timer_open(). If that timer is already allocated for other modules,
 *  NULL is returned. Otherwise, the Capture_Handle is returned.

 *  A capture is triggered based on the user-specified capture mode:
 *      - CAPTURE_MODE_RISING_RISING
 *      - CAPTURE_MODE_RISING_FALLING
 *      - CAPTURE_MODE_ANY_EDGE
 *  The user-specified callback function is called once the input signal matches
 *  the capture mode and the value passed into callback function is the interval
 *  between two triggering edge in the user-specified unit.
 *
 *  ## opening the driver ##
 *
 *  @code
 *  Capture_Handle      handle;
 *  Capture_Params      params;
 *
 *  Capture_Params_init(&params);
 *  params.mode  = CAPTURE_MODE_RISING_FALLING;
 *  params.callbackFxn = someCaptureCallbackFunction;
 *  params.periodUnit = CAPTURE_PERIOD_US;
 *  handle = Capture_open(someCapture_configIndexValue, &params);
 *  if (!handle)
 *  {
 *      System_printf("Capture did not open");
 *  }
 *
 *  ## starting the driver ##

 *  @code
 *  status = Capture_start(handle);
 *  if (status == Capture_STATUS_ERROR)
 *  {
 *      System_printf("Capture cannot start");
 *  }
 *  @endcode
 *
 *  ## stoping the driver ##
 *
 *  @code
 *  Capture_stop(handle);
 *  @endcode
 *
 *  ## closing the driver ##
 *
 *  @code
 *  Capture_close(handle);
 *  @endcode
 *
 *  # Implementation #
 *
 *  This module serves as the main interface for TI-RTOS
 *  applications. Its purpose is to redirect the module's APIs to specific
 *  peripheral implementations which are specified using a pointer to a
 *  Capture_FxnTable.
 *
 *  The Capture driver interface module is joined (at link time) to a
 *  NULL-terminated array of Capture_Config data structures named *Capture_Config*.
 *  *Capture_Config* is implemented in the application with each entry being an
 *  instance of a Capture module. Each entry in *Capture_Config* contains a:
 *  - (Capture_FxnTable *) to a set of functions that implement a Capture module
 *  - (void *) data object that is associated with the Capture_FxnTable
 *  - (void *) hardware attributes that are associated to the Capture_FxnTable
 *
 *  # Instrumentation #
 *  The Capture driver interface produces log statements if instrumentation is
 *  enabled.
 *
 *  Diagnostics Mask | Log details |
 *  ---------------- | ----------- |
 *  Diags_USER1      | basic operations performed |
 *  Diags_USER2      | detailed operations performed |
 *
 *  ============================================================================
 */
#ifndef ti_drivers_Capture__include
#define ti_drivers_Capture__include

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdint.h>
#include <stdbool.h>

/*!
 *  @brief      A handle that is returned from a Capture_open() call.
 */
typedef struct Capture_Config_ *Capture_Handle;

/*!
 * Common Capture_control command code reservation offset.
 * Capture driver implementations should offset command codes with CAPTURE_CMD_RESERVED
 * growing positively
 *
 * Example implementation specific command codes:
 * @code
 * #define CAPTUREXYZ_CMD_COMMAND0      CAPTURE_CMD_RESERVED + 0
 * #define CAPTUREXYZ_CMD_COMMAND1      CAPTURE_CMD_RESERVED + 1
 * @endcode
 */
#define CAPTURE_CMD_RESERVED             (32)

/*!
 * Common Capture_control status code reservation offset.
 * Capture driver implementations should offset status codes with
 * CAPTURE_STATUS_RESERVED growing negatively.
 *
 * Example implementation specific status codes:
 * @code
 * #define CAPTUREXYZ_STATUS_ERROR0     CAPTURE_STATUS_RESERVED - 0
 * #define CAPTUREXYZ_STATUS_ERROR1     CAPTURE_STATUS_RESERVED - 1
 * #define CAPTUREXYZ_STATUS_ERROR2     CAPTURE_STATUS_RESERVED - 2
 * @endcode
 */
#define CAPTURE_STATUS_RESERVED         (-32)

/*!
 * @brief   Successful status code returned by Capture_control().
 *
 * Capture_control() returns TIMER_STATUS_SUCCESS if the control code was executed
 * successfully.
 */
#define CAPTURE_STATUS_SUCCESS          (0)

/*!
 * @brief   Generic error status code returned by Capture_control().
 *
 * Capture_control() returns CAPTURE_STATUS_ERROR if the control code was not executed
 * successfully.
 */
#define CAPTURE_STATUS_ERROR            (-1)

/*!
 * @brief   An error status code returned by Capture_control() for undefined
 * command codes.
 *
 * Capture_control() returns TIMER_STATUS_UNDEFINEDCMD if the control code is not
 * recognized by the driver implementation.
 */
#define CAPTURE_STATUS_UNDEFINEDCMD    (-2)

/*!
 *  @brief Capture period unit enum
 *
 *  The Capture period unit needs to be passed in Capture_open() to
 *  specify the unit of two capture triggering interval.
 *
 */
typedef enum Capture_Period_Unit_ {
    CAPTURE_PERIOD_US,      /* Period in microseconds */
    CAPTURE_PERIOD_HZ,      /* Period in frequency */
    CAPTURE_PERIOD_COUNTS,  /* Period in counts */
} Capture_Period_Unit;

/*!
 *  @brief Capture mode enum
 *
 *  The Capture mode needs to be passed in Capture_open() to specify the capture
 *  triggering mode.
 *
 */
typedef enum Capture_Mode_ {
    CAPTURE_MODE_RISING_RISING, /*!< capture is triggered at the rising edge followed by the rising edge */
    CAPTURE_MODE_FALLING_FALLING, /*!< capture is triggered at the falling edge followed by the falling edge */
    CAPTURE_MODE_ANY_EDGE
    /*!< capture is triggered at the falling edge followed by the rising edge */
} Capture_Mode;

/*!
 *  @brief  Capture callback function
 *
 *  User definable callback function prototype. The Capture driver will call the
 *  defined function and pass in the Capture driver's handle and the pointer to the
 *  user-specified the argument.
 *
 *  @param  handle         Capture_Handle
 *
 *  @param  interval       Interval of two triggering edge in Capture_Period_Unit
 *
 */
typedef void (*Capture_CallBackFxn)(Capture_Handle handle, uint32_t interval);

/*!
 *  @brief Capture Parameters
 *
 *  Capture parameters are used to with the Capture_open() call. Default values for
 *  these parameters are set using Capture_Params_init().
 *
 */
typedef struct Capture_Params_ {
    Capture_Mode mode; /*!< Capture triggering mode */
    Capture_CallBackFxn callbackFxn; /*!< Callback function pointer */
    Capture_Period_Unit periodUnit; /*!< Period unit */
} Capture_Params;

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Capture_close().
 */
typedef void (*Capture_CloseFxn)(Capture_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Capture_control().
 */
typedef int_fast16_t (*Capture_ControlFxn)(Capture_Handle handle,
        uint_fast16_t cmd, void *arg);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Capture_init().
 */
typedef void (*Capture_InitFxn)(Capture_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Capture_open().
 */
typedef Capture_Handle (*Capture_OpenFxn)(Capture_Handle handle,
        Capture_Params *params);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Capture_start().
 */
typedef void (*Capture_StartFxn)(Capture_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              Capture_stop().
 */
typedef void (*Capture_StopFxn)(Capture_Handle handle);

/*!
 *  @brief      The definition of a Capture function table that contains the
 *              required set of functions to control a specific Capture driver
 *              implementation.
 */
typedef struct Capture_FxnTable_ {
    /*! Function to close the specified peripheral */
    Capture_CloseFxn closeFxn;

    /*! Function to send control commands to the specified peripheral */
    Capture_ControlFxn controlFxn;

    /*! Function to initialize the specified peripheral */
    Capture_InitFxn initFxn;

    /*! Function to open the specified peripheral */
    Capture_OpenFxn openFxn;

    /*! Function to start the specified peripheral */
    Capture_StartFxn startFxn;

    /*! Function to stop the specified peripheral */
    Capture_StopFxn stopFxn;

} Capture_FxnTable;

typedef struct Capture_Config_ {
    Capture_FxnTable const *fxnTablePtr;
    void *object;
    void const *hwAttrs;
} Capture_Config;

/*!
 *  @brief  Function to close a Capture module specified by the Capture handle
 *
 *  The function takes care of timer resource allocation. The corresponding timer
 *  resource to the Capture_Handle is released to be an available timer resource.
 *
 *  @pre    Capture_open() had to be called first.
 *
 *  @param  handle  A Capture_Handle returned from Capture_open
 *
 *  @sa     Capture_open()
 */
extern void Capture_close(Capture_Handle handle);

/*!
 *  @brief  Function performs implementation specific features on a given
 *          Capture_Handle.
 *
 *  @pre    Capture_open() must have been called first.
 *
 *  @param  handle      A Capture_Handle returned from Capture_open().
 *
 *  @param  cmd         A command value defined by the driver specific
 *                      implementation.
 *
 *  @param  arg         A pointer to an optional R/W (read/write) argument that
 *                      is accompanied with cmd.
 *
 *  @return A Capture_Status describing an error or success state. Negative values
 *          indicate an error occurred.
 *
 *  @sa     Capture_open()
 */
extern int_fast16_t Capture_control(Capture_Handle handle, uint_fast16_t cmd,
    void *arg);

/*!
 *  @brief  Function to initialize Capture.
 */
extern void Capture_init(void);

/*!
 *  @brief  Function to initialize a given Capture module specified by the
 *          particular index value. The parameter specifies which mode the Capture
 *          will operate.
 *
 *  The function takes care of timer resource allocation. If the particular timer
 *  passed by user has already been used by other modules, the return value is NULL.
 *  If the particular timer is available to use, Capture module owns it and returns
 *  a Capture_Handle.
 *
 *  @param  index         Logical instance number for the Capture indexed into
 *                        the Capture_config table
 *
 *  @param  params        Pointer to an parameter block, if NULL it will use
 *                        default values. All the fields in this structure are
 *                        RO (read-only).
 *
 *  @return A Capture_Handle on success or a NULL on an error if it has been
 *          opened already or used by other modules.
 *
 *  @sa     Capture_init()
 *  @sa     Capture_close()
 */
extern Capture_Handle Capture_open(uint_least8_t index, Capture_Params *params);

/*!
 *  @brief  Function to initialize the Capture_Params struct to its defaults
 *
 *  @param  params      An pointer to Capture_Params structure for
 *                      initialization
 *
 *  Defaults values are:
 *      mode = CAPTURE_MODE_RISING_RISING
 *      callbackFxn = user_specified_callbackFxn
 *      periodUnit = Capture_PERIOD_COUNTS
 */
extern void Capture_Params_init(Capture_Params *params);

/*!
 *  @brief  Function to start capture. The Capture running mode
 *          and interval period unit are specfied in the Capture_Params when calling
 *          Capture_open().
 *
 *  @param  handle        Capture_Handle
 *
 *  @return CAPTURE_STATUS_SUCCESS if Capture starts successfully.
 *          CAPTURE_STATUS_ERROR if Capture fails to start.
 *
 */
extern void Capture_start(Capture_Handle handle);

/*!
 *  @brief  Function to stop Capture after Capture_start() is called with success.
 *
 *  @param  handle        Capture_Handle
 *
 */
extern void Capture_stop(Capture_Handle handle);

#ifdef __cplusplus
}
#endif

#endif /* ti_drivers_Capture__include */
