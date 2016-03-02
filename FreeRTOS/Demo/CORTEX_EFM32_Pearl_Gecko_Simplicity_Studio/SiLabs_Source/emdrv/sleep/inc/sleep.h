/***************************************************************************//**
 * @file sleep.h
 * @brief Energy Modes management driver
 * @version 4.2.1
 * @details
 * This is a energy modes management module consisting of sleep.c and sleep.h
 * source files. The main purpose of the module is to ease energy
 * optimization with a simple API. The module allows the system to always sleep
 * in the lowest possible energy mode. Users could set up callbacks that are
 * being called before and after each and every sleep. A counting semaphore is
 * available for each low energy mode (EM1/EM2/EM3) to protect certain system
 * states from being corrupted. This semaphore has limit set to maximum 255 locks.
 *
 * The module provides the following public API to the users:
 * SLEEP_Init()
 * SLEEP_Sleep()
 * SLEEP_SleepBlockBegin()
 * SLEEP_SleepBlockEnd()
 * SLEEP_ForceSleepInEM4()
 *
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/

#ifndef __SLEEP_H
#define __SLEEP_H

#include <stdint.h>
#include <stdbool.h>

/* Device specific header file(s). */
#include "em_device.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Drivers
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup SLEEP
 * @brief Energy Modes management driver.
 * @details
 * This is a energy modes management module consisting of sleep.c and sleep.h
 * source files. The main purpose of the module is to ease energy
 * optimization with a simple API. The module allows the system to always sleep
 * in the lowest possible energy mode. Users could set up callbacks that are
 * being called before and after each and every sleep. A counting semaphore is
 * available for each low energy mode (EM1/EM2/EM3) to protect certain system
 * states from being corrupted. This semaphore has limit set to maximum 255 locks.
 * @{
 ******************************************************************************/

/*******************************************************************************
 *******************************   MACROS   ************************************
 ******************************************************************************/


/*******************************************************************************
 ****************************   CONFIGURATION   ********************************
 ******************************************************************************/

/** Enable/disable the HW block for protecting accidental setting of low energy
 *  modes (recommended to be set to true). */
#ifndef SLEEP_HW_LOW_ENERGY_BLOCK_ENABLED
#define SLEEP_HW_LOW_ENERGY_BLOCK_ENABLED    true
#endif

/** Enable/disable calling wakeup callback after EM4 reset. */
#ifndef SLEEP_EM4_WAKEUP_CALLBACK_ENABLED
#define SLEEP_EM4_WAKEUP_CALLBACK_ENABLED    true
#endif

/** Configure default lowest energy mode that the system can be set to.
 *  Possible values:
 *  @li sleepEM1 - EM1, the CPU core is turned off.
 *  @li sleepEM2 - EM2, like EM1 + all HF clocks are turned off, LF clocks are on.
 *  @li sleepEM3 - EM3, like EM2 + LF clocks are off, RAM retention, GPIO and ACMP
 *                   interrupt is on. */
#ifndef SLEEP_LOWEST_ENERGY_MODE_DEFAULT
#define SLEEP_LOWEST_ENERGY_MODE_DEFAULT    sleepEM3
#endif

/*******************************************************************************
 ******************************   TYPEDEFS   ***********************************
 ******************************************************************************/

/** Status value used for showing the Energy Mode the device is currently in. */
typedef enum
{
  /** Status value for EM0. */
  sleepEM0 = 0,

  /** Status value for EM1. */
  sleepEM1 = 1,

  /** Status value for EM2. */
  sleepEM2 = 2,

  /** Status value for EM3. */
  sleepEM3 = 3,

  /** Status value for EM4. */
  sleepEM4 = 4
} SLEEP_EnergyMode_t;

/** Callback function pointer type. */
typedef void (*SLEEP_CbFuncPtr_t)(SLEEP_EnergyMode_t);


/*******************************************************************************
 ******************************   PROTOTYPES   *********************************
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Initialize the Sleep module.
 *
 * @details
 *   Use this function to initialize the Sleep module, should be called
 *   only once! Pointers to sleep and wake-up callback functions shall be
 *   provided when calling this function.
 *   If SLEEP_EM4_WAKEUP_CALLBACK_ENABLED is set to true, this function checks
 *   for the cause of the reset that implicitly called it and calls the wakeup
 *   callback if the reset was a wakeup from EM4 (does not work on Gecko MCU).
 *
 * @param[in] pSleepCb
 *   Pointer to the callback function that is being called before the device is
 *   going to sleep.
 *
 * @param[in] pWakeUpCb
 *   Pointer to the callback function that is being called after wake up.
 ******************************************************************************/
void SLEEP_Init(SLEEP_CbFuncPtr_t pSleepCb, SLEEP_CbFuncPtr_t pWakeUpCb);

/***************************************************************************//**
 * @brief
 *   Gets the lowest energy mode that the system is allowed to be set to.
 *
 * @details
 *   This function uses the low energy mode block counters to determine the
 *   lowest possible that the system is allowed to be set to.
 *
 * @return
 *   Lowest energy mode that the system can be set to. Possible values:
 *   @li sleepEM0
 *   @li sleepEM1
 *   @li sleepEM2
 *   @li sleepEM3
 ******************************************************************************/
SLEEP_EnergyMode_t SLEEP_LowestEnergyModeGet(void);

/***************************************************************************//**
 * @brief
 *   Sets the system to sleep into the lowest possible energy mode.
 *
 * @details
 *   This function takes care of the system states protected by the sleep block
 *   provided by SLEEP_SleepBlockBegin() / SLEEP_SleepBlockEnd(). It allows
 *   the system to go into the lowest possible energy mode that the device can
 *   be set into at the time of the call of this function.
 *   This function will not go lower than EM3 because leaving EM4 requires
 *   resetting MCU. To enter into EM4 call SLEEP_ForceSleepInEM4().
 *
 * @return
 *   Energy Mode that was entered. Possible values:
 *   @li sleepEM0
 *   @li sleepEM1
 *   @li sleepEM2
 *   @li sleepEM3
 ******************************************************************************/
SLEEP_EnergyMode_t SLEEP_Sleep(void);


/***************************************************************************//**
 * @brief
 *   Force the device to go to EM4 without doing any checks.
 *
 * @details
 *   This function unblocks the low energy sleep block then goes to EM4.
 *
 * @note
 *   Regular RAM is not retained in EM4 and the wake up causes a reset.
 *   If the configuration option SLEEP_EM4_WAKEUP_CALLBACK_ENABLED is set to
 *   true, the SLEEP_Init() function checks for the reset cause and calls the
 *   EM4 wakeup callback.
 ******************************************************************************/
void SLEEP_ForceSleepInEM4(void);


/***************************************************************************//**
 * @brief
 *   Begin sleep block in the requested energy mode.
 *
 * @details
 *   Blocking a critical system state from a certain energy mode makes sure that
 *   the system is not set to that energy mode while the block is not being
 *   released.
 *   Every SLEEP_SleepBlockBegin() increases the corresponding counter and
 *   every SLEEP_SleepBlockEnd() decreases it.
 *
 *   Example:\code
 *      SLEEP_SleepBlockBegin(sleepEM2);  // do not allow EM2 or higher
 *      // do some stuff that requires EM1 at least, like ADC sampling
 *      SLEEP_SleepBlockEnd(sleepEM2);    // remove restriction for EM2\endcode
 *
 * @note
 *   Be aware that there is limit of maximum blocks nesting to 255.
 *
 * @param[in] eMode
 *   Energy mode to begin to block. Possible values:
 *   @li sleepEM1 - Begin to block the system from being set to EM1 (and EM2..4).
 *   @li sleepEM2 - Begin to block the system from being set to EM2 (and EM3/EM4).
 *   @li sleepEM3 - Begin to block the system from being set to EM3 (and EM4).
 ******************************************************************************/
void SLEEP_SleepBlockBegin(SLEEP_EnergyMode_t eMode);


/***************************************************************************//**
 * @brief
 *   End sleep block in the requested energy mode.
 *
 * @details
 *   Release restriction for entering certain energy mode. Every call of this
 *   function reduce blocking counter by 1. Once the counter for specific energy
 *   mode is 0 and all counters for lower energy modes are 0 as well, using
 *   particular energy mode is allowed.
 *   Every SLEEP_SleepBlockBegin() increases the corresponding counter and
 *   every SLEEP_SleepBlockEnd() decreases it.
 *
 *   Example:\code
 *      // at start all energy modes are allowed
 *      SLEEP_SleepBlockBegin(sleepEM2); // EM2, EM3, EM4 are blocked
 *      SLEEP_SleepBlockBegin(sleepEM1); // EM1, EM2, EM3, EM4 are blocked
 *      SLEEP_SleepBlockBegin(sleepEM1); // EM1, EM2, EM3, EM4 are blocked
 *      SLEEP_SleepBlockEnd(sleepEM2);   // still EM1, EM2, EM3, EM4 are blocked
 *      SLEEP_SleepBlockEnd(sleepEM1);   // still EM1, EM2, EM3, EM4 are blocked
 *      SLEEP_SleepBlockEnd(sleepEM1);   // all energy modes are allowed now\endcode
 *
 * @param[in] eMode
 *   Energy mode to end to block. Possible values:
 *   @li sleepEM1 - End to block the system from being set to EM1 (and EM2..4).
 *   @li sleepEM2 - End to block the system from being set to EM2 (and EM3/EM4).
 *   @li sleepEM3 - End to block the system from being set to EM3 (and EM4).
 ******************************************************************************/
void SLEEP_SleepBlockEnd(SLEEP_EnergyMode_t eMode);


/** @} (end addtogroup SLEEP) */
/** @} (end addtogroup EM_Drivers) */

#ifdef __cplusplus
}
#endif
#endif /* __SLEEP_H */
