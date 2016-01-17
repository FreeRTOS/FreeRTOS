/***************************************************************************//**
 * @file sleep.c
 * @brief Energy Modes management driver.
 * @version 4.0.0
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


/* Chip specific header file(s). */
#include "em_device.h"
#include "em_assert.h"
#include "em_int.h"
#include "em_rmu.h"
#include "em_emu.h"

/* Module header file(s). */
#include "sleep.h"

/* stdlib is needed for NULL definition */
#include <stdlib.h>

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

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

/* Number of low energy modes (EM1, EM2, EM3). Note: EM4 sleep/wakeup is handled
 * differently therefore it is not part of the list! */
#define SLEEP_NUMOF_LOW_ENERGY_MODES    3U



/*******************************************************************************
 ******************************   TYPEDEFS   ***********************************
 ******************************************************************************/


/*******************************************************************************
 ******************************   CONSTANTS   **********************************
 ******************************************************************************/


/*******************************************************************************
 *******************************   STATICS   ***********************************
 ******************************************************************************/

/* Callback functions to call before and after sleep. */
static SLEEP_CbFuncPtr_t sleepCallback  = NULL;
static SLEEP_CbFuncPtr_t wakeUpCallback = NULL;

/* Sleep block counter array representing the nested sleep blocks for the low
 * energy modes (EM1/EM2/EM3). Array index 0 corresponds to EM1, 1 to EM2 and 2
 * to EM3 accordingly.
 *
 * Note:
 * - EM4 sleep/wakeup is handled differently therefore it is not part of the
 *   list!
 * - Max. number of sleep block nesting is 255. */
static uint8_t sleepBlockCnt[SLEEP_NUMOF_LOW_ENERGY_MODES];

/*******************************************************************************
 ******************************   PROTOTYPES   *********************************
 ******************************************************************************/

static void SLEEP_EnterEMx(SLEEP_EnergyMode_t eMode);
//static SLEEP_EnergyMode_t SLEEP_LowestEnergyModeGet(void);

/** @endcond */

/*******************************************************************************
 ***************************   GLOBAL FUNCTIONS   ******************************
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
void SLEEP_Init(SLEEP_CbFuncPtr_t pSleepCb, SLEEP_CbFuncPtr_t pWakeUpCb)
{
  /* Initialize callback functions. */
  sleepCallback  = pSleepCb;
  wakeUpCallback = pWakeUpCb;

  /* Reset sleep block counters. Note: not using for() saves code! */
  sleepBlockCnt[0U] = 0U;
  sleepBlockCnt[1U] = 0U;
  sleepBlockCnt[2U] = 0U;

#if (SLEEP_EM4_WAKEUP_CALLBACK_ENABLED == true) && defined(RMU_RSTCAUSE_EM4WURST)
  /* Check if the Init() happened after an EM4 reset. */
  if (RMU_ResetCauseGet() & RMU_RSTCAUSE_EM4WURST)
  {
    /* Clear the cause of the reset. */
    RMU_ResetCauseClear();
    /* Call wakeup callback with EM4 parameter. */
    if (NULL != wakeUpCallback)
    {
      wakeUpCallback(sleepEM4);
    }
  }
#endif
}


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
SLEEP_EnergyMode_t SLEEP_Sleep(void)
{
  SLEEP_EnergyMode_t allowedEM;

  INT_Disable();

  allowedEM = SLEEP_LowestEnergyModeGet();

  if ((allowedEM >= sleepEM1) && (allowedEM <= sleepEM3))
  {
    SLEEP_EnterEMx(allowedEM);
  }
  else
  {
    allowedEM = sleepEM0;
  }

  INT_Enable();

  return(allowedEM);
}


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
void SLEEP_ForceSleepInEM4(void)
{
#if (SLEEP_HW_LOW_ENERGY_BLOCK_ENABLED == true)
  /* Unblock the EM2/EM3/EM4 block in the EMU. */
  EMU_EM2UnBlock();
#endif

  /* Request entering to EM4. */
  SLEEP_EnterEMx(sleepEM4);
}

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
void SLEEP_SleepBlockBegin(SLEEP_EnergyMode_t eMode)
{
  EFM_ASSERT((eMode >= sleepEM1) && (eMode < sleepEM4));
  EFM_ASSERT((sleepBlockCnt[(uint8_t) eMode - 1U]) < 255U);

  /* Increase the sleep block counter of the selected energy mode. */
  sleepBlockCnt[(uint8_t) eMode - 1U]++;

#if (SLEEP_HW_LOW_ENERGY_BLOCK_ENABLED == true)
  /* Block EM2/EM3 sleep if the EM2 block begins. */
  if (eMode == sleepEM2)
  {
    EMU_EM2Block();
  }
#endif
}

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
void SLEEP_SleepBlockEnd(SLEEP_EnergyMode_t eMode)
{
  EFM_ASSERT((eMode >= sleepEM1) && (eMode < sleepEM4));

  /* Decrease the sleep block counter of the selected energy mode. */
  if (sleepBlockCnt[(uint8_t) eMode - 1U] > 0U)
  {
    sleepBlockCnt[(uint8_t) eMode - 1U]--;
  }

#if (SLEEP_HW_LOW_ENERGY_BLOCK_ENABLED == true)
  /* Check if the EM2/EM3 block should be unblocked in the EMU. */
  if (0U == sleepBlockCnt[(uint8_t) sleepEM2 - 1U])
  {
    EMU_EM2UnBlock();
  }
#endif
}

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
SLEEP_EnergyMode_t SLEEP_LowestEnergyModeGet(void)
{
  SLEEP_EnergyMode_t tmpLowestEM = sleepEM0;

  /* Check which is the lowest energy mode that the system can be set to. */
  if (0U == sleepBlockCnt[(uint8_t) sleepEM1 - 1U])
  {
    tmpLowestEM = sleepEM1;
    if (0U == sleepBlockCnt[(uint8_t) sleepEM2 - 1U])
    {
      tmpLowestEM = sleepEM2;
      if (0U == sleepBlockCnt[(uint8_t) sleepEM3 - 1U])
      {
        tmpLowestEM = sleepEM3;
      }
    }
  }

  /* Compare with the default lowest energy mode setting. */
  if (SLEEP_LOWEST_ENERGY_MODE_DEFAULT < tmpLowestEM)
  {
    tmpLowestEM = SLEEP_LOWEST_ENERGY_MODE_DEFAULT;
  }

  return tmpLowestEM;
}

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

/***************************************************************************//**
 * @brief
 *   Call the callbacks and enter the requested energy mode.
 *
 * @details
 *   This function is not part of the API, therefore it shall not be called by
 *   the user directly as it doesn not have any checks if the system is ready
 *   for sleep!
 *
 * @note
 *   The EM4 wakeup callback is not being called from this function because
 *   waking up from EM4 causes a reset.
 *   If SLEEP_EM4_WAKEUP_CALLBACK_ENABLED is set to true, SLEEP_Init() function
 *   checks for the cause of the reset and calls the wakeup callback if the
 *   reset was a wakeup from EM4.
 ******************************************************************************/
static void SLEEP_EnterEMx(SLEEP_EnergyMode_t eMode)
{
  EFM_ASSERT((eMode > sleepEM0) && (eMode <= sleepEM4));

  /* Call sleepCallback() before going to sleep. */
  if (NULL != sleepCallback)
  {
    /* Call the callback before going to sleep. */
    sleepCallback(eMode);
  }

  /* Enter the requested energy mode. */
  switch (eMode)
  {
  case sleepEM1:
  {
    EMU_EnterEM1();
  } break;

  case sleepEM2:
  {
    EMU_EnterEM2(true);
  } break;

  case sleepEM3:
  {
    EMU_EnterEM3(true);
  } break;

  case sleepEM4:
  {
    EMU_EnterEM4();
  } break;

  default:
  {
    /* Don't do anything, stay in EM0. */
  } break;
  }

  /* Call the callback after waking up from sleep. */
  if (NULL != wakeUpCallback)
  {
    wakeUpCallback(eMode);
  }
}
/** @endcond */

/** @} (end addtogroup SLEEP */
/** @} (end addtogroup EM_Drivers) */
