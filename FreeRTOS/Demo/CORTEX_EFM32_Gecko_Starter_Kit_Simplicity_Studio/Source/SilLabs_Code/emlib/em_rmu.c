/***************************************************************************//**
 * @file em_rmu.c
 * @brief Reset Management Unit (RMU) peripheral module peripheral API
 *
 * @version 4.0.0
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Silicon Labs has no
 * obligation to support this Software. Silicon Labs is providing the
 * Software "AS IS", with no express or implied warranties of any kind,
 * including, but not limited to, any implied warranties of merchantability
 * or fitness for any particular purpose or warranties against infringement
 * of any proprietary rights of a third party.
 *
 * Silicon Labs will not be liable for any consequential, incidental, or
 * special damages, or any other relief, or for any claim by any third party,
 * arising from your use of this Software.
 *
 ******************************************************************************/


#include "em_rmu.h"
#if defined(RMU_COUNT) && (RMU_COUNT > 0)

#include "em_emu.h"
#include "em_bitband.h"

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup RMU
 * @brief Reset Management Unit (RMU) Peripheral API
 * @{
 ******************************************************************************/

/*******************************************************************************
 *****************************     DEFINES     *********************************
 ******************************************************************************/

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

/* Reset cause "don't care" definitions.
   1's mark the bits that must be zero, zeros are "don't cares". */
#define RMU_RSTCAUSE_PORST_XMASK         (0x00000000) /**0b0000000000000000  < Power On Reset */
#define RMU_RSTCAUSE_BODUNREGRST_XMASK   (0x00000081) /**0b0000000010000001  < Brown Out Detector Unregulated Domain Reset */
#define RMU_RSTCAUSE_BODREGRST_XMASK     (0x00000091) /**0b0000000010010001  < Brown Out Detector Regulated Domain Reset */
#define RMU_RSTCAUSE_EXTRST_XMASK        (0x00000001) /**0b0000000000000001  < External Pin Reset */
#define RMU_RSTCAUSE_WDOGRST_XMASK       (0x00000003) /**0b0000000000000011  < Watchdog Reset */
#define RMU_RSTCAUSE_LOCKUPRST_XMASK     (0x0000EFDF) /**0b1110111111011111  < LOCKUP Reset */
#define RMU_RSTCAUSE_SYSREQRST_XMASK     (0x0000EF9F) /**0b1110111110011111  < System Request Reset */
#define NUM_RSTCAUSES                             (7)
#ifndef _EFM32_GECKO_FAMILY
#define RMU_RSTCAUSE_EM4RST_XMASK        (0x00000719) /**0b0000011100011001  < EM4 Reset */
#define RMU_RSTCAUSE_EM4WURST_XMASK      (0x00000619) /**0b0000011000011001  < EM4 Wake-up Reset */
#define RMU_RSTCAUSE_BODAVDD0_XMASK      (0x0000041F) /**0b0000010000011111  < AVDD0 Bod Reset. */
#define RMU_RSTCAUSE_BODAVDD1_XMASK      (0x0000021F) /**0b0000001000011111  < AVDD1 Bod Reset. */
#undef NUM_RSTCAUSES
#define NUM_RSTCAUSES                            (11)
#endif
#ifdef BU_PRESENT
#define RMU_RSTCAUSE_BUBODVDDDREG_XMASK  (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector, VDD_DREG */
#define RMU_RSTCAUSE_BUBODBUVIN_XMASK    (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector, BU_VIN */
#define RMU_RSTCAUSE_BUBODUNREG_XMASK    (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector Unregulated Domain */
#define RMU_RSTCAUSE_BUBODREG_XMASK      (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector Regulated Domain */
#define RMU_RSTCAUSE_BUMODERST_XMASK     (0x00000001) /**0b0000000000000001  < Backup mode reset */
#undef NUM_RSTCAUSES
#define NUM_RSTCAUSES                            (16)
#endif

/*******************************************************************************
 *******************************   STRUCTS   ***********************************
 ******************************************************************************/

/** Reset cause mask type. */
typedef struct
{
  uint32_t    resetCauseMask;
  uint32_t    dontCareMask;
} RMU_ResetCauseMasks_Typedef;


/*******************************************************************************
 *******************************   TYPEDEFS   **********************************
 ******************************************************************************/

/** Reset cause mask table. */
static const RMU_ResetCauseMasks_Typedef  resetCauseMasks[NUM_RSTCAUSES] =
  {
    { RMU_RSTCAUSE_PORST,        RMU_RSTCAUSE_PORST_XMASK },
    { RMU_RSTCAUSE_BODUNREGRST,  RMU_RSTCAUSE_BODUNREGRST_XMASK },
    { RMU_RSTCAUSE_BODREGRST,    RMU_RSTCAUSE_BODREGRST_XMASK },
    { RMU_RSTCAUSE_EXTRST,       RMU_RSTCAUSE_EXTRST_XMASK },
    { RMU_RSTCAUSE_WDOGRST,      RMU_RSTCAUSE_WDOGRST_XMASK },
    { RMU_RSTCAUSE_LOCKUPRST,    RMU_RSTCAUSE_LOCKUPRST_XMASK },
    { RMU_RSTCAUSE_SYSREQRST,    RMU_RSTCAUSE_SYSREQRST_XMASK },
#ifndef _EFM32_GECKO_FAMILY
    { RMU_RSTCAUSE_EM4RST,       RMU_RSTCAUSE_EM4RST_XMASK },
    { RMU_RSTCAUSE_EM4WURST,     RMU_RSTCAUSE_EM4WURST_XMASK },
    { RMU_RSTCAUSE_BODAVDD0,     RMU_RSTCAUSE_BODAVDD0_XMASK },
    { RMU_RSTCAUSE_BODAVDD1,     RMU_RSTCAUSE_BODAVDD1_XMASK },
#endif
#ifdef BU_PRESENT
    { RMU_RSTCAUSE_BUBODVDDDREG, RMU_RSTCAUSE_BUBODVDDDREG_XMASK },
    { RMU_RSTCAUSE_BUBODBUVIN,   RMU_RSTCAUSE_BUBODBUVIN_XMASK },
    { RMU_RSTCAUSE_BUBODUNREG,   RMU_RSTCAUSE_BUBODUNREG_XMASK },
    { RMU_RSTCAUSE_BUBODREG,     RMU_RSTCAUSE_BUBODREG_XMASK },
    { RMU_RSTCAUSE_BUMODERST,    RMU_RSTCAUSE_BUMODERST_XMASK },
#endif
  };


/*******************************************************************************
 ********************************     TEST     ********************************
 ******************************************************************************/
#ifdef EMLIB_REGRESSION_TEST
/* Test variable that replaces the RSTCAUSE cause register when testing
   the RMU_ResetCauseGet function. */
extern uint32_t rstCause;
#endif


/** @endcond */

/*******************************************************************************
 **************************   GLOBAL FUNCTIONS   *******************************
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Disable/enable reset for various peripherals and signal sources
 *
 * @param[in] reset Reset types to enable/disable
 *
 * @param[in] enable
 *   @li false - Disable reset signal or flag
 *   @li true - Enable reset signal or flag
 ******************************************************************************/
void RMU_ResetControl(RMU_Reset_TypeDef reset, bool enable)
{
  BITBAND_Peripheral(&(RMU->CTRL), (uint32_t)reset, (uint32_t)enable);
}


/***************************************************************************//**
 * @brief
 *   Clear the reset cause register.
 *
 * @details
 *   This function clears all the reset cause bits of the RSTCAUSE register.
 *   The reset cause bits must be cleared by SW before a new reset occurs,
 *   otherwise reset causes may accumulate. See @ref RMU_ResetCauseGet().
 ******************************************************************************/
void RMU_ResetCauseClear(void)
{
  uint32_t locked;

  RMU->CMD = RMU_CMD_RCCLR;

  /* Clear some reset causes not cleared with RMU CMD register */
  /* (If EMU registers locked, they must be unlocked first) */
  locked = EMU->LOCK & EMU_LOCK_LOCKKEY_LOCKED;
  if (locked)
  {
    EMU_Unlock();
  }

  BITBAND_Peripheral(&(EMU->AUXCTRL), 0, 1);
  BITBAND_Peripheral(&(EMU->AUXCTRL), 0, 0);

  if (locked)
  {
    EMU_Lock();
  }
}


/***************************************************************************//**
 * @brief
 *   Get the cause of the last reset.
 *
 * @details
 *   In order to be useful, the reset cause must be cleared by SW before a new
 *   reset occurs, otherwise reset causes may accumulate. See @ref
 *   RMU_ResetCauseClear(). This function call will return the main cause for
 *   reset, which can be a bit mask (several causes), and clear away "noise".
 *
 * @return
 *   The reset cause, a bit mask of (typically, but not always, only one) of:
 *   @li RMU_RSTCAUSE_PORST - Power on reset
 *   @li RMU_RSTCAUSE_BODUNREGRST - Brown out detector, unregulated power
 *   @li RMU_RSTCAUSE_BODREGRST - Brown out detector, regulated power
 *   @li RMU_RSTCAUSE_EXTRST - External reset
 *   @li RMU_RSTCAUSE_WDOGRST - Watchdog reset
 *   @li RMU_RSTCAUSE_LOCKUPRST - Cortex-M3 lockup reset
 *   @li RMU_RSTCAUSE_SYSREQRST - Cortex-M3 system request reset
 *   @li RMU_RSTCAUSE_EM4RST - Set if the system has been in EM4
 *   @li RMU_RSTCAUSE_EM4WURST - Set if the system woke up on a pin from EM4
 *   @li RMU_RSTCAUSE_BODAVDD0 - Analog power domain 0 brown out detector reset
 *   @li RMU_RSTCAUSE_BODAVDD1 - Analog power domain 1 brown out detector reset
 *   @li RMU_RSTCAUSE_BUBODVDDDREG - Backup BOD on VDDD_REG triggered
 *   @li RMU_RSTCAUSE_BUBODBUVIN - Backup BOD on BU_VIN triggered
 *   @li RMU_RSTCAUSE_BUBODUNREG - Backup BOD on unregulated power triggered
 *   @li RMU_RSTCAUSE_BUBODREG - Backup BOD on regulated powered has triggered
 *   @li RMU_RSTCAUSE_BUMODERST - System has been in Backup mode
 ******************************************************************************/
uint32_t RMU_ResetCauseGet(void)
{
#ifndef EMLIB_REGRESSION_TEST
  uint32_t rstCause      = RMU->RSTCAUSE;
#endif
  uint32_t validRstCause = 0;
  int      i;
  
  for (i=0; i<NUM_RSTCAUSES; i++)
  {
    //Checks to see if rstCause matches a RSTCAUSE and is not excluded by the X-mask
    if ((rstCause & resetCauseMasks[i].resetCauseMask) &&
        !(rstCause & resetCauseMasks[i].dontCareMask))
    {
      //Adds the reset-cause to list of real reset-causes
      validRstCause |= resetCauseMasks[i].resetCauseMask;
    }
  }
  
  return validRstCause;
}


/** @} (end addtogroup RMU) */
/** @} (end addtogroup EM_Library) */
#endif /* defined(RMU_COUNT) && (RMU_COUNT > 0) */
