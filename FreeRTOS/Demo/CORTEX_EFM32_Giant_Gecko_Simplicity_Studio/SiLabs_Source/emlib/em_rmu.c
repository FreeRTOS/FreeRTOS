/***************************************************************************//**
 * @file em_rmu.c
 * @brief Reset Management Unit (RMU) peripheral module peripheral API
 *
 * @version 4.2.1
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2015 Silicon Labs, http://www.silabs.com</b>
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

#include "em_common.h"
#include "em_emu.h"
#include "em_bus.h"

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
#if (_RMU_RSTCAUSE_MASK == 0x0000007FUL)
#define RMU_RSTCAUSE_PORST_XMASK         (0x00000000) /**0b0000000000000000  < Power On Reset */
#define RMU_RSTCAUSE_BODUNREGRST_XMASK   (0x00000081) /**0b0000000010000001  < Brown Out Detector Unregulated Domain Reset */
#define RMU_RSTCAUSE_BODREGRST_XMASK     (0x00000091) /**0b0000000010010001  < Brown Out Detector Regulated Domain Reset */
#define RMU_RSTCAUSE_EXTRST_XMASK        (0x00000001) /**0b0000000000000001  < External Pin Reset */
#define RMU_RSTCAUSE_WDOGRST_XMASK       (0x00000003) /**0b0000000000000011  < Watchdog Reset */
#define RMU_RSTCAUSE_LOCKUPRST_XMASK     (0x0000EFDF) /**0b1110111111011111  < LOCKUP Reset */
#define RMU_RSTCAUSE_SYSREQRST_XMASK     (0x0000EF9F) /**0b1110111110011111  < System Request Reset */
#define NUM_RSTCAUSES                             (7)

#elif (_RMU_RSTCAUSE_MASK == 0x000007FFUL)
#define RMU_RSTCAUSE_PORST_XMASK         (0x00000000) /**0b0000000000000000  < Power On Reset */
#define RMU_RSTCAUSE_BODUNREGRST_XMASK   (0x00000081) /**0b0000000010000001  < Brown Out Detector Unregulated Domain Reset */
#define RMU_RSTCAUSE_BODREGRST_XMASK     (0x00000091) /**0b0000000010010001  < Brown Out Detector Regulated Domain Reset */
#define RMU_RSTCAUSE_EXTRST_XMASK        (0x00000001) /**0b0000000000000001  < External Pin Reset */
#define RMU_RSTCAUSE_WDOGRST_XMASK       (0x00000003) /**0b0000000000000011  < Watchdog Reset */
#define RMU_RSTCAUSE_LOCKUPRST_XMASK     (0x0000EFDF) /**0b1110111111011111  < LOCKUP Reset */
#define RMU_RSTCAUSE_SYSREQRST_XMASK     (0x0000EF9F) /**0b1110111110011111  < System Request Reset */
#define RMU_RSTCAUSE_EM4RST_XMASK        (0x00000719) /**0b0000011100011001  < EM4 Reset */
#define RMU_RSTCAUSE_EM4WURST_XMASK      (0x00000619) /**0b0000011000011001  < EM4 Wake-up Reset */
#define RMU_RSTCAUSE_BODAVDD0_XMASK      (0x0000041F) /**0b0000010000011111  < AVDD0 Bod Reset. */
#define RMU_RSTCAUSE_BODAVDD1_XMASK      (0x0000021F) /**0b0000001000011111  < AVDD1 Bod Reset. */
#define NUM_RSTCAUSES                            (11)

#elif (_RMU_RSTCAUSE_MASK == 0x0000FFFFUL)
#define RMU_RSTCAUSE_PORST_XMASK         (0x00000000) /**0b0000000000000000  < Power On Reset */
#define RMU_RSTCAUSE_BODUNREGRST_XMASK   (0x00000081) /**0b0000000010000001  < Brown Out Detector Unregulated Domain Reset */
#define RMU_RSTCAUSE_BODREGRST_XMASK     (0x00000091) /**0b0000000010010001  < Brown Out Detector Regulated Domain Reset */
#define RMU_RSTCAUSE_EXTRST_XMASK        (0x00000001) /**0b0000000000000001  < External Pin Reset */
#define RMU_RSTCAUSE_WDOGRST_XMASK       (0x00000003) /**0b0000000000000011  < Watchdog Reset */
#define RMU_RSTCAUSE_LOCKUPRST_XMASK     (0x0000EFDF) /**0b1110111111011111  < LOCKUP Reset */
#define RMU_RSTCAUSE_SYSREQRST_XMASK     (0x0000EF9F) /**0b1110111110011111  < System Request Reset */
#define RMU_RSTCAUSE_EM4RST_XMASK        (0x00000719) /**0b0000011100011001  < EM4 Reset */
#define RMU_RSTCAUSE_EM4WURST_XMASK      (0x00000619) /**0b0000011000011001  < EM4 Wake-up Reset */
#define RMU_RSTCAUSE_BODAVDD0_XMASK      (0x0000041F) /**0b0000010000011111  < AVDD0 Bod Reset */
#define RMU_RSTCAUSE_BODAVDD1_XMASK      (0x0000021F) /**0b0000001000011111  < AVDD1 Bod Reset */
#define RMU_RSTCAUSE_BUBODVDDDREG_XMASK  (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector, VDD_DREG */
#define RMU_RSTCAUSE_BUBODBUVIN_XMASK    (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector, BU_VIN */
#define RMU_RSTCAUSE_BUBODUNREG_XMASK    (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector Unregulated Domain */
#define RMU_RSTCAUSE_BUBODREG_XMASK      (0x00000001) /**0b0000000000000001  < Backup Brown Out Detector Regulated Domain */
#define RMU_RSTCAUSE_BUMODERST_XMASK     (0x00000001) /**0b0000000000000001  < Backup mode reset */
#define NUM_RSTCAUSES                            (16)

#elif ((_RMU_RSTCAUSE_MASK & 0x0FFFFFFF) == 0x00010F1DUL)
#define RMU_RSTCAUSE_PORST_XMASK         (0x00000000) /**0b0000000000000000  < Power On Reset */
#define RMU_RSTCAUSE_BODAVDD_XMASK       (0x00000001) /**0b0000000000000001  < AVDD Bod Reset */
#define RMU_RSTCAUSE_BODDVDD_XMASK       (0x00000003) /**0b0000000000000011  < DVDD Bod Reset */
#define RMU_RSTCAUSE_BODREGRST_XMASK     (0x0000000F) /**0b0000000000001111  < Brown Out Detector Regulated Domain Reset */
#define RMU_RSTCAUSE_EXTRST_XMASK        (0x0000000F) /**0b0000000000001111  < External Pin Reset */
#define RMU_RSTCAUSE_LOCKUPRST_XMASK     (0x0000001F) /**0b0000000000011111  < LOCKUP Reset */
#define RMU_RSTCAUSE_SYSREQRST_XMASK     (0x0000001F) /**0b0000000000011111  < System Request Reset */
#define RMU_RSTCAUSE_WDOGRST_XMASK       (0x0000001F) /**0b0000000000011111  < Watchdog Reset */
#define RMU_RSTCAUSE_EM4RST_XMASK        (0x00000003) /**0b0000000000000011  < EM4H/S Reset */
#define NUM_RSTCAUSES                             (9)

#else
#warning "RMU_RSTCAUSE XMASKs are not defined for this family."
#endif

/*******************************************************************************
 *******************************   STRUCTS   ***********************************
 ******************************************************************************/

/** Reset cause mask type. */
typedef struct
{
  uint32_t resetCauseMask;
  uint32_t dontCareMask;
} RMU_ResetCauseMasks_Typedef;


/*******************************************************************************
 *******************************   TYPEDEFS   **********************************
 ******************************************************************************/

/** Reset cause mask table. */
static const RMU_ResetCauseMasks_Typedef  resetCauseMasks[NUM_RSTCAUSES] =
  {
    { RMU_RSTCAUSE_PORST,        RMU_RSTCAUSE_PORST_XMASK },
#if defined(RMU_RSTCAUSE_BODUNREGRST)
    { RMU_RSTCAUSE_BODUNREGRST,  RMU_RSTCAUSE_BODUNREGRST_XMASK },
#endif
#if defined(RMU_RSTCAUSE_BODREGRST)
    { RMU_RSTCAUSE_BODREGRST,    RMU_RSTCAUSE_BODREGRST_XMASK },
#endif
#if defined(RMU_RSTCAUSE_AVDDBOD)
    { RMU_RSTCAUSE_AVDDBOD,      RMU_RSTCAUSE_BODAVDD_XMASK },
#endif
#if defined(RMU_RSTCAUSE_DVDDBOD)
    { RMU_RSTCAUSE_DVDDBOD,      RMU_RSTCAUSE_BODDVDD_XMASK },
#endif
#if defined(RMU_RSTCAUSE_DECBOD)
    { RMU_RSTCAUSE_DECBOD,       RMU_RSTCAUSE_BODREGRST_XMASK },
#endif
    { RMU_RSTCAUSE_EXTRST,       RMU_RSTCAUSE_EXTRST_XMASK },
    { RMU_RSTCAUSE_WDOGRST,      RMU_RSTCAUSE_WDOGRST_XMASK },
    { RMU_RSTCAUSE_LOCKUPRST,    RMU_RSTCAUSE_LOCKUPRST_XMASK },
    { RMU_RSTCAUSE_SYSREQRST,    RMU_RSTCAUSE_SYSREQRST_XMASK },
#if defined(RMU_RSTCAUSE_EM4RST)
    { RMU_RSTCAUSE_EM4RST,       RMU_RSTCAUSE_EM4RST_XMASK },
#endif
#if defined(RMU_RSTCAUSE_EM4WURST)
    { RMU_RSTCAUSE_EM4WURST,     RMU_RSTCAUSE_EM4WURST_XMASK },
#endif
#if defined(RMU_RSTCAUSE_BODAVDD0)
    { RMU_RSTCAUSE_BODAVDD0,     RMU_RSTCAUSE_BODAVDD0_XMASK },
#endif
#if defined(RMU_RSTCAUSE_BODAVDD1)
    { RMU_RSTCAUSE_BODAVDD1,     RMU_RSTCAUSE_BODAVDD1_XMASK },
#endif
#if defined(BU_PRESENT)
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
#if defined(EMLIB_REGRESSION_TEST)
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
 * @param[in] mode  Reset mode
 ******************************************************************************/
void RMU_ResetControl(RMU_Reset_TypeDef reset, RMU_ResetMode_TypeDef mode)
{
  /* Note that the RMU supports bit-band access, but not peripheral bit-field set/clear */
#if defined(_RMU_CTRL_PINRMODE_MASK)
  uint32_t val;
#endif
  uint32_t shift;

  shift = EFM32_CTZ((uint32_t)reset);
#if defined(_RMU_CTRL_PINRMODE_MASK)
  val = (uint32_t)mode << shift;
  RMU->CTRL = (RMU->CTRL & ~reset) | val;
#else
  BUS_RegBitWrite(&RMU->CTRL, (uint32_t)shift, mode ? 1 : 0);
#endif
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
  RMU->CMD = RMU_CMD_RCCLR;

#if defined(EMU_AUXCTRL_HRCCLR)
  {
    uint32_t locked;

    /* Clear some reset causes not cleared with RMU CMD register */
    /* (If EMU registers locked, they must be unlocked first) */
    locked = EMU->LOCK & EMU_LOCK_LOCKKEY_LOCKED;
    if (locked)
    {
      EMU_Unlock();
    }

    BUS_RegBitWrite(&(EMU->AUXCTRL), _EMU_AUXCTRL_HRCCLR_SHIFT, 1);
    BUS_RegBitWrite(&(EMU->AUXCTRL), _EMU_AUXCTRL_HRCCLR_SHIFT, 0);

    if (locked)
    {
      EMU_Lock();
    }
  }
#endif
}


/***************************************************************************//**
 * @brief
 *   Get the cause of the last reset.
 *
 * @details
 *   In order to be useful, the reset cause must be cleared by software before a new
 *   reset occurs, otherwise reset causes may accumulate. See @ref
 *   RMU_ResetCauseClear(). This function call will return the main cause for
 *   reset, which can be a bit mask (several causes), and clear away "noise".
 *
 * @return
 *   Reset cause mask. Please consult the reference manual for description
 *   of the reset cause mask.
 ******************************************************************************/
uint32_t RMU_ResetCauseGet(void)
{
#if !defined(EMLIB_REGRESSION_TEST)
  uint32_t rstCause = RMU->RSTCAUSE;
#endif
  uint32_t validRstCause = 0;
  uint32_t i;

  for (i = 0; i < NUM_RSTCAUSES; i++)
  {
    /* Checks to see if rstCause matches a RSTCAUSE and is not excluded by the X-mask */
    if ((rstCause & resetCauseMasks[i].resetCauseMask)
        && !(rstCause & resetCauseMasks[i].dontCareMask))
    {
      /* Adds the reset-cause to list of real reset-causes */
      validRstCause |= resetCauseMasks[i].resetCauseMask;
    }
  }
  return validRstCause;
}


/** @} (end addtogroup RMU) */
/** @} (end addtogroup EM_Library) */
#endif /* defined(RMU_COUNT) && (RMU_COUNT > 0) */
