/***************************************************************************//**
 * @file em_cmu.c
 * @brief Clock management unit (CMU) Peripheral API
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
#include "em_cmu.h"
#if defined( CMU_PRESENT )

#include <stddef.h>
#include <limits.h>
#include "em_assert.h"
#include "em_bus.h"
#include "em_emu.h"
#include "em_system.h"

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup CMU
 * @brief Clock management unit (CMU) Peripheral API
 * @{
 ******************************************************************************/

/*******************************************************************************
 ******************************   DEFINES   ************************************
 ******************************************************************************/

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

#if defined( _SILICON_LABS_32B_PLATFORM_2 )
/** Maximum allowed core frequency when using 0 wait-states on flash access. */
#define CMU_MAX_FREQ_0WS    26000000
/** Maximum allowed core frequency when using 1 wait-states on flash access */
#define CMU_MAX_FREQ_1WS    40000000
#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
/** Maximum allowed core frequency when using 0 wait-states on flash access. */
#define CMU_MAX_FREQ_0WS    16000000
/** Maximum allowed core frequency when using 1 wait-states on flash access */
#define CMU_MAX_FREQ_1WS    32000000
#else
#error "Unkown MCU platform."
#endif

#if defined( CMU_CTRL_HFLE )
/** Maximum frequency for HFLE needs to be enabled on Giant, Leopard and
    Wonder. */
#if defined( _EFM32_WONDER_FAMILY )     \
    || defined( _EZR32_LEOPARD_FAMILY ) \
    || defined( _EZR32_WONDER_FAMILY )
#define CMU_MAX_FREQ_HFLE() 24000000
#elif defined ( _EFM32_GIANT_FAMILY )
#define CMU_MAX_FREQ_HFLE() (maxFreqHfle())
#else
#error Invalid part/device.
#endif
#endif

/*******************************************************************************
 **************************   LOCAL VARIABLES   ********************************
 ******************************************************************************/

#if defined( _CMU_AUXHFRCOCTRL_FREQRANGE_MASK )
static CMU_AUXHFRCOFreq_TypeDef auxHfrcoFreq = cmuAUXHFRCOFreq_19M0Hz;
#endif

/** @endcond */

/*******************************************************************************
 **************************   LOCAL FUNCTIONS   ********************************
 ******************************************************************************/

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

/***************************************************************************//**
 * @brief
 *   Get the AUX clock frequency. Used by MSC flash programming and LESENSE,
 *   by default also as debug clock.
 *
 * @return
 *   AUX Frequency in Hz
 ******************************************************************************/
static uint32_t auxClkGet(void)
{
  uint32_t ret;

#if defined( _CMU_AUXHFRCOCTRL_FREQRANGE_MASK )
  ret = auxHfrcoFreq;

#elif defined( _CMU_AUXHFRCOCTRL_BAND_MASK )
  /* All Geckos from TG and newer */
  switch(CMU->AUXHFRCOCTRL & _CMU_AUXHFRCOCTRL_BAND_MASK)
  {
    case CMU_AUXHFRCOCTRL_BAND_1MHZ:
      ret = 1000000;
      break;

    case CMU_AUXHFRCOCTRL_BAND_7MHZ:
      ret = 7000000;
      break;

    case CMU_AUXHFRCOCTRL_BAND_11MHZ:
      ret = 11000000;
      break;

    case CMU_AUXHFRCOCTRL_BAND_14MHZ:
      ret = 14000000;
      break;

    case CMU_AUXHFRCOCTRL_BAND_21MHZ:
      ret = 21000000;
      break;

#if defined( _CMU_AUXHFRCOCTRL_BAND_28MHZ )
    case CMU_AUXHFRCOCTRL_BAND_28MHZ:
      ret = 28000000;
      break;
#endif

    default:
      EFM_ASSERT(0);
      ret = 0;
      break;
  }

#else
  /* Gecko has a fixed 14Mhz AUXHFRCO clock */
  ret = 14000000;

#endif

  return ret;
}


/***************************************************************************//**
 * @brief
 *   Get the Debug Trace clock frequency
 *
 * @return
 *   Debug Trace frequency in Hz
 ******************************************************************************/
static uint32_t dbgClkGet(void)
{
  uint32_t ret;
  CMU_Select_TypeDef clk;

  /* Get selected clock source */
  clk = CMU_ClockSelectGet(cmuClock_DBG);

  switch(clk)
  {
    case cmuSelect_HFCLK:
      ret = SystemHFClockGet();
#if defined( _CMU_CTRL_HFCLKDIV_MASK )
      /* Family with an additional divider. */
      ret = ret / (1 + ((CMU->CTRL & _CMU_CTRL_HFCLKDIV_MASK)
                        >> _CMU_CTRL_HFCLKDIV_SHIFT));
#endif
      break;

    case cmuSelect_AUXHFRCO:
      ret = auxClkGet();
      break;

    default:
      EFM_ASSERT(0);
      ret = 0;
      break;
  }
  return ret;
}


/***************************************************************************//**
 * @brief
 *   Configure flash access wait states in order to support given core clock
 *   frequency.
 *
 * @param[in] coreFreq
 *   Core clock frequency to configure flash wait-states for
 ******************************************************************************/
static void flashWaitStateControl(uint32_t coreFreq)
{
  uint32_t mode;
  bool mscLocked;
#if defined( MSC_READCTRL_MODE_WS0SCBTP )
  bool scbtpEn;   /* Suppressed Conditional Branch Target Prefetch setting. */
#endif

  /* Make sure the MSC is unlocked */
  mscLocked = MSC->LOCK;
  MSC->LOCK = MSC_UNLOCK_CODE;

  /* Get mode and SCBTP enable */
  mode = MSC->READCTRL & _MSC_READCTRL_MODE_MASK;
#if defined( MSC_READCTRL_MODE_WS0SCBTP )
  switch(mode)
  {
    case MSC_READCTRL_MODE_WS0:
    case MSC_READCTRL_MODE_WS1:
#if defined( MSC_READCTRL_MODE_WS2 )
    case MSC_READCTRL_MODE_WS2:
#endif
      scbtpEn = false;
      break;

    default: /* WSxSCBTP */
      scbtpEn = true;
    break;
  }
#endif


  /* Set mode based on the core clock frequency and SCBTP enable */
#if defined( MSC_READCTRL_MODE_WS0SCBTP )
  if (false)
  {
  }
#if defined( MSC_READCTRL_MODE_WS2 )
  else if (coreFreq > CMU_MAX_FREQ_1WS)
  {
    mode = (scbtpEn ? MSC_READCTRL_MODE_WS2SCBTP : MSC_READCTRL_MODE_WS2);
  }
#endif
  else if ((coreFreq <= CMU_MAX_FREQ_1WS) && (coreFreq > CMU_MAX_FREQ_0WS))
  {
    mode = (scbtpEn ? MSC_READCTRL_MODE_WS1SCBTP : MSC_READCTRL_MODE_WS1);
  }
  else
  {
    mode = (scbtpEn ? MSC_READCTRL_MODE_WS0SCBTP : MSC_READCTRL_MODE_WS0);
  }

#else /* If MODE and SCBTP is in separate register fields */

  if (false)
  {
  }
#if defined( MSC_READCTRL_MODE_WS2 )
  else if (coreFreq > CMU_MAX_FREQ_1WS)
  {
    mode = MSC_READCTRL_MODE_WS2;
  }
#endif
  else if ((coreFreq <= CMU_MAX_FREQ_1WS) && (coreFreq > CMU_MAX_FREQ_0WS))
  {
    mode = MSC_READCTRL_MODE_WS1;
  }
  else
  {
    mode = MSC_READCTRL_MODE_WS0;
  }
#endif

  /* BUS_RegMaskedWrite cannot be used here as it would temporarely set the
     mode field to WS0 */
  MSC->READCTRL = (MSC->READCTRL &~_MSC_READCTRL_MODE_MASK) | mode;

  if (mscLocked)
  {
    MSC->LOCK = 0;
  }
}


/***************************************************************************//**
 * @brief
 *   Configure flash access wait states to most conservative setting for
 *   this target. Retain SCBTP (Suppressed Conditional Branch Target Prefetch)
 *   setting.
 ******************************************************************************/
static void flashWaitStateMax(void)
{
  flashWaitStateControl(SystemMaxCoreClockGet());
}


/***************************************************************************//**
 * @brief
 *   Get the LFnCLK frequency based on current configuration.
 *
 * @param[in] lfClkBranch
 *   Selected LF branch
 *
 * @return
 *   The LFnCLK frequency in Hz. If no LFnCLK is selected (disabled), 0 is
 *   returned.
 ******************************************************************************/
static uint32_t lfClkGet(CMU_Clock_TypeDef lfClkBranch)
{
  uint32_t sel;
  uint32_t ret = 0;

  switch (lfClkBranch)
  {
    case cmuClock_LFA:
    case cmuClock_LFB:
#if defined( _CMU_LFCCLKEN0_MASK )
    case cmuClock_LFC:
#endif
#if defined( _CMU_LFECLKSEL_MASK )
    case cmuClock_LFE:
#endif
      break;

    default:
      EFM_ASSERT(0);
      break;
  }

  sel = CMU_ClockSelectGet(lfClkBranch);

  /* Get clock select field */
  switch (lfClkBranch)
  {
    case cmuClock_LFA:
#if defined( _CMU_LFCLKSEL_MASK )
      sel = (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFA_MASK) >> _CMU_LFCLKSEL_LFA_SHIFT;
#elif defined( _CMU_LFACLKSEL_MASK )
      sel = (CMU->LFACLKSEL & _CMU_LFACLKSEL_LFA_MASK) >> _CMU_LFACLKSEL_LFA_SHIFT;
#else
      EFM_ASSERT(0);
#endif
      break;

    case cmuClock_LFB:
#if defined( _CMU_LFCLKSEL_MASK )
      sel = (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFB_MASK) >> _CMU_LFCLKSEL_LFB_SHIFT;
#elif defined( _CMU_LFBCLKSEL_MASK )
      sel = (CMU->LFBCLKSEL & _CMU_LFBCLKSEL_LFB_MASK) >> _CMU_LFBCLKSEL_LFB_SHIFT;
#else
      EFM_ASSERT(0);
#endif
      break;

#if defined( _CMU_LFCCLKEN0_MASK )
    case cmuClock_LFC:
      sel = (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFC_MASK) >> _CMU_LFCLKSEL_LFC_SHIFT;
      break;
#endif

#if defined( _CMU_LFECLKSEL_MASK )
    case cmuClock_LFE:
      sel = (CMU->LFECLKSEL & _CMU_LFECLKSEL_LFE_MASK) >> _CMU_LFECLKSEL_LFE_SHIFT;
      break;
#endif

    default:
      EFM_ASSERT(0);
      break;
  }

  /* Get clock frequency */
#if defined( _CMU_LFCLKSEL_MASK )
  switch (sel)
  {
    case _CMU_LFCLKSEL_LFA_LFRCO:
      ret = SystemLFRCOClockGet();
      break;

    case _CMU_LFCLKSEL_LFA_LFXO:
      ret = SystemLFXOClockGet();
      break;

#if defined( _CMU_LFCLKSEL_LFA_HFCORECLKLEDIV2 )
    case _CMU_LFCLKSEL_LFA_HFCORECLKLEDIV2:
#if defined( CMU_CTRL_HFLE )
      /* Family which can use an extra div 4 divider  */
      /* (and must if >32MHz) or HFLE is set.         */
      if(((CMU->HFCORECLKDIV & _CMU_HFCORECLKDIV_HFCORECLKLEDIV_MASK)
           == CMU_HFCORECLKDIV_HFCORECLKLEDIV_DIV4)
         || (CMU->CTRL & CMU_CTRL_HFLE))
      {
        ret = SystemCoreClockGet() / 4U;
      }
      else
      {
        ret = SystemCoreClockGet() / 2U;
      }
#else
      ret = SystemCoreClockGet() / 2U;
#endif
      break;
#endif

    case _CMU_LFCLKSEL_LFA_DISABLED:
      ret = 0;
#if defined( CMU_LFCLKSEL_LFAE )
      /* Check LF Extended bit setting for LFA or LFB ULFRCO clock */
      if ((lfClkBranch == cmuClock_LFA) || (lfClkBranch == cmuClock_LFB))
      {
        if (CMU->LFCLKSEL >> (lfClkBranch == cmuClock_LFA
                              ? _CMU_LFCLKSEL_LFAE_SHIFT
                              : _CMU_LFCLKSEL_LFBE_SHIFT))
        {
          ret = SystemULFRCOClockGet();
        }
      }
#endif
      break;

    default:
      EFM_ASSERT(0);
      ret = 0U;
      break;
  }
#endif /* _CMU_LFCLKSEL_MASK */

#if defined( _CMU_LFACLKSEL_MASK )
  switch (sel)
  {
    case _CMU_LFACLKSEL_LFA_LFRCO:
      ret = SystemLFRCOClockGet();
      break;

    case _CMU_LFACLKSEL_LFA_LFXO:
      ret = SystemLFXOClockGet();
      break;

    case _CMU_LFACLKSEL_LFA_ULFRCO:
      ret = SystemULFRCOClockGet();
      break;

#if defined( _CMU_LFACLKSEL_LFA_HFCLKLE )
    case _CMU_LFACLKSEL_LFA_HFCLKLE:
      ret = ((CMU->HFPRESC & _CMU_HFPRESC_HFCLKLEPRESC_MASK)
             == CMU_HFPRESC_HFCLKLEPRESC_DIV4)
            ? SystemCoreClockGet() / 4U
            : SystemCoreClockGet() / 2U;
      break;
#elif defined( _CMU_LFBCLKSEL_LFB_HFCLKLE )
    case _CMU_LFBCLKSEL_LFB_HFCLKLE:
      ret = ((CMU->HFPRESC & _CMU_HFPRESC_HFCLKLEPRESC_MASK)
             == CMU_HFPRESC_HFCLKLEPRESC_DIV4)
            ? SystemCoreClockGet() / 4U
            : SystemCoreClockGet() / 2U;
      break;
#endif

    case _CMU_LFACLKSEL_LFA_DISABLED:
      ret = 0;
      break;
  }
#endif

  return ret;
}


#if defined( CMU_CTRL_HFLE )              \
    && !defined( _EFM32_WONDER_FAMILY )   \
    && !defined( _EZR32_LEOPARD_FAMILY )  \
    && !defined( _EZR32_WONDER_FAMILY )
/***************************************************************************//**
 * @brief
 *   Return max allowed frequency for low energy peripherals.
 ******************************************************************************/
static uint32_t maxFreqHfle(void)
{
  uint16_t majorMinorRev;

  switch (SYSTEM_GetFamily())
  {
    case systemPartFamilyEfm32Leopard:
      /* CHIP MAJOR bit [5:0] */
      majorMinorRev = (((ROMTABLE->PID0 & _ROMTABLE_PID0_REVMAJOR_MASK)
                        >> _ROMTABLE_PID0_REVMAJOR_SHIFT) << 8);
      /* CHIP MINOR bit [7:4] */
      majorMinorRev |= (((ROMTABLE->PID2 & _ROMTABLE_PID2_REVMINORMSB_MASK)
                         >> _ROMTABLE_PID2_REVMINORMSB_SHIFT) << 4);
      /* CHIP MINOR bit [3:0] */
      majorMinorRev |=  ((ROMTABLE->PID3 & _ROMTABLE_PID3_REVMINORLSB_MASK)
                         >> _ROMTABLE_PID3_REVMINORLSB_SHIFT);

      if (majorMinorRev >= 0x0204)
        return 24000000;
      else
        return 32000000;

    case systemPartFamilyEfm32Giant:
      return 32000000;

    default:
      /* Invalid device family. */
      EFM_ASSERT(false);
      return 0;
  }
}
#endif


/***************************************************************************//**
 * @brief
 *   Wait for ongoing sync of register(s) to low frequency domain to complete.
 *
 * @param[in] mask
 *   Bitmask corresponding to SYNCBUSY register defined bits, indicating
 *   registers that must complete any ongoing synchronization.
 ******************************************************************************/
__STATIC_INLINE void syncReg(uint32_t mask)
{
  /* Avoid deadlock if modifying the same register twice when freeze mode is */
  /* activated. */
  if (CMU->FREEZE & CMU_FREEZE_REGFREEZE)
    return;

  /* Wait for any pending previous write operation to have been completed */
  /* in low frequency domain */
  while (CMU->SYNCBUSY & mask)
  {
  }
}


#if defined(USB_PRESENT)
/***************************************************************************//**
 * @brief
 *   Get the USBC frequency
 *
 * @return
 *   USBC frequency in Hz
 ******************************************************************************/
static uint32_t usbCClkGet(void)
{
  uint32_t ret;
  CMU_Select_TypeDef clk;

  /* Get selected clock source */
  clk = CMU_ClockSelectGet(cmuClock_USBC);

  switch(clk)
  {
    case cmuSelect_LFXO:
      ret = SystemLFXOClockGet();
      break;
    case cmuSelect_LFRCO:
      ret = SystemLFRCOClockGet();
      break;
    case cmuSelect_HFCLK:
      ret = SystemHFClockGet();
      break;
    default:
      /* Clock is not enabled */
      ret = 0;
      break;
  }
  return ret;
}
#endif


/** @endcond */

/*******************************************************************************
 **************************   GLOBAL FUNCTIONS   *******************************
 ******************************************************************************/

#if defined( _CMU_AUXHFRCOCTRL_BAND_MASK )
/***************************************************************************//**
 * @brief
 *   Get AUXHFRCO band in use.
 *
 * @return
 *   AUXHFRCO band in use.
 ******************************************************************************/
CMU_AUXHFRCOBand_TypeDef CMU_AUXHFRCOBandGet(void)
{
  return (CMU_AUXHFRCOBand_TypeDef)((CMU->AUXHFRCOCTRL
                                     & _CMU_AUXHFRCOCTRL_BAND_MASK)
                                    >> _CMU_AUXHFRCOCTRL_BAND_SHIFT);
}
#endif /* _CMU_AUXHFRCOCTRL_BAND_MASK */


#if defined( _CMU_AUXHFRCOCTRL_BAND_MASK )
/***************************************************************************//**
 * @brief
 *   Set AUXHFRCO band and the tuning value based on the value in the
 *   calibration table made during production.
 *
 * @param[in] band
 *   AUXHFRCO band to activate.
 ******************************************************************************/
void CMU_AUXHFRCOBandSet(CMU_AUXHFRCOBand_TypeDef band)
{
  uint32_t tuning;

  /* Read tuning value from calibration table */
  switch (band)
  {
    case cmuAUXHFRCOBand_1MHz:
      tuning = (DEVINFO->AUXHFRCOCAL0 & _DEVINFO_AUXHFRCOCAL0_BAND1_MASK)
               >> _DEVINFO_AUXHFRCOCAL0_BAND1_SHIFT;
      break;

    case cmuAUXHFRCOBand_7MHz:
      tuning = (DEVINFO->AUXHFRCOCAL0 & _DEVINFO_AUXHFRCOCAL0_BAND7_MASK)
               >> _DEVINFO_AUXHFRCOCAL0_BAND7_SHIFT;
      break;

    case cmuAUXHFRCOBand_11MHz:
      tuning = (DEVINFO->AUXHFRCOCAL0 & _DEVINFO_AUXHFRCOCAL0_BAND11_MASK)
               >> _DEVINFO_AUXHFRCOCAL0_BAND11_SHIFT;
      break;

    case cmuAUXHFRCOBand_14MHz:
      tuning = (DEVINFO->AUXHFRCOCAL0 & _DEVINFO_AUXHFRCOCAL0_BAND14_MASK)
               >> _DEVINFO_AUXHFRCOCAL0_BAND14_SHIFT;
      break;

    case cmuAUXHFRCOBand_21MHz:
      tuning = (DEVINFO->AUXHFRCOCAL1 & _DEVINFO_AUXHFRCOCAL1_BAND21_MASK)
               >> _DEVINFO_AUXHFRCOCAL1_BAND21_SHIFT;
      break;

#if defined( _CMU_AUXHFRCOCTRL_BAND_28MHZ )
    case cmuAUXHFRCOBand_28MHz:
      tuning = (DEVINFO->AUXHFRCOCAL1 & _DEVINFO_AUXHFRCOCAL1_BAND28_MASK)
               >> _DEVINFO_AUXHFRCOCAL1_BAND28_SHIFT;
      break;
#endif

    default:
      EFM_ASSERT(0);
      return;
  }

  /* Set band/tuning */
  CMU->AUXHFRCOCTRL = (CMU->AUXHFRCOCTRL &
                       ~(_CMU_AUXHFRCOCTRL_BAND_MASK
                         | _CMU_AUXHFRCOCTRL_TUNING_MASK))
                      | (band << _CMU_AUXHFRCOCTRL_BAND_SHIFT)
                      | (tuning << _CMU_AUXHFRCOCTRL_TUNING_SHIFT);

}
#endif /* _CMU_AUXHFRCOCTRL_BAND_MASK */


#if defined( _CMU_AUXHFRCOCTRL_FREQRANGE_MASK )
/**************************************************************************//**
 * @brief
 *   Get a pointer to the AUXHFRCO frequency calibration word in DEVINFO
 *
 * @param[in] freq
 *   Frequency in Hz
 *
 * @return
 *   AUXHFRCO calibration word for a given frequency
 *****************************************************************************/
static uint32_t CMU_AUXHFRCODevinfoGet(CMU_AUXHFRCOFreq_TypeDef freq)
{
  switch (freq)
  {
  /* 1, 2 and 4MHz share the same calibration word */
    case cmuAUXHFRCOFreq_1M0Hz:
    case cmuAUXHFRCOFreq_2M0Hz:
    case cmuAUXHFRCOFreq_4M0Hz:
      return DEVINFO->AUXHFRCOCAL0;

    case cmuAUXHFRCOFreq_7M0Hz:
      return DEVINFO->AUXHFRCOCAL3;

    case cmuAUXHFRCOFreq_13M0Hz:
      return DEVINFO->AUXHFRCOCAL6;

    case cmuAUXHFRCOFreq_16M0Hz:
      return DEVINFO->AUXHFRCOCAL7;

    case cmuAUXHFRCOFreq_19M0Hz:
      return DEVINFO->AUXHFRCOCAL8;

    case cmuAUXHFRCOFreq_26M0Hz:
      return DEVINFO->AUXHFRCOCAL10;

    case cmuAUXHFRCOFreq_32M0Hz:
      return DEVINFO->AUXHFRCOCAL11;

    case cmuAUXHFRCOFreq_38M0Hz:
      return DEVINFO->AUXHFRCOCAL12;

    default: /* cmuAUXHFRCOFreq_UserDefined */
      return 0;
  }
}
#endif /* _CMU_AUXHFRCOCTRL_FREQRANGE_MASK */


#if defined( _CMU_AUXHFRCOCTRL_FREQRANGE_MASK )
/***************************************************************************//**
 * @brief
 *   Get AUXHFRCO frequency enumeration in use
 *
 * @return
 *   AUXHFRCO frequency enumeration in use
 ******************************************************************************/
CMU_AUXHFRCOFreq_TypeDef CMU_AUXHFRCOFreqGet(void)
{
  return auxHfrcoFreq;
}
#endif /* _CMU_AUXHFRCOCTRL_FREQRANGE_MASK */


#if defined( _CMU_AUXHFRCOCTRL_FREQRANGE_MASK )
/***************************************************************************//**
 * @brief
 *   Set AUXHFRCO calibration for the selected target frequency
 *
 * @param[in] frequency
 *   AUXHFRCO frequency to set
 ******************************************************************************/
void CMU_AUXHFRCOFreqSet(CMU_AUXHFRCOFreq_TypeDef freq)
{
  uint32_t freqCal;

  /* Get DEVINFO index, set global auxHfrcoFreq */
  freqCal = CMU_AUXHFRCODevinfoGet(freq);
  EFM_ASSERT((freqCal != 0) && (freqCal != UINT_MAX));
  auxHfrcoFreq = freq;

  /* Wait for any previous sync to complete, and then set calibration data
     for the selected frequency.  */
  while(BUS_RegBitRead(&CMU->SYNCBUSY, _CMU_SYNCBUSY_AUXHFRCOBSY_SHIFT));

  /* Set divider in AUXHFRCOCTRL for 1, 2 and 4MHz */
  switch(freq)
  {
    case cmuAUXHFRCOFreq_1M0Hz:
      freqCal = (freqCal & ~_CMU_AUXHFRCOCTRL_CLKDIV_MASK)
                | CMU_AUXHFRCOCTRL_CLKDIV_DIV4;
      break;

    case cmuAUXHFRCOFreq_2M0Hz:
      freqCal = (freqCal & ~_CMU_AUXHFRCOCTRL_CLKDIV_MASK)
                | CMU_AUXHFRCOCTRL_CLKDIV_DIV2;
      break;

    case cmuAUXHFRCOFreq_4M0Hz:
      freqCal = (freqCal & ~_CMU_AUXHFRCOCTRL_CLKDIV_MASK)
                | CMU_AUXHFRCOCTRL_CLKDIV_DIV1;
      break;

    default:
      break;
  }
  CMU->AUXHFRCOCTRL = freqCal;
}
#endif /* _CMU_AUXHFRCOCTRL_FREQRANGE_MASK */


/***************************************************************************//**
 * @brief
 *   Calibrate clock.
 *
 * @details
 *   Run a calibration for HFCLK against a selectable reference clock. Please
 *   refer to the reference manual, CMU chapter, for further details.
 *
 * @note
 *   This function will not return until calibration measurement is completed.
 *
 * @param[in] HFCycles
 *   The number of HFCLK cycles to run calibration. Increasing this number
 *   increases precision, but the calibration will take more time.
 *
 * @param[in] ref
 *   The reference clock used to compare HFCLK with.
 *
 * @return
 *   The number of ticks the reference clock after HFCycles ticks on the HF
 *   clock.
 ******************************************************************************/
uint32_t CMU_Calibrate(uint32_t HFCycles, CMU_Osc_TypeDef ref)
{
  EFM_ASSERT(HFCycles <= (_CMU_CALCNT_CALCNT_MASK >> _CMU_CALCNT_CALCNT_SHIFT));

  /* Set reference clock source */
  switch (ref)
  {
    case cmuOsc_LFXO:
      CMU->CALCTRL = CMU_CALCTRL_UPSEL_LFXO;
      break;

    case cmuOsc_LFRCO:
      CMU->CALCTRL = CMU_CALCTRL_UPSEL_LFRCO;
      break;

    case cmuOsc_HFXO:
      CMU->CALCTRL = CMU_CALCTRL_UPSEL_HFXO;
      break;

    case cmuOsc_HFRCO:
      CMU->CALCTRL = CMU_CALCTRL_UPSEL_HFRCO;
      break;

    case cmuOsc_AUXHFRCO:
      CMU->CALCTRL = CMU_CALCTRL_UPSEL_AUXHFRCO;
      break;

    default:
      EFM_ASSERT(0);
      return 0;
  }

  /* Set top value */
  CMU->CALCNT = HFCycles;

  /* Start calibration */
  CMU->CMD = CMU_CMD_CALSTART;

#if defined( CMU_STATUS_CALRDY )
  /* Wait until calibration completes */
  while (!BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_CALRDY_SHIFT))
  {
  }
#else
  /* Wait until calibration completes */
  while (BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_CALBSY_SHIFT))
  {
  }
#endif

  return CMU->CALCNT;
}


#if defined( _CMU_CALCTRL_UPSEL_MASK ) && defined( _CMU_CALCTRL_DOWNSEL_MASK )
/***************************************************************************//**
 * @brief
 *   Configure clock calibration
 *
 * @details
 *   Configure a calibration for a selectable clock source against another
 *   selectable reference clock.
 *   Refer to the reference manual, CMU chapter, for further details.
 *
 * @note
 *   After configuration, a call to CMU_CalibrateStart() is required, and
 *   the resulting calibration value can be read out with the
 *   CMU_CalibrateCountGet() function call.
 *
 * @param[in] downCycles
 *   The number of downSel clock cycles to run calibration. Increasing this
 *   number increases precision, but the calibration will take more time.
 *
 * @param[in] downSel
 *   The clock which will be counted down downCycles
 *
 * @param[in] upSel
 *   The reference clock, the number of cycles generated by this clock will
 *   be counted and added up, the result can be given with the
 *   CMU_CalibrateCountGet() function call.
 ******************************************************************************/
void CMU_CalibrateConfig(uint32_t downCycles, CMU_Osc_TypeDef downSel,
                         CMU_Osc_TypeDef upSel)
{
  /* Keep untouched configuration settings */
  uint32_t calCtrl = CMU->CALCTRL
                     & ~(_CMU_CALCTRL_UPSEL_MASK | _CMU_CALCTRL_DOWNSEL_MASK);

  /* 20 bits of precision to calibration count register */
  EFM_ASSERT(downCycles <= (_CMU_CALCNT_CALCNT_MASK >> _CMU_CALCNT_CALCNT_SHIFT));

  /* Set down counting clock source - down counter */
  switch (downSel)
  {
    case cmuOsc_LFXO:
      calCtrl |= CMU_CALCTRL_DOWNSEL_LFXO;
      break;

    case cmuOsc_LFRCO:
      calCtrl |= CMU_CALCTRL_DOWNSEL_LFRCO;
      break;

    case cmuOsc_HFXO:
      calCtrl |= CMU_CALCTRL_DOWNSEL_HFXO;
      break;

    case cmuOsc_HFRCO:
      calCtrl |= CMU_CALCTRL_DOWNSEL_HFRCO;
      break;

    case cmuOsc_AUXHFRCO:
      calCtrl |= CMU_CALCTRL_DOWNSEL_AUXHFRCO;
      break;

    default:
      EFM_ASSERT(0);
      break;
  }

  /* Set top value to be counted down by the downSel clock */
  CMU->CALCNT = downCycles;

  /* Set reference clock source - up counter */
  switch (upSel)
  {
    case cmuOsc_LFXO:
      calCtrl |= CMU_CALCTRL_UPSEL_LFXO;
      break;

    case cmuOsc_LFRCO:
      calCtrl |= CMU_CALCTRL_UPSEL_LFRCO;
      break;

    case cmuOsc_HFXO:
      calCtrl |= CMU_CALCTRL_UPSEL_HFXO;
      break;

    case cmuOsc_HFRCO:
      calCtrl |= CMU_CALCTRL_UPSEL_HFRCO;
      break;

    case cmuOsc_AUXHFRCO:
      calCtrl |= CMU_CALCTRL_UPSEL_AUXHFRCO;
      break;

    default:
      EFM_ASSERT(0);
      break;
  }

  CMU->CALCTRL = calCtrl;
}
#endif


/***************************************************************************//**
 * @brief
 *    Get calibration count register
 * @note
 *    If continuous calibrartion mode is active, calibration busy will almost
 *    always be off, and we just need to read the value, where the normal case
 *    would be that this function call has been triggered by the CALRDY
 *    interrupt flag.
 * @return
 *    Calibration count, the number of UPSEL clocks (see CMU_CalibrateConfig)
 *    in the period of DOWNSEL oscillator clock cycles configured by a previous
 *    write operation to CMU->CALCNT
 ******************************************************************************/
uint32_t CMU_CalibrateCountGet(void)
{
  /* Wait until calibration completes, UNLESS continuous calibration mode is  */
  /* active */
#if defined( CMU_CALCTRL_CONT )
  if (!BUS_RegBitRead(&CMU->CALCTRL, _CMU_CALCTRL_CONT_SHIFT))
  {
#if defined( CMU_STATUS_CALRDY )
    /* Wait until calibration completes */
    while (!BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_CALRDY_SHIFT))
    {
    }
#else
    /* Wait until calibration completes */
    while (BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_CALBSY_SHIFT))
    {
    }
#endif
  }
#else
  while (BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_CALBSY_SHIFT))
  {
  }
#endif
  return CMU->CALCNT;
}


/***************************************************************************//**
 * @brief
 *   Get clock divisor/prescaler.
 *
 * @param[in] clock
 *   Clock point to get divisor/prescaler for. Notice that not all clock points
 *   have a divisor/prescaler. Please refer to CMU overview in reference manual.
 *
 * @return
 *   The current clock point divisor/prescaler. 1 is returned
 *   if @p clock specifies a clock point without a divisor/prescaler.
 ******************************************************************************/
CMU_ClkDiv_TypeDef CMU_ClockDivGet(CMU_Clock_TypeDef clock)
{
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
  return 1 + (uint32_t)CMU_ClockPrescGet(clock);

#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
  uint32_t           divReg;
  CMU_ClkDiv_TypeDef ret;

  /* Get divisor reg id */
  divReg = (clock >> CMU_DIV_REG_POS) & CMU_DIV_REG_MASK;

  switch (divReg)
  {
#if defined( _CMU_CTRL_HFCLKDIV_MASK )
    case CMU_HFCLKDIV_REG:
      ret = 1 + ((CMU->CTRL & _CMU_CTRL_HFCLKDIV_MASK)
                 >> _CMU_CTRL_HFCLKDIV_SHIFT);
      break;
#endif

    case CMU_HFPERCLKDIV_REG:
      ret = (CMU_ClkDiv_TypeDef)((CMU->HFPERCLKDIV
                                  & _CMU_HFPERCLKDIV_HFPERCLKDIV_MASK)
                                 >> _CMU_HFPERCLKDIV_HFPERCLKDIV_SHIFT);
      ret = CMU_Log2ToDiv(ret);
      break;

    case CMU_HFCORECLKDIV_REG:
      ret = (CMU_ClkDiv_TypeDef)((CMU->HFCORECLKDIV
                                  & _CMU_HFCORECLKDIV_HFCORECLKDIV_MASK)
                                 >> _CMU_HFCORECLKDIV_HFCORECLKDIV_SHIFT);
      ret = CMU_Log2ToDiv(ret);
      break;

    case CMU_LFAPRESC0_REG:
      switch (clock)
      {
        case cmuClock_RTC:
          ret = (CMU_ClkDiv_TypeDef)((CMU->LFAPRESC0 & _CMU_LFAPRESC0_RTC_MASK)
                                     >> _CMU_LFAPRESC0_RTC_SHIFT);
          ret = CMU_Log2ToDiv(ret);
          break;

#if defined(_CMU_LFAPRESC0_LETIMER0_MASK)
        case cmuClock_LETIMER0:
          ret = (CMU_ClkDiv_TypeDef)((CMU->LFAPRESC0 & _CMU_LFAPRESC0_LETIMER0_MASK)
                                     >> _CMU_LFAPRESC0_LETIMER0_SHIFT);
          ret = CMU_Log2ToDiv(ret);
          break;
#endif

#if defined(_CMU_LFAPRESC0_LCD_MASK)
        case cmuClock_LCDpre:
          ret = (CMU_ClkDiv_TypeDef)(((CMU->LFAPRESC0 & _CMU_LFAPRESC0_LCD_MASK)
                                      >> _CMU_LFAPRESC0_LCD_SHIFT)
                                     + CMU_DivToLog2(cmuClkDiv_16));
          ret = CMU_Log2ToDiv(ret);
          break;
#endif

#if defined(_CMU_LFAPRESC0_LESENSE_MASK)
        case cmuClock_LESENSE:
          ret = (CMU_ClkDiv_TypeDef)((CMU->LFAPRESC0 & _CMU_LFAPRESC0_LESENSE_MASK)
                                     >> _CMU_LFAPRESC0_LESENSE_SHIFT);
          ret = CMU_Log2ToDiv(ret);
          break;
#endif

        default:
          EFM_ASSERT(0);
          ret = cmuClkDiv_1;
          break;
      }
      break;

    case CMU_LFBPRESC0_REG:
      switch (clock)
      {
#if defined(_CMU_LFBPRESC0_LEUART0_MASK)
        case cmuClock_LEUART0:
          ret = (CMU_ClkDiv_TypeDef)((CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART0_MASK)
                                     >> _CMU_LFBPRESC0_LEUART0_SHIFT);
          ret = CMU_Log2ToDiv(ret);
          break;
#endif

#if defined(_CMU_LFBPRESC0_LEUART1_MASK)
        case cmuClock_LEUART1:
          ret = (CMU_ClkDiv_TypeDef)((CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART1_MASK)
                                     >> _CMU_LFBPRESC0_LEUART1_SHIFT);
          ret = CMU_Log2ToDiv(ret);
          break;
#endif

        default:
          EFM_ASSERT(0);
          ret = cmuClkDiv_1;
          break;
      }
      break;

    default:
      EFM_ASSERT(0);
      ret = cmuClkDiv_1;
      break;
  }

  return ret;
#endif
}


/***************************************************************************//**
 * @brief
 *   Set clock divisor/prescaler.
 *
 * @note
 *   If setting a LF clock prescaler, synchronization into the low frequency
 *   domain is required. If the same register is modified before a previous
 *   update has completed, this function will stall until the previous
 *   synchronization has completed. Please refer to CMU_FreezeEnable() for
 *   a suggestion on how to reduce stalling time in some use cases.
 *
 * @param[in] clock
 *   Clock point to set divisor/prescaler for. Notice that not all clock points
 *   have a divisor/prescaler, please refer to CMU overview in the reference
 *   manual.
 *
 * @param[in] div
 *   The clock divisor to use (<= cmuClkDiv_512).
 ******************************************************************************/
void CMU_ClockDivSet(CMU_Clock_TypeDef clock, CMU_ClkDiv_TypeDef div)
{
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
  CMU_ClockPrescSet(clock, (CMU_ClkPresc_TypeDef)(div - 1));

#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
  uint32_t freq;
  uint32_t divReg;

  /* Get divisor reg id */
  divReg = (clock >> CMU_DIV_REG_POS) & CMU_DIV_REG_MASK;

  switch (divReg)
  {
#if defined( _CMU_CTRL_HFCLKDIV_MASK )
    case CMU_HFCLKDIV_REG:
      EFM_ASSERT((div>=cmuClkDiv_1) && (div<=cmuClkDiv_8));

      /* Configure worst case wait states for flash access before setting divisor */
      flashWaitStateMax();

      /* Set divider */
      CMU->CTRL = (CMU->CTRL & ~_CMU_CTRL_HFCLKDIV_MASK)
                  | ((div-1) << _CMU_CTRL_HFCLKDIV_SHIFT);

      /* Update CMSIS core clock variable */
      /* (The function will update the global variable) */
      freq = SystemCoreClockGet();

      /* Optimize flash access wait state setting for current core clk */
      flashWaitStateControl(freq);
      break;
#endif

    case CMU_HFPERCLKDIV_REG:
      EFM_ASSERT((div >= cmuClkDiv_1) && (div <= cmuClkDiv_512));
      /* Convert to correct scale */
      div = CMU_DivToLog2(div);
      CMU->HFPERCLKDIV = (CMU->HFPERCLKDIV & ~_CMU_HFPERCLKDIV_HFPERCLKDIV_MASK)
                         | (div << _CMU_HFPERCLKDIV_HFPERCLKDIV_SHIFT);
      break;

    case CMU_HFCORECLKDIV_REG:
      EFM_ASSERT(div <= cmuClkDiv_512);

      /* Configure worst case wait states for flash access before setting divisor */
      flashWaitStateMax();

#if defined( CMU_CTRL_HFLE )
      /* Clear HFLE and set DIV2 factor for peripheral clock
         when running at frequencies lower than or equal to CMU_MAX_FREQ_HFLE. */
      if ((CMU_ClockFreqGet(cmuClock_HF) / div) <= CMU_MAX_FREQ_HFLE())
      {
        /* Clear CMU HFLE */
        BUS_RegBitWrite(&CMU->CTRL, _CMU_CTRL_HFLE_SHIFT, 0);

        /* Set DIV2 factor for peripheral clock */
        BUS_RegBitWrite(&CMU->HFCORECLKDIV,
                        _CMU_HFCORECLKDIV_HFCORECLKLEDIV_SHIFT, 0);
      }
      else
      {
        /* Set CMU HFLE */
        BUS_RegBitWrite(&CMU->CTRL, _CMU_CTRL_HFLE_SHIFT, 1);

        /* Set DIV4 factor for peripheral clock */
        BUS_RegBitWrite(&CMU->HFCORECLKDIV,
                        _CMU_HFCORECLKDIV_HFCORECLKLEDIV_SHIFT, 1);
      }
#endif

      /* Convert to correct scale */
      div = CMU_DivToLog2(div);

      CMU->HFCORECLKDIV = (CMU->HFCORECLKDIV
                           & ~_CMU_HFCORECLKDIV_HFCORECLKDIV_MASK)
                          | (div << _CMU_HFCORECLKDIV_HFCORECLKDIV_SHIFT);

      /* Update CMSIS core clock variable */
      /* (The function will update the global variable) */
      freq = SystemCoreClockGet();

      /* Optimize flash access wait state setting for current core clk */
      flashWaitStateControl(freq);
      break;

    case CMU_LFAPRESC0_REG:
      switch (clock)
      {
        case cmuClock_RTC:
          EFM_ASSERT(div <= cmuClkDiv_32768);

          /* LF register about to be modified require sync. busy check */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          /* Convert to correct scale */
          div = CMU_DivToLog2(div);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_RTC_MASK)
                           | (div << _CMU_LFAPRESC0_RTC_SHIFT);
          break;

#if defined(_CMU_LFAPRESC0_LETIMER0_MASK)
        case cmuClock_LETIMER0:
          EFM_ASSERT(div <= cmuClkDiv_32768);

          /* LF register about to be modified require sync. busy check */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          /* Convert to correct scale */
          div = CMU_DivToLog2(div);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_LETIMER0_MASK)
                           | (div << _CMU_LFAPRESC0_LETIMER0_SHIFT);
          break;
#endif

#if defined(LCD_PRESENT)
        case cmuClock_LCDpre:
          EFM_ASSERT((div >= cmuClkDiv_16) && (div <= cmuClkDiv_128));

          /* LF register about to be modified require sync. busy check */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          /* Convert to correct scale */
          div = CMU_DivToLog2(div);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_LCD_MASK)
                           | ((div - CMU_DivToLog2(cmuClkDiv_16))
                              << _CMU_LFAPRESC0_LCD_SHIFT);
          break;
#endif /* defined(LCD_PRESENT) */

#if defined(LESENSE_PRESENT)
        case cmuClock_LESENSE:
          EFM_ASSERT(div <= cmuClkDiv_8);

          /* LF register about to be modified require sync. busy check */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          /* Convert to correct scale */
          div = CMU_DivToLog2(div);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_LESENSE_MASK)
                           | (div << _CMU_LFAPRESC0_LESENSE_SHIFT);
          break;
#endif /* defined(LESENSE_PRESENT) */

        default:
          EFM_ASSERT(0);
          break;
      }
      break;

    case CMU_LFBPRESC0_REG:
      switch (clock)
      {
#if defined(_CMU_LFBPRESC0_LEUART0_MASK)
        case cmuClock_LEUART0:
          EFM_ASSERT(div <= cmuClkDiv_8);

          /* LF register about to be modified require sync. busy check */
          syncReg(CMU_SYNCBUSY_LFBPRESC0);

          /* Convert to correct scale */
          div = CMU_DivToLog2(div);

          CMU->LFBPRESC0 = (CMU->LFBPRESC0 & ~_CMU_LFBPRESC0_LEUART0_MASK)
                           | (((uint32_t)div) << _CMU_LFBPRESC0_LEUART0_SHIFT);
          break;
#endif

#if defined(_CMU_LFBPRESC0_LEUART1_MASK)
        case cmuClock_LEUART1:
          EFM_ASSERT(div <= cmuClkDiv_8);

          /* LF register about to be modified require sync. busy check */
          syncReg(CMU_SYNCBUSY_LFBPRESC0);

          /* Convert to correct scale */
          div = CMU_DivToLog2(div);

          CMU->LFBPRESC0 = (CMU->LFBPRESC0 & ~_CMU_LFBPRESC0_LEUART1_MASK)
                           | (((uint32_t)div) << _CMU_LFBPRESC0_LEUART1_SHIFT);
          break;
#endif

        default:
          EFM_ASSERT(0);
          break;
      }
      break;

    default:
      EFM_ASSERT(0);
      break;
  }
#endif
}


/***************************************************************************//**
 * @brief
 *   Enable/disable a clock.
 *
 * @details
 *   In general, module clocking is disabled after a reset. If a module
 *   clock is disabled, the registers of that module are not accessible and
 *   reading from such registers may return undefined values. Writing to
 *   registers of clock disabled modules have no effect. One should normally
 *   avoid accessing module registers of a module with a disabled clock.
 *
 * @note
 *   If enabling/disabling a LF clock, synchronization into the low frequency
 *   domain is required. If the same register is modified before a previous
 *   update has completed, this function will stall until the previous
 *   synchronization has completed. Please refer to CMU_FreezeEnable() for
 *   a suggestion on how to reduce stalling time in some use cases.
 *
 * @param[in] clock
 *   The clock to enable/disable. Notice that not all defined clock
 *   points have separate enable/disable control, please refer to CMU overview
 *   in reference manual.
 *
 * @param[in] enable
 *   @li true - enable specified clock.
 *   @li false - disable specified clock.
 ******************************************************************************/
void CMU_ClockEnable(CMU_Clock_TypeDef clock, bool enable)
{
  volatile uint32_t *reg;
  uint32_t          bit;
  uint32_t          sync = 0;

  /* Identify enable register */
  switch ((clock >> CMU_EN_REG_POS) & CMU_EN_REG_MASK)
  {
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
    case CMU_CTRL_EN_REG:
      reg = &CMU->CTRL;
      break;
#endif

#if defined( _SILICON_LABS_32B_PLATFORM_1 )
    case CMU_HFCORECLKEN0_EN_REG:
      reg = &CMU->HFCORECLKEN0;
#if defined( CMU_CTRL_HFLE )
      /* Set HFLE and DIV4 factor for peripheral clock when
         running at frequencies higher than or equal to CMU_MAX_FREQ_HFLE. */
      if ( CMU_ClockFreqGet(cmuClock_CORE) > CMU_MAX_FREQ_HFLE())
      {
        /* Enable CMU HFLE */
        BUS_RegBitWrite(&CMU->CTRL, _CMU_CTRL_HFLE_SHIFT, 1);

        /* Set DIV4 factor for peripheral clock */
        BUS_RegBitWrite(&CMU->HFCORECLKDIV,
                        _CMU_HFCORECLKDIV_HFCORECLKLEDIV_SHIFT, 1);
      }
#endif
      break;
#endif

#if defined( _CMU_HFBUSCLKEN0_MASK )
    case CMU_HFBUSCLKEN0_EN_REG:
      reg = &CMU->HFBUSCLKEN0;
      break;
#endif

#if defined( _CMU_HFRADIOCLKEN0_MASK )
    case CMU_HFRADIOCLKEN0_EN_REG:
      reg = &CMU->HFRADIOCLKEN0;
      break;
#endif

#if defined( _CMU_HFPERCLKDIV_MASK )
    case CMU_HFPERCLKDIV_EN_REG:
      reg = &CMU->HFPERCLKDIV;
      break;
#endif

    case CMU_HFPERCLKEN0_EN_REG:
      reg = &CMU->HFPERCLKEN0;
      break;

    case CMU_LFACLKEN0_EN_REG:
      reg  = &CMU->LFACLKEN0;
      sync = CMU_SYNCBUSY_LFACLKEN0;
      break;

    case CMU_LFBCLKEN0_EN_REG:
      reg  = &CMU->LFBCLKEN0;
      sync = CMU_SYNCBUSY_LFBCLKEN0;
      break;

#if defined( _CMU_LFCCLKEN0_MASK )
    case CMU_LFCCLKEN0_EN_REG:
      reg = &CMU->LFCCLKEN0;
      sync = CMU_SYNCBUSY_LFCCLKEN0;
      break;
#endif

#if defined( _CMU_LFECLKEN0_MASK )
    case CMU_LFECLKEN0_EN_REG:
      reg  = &CMU->LFECLKEN0;
      sync = CMU_SYNCBUSY_LFECLKEN0;
      break;
#endif

    case CMU_PCNT_EN_REG:
      reg = &CMU->PCNTCTRL;
      break;

    default: /* Cannot enable/disable clock point */
      EFM_ASSERT(0);
      return;
  }

  /* Get bit position used to enable/disable */
  bit = (clock >> CMU_EN_BIT_POS) & CMU_EN_BIT_MASK;

  /* LF synchronization required? */
  if (sync)
  {
    syncReg(sync);
  }

  /* Set/clear bit as requested */
  BUS_RegBitWrite(reg, bit, enable);
}


/***************************************************************************//**
 * @brief
 *   Get clock frequency for a clock point.
 *
 * @param[in] clock
 *   Clock point to fetch frequency for.
 *
 * @return
 *   The current frequency in Hz.
 ******************************************************************************/
uint32_t CMU_ClockFreqGet(CMU_Clock_TypeDef clock)
{
  uint32_t ret;

  switch(clock & (CMU_CLK_BRANCH_MASK << CMU_CLK_BRANCH_POS))
  {
    case (CMU_HF_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = SystemHFClockGet();
#if defined( _CMU_CTRL_HFCLKDIV_MASK )
      /* Family with an additional divider. */
      ret = ret / (1U + ((CMU->CTRL & _CMU_CTRL_HFCLKDIV_MASK)
                         >> _CMU_CTRL_HFCLKDIV_SHIFT));
#endif
#if defined( _CMU_HFPRESC_MASK )
      ret = ret / (1U + ((CMU->HFPRESC & _CMU_HFPRESC_PRESC_MASK)
                         >> _CMU_HFPRESC_PRESC_SHIFT));
#endif
      break;

    case (CMU_HFPER_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = SystemHFClockGet();
#if defined( _SILICON_LABS_32B_PLATFORM_1 )
#if defined( _CMU_CTRL_HFCLKDIV_MASK )
      /* Family with an additional divider. */
      ret = ret / (1U + ((CMU->CTRL & _CMU_CTRL_HFCLKDIV_MASK)
                         >> _CMU_CTRL_HFCLKDIV_SHIFT));
#endif
      ret >>= (CMU->HFPERCLKDIV & _CMU_HFPERCLKDIV_HFPERCLKDIV_MASK)
              >> _CMU_HFPERCLKDIV_HFPERCLKDIV_SHIFT;
#elif defined( _SILICON_LABS_32B_PLATFORM_2 )
      ret /= 1U + ((CMU->HFPERPRESC & _CMU_HFPERPRESC_PRESC_MASK)
                   >> _CMU_HFPERPRESC_PRESC_SHIFT);
#endif
      break;

#if defined( _SILICON_LABS_32B_PLATFORM_2 )
#if defined( _CMU_HFRADIOPRESC_PRESC_MASK )
    case (CMU_HFRADIO_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = SystemHFClockGet();
      ret /= 1U + ((CMU->HFRADIOPRESC & _CMU_HFRADIOPRESC_PRESC_MASK)
                   >> _CMU_HFRADIOPRESC_PRESC_SHIFT);
      break;
#endif

#if defined( CRYPTO_PRESENT )   \
    || defined( LDMA_PRESENT )  \
    || defined( GPCRC_PRESENT ) \
    || defined( PRS_PRESENT )   \
    || defined( GPIO_PRESENT )
    case (CMU_HFBUS_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = SystemHFClockGet();
      break;
#endif

    case (CMU_HFCORE_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = SystemHFClockGet();
      ret /= 1U + ((CMU->HFCOREPRESC & _CMU_HFCOREPRESC_PRESC_MASK)
                   >> _CMU_HFCOREPRESC_PRESC_SHIFT);
      break;

    case (CMU_HFEXP_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = SystemHFClockGet();
      ret /= 1U + ((CMU->HFEXPPRESC & _CMU_HFEXPPRESC_PRESC_MASK)
                   >> _CMU_HFEXPPRESC_PRESC_SHIFT);
      break;
#endif

#if defined( _SILICON_LABS_32B_PLATFORM_1 )
#if defined(AES_PRESENT)    \
    || defined(DMA_PRESENT) \
    || defined(EBI_PRESENT) \
    || defined(USB_PRESENT)
    case (CMU_HFCORE_CLK_BRANCH << CMU_CLK_BRANCH_POS):
    {
      ret = SystemCoreClockGet();
    } break;
#endif
#endif

    case (CMU_LFA_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFA);
      break;

#if defined( _CMU_LFACLKEN0_RTC_MASK )
    case (CMU_RTC_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFA);
      ret >>= (CMU->LFAPRESC0 & _CMU_LFAPRESC0_RTC_MASK)
              >> _CMU_LFAPRESC0_RTC_SHIFT;
      break;
#endif

#if defined( _CMU_LFECLKEN0_RTCC_MASK )
    case (CMU_RTCC_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFE);
      break;
#endif

#if defined( _CMU_LFACLKEN0_LETIMER0_MASK )
    case (CMU_LETIMER0_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFA);
#if defined( _SILICON_LABS_32B_PLATFORM_1 )
      ret >>= (CMU->LFAPRESC0 & _CMU_LFAPRESC0_LETIMER0_MASK)
              >> _CMU_LFAPRESC0_LETIMER0_SHIFT;
#elif defined( _SILICON_LABS_32B_PLATFORM_2 )
      ret /= CMU_Log2ToDiv((CMU->LFAPRESC0 & _CMU_LFAPRESC0_LETIMER0_MASK)
                           >> _CMU_LFAPRESC0_LETIMER0_SHIFT);
#endif
      break;
#endif

#if defined(_CMU_LFACLKEN0_LCD_MASK)
    case (CMU_LCDPRE_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFA);
      ret >>= ((CMU->LFAPRESC0 & _CMU_LFAPRESC0_LCD_MASK)
               >> _CMU_LFAPRESC0_LCD_SHIFT)
              + CMU_DivToLog2(cmuClkDiv_16);
      break;

    case (CMU_LCD_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFA);
      ret >>= (CMU->LFAPRESC0 & _CMU_LFAPRESC0_LCD_MASK)
              >> _CMU_LFAPRESC0_LCD_SHIFT;
      ret /= 1U + ((CMU->LCDCTRL & _CMU_LCDCTRL_FDIV_MASK)
                   >> _CMU_LCDCTRL_FDIV_SHIFT);
      break;
#endif

#if defined(_CMU_LFACLKEN0_LESENSE_MASK)
    case (CMU_LESENSE_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFA);
      ret >>= (CMU->LFAPRESC0 & _CMU_LFAPRESC0_LESENSE_MASK)
              >> _CMU_LFAPRESC0_LESENSE_SHIFT;
      break;
#endif

    case (CMU_LFB_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFB);
      break;

#if defined( _CMU_LFBCLKEN0_LEUART0_MASK )
    case (CMU_LEUART0_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFB);
#if defined( _SILICON_LABS_32B_PLATFORM_1 )
      ret >>= (CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART0_MASK)
              >> _CMU_LFBPRESC0_LEUART0_SHIFT;
#elif defined( _SILICON_LABS_32B_PLATFORM_2 )
      ret /= CMU_Log2ToDiv((CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART0_MASK)
                           >> _CMU_LFBPRESC0_LEUART0_SHIFT);
#endif
      break;
#endif

#if defined( _CMU_LFBCLKEN0_LEUART1_MASK )
    case (CMU_LEUART1_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFB);
#if defined( _SILICON_LABS_32B_PLATFORM_1 )
      ret >>= (CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART1_MASK)
              >> _CMU_LFBPRESC0_LEUART1_SHIFT;
#elif defined( _SILICON_LABS_32B_PLATFORM_2 )
      ret /= CMU_Log2ToDiv((CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART1_MASK)
                           >> _CMU_LFBPRESC0_LEUART1_SHIFT);
#endif
      break;
#endif

#if defined( _SILICON_LABS_32B_PLATFORM_2 )
    case (CMU_LFE_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = lfClkGet(cmuClock_LFE);
      break;
#endif

    case (CMU_DBG_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = dbgClkGet();
      break;

    case (CMU_AUX_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = auxClkGet();
      break;

#if defined(USB_PRESENT)
    case (CMU_USBC_CLK_BRANCH << CMU_CLK_BRANCH_POS):
      ret = usbCClkGet();
      break;
#endif

    default:
      EFM_ASSERT(0);
      ret = 0;
      break;
  }

  return ret;
}


#if defined( _SILICON_LABS_32B_PLATFORM_2 )
/***************************************************************************//**
 * @brief
 *   Get clock prescaler.
 *
 * @param[in] clock
 *   Clock point to get the prescaler for. Notice that not all clock points
 *   have a prescaler. Please refer to CMU overview in reference manual.
 *
 * @return
 *   The prescaler value of the current clock point. 0 is returned
 *   if @p clock specifies a clock point without a prescaler.
 ******************************************************************************/
uint32_t CMU_ClockPrescGet(CMU_Clock_TypeDef clock)
{
  uint32_t  prescReg;
  uint32_t  ret;

  /* Get prescaler register id. */
  prescReg = (clock >> CMU_PRESC_REG_POS) & CMU_PRESC_REG_MASK;

  switch (prescReg)
  {
    case CMU_HFPRESC_REG:
      ret = ((CMU->HFPRESC & _CMU_HFPRESC_PRESC_MASK)
             >> _CMU_HFPRESC_PRESC_SHIFT);
      break;

    case CMU_HFEXPPRESC_REG:
      ret = ((CMU->HFEXPPRESC & _CMU_HFEXPPRESC_PRESC_MASK)
             >> _CMU_HFEXPPRESC_PRESC_SHIFT);
      break;

    case CMU_HFCLKLEPRESC_REG:
      ret = ((CMU->HFPRESC & _CMU_HFPRESC_HFCLKLEPRESC_MASK)
             >> _CMU_HFPRESC_HFCLKLEPRESC_SHIFT);
      break;

    case CMU_HFPERPRESC_REG:
      ret = ((CMU->HFPERPRESC & _CMU_HFPERPRESC_PRESC_MASK)
             >> _CMU_HFPERPRESC_PRESC_SHIFT);
      break;

#if defined( _CMU_HFRADIOPRESC_PRESC_MASK )
    case CMU_HFRADIOPRESC_REG:
      ret = ((CMU->HFRADIOPRESC & _CMU_HFRADIOPRESC_PRESC_MASK)
             >> _CMU_HFRADIOPRESC_PRESC_SHIFT);
      break;
#endif

    case CMU_HFCOREPRESC_REG:
      ret = ((CMU->HFCOREPRESC & _CMU_HFCOREPRESC_PRESC_MASK)
             >> _CMU_HFCOREPRESC_PRESC_SHIFT);
      break;

    case CMU_LFAPRESC0_REG:
      switch (clock)
      {
#if defined( _CMU_LFAPRESC0_LETIMER0_MASK )
        case cmuClock_LETIMER0:
          ret = (((CMU->LFAPRESC0 & _CMU_LFAPRESC0_LETIMER0_MASK)
                 >> _CMU_LFAPRESC0_LETIMER0_SHIFT));
          /* Convert the exponent to prescaler value. */
          ret = CMU_Log2ToDiv(ret) - 1U;
          break;
#endif

        default:
          EFM_ASSERT(0);
          ret = 0U;
          break;
      }
      break;

    case CMU_LFBPRESC0_REG:
      switch (clock)
      {
#if defined( _CMU_LFBPRESC0_LEUART0_MASK )
        case cmuClock_LEUART0:
          ret = (((CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART0_MASK)
                 >> _CMU_LFBPRESC0_LEUART0_SHIFT));
          /* Convert the exponent to prescaler value. */
          ret = CMU_Log2ToDiv(ret) - 1U;
          break;
#endif

#if defined( _CMU_LFBPRESC0_LEUART1_MASK )
        case cmuClock_LEUART1:
          ret = (((CMU->LFBPRESC0 & _CMU_LFBPRESC0_LEUART1_MASK)
                 >> _CMU_LFBPRESC0_LEUART1_SHIFT));
          /* Convert the exponent to prescaler value. */
          ret = CMU_Log2ToDiv(ret) - 1U;
          break;
#endif

        default:
          EFM_ASSERT(0);
          ret = 0U;
          break;
      }
      break;

    case CMU_LFEPRESC0_REG:
      switch (clock)
      {
#if defined( RTCC_PRESENT )
        case cmuClock_RTCC:
          /* No need to compute with LFEPRESC0_RTCC - DIV1 is the only  */
          /* allowed value. Convert the exponent to prescaler value.    */
          ret = _CMU_LFEPRESC0_RTCC_DIV1;
          break;

        default:
          EFM_ASSERT(0);
          ret = 0U;
          break;
#endif
      }
      break;

    default:
      EFM_ASSERT(0);
      ret = 0U;
      break;
  }

  return ret;
}
#endif


#if defined( _SILICON_LABS_32B_PLATFORM_2 )
/***************************************************************************//**
 * @brief
 *   Set clock prescaler.
 *
 * @note
 *   If setting a LF clock prescaler, synchronization into the low frequency
 *   domain is required. If the same register is modified before a previous
 *   update has completed, this function will stall until the previous
 *   synchronization has completed. Please refer to CMU_FreezeEnable() for
 *   a suggestion on how to reduce stalling time in some use cases.
 *
 * @param[in] clock
 *   Clock point to set prescaler for. Notice that not all clock points
 *   have a prescaler, please refer to CMU overview in the reference manual.
 *
 * @param[in] presc
 *   The clock prescaler to use.
 ******************************************************************************/
void CMU_ClockPrescSet(CMU_Clock_TypeDef clock, CMU_ClkPresc_TypeDef presc)
{
  uint32_t freq;
  uint32_t prescReg;

  /* Get divisor reg id */
  prescReg = (clock >> CMU_PRESC_REG_POS) & CMU_PRESC_REG_MASK;

  switch (prescReg)
  {
    case CMU_HFPRESC_REG:
      EFM_ASSERT(presc < 32U);

      CMU->HFPRESC = (CMU->HFPRESC & ~_CMU_HFPRESC_PRESC_MASK)
                     | (presc << _CMU_HFPRESC_PRESC_SHIFT);
      break;

    case CMU_HFEXPPRESC_REG:
      EFM_ASSERT(presc < 32U);

      CMU->HFEXPPRESC = (CMU->HFEXPPRESC & ~_CMU_HFEXPPRESC_PRESC_MASK)
                        | (presc << _CMU_HFEXPPRESC_PRESC_SHIFT);
      break;

    case CMU_HFCLKLEPRESC_REG:
      EFM_ASSERT(presc < 2U);

      /* Specifies the clock divider for HFCLKLE. When running at frequencies
       * higher than 32 MHz, this must be set to DIV4. */
      CMU->HFPRESC = (CMU->HFPRESC & ~_CMU_HFPRESC_HFCLKLEPRESC_MASK)
                     | (presc << _CMU_HFPRESC_HFCLKLEPRESC_SHIFT);
      break;

    case CMU_HFPERPRESC_REG:
      EFM_ASSERT(presc < 512U);

      CMU->HFPERPRESC = (CMU->HFPERPRESC & ~_CMU_HFPERPRESC_PRESC_MASK)
                        | (presc << _CMU_HFPERPRESC_PRESC_SHIFT);
      break;

#if defined( _CMU_HFRADIOPRESC_PRESC_MASK )
    case CMU_HFRADIOPRESC_REG:
      EFM_ASSERT(presc < 512U);

      CMU->HFRADIOPRESC = (CMU->HFRADIOPRESC & ~_CMU_HFRADIOPRESC_PRESC_MASK)
                          | (presc << _CMU_HFRADIOPRESC_PRESC_SHIFT);
      break;
#endif

    case CMU_HFCOREPRESC_REG:
      EFM_ASSERT(presc < 512U);

      /* Configure worst case wait states for flash access before setting
       * the prescaler. */
      flashWaitStateControl(CMU_MAX_FREQ_0WS + 1);

      CMU->HFCOREPRESC = (CMU->HFCOREPRESC & ~_CMU_HFCOREPRESC_PRESC_MASK)
                         | (presc << _CMU_HFCOREPRESC_PRESC_SHIFT);

      /* Update CMSIS core clock variable */
      /* (The function will update the global variable) */
      freq = SystemCoreClockGet();

      /* Optimize flash access wait state setting for current core clk */
      flashWaitStateControl(freq);
      break;

    case CMU_LFAPRESC0_REG:
      switch (clock)
      {
#if defined( RTC_PRESENT )
        case cmuClock_RTC:
          EFM_ASSERT(presc <= 32768U);

          /* Convert prescaler value to DIV exponent scale. */
          presc = CMU_PrescToLog2(presc);

          /* LF register about to be modified require sync. Busy check. */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_RTC_MASK)
                           | (presc << _CMU_LFAPRESC0_RTC_SHIFT);
          break;
#endif

#if defined( RTCC_PRESENT )
        case cmuClock_RTCC:
#if defined( _CMU_LFEPRESC0_RTCC_MASK )
          /* DIV1 is the only accepted value. */
          EFM_ASSERT(presc <= 0U);

          /* LF register about to be modified require sync. Busy check.. */
          syncReg(CMU_SYNCBUSY_LFEPRESC0);

          CMU->LFEPRESC0 = (CMU->LFEPRESC0 & ~_CMU_LFEPRESC0_RTCC_MASK)
                           | (presc << _CMU_LFEPRESC0_RTCC_SHIFT);
#else
          EFM_ASSERT(presc <= 32768U);

          /* Convert prescaler value to DIV exponent scale. */
          presc = CMU_PrescToLog2(presc);

          /* LF register about to be modified require sync. Busy check. */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_RTCC_MASK)
                           | (presc << _CMU_LFAPRESC0_RTCC_SHIFT);
#endif
          break;
#endif

#if defined( _CMU_LFAPRESC0_LETIMER0_MASK )
        case cmuClock_LETIMER0:
          EFM_ASSERT(presc <= 32768U);

          /* Convert prescaler value to DIV exponent scale. */
          presc = CMU_PrescToLog2(presc);

          /* LF register about to be modified require sync. Busy check. */
          syncReg(CMU_SYNCBUSY_LFAPRESC0);

          CMU->LFAPRESC0 = (CMU->LFAPRESC0 & ~_CMU_LFAPRESC0_LETIMER0_MASK)
                           | (presc << _CMU_LFAPRESC0_LETIMER0_SHIFT);
          break;
#endif

        default:
          EFM_ASSERT(0);
          break;
      }
      break;

    case CMU_LFBPRESC0_REG:
      switch (clock)
      {
#if defined( _CMU_LFBPRESC0_LEUART0_MASK )
        case cmuClock_LEUART0:
          EFM_ASSERT(presc <= 8U);

          /* Convert prescaler value to DIV exponent scale. */
          presc = CMU_PrescToLog2(presc);

          /* LF register about to be modified require sync. Busy check. */
          syncReg(CMU_SYNCBUSY_LFBPRESC0);

          CMU->LFBPRESC0 = (CMU->LFBPRESC0 & ~_CMU_LFBPRESC0_LEUART0_MASK)
                           | (presc << _CMU_LFBPRESC0_LEUART0_SHIFT);
          break;
#endif

#if defined( _CMU_LFBPRESC0_LEUART1_MASK )
        case cmuClock_LEUART1:
          EFM_ASSERT(presc <= 8U);

          /* Convert prescaler value to DIV exponent scale. */
          presc = CMU_PrescToLog2(presc);

          /* LF register about to be modified require sync. Busy check. */
          syncReg(CMU_SYNCBUSY_LFBPRESC0);

          CMU->LFBPRESC0 = (CMU->LFBPRESC0 & ~_CMU_LFBPRESC0_LEUART1_MASK)
                           | (presc << _CMU_LFBPRESC0_LEUART1_SHIFT);
          break;
#endif

        default:
          EFM_ASSERT(0);
          break;
      }
      break;

    case CMU_LFEPRESC0_REG:
      switch (clock)
      {
#if defined( _CMU_LFEPRESC0_RTCC_MASK )
        case cmuClock_RTCC:
          EFM_ASSERT(presc <= 0U);

          /* LF register about to be modified require sync. Busy check. */
          syncReg(CMU_SYNCBUSY_LFEPRESC0);

          CMU->LFEPRESC0 = (CMU->LFEPRESC0 & ~_CMU_LFEPRESC0_RTCC_MASK)
                           | (presc << _CMU_LFEPRESC0_RTCC_SHIFT);
          break;
#endif

        default:
          EFM_ASSERT(0);
          break;
      }
      break;

    default:
      EFM_ASSERT(0);
      break;
  }
}
#endif


/***************************************************************************//**
 * @brief
 *   Get currently selected reference clock used for a clock branch.
 *
 * @param[in] clock
 *   Clock branch to fetch selected ref. clock for. One of:
 *   @li #cmuClock_HF
 *   @li #cmuClock_LFA
 *   @li #cmuClock_LFB @if _CMU_LFCLKSEL_LFAE_ULFRCO
 *   @li #cmuClock_LFC
 *   @endif            @if _SILICON_LABS_32B_PLATFORM_2
 *   @li #cmuClock_LFE
 *   @endif
 *   @li #cmuClock_DBG @if DOXYDOC_USB_PRESENT
 *   @li #cmuClock_USBC
 *   @endif
 *
 * @return
 *   Reference clock used for clocking selected branch, #cmuSelect_Error if
 *   invalid @p clock provided.
 ******************************************************************************/
CMU_Select_TypeDef CMU_ClockSelectGet(CMU_Clock_TypeDef clock)
{
  CMU_Select_TypeDef ret = cmuSelect_Disabled;
  uint32_t selReg;

  selReg = (clock >> CMU_SEL_REG_POS) & CMU_SEL_REG_MASK;

  switch (selReg)
  {
    case CMU_HFCLKSEL_REG:
#if defined( _CMU_HFCLKSEL_HF_MASK )
      switch (CMU->HFCLKSEL & _CMU_HFCLKSEL_HF_MASK)
      {
        case CMU_HFCLKSEL_HF_LFXO:
          ret = cmuSelect_LFXO;
          break;

        case CMU_HFCLKSEL_HF_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_HFCLKSEL_HF_HFXO:
          ret = cmuSelect_HFXO;
          break;

        default:
          ret = cmuSelect_HFRCO;
          break;
      }
#else
      switch (CMU->STATUS
              & (CMU_STATUS_HFRCOSEL
                 | CMU_STATUS_HFXOSEL
                 | CMU_STATUS_LFRCOSEL
#if defined( CMU_STATUS_USHFRCODIV2SEL )
                 | CMU_STATUS_USHFRCODIV2SEL
#endif
                 | CMU_STATUS_LFXOSEL))
      {
        case CMU_STATUS_LFXOSEL:
          ret = cmuSelect_LFXO;
          break;

        case CMU_STATUS_LFRCOSEL:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_STATUS_HFXOSEL:
          ret = cmuSelect_HFXO;
          break;

#if defined( CMU_STATUS_USHFRCODIV2SEL )
        case CMU_STATUS_USHFRCODIV2SEL:
          ret = cmuSelect_USHFRCODIV2;
          break;
#endif

        default:
          ret = cmuSelect_HFRCO;
          break;
      }
#endif
      break;

    case CMU_LFACLKSEL_REG:
#if defined( _CMU_LFCLKSEL_MASK )
      switch (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFA_MASK)
      {
        case CMU_LFCLKSEL_LFA_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_LFCLKSEL_LFA_LFXO:
          ret = cmuSelect_LFXO;
          break;

#if defined( CMU_LFCLKSEL_LFA_HFCORECLKLEDIV2 )
        case CMU_LFCLKSEL_LFA_HFCORECLKLEDIV2:
          ret = cmuSelect_CORELEDIV2;
          break;
#endif

        default:
#if defined( CMU_LFCLKSEL_LFAE )
          if (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFAE_MASK)
          {
            ret = cmuSelect_ULFRCO;
            break;
          }
#else
          ret = cmuSelect_Disabled;
#endif
          break;
      }
#endif /* _CMU_LFCLKSEL_MASK */

#if defined( _CMU_LFACLKSEL_MASK )
      switch (CMU->LFACLKSEL & _CMU_LFACLKSEL_LFA_MASK)
      {
        case CMU_LFACLKSEL_LFA_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_LFACLKSEL_LFA_LFXO:
          ret = cmuSelect_LFXO;
          break;

        case CMU_LFACLKSEL_LFA_ULFRCO:
          ret = cmuSelect_ULFRCO;
          break;

#if defined( _CMU_LFACLKSEL_LFA_HFCLKLE )
        case CMU_LFACLKSEL_LFA_HFCLKLE:
          ret = cmuSelect_HFCLKLE;
          break;
#endif

        default:
          ret = cmuSelect_Disabled;
          break;
      }
#endif
      break;

    case CMU_LFBCLKSEL_REG:
#if defined( _CMU_LFCLKSEL_MASK )
      switch (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFB_MASK)
      {
        case CMU_LFCLKSEL_LFB_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_LFCLKSEL_LFB_LFXO:
          ret = cmuSelect_LFXO;
          break;

#if defined( CMU_LFCLKSEL_LFB_HFCORECLKLEDIV2 )
        case CMU_LFCLKSEL_LFB_HFCORECLKLEDIV2:
          ret = cmuSelect_CORELEDIV2;
          break;
#endif

#if defined( CMU_LFCLKSEL_LFB_HFCLKLE )
        case CMU_LFCLKSEL_LFB_HFCLKLE:
          ret = cmuSelect_HFCLKLE;
          break;
#endif

        default:
#if defined( CMU_LFCLKSEL_LFBE )
          if (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFBE_MASK)
          {
            ret = cmuSelect_ULFRCO;
            break;
          }
#else
          ret = cmuSelect_Disabled;
#endif
          break;
      }
#endif /* _CMU_LFCLKSEL_MASK */

#if defined( _CMU_LFBCLKSEL_MASK )
      switch (CMU->LFBCLKSEL & _CMU_LFBCLKSEL_LFB_MASK)
      {
        case CMU_LFBCLKSEL_LFB_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_LFBCLKSEL_LFB_LFXO:
          ret = cmuSelect_LFXO;
          break;

        case CMU_LFBCLKSEL_LFB_ULFRCO:
          ret = cmuSelect_ULFRCO;
          break;

        case CMU_LFBCLKSEL_LFB_HFCLKLE:
          ret = cmuSelect_HFCLKLE;
          break;

        default:
          ret = cmuSelect_Disabled;
          break;
      }
#endif
      break;

#if defined( _CMU_LFCLKSEL_LFC_MASK )
    case CMU_LFCCLKSEL_REG:
      switch (CMU->LFCLKSEL & _CMU_LFCLKSEL_LFC_MASK)
      {
        case CMU_LFCLKSEL_LFC_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_LFCLKSEL_LFC_LFXO:
          ret = cmuSelect_LFXO;
          break;

        default:
          ret = cmuSelect_Disabled;
          break;
      }
      break;
#endif

#if defined( _CMU_LFECLKSEL_LFE_MASK )
    case CMU_LFECLKSEL_REG:
      switch (CMU->LFECLKSEL & _CMU_LFECLKSEL_LFE_MASK)
      {
        case CMU_LFECLKSEL_LFE_LFRCO:
          ret = cmuSelect_LFRCO;
          break;

        case CMU_LFECLKSEL_LFE_LFXO:
          ret = cmuSelect_LFXO;
          break;

        case CMU_LFECLKSEL_LFE_ULFRCO:
          ret = cmuSelect_ULFRCO;
          break;

#if defined ( _CMU_LFECLKSEL_LFE_HFCLKLE )
        case CMU_LFECLKSEL_LFE_HFCLKLE:
          ret = cmuSelect_HFCLKLE;
          break;
#endif

        default:
          ret = cmuSelect_Disabled;
          break;
      }
      break;
#endif /* CMU_LFECLKSEL_REG */

    case CMU_DBGCLKSEL_REG:
#if defined( _CMU_DBGCLKSEL_DBG_MASK )
      switch (CMU->DBGCLKSEL & _CMU_DBGCLKSEL_DBG_MASK)
      {
        case CMU_DBGCLKSEL_DBG_HFCLK:
          ret = cmuSelect_HFCLK;
          break;

        case CMU_DBGCLKSEL_DBG_AUXHFRCO:
          ret = cmuSelect_AUXHFRCO;
          break;
      }
#else
      ret = cmuSelect_AUXHFRCO;
#endif /* CMU_DBGCLKSEL_DBG */

#if defined( _CMU_CTRL_DBGCLK_MASK )
      switch(CMU->CTRL & _CMU_CTRL_DBGCLK_MASK)
      {
        case CMU_CTRL_DBGCLK_AUXHFRCO:
          ret = cmuSelect_AUXHFRCO;
          break;

        case CMU_CTRL_DBGCLK_HFCLK:
          ret = cmuSelect_HFCLK;
          break;
      }
#else
      ret = cmuSelect_AUXHFRCO;
#endif
      break;


#if defined( USB_PRESENT )
    case CMU_USBCCLKSEL_REG:
      switch (CMU->STATUS
              & (CMU_STATUS_USBCLFXOSEL
#if defined(_CMU_STATUS_USBCHFCLKSEL_MASK)
                 | CMU_STATUS_USBCHFCLKSEL
#endif
#if defined(_CMU_STATUS_USBCUSHFRCOSEL_MASK)
                 | CMU_STATUS_USBCUSHFRCOSEL
#endif
                 | CMU_STATUS_USBCLFRCOSEL))
      {
#if defined(_CMU_STATUS_USBCHFCLKSEL_MASK)
        case CMU_STATUS_USBCHFCLKSEL:
          ret = cmuSelect_HFCLK;
          break;
#endif

#if defined(_CMU_STATUS_USBCUSHFRCOSEL_MASK)
        case CMU_STATUS_USBCUSHFRCOSEL:
          ret = cmuSelect_USHFRCO;
          break;
#endif

        case CMU_STATUS_USBCLFXOSEL:
          ret = cmuSelect_LFXO;
          break;

        case CMU_STATUS_USBCLFRCOSEL:
          ret = cmuSelect_LFRCO;
          break;

        default:
          ret = cmuSelect_Disabled;
          break;
      }
      break;
#endif

    default:
      EFM_ASSERT(0);
      ret = cmuSelect_Error;
      break;
  }

  return ret;
}


/***************************************************************************//**
 * @brief
 *   Select reference clock/oscillator used for a clock branch.
 *
 * @details
 *   Notice that if a selected reference is not enabled prior to selecting its
 *   use, it will be enabled, and this function will wait for the selected
 *   oscillator to be stable. It will however NOT be disabled if another
 *   reference clock is selected later.
 *
 *   This feature is particularly important if selecting a new reference
 *   clock for the clock branch clocking the core, otherwise the system
 *   may halt.
 *
 * @param[in] clock
 *   Clock branch to select reference clock for. One of:
 *   @li #cmuClock_HF
 *   @li #cmuClock_LFA
 *   @li #cmuClock_LFB @if _CMU_LFCLKSEL_LFAE_ULFRCO
 *   @li #cmuClock_LFC
 *   @endif            @if _SILICON_LABS_32B_PLATFORM_2
 *   @li #cmuClock_LFE
 *   @endif
 *   @li #cmuClock_DBG @if DOXYDOC_USB_PRESENT
 *   @li #cmuClock_USBC
 *   @endif
 *
 * @param[in] ref
 *   Reference selected for clocking, please refer to reference manual for
 *   for details on which reference is available for a specific clock branch.
 *   @li #cmuSelect_HFRCO
 *   @li #cmuSelect_LFRCO
 *   @li #cmuSelect_HFXO
 *   @li #cmuSelect_LFXO
 *   @li #cmuSelect_CORELEDIV2
 *   @li #cmuSelect_AUXHFRCO
 *   @li #cmuSelect_HFCLK @ifnot DOXYDOC_EFM32_GECKO_FAMILY
 *   @li #cmuSelect_ULFRCO
 *   @endif
 ******************************************************************************/
void CMU_ClockSelectSet(CMU_Clock_TypeDef clock, CMU_Select_TypeDef ref)
{
  uint32_t        select = cmuOsc_HFRCO;
  CMU_Osc_TypeDef osc    = cmuOsc_HFRCO;
  uint32_t        freq;
  uint32_t        tmp;
  uint32_t        selRegId;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
  volatile uint32_t *selReg = NULL;
#endif
#if defined( CMU_LFCLKSEL_LFAE_ULFRCO )
  uint32_t        lfExtended = 0;
#endif

  selRegId = (clock >> CMU_SEL_REG_POS) & CMU_SEL_REG_MASK;

  switch (selRegId)
  {
    case CMU_HFCLKSEL_REG:
      switch (ref)
      {
        case cmuSelect_LFXO:
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
          select = CMU_HFCLKSEL_HF_LFXO;
#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
          select = CMU_CMD_HFCLKSEL_LFXO;
#endif
          osc = cmuOsc_LFXO;
          break;

        case cmuSelect_LFRCO:
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
          select = CMU_HFCLKSEL_HF_LFRCO;
#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
          select = CMU_CMD_HFCLKSEL_LFRCO;
#endif
          osc = cmuOsc_LFRCO;
          break;

        case cmuSelect_HFXO:
          osc = cmuOsc_HFXO;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
          select = CMU_HFCLKSEL_HF_HFXO;
          /* Adjust HFXO buffer current for high frequencies, */
          /* enable WSHFLE for frequencies above 32MHz.       */
          if (SystemHFXOClockGet() > 32000000)
          {
            CMU->CTRL |= CMU_CTRL_WSHFLE;
          }
#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
          select = CMU_CMD_HFCLKSEL_HFXO;
#if defined( CMU_CTRL_HFLE )
          /* Adjust HFXO buffer current for high frequencies,     */
          /* enable HFLE for frequencies above CMU_MAX_FREQ_HFLE. */
          if(SystemHFXOClockGet() > CMU_MAX_FREQ_HFLE())
          {
            CMU->CTRL = (CMU->CTRL & ~_CMU_CTRL_HFXOBUFCUR_MASK)
                        | CMU_CTRL_HFXOBUFCUR_BOOSTABOVE32MHZ
            /* Must have HFLE enabled to access some LE peripherals >=32MHz */
                        | CMU_CTRL_HFLE;

            /* Set HFLE and DIV4 factor for peripheral clock if HFCORE  */
            /* clock for LE is enabled.                                 */
            if (CMU->HFCORECLKEN0 & CMU_HFCORECLKEN0_LE)
            {
              BUS_RegBitWrite(&CMU->HFCORECLKDIV,
                              _CMU_HFCORECLKDIV_HFCORECLKLEDIV_SHIFT, 1);
            }
          }
          else
          {
            /* This can happen if the user configures the EFM32_HFXO_FREQ to */
            /* use another oscillator frequency */
            CMU->CTRL = (CMU->CTRL & ~_CMU_CTRL_HFXOBUFCUR_MASK)
                        | CMU_CTRL_HFXOBUFCUR_BOOSTUPTO32MHZ;
          }
#endif
#endif
          break;

        case cmuSelect_HFRCO:
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
          select = CMU_HFCLKSEL_HF_HFRCO;
#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
          select = CMU_CMD_HFCLKSEL_HFRCO;
#endif
          osc = cmuOsc_HFRCO;
          break;

#if defined( CMU_CMD_HFCLKSEL_USHFRCODIV2 )
        case cmuSelect_USHFRCODIV2:
          select = CMU_CMD_HFCLKSEL_USHFRCODIV2;
          osc = cmuOsc_USHFRCO;
          break;
#endif

#if defined( CMU_LFCLKSEL_LFAE_ULFRCO ) || defined( CMU_LFACLKSEL_LFA_ULFRCO )
        case cmuSelect_ULFRCO:
          /* ULFRCO cannot be used as HFCLK  */
          EFM_ASSERT(0);
          return;
#endif

        default:
          EFM_ASSERT(0);
          return;
      }

      /* Ensure selected oscillator is enabled, waiting for it to stabilize */
      CMU_OscillatorEnable(osc, true, true);

      /* Configure worst case wait states for flash access before selecting */
      flashWaitStateMax();

      /* Switch to selected oscillator */
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      CMU->HFCLKSEL = select;
#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
      CMU->CMD = select;
#endif

      /* Keep EMU module informed */
      EMU_UpdateOscConfig();

      /* Update CMSIS core clock variable */
      /* (The function will update the global variable) */
      freq = SystemCoreClockGet();

      /* Optimize flash access wait state setting for currently selected core clk */
      flashWaitStateControl(freq);
      break;

#if defined( _SILICON_LABS_32B_PLATFORM_2 )
    case CMU_LFACLKSEL_REG:
      selReg = (selReg == NULL) ? &CMU->LFACLKSEL : selReg;
#if !defined( _CMU_LFACLKSEL_LFA_HFCLKLE )
      /* HFCLKCLE can not be used as LFACLK */
      EFM_ASSERT(ref != cmuSelect_HFCLKLE);
#endif
    case CMU_LFECLKSEL_REG:
      selReg = (selReg == NULL) ? &CMU->LFECLKSEL : selReg;
#if !defined( _CMU_LFECLKSEL_LFE_HFCLKLE )
      /* HFCLKCLE can not be used as LFECLK */
      EFM_ASSERT(ref != cmuSelect_HFCLKLE);
#endif
    case CMU_LFBCLKSEL_REG:
      selReg = (selReg == NULL) ? &CMU->LFBCLKSEL : selReg;
      switch (ref)
      {
        case cmuSelect_Disabled:
          tmp = _CMU_LFACLKSEL_LFA_DISABLED;
          break;

        case cmuSelect_LFXO:
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFXO, true, true);
          tmp = _CMU_LFACLKSEL_LFA_LFXO;
          break;

        case cmuSelect_LFRCO:
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFRCO, true, true);
          tmp = _CMU_LFACLKSEL_LFA_LFRCO;
          break;

        case cmuSelect_HFCLKLE:
          /* Ensure HFCORE to LE clocking is enabled */
          BUS_RegBitWrite(&CMU->HFBUSCLKEN0, _CMU_HFBUSCLKEN0_LE_SHIFT, 1);
          tmp = _CMU_LFBCLKSEL_LFB_HFCLKLE;

          /* If core frequency is > 32MHz enable WSHFLE */
          freq = SystemCoreClockGet();
          if (freq > 32000000U)
          {
            /* Enable CMU HFLE */
            BUS_RegBitWrite(&CMU->CTRL, _CMU_CTRL_WSHFLE_SHIFT, 1);

            /* Enable DIV4 factor for peripheral clock */
            BUS_RegBitWrite(&CMU->HFPRESC, _CMU_HFPRESC_HFCLKLEPRESC_SHIFT, 1);
          }
          break;

        case cmuSelect_ULFRCO:
          /* ULFRCO is always on, there is no need to enable it. */
          tmp = _CMU_LFACLKSEL_LFA_ULFRCO;
          break;

        default:
          EFM_ASSERT(0);
          return;
      }
      *selReg = tmp;
      break;

#elif defined( _SILICON_LABS_32B_PLATFORM_1 )
    case CMU_LFACLKSEL_REG:
    case CMU_LFBCLKSEL_REG:
      switch (ref)
      {
        case cmuSelect_Disabled:
          tmp = _CMU_LFCLKSEL_LFA_DISABLED;
          break;

        case cmuSelect_LFXO:
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFXO, true, true);
          tmp = _CMU_LFCLKSEL_LFA_LFXO;
          break;

        case cmuSelect_LFRCO:
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFRCO, true, true);
          tmp = _CMU_LFCLKSEL_LFA_LFRCO;
          break;

        case cmuSelect_CORELEDIV2:
          /* Ensure HFCORE to LE clocking is enabled */
          BUS_RegBitWrite(&(CMU->HFCORECLKEN0), _CMU_HFCORECLKEN0_LE_SHIFT, 1);
          tmp = _CMU_LFCLKSEL_LFA_HFCORECLKLEDIV2;
#if defined( CMU_CTRL_HFLE )
          /* If core frequency is higher than CMU_MAX_FREQ_HFLE on
             Giant/Leopard/Wonder, enable HFLE and DIV4. */
          freq = SystemCoreClockGet();
          if(freq > CMU_MAX_FREQ_HFLE())
          {
            /* Enable CMU HFLE */
            BUS_RegBitWrite(&CMU->CTRL, _CMU_CTRL_HFLE_SHIFT, 1);

            /* Enable DIV4 factor for peripheral clock */
            BUS_RegBitWrite(&CMU->HFCORECLKDIV,
                            _CMU_HFCORECLKDIV_HFCORECLKLEDIV_SHIFT, 1);
          }
#endif
          break;

#if defined( CMU_LFCLKSEL_LFAE_ULFRCO )
        case cmuSelect_ULFRCO:
          /* ULFRCO is always enabled */
          tmp = _CMU_LFCLKSEL_LFA_DISABLED;
          lfExtended = 1;
          break;
#endif

        default:
          /* Illegal clock source for LFA/LFB selected */
          EFM_ASSERT(0);
          return;
      }

      /* Apply select */
      if (selRegId == CMU_LFACLKSEL_REG)
      {
#if defined( _CMU_LFCLKSEL_LFAE_MASK )
        CMU->LFCLKSEL = (CMU->LFCLKSEL
                         & ~(_CMU_LFCLKSEL_LFA_MASK | _CMU_LFCLKSEL_LFAE_MASK))
                        | (tmp << _CMU_LFCLKSEL_LFA_SHIFT)
                        | (lfExtended << _CMU_LFCLKSEL_LFAE_SHIFT);
#else
        CMU->LFCLKSEL = (CMU->LFCLKSEL & ~_CMU_LFCLKSEL_LFA_MASK)
                        | (tmp << _CMU_LFCLKSEL_LFA_SHIFT);
#endif
      }
      else
      {
#if defined( _CMU_LFCLKSEL_LFBE_MASK )
        CMU->LFCLKSEL = (CMU->LFCLKSEL
                         & ~(_CMU_LFCLKSEL_LFB_MASK | _CMU_LFCLKSEL_LFBE_MASK))
                        | (tmp << _CMU_LFCLKSEL_LFB_SHIFT)
                        | (lfExtended << _CMU_LFCLKSEL_LFBE_SHIFT);
#else
        CMU->LFCLKSEL = (CMU->LFCLKSEL & ~_CMU_LFCLKSEL_LFB_MASK)
                        | (tmp << _CMU_LFCLKSEL_LFB_SHIFT);
#endif
      }
      break;

#if defined( _CMU_LFCLKSEL_LFC_MASK )
    case CMU_LFCCLKSEL_REG:
      switch(ref)
      {
        case cmuSelect_Disabled:
          tmp = _CMU_LFCLKSEL_LFA_DISABLED;
          break;

        case cmuSelect_LFXO:
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFXO, true, true);
          tmp = _CMU_LFCLKSEL_LFC_LFXO;
          break;

        case cmuSelect_LFRCO:
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFRCO, true, true);
          tmp = _CMU_LFCLKSEL_LFC_LFRCO;
          break;

        default:
          /* Illegal clock source for LFC selected */
          EFM_ASSERT(0);
          return;
      }

      /* Apply select */
      CMU->LFCLKSEL = (CMU->LFCLKSEL & ~_CMU_LFCLKSEL_LFC_MASK)
                      | (tmp << _CMU_LFCLKSEL_LFC_SHIFT);
      break;
#endif
#endif

#if defined( CMU_DBGCLKSEL_DBG ) || defined( CMU_CTRL_DBGCLK )
    case CMU_DBGCLKSEL_REG:
      switch(ref)
      {
#if defined( CMU_DBGCLKSEL_DBG )
        case cmuSelect_AUXHFRCO:
          /* Select AUXHFRCO as debug clock */
          CMU->DBGCLKSEL = CMU_DBGCLKSEL_DBG_AUXHFRCO;
          break;

        case cmuSelect_HFCLK:
          /* Select divided HFCLK as debug clock */
          CMU->DBGCLKSEL = CMU_DBGCLKSEL_DBG_HFCLK;
          break;
#endif

#if defined( CMU_CTRL_DBGCLK )
        case cmuSelect_AUXHFRCO:
          /* Select AUXHFRCO as debug clock */
          CMU->CTRL = (CMU->CTRL & ~(_CMU_CTRL_DBGCLK_MASK))
                      | CMU_CTRL_DBGCLK_AUXHFRCO;
          break;

        case cmuSelect_HFCLK:
          /* Select divided HFCLK as debug clock */
          CMU->CTRL = (CMU->CTRL & ~(_CMU_CTRL_DBGCLK_MASK))
                      | CMU_CTRL_DBGCLK_HFCLK;
          break;
#endif

        default:
          /* Illegal clock source for debug selected */
          EFM_ASSERT(0);
          return;
      }
      break;
#endif

#if defined(USB_PRESENT)
    case CMU_USBCCLKSEL_REG:
      switch(ref)
      {
        case cmuSelect_LFXO:
          /* Select LFXO as clock source for USB, can only be used in sleep mode */
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFXO, true, true);

          /* Switch oscillator */
          CMU->CMD = CMU_CMD_USBCCLKSEL_LFXO;

          /* Wait until clock is activated */
          while((CMU->STATUS & CMU_STATUS_USBCLFXOSEL)==0)
          {
          }
          break;

        case cmuSelect_LFRCO:
          /* Select LFRCO as clock source for USB, can only be used in sleep mode */
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_LFRCO, true, true);

          /* Switch oscillator */
          CMU->CMD = CMU_CMD_USBCCLKSEL_LFRCO;

          /* Wait until clock is activated */
          while((CMU->STATUS & CMU_STATUS_USBCLFRCOSEL)==0)
          {
          }
          break;

#if defined( CMU_STATUS_USBCHFCLKSEL )
        case cmuSelect_HFCLK:
          /* Select undivided HFCLK as clock source for USB */
          /* Oscillator must already be enabled to avoid a core lockup */
          CMU->CMD = CMU_CMD_USBCCLKSEL_HFCLKNODIV;
          /* Wait until clock is activated */
          while((CMU->STATUS & CMU_STATUS_USBCHFCLKSEL)==0)
          {
          }
          break;
#endif

#if defined( CMU_CMD_USBCCLKSEL_USHFRCO )
        case cmuSelect_USHFRCO:
          /* Select USHFRCO as clock source for USB */
          /* Ensure selected oscillator is enabled, waiting for it to stabilize */
          CMU_OscillatorEnable(cmuOsc_USHFRCO, true, true);

          /* Switch oscillator */
          CMU->CMD = CMU_CMD_USBCCLKSEL_USHFRCO;

          /* Wait until clock is activated */
          while((CMU->STATUS & CMU_STATUS_USBCUSHFRCOSEL)==0)
          {
          }
          break;
#endif

        default:
          /* Illegal clock source for USB */
          EFM_ASSERT(0);
          return;
      }
      break;
#endif

    default:
      EFM_ASSERT(0);
      break;
  }
}


/**************************************************************************//**
 * @brief
 *   CMU low frequency register synchronization freeze control.
 *
 * @details
 *   Some CMU registers requires synchronization into the low frequency (LF)
 *   domain. The freeze feature allows for several such registers to be
 *   modified before passing them to the LF domain simultaneously (which
 *   takes place when the freeze mode is disabled).
 *
 *   Another usage scenario of this feature, is when using an API (such
 *   as the CMU API) for modifying several bit fields consecutively in the
 *   same register. If freeze mode is enabled during this sequence, stalling
 *   can be avoided.
 *
 * @note
 *   When enabling freeze mode, this function will wait for all current
 *   ongoing CMU synchronization to LF domain to complete (Normally
 *   synchronization will not be in progress.) However for this reason, when
 *   using freeze mode, modifications of registers requiring LF synchronization
 *   should be done within one freeze enable/disable block to avoid unecessary
 *   stalling.
 *
 * @param[in] enable
 *   @li true - enable freeze, modified registers are not propagated to the
 *       LF domain
 *   @li false - disable freeze, modified registers are propagated to LF
 *       domain
 *****************************************************************************/
void CMU_FreezeEnable(bool enable)
{
  if (enable)
  {
    /* Wait for any ongoing LF synchronization to complete. This is just to */
    /* protect against the rare case when a user                            */
    /* - modifies a register requiring LF sync                              */
    /* - then enables freeze before LF sync completed                       */
    /* - then modifies the same register again                              */
    /* since modifying a register while it is in sync progress should be    */
    /* avoided.                                                             */
    while (CMU->SYNCBUSY)
    {
    }

    CMU->FREEZE = CMU_FREEZE_REGFREEZE;
  }
  else
  {
    CMU->FREEZE = 0;
  }
}


#if defined( _CMU_HFRCOCTRL_BAND_MASK )
/***************************************************************************//**
 * @brief
 *   Get HFRCO band in use.
 *
 * @return
 *   HFRCO band in use.
 ******************************************************************************/
CMU_HFRCOBand_TypeDef CMU_HFRCOBandGet(void)
{
  return (CMU_HFRCOBand_TypeDef)((CMU->HFRCOCTRL & _CMU_HFRCOCTRL_BAND_MASK)
                                 >> _CMU_HFRCOCTRL_BAND_SHIFT);
}
#endif /* _CMU_HFRCOCTRL_BAND_MASK */


#if defined( _CMU_HFRCOCTRL_BAND_MASK )
/***************************************************************************//**
 * @brief
 *   Set HFRCO band and the tuning value based on the value in the calibration
 *   table made during production.
 *
 * @param[in] band
 *   HFRCO band to activate.
 ******************************************************************************/
void CMU_HFRCOBandSet(CMU_HFRCOBand_TypeDef band)
{
  uint32_t           tuning;
  uint32_t           freq;
  CMU_Select_TypeDef osc;

  /* Read tuning value from calibration table */
  switch (band)
  {
    case cmuHFRCOBand_1MHz:
      tuning = (DEVINFO->HFRCOCAL0 & _DEVINFO_HFRCOCAL0_BAND1_MASK)
               >> _DEVINFO_HFRCOCAL0_BAND1_SHIFT;
      break;

    case cmuHFRCOBand_7MHz:
      tuning = (DEVINFO->HFRCOCAL0 & _DEVINFO_HFRCOCAL0_BAND7_MASK)
               >> _DEVINFO_HFRCOCAL0_BAND7_SHIFT;
      break;

    case cmuHFRCOBand_11MHz:
      tuning = (DEVINFO->HFRCOCAL0 & _DEVINFO_HFRCOCAL0_BAND11_MASK)
               >> _DEVINFO_HFRCOCAL0_BAND11_SHIFT;
      break;

    case cmuHFRCOBand_14MHz:
      tuning = (DEVINFO->HFRCOCAL0 & _DEVINFO_HFRCOCAL0_BAND14_MASK)
               >> _DEVINFO_HFRCOCAL0_BAND14_SHIFT;
      break;

    case cmuHFRCOBand_21MHz:
      tuning = (DEVINFO->HFRCOCAL1 & _DEVINFO_HFRCOCAL1_BAND21_MASK)
               >> _DEVINFO_HFRCOCAL1_BAND21_SHIFT;
      break;

#if defined( _CMU_HFRCOCTRL_BAND_28MHZ )
    case cmuHFRCOBand_28MHz:
      tuning = (DEVINFO->HFRCOCAL1 & _DEVINFO_HFRCOCAL1_BAND28_MASK)
               >> _DEVINFO_HFRCOCAL1_BAND28_SHIFT;
      break;
#endif

    default:
      EFM_ASSERT(0);
      return;
  }

  /* If HFRCO is used for core clock, we have to consider flash access WS. */
  osc = CMU_ClockSelectGet(cmuClock_HF);
  if (osc == cmuSelect_HFRCO)
  {
    /* Configure worst case wait states for flash access before setting divider */
    flashWaitStateMax();
  }

  /* Set band/tuning */
  CMU->HFRCOCTRL = (CMU->HFRCOCTRL &
                    ~(_CMU_HFRCOCTRL_BAND_MASK | _CMU_HFRCOCTRL_TUNING_MASK))
                   | (band << _CMU_HFRCOCTRL_BAND_SHIFT)
                   | (tuning << _CMU_HFRCOCTRL_TUNING_SHIFT);

  /* If HFRCO is used for core clock, optimize flash WS */
  if (osc == cmuSelect_HFRCO)
  {
    /* Update CMSIS core clock variable and get current core clock */
    /* (The function will update the global variable) */
    /* NOTE! We need at least 21 cycles before setting zero wait state to flash */
    /* (i.e. WS0) when going from the 28MHz to 1MHz in the HFRCO band */
    freq = SystemCoreClockGet();

    /* Optimize flash access wait state setting for current core clk */
    flashWaitStateControl(freq);
  }
}
#endif /* _CMU_HFRCOCTRL_BAND_MASK */


#if defined( _CMU_HFRCOCTRL_FREQRANGE_MASK )
/**************************************************************************//**
 * @brief
 *   Get a pointer to the HFRCO frequency calibration word in DEVINFO
 *
 * @param[in] freq
 *   Frequency in Hz
 *
 * @return
 *   HFRCO calibration word for a given frequency
 *****************************************************************************/
static uint32_t CMU_HFRCODevinfoGet(CMU_HFRCOFreq_TypeDef freq)
{
  switch (freq)
  {
    /* 1, 2 and 4MHz share the same calibration word */
    case cmuHFRCOFreq_1M0Hz:
    case cmuHFRCOFreq_2M0Hz:
    case cmuHFRCOFreq_4M0Hz:
      return DEVINFO->HFRCOCAL0;

    case cmuHFRCOFreq_7M0Hz:
      return DEVINFO->HFRCOCAL3;

    case cmuHFRCOFreq_13M0Hz:
      return DEVINFO->HFRCOCAL6;

    case cmuHFRCOFreq_16M0Hz:
      return DEVINFO->HFRCOCAL7;

    case cmuHFRCOFreq_19M0Hz:
      return DEVINFO->HFRCOCAL8;

    case cmuHFRCOFreq_26M0Hz:
      return DEVINFO->HFRCOCAL10;

    case cmuHFRCOFreq_32M0Hz:
      return DEVINFO->HFRCOCAL11;

    case cmuHFRCOFreq_38M0Hz:
      return DEVINFO->HFRCOCAL12;

    default: /* cmuHFRCOFreq_UserDefined */
      return 0;
  }
}


/***************************************************************************//**
 * @brief
 *   Get HFRCO frequency enumeration in use
 *
 * @return
 *   HFRCO frequency enumeration in use
 ******************************************************************************/
CMU_HFRCOFreq_TypeDef CMU_HFRCOFreqGet(void)
{
  return (CMU_HFRCOFreq_TypeDef)SystemHfrcoFreq;
}


/***************************************************************************//**
 * @brief
 *   Set HFRCO calibration for the selected target frequency
 *
 * @param[in] freq
 *   HFRCO frequency band to set
 ******************************************************************************/
void CMU_HFRCOFreqSet(CMU_HFRCOFreq_TypeDef freq)
{
  uint32_t freqCal;

  /* Get DEVINFO index, set CMSIS frequency SystemHfrcoFreq */
  freqCal = CMU_HFRCODevinfoGet(freq);
  EFM_ASSERT((freqCal != 0) && (freqCal != UINT_MAX));
  SystemHfrcoFreq = (uint32_t)freq;

  /* Set max wait-states while changing core clock */
  if (CMU_ClockSelectGet(cmuClock_HF) == cmuSelect_HFRCO)
  {
    flashWaitStateMax();
  }

  /* Wait for any previous sync to complete, and then set calibration data
     for the selected frequency.  */
  while(BUS_RegBitRead(&CMU->SYNCBUSY, _CMU_SYNCBUSY_HFRCOBSY_SHIFT));

  /* Check for valid calibration data */
  EFM_ASSERT(freqCal != UINT_MAX);

  /* Set divider in HFRCOCTRL for 1, 2 and 4MHz */
  switch(freq)
  {
    case cmuHFRCOFreq_1M0Hz:
      freqCal = (freqCal & ~_CMU_HFRCOCTRL_CLKDIV_MASK)
                | CMU_HFRCOCTRL_CLKDIV_DIV4;
      break;

    case cmuHFRCOFreq_2M0Hz:
      freqCal = (freqCal & ~_CMU_HFRCOCTRL_CLKDIV_MASK)
                | CMU_HFRCOCTRL_CLKDIV_DIV2;
      break;

    case cmuHFRCOFreq_4M0Hz:
      freqCal = (freqCal & ~_CMU_HFRCOCTRL_CLKDIV_MASK)
                | CMU_HFRCOCTRL_CLKDIV_DIV1;
      break;

    default:
      break;
  }
  CMU->HFRCOCTRL = freqCal;

  /* Optimize flash access wait-state configuration for this frequency, */
  /* if HFRCO is reference for core clock.                              */
  if (CMU_ClockSelectGet(cmuClock_HF) == cmuSelect_HFRCO)
  {
    flashWaitStateControl((uint32_t)freq);
  }
}
#endif /* _CMU_HFRCOCTRL_FREQRANGE_MASK */

#if defined( _CMU_HFRCOCTRL_SUDELAY_MASK )
/***************************************************************************//**
 * @brief
 *   Get the HFRCO startup delay.
 *
 * @details
 *   Please refer to the reference manual for further details.
 *
 * @return
 *   The startup delay in use.
 ******************************************************************************/
uint32_t CMU_HFRCOStartupDelayGet(void)
{
  return (CMU->HFRCOCTRL & _CMU_HFRCOCTRL_SUDELAY_MASK)
         >> _CMU_HFRCOCTRL_SUDELAY_SHIFT;
}


/***************************************************************************//**
 * @brief
 *   Set the HFRCO startup delay.
 *
 * @details
 *   Please refer to the reference manual for further details.
 *
 * @param[in] delay
 *   The startup delay to set (<= 31).
 ******************************************************************************/
void CMU_HFRCOStartupDelaySet(uint32_t delay)
{
  EFM_ASSERT(delay <= 31);

  delay &= _CMU_HFRCOCTRL_SUDELAY_MASK >> _CMU_HFRCOCTRL_SUDELAY_SHIFT;
  CMU->HFRCOCTRL = (CMU->HFRCOCTRL & ~(_CMU_HFRCOCTRL_SUDELAY_MASK))
                   | (delay << _CMU_HFRCOCTRL_SUDELAY_SHIFT);
}
#endif


#if defined( _CMU_HFXOCTRL_AUTOSTARTRDYSELRAC_MASK )
/***************************************************************************//**
 * @brief
 *   Enable or disable HFXO autostart
 *
 * @param[in] enRACStartSel
 *   If true, HFXO is automatically started and selected upon RAC wakeup.
 *   If false, HFXO is not started or selected automatically upon RAC wakeup.
 *
 * @param[in] enEM0EM1Start
 *   If true, HFXO is automatically started upon entering EM0/EM1 entry from
 *   EM2/EM3. HFXO selection has to be handled by the user.
 *   If false, HFXO is not started automatically when entering EM0/EM1.
 *
 * @param[in] enEM0EM1StartSel
 *   If true, HFXO is automatically started and immediately selected upon
 *   entering EM0/EM1 entry from EM2/EM3. Note that this option stalls the use of
 *   HFSRCCLK until HFXO becomes ready.
 *   If false, HFXO is not started or selected automatically when entering
 *   EM0/EM1.
 ******************************************************************************/
void CMU_HFXOAutostartEnable(bool enRACStartSel,
                             bool enEM0EM1Start,
                             bool enEM0EM1StartSel)
{
  uint32_t hfxoCtrl;
  hfxoCtrl = CMU->HFXOCTRL & ~(_CMU_HFXOCTRL_AUTOSTARTRDYSELRAC_MASK
                              | _CMU_HFXOCTRL_AUTOSTARTEM0EM1_MASK
                              | _CMU_HFXOCTRL_AUTOSTARTSELEM0EM1_MASK);

  hfxoCtrl |= (enRACStartSel ? CMU_HFXOCTRL_AUTOSTARTRDYSELRAC : 0)
              | (enEM0EM1Start ? CMU_HFXOCTRL_AUTOSTARTEM0EM1 : 0)
              | (enEM0EM1StartSel ? CMU_HFXOCTRL_AUTOSTARTSELEM0EM1 : 0);

  CMU->HFXOCTRL = hfxoCtrl;
}
#endif /* _CMU_HFXOCTRL_AUTOSTARTRDYSELRAC_MASK */


#if defined( _CMU_HFXOCTRL_MASK )
/**************************************************************************//**
 * @brief
 *   Set HFXO control registers
 *
 * @note
 *   HFXO configuration should be obtained from a configuration tool,
 *   app note or xtal datasheet. This function disables the HFXO to ensure
 *   a valid state before update.
 *
 * @param[in] hfxoInit
 *    HFXO setup parameters
 *****************************************************************************/
void CMU_HFXOInit(CMU_HFXOInit_TypeDef *hfxoInit)
{
  uint32_t ishReg;
  uint32_t ishMax;

  /* Do not disable HFXO if it is currently selected as HF/Core clock */
  EFM_ASSERT(CMU_ClockSelectGet(cmuClock_HF) != cmuSelect_HFXO);

  /* HFXO must be disabled before reconfiguration */
  CMU_OscillatorEnable(cmuOsc_HFXO, false, false);

  /* Apply control settings */
  BUS_RegMaskedWrite(&CMU->HFXOCTRL,
                     _CMU_HFXOCTRL_LOWPOWER_MASK
#if defined( _CMU_HFXOCTRL_AUTOSTARTRDYSELRAC_MASK )
                     | _CMU_HFXOCTRL_AUTOSTARTRDYSELRAC_MASK
#endif
                     | _CMU_HFXOCTRL_AUTOSTARTEM0EM1_MASK
                     | _CMU_HFXOCTRL_AUTOSTARTSELEM0EM1_MASK,
                     (hfxoInit->lowPowerMode
                      ? CMU_HFXOCTRL_LOWPOWER : 0)
#if defined( _CMU_HFXOCTRL_AUTOSTARTRDYSELRAC_MASK )
                     | (hfxoInit->autoStartSelOnRacWakeup
                        ? CMU_HFXOCTRL_AUTOSTARTRDYSELRAC : 0)
#endif
                     | (hfxoInit->autoStartEm01
                        ? CMU_HFXOCTRL_AUTOSTARTEM0EM1 : 0)
                     | (hfxoInit->autoSelEm01
                        ? CMU_HFXOCTRL_AUTOSTARTSELEM0EM1 : 0));

  /* Set XTAL tuning parameters */

  /* Set peak detection threshold in CMU_HFXOCTRL1_PEAKDETTHR[2:0] (hidden). */
  BUS_RegMaskedWrite((volatile uint32_t *)0x400E4028, 0x7, hfxoInit->thresholdPeakDetect);

  /* Set tuning for startup and steady state */
  BUS_RegMaskedWrite(&CMU->HFXOSTARTUPCTRL,
                     _CMU_HFXOSTARTUPCTRL_CTUNE_MASK
                     | _CMU_HFXOSTARTUPCTRL_REGISHWARM_MASK
                     | _CMU_HFXOSTARTUPCTRL_IBTRIMXOCORE_MASK
                     | _CMU_HFXOSTARTUPCTRL_IBTRIMXOCOREWARM_MASK,
                     (hfxoInit->ctuneStartup
                      << _CMU_HFXOSTARTUPCTRL_CTUNE_SHIFT)
                     | (hfxoInit->regIshStartup
                        << _CMU_HFXOSTARTUPCTRL_REGISHWARM_SHIFT)
                     | (hfxoInit->xoCoreBiasTrimStartup
                        << _CMU_HFXOSTARTUPCTRL_IBTRIMXOCORE_SHIFT)
                     | 0x4 /* Recommended tuning */
                        << _CMU_HFXOSTARTUPCTRL_IBTRIMXOCOREWARM_SHIFT);

  /* Adjust CMU_HFXOSTEADYSTATECTRL_REGISHUPPER according to regIshSteadyState.
     Saturate at max value. Please see the reference manual page 433 and Section
     12.5.10 CMU_HFXOSTEADYSTATECTRL for more details. */
  ishReg = hfxoInit->regIshSteadyState + 3;
  ishMax = _CMU_HFXOSTEADYSTATECTRL_REGISHUPPER_MASK
            >> _CMU_HFXOSTEADYSTATECTRL_REGISHUPPER_SHIFT;
  ishReg = ishReg > ishMax ? ishMax : ishReg;
  ishReg <<= _CMU_HFXOSTEADYSTATECTRL_REGISHUPPER_SHIFT;

  BUS_RegMaskedWrite(&CMU->HFXOSTEADYSTATECTRL,
                     _CMU_HFXOSTEADYSTATECTRL_CTUNE_MASK
                     | _CMU_HFXOSTEADYSTATECTRL_REGISH_MASK
                     | _CMU_HFXOSTEADYSTATECTRL_IBTRIMXOCORE_MASK
                     | _CMU_HFXOSTEADYSTATECTRL_REGISHUPPER_MASK,
                     (hfxoInit->ctuneSteadyState
                      << _CMU_HFXOSTEADYSTATECTRL_CTUNE_SHIFT)
                     | (hfxoInit->regIshSteadyState
                        << _CMU_HFXOSTEADYSTATECTRL_REGISH_SHIFT)
                     | (hfxoInit->xoCoreBiasTrimSteadyState
                        << _CMU_HFXOSTEADYSTATECTRL_IBTRIMXOCORE_SHIFT)
                     | ishReg);

  /* Set timeouts */
  BUS_RegMaskedWrite(&CMU->HFXOTIMEOUTCTRL,
                     _CMU_HFXOTIMEOUTCTRL_SHUNTOPTTIMEOUT_MASK
                     | _CMU_HFXOTIMEOUTCTRL_PEAKDETTIMEOUT_MASK
                     | _CMU_HFXOTIMEOUTCTRL_WARMSTEADYTIMEOUT_MASK
                     | _CMU_HFXOTIMEOUTCTRL_STEADYTIMEOUT_MASK
                     | _CMU_HFXOTIMEOUTCTRL_STARTUPTIMEOUT_MASK,
                     (hfxoInit->timeoutShuntOptimization
                      << _CMU_HFXOTIMEOUTCTRL_SHUNTOPTTIMEOUT_SHIFT)
                     | (hfxoInit->timeoutPeakDetect
                        << _CMU_HFXOTIMEOUTCTRL_PEAKDETTIMEOUT_SHIFT)
                     | (hfxoInit->timeoutWarmSteady
                        << _CMU_HFXOTIMEOUTCTRL_WARMSTEADYTIMEOUT_SHIFT)
                     | (hfxoInit->timeoutSteady
                        << _CMU_HFXOTIMEOUTCTRL_STEADYTIMEOUT_SHIFT)
                     | (hfxoInit->timeoutStartup
                        << _CMU_HFXOTIMEOUTCTRL_STARTUPTIMEOUT_SHIFT));
}
#endif


/***************************************************************************//**
 * @brief
 *   Get the LCD framerate divisor (FDIV) setting.
 *
 * @return
 *   The LCD framerate divisor.
 ******************************************************************************/
uint32_t CMU_LCDClkFDIVGet(void)
{
#if defined( LCD_PRESENT )
  return (CMU->LCDCTRL & _CMU_LCDCTRL_FDIV_MASK) >> _CMU_LCDCTRL_FDIV_SHIFT;
#else
  return 0;
#endif /* defined(LCD_PRESENT) */
}


/***************************************************************************//**
 * @brief
 *   Set the LCD framerate divisor (FDIV) setting.
 *
 * @note
 *   The FDIV field (CMU LCDCTRL register) should only be modified while the
 *   LCD module is clock disabled (CMU LFACLKEN0.LCD bit is 0). This function
 *   will NOT modify FDIV if the LCD module clock is enabled. Please refer to
 *   CMU_ClockEnable() for disabling/enabling LCD clock.
 *
 * @param[in] div
 *   The FDIV setting to use.
 ******************************************************************************/
void CMU_LCDClkFDIVSet(uint32_t div)
{
#if defined( LCD_PRESENT )
  EFM_ASSERT(div <= cmuClkDiv_128);

  /* Do not allow modification if LCD clock enabled */
  if (CMU->LFACLKEN0 & CMU_LFACLKEN0_LCD)
  {
    return;
  }

  div        <<= _CMU_LCDCTRL_FDIV_SHIFT;
  div         &= _CMU_LCDCTRL_FDIV_MASK;
  CMU->LCDCTRL = (CMU->LCDCTRL & ~_CMU_LCDCTRL_FDIV_MASK) | div;
#else
  (void)div;  /* Unused parameter */
#endif /* defined(LCD_PRESENT) */
}


#if defined( _CMU_LFXOCTRL_MASK )
/**************************************************************************//**
 * @brief
 *   Set LFXO control registers
 *
 * @note
 *   LFXO configuration should be obtained from a configuration tool,
 *   app note or xtal datasheet. This function disables the LFXO to ensure
 *   a valid state before update.
 *
 * @param[in] lfxoInit
 *    LFXO setup parameters
 *****************************************************************************/
void CMU_LFXOInit(CMU_LFXOInit_TypeDef *lfxoInit)
{
  /* Do not disable LFXO if it is currently selected as HF/Core clock */
  EFM_ASSERT(CMU_ClockSelectGet(cmuClock_HF) != cmuSelect_LFXO);

  /* LFXO must be disabled before reconfiguration */
  CMU_OscillatorEnable(cmuOsc_LFXO, false, false);

  BUS_RegMaskedWrite(&CMU->LFXOCTRL,
                     _CMU_LFXOCTRL_TUNING_MASK
                     | _CMU_LFXOCTRL_GAIN_MASK
                     | _CMU_LFXOCTRL_TIMEOUT_MASK,
                     (lfxoInit->ctune << _CMU_LFXOCTRL_TUNING_SHIFT)
                     | (lfxoInit->gain << _CMU_LFXOCTRL_GAIN_SHIFT)
                     | (lfxoInit->timeout << _CMU_LFXOCTRL_TIMEOUT_SHIFT));
}
#endif


/***************************************************************************//**
 * @brief
 *   Enable/disable oscillator.
 *
 * @note
 *   WARNING: When this function is called to disable either cmuOsc_LFXO or
 *   cmuOsc_HFXO the LFXOMODE or HFXOMODE fields of the CMU_CTRL register
 *   are reset to the reset value. I.e. if external clock sources are selected
 *   in either LFXOMODE or HFXOMODE fields, the configuration will be cleared
 *   and needs to be reconfigured if needed later.
 *
 * @param[in] osc
 *   The oscillator to enable/disable.
 *
 * @param[in] enable
 *   @li true - enable specified oscillator.
 *   @li false - disable specified oscillator.
 *
 * @param[in] wait
 *   Only used if @p enable is true.
 *   @li true - wait for oscillator start-up time to timeout before returning.
 *   @li false - do not wait for oscillator start-up time to timeout before
 *     returning.
 ******************************************************************************/
void CMU_OscillatorEnable(CMU_Osc_TypeDef osc, bool enable, bool wait)
{
  uint32_t rdyBitPos;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
  uint32_t ensBitPos;
#endif
  uint32_t enBit;
  uint32_t disBit;

  switch (osc)
  {
    case cmuOsc_HFRCO:
      enBit  = CMU_OSCENCMD_HFRCOEN;
      disBit = CMU_OSCENCMD_HFRCODIS;
      rdyBitPos = _CMU_STATUS_HFRCORDY_SHIFT;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      ensBitPos = _CMU_STATUS_HFRCOENS_SHIFT;
#endif
      break;

    case cmuOsc_HFXO:
      enBit  = CMU_OSCENCMD_HFXOEN;
      disBit = CMU_OSCENCMD_HFXODIS;
      rdyBitPos = _CMU_STATUS_HFXORDY_SHIFT;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      ensBitPos = _CMU_STATUS_HFXOENS_SHIFT;
#endif
      break;

    case cmuOsc_AUXHFRCO:
      enBit  = CMU_OSCENCMD_AUXHFRCOEN;
      disBit = CMU_OSCENCMD_AUXHFRCODIS;
      rdyBitPos = _CMU_STATUS_AUXHFRCORDY_SHIFT;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      ensBitPos = _CMU_STATUS_AUXHFRCOENS_SHIFT;
#endif
      break;

    case cmuOsc_LFRCO:
      enBit  = CMU_OSCENCMD_LFRCOEN;
      disBit = CMU_OSCENCMD_LFRCODIS;
      rdyBitPos = _CMU_STATUS_LFRCORDY_SHIFT;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      ensBitPos = _CMU_STATUS_LFRCOENS_SHIFT;
#endif
      break;

    case cmuOsc_LFXO:
      enBit  = CMU_OSCENCMD_LFXOEN;
      disBit = CMU_OSCENCMD_LFXODIS;
      rdyBitPos = _CMU_STATUS_LFXORDY_SHIFT;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      ensBitPos = _CMU_STATUS_LFXOENS_SHIFT;
#endif
      break;

#if defined( _CMU_STATUS_USHFRCOENS_MASK )
    case cmuOsc_USHFRCO:
      enBit  = CMU_OSCENCMD_USHFRCOEN;
      disBit = CMU_OSCENCMD_USHFRCODIS;
      rdyBitPos = _CMU_STATUS_USHFRCORDY_SHIFT;
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      ensBitPos = _CMU_STATUS_USHFRCOENS_SHIFT;
#endif
      break;
#endif

#if defined( CMU_LFCLKSEL_LFAE_ULFRCO )
    case cmuOsc_ULFRCO:
      /* ULFRCO is always enabled, and cannot be turned off */
      return;
#endif

    default:
      /* Undefined clock source */
      EFM_ASSERT(0);
      return;
  }

  if (enable)
  {
    CMU->OSCENCMD = enBit;

#if defined( _SILICON_LABS_32B_PLATFORM_2 )
    /* Always wait for ENS to go high */
    while (!BUS_RegBitRead(&CMU->STATUS, ensBitPos))
    {
    }
#endif

    /* Wait for clock to become ready after enable */
    if (wait)
    {
      while (!BUS_RegBitRead(&CMU->STATUS, rdyBitPos));
#if defined( _CMU_STATUS_HFXOSHUNTOPTRDY_MASK )
      /* Wait for shunt current optimization to complete */
      if ((osc == cmuOsc_HFXO)
          && (BUS_RegMaskedRead(&CMU->HFXOCTRL,
                                _CMU_HFXOCTRL_PEAKDETSHUNTOPTMODE_MASK)
              == CMU_HFXOCTRL_PEAKDETSHUNTOPTMODE_AUTOCMD))
      {
        while (!BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_HFXOSHUNTOPTRDY_SHIFT))
        {
        }
        /* Assert on failed peak detection. Incorrect HFXO initialization parameters
           caused startup to fail. Please review parameters. */
        EFM_ASSERT(BUS_RegBitRead(&CMU->STATUS, _CMU_STATUS_HFXOPEAKDETRDY_SHIFT));
      }
#endif
    }
  }
  else
  {
    CMU->OSCENCMD = disBit;

#if defined( _SILICON_LABS_32B_PLATFORM_2 )
    /* Always wait for ENS to go low */
    while (BUS_RegBitRead(&CMU->STATUS, ensBitPos))
    {
    }
#endif
  }

  /* Keep EMU module informed */
  EMU_UpdateOscConfig();
}


/***************************************************************************//**
 * @brief
 *   Get oscillator frequency tuning setting.
 *
 * @param[in] osc
 *   Oscillator to get tuning value for, one of:
 *   @li #cmuOsc_LFRCO
 *   @li #cmuOsc_HFRCO
 *   @li #cmuOsc_AUXHFRCO
 *
 * @return
 *   The oscillator frequency tuning setting in use.
 ******************************************************************************/
uint32_t CMU_OscillatorTuningGet(CMU_Osc_TypeDef osc)
{
  uint32_t ret;

  switch (osc)
  {
    case cmuOsc_LFRCO:
      ret = (CMU->LFRCOCTRL & _CMU_LFRCOCTRL_TUNING_MASK)
            >> _CMU_LFRCOCTRL_TUNING_SHIFT;
      break;

    case cmuOsc_HFRCO:
      ret = (CMU->HFRCOCTRL & _CMU_HFRCOCTRL_TUNING_MASK)
            >> _CMU_HFRCOCTRL_TUNING_SHIFT;
      break;

    case cmuOsc_AUXHFRCO:
      ret = (CMU->AUXHFRCOCTRL & _CMU_AUXHFRCOCTRL_TUNING_MASK)
            >> _CMU_AUXHFRCOCTRL_TUNING_SHIFT;
      break;

    default:
      EFM_ASSERT(0);
      ret = 0;
      break;
  }

  return ret;
}


/***************************************************************************//**
 * @brief
 *   Set the oscillator frequency tuning control.
 *
 * @note
 *   Oscillator tuning is done during production, and the tuning value is
 *   automatically loaded after a reset. Changing the tuning value from the
 *   calibrated value is for more advanced use.
 *
 * @param[in] osc
 *   Oscillator to set tuning value for, one of:
 *   @li #cmuOsc_LFRCO
 *   @li #cmuOsc_HFRCO
 *   @li #cmuOsc_AUXHFRCO
 *
 * @param[in] val
 *   The oscillator frequency tuning setting to use.
 ******************************************************************************/
void CMU_OscillatorTuningSet(CMU_Osc_TypeDef osc, uint32_t val)
{
  switch (osc)
  {
    case cmuOsc_LFRCO:
      EFM_ASSERT(val <= (_CMU_LFRCOCTRL_TUNING_MASK
                         >> _CMU_LFRCOCTRL_TUNING_SHIFT));
      val &= (_CMU_LFRCOCTRL_TUNING_MASK >> _CMU_LFRCOCTRL_TUNING_SHIFT);
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      while(BUS_RegBitRead(&CMU->SYNCBUSY, _CMU_SYNCBUSY_LFRCOBSY_SHIFT));
#endif
      CMU->LFRCOCTRL = (CMU->LFRCOCTRL & ~(_CMU_LFRCOCTRL_TUNING_MASK))
                       | (val << _CMU_LFRCOCTRL_TUNING_SHIFT);
      break;

    case cmuOsc_HFRCO:
      EFM_ASSERT(val <= (_CMU_HFRCOCTRL_TUNING_MASK
                         >> _CMU_HFRCOCTRL_TUNING_SHIFT));
      val &= (_CMU_HFRCOCTRL_TUNING_MASK >> _CMU_HFRCOCTRL_TUNING_SHIFT);
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      while(BUS_RegBitRead(&CMU->SYNCBUSY, _CMU_SYNCBUSY_HFRCOBSY_SHIFT))
      {
      }
#endif
      CMU->HFRCOCTRL = (CMU->HFRCOCTRL & ~(_CMU_HFRCOCTRL_TUNING_MASK))
                       | (val << _CMU_HFRCOCTRL_TUNING_SHIFT);
      break;

    case cmuOsc_AUXHFRCO:
      EFM_ASSERT(val <= (_CMU_AUXHFRCOCTRL_TUNING_MASK
                         >> _CMU_AUXHFRCOCTRL_TUNING_SHIFT));
      val &= (_CMU_AUXHFRCOCTRL_TUNING_MASK >> _CMU_AUXHFRCOCTRL_TUNING_SHIFT);
#if defined( _SILICON_LABS_32B_PLATFORM_2 )
      while(BUS_RegBitRead(&CMU->SYNCBUSY, _CMU_SYNCBUSY_AUXHFRCOBSY_SHIFT))
      {
      }
#endif
      CMU->AUXHFRCOCTRL = (CMU->AUXHFRCOCTRL & ~(_CMU_AUXHFRCOCTRL_TUNING_MASK))
                          | (val << _CMU_AUXHFRCOCTRL_TUNING_SHIFT);
      break;

    default:
      EFM_ASSERT(0);
      break;
  }
}


/**************************************************************************//**
 * @brief
 *   Determine if currently selected PCNTn clock used is external or LFBCLK.
 *
 * @param[in] instance
 *   PCNT instance number to get currently selected clock source for.
 *
 * @return
 *   @li true - selected clock is external clock.
 *   @li false - selected clock is LFBCLK.
 *****************************************************************************/
bool CMU_PCNTClockExternalGet(unsigned int instance)
{
  uint32_t setting;

  switch (instance)
  {
#if defined( _CMU_PCNTCTRL_PCNT0CLKEN_MASK )
    case 0:
      setting = CMU->PCNTCTRL & CMU_PCNTCTRL_PCNT0CLKSEL_PCNT0S0;
      break;

#if defined( _CMU_PCNTCTRL_PCNT1CLKEN_MASK )
    case 1:
      setting = CMU->PCNTCTRL & CMU_PCNTCTRL_PCNT1CLKSEL_PCNT1S0;
      break;

#if defined( _CMU_PCNTCTRL_PCNT2CLKEN_MASK )
    case 2:
      setting = CMU->PCNTCTRL & CMU_PCNTCTRL_PCNT2CLKSEL_PCNT2S0;
      break;
#endif
#endif
#endif

    default:
      setting = 0;
      break;
  }
  return (setting ? true : false);
}


/**************************************************************************//**
 * @brief
 *   Select PCNTn clock.
 *
 * @param[in] instance
 *   PCNT instance number to set selected clock source for.
 *
 * @param[in] external
 *   Set to true to select external clock, false to select LFBCLK.
 *****************************************************************************/
void CMU_PCNTClockExternalSet(unsigned int instance, bool external)
{
#if defined( PCNT_PRESENT )
  uint32_t setting = 0;

  EFM_ASSERT(instance < PCNT_COUNT);

  if (external)
  {
    setting = 1;
  }

  BUS_RegBitWrite(&(CMU->PCNTCTRL), (instance * 2) + 1, setting);

#else
  (void)instance;  /* Unused parameter */
  (void)external;  /* Unused parameter */
#endif
}


#if defined( _CMU_USHFRCOCONF_BAND_MASK )
/***************************************************************************//**
 * @brief
 *   Get USHFRCO band in use.
 *
 * @return
 *   USHFRCO band in use.
 ******************************************************************************/
CMU_USHFRCOBand_TypeDef CMU_USHFRCOBandGet(void)
{
  return (CMU_USHFRCOBand_TypeDef)((CMU->USHFRCOCONF
                                    & _CMU_USHFRCOCONF_BAND_MASK)
                                   >> _CMU_USHFRCOCONF_BAND_SHIFT);
}
#endif

#if defined( _CMU_USHFRCOCONF_BAND_MASK )
/***************************************************************************//**
 * @brief
 *   Set USHFRCO band to use.
 *
 * @param[in] band
 *   USHFRCO band to activate.
 ******************************************************************************/
void CMU_USHFRCOBandSet(CMU_USHFRCOBand_TypeDef band)
{
  uint32_t           tuning;
  uint32_t           fineTuning;
  CMU_Select_TypeDef osc;

  /* Cannot switch band if USHFRCO is already selected as HF clock. */
  osc = CMU_ClockSelectGet(cmuClock_HF);
  EFM_ASSERT((CMU_USHFRCOBandGet() != band) && (osc != cmuSelect_USHFRCO));

  /* Read tuning value from calibration table */
  switch (band)
  {
    case cmuUSHFRCOBand_24MHz:
      tuning = (DEVINFO->USHFRCOCAL0 & _DEVINFO_USHFRCOCAL0_BAND24_TUNING_MASK)
               >> _DEVINFO_USHFRCOCAL0_BAND24_TUNING_SHIFT;
      fineTuning = (DEVINFO->USHFRCOCAL0
                    & _DEVINFO_USHFRCOCAL0_BAND24_FINETUNING_MASK)
                   >> _DEVINFO_USHFRCOCAL0_BAND24_FINETUNING_SHIFT;
      break;

    case cmuUSHFRCOBand_48MHz:
      tuning = (DEVINFO->USHFRCOCAL0 & _DEVINFO_USHFRCOCAL0_BAND48_TUNING_MASK)
               >> _DEVINFO_USHFRCOCAL0_BAND48_TUNING_SHIFT;
      fineTuning = (DEVINFO->USHFRCOCAL0
                    & _DEVINFO_USHFRCOCAL0_BAND48_FINETUNING_MASK)
                   >> _DEVINFO_USHFRCOCAL0_BAND48_FINETUNING_SHIFT;
      /* Enable the clock divider before switching the band from 24 to 48MHz */
      BUS_RegBitWrite(&CMU->USHFRCOCONF, _CMU_USHFRCOCONF_USHFRCODIV2DIS_SHIFT, 0);
      break;

    default:
      EFM_ASSERT(0);
      return;
  }

  /* Set band and tuning */
  CMU->USHFRCOCONF = (CMU->USHFRCOCONF & ~_CMU_USHFRCOCONF_BAND_MASK)
                     | (band << _CMU_USHFRCOCONF_BAND_SHIFT);
  CMU->USHFRCOCTRL = (CMU->USHFRCOCTRL & ~_CMU_USHFRCOCTRL_TUNING_MASK)
                     | (tuning << _CMU_USHFRCOCTRL_TUNING_SHIFT);
  CMU->USHFRCOTUNE = (CMU->USHFRCOTUNE & ~_CMU_USHFRCOTUNE_FINETUNING_MASK)
                     | (fineTuning << _CMU_USHFRCOTUNE_FINETUNING_SHIFT);

  /* Disable the clock divider after switching the band from 48 to 24MHz */
  if (band == cmuUSHFRCOBand_24MHz)
  {
    BUS_RegBitWrite(&CMU->USHFRCOCONF, _CMU_USHFRCOCONF_USHFRCODIV2DIS_SHIFT, 1);
  }
}
#endif



/** @} (end addtogroup CMU) */
/** @} (end addtogroup EM_Library) */
#endif /* __EM_CMU_H */
