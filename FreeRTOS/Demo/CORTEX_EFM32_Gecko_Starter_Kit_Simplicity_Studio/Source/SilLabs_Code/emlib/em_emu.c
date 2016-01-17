/***************************************************************************//**
 * @file em_emu.c
 * @brief Energy Management Unit (EMU) Peripheral API
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


#include "em_emu.h"
#if defined( EMU_PRESENT ) && ( EMU_COUNT > 0 )

#include "em_cmu.h"
#include "em_system.h"
#include "em_assert.h"

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup EMU
 * @brief Energy Management Unit (EMU) Peripheral API
 * @{
 ******************************************************************************/

/* Consistency check, since restoring assumes similar bitpositions in */
/* CMU OSCENCMD and STATUS regs */
#if (CMU_STATUS_AUXHFRCOENS != CMU_OSCENCMD_AUXHFRCOEN)
#error Conflict in AUXHFRCOENS and AUXHFRCOEN bitpositions
#endif
#if (CMU_STATUS_HFXOENS != CMU_OSCENCMD_HFXOEN)
#error Conflict in HFXOENS and HFXOEN bitpositions
#endif
#if (CMU_STATUS_LFRCOENS != CMU_OSCENCMD_LFRCOEN)
#error Conflict in LFRCOENS and LFRCOEN bitpositions
#endif
#if (CMU_STATUS_LFXOENS != CMU_OSCENCMD_LFXOEN)
#error Conflict in LFXOENS and LFXOEN bitpositions
#endif


/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */
/* Fix for errata EMU_E107 - non-WIC interrupt masks. */
#if defined(_EFM32_GECKO_FAMILY)
  #define ERRATA_FIX_EMU_E107_EN
  #define NON_WIC_INT_MASK_0    (~(0x0dfc0323U))
  #define NON_WIC_INT_MASK_1    (~(0x0U))
#elif defined(_EFM32_TINY_FAMILY)
  #define ERRATA_FIX_EMU_E107_EN
  #define NON_WIC_INT_MASK_0    (~(0x001be323U))
  #define NON_WIC_INT_MASK_1    (~(0x0U))
#elif defined(_EFM32_GIANT_FAMILY)
  #define ERRATA_FIX_EMU_E107_EN
  #define NON_WIC_INT_MASK_0    (~(0xff020e63U))
  #define NON_WIC_INT_MASK_1    (~(0x00000046U))
#elif defined(_EFM32_WONDER_FAMILY)
  #define ERRATA_FIX_EMU_E107_EN
  #define NON_WIC_INT_MASK_0    (~(0xff020e63U))
  #define NON_WIC_INT_MASK_1    (~(0x00000046U))
#else
/* Zero Gecko and future families are not affected by errata EMU_E107 */
#endif

/* Fix for errata EMU_E108 - High Current Consumption on EM4 Entry. */
#if defined(_EFM32_HAPPY_FAMILY)
#define ERRATA_FIX_EMU_E108_EN
#endif
/** @endcond */

/*******************************************************************************
 **************************   LOCAL VARIABLES   ********************************
 ******************************************************************************/

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */
/**
 * CMU configured oscillator selection and oscillator enable status. When a
 * user configures oscillators, this varaiable shall shadow the configuration.
 * It is used by the EMU module in order to be able to restore the oscillator
 * config after having been in certain energy modes (since HW may automatically
 * alter config when going into an energy mode). It is the responsibility of
 * the CMU module to keep it up-to-date (or a user if not using the CMU API
 * for oscillator control).
 */
static uint32_t cmuStatus;
/** @endcond */


/*******************************************************************************
 **************************   LOCAL FUNCTIONS   ********************************
 ******************************************************************************/

/** @cond DO_NOT_INCLUDE_WITH_DOXYGEN */

/***************************************************************************//**
 * @brief
 *   Restore oscillators and core clock after having been in EM2 or EM3.
 ******************************************************************************/
static void EMU_Restore(void)
{
  uint32_t oscEnCmd;
  uint32_t cmuLocked;
  uint32_t statusClkSelMask;

  /* Although we could use the CMU API for most of the below handling, we */
  /* would like this function to be as efficient as possible. */

  /* CMU registers may be locked */
  cmuLocked = CMU->LOCK & CMU_LOCK_LOCKKEY_LOCKED;
  CMU_Unlock();

  /* AUXHFRCO are automatically disabled (except if using debugger). */
  /* HFRCO, USHFRCO and HFXO are automatically disabled. */
  /* LFRCO/LFXO may be disabled by SW in EM3. */
  /* Restore according to status prior to entering energy mode. */
  oscEnCmd = 0;
  oscEnCmd |= ((cmuStatus & CMU_STATUS_HFRCOENS)    ? CMU_OSCENCMD_HFRCOEN : 0);
  oscEnCmd |= ((cmuStatus & CMU_STATUS_AUXHFRCOENS) ? CMU_OSCENCMD_AUXHFRCOEN : 0);
  oscEnCmd |= ((cmuStatus & CMU_STATUS_LFRCOENS)    ? CMU_OSCENCMD_LFRCOEN : 0);
  oscEnCmd |= ((cmuStatus & CMU_STATUS_HFXOENS)     ? CMU_OSCENCMD_HFXOEN : 0);
  oscEnCmd |= ((cmuStatus & CMU_STATUS_LFXOENS)     ? CMU_OSCENCMD_LFXOEN : 0);
#if defined( _CMU_STATUS_USHFRCOENS_MASK )
  oscEnCmd |= ((cmuStatus & CMU_STATUS_USHFRCOENS)  ? CMU_OSCENCMD_USHFRCOEN : 0);
#endif
  CMU->OSCENCMD = oscEnCmd;

  statusClkSelMask =
    (CMU_STATUS_HFRCOSEL |
     CMU_STATUS_HFXOSEL |
     CMU_STATUS_LFRCOSEL |
#if defined( CMU_STATUS_USHFRCODIV2SEL )
     CMU_STATUS_USHFRCODIV2SEL |
#endif
     CMU_STATUS_LFXOSEL);

  /* Restore oscillator used for clocking core */
  switch (cmuStatus & statusClkSelMask)
  {
  case CMU_STATUS_LFRCOSEL:
    /* Wait for LFRCO to stabilize */
    while (!(CMU->STATUS & CMU_STATUS_LFRCORDY))
      ;
    CMU->CMD = CMU_CMD_HFCLKSEL_LFRCO;
    break;

  case CMU_STATUS_LFXOSEL:
    /* Wait for LFXO to stabilize */
    while (!(CMU->STATUS & CMU_STATUS_LFXORDY))
      ;
    CMU->CMD = CMU_CMD_HFCLKSEL_LFXO;
    break;

  case CMU_STATUS_HFXOSEL:
    /* Wait for HFXO to stabilize */
    while (!(CMU->STATUS & CMU_STATUS_HFXORDY))
      ;
    CMU->CMD = CMU_CMD_HFCLKSEL_HFXO;
    break;

#if defined( CMU_STATUS_USHFRCODIV2SEL )
  case CMU_STATUS_USHFRCODIV2SEL:
    /* Wait for USHFRCO to stabilize */
    while (!(CMU->STATUS & CMU_STATUS_USHFRCORDY))
      ;
    CMU->CMD = _CMU_CMD_HFCLKSEL_USHFRCODIV2;
    break;
#endif

  default: /* CMU_STATUS_HFRCOSEL */
    /* If core clock was HFRCO core clock, it is automatically restored to */
    /* state prior to entering energy mode. No need for further action. */
    break;
  }

  /* If HFRCO was disabled before entering Energy Mode, turn it off again */
  /* as it is automatically enabled by wake up */
  if ( ! (cmuStatus & CMU_STATUS_HFRCOENS) )
  {
    CMU->OSCENCMD = CMU_OSCENCMD_HFRCODIS;
  }

  /* Restore CMU register locking */
  if (cmuLocked)
  {
    CMU_Lock();
  }
}


/* Get enable conditions for errata EMU_E107 fix. */
#if defined(ERRATA_FIX_EMU_E107_EN)
static __INLINE bool getErrataFixEmuE107En(void)
{
  /* SYSTEM_ChipRevisionGet could have been used here, but we would like a faster implementation in this case. */
  uint16_t majorMinorRev;

  /* CHIP MAJOR bit [3:0] */
  majorMinorRev = (((ROMTABLE->PID0 & _ROMTABLE_PID0_REVMAJOR_MASK) >> _ROMTABLE_PID0_REVMAJOR_SHIFT) << 8);
  /* CHIP MINOR bit [7:4] */
  majorMinorRev |= (((ROMTABLE->PID2 & _ROMTABLE_PID2_REVMINORMSB_MASK) >> _ROMTABLE_PID2_REVMINORMSB_SHIFT) << 4);
  /* CHIP MINOR bit [3:0] */
  majorMinorRev |=  ((ROMTABLE->PID3 & _ROMTABLE_PID3_REVMINORLSB_MASK) >> _ROMTABLE_PID3_REVMINORLSB_SHIFT);

#if defined(_EFM32_GECKO_FAMILY)
  return (majorMinorRev <= 0x0103);
#elif defined(_EFM32_TINY_FAMILY)
  return (majorMinorRev <= 0x0102);
#elif defined(_EFM32_GIANT_FAMILY)
  return (majorMinorRev <= 0x0103) || (majorMinorRev == 0x0204);
#elif defined(_EFM32_WONDER_FAMILY)
  return (majorMinorRev == 0x0100);
#else
  /* Zero Gecko and future families are not affected by errata EMU_E107 */
  return false;
#endif
}
#endif

/** @endcond */


/*******************************************************************************
 **************************   GLOBAL FUNCTIONS   *******************************
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Enter energy mode 2 (EM2).
 *
 * @details
 *   When entering EM2, the high frequency clocks are disabled, ie HFXO, HFRCO
 *   and AUXHFRCO (for AUXHFRCO, see exception note below). When re-entering
 *   EM0, HFRCO is re-enabled and the core will be clocked by the configured
 *   HFRCO band. This ensures a quick wakeup from EM2.
 *
 *   However, prior to entering EM2, the core may have been using another
 *   oscillator than HFRCO. The @p restore parameter gives the user the option
 *   to restore all HF oscillators according to state prior to entering EM2,
 *   as well as the clock used to clock the core. This restore procedure is
 *   handled by SW. However, since handled by SW, it will not be restored
 *   before completing the interrupt function(s) waking up the core!
 *
 * @note
 *   If restoring core clock to use the HFXO oscillator, which has been
 *   disabled during EM2 mode, this function will stall until the oscillator
 *   has stabilized. Stalling time can be reduced by adding interrupt
 *   support detecting stable oscillator, and an asynchronous switch to the
 *   original oscillator. See CMU documentation. Such a feature is however
 *   outside the scope of the implementation in this function.
 * @par
 *   If HFXO is re-enabled by this function, and NOT used to clock the core,
 *   this function will not wait for HFXO to stabilize. This must be considered
 *   by the application if trying to use features relying on that oscillator
 *   upon return.
 * @par
 *   If a debugger is attached, the AUXHFRCO will not be disabled if enabled
 *   upon entering EM2. It will thus remain enabled when returning to EM0
 *   regardless of the @p restore parameter.
 *
 * @param[in] restore
 *   @li true - restore oscillators and clocks, see function details.
 *   @li false - do not restore oscillators and clocks, see function details.
 * @par
 *   The @p restore option should only be used if all clock control is done
 *   via the CMU API.
 ******************************************************************************/
void EMU_EnterEM2(bool restore)
{
#if defined(ERRATA_FIX_EMU_E107_EN)
  bool errataFixEmuE107En;
  uint32_t nonWicIntEn[2];
#endif

  /* Auto-update CMU status just in case before entering energy mode. */
  /* This variable is normally kept up-to-date by the CMU API. */
  cmuStatus = CMU->STATUS;

  /* Enter Cortex-M3 deep sleep mode */
  SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;

  /* Fix for errata EMU_E107 - store non-WIC interrupt enable flags.
     Disable the enabled non-WIC interrupts. */
#if defined(ERRATA_FIX_EMU_E107_EN)
  errataFixEmuE107En = getErrataFixEmuE107En();
  if (errataFixEmuE107En)
  {
    nonWicIntEn[0] = NVIC->ISER[0] & NON_WIC_INT_MASK_0;
    NVIC->ICER[0] = nonWicIntEn[0];
#if (NON_WIC_INT_MASK_1 != (~(0x0U)))
    nonWicIntEn[1] = NVIC->ISER[1] & NON_WIC_INT_MASK_1;
    NVIC->ICER[1] = nonWicIntEn[1];
#endif
  }
#endif

  __WFI();

  /* Fix for errata EMU_E107 - restore state of non-WIC interrupt enable flags. */
#if defined(ERRATA_FIX_EMU_E107_EN)
  if (errataFixEmuE107En)
  {
    NVIC->ISER[0] = nonWicIntEn[0];
#if (NON_WIC_INT_MASK_1 != (~(0x0U)))
    NVIC->ISER[1] = nonWicIntEn[1];
#endif
  }
#endif

  /* Restore oscillators/clocks if specified */
  if (restore)
  {
    EMU_Restore();
  }
  /* If not restoring, and original clock was not HFRCO, we have to */
  /* update CMSIS core clock variable since core clock has changed */
  /* to using HFRCO. */
  else if (!(cmuStatus & CMU_STATUS_HFRCOSEL))
  {
    SystemCoreClockUpdate();
  }
}


/***************************************************************************//**
 * @brief
 *   Enter energy mode 3 (EM3).
 *
 * @details
 *   When entering EM3, the high frequency clocks are disabled by HW, ie HFXO,
 *   HFRCO and AUXHFRCO (for AUXHFRCO, see exception note below). In addition,
 *   the low frequency clocks, ie LFXO and LFRCO are disabled by SW. When
 *   re-entering EM0, HFRCO is re-enabled and the core will be clocked by the
 *   configured HFRCO band. This ensures a quick wakeup from EM3.
 *
 *   However, prior to entering EM3, the core may have been using another
 *   oscillator than HFRCO. The @p restore parameter gives the user the option
 *   to restore all HF/LF oscillators according to state prior to entering EM3,
 *   as well as the clock used to clock the core. This restore procedure is
 *   handled by SW. However, since handled by SW, it will not be restored
 *   before completing the interrupt function(s) waking up the core!
 *
 * @note
 *   If restoring core clock to use an oscillator other than HFRCO, this
 *   function will stall until the oscillator has stabilized. Stalling time
 *   can be reduced by adding interrupt support detecting stable oscillator,
 *   and an asynchronous switch to the original oscillator. See CMU
 *   documentation. Such a feature is however outside the scope of the
 *   implementation in this function.
 * @par
 *   If HFXO/LFXO/LFRCO are re-enabled by this function, and NOT used to clock
 *   the core, this function will not wait for those oscillators to stabilize.
 *   This must be considered by the application if trying to use features
 *   relying on those oscillators upon return.
 * @par
 *   If a debugger is attached, the AUXHFRCO will not be disabled if enabled
 *   upon entering EM3. It will thus remain enabled when returning to EM0
 *   regardless of the @p restore parameter.
 *
 * @param[in] restore
 *   @li true - restore oscillators and clocks, see function details.
 *   @li false - do not restore oscillators and clocks, see function details.
 * @par
 *   The @p restore option should only be used if all clock control is done
 *   via the CMU API.
 ******************************************************************************/
void EMU_EnterEM3(bool restore)
{
  uint32_t cmuLocked;

#if defined(ERRATA_FIX_EMU_E107_EN)
  bool errataFixEmuE107En;
  uint32_t nonWicIntEn[2];
#endif

  /* Auto-update CMU status just in case before entering energy mode. */
  /* This variable is normally kept up-to-date by the CMU API. */
  cmuStatus = CMU->STATUS;

  /* CMU registers may be locked */
  cmuLocked = CMU->LOCK & CMU_LOCK_LOCKKEY_LOCKED;
  CMU_Unlock();

  /* Disable LF oscillators */
  CMU->OSCENCMD = CMU_OSCENCMD_LFXODIS | CMU_OSCENCMD_LFRCODIS;

  /* Restore CMU register locking */
  if (cmuLocked)
  {
    CMU_Lock();
  }

  /* Enter Cortex-M3 deep sleep mode */
  SCB->SCR |= SCB_SCR_SLEEPDEEP_Msk;

  /* Fix for errata EMU_E107 - store non-WIC interrupt enable flags.
     Disable the enabled non-WIC interrupts. */
#if defined(ERRATA_FIX_EMU_E107_EN)
  errataFixEmuE107En = getErrataFixEmuE107En();
  if (errataFixEmuE107En)
  {
    nonWicIntEn[0] = NVIC->ISER[0] & NON_WIC_INT_MASK_0;
    NVIC->ICER[0] = nonWicIntEn[0];
#if (NON_WIC_INT_MASK_1 != (~(0x0U)))
    nonWicIntEn[1] = NVIC->ISER[1] & NON_WIC_INT_MASK_1;
    NVIC->ICER[1] = nonWicIntEn[1];
#endif

  }
#endif

  __WFI();

  /* Fix for errata EMU_E107 - restore state of non-WIC interrupt enable flags. */
#if defined(ERRATA_FIX_EMU_E107_EN)
  if (errataFixEmuE107En)
  {
    NVIC->ISER[0] = nonWicIntEn[0];
#if (NON_WIC_INT_MASK_1 != (~(0x0U)))
    NVIC->ISER[1] = nonWicIntEn[1];
#endif
  }
#endif

  /* Restore oscillators/clocks if specified */
  if (restore)
  {
    EMU_Restore();
  }
  /* If not restoring, and original clock was not HFRCO, we have to */
  /* update CMSIS core clock variable since core clock has changed */
  /* to using HFRCO. */
  else if (!(cmuStatus & CMU_STATUS_HFRCOSEL))
  {
    SystemCoreClockUpdate();
  }
}


/***************************************************************************//**
 * @brief
 *   Enter energy mode 4 (EM4).
 *
 * @note
 *   Only a power on reset or external reset pin can wake the device from EM4.
 ******************************************************************************/
void EMU_EnterEM4(void)
{
  int i;
  uint32_t em4seq2;
  uint32_t em4seq3;

  em4seq2 = (EMU->CTRL & ~_EMU_CTRL_EM4CTRL_MASK) | (2 << _EMU_CTRL_EM4CTRL_SHIFT);
  em4seq3 = (EMU->CTRL & ~_EMU_CTRL_EM4CTRL_MASK) | (3 << _EMU_CTRL_EM4CTRL_SHIFT);

  /* Make sure register write lock is disabled */
  EMU_Unlock();

#if defined(ERRATA_FIX_EMU_E108_EN)
  /* Fix for errata EMU_E108 - High Current Consumption on EM4 Entry. */
  __disable_irq();
  *(volatile uint32_t *)0x400C80E4 = 0;
#endif

  for (i = 0; i < 4; i++)
  {
    EMU->CTRL = em4seq2;
    EMU->CTRL = em4seq3;
  }
  EMU->CTRL = em4seq2;
}


/***************************************************************************//**
 * @brief
 *   Power down memory block.
 *
 * @param[in] blocks
 *   Specifies a logical OR of bits indicating memory blocks to power down.
 *   Bit 0 selects block 1, bit 1 selects block 2, etc. Memory block 0 cannot
 *   be disabled. Please refer to the EFM32 reference manual for available
 *   memory blocks for a device.
 *
 * @note
 *   Only a reset can make the specified memory block(s) available for use
 *   after having been powered down. Function will be void for devices not
 *   supporting this feature.
 ******************************************************************************/
void EMU_MemPwrDown(uint32_t blocks)
{
#if defined(_EMU_MEMCTRL_RESETVALUE)
  EFM_ASSERT(blocks <= _EMU_MEMCTRL_MASK);

  EMU->MEMCTRL = blocks;
#else
  (void)blocks;
#endif
}


/***************************************************************************//**
 * @brief
 *   Update EMU module with CMU oscillator selection/enable status.
 *
 * @details
 *   When entering EM2 and EM3, the HW may change the core clock oscillator
 *   used, as well as disabling some oscillators. The user may optionally select
 *   to restore the oscillators after waking up from EM2 and EM3 through the
 *   SW API.
 *
 *   However, in order to support this in a safe way, the EMU module must
 *   be kept up-to-date on the actual selected configuration. The CMU
 *   module must keep the EMU module up-to-date.
 *
 *   This function is mainly intended for internal use by the CMU module,
 *   but if the applications changes oscillator configurations without
 *   using the CMU API, this function can be used to keep the EMU module
 *   up-to-date.
 ******************************************************************************/
void EMU_UpdateOscConfig(void)
{
  /* Fetch current configuration */
  cmuStatus = CMU->STATUS;
}


#if defined( _EMU_CTRL_EMVREG_MASK ) || defined( _EMU_CTRL_EM23VREG_MASK )
/***************************************************************************//**
 * @brief
 *   Update EMU module with Energy Mode 2 and 3 configuration
 *
 * @param[in] em23Init
 *    Energy Mode 2 and 3 configuration structure
 ******************************************************************************/
void EMU_EM23Init(EMU_EM23Init_TypeDef *em23Init)
{
#if defined( _EMU_CTRL_EMVREG_MASK )
  EMU->CTRL = em23Init->em23Vreg ? (EMU->CTRL | EMU_CTRL_EMVREG) : (EMU->CTRL & ~EMU_CTRL_EMVREG);
#elif defined( _EMU_CTRL_EM23VREG_MASK )
  EMU->CTRL = em23Init->em23Vreg ? (EMU->CTRL | EMU_CTRL_EM23VREG) : (EMU->CTRL & ~EMU_CTRL_EM23VREG);
#endif
}
#endif


#if defined( _EMU_EM4CONF_MASK )
/***************************************************************************//**
 * @brief
 *   Update EMU module with Energy Mode 4 configuration
 *
 * @param[in] em4Init
 *    Energy Mode 4 configuration structure
 ******************************************************************************/
void EMU_EM4Init(EMU_EM4Init_TypeDef *em4Init)
{
  uint32_t em4conf = EMU->EM4CONF;

  /* Clear fields that will be reconfigured */
  em4conf &= ~(
    _EMU_EM4CONF_LOCKCONF_MASK |
    _EMU_EM4CONF_OSC_MASK |
    _EMU_EM4CONF_BURTCWU_MASK |
    _EMU_EM4CONF_VREGEN_MASK);

  /* Configure new settings */
  em4conf |= (
    (em4Init->lockConfig << _EMU_EM4CONF_LOCKCONF_SHIFT) |
    (em4Init->osc) |
    (em4Init->buRtcWakeup << _EMU_EM4CONF_BURTCWU_SHIFT) |
    (em4Init->vreg << _EMU_EM4CONF_VREGEN_SHIFT));

  /* Apply configuration. Note that lock can be set after this stage. */
  EMU->EM4CONF = em4conf;
}
#endif


#if defined( BU_PRESENT )

/***************************************************************************//**
 * @brief
 *   Configure Backup Power Domain settings
 *
 * @param[in] bupdInit
 *   Backup power domain initialization structure
 ******************************************************************************/
void EMU_BUPDInit(EMU_BUPDInit_TypeDef *bupdInit)
{
  uint32_t reg;

  /* Set power connection configuration */
  reg = EMU->PWRCONF & ~(
    _EMU_PWRCONF_PWRRES_MASK|
    _EMU_PWRCONF_VOUTSTRONG_MASK|
    _EMU_PWRCONF_VOUTMED_MASK|
    _EMU_PWRCONF_VOUTWEAK_MASK);

  reg |= (bupdInit->resistor|
         (bupdInit->voutStrong << _EMU_PWRCONF_VOUTSTRONG_SHIFT)|
         (bupdInit->voutMed    << _EMU_PWRCONF_VOUTMED_SHIFT)|
         (bupdInit->voutWeak   << _EMU_PWRCONF_VOUTWEAK_SHIFT));

  EMU->PWRCONF = reg;

  /* Set backup domain inactive mode configuration */
  reg = EMU->BUINACT & ~(_EMU_BUINACT_PWRCON_MASK);
  reg |= (bupdInit->inactivePower);
  EMU->BUINACT = reg;

  /* Set backup domain active mode configuration */
  reg = EMU->BUACT & ~(_EMU_BUACT_PWRCON_MASK);
  reg |= (bupdInit->activePower);
  EMU->BUACT = reg;

  /* Set power control configuration */
  reg = EMU->BUCTRL & ~(
    _EMU_BUCTRL_PROBE_MASK|
    _EMU_BUCTRL_BODCAL_MASK|
    _EMU_BUCTRL_STATEN_MASK|
    _EMU_BUCTRL_EN_MASK);

  /* Note use of ->enable to both enable BUPD, use BU_VIN pin input and
     release reset */
  reg |= (bupdInit->probe|
         (bupdInit->bodCal          << _EMU_BUCTRL_BODCAL_SHIFT)|
         (bupdInit->statusPinEnable << _EMU_BUCTRL_STATEN_SHIFT)|
         (bupdInit->enable          << _EMU_BUCTRL_EN_SHIFT));

  /* Enable configuration */
  EMU->BUCTRL = reg;

  /* If enable is true, enable BU_VIN input power pin, if not disable it  */
  EMU_BUPinEnable(bupdInit->enable);

  /* If enable is true, release BU reset, if not keep reset asserted */
  BITBAND_Peripheral(&(RMU->CTRL), _RMU_CTRL_BURSTEN_SHIFT, !bupdInit->enable);
}


/***************************************************************************//**
 * @brief
 *   Configure Backup Power Domain BOD Threshold value
 * @note
 *   These values are precalibrated
 * @param[in] mode Active or Inactive mode
 * @param[in] value
 ******************************************************************************/
void EMU_BUThresholdSet(EMU_BODMode_TypeDef mode, uint32_t value)
{
  EFM_ASSERT(value<=(_EMU_BUACT_BUEXTHRES_MASK>>_EMU_BUACT_BUEXTHRES_SHIFT));

  switch(mode)
  {
  case emuBODMode_Active:
    EMU->BUACT = (EMU->BUACT & ~(_EMU_BUACT_BUEXTHRES_MASK))|(value<<_EMU_BUACT_BUEXTHRES_SHIFT);
    break;
  case emuBODMode_Inactive:
    EMU->BUINACT = (EMU->BUINACT & ~(_EMU_BUINACT_BUENTHRES_MASK))|(value<<_EMU_BUINACT_BUENTHRES_SHIFT);
    break;
  }
}


/***************************************************************************//**
 * @brief
 *  Configure Backup Power Domain BOD Threshold Range
 * @note
 *  These values are precalibrated
 * @param[in] mode Active or Inactive mode
 * @param[in] value
 ******************************************************************************/
void EMU_BUThresRangeSet(EMU_BODMode_TypeDef mode, uint32_t value)
{
  EFM_ASSERT(value<=(_EMU_BUACT_BUEXRANGE_MASK>>_EMU_BUACT_BUEXRANGE_SHIFT));

  switch(mode)
  {
  case emuBODMode_Active:
    EMU->BUACT = (EMU->BUACT & ~(_EMU_BUACT_BUEXRANGE_MASK))|(value<<_EMU_BUACT_BUEXRANGE_SHIFT);
    break;
  case emuBODMode_Inactive:
    EMU->BUINACT = (EMU->BUINACT & ~(_EMU_BUINACT_BUENRANGE_MASK))|(value<<_EMU_BUINACT_BUENRANGE_SHIFT);
    break;
  }
}

#endif


/** @} (end addtogroup EMU) */
/** @} (end addtogroup EM_Library) */
#endif /* __EM_EMU_H */
