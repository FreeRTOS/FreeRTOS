/***************************************************************************//**
 * @file em_emu.h
 * @brief Energy management unit (EMU) peripheral API
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

#ifndef __SILICON_LABS_EM_EMU_H__
#define __SILICON_LABS_EM_EMU_H__

#include "em_device.h"
#if defined( EMU_PRESENT )

#include <stdbool.h>
#include "em_bus.h"

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**
 * @addtogroup EM_Library
 * @{
 ******************************************************************************/

/***************************************************************************//**
 * @addtogroup EMU
 * @{
 ******************************************************************************/

/*******************************************************************************
 ********************************   ENUMS   ************************************
 ******************************************************************************/

#if defined( _EMU_EM4CONF_OSC_MASK )
/** EM4 duty oscillator */
typedef enum
{
  /** Select ULFRCO as duty oscillator in EM4 */
  emuEM4Osc_ULFRCO = EMU_EM4CONF_OSC_ULFRCO,
  /** Select LFXO as duty oscillator in EM4 */
  emuEM4Osc_LFXO = EMU_EM4CONF_OSC_LFXO,
  /** Select LFRCO as duty oscillator in EM4 */
  emuEM4Osc_LFRCO = EMU_EM4CONF_OSC_LFRCO
} EMU_EM4Osc_TypeDef;
#endif

#if defined( _EMU_BUCTRL_PROBE_MASK )
/** Backup Power Voltage Probe types */
typedef enum
{
  /** Disable voltage probe */
  emuProbe_Disable = EMU_BUCTRL_PROBE_DISABLE,
  /** Connect probe to VDD_DREG */
  emuProbe_VDDDReg = EMU_BUCTRL_PROBE_VDDDREG,
  /** Connect probe to BU_IN */
  emuProbe_BUIN    = EMU_BUCTRL_PROBE_BUIN,
  /** Connect probe to BU_OUT */
  emuProbe_BUOUT   = EMU_BUCTRL_PROBE_BUOUT
} EMU_Probe_TypeDef;
#endif

#if defined( _EMU_PWRCONF_PWRRES_MASK )
/** Backup Power Domain resistor selection */
typedef enum
{
  /** Main power and backup power connected with RES0 series resistance */
  emuRes_Res0 = EMU_PWRCONF_PWRRES_RES0,
  /** Main power and backup power connected with RES1 series resistance */
  emuRes_Res1 = EMU_PWRCONF_PWRRES_RES1,
  /** Main power and backup power connected with RES2 series resistance */
  emuRes_Res2 = EMU_PWRCONF_PWRRES_RES2,
  /** Main power and backup power connected with RES3 series resistance */
  emuRes_Res3 = EMU_PWRCONF_PWRRES_RES3,
} EMU_Resistor_TypeDef;
#endif

#if defined( BU_PRESENT )
/** Backup Power Domain power connection */
typedef enum
{
  /** No connection between main and backup power */
  emuPower_None = EMU_BUINACT_PWRCON_NONE,
  /** Main power and backup power connected through diode,
      allowing current from backup to main only */
  emuPower_BUMain = EMU_BUINACT_PWRCON_BUMAIN,
  /** Main power and backup power connected through diode,
      allowing current from main to backup only */
  emuPower_MainBU = EMU_BUINACT_PWRCON_MAINBU,
  /** Main power and backup power connected without diode */
  emuPower_NoDiode = EMU_BUINACT_PWRCON_NODIODE,
} EMU_Power_TypeDef;
#endif

/** BOD threshold setting selector, active or inactive mode */
typedef enum
{
  /** Configure BOD threshold for active mode */
  emuBODMode_Active,
  /** Configure BOD threshold for inactive mode */
  emuBODMode_Inactive,
} EMU_BODMode_TypeDef;

#if defined( _EMU_EM4CTRL_EM4STATE_MASK )
/** EM4 modes */
typedef enum
{
  /** EM4 Hibernate */
  emuEM4Hibernate = EMU_EM4CTRL_EM4STATE_EM4H,
  /** EM4 Shutoff */
  emuEM4Shutoff = EMU_EM4CTRL_EM4STATE_EM4S,
} EMU_EM4State_TypeDef;
#endif


#if defined( _EMU_EM4CTRL_EM4IORETMODE_MASK )
typedef enum
{
  /** No Retention: Pads enter reset state when entering EM4 */
  emuPinRetentionDisable = EMU_EM4CTRL_EM4IORETMODE_DISABLE,
  /** Retention through EM4: Pads enter reset state when exiting EM4 */
  emuPinRetentionEm4Exit = EMU_EM4CTRL_EM4IORETMODE_EM4EXIT,
  /** Retention through EM4 and wakeup: call EMU_UnlatchPinRetention() to
      release pins from retention after EM4 wakeup */
  emuPinRetentionLatch   = EMU_EM4CTRL_EM4IORETMODE_SWUNLATCH,
} EMU_EM4PinRetention_TypeDef;
#endif


#if defined( _EMU_PWRCFG_MASK )
/** Power configurations */
typedef enum
{
  /** DCDC is connected to DVDD */
  emuPowerConfig_DcdcToDvdd = EMU_PWRCFG_PWRCFG_DCDCTODVDD,
} EMU_PowerConfig_TypeDef;
#endif

#if defined( _EMU_DCDCCTRL_MASK )
/** DCDC operating modes */
typedef enum
{
  /** DCDC regulator bypass */
  emuDcdcMode_Bypass = EMU_DCDCCTRL_DCDCMODE_BYPASS,
  /** DCDC low-noise mode */
  emuDcdcMode_LowNoise = EMU_DCDCCTRL_DCDCMODE_LOWNOISE,
} EMU_DcdcMode_TypeDef;
#endif

#if defined( _EMU_PWRCTRL_MASK )
/** DCDC to DVDD mode analog peripheral power supply select */
typedef enum
{
  /** Select AVDD as analog power supply. Typically lower noise, but less energy efficient. */
  emuDcdcAnaPeripheralPower_AVDD = EMU_PWRCTRL_ANASW_AVDD,
  /** Select DCDC (DVDD) as analog power supply. Typically more energy efficient, but more noise. */
  emuDcdcAnaPeripheralPower_DCDC = EMU_PWRCTRL_ANASW_DVDD
} EMU_DcdcAnaPeripheralPower_TypeDef;
#endif

#if defined( _EMU_DCDCMISCCTRL_MASK )
/** DCDC Low-noise efficiency mode */
typedef enum
{
#if defined( _EFM_DEVICE )
  /** High efficiency mode */
  emuDcdcLnHighEfficiency = 0,
#endif
  /** Fast transient response mode */
  emuDcdcLnFastTransient = EMU_DCDCMISCCTRL_LNFORCECCM,
} EMU_DcdcLnTransientMode_TypeDef;
#endif

#if defined( _EMU_DCDCCTRL_MASK )
/** DCDC Low-noise RCO band select */
typedef enum
{
  /** Set RCO to 3MHz */
  EMU_DcdcLnRcoBand_3MHz = 0,
  /** Set RCO to 4MHz */
  EMU_DcdcLnRcoBand_4MHz = 1,
  /** Set RCO to 5MHz */
  EMU_DcdcLnRcoBand_5MHz = 2,
  /** Set RCO to 6MHz */
  EMU_DcdcLnRcoBand_6MHz = 3,
  /** Set RCO to 7MHz */
  EMU_DcdcLnRcoBand_7MHz = 4,
  /** Set RCO to 8MHz */
  EMU_DcdcLnRcoBand_8MHz = 5,
  /** Set RCO to 9MHz */
  EMU_DcdcLnRcoBand_9MHz = 6,
  /** Set RCO to 10MHz */
  EMU_DcdcLnRcoBand_10MHz = 7,
} EMU_DcdcLnRcoBand_TypeDef;

#endif

#if defined( EMU_STATUS_VMONRDY )
/** VMON channels */
typedef enum
{
  emuVmonChannel_AVDD,
  emuVmonChannel_ALTAVDD,
  emuVmonChannel_DVDD,
  emuVmonChannel_IOVDD0
} EMU_VmonChannel_TypeDef;
#endif /* EMU_STATUS_VMONRDY */

/*******************************************************************************
 *******************************   STRUCTS   ***********************************
 ******************************************************************************/

/** Energy Mode 2 and 3 initialization structure  */
typedef struct
{
  bool em23VregFullEn;                  /**< Enable full VREG drive strength in EM2/3 */
} EMU_EM23Init_TypeDef;

/** Default initialization of EM2 and 3 configuration */
#define EMU_EM23INIT_DEFAULT    \
{ false }                               /* Reduced voltage regulator drive strength in EM2 and EM3 */


#if defined( _EMU_EM4CONF_MASK ) || defined( _EMU_EM4CTRL_MASK )
/** Energy Mode 4 initialization structure  */
typedef struct
{
#if defined( _EMU_EM4CONF_MASK )
  /* Init parameters for platforms with EMU->EM4CONF register */
  bool                  lockConfig;     /**< Lock configuration of regulator, BOD and oscillator */
  bool                  buBodRstDis;    /**< When set, no reset will be asserted due to Brownout when in EM4 */
  EMU_EM4Osc_TypeDef    osc;            /**< EM4 duty oscillator */
  bool                  buRtcWakeup;    /**< Wake up on EM4 BURTC interrupt */
  bool                  vreg;           /**< Enable EM4 voltage regulator */

#elif defined( _EMU_EM4CTRL_MASK )
  /* Init parameters for platforms with EMU->EM4CTRL register */
  bool                        retainLfxo;       /**< Disable the LFXO upon EM4 entry */
  bool                        retainLfrco;      /**< Disable the LFRCO upon EM4 entry */
  bool                        retainUlfrco;     /**< Disable the ULFRCO upon EM4 entry */
  EMU_EM4State_TypeDef        em4State;         /**< Hibernate or shutoff EM4 state */
  EMU_EM4PinRetention_TypeDef pinRetentionMode; /**< EM4 pin retention mode */
#endif
} EMU_EM4Init_TypeDef;
#endif

/** Default initialization of EM4 configuration */
#if defined( _EMU_EM4CONF_MASK )
#define EMU_EM4INIT_DEFAULT                                                                \
{                                                                                          \
  false,                              /* Dont't lock configuration after it's been set */  \
  false,                              /* No reset will be asserted due to Brownout when in EM4 */ \
  emuEM4Osc_ULFRCO,                   /* Use default ULFRCO oscillator  */                 \
  true,                               /* Wake up on EM4 BURTC interrupt */                 \
  true,                               /* Enable VREG */                                    \
}
#endif
#if defined( _EMU_EM4CTRL_MASK )
#define EMU_EM4INIT_DEFAULT                                                                \
{                                                                                          \
  false,                             /* Retain LFXO configuration upon EM4 entry */        \
  false,                             /* Retain LFRCO configuration upon EM4 entry */       \
  false,                             /* Retain ULFRCO configuration upon EM4 entry */      \
  emuEM4Shutoff,                     /* Use EM4 shutoff state */                           \
  emuPinRetentionDisable,            /* Do not retain pins in EM4 */                       \
}
#endif

#if defined( BU_PRESENT )
/** Backup Power Domain Initialization structure */
typedef struct
{
  /* Backup Power Domain power configuration */

  /** Voltage probe select, selects ADC voltage */
  EMU_Probe_TypeDef     probe;
  /** Enable BOD calibration mode */
  bool                  bodCal;
  /** Enable BU_STAT status pin for active BU mode */
  bool                  statusPinEnable;

  /* Backup Power Domain connection configuration */
  /** Power domain resistor */
  EMU_Resistor_TypeDef  resistor;
  /** BU_VOUT strong enable */
  bool                  voutStrong;
  /** BU_VOUT medium enable */
  bool                  voutMed;
  /** BU_VOUT weak enable */
  bool                  voutWeak;
  /** Power connection, when not in Backup Mode */
  EMU_Power_TypeDef  inactivePower;
  /** Power connection, when in Backup Mode */
  EMU_Power_TypeDef     activePower;
  /** Enable backup power domain, and release reset, enable BU_VIN pin  */
  bool                  enable;
} EMU_BUPDInit_TypeDef;

/** Default Backup Power Domain configuration */
#define EMU_BUPDINIT_DEFAULT                                              \
{                                                                         \
  emuProbe_Disable, /* Do not enable voltage probe */                     \
  false,            /* Disable BOD calibration mode */                    \
  false,            /* Disable BU_STAT pin for backup mode indication */  \
                                                                          \
  emuRes_Res0,      /* RES0 series resistance between main and backup power */ \
  false,            /* Don't enable strong switch */                           \
  false,            /* Don't enable medium switch */                           \
  false,            /* Don't enable weak switch */                             \
                                                                               \
  emuPower_None,    /* No connection between main and backup power (inactive mode) */     \
  emuPower_None,    /* No connection between main and backup power (active mode) */       \
  true              /* Enable BUPD enter on BOD, enable BU_VIN pin, release BU reset  */  \
}
#endif

#if defined( _EMU_DCDCCTRL_MASK )
/** DCDC initialization structure */
typedef struct
{
  EMU_PowerConfig_TypeDef powerConfig;                  /**< Device external power configuration */
  EMU_DcdcMode_TypeDef dcdcMode;                        /**< DCDC regulator operating mode in EM0 */
  uint16_t mVout;                                       /**< Target output voltage (mV) */
  uint16_t em01LoadCurrent_mA;                          /**< Estimated average load current in EM0 (mA).
                                                             This estimate is also used for EM1 optimization,
                                                             so if EM1 current is expected to be higher than EM0,
                                                             then this parameter should hold the higher EM1 current. */
  uint16_t em234LoadCurrent_uA;                         /**< Estimated average load current in EM2 (uA).
                                                             This estimate is also used for EM3 and 4 optimization,
                                                             so if EM3 or 4 current is expected to be higher than EM2,
                                                             then this parameter should hold the higher EM3 or 4 current. */
  uint16_t maxCurrent_mA;                               /**< Maximum peak DCDC output current (mA).
                                                             This can be set to the maximum for the power source,
                                                             for example the maximum for a battery. */
  EMU_DcdcAnaPeripheralPower_TypeDef anaPeripheralPower;/**< Select analog peripheral power in DCDC-to-DVDD mode */
  EMU_DcdcLnTransientMode_TypeDef lnTransientMode;      /**< Low-noise transient mode */

} EMU_DCDCInit_TypeDef;

/** Default DCDC initialization */
#if defined( _EFM_DEVICE )
#define EMU_DCDCINIT_DEFAULT                                                                                    \
{                                                                                                               \
  emuPowerConfig_DcdcToDvdd,     /* DCDC to DVDD */                                                             \
  emuDcdcMode_LowNoise,          /* Low-niose mode in EM0 (can be set to LowPower on EFM32PG revB0) */          \
  1800,                          /* Nominal output voltage for DVDD mode, 1.8V  */                              \
  5,                             /* Nominal EM0 load current of less than 5mA */                                \
  10,                            /* Nominal EM2/3 load current less than 10uA  */                               \
  160,                           /* Maximum peak current of 160mA */                                            \
  emuDcdcAnaPeripheralPower_DCDC,/* Select DCDC as analog power supply (lower power) */                         \
  emuDcdcLnHighEfficiency,       /* Use low-noise high-efficiency mode (ignored if emuDcdcMode_LowPower) */     \
}
#else /* EFR32 device */
#define EMU_DCDCINIT_DEFAULT                                                                                    \
{                                                                                                               \
  emuPowerConfig_DcdcToDvdd,     /* DCDC to DVDD */                                                             \
  emuDcdcMode_LowNoise,          /* Low-niose mode in EM0 */                                                    \
  1800,                          /* Nominal output voltage for DVDD mode, 1.8V  */                              \
  15,                             /* Nominal EM0 load current of less than 5mA */                               \
  10,                            /* Nominal EM2/3 load current less than 10uA  */                               \
  160,                           /* Maximum peak current of 160mA */                                            \
  emuDcdcAnaPeripheralPower_AVDD,/* Select AVDD as analog power supply (less noise) */                          \
  emuDcdcLnFastTransient,        /* Use low-noise fast-transient mode */                                        \
}
#endif

#endif

#if defined( EMU_STATUS_VMONRDY )
/** VMON initialization structure */
typedef struct
{
  EMU_VmonChannel_TypeDef channel;                 /**< VMON channel to configure */
  int threshold;                                   /**< Trigger threshold (mV) */
  bool riseWakeup;                                 /**< Wake up from EM4H on rising edge */
  bool fallWakeup;                                 /**< Wake up from EM4H on falling edge */
  bool enable;                                     /**< Enable VMON channel */
  bool retDisable;                                 /**< Disable IO0 retention when voltage drops below threshold (IOVDD only) */
} EMU_VmonInit_TypeDef;

/** Default VMON initialization structure */
#define EMU_VMONINIT_DEFAULT                                               \
{                                                                          \
  emuVmonChannel_AVDD,          /* AVDD VMON channel */                    \
  3200,                         /* 3.2 V threshold */                      \
  false,                        /* Don't wake from EM4H on rising edge */  \
  false,                        /* Don't wake from EM4H on falling edge */ \
  true,                         /* Enable VMON channel */                  \
  false                         /* Don't disable IO0 retention */          \
}

/** VMON Hysteresis initialization structure */
typedef struct
{
  EMU_VmonChannel_TypeDef channel;                     /**< VMON channel to configure */
  int riseThreshold;                                   /**< Rising threshold (mV) */
  int fallThreshold;                                   /**< Falling threshold (mV) */
  bool riseWakeup;                                     /**< Wake up from EM4H on rising edge */
  bool fallWakeup;                                     /**< Wake up from EM4H on falling edge */
  bool enable;                                         /**< Enable VMON channel */
} EMU_VmonHystInit_TypeDef;

/** Default VMON Hysteresis initialization structure */
#define EMU_VMONHYSTINIT_DEFAULT                                           \
{                                                                          \
  emuVmonChannel_AVDD,          /* AVDD VMON channel */                    \
  3200,                         /* 3.2 V rise threshold */                 \
  3200,                         /* 3.2 V fall threshold */                 \
  false,                        /* Don't wake from EM4H on rising edge */  \
  false,                        /* Don't wake from EM4H on falling edge */ \
  true                          /* Enable VMON channel */                  \
}
#endif /* EMU_STATUS_VMONRDY */

/*******************************************************************************
 *****************************   PROTOTYPES   **********************************
 ******************************************************************************/

/***************************************************************************//**
 * @brief
 *   Enter energy mode 1 (EM1).
 ******************************************************************************/
__STATIC_INLINE void EMU_EnterEM1(void)
{
  /* Enter sleep mode */
  SCB->SCR &= ~SCB_SCR_SLEEPDEEP_Msk;
  __WFI();
}

void EMU_EM23Init(EMU_EM23Init_TypeDef *em23Init);
#if defined( _EMU_EM4CONF_MASK ) || defined( _EMU_EM4CTRL_MASK )
void EMU_EM4Init(EMU_EM4Init_TypeDef *em4Init);
#endif
void EMU_EnterEM2(bool restore);
void EMU_EnterEM3(bool restore);
void EMU_EnterEM4(void);
void EMU_MemPwrDown(uint32_t blocks);
void EMU_UpdateOscConfig(void);
#if defined( BU_PRESENT )
void EMU_BUPDInit(EMU_BUPDInit_TypeDef *bupdInit);
void EMU_BUThresholdSet(EMU_BODMode_TypeDef mode, uint32_t value);
void EMU_BUThresRangeSet(EMU_BODMode_TypeDef mode, uint32_t value);
#endif
#if defined( _EMU_DCDCCTRL_MASK )
bool EMU_DCDCInit(EMU_DCDCInit_TypeDef *dcdcInit);
void EMU_DCDCModeSet(EMU_DcdcMode_TypeDef dcdcMode);
bool EMU_DCDCOutputVoltageSet(uint32_t mV, bool setLpVoltage, bool setLnVoltage);
void EMU_DCDCOptimizeSlice(uint32_t mALoadCurrent);
void EMU_DCDCLnRcoBandSet(EMU_DcdcLnRcoBand_TypeDef band);
bool EMU_DCDCPowerOff(void);
#endif
#if defined( EMU_STATUS_VMONRDY )
void EMU_VmonInit(EMU_VmonInit_TypeDef *vmonInit);
void EMU_VmonHystInit(EMU_VmonHystInit_TypeDef *vmonInit);
void EMU_VmonEnable(EMU_VmonChannel_TypeDef channel, bool enable);
bool EMU_VmonChannelStatusGet(EMU_VmonChannel_TypeDef channel);

/***************************************************************************//**
 * @brief
 *   Get the status of the voltage monitor (VMON).
 *
 * @return
 *   Status of the VMON. True if all the enabled channels are ready, false if
 *   one or more of the enabled channels are not ready.
 ******************************************************************************/
__STATIC_INLINE bool EMU_VmonStatusGet(void)
{
  return BUS_RegBitRead(&EMU->STATUS, _EMU_STATUS_VMONRDY_SHIFT);
}
#endif /* EMU_STATUS_VMONRDY */

#if defined( _EMU_IF_MASK )
/***************************************************************************//**
 * @brief
 *   Clear one or more pending EMU interrupts.
 *
 * @param[in] flags
 *   Pending EMU interrupt sources to clear. Use one or more valid
 *   interrupt flags for the EMU module (EMU_IFC_nnn).
 ******************************************************************************/
__STATIC_INLINE void EMU_IntClear(uint32_t flags)
{
  EMU->IFC = flags;
}


/***************************************************************************//**
 * @brief
 *   Disable one or more EMU interrupts.
 *
 * @param[in] flags
 *   EMU interrupt sources to disable. Use one or more valid
 *   interrupt flags for the EMU module (EMU_IEN_nnn).
 ******************************************************************************/
__STATIC_INLINE void EMU_IntDisable(uint32_t flags)
{
  EMU->IEN &= ~flags;
}


/***************************************************************************//**
 * @brief
 *   Enable one or more EMU interrupts.
 *
 * @note
 *   Depending on the use, a pending interrupt may already be set prior to
 *   enabling the interrupt. Consider using EMU_IntClear() prior to enabling
 *   if such a pending interrupt should be ignored.
 *
 * @param[in] flags
 *   EMU interrupt sources to enable. Use one or more valid
 *   interrupt flags for the EMU module (EMU_IEN_nnn).
 ******************************************************************************/
__STATIC_INLINE void EMU_IntEnable(uint32_t flags)
{
  EMU->IEN |= flags;
}


/***************************************************************************//**
 * @brief
 *   Get pending EMU interrupt flags.
 *
 * @note
 *   The event bits are not cleared by the use of this function.
 *
 * @return
 *   EMU interrupt sources pending. Returns one or more valid
 *   interrupt flags for the EMU module (EMU_IF_nnn).
 ******************************************************************************/
__STATIC_INLINE uint32_t EMU_IntGet(void)
{
  return EMU->IF;
}


/***************************************************************************//**
 * @brief
 *   Get enabled and pending EMU interrupt flags.
 *   Useful for handling more interrupt sources in the same interrupt handler.
 *
 * @note
 *   Interrupt flags are not cleared by the use of this function.
 *
 * @return
 *   Pending and enabled EMU interrupt sources
 *   The return value is the bitwise AND of
 *   - the enabled interrupt sources in EMU_IEN and
 *   - the pending interrupt flags EMU_IF
 ******************************************************************************/
__STATIC_INLINE uint32_t EMU_IntGetEnabled(void)
{
  uint32_t ien;

  ien = EMU->IEN;
  return EMU->IF & ien;
}


/***************************************************************************//**
 * @brief
 *   Set one or more pending EMU interrupts
 *
 * @param[in] flags
 *   EMU interrupt sources to set to pending. Use one or more valid
 *   interrupt flags for the EMU module (EMU_IFS_nnn).
 ******************************************************************************/
__STATIC_INLINE void EMU_IntSet(uint32_t flags)
{
  EMU->IFS = flags;
}
#endif /* _EMU_IF_MASK */


#if defined( _EMU_EM4CONF_LOCKCONF_MASK )
/***************************************************************************//**
 * @brief
 *   Enable or disable EM4 lock configuration
 * @param[in] enable
 *   If true, locks down EM4 configuration
 ******************************************************************************/
__STATIC_INLINE void EMU_EM4Lock(bool enable)
{
  BUS_RegBitWrite(&(EMU->EM4CONF), _EMU_EM4CONF_LOCKCONF_SHIFT, enable);
}
#endif

#if defined( _EMU_STATUS_BURDY_MASK )
/***************************************************************************//**
 * @brief
 *   Halts until backup power functionality is ready
 ******************************************************************************/
__STATIC_INLINE void EMU_BUReady(void)
{
  while(!(EMU->STATUS & EMU_STATUS_BURDY))
    ;
}
#endif

#if defined( _EMU_ROUTE_BUVINPEN_MASK )
/***************************************************************************//**
 * @brief
 *   Disable BU_VIN support
 * @param[in] enable
 *   If true, enables BU_VIN input pin support, if false disables it
 ******************************************************************************/
__STATIC_INLINE void EMU_BUPinEnable(bool enable)
{
  BUS_RegBitWrite(&(EMU->ROUTE), _EMU_ROUTE_BUVINPEN_SHIFT, enable);
}
#endif

/***************************************************************************//**
 * @brief
 *   Lock the EMU in order to protect its registers against unintended
 *   modification.
 *
 * @note
 *   If locking the EMU registers, they must be unlocked prior to using any
 *   EMU API functions modifying EMU registers, excluding interrupt control
 *   and regulator control if the architecture has a EMU_PWRCTRL register.
 *   An exception to this is the energy mode entering API (EMU_EnterEMn()),
 *   which can be used when the EMU registers are locked.
 ******************************************************************************/
__STATIC_INLINE void EMU_Lock(void)
{
  EMU->LOCK = EMU_LOCK_LOCKKEY_LOCK;
}


/***************************************************************************//**
 * @brief
 *   Unlock the EMU so that writing to locked registers again is possible.
 ******************************************************************************/
__STATIC_INLINE void EMU_Unlock(void)
{
  EMU->LOCK = EMU_LOCK_LOCKKEY_UNLOCK;
}


#if defined( _EMU_PWRLOCK_MASK )
/***************************************************************************//**
 * @brief
 *   Lock the EMU regulator control registers in order to protect against
 *   unintended modification.
 ******************************************************************************/
__STATIC_INLINE void EMU_PowerLock(void)
{
  EMU->PWRLOCK = EMU_PWRLOCK_LOCKKEY_LOCK;
}


/***************************************************************************//**
 * @brief
 *   Unlock the EMU power control registers so that writing to
 *   locked registers again is possible.
 ******************************************************************************/
__STATIC_INLINE void EMU_PowerUnlock(void)
{
  EMU->PWRLOCK = EMU_PWRLOCK_LOCKKEY_UNLOCK;
}
#endif


/***************************************************************************//**
 * @brief
 *   Block entering EM2 or higher number energy modes.
 ******************************************************************************/
__STATIC_INLINE void EMU_EM2Block(void)
{
  BUS_RegBitWrite(&(EMU->CTRL), _EMU_CTRL_EM2BLOCK_SHIFT, 1U);
}

/***************************************************************************//**
 * @brief
 *   Unblock entering EM2 or higher number energy modes.
 ******************************************************************************/
__STATIC_INLINE void EMU_EM2UnBlock(void)
{
  BUS_RegBitWrite(&(EMU->CTRL), _EMU_CTRL_EM2BLOCK_SHIFT, 0U);
}

#if defined( _EMU_EM4CTRL_EM4IORETMODE_MASK )
/***************************************************************************//**
 * @brief
 *   When EM4 pin retention is set to emuPinRetentionLatch, then pins are retained
 *   through EM4 entry and wakeup. The pin state is released by calling this function.
 *   The feature allows peripherals or GPIO to be re-initialized after EM4 exit (reset),
 *   and when the initialization is done, this function can release pins and return control
 *   to the peripherals or GPIO.
 ******************************************************************************/
__STATIC_INLINE void EMU_UnlatchPinRetention(void)
{
  EMU->CMD = EMU_CMD_EM4UNLATCH;
}
#endif

/** @} (end addtogroup EMU) */
/** @} (end addtogroup EM_Library) */

#ifdef __cplusplus
}
#endif

#endif /* defined( EMU_PRESENT ) */
#endif /* __SILICON_LABS_EM_EMU_H__ */
