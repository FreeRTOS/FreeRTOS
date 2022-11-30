/**
  ******************************************************************************
  * @file    stm32h7xx_hal_pwr_ex.h
  * @author  MCD Application Team
  * @brief   Header file of PWR HAL Extension module.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2017 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef STM32H7xx_HAL_PWR_EX_H
#define STM32H7xx_HAL_PWR_EX_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32h7xx_hal_def.h"

/** @addtogroup STM32H7xx_HAL_Driver
  * @{
  */

/** @addtogroup PWREx
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/** @defgroup PWREx_Exported_Types PWREx Exported Types
  * @{
  */
/**
  * @brief  PWREx AVD configuration structure definition
  */
typedef struct
{
  uint32_t AVDLevel;       /*!< AVDLevel: Specifies the AVD detection level.
                                 This parameter can be a value of @ref PWREx_AVD_detection_level */

  uint32_t Mode;            /*!< Mode: Specifies the operating mode for the selected pins.
                                  This parameter can be a value of @ref PWREx_AVD_Mode */
}PWREx_AVDTypeDef;

/**
  * @brief  PWREx Wakeup pin configuration structure definition
  */
typedef struct
{
  uint32_t WakeUpPin;     /*!< WakeUpPin: Specifies the Wake-Up pin to be enabled.
                                This parameter can be a value of @ref PWREx_WakeUp_Pins */

  uint32_t PinPolarity;   /*!< PinPolarity: Specifies the Wake-Up pin polarity.
                                This parameter can be a value of @ref PWREx_PIN_Polarity */

  uint32_t PinPull;       /*!< PinPull: Specifies the Wake-Up pin pull.
                                This parameter can be a value of @ref PWREx_PIN_Pull */
}PWREx_WakeupPinTypeDef;

/**
  * @}
  */
/* Exported constants --------------------------------------------------------*/

/** @defgroup PWREx_Exported_Constants PWREx Exported Constants
  * @{
  */
/** @defgroup PWREx_WakeUp_Pins PWREx Wake-Up Pins
  * @{
  */
#define PWR_WAKEUP_PIN6  PWR_WKUPEPR_WKUPEN6
#define PWR_WAKEUP_PIN5  PWR_WKUPEPR_WKUPEN5
#define PWR_WAKEUP_PIN4  PWR_WKUPEPR_WKUPEN4
#define PWR_WAKEUP_PIN3  PWR_WKUPEPR_WKUPEN3
#define PWR_WAKEUP_PIN2  PWR_WKUPEPR_WKUPEN2
#define PWR_WAKEUP_PIN1  PWR_WKUPEPR_WKUPEN1
/* High level and No pull */
#define PWR_WAKEUP_PIN6_HIGH  PWR_WKUPEPR_WKUPEN6
#define PWR_WAKEUP_PIN5_HIGH  PWR_WKUPEPR_WKUPEN5
#define PWR_WAKEUP_PIN4_HIGH  PWR_WKUPEPR_WKUPEN4
#define PWR_WAKEUP_PIN3_HIGH  PWR_WKUPEPR_WKUPEN3
#define PWR_WAKEUP_PIN2_HIGH  PWR_WKUPEPR_WKUPEN2
#define PWR_WAKEUP_PIN1_HIGH  PWR_WKUPEPR_WKUPEN1
/* Low level and No pull */
#define PWR_WAKEUP_PIN6_LOW  (uint32_t)(PWR_WKUPEPR_WKUPP6 | PWR_WKUPEPR_WKUPEN6)
#define PWR_WAKEUP_PIN5_LOW  (uint32_t)(PWR_WKUPEPR_WKUPP5 | PWR_WKUPEPR_WKUPEN5)
#define PWR_WAKEUP_PIN4_LOW  (uint32_t)(PWR_WKUPEPR_WKUPP4 | PWR_WKUPEPR_WKUPEN4)
#define PWR_WAKEUP_PIN3_LOW  (uint32_t)(PWR_WKUPEPR_WKUPP3 | PWR_WKUPEPR_WKUPEN3)
#define PWR_WAKEUP_PIN2_LOW  (uint32_t)(PWR_WKUPEPR_WKUPP2 | PWR_WKUPEPR_WKUPEN2)
#define PWR_WAKEUP_PIN1_LOW  (uint32_t)(PWR_WKUPEPR_WKUPP1 | PWR_WKUPEPR_WKUPEN1)
/**
  * @}
  */

/** @defgroup PWREx_PIN_Polarity PWREx Pin Polarity configuration
  * @{
  */
#define PWR_PIN_POLARITY_HIGH  ((uint32_t)0x00000000U)
#define PWR_PIN_POLARITY_LOW   ((uint32_t)0x00000001U)
/**
  * @}
  */

/** @defgroup PWREx_PIN_Pull PWREx Pin Pull configuration
  * @{
  */
#define PWR_PIN_NO_PULL    ((uint32_t)0x00000000U)
#define PWR_PIN_PULL_UP    ((uint32_t)0x00000001U)
#define PWR_PIN_PULL_DOWN  ((uint32_t)0x00000002U)
/**
  * @}
  */


/** @defgroup PWREx_Wakeup_Pins_Flags PWREx Wakeup Pins Flags.
  * @{
  */
#define PWR_WAKEUP_FLAG1  PWR_WKUPFR_WKUPF1 /*!< Wakeup event on pin 1 */
#define PWR_WAKEUP_FLAG2  PWR_WKUPFR_WKUPF2 /*!< Wakeup event on pin 2 */
#define PWR_WAKEUP_FLAG3  PWR_WKUPFR_WKUPF3 /*!< Wakeup event on pin 3 */
#define PWR_WAKEUP_FLAG4  PWR_WKUPFR_WKUPF4 /*!< Wakeup event on pin 4 */
#define PWR_WAKEUP_FLAG5  PWR_WKUPFR_WKUPF5 /*!< Wakeup event on pin 5 */
#define PWR_WAKEUP_FLAG6  PWR_WKUPFR_WKUPF6 /*!< Wakeup event on pin 6 */
/**
  * @}
  */

#if defined(DUAL_CORE)
/** @defgroup PWREx_Core_Select PWREx Core definition
  * @{
  */
#define PWR_CORE_CPU1  ((uint32_t)0x00000000U)
#define PWR_CORE_CPU2  ((uint32_t)0x00000001U)
/**
  * @}
  */
#endif /*DUAL_CORE*/

/** @defgroup PWREx_Domains PWREx Domains definition
  * @{
  */
#define PWR_D1_DOMAIN  ((uint32_t)0x00000000U)
#define PWR_D2_DOMAIN  ((uint32_t)0x00000001U)
#define PWR_D3_DOMAIN  ((uint32_t)0x00000002U)
/**
  * @}
  */

/** @defgroup PWREx_Domain_Flags PWREx Domain Flags definition
  * @{
  */
#if defined(DUAL_CORE)
#define PWR_D1_DOMAIN_FLAGS  ((uint32_t)0x00000000U)
#define PWR_D2_DOMAIN_FLAGS  ((uint32_t)0x00000001U)
#else
#define PWR_CPU_FLAGS        ((uint32_t)0x00000000U)
#endif /*DUAL_CORE*/
/**
  * @}
  */

/** @defgroup PWREx_D3_State PWREx D3 Domain State
  * @{
  */
#define PWR_D3_DOMAIN_STOP  ((uint32_t)0x00000000U)
#define PWR_D3_DOMAIN_RUN   ((uint32_t)0x00000800U)

/**
  * @}
  */

/** @defgroup PWREx_Supply_configuration PWREx Supply configuration
  * @{
  */
#define PWR_LDO_SUPPLY                      PWR_CR3_LDOEN                                                               /*!< Core domains are suppplied from the LDO                                                                     */
#if defined(SMPS)
#define PWR_DIRECT_SMPS_SUPPLY              PWR_CR3_SMPSEN                                                              /*!< Core domains are suppplied from the SMPS only                                                               */
#define PWR_SMPS_1V8_SUPPLIES_LDO           (PWR_CR3_SMPSLEVEL_0 | PWR_CR3_SMPSEN | PWR_CR3_LDOEN)                      /*!< The SMPS 1.8V output supplies the LDO which supplies the Core domains                                       */
#define PWR_SMPS_2V5_SUPPLIES_LDO           (PWR_CR3_SMPSLEVEL_1 | PWR_CR3_SMPSEN | PWR_CR3_LDOEN)                      /*!< The SMPS 2.5V output supplies the LDO which supplies the Core domains                                       */
#define PWR_SMPS_1V8_SUPPLIES_EXT_AND_LDO   (PWR_CR3_SMPSLEVEL_0 | PWR_CR3_SMPSEXTHP | PWR_CR3_SMPSEN | PWR_CR3_LDOEN)  /*!< The SMPS 1.8V output supplies an external circuits and the LDO. The Core domains are suppplied from the LDO */
#define PWR_SMPS_2V5_SUPPLIES_EXT_AND_LDO   (PWR_CR3_SMPSLEVEL_1 | PWR_CR3_SMPSEXTHP | PWR_CR3_SMPSEN | PWR_CR3_LDOEN)  /*!< The SMPS 2.5V output supplies an external circuits and the LDO. The Core domains are suppplied from the LDO */
#define PWR_SMPS_1V8_SUPPLIES_EXT           (PWR_CR3_SMPSLEVEL_0 | PWR_CR3_SMPSEXTHP | PWR_CR3_SMPSEN | PWR_CR3_BYPASS) /*!< The SMPS 1.8V output supplies an external source which supplies the Core domains                            */
#define PWR_SMPS_2V5_SUPPLIES_EXT           (PWR_CR3_SMPSLEVEL_1 | PWR_CR3_SMPSEXTHP | PWR_CR3_SMPSEN | PWR_CR3_BYPASS) /*!< The SMPS 2.5V output supplies an external source which supplies the Core domains                            */
#endif /* SMPS */
#define PWR_EXTERNAL_SOURCE_SUPPLY          PWR_CR3_BYPASS                                                              /*!< The SMPS disabled and the LDO Bypass. The Core domains are supplied from an external source                 */

#if defined(SMPS)
#define PWR_SUPPLY_CONFIG_MASK               (PWR_CR3_SMPSLEVEL | PWR_CR3_SMPSEXTHP | \
                                              PWR_CR3_SMPSEN | PWR_CR3_LDOEN | PWR_CR3_BYPASS)
#else
#define PWR_SUPPLY_CONFIG_MASK               (PWR_CR3_SCUEN | PWR_CR3_LDOEN | PWR_CR3_BYPASS)
#endif /* SMPS */
/**
  * @}
  */


/** @defgroup PWREx_AVD_detection_level PWREx AVD detection level
  * @{
  */
#define PWR_AVDLEVEL_0  PWR_CR1_ALS_LEV0
#define PWR_AVDLEVEL_1  PWR_CR1_ALS_LEV1
#define PWR_AVDLEVEL_2  PWR_CR1_ALS_LEV2
#define PWR_AVDLEVEL_3  PWR_CR1_ALS_LEV3
/**
  * @}
  */

/** @defgroup PWREx_AVD_Mode PWREx AVD Mode
  * @{
  */
#define PWR_AVD_MODE_NORMAL                ((uint32_t)0x00000000U)   /*!< Basic mode is used                                                 */
#define PWR_AVD_MODE_IT_RISING             ((uint32_t)0x00010001U)   /*!< External Interrupt Mode with Rising edge trigger detection         */
#define PWR_AVD_MODE_IT_FALLING            ((uint32_t)0x00010002U)   /*!< External Interrupt Mode with Falling edge trigger detection        */
#define PWR_AVD_MODE_IT_RISING_FALLING     ((uint32_t)0x00010003U)   /*!< External Interrupt Mode with Rising/Falling edge trigger detection */
#define PWR_AVD_MODE_EVENT_RISING          ((uint32_t)0x00020001U)   /*!< Event Mode with Rising edge trigger detection                      */
#define PWR_AVD_MODE_EVENT_FALLING         ((uint32_t)0x00020002U)   /*!< Event Mode with Falling edge trigger detection                     */
#define PWR_AVD_MODE_EVENT_RISING_FALLING  ((uint32_t)0x00020003U)   /*!< Event Mode with Rising/Falling edge trigger detection              */
/**
  * @}
  */

/** @defgroup PWREx_Regulator_Voltage_Scale PWREx Regulator Voltage Scale
  * @{
  */
#define PWR_REGULATOR_SVOS_SCALE5  (PWR_CR1_SVOS_0)
#define PWR_REGULATOR_SVOS_SCALE4  (PWR_CR1_SVOS_1)
#define PWR_REGULATOR_SVOS_SCALE3  (uint32_t)(PWR_CR1_SVOS_0 | PWR_CR1_SVOS_1)
/**
  * @}
  */

/** @defgroup PWREx_VBAT_Battery_Charging_Resistor PWR battery charging resistor selection
  * @{
  */
#define PWR_BATTERY_CHARGING_RESISTOR_5    ((uint32_t)0x00000000U) /*!< VBAT charging through a 5 kOhms resistor   */
#define PWR_BATTERY_CHARGING_RESISTOR_1_5  PWR_CR3_VBRS            /*!< VBAT charging through a 1.5 kOhms resistor */
/**
  * @}
  */

/** @defgroup PWREx_VBAT_Thresholds PWREx VBAT Thresholds
  * @{
  */
#define PWR_VBAT_BETWEEN_HIGH_LOW_THRESHOLD  ((uint32_t)0x00000000U)
#define PWR_VBAT_BELOW_LOW_THRESHOLD         PWR_CR2_VBATL
#define PWR_VBAT_ABOVE_HIGH_THRESHOLD        PWR_CR2_VBATH
/**
  * @}
  */

/** @defgroup PWREx_TEMP_Thresholds PWREx Temperature Thresholds
  * @{
  */
#define PWR_TEMP_BETWEEN_HIGH_LOW_THRESHOLD  ((uint32_t)0x00000000U)
#define PWR_TEMP_BELOW_LOW_THRESHOLD         PWR_CR2_TEMPL
#define PWR_TEMP_ABOVE_HIGH_THRESHOLD        PWR_CR2_TEMPH
/**
  * @}
  */
/** @defgroup PWREx_AVD_EXTI_Line PWREx AVD EXTI Line 16
  * @{
  */
#define PWR_EXTI_LINE_AVD  ((uint32_t)EXTI_IMR1_IM16) /*!< External interrupt line 16 Connected to the AVD EXTI Line */
/**
  * @}
  */
/**
  * @}
  */
/* Exported macro ------------------------------------------------------------*/
/** @defgroup PWREx_Exported_Macro PWREx Exported Macro
  *  @{
  */

/**
  * @brief Enable the AVD EXTI Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_ENABLE_IT()  SET_BIT(EXTI->IMR1, PWR_EXTI_LINE_AVD)

#if defined(DUAL_CORE)
/**
  * @brief Enable the AVD EXTI D2 Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTID2_ENABLE_IT()  SET_BIT(EXTI_D2->IMR1, PWR_EXTI_LINE_AVD)
#endif /*DUAL_CORE*/

/**
  * @brief Disable the AVD EXTI Line 16
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_DISABLE_IT()  CLEAR_BIT(EXTI->IMR1, PWR_EXTI_LINE_AVD)

#if defined(DUAL_CORE)
/**
  * @brief Disable the AVD EXTI D2 Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTID2_DISABLE_IT()  CLEAR_BIT(EXTI_D2->IMR1, PWR_EXTI_LINE_AVD)
#endif /*DUAL_CORE*/

/**
  * @brief   Enable event on AVD EXTI Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_ENABLE_EVENT()  SET_BIT(EXTI->EMR1, PWR_EXTI_LINE_AVD)

#if defined(DUAL_CORE)
/**
  * @brief   Enable event on AVD EXTI D2 Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTID2_ENABLE_EVENT()  SET_BIT(EXTI_D2->EMR1, PWR_EXTI_LINE_AVD)
#endif /*DUAL_CORE*/

/**
  * @brief   Disable event on AVD EXTI Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_DISABLE_EVENT()  CLEAR_BIT(EXTI->EMR1, PWR_EXTI_LINE_AVD)

#if defined(DUAL_CORE)
/**
  * @brief   Disable event on AVD EXTI D2 Line 16.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTID2_DISABLE_EVENT()  CLEAR_BIT(EXTI_D2->EMR1, PWR_EXTI_LINE_AVD)
#endif /*DUAL_CORE*/

/**
  * @brief  Enable the AVD Extended Interrupt Rising Trigger.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_ENABLE_RISING_EDGE()  SET_BIT(EXTI->RTSR1, PWR_EXTI_LINE_AVD)

/**
  * @brief  Disable the AVD Extended Interrupt Rising Trigger.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_DISABLE_RISING_EDGE()  CLEAR_BIT(EXTI->RTSR1, PWR_EXTI_LINE_AVD)

/**
  * @brief  Enable the AVD Extended Interrupt Falling Trigger.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_ENABLE_FALLING_EDGE()  SET_BIT(EXTI->FTSR1, PWR_EXTI_LINE_AVD)


/**
  * @brief  Disable the AVD Extended Interrupt Falling Trigger.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_DISABLE_FALLING_EDGE()  CLEAR_BIT(EXTI->FTSR1, PWR_EXTI_LINE_AVD)


/**
  * @brief  AVD EXTI line configuration: set rising & falling edge trigger.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_ENABLE_RISING_FALLING_EDGE()  do { \
  __HAL_PWR_AVD_EXTI_ENABLE_RISING_EDGE(); \
  __HAL_PWR_AVD_EXTI_ENABLE_FALLING_EDGE(); \
} while(0);

/**
  * @brief  Disable the AVD Extended Interrupt Rising & Falling Trigger.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_DISABLE_RISING_FALLING_EDGE()  \
do { \
  __HAL_PWR_AVD_EXTI_DISABLE_RISING_EDGE(); \
  __HAL_PWR_AVD_EXTI_DISABLE_FALLING_EDGE(); \
} while(0);

/**
  * @brief  Check whether the specified AVD EXTI interrupt flag is set or not.
  * @retval EXTI AVD Line Status.
  */
#define __HAL_PWR_AVD_EXTI_GET_FLAG()  ((READ_BIT(EXTI->PR1, PWR_EXTI_LINE_AVD) == PWR_EXTI_LINE_AVD) ? SET : RESET)

#if defined(DUAL_CORE)
/**
  * @brief  Check whether the specified AVD EXTI D2 interrupt flag is set or not.
  * @retval EXTI D2 AVD Line Status.
  */
#define __HAL_PWR_AVD_EXTID2_GET_FLAG()  ((READ_BIT(EXTI_D2->PR1, PWR_EXTI_LINE_AVD) == PWR_EXTI_LINE_AVD) ? SET : RESET)
#endif /*DUAL_CORE*/

/**
  * @brief  Clear the AVD EXTI flag.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTI_CLEAR_FLAG()  SET_BIT(EXTI->PR1, PWR_EXTI_LINE_AVD)

#if defined(DUAL_CORE)
/**
  * @brief  Clear the AVD EXTI D2 flag.
  * @retval None.
  */
#define __HAL_PWR_AVD_EXTID2_CLEAR_FLAG()  SET_BIT(EXTI_D2->PR1, PWR_EXTI_LINE_AVD)
#endif /*DUAL_CORE*/

/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @addtogroup PWREx_Exported_Functions PWREx Exported Functions
  * @{
  */

/** @addtogroup PWREx_Exported_Functions_Group1 Power supply control functions
  * @{
  */
/* Power supply control functions */
HAL_StatusTypeDef HAL_PWREx_ConfigSupply(uint32_t SupplySource);
uint32_t HAL_PWREx_GetSupplyConfig(void);
/* Power volatge scaling functions */
HAL_StatusTypeDef HAL_PWREx_ControlVoltageScaling(uint32_t VoltageScaling);
uint32_t HAL_PWREx_GetVoltageRange(void);
HAL_StatusTypeDef HAL_PWREx_ControlStopModeVoltageScaling(uint32_t VoltageScaling);
uint32_t HAL_PWREx_GetStopModeVoltageRange(void);
/**
  * @}
  */

/** @addtogroup PWREx_Exported_Functions_Group2 Low power control functions
  * @{
  */
/* System low power control functions */
void HAL_PWREx_EnterSTOPMode(uint32_t Regulator, uint8_t STOPEntry, uint32_t Domain);
void HAL_PWREx_EnterSTANDBYMode(uint32_t Domain);
void HAL_PWREx_ConfigD3Domain(uint32_t D3State);

#if defined(DUAL_CORE)
void HAL_PWREx_ClearDomainFlags(uint32_t DomainFlags);

/* Power core holding functions */
HAL_StatusTypeDef HAL_PWREx_HoldCore(uint32_t CPU);
void HAL_PWREx_ReleaseCore(uint32_t CPU);

#endif /*DUAL_CORE*/

/* Clear pending event function */
void HAL_PWREx_ClearPendingEvent(void);

/* Flash low power control functions */
void HAL_PWREx_EnableFlashPowerDown(void);
void HAL_PWREx_DisableFlashPowerDown(void);
/* Wakeup Pins control functions */
void HAL_PWREx_EnableWakeUpPin(PWREx_WakeupPinTypeDef *sPinParams);
void HAL_PWREx_DisableWakeUpPin(uint32_t WakeUpPin);
uint32_t HAL_PWREx_GetWakeupFlag(uint32_t WakeUpFlag);
HAL_StatusTypeDef HAL_PWREx_ClearWakeupFlag(uint32_t WakeUpFlag);

/* Power Wakeup PIN IRQ Handler */
void HAL_PWREx_WAKEUP_PIN_IRQHandler(void);
void HAL_PWREx_WKUP1_Callback(void);
void HAL_PWREx_WKUP2_Callback(void);
void HAL_PWREx_WKUP3_Callback(void);
void HAL_PWREx_WKUP4_Callback(void);
void HAL_PWREx_WKUP5_Callback(void);
void HAL_PWREx_WKUP6_Callback(void);
/**
  * @}
  */

/** @addtogroup PWREx_Exported_Functions_Group3 Peripherals control functions
  * @{
  */
/* Backup regulator control functions */
HAL_StatusTypeDef HAL_PWREx_EnableBkUpReg(void);
HAL_StatusTypeDef HAL_PWREx_DisableBkUpReg(void);

/* USB regulator control functions */
HAL_StatusTypeDef HAL_PWREx_EnableUSBReg(void);
HAL_StatusTypeDef HAL_PWREx_DisableUSBReg(void);
void HAL_PWREx_EnableUSBVoltageDetector(void);
void HAL_PWREx_DisableUSBVoltageDetector(void);

/* Battery control functions */
void HAL_PWREx_EnableBatteryCharging(uint32_t ResistorValue);
void HAL_PWREx_DisableBatteryCharging(void);
/**
  * @}
  */

/** @addtogroup PWREx_Exported_Functions_Group4 Power Monitoring functions
  * @{
  */
/* Power VBAT/Temperature monitoring functions */
void HAL_PWREx_EnableMonitoring(void);
void HAL_PWREx_DisableMonitoring(void);
uint32_t HAL_PWREx_GetTemperatureLevel(void);
uint32_t HAL_PWREx_GetVBATLevel(void);

/* Power AVD configuration functions */
void HAL_PWREx_ConfigAVD(PWREx_AVDTypeDef *sConfigAVD);
void HAL_PWREx_EnableAVD(void);
void HAL_PWREx_DisableAVD(void);

/* Power PVD/AVD IRQ Handler */
void HAL_PWREx_PVD_AVD_IRQHandler(void);
void HAL_PWREx_AVDCallback(void);

/**
  * @}
  */

/**
  * @}
  */
/* Private types -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private constants ---------------------------------------------------------*/
/* Private macros ------------------------------------------------------------*/
/** @defgroup PWREx_Private_Macros PWREx Private Macros
  * @{
  */

/** @defgroup PWREx_IS_PWR_Definitions PWREx Private macros to check input parameters
  * @{
  */
#if defined(SMPS)
#define IS_PWR_SUPPLY(PWR_SOURCE)  (((PWR_SOURCE) == PWR_LDO_SUPPLY)                    || \
                                    ((PWR_SOURCE) == PWR_DIRECT_SMPS_SUPPLY)            || \
                                    ((PWR_SOURCE) == PWR_SMPS_1V8_SUPPLIES_LDO)         || \
                                    ((PWR_SOURCE) == PWR_SMPS_2V5_SUPPLIES_LDO)         || \
                                    ((PWR_SOURCE) == PWR_SMPS_1V8_SUPPLIES_EXT_AND_LDO) || \
                                    ((PWR_SOURCE) == PWR_SMPS_2V5_SUPPLIES_EXT_AND_LDO) || \
                                    ((PWR_SOURCE) == PWR_SMPS_1V8_SUPPLIES_EXT)         || \
                                    ((PWR_SOURCE) == PWR_SMPS_2V5_SUPPLIES_EXT)         || \
                                    ((PWR_SOURCE) == PWR_EXTERNAL_SOURCE_SUPPLY))

#else
#define IS_PWR_SUPPLY(PWR_SOURCE)  (((PWR_SOURCE) == PWR_LDO_SUPPLY) || \
                                    ((PWR_SOURCE) == PWR_EXTERNAL_SOURCE_SUPPLY))
#endif /*SMPS*/

#define IS_PWR_STOP_MODE_REGULATOR_VOLTAGE(VOLTAGE)  (((VOLTAGE) == PWR_REGULATOR_SVOS_SCALE3)  || \
                                                      ((VOLTAGE) == PWR_REGULATOR_SVOS_SCALE4)  || \
                                                      ((VOLTAGE) == PWR_REGULATOR_SVOS_SCALE5))

#define IS_PWR_DOMAIN(DOMAIN)  (((DOMAIN) == PWR_D1_DOMAIN) || \
                                ((DOMAIN) == PWR_D2_DOMAIN) || \
                                ((DOMAIN) == PWR_D3_DOMAIN))

#define IS_D3_STATE(STATE)  (((STATE) == PWR_D3_DOMAIN_STOP) || ((STATE) == PWR_D3_DOMAIN_RUN))

#define IS_PWR_WAKEUP_PIN(PIN)  (((PIN) == PWR_WAKEUP_PIN1)       || \
                                 ((PIN) == PWR_WAKEUP_PIN2)       || \
                                 ((PIN) == PWR_WAKEUP_PIN3)       || \
                                 ((PIN) == PWR_WAKEUP_PIN4)       || \
                                 ((PIN) == PWR_WAKEUP_PIN5)       || \
                                 ((PIN) == PWR_WAKEUP_PIN6)       || \
                                 ((PIN) == PWR_WAKEUP_PIN1_HIGH)  || \
                                 ((PIN) == PWR_WAKEUP_PIN2_HIGH)  || \
                                 ((PIN) == PWR_WAKEUP_PIN3_HIGH)  || \
                                 ((PIN) == PWR_WAKEUP_PIN4_HIGH)  || \
                                 ((PIN) == PWR_WAKEUP_PIN5_HIGH)  || \
                                 ((PIN) == PWR_WAKEUP_PIN6_HIGH)  || \
                                 ((PIN) == PWR_WAKEUP_PIN1_LOW)   || \
                                 ((PIN) == PWR_WAKEUP_PIN2_LOW)   || \
                                 ((PIN) == PWR_WAKEUP_PIN3_LOW)   || \
                                 ((PIN) == PWR_WAKEUP_PIN4_LOW)   || \
                                 ((PIN) == PWR_WAKEUP_PIN5_LOW)    || \
                                 ((PIN) == PWR_WAKEUP_PIN6_LOW))

#define IS_PWR_WAKEUP_PIN_POLARITY(POLARITY)  (((POLARITY) == PWR_PIN_POLARITY_HIGH) || \
                                               ((POLARITY) == PWR_PIN_POLARITY_LOW))

#define IS_PWR_WAKEUP_PIN_PULL(PULL)  (((PULL) == PWR_PIN_NO_PULL)  || \
                                       ((PULL) == PWR_PIN_PULL_UP)  || \
                                       ((PULL) == PWR_PIN_PULL_DOWN))

#define IS_PWR_WAKEUP_FLAG(FLAG)  (((FLAG) == PWR_WAKEUP_FLAG1)  || \
                                   ((FLAG) == PWR_WAKEUP_FLAG2)  || \
                                   ((FLAG) == PWR_WAKEUP_FLAG3)  || \
                                   ((FLAG) == PWR_WAKEUP_FLAG4)  || \
                                   ((FLAG) == PWR_WAKEUP_FLAG5)  || \
                                   ((FLAG) == PWR_WAKEUP_FLAG6))

#define IS_PWR_AVD_LEVEL(LEVEL)  (((LEVEL) == PWR_AVDLEVEL_0) || ((LEVEL) == PWR_AVDLEVEL_1) || \
                                  ((LEVEL) == PWR_AVDLEVEL_2) || ((LEVEL) == PWR_AVDLEVEL_3))

#define IS_PWR_AVD_MODE(MODE)  (((MODE) == PWR_AVD_MODE_IT_RISING)|| ((MODE) == PWR_AVD_MODE_IT_FALLING) || \
                                ((MODE) == PWR_AVD_MODE_IT_RISING_FALLING) || ((MODE) == PWR_AVD_MODE_EVENT_RISING) || \
                                ((MODE) == PWR_AVD_MODE_EVENT_FALLING) || ((MODE) == PWR_AVD_MODE_EVENT_RISING_FALLING) || \
                                ((MODE) == PWR_AVD_MODE_NORMAL))

#define IS_PWR_BATTERY_RESISTOR_SELECT(RESISTOR)  (((RESISTOR) == PWR_BATTERY_CHARGING_RESISTOR_5) ||\
                                                   ((RESISTOR) == PWR_BATTERY_CHARGING_RESISTOR_1_5))

#define IS_PWR_D1_CPU(CPU) ((CPU) == CM7_CPUID)

#if defined(DUAL_CORE)
#define IS_PWR_CORE(CPU)  (((CPU) == PWR_CORE_CPU1) || ((CPU) == PWR_CORE_CPU2))

#define IS_PWR_D2_CPU(CPU) ((CPU) == CM4_CPUID)

#define IS_PWR_DOMAIN_FLAG(FLAG)  (((FLAG) == PWR_D1_DOMAIN_FLAGS) || \
                                   ((FLAG) == PWR_D2_DOMAIN_FLAGS))
#endif /*DUAL_CORE*/

/**
  * @}
  */
/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */
#ifdef __cplusplus
}
#endif


#endif /* STM32H7xx_HAL_PWR_EX_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
