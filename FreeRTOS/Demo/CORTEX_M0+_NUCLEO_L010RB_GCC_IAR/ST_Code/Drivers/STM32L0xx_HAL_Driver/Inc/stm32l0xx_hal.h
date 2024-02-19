/**
  ******************************************************************************
  * @file    stm32l0xx_hal.h
  * @author  MCD Application Team
  * @brief   This file contains all the functions prototypes for the HAL
  *          module driver.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright (c) 2016 STMicroelectronics.
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
#ifndef __STM32L0xx_HAL_H
#define __STM32L0xx_HAL_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l0xx_hal_conf.h"

/** @addtogroup STM32L0xx_HAL_Driver
  * @{
  */

/** @defgroup HAL HAL
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/

/** @defgroup HAL_Exported_Constants HAL Exported Constants
  * @{
  */

/** @defgroup HAL_TICK_FREQ Tick Frequency
  * @{
  */
typedef enum
{
  HAL_TICK_FREQ_10HZ         = 100U,
  HAL_TICK_FREQ_100HZ        = 10U,
  HAL_TICK_FREQ_1KHZ         = 1U,
  HAL_TICK_FREQ_DEFAULT      = HAL_TICK_FREQ_1KHZ
} HAL_TickFreqTypeDef;
/**
  * @}
  */

/** @defgroup SYSCFG_BootMode Boot Mode
  * @{
  */
#define SYSCFG_BOOT_MAINFLASH          (0x00000000U)
#define SYSCFG_BOOT_SYSTEMFLASH        SYSCFG_CFGR1_BOOT_MODE_0
#define SYSCFG_BOOT_SRAM               SYSCFG_CFGR1_BOOT_MODE

/**
  * @}
  */

/** @defgroup DBGMCU_Low_Power_Config DBGMCU Low Power Configuration
  * @{
  */
#define DBGMCU_SLEEP                 DBGMCU_CR_DBG_SLEEP
#define DBGMCU_STOP                  DBGMCU_CR_DBG_STOP
#define DBGMCU_STANDBY               DBGMCU_CR_DBG_STANDBY
#define IS_DBGMCU_PERIPH(__PERIPH__) ((((__PERIPH__) & (~(DBGMCU_CR_DBG))) == 0x00U) && ((__PERIPH__) != 0x00U))


/**
  * @}
  */

#if defined (LCD_BASE) /* STM32L0x3xx only */
/** @defgroup SYSCFG_LCD_EXT_CAPA SYSCFG LCD External Capacitors
  * @{
  */
#define SYSCFG_LCD_EXT_CAPA             SYSCFG_CFGR2_CAPA /*!< Connection of internal Vlcd rail to external capacitors */
#define SYSCFG_VLCD_PB2_EXT_CAPA_ON     SYSCFG_CFGR2_CAPA_0  /*!< Connection on PB2   */
#define SYSCFG_VLCD_PB12_EXT_CAPA_ON    SYSCFG_CFGR2_CAPA_1  /*!< Connection on PB12  */
#define SYSCFG_VLCD_PB0_EXT_CAPA_ON     SYSCFG_CFGR2_CAPA_2  /*!< Connection on PB0   */
#if defined (SYSCFG_CFGR2_CAPA_3)
#define SYSCFG_VLCD_PE11_EXT_CAPA_ON    SYSCFG_CFGR2_CAPA_3  /*!< Connection on PE11  */
#endif
#if defined (SYSCFG_CFGR2_CAPA_4)
#define SYSCFG_VLCD_PE12_EXT_CAPA_ON    SYSCFG_CFGR2_CAPA_4  /*!< Connection on PE12  */
#endif

/**
  * @}
  */
#endif

/** @defgroup SYSCFG_VREFINT_OUT_SELECT SYSCFG VREFINT Out Selection
  * @{
  */
#define SYSCFG_VREFINT_OUT_NONE          (0x00000000U)           /* no pad connected */
#define SYSCFG_VREFINT_OUT_PB0           SYSCFG_CFGR3_VREF_OUT_0 /* Selects PBO as output for the Vrefint */
#define SYSCFG_VREFINT_OUT_PB1           SYSCFG_CFGR3_VREF_OUT_1 /* Selects PB1 as output for the Vrefint */
#define SYSCFG_VREFINT_OUT_PB0_PB1       SYSCFG_CFGR3_VREF_OUT   /* Selects PBO and PB1 as output for the Vrefint */

#define IS_SYSCFG_VREFINT_OUT_SELECT(OUTPUT)   (((OUTPUT) == SYSCFG_VREFINT_OUT_NONE)  || \
                                                ((OUTPUT) == SYSCFG_VREFINT_OUT_PB0)  || \
                                                ((OUTPUT) == SYSCFG_VREFINT_OUT_PB1)  || \
                                                ((OUTPUT) == SYSCFG_VREFINT_OUT_PB0_PB1))
/**
  * @}
  */

/** @defgroup SYSCFG_flags_definition SYSCFG Flags Definition
  * @{
  */
#define SYSCFG_FLAG_VREFINT_READY      SYSCFG_CFGR3_VREFINT_RDYF

#define IS_SYSCFG_FLAG(FLAG)           ((FLAG) == SYSCFG_FLAG_VREFINT_READY))

/**
  * @}
  */

/** @defgroup SYSCFG_FastModePlus_GPIO Fast Mode Plus on GPIO
  * @{
  */
/** @brief  Fast mode Plus driving capability on a specific GPIO
  */
#if defined (SYSCFG_CFGR2_I2C_PB6_FMP)
#define SYSCFG_FASTMODEPLUS_PB6       SYSCFG_CFGR2_I2C_PB6_FMP  /* Enable Fast Mode Plus on PB6 */
#endif
#if defined (SYSCFG_CFGR2_I2C_PB7_FMP)
#define SYSCFG_FASTMODEPLUS_PB7       SYSCFG_CFGR2_I2C_PB7_FMP  /* Enable Fast Mode Plus on PB7 */
#endif
#if defined (SYSCFG_CFGR2_I2C_PB8_FMP)
#define SYSCFG_FASTMODEPLUS_PB8       SYSCFG_CFGR2_I2C_PB8_FMP  /* Enable Fast Mode Plus on PB8 */
#endif
#if defined (SYSCFG_CFGR2_I2C_PB9_FMP)
#define SYSCFG_FASTMODEPLUS_PB9       SYSCFG_CFGR2_I2C_PB9_FMP  /* Enable Fast Mode Plus on PB9 */
#endif

#define IS_SYSCFG_FASTMODEPLUS(PIN) ((((PIN) & (SYSCFG_FASTMODEPLUS_PB6)) == SYSCFG_FASTMODEPLUS_PB6)  || \
                                     (((PIN) & (SYSCFG_FASTMODEPLUS_PB7)) == SYSCFG_FASTMODEPLUS_PB7)  || \
                                     (((PIN) & (SYSCFG_FASTMODEPLUS_PB8)) == SYSCFG_FASTMODEPLUS_PB8)  || \
                                     (((PIN) & (SYSCFG_FASTMODEPLUS_PB9)) == SYSCFG_FASTMODEPLUS_PB9)  )
/**
 * @}
 */
 /**
  * @}
  */

/* Exported macros -----------------------------------------------------------*/
/** @defgroup HAL_Exported_Macros HAL Exported Macros
  * @{
  */

/** @brief  Freeze/Unfreeze Peripherals in Debug mode
  */
#if defined (DBGMCU_APB1_FZ_DBG_TIM2_STOP)
/**
  * @brief  TIM2 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_TIM2()     SET_BIT(DBGMCU->APB1FZ,DBGMCU_APB1_FZ_DBG_TIM2_STOP)
#define __HAL_DBGMCU_UNFREEZE_TIM2()   CLEAR_BIT(DBGMCU->APB1FZ,DBGMCU_APB1_FZ_DBG_TIM2_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_TIM3_STOP)
/**
  * @brief  TIM3 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_TIM3()     SET_BIT(DBGMCU->APB1FZ,DBGMCU_APB1_FZ_DBG_TIM3_STOP)
#define __HAL_DBGMCU_UNFREEZE_TIM3()   CLEAR_BIT(DBGMCU->APB1FZ,DBGMCU_APB1_FZ_DBG_TIM3_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_TIM6_STOP)
/**
  * @brief  TIM6 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_TIM6()     SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_TIM6_STOP)
#define __HAL_DBGMCU_UNFREEZE_TIM6()   CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_TIM6_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_TIM7_STOP)
/**
  * @brief  TIM7 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_TIM7()     SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_TIM7_STOP)
#define __HAL_DBGMCU_UNFREEZE_TIM7()   CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_TIM7_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_RTC_STOP)
/**
  * @brief  RTC Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_RTC()      SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_RTC_STOP)
#define __HAL_DBGMCU_UNFREEZE_RTC()    CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_RTC_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_WWDG_STOP)
/**
  * @brief  WWDG Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_WWDG()     SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_WWDG_STOP)
#define __HAL_DBGMCU_UNFREEZE_WWDG()   CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_WWDG_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_IWDG_STOP)
/**
  * @brief  IWDG Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_IWDG()     SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_IWDG_STOP)
#define __HAL_DBGMCU_UNFREEZE_IWDG()   CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_IWDG_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_I2C1_STOP)
/**
  * @brief  I2C1 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_I2C1_TIMEOUT()   SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_I2C1_STOP)
#define __HAL_DBGMCU_UNFREEZE_I2C1_TIMEOUT_DBGMCU() CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_I2C1_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_I2C2_STOP)
/**
  * @brief  I2C2 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_I2C2_TIMEOUT_DBGMCU()   SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_I2C2_STOP)
#define __HAL_DBGMCU_UNFREEZE_I2C2_TIMEOUT_DBGMCU() CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_I2C2_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_I2C3_STOP)
/**
  * @brief  I2C3 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_I2C3_TIMEOUT()   SET_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_I2C3_STOP)
#define __HAL_DBGMCU_UNFREEZE_I2C3_TIMEOUT() CLEAR_BIT(DBGMCU->APB1FZ, DBGMCU_APB1_FZ_DBG_I2C3_STOP)
#endif

#if defined (DBGMCU_APB1_FZ_DBG_LPTIMER_STOP)
/**
  * @brief  LPTIMER Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_LPTIMER()        SET_BIT(DBGMCU->APB1FZ ,DBGMCU_APB1_FZ_DBG_LPTIMER_STOP)
#define __HAL_DBGMCU_UNFREEZE_LPTIMER()      CLEAR_BIT(DBGMCU->APB1FZ ,DBGMCU_APB1_FZ_DBG_LPTIMER_STOP)
#endif

#if defined (DBGMCU_APB2_FZ_DBG_TIM22_STOP)
/**
  * @brief  TIM22 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_TIM22()          SET_BIT(DBGMCU->APB2FZ, DBGMCU_APB2_FZ_DBG_TIM22_STOP)
#define __HAL_DBGMCU_UNFREEZE_TIM22()        CLEAR_BIT(DBGMCU->APB2FZ, DBGMCU_APB2_FZ_DBG_TIM22_STOP)
#endif

#if defined (DBGMCU_APB2_FZ_DBG_TIM21_STOP)
/**
  * @brief  TIM21 Peripherals Debug mode
  */
#define __HAL_DBGMCU_FREEZE_TIM21()          SET_BIT(DBGMCU->APB2FZ, DBGMCU_APB2_FZ_DBG_TIM21_STOP)
#define __HAL_DBGMCU_UNFREEZE_TIM21()        CLEAR_BIT(DBGMCU->APB2FZ, DBGMCU_APB2_FZ_DBG_TIM21_STOP)
#endif

/** @brief  Main Flash memory mapped at 0x00000000
  */
#define __HAL_SYSCFG_REMAPMEMORY_FLASH()     CLEAR_BIT(SYSCFG->CFGR1, SYSCFG_CFGR1_MEM_MODE)

/** @brief  System Flash memory mapped at 0x00000000
  */
#define __HAL_SYSCFG_REMAPMEMORY_SYSTEMFLASH()      MODIFY_REG(SYSCFG->CFGR1, SYSCFG_CFGR1_MEM_MODE, SYSCFG_CFGR1_MEM_MODE_0)


/** @brief  Embedded SRAM mapped at 0x00000000
  */
#define __HAL_SYSCFG_REMAPMEMORY_SRAM()             MODIFY_REG(SYSCFG->CFGR1, SYSCFG_CFGR1_MEM_MODE, SYSCFG_CFGR1_MEM_MODE_0 | SYSCFG_CFGR1_MEM_MODE_1)

/** @brief  Configuration of the DBG Low Power mode.
  * @param  __DBGLPMODE__ bit field to indicate in wich Low Power mode DBG is still active.
  *         This parameter can be a value of
  *         - DBGMCU_SLEEP
  *         - DBGMCU_STOP
  *         - DBGMCU_STANDBY
  */
#define __HAL_SYSCFG_DBG_LP_CONFIG(__DBGLPMODE__)    do {assert_param(IS_DBGMCU_PERIPH(__DBGLPMODE__)); \
                                                       MODIFY_REG(DBGMCU->CR, DBGMCU_CR_DBG, (__DBGLPMODE__)); \
                                                     } while (0)

#if defined (LCD_BASE) /* STM32L0x3xx only */

/** @brief  Macro to configure the VLCD Decoupling capacitance connection.
  *
  * @param  __SYSCFG_VLCD_CAPA__ specifies the decoupling of LCD capacitance for rails connection on GPIO.
  *          This parameter can be a combination of following values (when available):
  *            @arg SYSCFG_VLCD_PB2_EXT_CAPA_ON:  Connection on PB2
  *            @arg SYSCFG_VLCD_PB12_EXT_CAPA_ON: Connection on PB12
  *            @arg SYSCFG_VLCD_PB0_EXT_CAPA_ON:  Connection on PB0
  *            @arg SYSCFG_VLCD_PE11_EXT_CAPA_ON: Connection on PE11
  *            @arg SYSCFG_VLCD_PE12_EXT_CAPA_ON: Connection on PE12
  * @retval None
  */
#define __HAL_SYSCFG_VLCD_CAPA_CONFIG(__SYSCFG_VLCD_CAPA__) \
                  MODIFY_REG(SYSCFG->CFGR2, SYSCFG_LCD_EXT_CAPA, (uint32_t)(__SYSCFG_VLCD_CAPA__))

/**
  * @brief  Returns the decoupling of LCD capacitance configured by user.
  * @retval The LCD capacitance connection as configured by user. The returned can be a combination of :
  *            SYSCFG_VLCD_PB2_EXT_CAPA_ON:  Connection on PB2
  *            SYSCFG_VLCD_PB12_EXT_CAPA_ON: Connection on PB12
  *            SYSCFG_VLCD_PB0_EXT_CAPA_ON:  Connection on PB0
  *            SYSCFG_VLCD_PE11_EXT_CAPA_ON: Connection on PE11
  *            SYSCFG_VLCD_PE12_EXT_CAPA_ON: Connection on PE12
  */
#define __HAL_SYSCFG_GET_VLCD_CAPA_CONFIG()          READ_BIT(SYSCFG->CFGR2, SYSCFG_LCD_EXT_CAPA)

#endif

/**
  * @brief  Returns the boot mode as configured by user.
  * @retval The boot mode as configured by user. The returned can be a value of :
  *     - SYSCFG_BOOT_MAINFLASH
  *     - SYSCFG_BOOT_SYSTEMFLASH
  *     - SYSCFG_BOOT_SRAM
  */
#define __HAL_SYSCFG_GET_BOOT_MODE()          READ_BIT(SYSCFG->CFGR1, SYSCFG_CFGR1_BOOT_MODE)


/** @brief  Check whether the specified SYSCFG flag is set or not.
  * @param  __FLAG__ specifies the flag to check.
  *         The only parameter supported is SYSCFG_FLAG_VREFINT_READY
  * @retval The new state of __FLAG__ (TRUE or FALSE).
  */
#define __HAL_SYSCFG_GET_FLAG(__FLAG__) (((SYSCFG->CFGR3) & (__FLAG__)) == (__FLAG__))

/** @brief  Fast mode Plus driving capability enable macro
  * @param __FASTMODEPLUS__ This parameter can be a value of :
  *     @arg SYSCFG_FASTMODEPLUS_PB6
  *     @arg SYSCFG_FASTMODEPLUS_PB7
  *     @arg SYSCFG_FASTMODEPLUS_PB8
  *     @arg SYSCFG_FASTMODEPLUS_PB9
  */
#define __HAL_SYSCFG_FASTMODEPLUS_ENABLE(__FASTMODEPLUS__)  do {assert_param(IS_SYSCFG_FASTMODEPLUS((__FASTMODEPLUS__))); \
                                                                SET_BIT(SYSCFG->CFGR2, (__FASTMODEPLUS__));                 \
                                                               }while(0)
/** @brief  Fast mode Plus driving capability disable macro
  * @param __FASTMODEPLUS__ This parameter can be a value of :
  *     @arg SYSCFG_FASTMODEPLUS_PB6
  *     @arg SYSCFG_FASTMODEPLUS_PB7
  *     @arg SYSCFG_FASTMODEPLUS_PB8
  *     @arg SYSCFG_FASTMODEPLUS_PB9
  */
#define __HAL_SYSCFG_FASTMODEPLUS_DISABLE(__FASTMODEPLUS__) do {assert_param(IS_SYSCFG_FASTMODEPLUS((__FASTMODEPLUS__))); \
                                                                CLEAR_BIT(SYSCFG->CFGR2, (__FASTMODEPLUS__));               \
                                                               }while(0)


/**
  * @}
  */

/** @defgroup HAL_Private_Macros HAL Private Macros
  * @{
  */
#define IS_TICKFREQ(FREQ) (((FREQ) == HAL_TICK_FREQ_10HZ)  || \
                           ((FREQ) == HAL_TICK_FREQ_100HZ) || \
                           ((FREQ) == HAL_TICK_FREQ_1KHZ))
/**
  * @}
  */

/* Exported variables --------------------------------------------------------*/
/** @defgroup HAL_Exported_Variables HAL Exported Variables
  * @{
  */
extern __IO uint32_t uwTick;
extern uint32_t uwTickPrio;
extern HAL_TickFreqTypeDef uwTickFreq;

/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @defgroup HAL_Exported_Functions HAL Exported Functions
  * @{
  */
/** @defgroup HAL_Exported_Functions_Group1 Initialization and de-initialization functions
 *  @brief    Initialization and de-initialization functions
 * @{
  */
HAL_StatusTypeDef HAL_Init(void);
HAL_StatusTypeDef HAL_DeInit(void);
void HAL_MspInit(void);
void HAL_MspDeInit(void);
HAL_StatusTypeDef HAL_InitTick(uint32_t TickPriority);

/**
  * @}
  */

/** @defgroup HAL_Exported_Functions_Group2 Peripheral Control functions
  * @brief    Peripheral Control functions
  * @{
  */
void HAL_IncTick(void);
void HAL_Delay(uint32_t Delay);
uint32_t HAL_GetTick(void);
uint32_t HAL_GetTickPrio(void);
HAL_StatusTypeDef HAL_SetTickFreq(HAL_TickFreqTypeDef Freq);
HAL_TickFreqTypeDef HAL_GetTickFreq(void);
void HAL_SuspendTick(void);
void HAL_ResumeTick(void);
uint32_t HAL_GetHalVersion(void);
uint32_t HAL_GetREVID(void);
uint32_t HAL_GetDEVID(void);
uint32_t HAL_GetUIDw0(void);
uint32_t HAL_GetUIDw1(void);
uint32_t HAL_GetUIDw2(void);
/**
  * @}
  */

/** @defgroup HAL_Exported_Functions_Group3 DBGMCU Peripheral Control functions
  * @brief    DBGMCU Peripheral Control functions
  * @{
  */
void HAL_DBGMCU_EnableDBGSleepMode(void);
void HAL_DBGMCU_DisableDBGSleepMode(void);
void HAL_DBGMCU_EnableDBGStopMode(void);
void HAL_DBGMCU_DisableDBGStopMode(void);
void HAL_DBGMCU_EnableDBGStandbyMode(void);
void HAL_DBGMCU_DisableDBGStandbyMode(void);
void HAL_DBGMCU_DBG_EnableLowPowerConfig(uint32_t Periph);
void HAL_DBGMCU_DBG_DisableLowPowerConfig(uint32_t Periph);
/**
  * @}
  */

/** @defgroup HAL_Exported_Functions_Group4 SYSCFG Peripheral Control functions
  * @brief    SYSCFG Peripheral Control functions
  * @{
  */
uint32_t  HAL_SYSCFG_GetBootMode(void);
void HAL_SYSCFG_Enable_Lock_VREFINT(void);
void HAL_SYSCFG_Disable_Lock_VREFINT(void);
void HAL_SYSCFG_VREFINT_OutputSelect(uint32_t SYSCFG_Vrefint_OUTPUT);
/**
  * @}
  */
/**
  * @}
  */

/* Define the private group ***********************************/
/**************************************************************/
/** @defgroup HAL_Private HAL Private
  * @{
  */
/**
  * @}
  */
/**************************************************************/


/**
  * @}
  */

/**
  * @}
  */

#ifdef __cplusplus
}
#endif

#endif /* __STM32L0xx_HAL_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/

