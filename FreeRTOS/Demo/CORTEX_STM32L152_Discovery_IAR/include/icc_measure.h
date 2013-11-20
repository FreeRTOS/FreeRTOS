 /**
  ******************************************************************************
  * @file    icc_measure.h
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   Current measurements defines
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __ICC_MEASURE_H
#define __ICC_MEASURE_H

/* Includes ------------------------------------------------------------------*/


/* Private define ------------------------------------------------------------*/
#define MCU_RUN		0
#define MCU_SLEEP       1
#define MCU_LP_RUN      2
#define MCU_LP_SLEEP    3
#define MCU_STOP_RTC	4
#define MCU_STOP_NoRTC	5
#define MCU_STBY	6

#define NoRTC FALSE
#define WITHRTC !NoRTC
#define NoDIV2 FALSE
#define DIV2 !NoDIV2

/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
uint16_t ADC_Supply(void);
void ADC_Icc_Init(void);
uint16_t ADC_Icc_Test(uint8_t Mcu_State);
void GPIO_LowPower_Config(void);
void STOP_Init(void);
void STBY_Init(void);
uint16_t Current_Measurement(void);
void EnterLPSLEEPModeRAM(void);
void SetHSICLKToMSI(uint32_t ,bool ,bool );
void EnterLPRUNModeRAM(void);
#endif /* __ICC_MEASURE_H*/

/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
