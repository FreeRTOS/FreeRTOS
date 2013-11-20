 /**
  ******************************************************************************
  * @file   discover_functions.h
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   This file contains measurement values and board
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
#ifndef __DISCOVER_FUNCTIONS_H
#define __DISCOVER_FUNCTIONS_H

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"  

#define DELAY Delay(150)
#define TEMPO if(!KeyPressed) DELAY

//#define SLIDER_DETECTED (sMCKeyInfo[0].Setting.b.DETECTED)
//#define SLIDER_POSITION (sMCKeyInfo[0].UnScaledPosition)

#define enableGlobalInterrupts()   __set_PRIMASK(0);
#define disableGlobalInterrupts()  __set_PRIMASK(1);

#define STR_VERSION     tab[1] = 'V';tab[2] = '2'|DOT; tab[3] = '0'|DOT; tab[4] = '4'

#define STATE_VREF	        0
#define STATE_SLIDER_VALUE 	1
#define STATE_SLIDER_BUTTON 	2
#define STATE_ICC_RUN 	        3
#define STATE_ICC_LP_RUN        4
#define STATE_ICC_STOP     	5
#define STATE_ICC_STBY  	6

#define MAX_STATE 	        7


/* Theorically BandGAP 1.224volt */
#define VREF 		1.224L


/*
	ADC Converter 
	LSBIdeal = VREF/4096 or VDA/4096
*/
#define ADC_CONV 	4096

/*
 VDD Factory for VREFINT measurement 
*/
#define VDD_FACTORY 3.0L

#define MAX_CURRENT 	99999

/* AUTO TEST VALUE */

#define VCC_MIN 	2920  /* nominal Vcc/Vdd is 2.99V, allow 2.5% lower - Vref can be ~2% lower than 1.225 */
#define VCC_MAX 	3100
#define ICC_RUN_MIN 	6000
#define ICC_RUN_MAX 	11000 /* typical ICC_RUN is ~0.9mA */
#define ICC_STOP_MIN 	250
#define ICC_STOP_MAX 	800   /* typical ICC_STOP is 0.6uA */
#define ICC_BIAS_MAX    30    /* ! converter value in decimal ! --> 3.0volts/4036* 30 = 21 mV */

#define ICC_STBY_MIN 	150   /* typical ICC_STAND BY is 0.3 uA */
#define ICC_STBY_MAX    450    

/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/

#define AUTOTEST(a) DATA_EEPROM_Unlock();   DATA_EEPROM_FastProgramByte((uint32_t)&self_test,a ) ;  DATA_EEPROM_Lock()	
  
/* Exported functions ------------------------------------------------------- */


void  Init_Port (void);
void convert_into_char(uint32_t number, uint16_t *p_tab);
void LPR_init(void);
void Halt_Init(void);
uint16_t Vref_measure(void);
void Icc_measure(void);
float Icc_RUN(void);
float Icc_SLEEP(void);
float Icc_LPRUN(void);
float Icc_LPSLEEP(void);
float Icc_STOP(void);
float Icc_Stop_NoRTC(void);
void Icc_STBY(void);
float Icc_STBY_NoRTC(void);
void auto_test(void);
void Bias_measurement(void);
void test_vdd(void);
void test_icc_Run(void);
void test_icc_STOP(void);
void test_icc_STBY(void);
void display_MuAmp (uint32_t);
void FLASH_ProgramBias(uint8_t) ;
float Vdd_appli(void);
uint16_t wake_up_measurement (void);
void RCC_Configuration(void);
void Init_clocks(void);
void Init_GPIOs (void);
void TimingDelay_Decrement(void);
void Delay(uint32_t nTime);
void ExtraCode_StateMachine(void);
void Config_Systick(void);
void Config_Systick_50ms(void);	
void Button_value(void);
void Slider_value(void);
void auto_test_part2(void);

#endif /* __DISCOVER_FUNCTIONS_H*/

/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
