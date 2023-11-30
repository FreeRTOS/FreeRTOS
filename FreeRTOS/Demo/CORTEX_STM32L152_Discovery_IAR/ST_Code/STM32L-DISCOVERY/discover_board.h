 /**
  ******************************************************************************
  * @file    discover_board.h
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   Input/Output defines
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

#ifndef __DISCOVER_BOARD_H
#define __DISCOVER_BOARD_H

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"  

#define bool _Bool
#define FALSE 0
#define TRUE !FALSE

/* MACROs for SET, RESET or TOGGLE Output port */

#define GPIO_HIGH(a,b) 		a->BSRRL = b
#define GPIO_LOW(a,b)		a->BSRRH = b
#define GPIO_TOGGLE(a,b) 	a->ODR ^= b 

#define USERBUTTON_GPIO_PORT	GPIOA
#define USERBUTTON_GPIO_PIN     GPIO_Pin_0
#define USERBUTTON_GPIO_CLK     RCC_AHBPeriph_GPIOA

#define LD_GPIO_PORT 		GPIOB
#define LD_GREEN_GPIO_PIN 		GPIO_Pin_7
#define LD_BLUE_GPIO_PIN             GPIO_Pin_6
#define LD_GPIO_PORT_CLK             RCC_AHBPeriph_GPIOB

#define CTN_GPIO_PORT           GPIOC
#define CTN_CNTEN_GPIO_PIN      GPIO_Pin_13
#define CTN_GPIO_CLK            RCC_AHBPeriph_GPIOC

#define WAKEUP_GPIO_PORT        GPIOA

#define IDD_MEASURE_PORT	GPIOA
#define IDD_MEASURE             GPIO_Pin_4

#endif


/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
