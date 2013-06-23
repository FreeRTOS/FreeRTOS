/**********************************************************************
* $Id$		lpc43xx_libcfg.h		2011-06-02
*//**
* @file		lpc43xx_libcfg.h
* @brief	Library configuration file
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

#ifndef lpc43xx_LIBCFG_H_
#define lpc43xx_LIBCFG_H_

#include "lpc_types.h"


/************************** DEBUG MODE DEFINITIONS *********************************/
/* Un-comment the line below to compile the library in DEBUG mode, this will expanse
   the "CHECK_PARAM" macro in the FW library code */

#define DEBUG


/******************* PERIPHERAL FW LIBRARY CONFIGURATION DEFINITIONS ***********************/

/* Comment the line below to disable the specific peripheral inclusion */

/* GPIO ------------------------------- */
#define _GPIO

/* EXTI ------------------------------- */
//#define _EXTI

/* UART ------------------------------- */
#define _UART
#define _UART0
#define _UART1
#define _UART2
#define _UART3

/* SPI ------------------------------- */
//#define _SPI

/* SSP ------------------------------- */
//#define _SSP
//#define _SSP0
//#define _SSP1

/* SYSTICK --------------------------- */
//#define _SYSTICK

/* I2C ------------------------------- */
//#define _I2C
//#define _I2C0
//#define _I2C1
//#define _I2C2

/* TIMER ------------------------------- */
//#define _TIM

/* WDT ------------------------------- */
//#define _WDT


/* GPDMA ------------------------------- */
//#define _GPDMA


/* DAC ------------------------------- */
//#define _DAC

/* DAC ------------------------------- */
//#define _ADC


/* PWM ------------------------------- */
//#define _PWM
//#define _PWM1

/* RTC ------------------------------- */
//#define _RTC

/* I2S ------------------------------- */
//#define _I2S

/* USB device ------------------------------- */
#define _USBDEV
//#define _USB_DMA

/* QEI ------------------------------- */
//#define _QEI

/* MCPWM ------------------------------- */
//#define _MCPWM

/* CAN--------------------------------*/
//#define _CAN

/* RIT ------------------------------- */
//#define _RIT

/* EMAC ------------------------------ */
//#define _EMAC

/************************** GLOBAL/PUBLIC MACRO DEFINITIONS *********************************/

#ifdef  DEBUG
/*******************************************************************************
* @brief		The CHECK_PARAM macro is used for function's parameters check.
* 				It is used only if the library is compiled in DEBUG mode.
* @param[in]	expr - If expr is false, it calls check_failed() function
*                    	which reports the name of the source file and the source
*                    	line number of the call that failed.
*                    - If expr is true, it returns no value.
* @return		None
*******************************************************************************/
#define CHECK_PARAM(expr) ((expr) ? (void)0 : check_failed((uint8_t *)__FILE__, __LINE__))
#else
#define CHECK_PARAM(expr)
#endif /* DEBUG */



/************************** GLOBAL/PUBLIC FUNCTION DECLARATION *********************************/

#ifdef  DEBUG
void check_failed(uint8_t *file, uint32_t line);
#endif


#endif /* lpc43xx_LIBCFG_H_ */
