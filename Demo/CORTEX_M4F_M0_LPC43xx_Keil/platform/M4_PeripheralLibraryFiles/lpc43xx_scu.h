/**********************************************************************
* $Id$		lpc43xx_scu.h		2011-06-02
*//**
* @file		lpc43xx_scu.h
* @brief	Contains all macro definitions and function prototypes
* 			support for SCU firmware library on lpc43xx
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

/* Peripheral group ----------------------------------------------------------- */
/** @defgroup SCU	SCU (System Control Unit)
 * @ingroup LPC4300CMSIS_FwLib_Drivers
 * @{
 */

#ifndef __SCU_H
#define __SCU_H

#ifdef __cplusplus
extern "C"
{
#endif

/* Private macros ------------------------------------------------------------- */
/** @defgroup SCT_Private_Macros SCT Private Macros
 * @{
 */

/** Port offset definition */
#define PORT_OFFSET 	0x80
/** Pin offset definition */
#define PIN_OFFSET  	0x04

/* Pin modes */
#define MD_PUP  (0x0<<3)
#define MD_BUK  (0x1<<3)
#define MD_PLN  (0x2<<3)
#define MD_PDN  (0x3<<3)
#define MD_EHS  (0x1<<5)
#define MD_EZI  (0x1<<6)
#define MD_ZI   (0x1<<7)
#define MD_EHD0 (0x1<<8)
#define MD_EHD1 (0x1<<8)
#define MD_PLN_FAST (MD_PLN | MD_EZI | MD_ZI | MD_EHS)
// 0xF0

/* Pin function */
#define FUNC0 			0x0				/** Function 0 	*/
#define FUNC1 			0x1				/** Function 1 	*/
#define FUNC2 			0x2				/** Function 2	*/
#define FUNC3 			0x3				/** Function 3	*/
#define FUNC4			0x4
#define FUNC5			0x5
#define FUNC6			0x6
#define FUNC7			0x7
/**
 * @}
 */

/* Public Functions ----------------------------------------------------------- */
/** @defgroup SCU_Public_Functions SCU Public Functions
 * @{
 */

void scu_pinmux(uint8_t port, uint8_t pin, uint8_t mode, uint8_t func);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* end __SCU_H */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
