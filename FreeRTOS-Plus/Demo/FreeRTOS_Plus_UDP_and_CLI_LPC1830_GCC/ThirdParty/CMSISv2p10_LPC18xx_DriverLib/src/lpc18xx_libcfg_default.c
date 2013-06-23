/***********************************************************************//**
 * @file		lpc18xx_libcfg_default.c
 * @brief		Library configuration source file (default),
 * 				used to build library without examples.
 * @version		2.0
 * @date		21. May. 2010
 * @author		NXP MCU SW Application Team
 **************************************************************************
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
 **************************************************************************/

/* Library group ----------------------------------------------------------- */
/** @addtogroup LIBCFG_DEFAULT
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_libcfg_default.h"

/* Public Functions ----------------------------------------------------------- */
/** @addtogroup LIBCFG_DEFAULT_Public_Functions
 * @{
 */

#ifndef __BUILD_WITH_EXAMPLE__

#ifdef  DEBUG
/*******************************************************************************
* @brief		Reports the name of the source file and the source line number
* 				where the CHECK_PARAM error has occurred.
* @param[in]	file Pointer to the source file name
* @param[in]    line assert_param error line source number
* @return		None
*******************************************************************************/
void check_failed(uint8_t *file, uint32_t line)
{
	/* User can add his own implementation to report the file name and line number,
	 ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */

	/* Infinite loop */
	while(1);
}
#endif /* DEBUG */

#endif /* __BUILD_WITH_EXAMPLE__ */

/**
 * @}
 */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
