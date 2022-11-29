/******************** (C) COPYRIGHT 2008 STMicroelectronics ********************
* File Name          : stm32fxxx_eth_lib.c
* Author             : MCD Application Team
* Version            : V2.0.2
* Date               : 07/11/2008
* Description        : This file provides all peripherals pointers initialization.
********************************************************************************
* THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

#define EXT
#include "stm32f10x_lib.h"
/* Includes ------------------------------------------------------------------*/
#include "stm32fxxx_eth_lib.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

#ifdef ETH_DEBUG
/*******************************************************************************
* Function Name  : ethernet_debug
* Description    : This function initialize peripherals pointers.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void eth_debug(void)
{
/********************************** ETHERNET **********************************/
#ifdef _ETH_MAC
  ETH_MAC = ((ETH_MAC_TypeDef *) ETH_MAC_BASE);
#endif /*_ETH_MAC */

#ifdef _ETH_MMC
  ETH_MMC = ((ETH_MMC_TypeDef *) ETH_MMC_BASE);
#endif /*_ETH_MMC */

#ifdef _ETH_PTP
  ETH_PTP = ((ETH_PTP_TypeDef *) ETH_PTP_BASE);
#endif /*_ETH_PTP */

#ifdef _ETH_DMA
  ETH_DMA = ((ETH_DMA_TypeDef *) ETH_DMA_BASE);
#endif /*_ETH_DMA */
}

#endif  /* ETH_DEBUG*/

/******************* (C) COPYRIGHT 2008 STMicroelectronics *****END OF FILE****/
