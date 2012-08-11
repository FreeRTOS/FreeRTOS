/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_lib.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides all peripherals pointers
                     : initialization.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#define EXT

/* Standard include ----------------------------------------------------------*/
#include "91x_map.h"

/* Include of other module interface headers ---------------------------------*/
/* Local includes ------------------------------------------------------------*/
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Interface functions -------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
#ifdef DEBUG

/*******************************************************************************
* Function Name  : debug
* Description    : this function initialize peripherals pointers
* Input          : no one
* Output         : no one
* Return         : no one
*******************************************************************************/
void debug(void)
{


/************************* DMA *************************/

#ifdef _DMA
  DMA = (DMA_TypeDef *)DMA_BASE;
#endif /* _DMA */

/************************* DMA *************************/


#ifdef _DMA_Channel0
  DMA_Channel0= (DMA_Channel_TypeDef *)DMA_Channel0_BASE;
#endif /* _DMA_Channel0 */

#ifdef _DMA_Channel1
  DMA_Channel1=       (DMA_Channel_TypeDef *)DMA_Channel1_BASE;
#endif /* _DMA_Channel1 */

#ifdef _DMA_Channel2
  DMA_Channel2 =      (DMA_Channel_TypeDef *)DMA_Channel2_BASE;
#endif /* _DMA_Channel2 */

#ifdef _DMA_Channel3
  DMA_Channel3 =       (DMA_Channel_TypeDef *)DMA_Channel3_BASE;
#endif /* _DMA_Channel3 */

#ifdef _DMA_Channel4
 DMA_Channel4 =      (DMA_Channel_TypeDef *)DMA_Channel4_BASE;
#endif /* _DMA_Channel4 */

#ifdef _DMA_Channel5
 DMA_Channel5=       (DMA_Channel_TypeDef *)DMA_Channel5_BASE;
#endif /* _DMA_Channel5*/


#ifdef _DMA_Channel6
 DMA_Channel6 =      (DMA_Channel_TypeDef *)DMA_Channel6_BASE;
#endif /* _DMA_Channel6 */

#ifdef _DMA_Channel7
 DMA_Channel7 =      (DMA_Channel_TypeDef *)DMA_Channel7_BASE;
#endif /* _DMA_Channel7 */
 


 /************************* EMI *************************/

#ifdef _EMI_Bank0
  EMI_Bank0= (EMI_Bank_TypeDef *)EMI_Bank0_BASE;
#endif /* _EMI_Bank0 */

#ifdef _EMI_Bank1
  EMI_Bank1=       (EMI_Bank_TypeDef *)EMI_Bank1_BASE;
#endif /* _EMI_Bank1 */

#ifdef _EMI_Bank2
  EMI_Bank2 =      (EMI_Bank_TypeDef *)EMI_Bank2_BASE;
#endif /* _EMI_Bank2 */

#ifdef _EMI_Bank3
 EMI_Bank3 =      (EMI_Bank_TypeDef *)EMI_Bank3_BASE;
 #endif /* _EMI_Bank3 */



/************************* AHBAPB *************************/

#ifdef _AHBAPB0
  AHBAPB0 = (AHBAPB_TypeDef *)AHBAPB0_BASE;
#endif /* _AHBAPB0 */

#ifdef _AHBAPB1
  AHBAPB1 = (AHBAPB_TypeDef *)AHBAPB1_BASE;
#endif /*_AHBAPB1 */



/************************* FMI *************************/

#ifdef _FMI
  FMI = (FMI_TypeDef *)FMI_BASE;
#endif /* _FMI */

/************************* VIC *************************/

#ifdef _VIC0
  VIC0 = (VIC_TypeDef *)VIC0_BASE;
#endif /* _VIC0 */

#ifdef _VIC1
  VIC1 = (VIC_TypeDef *)VIC1_BASE;
#endif /* _VIC1 */

/************************* WIU *************************/

#ifdef _WIU
  WIU  = (WIU_TypeDef *)WIU_BASE;
#endif /* _WIU */

/************************* TIM *************************/

#ifdef _TIM0
  TIM0 = (TIM_TypeDef *)TIM0_BASE;
#endif /* _TIM0 */

#ifdef _TIM1
  TIM1 = (TIM_TypeDef *)TIM1_BASE;
#endif /* _TIM1 */

#ifdef _TIM2
  TIM2 = (TIM_TypeDef *)TIM2_BASE;
#endif /* _TIM2 */

#ifdef _TIM3
  TIM3 = (TIM_TypeDef *)TIM3_BASE;
#endif /* _TIM3 */

/************************* GPIO ************************/

#ifdef _GPIO0
  GPIO0 = (GPIO_TypeDef *)GPIO0_BASE;
#endif /* _GPIO0 */

#ifdef _GPIO1
  GPIO1 = (GPIO_TypeDef *)GPIO1_BASE;
#endif /* _GPIO1 */

#ifdef _GPIO2
  GPIO2 = (GPIO_TypeDef *)GPIO2_BASE;
#endif /* _GPIO2 */

#ifdef _GPIO3
  GPIO3 = (GPIO_TypeDef *)GPIO3_BASE;
#endif /* _GPIO3 */

#ifdef _GPIO4
  GPIO4 = (GPIO_TypeDef *)GPIO4_BASE;
#endif /* _GPIO4 */

#ifdef _GPIO5
  GPIO5 = (GPIO_TypeDef *)GPIO5_BASE;
#endif /* _GPIO5 */

#ifdef _GPIO6
  GPIO6 = (GPIO_TypeDef *)GPIO6_BASE;
#endif /* _GPIO6 */

#ifdef _GPIO7
  GPIO7 = (GPIO_TypeDef *)GPIO7_BASE;
#endif /* _GPIO7 */

#ifdef _GPIO8
  GPIO8 = (GPIO_TypeDef *)GPIO8_BASE;
#endif /* _GPIO8 */

#ifdef _GPIO9
  GPIO9 = (GPIO_TypeDef *)GPIO9_BASE;
#endif /* _GPIO9 */

/************************* RTC *************************/

#ifdef _RTC
  RTC = (RTC_TypeDef *)RTC_BASE;
#endif /* _RTC */

/************************* PRCCU ***********************/

#ifdef _SCU
  SCU = (SCU_TypeDef *)SCU_BASE;
#endif /* _PRCCU */

/************************** MC *************************/

#ifdef _MC
  MC = (MC_TypeDef *)MC_BASE;
#endif /* _MC */

/************************* UART ************************/

#ifdef _UART0
  UART0 = (UART_TypeDef *)UART0_BASE;
#endif /* _UART0 */

#ifdef _UART1
  UART1 = (UART_TypeDef *)UART1_BASE;
#endif /* _UART1 */

#ifdef _UART2
  UART2 = (UART_TypeDef *)UART2_BASE;
#endif /* _UART2 */

/************************* SSP *************************/

#ifdef _SSP0
  SSP0 = (SSP_TypeDef *)SSP0_BASE;
#endif /* _SSP0 */

#ifdef _SSP1
  SSP1 = (SSP_TypeDef *)SSP1_BASE;
#endif /* _SSP1 */

/************************* CAN *************************/

#ifdef _CAN
  CAN = (CAN_TypeDef *)CAN_BASE;
#endif /* _CAN */

/************************* ADC *************************/

#ifdef _ADC
  ADC = (ADC_TypeDef *)ADC_BASE;
#endif /* _ADC */

/************************* WDG *************************/

#ifdef _WDG
  WDG = (WDG_TypeDef *)WDG_BASE;
#endif /* _WDG */

/************************* I2C *************************/

#ifdef _I2C0
  I2C0 = (I2C_TypeDef *)I2C0_BASE;
#endif /* _I2C0 */

#ifdef _I2C1
  I2C1 = (I2C_TypeDef *)I2C1_BASE;
#endif /* _I2C1 */
/********************** ENET **************************/
#ifdef _ENET
  ENET_MAC = (ENET_MAC_TypeDef *)ENET_MAC_BASE;
  ENET_DMA = (ENET_DMA_TypeDef *)ENET_DMA_BASE;
#endif /* _ENET */
}
#endif  /* DEBUG */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
