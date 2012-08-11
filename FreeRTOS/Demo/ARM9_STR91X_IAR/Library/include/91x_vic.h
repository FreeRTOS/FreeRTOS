/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_vic.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      VIC software library.
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


/* Define to prevent recursive inclusion ------------------------------------ */
#ifndef __91x_VIC_H
#define __91x_VIC_H

/* Includes ------------------------------------------------------------------*/
#include "91x_map.h"
#include "91x_it.h"

/* Exported types ------------------------------------------------------------*/
/* Type of interrupt */
typedef enum
{
 VIC_IRQ,
 VIC_FIQ
} VIC_ITLineMode;

/* Exported constants --------------------------------------------------------*/

/* VIC sources*/

#define WDG_ITLine        0
#define SW_ITLine         1
#define ARMRX_ITLine      2
#define ARMTX_ITLine      3
#define TIM0_ITLine       4
#define TIM1_ITLine       5
#define TIM2_ITLine       6
#define TIM3_ITLine       7
#define USBHP_ITLine      8
#define USBLP_ITLine      9
#define SCU_ITLine        10
#define ENET_ITLine      11
#define DMA_ITLine        12
#define CAN_ITLine        13
#define MC_ITLine         14
#define ADC_ITLine        15
#define UART0_ITLine      16
#define UART1_ITLine      17
#define UART2_ITLine      18
#define I2C0_ITLine       19
#define I2C1_ITLine       20
#define SSP0_ITLine       21
#define SSP1_ITLine       22
#define LVD_ITLine        23
#define RTC_ITLine        24
#define WIU_ITLine        25
#define EXTIT0_ITLine     26
#define EXTIT1_ITLine     27
#define EXTIT2_ITLine     28
#define EXTIT3_ITLine     29
#define USBWU_ITLine      30
#define PFQBC_ITLine      31


/* Module private variables --------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void VIC_DeInit(void);
FlagStatus VIC_GetIRQStatus(u16 VIC_Source);
FlagStatus VIC_GetFIQStatus(u16 VIC_Source);
FlagStatus VIC_GetSourceITStatus(u16 VIC_Source);
void VIC_ITCmd(u16 VIC_Source, FunctionalState VIC_NewState);
void VIC_SWITCmd(u16 VIC_Source, FunctionalState VIC_NewState);
void VIC_ProtectionCmd(FunctionalState VIC_NewState);
u32 VIC_GetCurrentISRAdd(VIC_TypeDef* VICx);
u32 VIC_GetISRVectAdd(u16 VIC_Source);
void VIC_Config(u16 VIC_Source, VIC_ITLineMode VIC_LineMode, u8 VIC_Priority);

#endif /* __91x_VIC_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/

