/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_ahbapb.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      AHBAPB software library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef _91x_AHBAPB_H
#define _91x_AHBAPB_H

#include "91x_map.h"

#define AHBAPB_Split_Enable  0x01000000
#define AHBAPB_Split_Disable 0xFEFFFFFF
#define AHBAPB_Error_Enable  0x0000100
#define AHBAPB_Error_Disable 0xFFFFEFF

/*FLAG*/
#define  AHBAPB_FLAG_ERROR  0x01  /* error flag*/
#define  AHBAPB_FLAG_OUTM   0x10  /* Out of Memory flag */
#define  AHBAPB_FLAG_APBT   0x20  /* APB Time-out flag */
#define  AHBAPB_FLAG_RW     0x40  /*Access type flag*/

/* Includes ------------------------------------------------------------------*/


/* AHBAPB Init structure definition */
typedef struct
{
  u32 AHBAPB_SetTimeOut;
  u32 AHBAPB_Error;
  u32 AHBAPB_Split;
  u8 AHBAPB_SplitCounter;
}AHBAPB_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
void AHBAPB_DeInit(AHBAPB_TypeDef* AHBAPBx);
void AHBAPB_Init(AHBAPB_TypeDef* AHBAPBx, AHBAPB_InitTypeDef* AHBAPB_InitStruct);
void AHBAPB_StructInit(AHBAPB_InitTypeDef* AHBAPB_InitStruct);
FlagStatus AHBAPB_GetFlagStatus(AHBAPB_TypeDef* AHBAPBx, u8 AHBAPB_FLAG);
void AHBAPB_ClearFlag(AHBAPB_TypeDef* AHBAPBx, u8 AHBAPB_FLAG);
u32 AHBAPB_GetPeriphAddrError(AHBAPB_TypeDef* AHBAPBx);


#endif /* _91x_AHBAPB_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
