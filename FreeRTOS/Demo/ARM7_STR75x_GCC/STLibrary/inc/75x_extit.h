/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_extit.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      EXTIT software library.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_EXTIT_H
#define __75x_EXTIT_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* EXTIT Trigger enumeration */
typedef enum
{
  EXTIT_ITTrigger_Falling = 1,
  EXTIT_ITTrigger_Rising
}EXTITTrigger_TypeDef;

/* EXTIT Init Structure definition */
typedef struct
{
  u32 EXTIT_ITLine;
  EXTITTrigger_TypeDef EXTIT_ITTrigger;
  FunctionalState EXTIT_ITLineCmd;
}EXTIT_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* EXTIT Lines */
#define EXTIT_ITLineNone    0x0000  /* No interrupt selected */
#define EXTIT_ITLine0       0x0001  /* External interrupt line 0 */
#define EXTIT_ITLine1       0x0002  /* External interrupt line 1 */
#define EXTIT_ITLine2       0x0004  /* External interrupt line 2 */
#define EXTIT_ITLine3       0x0008  /* External interrupt line 3 */
#define EXTIT_ITLine4       0x0010  /* External interrupt line 4 */
#define EXTIT_ITLine5       0x0020  /* External interrupt line 5 */
#define EXTIT_ITLine6       0x0040  /* External interrupt line 6 */
#define EXTIT_ITLine7       0x0080  /* External interrupt line 7 */
#define EXTIT_ITLine8       0x0100  /* External interrupt line 8 */
#define EXTIT_ITLine9       0x0200  /* External interrupt line 9 */
#define EXTIT_ITLine10      0x0400  /* External interrupt line 10 */
#define EXTIT_ITLine11      0x0800  /* External interrupt line 11 */
#define EXTIT_ITLine12      0x1000  /* External interrupt line 12 */
#define EXTIT_ITLine13      0x2000  /* External interrupt line 13 */
#define EXTIT_ITLine14      0x4000  /* External interrupt line 14 */
#define EXTIT_ITLine15      0x8000  /* External interrupt line 15 */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void EXTIT_DeInit(void);
void EXTIT_Init(EXTIT_InitTypeDef* EXTIT_InitStruct);
void EXTIT_StructInit(EXTIT_InitTypeDef* EXTIT_InitStruct);
void EXTIT_GenerateSWInterrupt(u16 EXTIT_ITLine);
FlagStatus EXTIT_GetFlagStatus(u16 EXTIT_ITLine);
void EXTIT_ClearFlag(u16 EXTIT_ITLine);
ITStatus EXTIT_GetITStatus(u16 EXTIT_ITLine);
void EXTIT_ClearITPendingBit(u16 EXTIT_ITLine);

#endif /* __75x_EXTIT_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
