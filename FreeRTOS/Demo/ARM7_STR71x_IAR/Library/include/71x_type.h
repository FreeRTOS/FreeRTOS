/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : 71x_type.h
* Author             : MCD Application Team
* Date First Issued  : 05/16/2003
* Description        : Common data types
********************************************************************************
* History:
*  30/11/2004 : V2.0
*  14/07/2004 : V1.3
*  01/01/2004 : V1.2
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#ifndef _71x_type_H
#define _71x_type_H

typedef unsigned long   u32;
typedef unsigned short  u16;
typedef unsigned char   u8;

typedef signed long   s32;
typedef signed short  s16;
typedef signed char   s8;

typedef volatile unsigned long   vu32;
typedef volatile unsigned short  vu16;
typedef volatile unsigned char   vu8;

typedef volatile signed long   vs32;
typedef volatile signed short  vs16;
typedef volatile signed char   vs8;

/*===================================================================*/
typedef enum { FALSE = 0, TRUE  = !FALSE } bool;
/*===================================================================*/
typedef enum { RESET = 0, SET   = !RESET } FlagStatus;
/*===================================================================*/
typedef enum { DISABLE = 0, ENABLE  = !DISABLE} FunctionalState;
/*===================================================================*/
typedef enum { INDIRECT = 0, DIRECT  = !INDIRECT} RegisterAccess;
/*===================================================================*/

#endif /* _71x_type_H */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
