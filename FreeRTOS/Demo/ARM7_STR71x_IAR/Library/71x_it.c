/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : 71x_it.c
* Author             : MCD Application Team
* Date First Issued  : 16/05/2003
* Description        : Main Interrupt Service Routines
*******************************************************************************
* History:
* 24/05/05 : V3.0
* 30/11/04 : V2.0
* 16/05/03 : Created
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#include "71x_it.h"


 u32 counter=1;
/*******************************************************************************
* Function Name  : Undefined_Handler
* Description    : This function handles Undefined instruction exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Undefined_Handler(void)
{
	for( ;; );
}

/*******************************************************************************
* Function Name  : FIQ_Handler
* Description    : This function handles FIQ exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void FIQ_Handler(void)
{
	for( ;; );
}

/*******************************************************************************
* Function Name  : Prefetch_Handler
* Description    : This function handles Prefetch Abort exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Prefetch_Handler(void)
{
	for( ;; );
}

/*******************************************************************************
* Function Name  : Abort_Handler
* Description    : This function handles Data Abort exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Abort_Handler(void)
{
	for( ;; );
}

void Default_Handler( void );
void Default_Handler( void )
{
	for( ;; );
}


/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
