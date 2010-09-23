/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_it.c
* Author             : MCD Application Team
* Date First Issued  : 03/31/2006 :  Beta Version V0.1
* Description        : Main Interrupt Service Routines.
********************************************************************************
*    This file can be used to describe all the exceptions subroutines
*    that may occur within user application.
*    When an interrupt happens, the software will branch automatically
*    to the corresponding routine according to the interrupt vector
*    loaded in the PC register.
*    The following routines are all empty, user can write code for
*    exceptions handlers and peripherals IRQ interrupts.
********************************************************************************
* History:
* 03/31/2006 :  Beta Version V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#include "FreeRTOSConfig.h"
#include "91x_it.h"

/*******************************************************************************
* Function Name  : Undefined_Handler
* Description    : This function Undefined instruction exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Undefined_Handler(void)
{
	// NOT USED.
}
/*******************************************************************************
* Function Name  : SWI_Handler
* Description    : This function handles SW exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SWI_Handler(void)
{
	// NOT USED.
}
/*******************************************************************************
* Function Name  : Prefetch_Handler
* Description    : This function handles preftetch abort exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Prefetch_Handler(void)
{
	// NOT USED.
}
/*******************************************************************************
* Function Name  : Abort_Handler
* Description    : This function handles data abort exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Abort_Handler(void)
{
	// NOT USED.
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
	// NOT USED.
}
/*******************************************************************************
* Function Name  : SW_IRQHandler
* Description    : This function handles the SW interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SW_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : ARMRX_IRQHandler
* Description    : This function handles the ARMRX interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ARMRX_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : ARMTX_IRQHandler
* Description    : This function handles the ARMTX interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ARMTX_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : TIM0_IRQHandler
* Description    : This function handles the TIM0 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM0_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : TIM1_IRQHandler
* Description    : This function handles the TIM1 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : TIM2_IRQHandler
* Description    : This function handles the TIM2 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
//void TIM2_IRQHandler(void)
//{
//}
/*******************************************************************************
* Function Name  : TIM3_IRQHandler
* Description    : This function handles the TIM3 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM3_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : USBHP_IRQHandler
* Description    : This function handles the USBHP interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void USBHP_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : USBLP_IRQHandler
* Description    : This function handles the USBLP interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void USBLP_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : SCU_IRQHandler
* Description    : This function handles the SCU interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : DMA_IRQHandler
* Description    : This function handles the DMA interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : CAN_IRQHandler
* Description    : This function handles the CAN interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void CAN_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : MC_IRQHandler
* Description    : This function handles the MC interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void MC_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : ADC_IRQHandler
* Description    : This function handles the ADC interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : UART0_IRQHandler
* Description    : This function handles the UART0 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void UART0_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : UART2_IRQHandler
* Description    : This function handles the UART2 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void UART2_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : I2C0_IRQHandler
* Description    : This function handles the I2C0 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void I2C0_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : I2C1_IRQHandler
* Description    : This function handles the I2C1 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void I2C1_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : SSP0_IRQHandler
* Description    : This function handles the SSP0 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SSP0_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : SSP1_IRQHandler
* Description    : This function handles the SSP1 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SSP1_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : LVD_IRQHandler
* Description    : This function handles the LVD interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void LVD_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : RTC_IRQHandler
* Description    : This function handles the RTC interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : WIU_IRQHandler
* Description    : This function handles the WIU interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void WIU_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : EXTIT0_IRQHandler
* Description    : This function handles the EXTIT0 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT0_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : EXTIT1_IRQHandler
* Description    : This function handles the EXTIT1 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT1_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : EXTIT2_IRQHandler
* Description    : This function handles the EXTIT2 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT2_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : EXTIT3_IRQHandler
* Description    : This function handles the EXTIT3 interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT3_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : USBWU_IRQHandler
* Description    : This function handles the USBWU interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void USBWU_IRQHandler(void)
{
}
/*******************************************************************************
* Function Name  : PFQBC_IRQHandler
* Description    : This function handles the PFQBC interrupt request
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void PFQBC_IRQHandler(void)
{
}

#if configUSE_WATCHDOG_TICK == 0
	/* The kernel is not using the watchdog interrupt so it can be defined here. */
	void WDG_IRQHandler( void )
	{
	}
#else
	/* The kernel is not using the timer 2 interrupt so it can be defined here. */
	void TIM2_IRQHandler( void )
	{
	}
#endif /* configUSE_WATCHDOG_TICK */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
