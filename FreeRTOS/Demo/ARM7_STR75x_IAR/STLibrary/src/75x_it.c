/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_it.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : Main Interrupt Service Routines.
*                      This file can be used to describe all the exceptions
*                      subroutines that may occur within user application.
*                      When an interrupt happens, the software will branch
*                      automatically to the corresponding routine according
*                      to the interrupt vector loaded in the PC register.
*                      The following routines are all empty, user can write code
*                      for exceptions handlers and peripherals IRQ interrupts.
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

/* Includes ------------------------------------------------------------------*/
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : Undefined_Handler
* Description    : This function handles Undefined instruction exception.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void Undefined_Handler(void)
{
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
}

/*******************************************************************************
* Function Name  : WAKUP_IRQHandler
* Description    : This function handles External line 15(WAKUP) interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void WAKUP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM2_OC2_IRQHandler
* Description    : This function handles TIM2 Output Compare 2 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM2_OC2_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM2_OC1_IRQHandler
* Description    : This function handles TIM2 Output Compare 1 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM2_OC1_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM2_IC12_IRQHandler
* Description    : This function handles TIM2 Input Capture 1 & 2 interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM2_IC12_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM2_UP_IRQHandler
* Description    : This function handles TIM2 Update interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM2_UP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM1_OC2_IRQHandler
* Description    : This function handles TIM1 Output Compare 2 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC2_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM1_OC1_IRQHandler
* Description    : This function handles TIM1 Output Compare 1 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_OC1_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM1_IC12_IRQHandler
* Description    : This function handles TIM1 Input Capture 1 & 2 interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_IC12_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM1_UP_IRQHandler
* Description    : This function handles TIM1 Update interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM1_UP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM0_OC2_IRQHandler
* Description    : This function handles TIM0 Output Compare 2 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM0_OC2_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM0_OC1_IRQHandler
* Description    : This function handles TIM0 Output Compare 1 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM0_OC1_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM0_IC12_IRQHandler
* Description    : This function handles TIM0 Input Capture 1 & 2 interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM0_IC12_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TIM0_UP_IRQHandler
* Description    : This function handles TIM0 Update interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TIM0_UP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : PWM_OC123_IRQHandler
* Description    : This function handles PWM Output Compare 1,2&3 interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_OC123_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : PWM_EM_IRQHandler
* Description    : This function handles PWM Emergency interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_EM_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : PWM_UP_IRQHandler
* Description    : This function handles PWM Update interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void PWM_UP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : I2C_IRQHandler
* Description    : This function handles I2C global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void I2C_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : SSP1_IRQHandler
* Description    : This function handles SSP1 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SSP1_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : SSP0_IRQHandler
* Description    : This function handles SSP0 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SSP0_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : UART2_IRQHandler
* Description    : This function handles UART2 global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void UART2_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : UART1_IRQHandler
* Description    : This function handles UART1 global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void UART1_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : UART0_IRQHandler
* Description    : This function handles UART0 global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void UART0_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : CAN_IRQHandler
* Description    : This function handles CAN global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void CAN_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : USBLP_IRQHandler
* Description    : This function handles USB Low Priority event interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void USB_LP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : USBHP_IRQHandler
* Description    : This function handles USB High Priority event interrupt
*                  request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void USB_HP_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : ADC_IRQHandler
* Description    : This function handles ADC global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : DMA_IRQHandler
* Description    : This function handles DMA global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void DMA_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : EXTIT_IRQHandler
* Description    : This function handles External lines 14 to 1 interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void EXTIT_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : MRCC_IRQHandler
* Description    : This function handles MRCC interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void MRCC_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : FLASHSMI_IRQHandler
* Description    : This function handles Flash and SMI global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void FLASHSMI_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : RTC_IRQHandler
* Description    : This function handles RTC global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void RTC_IRQHandler(void)
{
}

/*******************************************************************************
* Function Name  : TB_IRQHandler
* Description    : This function handles TB global interrupt request.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void TB_IRQHandler(void)
{
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
