/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_vector.c
* Author             : MCD Tools Team
* Date First Issued  : 05/14/2007
* Description        : This file contains the vector table for STM32F10x.
*                     	 After Reset the Cortex-M3 processor is in Thread mode,
*                     	 priority is Privileged, and the Stack is set to Main.
********************************************************************************
* History:
* 05/14/2007: V0.2
*
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ----------------------------------------------------------------------*/

void NMIException(void);
void HardFaultException(void);
void MemManageException(void);
void BusFaultException(void);
void UsageFaultException(void);
void DebugMonitor(void);
void SVCHandler(void);
void PendSVC(void);
void SysTickHandler(void);
void WWDG_IRQHandler(void);
void PVD_IRQHandler(void);
void TAMPER_IRQHandler(void);
void RTC_IRQHandler(void);
void FLASH_IRQHandler(void);
void RCC_IRQHandler(void);
void EXTI0_IRQHandler(void);
void EXTI1_IRQHandler(void);
void EXTI2_IRQHandler(void);
void EXTI3_IRQHandler(void);
void EXTI4_IRQHandler(void);
void DMAChannel1_IRQHandler(void);
void DMAChannel2_IRQHandler(void);
void DMAChannel3_IRQHandler(void);
void DMAChannel4_IRQHandler(void);
void DMAChannel5_IRQHandler(void);
void DMAChannel6_IRQHandler(void);
void DMAChannel7_IRQHandler(void);
void ADC_IRQHandler(void);
void USB_HP_CAN_TX_IRQHandler(void);
void USB_LP_CAN_RX0_IRQHandler(void);
void CAN_RX1_IRQHandler(void);
void CAN_SCE_IRQHandler(void);
void EXTI9_5_IRQHandler(void);
void TIM1_BRK_IRQHandler(void);
void TIM1_UP_IRQHandler(void);
void TIM1_TRG_COM_IRQHandler(void);
void TIM1_CC_IRQHandler(void);
void TIM2_IRQHandler(void);
void TIM3_IRQHandler(void);
void TIM4_IRQHandler(void);
void I2C1_EV_IRQHandler(void);
void I2C1_ER_IRQHandler(void);
void I2C2_EV_IRQHandler(void);
void I2C2_ER_IRQHandler(void);
void SPI1_IRQHandler(void);
void SPI2_IRQHandler(void);
void USART1_IRQHandler(void);
void USART2_IRQHandler(void);
void USART3_IRQHandler(void);
void EXTI15_10_IRQHandler(void);
void RTCAlarm_IRQHandler(void);
void USBWakeUp_IRQHandler(void);


/* Exported types --------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
extern unsigned long _etext;
extern unsigned long _sidata;		/* start address for the initialization values of the .data section. defined in linker script */
extern unsigned long _sdata;		/* start address for the .data section. defined in linker script */
extern unsigned long _edata;		/* end address for the .data section. defined in linker script */

extern unsigned long _sbss;			/* start address for the .bss section. defined in linker script */
extern unsigned long _ebss;			/* end address for the .bss section. defined in linker script */

extern void _estack;		/* init value for the stack pointer. defined in linker script */



/* Private typedef -----------------------------------------------------------*/
/* function prototypes ------------------------------------------------------*/
void Reset_Handler(void) __attribute__((__interrupt__));
extern int main(void);
extern void xPortPendSVHandler(void);
extern void xPortSysTickHandler(void);
extern void vTimer2IntHandler( void );
extern void vPortSVCHandler( void );


/******************************************************************************
*
* The minimal vector table for a Cortex M3.  Note that the proper constructs
* must be placed on this to ensure that it ends up at physical address
* 0x0000.0000.
*
******************************************************************************/


__attribute__ ((section(".isr_vector")))
void (* const g_pfnVectors[])(void) =
{
  &_estack,            // The initial stack pointer
  Reset_Handler,             // The reset handler
  NMIException,
  HardFaultException,
  MemManageException,
  BusFaultException,
  UsageFaultException,
  (void*)0, (void*)0, (void*)0, (void*)0,            /* Reserved */ 
  vPortSVCHandler,
  DebugMonitor,
  (void*)0,                      /* Reserved */
  xPortPendSVHandler,
  xPortSysTickHandler,
  WWDG_IRQHandler,
  PVD_IRQHandler,
  TAMPER_IRQHandler,
  RTC_IRQHandler,
  FLASH_IRQHandler,
  RCC_IRQHandler,
  EXTI0_IRQHandler,
  EXTI1_IRQHandler,
  EXTI2_IRQHandler,
  EXTI3_IRQHandler,
  EXTI4_IRQHandler,
  DMAChannel1_IRQHandler,
  DMAChannel2_IRQHandler,
  DMAChannel3_IRQHandler,
  DMAChannel4_IRQHandler,
  DMAChannel5_IRQHandler,
  DMAChannel6_IRQHandler,
  DMAChannel7_IRQHandler,
  ADC_IRQHandler,
  USB_HP_CAN_TX_IRQHandler,
  USB_LP_CAN_RX0_IRQHandler,
  CAN_RX1_IRQHandler,
  CAN_SCE_IRQHandler,
  EXTI9_5_IRQHandler,
  TIM1_BRK_IRQHandler,
  TIM1_UP_IRQHandler,
  TIM1_TRG_COM_IRQHandler,
  TIM1_CC_IRQHandler,
  vTimer2IntHandler,
  TIM3_IRQHandler,
  TIM4_IRQHandler,
  I2C1_EV_IRQHandler,
  I2C1_ER_IRQHandler,
  I2C2_EV_IRQHandler,
  I2C2_ER_IRQHandler,
  SPI1_IRQHandler,
  SPI2_IRQHandler,
  USART1_IRQHandler,
  USART2_IRQHandler,
  USART3_IRQHandler,
  EXTI15_10_IRQHandler,
  RTCAlarm_IRQHandler,
  USBWakeUp_IRQHandler,
  (void*)0,
  (void*)0,
  (void*)0,
  (void*)0,
  (void*)0,
  (void*)0,
  (void*)0,
  (void*)0xF108F85F //this is a workaround for boot in RAM mode.
};

/*******************************************************************************
* Function Name  : Reset_Handler
* Description    : This is the code that gets called when the processor first starts execution
*		       following a reset event.  Only the absolutely necessary set is performed,
*		       after which the application supplied main() routine is called. 
* Input          :
* Output         :
* Return         :
*******************************************************************************/
void Reset_Handler(void)
{
    unsigned long *pulSrc, *pulDest;

    //
    // Copy the data segment initializers from flash to SRAM.
    //
    pulSrc = &_sidata;
    for(pulDest = &_sdata; pulDest < &_edata; )
    {
        *(pulDest++) = *(pulSrc++);
    }

    //
    // Zero fill the bss segment.
    //
    for(pulDest = &_sbss; pulDest < &_ebss; )
    {
        *(pulDest++) = 0;
    }

    //
    // Call the application's entry point.
    //
    main();
}


/********************* (C) COPYRIGHT 2007 STMicroelectronics  *****END OF FILE****/


