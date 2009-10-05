/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_scu.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides the SCU library software functions
*                      prototypes & definitions
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
#ifndef __91x_SCU_H
#define __91x_SCU_H

/* Includes ------------------------------------------------------------------*/
#include "91x_map.h"

/* Exported constants --------------------------------------------------------*/

/*MCLK_Source*/
#define SCU_MCLK_PLL      0x0
#define SCU_MCLK_RTC      0x1
#define SCU_MCLK_OSC      0x2

/*RCLK_Divisor*/
#define SCU_RCLK_Div1     0xFFFFFFE3
#define SCU_RCLK_Div2     0x4
#define SCU_RCLK_Div4     0x8
#define SCU_RCLK_Div8     0xC
#define SCU_RCLK_Div16    0x10
#define SCU_RCLK_Div1024  0x14

/*HCLK_Divisor*/
#define SCU_HCLK_Div1 0xFFFFFF9F
#define SCU_HCLK_Div2 0x20
#define SCU_HCLK_Div4 0x40

/*PCLK_Divisor*/
#define SCU_PCLK_Div1 0xFFFFFE7F
#define SCU_PCLK_Div2 0x80
#define SCU_PCLK_Div4 0x100
#define SCU_PCLK_Div8 0x180

/*FMICLK_Divisor*/
#define SCU_FMICLK_Div1 0xFFFEFFFF
#define SCU_FMICLK_Div2 0x10000

/*BRCLK_Divisor*/
#define SCU_BRCLK_Div1 0xFFFFFDFF
#define SCU_BRCLK_Div2 0x200

/*TIMCLK_Source*/
#define SCU_TIMCLK_EXT 0x1
#define SCU_TIMCLK_INT 0x0

/*TIMx*/
#define SCU_TIM01 0x0
#define SCU_TIM23 0x1


/*USBCLK_Source*/
#define SCU_USBCLK_MCLK  0xFFFFF3FF
#define SCU_USBCLK_MCLK2 0x400
#define SCU_USBCLK_EXT   0x800

/*SCU_EMIBCLK*/
#define SCU_EMIBCLK_Div1 0xFFF9FFFF
#define SCU_EMIBCLK_Div2 0x20000

/*SCU_EMIMODE*/
#define SCU_EMI_MUX   0xFFFFFFBF
#define SCU_EMI_DEMUX 0x40

/*SCU_EMIALE_LEN*/
#define SCU_EMIALE_LEN1 0xFFFFFEFF
#define SCU_EMIALE_LEN2 0x100

/*SCU_EMIALE_POL*/
#define SCU_EMIALE_POLLow  0xFFFFFF7F
#define SCU_EMIALE_POLHigh 0x80

/*UART_IrDA_Mode*/
#define SCU_UARTMode_IrDA 0x1
#define SCU_UARTMode_UART 0x0

/*APBPeriph*/
#define __TIM01 0x1
#define __TIM23 0x2
#define __MC    0x4
#define __UART0 0x8
#define __UART1 0x10
#define __UART2 0x20
#define __I2C0  0x40
#define __I2C1  0x80
#define __SSP0  0x100
#define __SSP1  0x200
#define __CAN   0x400
#define __ADC   0x800
#define __WDG   0x1000
#define __WIU   0x2000
#define __GPIO0 0x4000
#define __GPIO1 0x8000
#define __GPIO2 0x10000
#define __GPIO3 0x20000
#define __GPIO4 0x40000
#define __GPIO5 0x80000
#define __GPIO6 0x100000
#define __GPIO7 0x200000
#define __GPIO8 0x400000
#define __GPIO9 0x800000
#define __RTC   0x1000000

/*AHBPeriph*/
#define __FMI          0x1
#define __FPQBC        0x2
#define __SRAM         0x8
#define __SRAM_ARBITER 0x10
#define __VIC          0x20
#define __EMI          0x40
#define __EMI_MEM_CLK  0x80
#define __DMA          0x100
#define __USB          0x200
#define __USB48M       0x400
#define __ENET         0x800
#define __PFQBC_AHB    0x1000

/*SCU_IT*/
#define SCU_IT_LVD_RST    0x10
#define SCU_IT_SRAM_ERROR 0x8
#define SCU_IT_ACK_PFQBC  0x4
#define SCU_IT_LOCK_LOST  0x2
#define SCU_IT_LOCK       0x1

/*SCU_FLAG*/
#define SCU_FLAG_SRAM_ERROR 0x20
#define SCU_FLAG_ACK_PFQBC  0x10
#define SCU_FLAG_LVD_RESET  0x8
#define SCU_FLAG_WDG_RST    0x4
#define SCU_FLAG_LOCK_LOST  0x2
#define SCU_FLAG_LOCK       0x1


/* Module private variables --------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
ErrorStatus SCU_MCLKSourceConfig(u32 MCLK_Source);
ErrorStatus SCU_PLLFactorsConfig(u8 PLLN, u8 PLLM, u8 PLLP);
ErrorStatus SCU_PLLCmd(FunctionalState NewState);
void SCU_RCLKDivisorConfig(u32 RCLK_Divisor);
void SCU_HCLKDivisorConfig(u32 HCLK_Divisor);
void SCU_PCLKDivisorConfig(u32 PCLK_Divisor);
void SCU_APBPeriphClockConfig(u32 APBPeriph, FunctionalState NewState);
void SCU_AHBPeriphClockConfig(u32 AHBPeriph, FunctionalState NewState);
void SCU_APBPeriphReset(u32 APBPeriph, FunctionalState NewState);
void SCU_AHBPeriphReset(u32 AHBPeriph, FunctionalState NewState);
void SCU_APBPeriphIdleConfig(u32 APBPeriph, FunctionalState NewState);
void SCU_AHBPeriphIdleConfig(u32 AHBPeriph, FunctionalState NewState);
void SCU_APBPeriphDebugConfig(u32 APBPeriph, FunctionalState NewState);
void SCU_AHBPeriphDebugConfig(u32 AHBPeriph, FunctionalState NewState);
void SCU_BRCLKDivisorConfig(u32 BRCLK_Divisor);
void SCU_TIMCLKSourceConfig(u8 TIMx, u32 TIMCLK_Source);
void SCU_TIMPresConfig(u8 TIMx, u16 Prescaler);
void SCU_USBCLKConfig(u32 USBCLK_Source);
void SCU_PHYCLKConfig(FunctionalState NewState);
void SCU_FMICLKDivisorConfig(u32 FMICLK_Divisor);
void SCU_EMIBCLKDivisorConfig(u32 SCU_EMIBCLK);
void SCU_EMIModeConfig(u32 SCU_EMIMODE);
void SCU_EMIALEConfig(u32 SCU_EMIALE_LEN, u32 SCU_EMIALE_POL);
void SCU_ITConfig(u32 SCU_IT, FunctionalState NewState);
FlagStatus SCU_GetFlagStatus(u32 SCU_Flag);
void SCU_ClearFlag(u32 SCU_Flag);
u32 SCU_GetPLLFreqValue(void);
u32 SCU_GetMCLKFreqValue(void);
u32 SCU_GetRCLKFreqValue(void);
u32 SCU_GetHCLKFreqValue(void);
u32 SCU_GetPCLKFreqValue(void);
void SCU_WakeUpLineConfig(u8 EXTint);
void SCU_SpecIntRunModeConfig(FunctionalState NewState);
void SCU_EnterIdleMode(void);
void SCU_EnterSleepMode(void);
void SCU_UARTIrDASelect(UART_TypeDef * UARTx, u8 UART_IrDA_Mode);
void SCU_PFQBCCmd(FunctionalState NewState);

#endif /*__91x_SCU_H*/

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
