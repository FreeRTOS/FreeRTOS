/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_mrcc.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      MRCC software library.
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
#ifndef __75x_MRCC_H
#define __75x_MRCC_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* MRCC Buck-up registers */
typedef enum
{
  MRCC_BKP0,
  MRCC_BKP1
}MRCC_BKPReg;

typedef enum
{
  FREEOSC,
  OSC4MPLL,
  OSC4M,
  CKRTC,
  Disabled,
  OSC4M_Div128,
  LPOSC,
  OSC32K,
  Internal,
  External,
  ON,
  OFF
}CLKSourceTypeDef;


typedef struct
{
  CLKSourceTypeDef CKSYS_Source;  /* FREEOSC, OSC4MPLL, OSC4M, CKRTC */
  CLKSourceTypeDef CKRTC_Source;  /* Disabled, OSC4M_Div128, OSC32K, LPOSC */
  CLKSourceTypeDef CKUSB_Source;  /* Disabled, Internal, External */
  CLKSourceTypeDef PLL_Status;    /* ON, OFF */
  CLKSourceTypeDef OSC4M_Status;  /* ON, OFF */
  CLKSourceTypeDef LPOSC_Status;  /* ON, OFF */
  CLKSourceTypeDef OSC32K_Status; /* ON, OFF */
  u32 CKSYS_Frequency;  
  u32 HCLK_Frequency;   
  u32 CKTIM_Frequency;  
  u32 PCLK_Frequency;   
}MRCC_ClocksTypeDef;

/* Exported constants --------------------------------------------------------*/
/* Oscillator divider by 2 */
#define MRCC_XTDIV2_Disable    0xFFFF7FFF
#define MRCC_XTDIV2_Enable     0x00008000

/* System clock source */
#define MRCC_CKSYS_FREEOSC     0x01
#define MRCC_CKSYS_OSC4M       0x02
#define MRCC_CKSYS_OSC4MPLL    0x03
#define MRCC_CKSYS_RTC         0x04

/* PLL multiplication factors */
#define MRCC_PLL_Disabled    0xFEFFFFFF
#define MRCC_PLL_NoChange    0x00000001
#define MRCC_PLL_Mul_12      0x18000000
#define MRCC_PLL_Mul_14      0x10000000
#define MRCC_PLL_Mul_15      0x08000000
#define MRCC_PLL_Mul_16      0x00000000

/* AHB clock source */
#define MRCC_CKSYS_Div1    0x00000000
#define MRCC_CKSYS_Div2    0x00000008
#define MRCC_CKSYS_Div4    0x00000010
#define MRCC_CKSYS_Div8    0x00000018

/* TIM clock source */
#define MRCC_HCLK_Div1    0x00000000
#define MRCC_HCLK_Div2    0x00000001
#define MRCC_HCLK_Div4    0x00000002
#define MRCC_HCLK_Div8    0x00000003

/* APB clock source */
#define MRCC_CKTIM_Div1    0xFFFFFFFB
#define MRCC_CKTIM_Div2    0x00000004

/* RTC clock sources */
#define MRCC_CKRTC_OSC4M_Div128    0x01000000
#define MRCC_CKRTC_OSC32K          0x02000000
#define MRCC_CKRTC_LPOSC           0x03000000

/* USB clock sources */
#define MRCC_CKUSB_Internal    0xFFBFFFFF
#define MRCC_CKUSB_External    0x00400000

/* MRCC Interrupts */
#define MRCC_IT_LOCK    0x40000000
#define MRCC_IT_NCKD    0x00080000

/* Peripheral Clock */
#define MRCC_Peripheral_ALL      0x1975623F
#define MRCC_Peripheral_EXTIT    0x10000000
#define MRCC_Peripheral_RTC      0x08000000
#define MRCC_Peripheral_GPIO     0x01000000
#define MRCC_Peripheral_UART2    0x00400000
#define MRCC_Peripheral_UART1    0x00200000
#define MRCC_Peripheral_UART0    0x00100000
#define MRCC_Peripheral_I2C      0x00040000
#define MRCC_Peripheral_CAN      0x00010000
#define MRCC_Peripheral_SSP1     0x00004000
#define MRCC_Peripheral_SSP0     0x00002000
#define MRCC_Peripheral_USB      0x00000200
#define MRCC_Peripheral_PWM      0x00000020
#define MRCC_Peripheral_TIM2     0x00000010
#define MRCC_Peripheral_TIM1     0x00000008
#define MRCC_Peripheral_TIM0     0x00000004
#define MRCC_Peripheral_TB       0x00000002
#define MRCC_Peripheral_ADC      0x00000001

/* Clock sources to measure theire frequency */
#define MRCC_ClockSource_CKSYS    0x01
#define MRCC_ClockSource_HCLK     0x02
#define MRCC_ClockSource_PCLK     0x03
#define MRCC_ClockSource_CKTIM    0x04

/* Low Power Debug Mode */
#define MRCC_LPDM_Disable    0xFFFFFFF7
#define MRCC_LPDM_Enable     0x00000008

/* WFI Mode parameters */
#define MRCC_WFIParam_FLASHPowerDown    0x00000000
#define MRCC_WFIParam_FLASHOn           0x00000010
#define MRCC_WFIParam_FLASHOff          0x00004000

/* STOP Mode parameters */
#define MRCC_STOPParam_Default     0x00000000
#define MRCC_STOPParam_OSC4MOff    0x00008000
#define MRCC_STOPParam_FLASHOff    0x00004000
#define MRCC_STOPParam_MVREGOff    0x00002000

/* I/O Pins voltage range */
#define MRCC_IOVoltageRange_5V     0xFFFEFFFF
#define MRCC_IOVoltageRange_3V3    0x00010000

/* Clock sources to output on MCO pin */
#define MRCC_MCO_HCLK          0x00000000
#define MRCC_MCO_PCLK          0x00000040
#define MRCC_MCO_OSC4M         0x00000080
#define MRCC_MCO_CKPLL2        0x000000C0
#define MRCC_MCOPrescaler_1    0xFFFFFFDF
#define MRCC_MCOPrescaler_2    0x00000020

/* 4MHz main oscillator configuration */
#define MRCC_OSC4M_Default    0xFFFCFFFF
#define MRCC_OSC4M_Disable    0x00020000
#define MRCC_OSC4M_Bypass     0x00010000

/* OSC32K oscillator configuration */
#define MRCC_OSC32K_Disable          0xDFFFFFFF
#define MRCC_OSC32K_Enable           0x20000000
#define MRCC_OSC32KBypass_Disable    0xBFFFFFFF
#define MRCC_OSC32KBypass_Enable     0x40000000

/* LPOSC oscillator configuration */
#define MRCC_LPOSC_Disable    0xEFFFFFFF
#define MRCC_LPOSC_Enable     0x10000000

/* RTC measurement configuration */
#define MRCC_RTCM_Disable    0xFBFFFFFF
#define MRCC_RTCM_Enable     0x04000000

/* MRCC Flags */
#define MRCC_FLAG_LOCK         0x3F
#define MRCC_FLAG_LOCKIF       0x3D
#define MRCC_FLAG_CKSEL        0x37
#define MRCC_FLAG_CKOSCSEL     0x35
#define MRCC_FLAG_NCKD         0x32
#define MRCC_FLAG_SWR          0x5D
#define MRCC_FLAG_WDGR         0x5C
#define MRCC_FLAG_EXTR         0x5B
#define MRCC_FLAG_WKP          0x5A
#define MRCC_FLAG_STDB         0x59
#define MRCC_FLAG_BCOUNT       0x58
#define MRCC_FLAG_OSC32KRDY    0x7F
#define MRCC_FLAG_CKRTCOK      0x7B
#define MRCC_FLAG_LPDONE       0x67
#define MRCC_FLAG_LP           0x60

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void MRCC_DeInit(void);
void MRCC_XTDIV2Config(u32 MRCC_XTDIV2);
ErrorStatus MRCC_CKSYSConfig(u32 MRCC_CKSYS, u32 MRCC_PLL);
void MRCC_HCLKConfig(u32 MRCC_HCLK);
void MRCC_CKTIMConfig(u32 MRCC_CKTIM);
void MRCC_PCLKConfig(u32 MRCC_PCLK);
ErrorStatus MRCC_CKRTCConfig(u32 MRCC_CKRTC);
ErrorStatus MRCC_CKUSBConfig(u32 MRCC_CKUSB);
void MRCC_ITConfig(u32 MRCC_IT, FunctionalState NewState);
void MRCC_PeripheralClockConfig(u32 MRCC_Peripheral, FunctionalState NewState);
void MRCC_PeripheralSWResetConfig(u32 MRCC_Peripheral, FunctionalState NewState);
void MRCC_GetClocksStatus(MRCC_ClocksTypeDef*  MRCC_ClocksStatus);
void MRCC_LPMC_DBGConfig(u32 MRCC_LPDM);
void MRCC_EnterWFIMode(u32 MRCC_WFIParam);
void MRCC_EnterSTOPMode(u32 MRCC_STOPParam);
void MRCC_EnterSTANDBYMode(void);
void MRCC_GenerateSWReset(void);
void MRCC_WriteBackupRegister(MRCC_BKPReg MRCC_BKP, u32 Data);
u32 MRCC_ReadBackupRegister(MRCC_BKPReg MRCC_BKP);
void MRCC_IOVoltageRangeConfig(u32 MRCC_IOVoltageRange);
void MRCC_MCOConfig(u32 MRCC_MCO, u32 MCO_MCOPrescaler);
ErrorStatus MRCC_OSC4MConfig(u32 MRCC_OSC4M);
ErrorStatus MRCC_OSC32KConfig(u32 MRCC_OSC32K, u32 MRCC_OSC32KBypass);
ErrorStatus MRCC_LPOSCConfig(u32 MRCC_LPOSC);
void MRCC_RTCMConfig(u32 MRCC_RTCM);
void MRCC_SetBuilderCounter(u8 BuilderCounter);
u16 MRCC_GetCKSYSCounter(void);
FlagStatus MRCC_GetFlagStatus(u8 MRCC_FLAG);
void MRCC_ClearFlag(u8 MRCC_FLAG);
ITStatus MRCC_GetITStatus(u32 MRCC_IT);
void MRCC_ClearITPendingBit(u32 MRCC_IT);
ErrorStatus MRCC_WaitForOSC4MStartUp(void);

#endif /* __75x_MRCC_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
