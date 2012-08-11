/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_map.h
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file contains all the peripheral register's definitions
*                      and memory mapping.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F10x_MAP_H
#define __STM32F10x_MAP_H

#ifndef EXT
  #define EXT extern
#endif /* EXT */

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_conf.h"
#include "stm32f10x_type.h"
#include "cortexm3_macro.h"

/* Exported types ------------------------------------------------------------*/
/******************************************************************************/
/*                          IP registers structures                           */
/******************************************************************************/

/*------------------------ Analog to Digital Converter -----------------------*/
typedef struct
{
  vu32 SR;
  vu32 CR1;
  vu32 CR2;
  vu32 SMPR1;
  vu32 SMPR2;
  vu32 JOFR1;
  vu32 JOFR2;
  vu32 JOFR3;
  vu32 JOFR4;
  vu32 HTR;
  vu32 LTR;
  vu32 SQR1;
  vu32 SQR2;
  vu32 SQR3;
  vu32 JSQR;
  vu32 JDR1;
  vu32 JDR2;
  vu32 JDR3;
  vu32 JDR4;
  vu32 DR;
} ADC_TypeDef;

/*------------------------ Backup Registers ----------------------------------*/
typedef struct
{
  u32 RESERVED0;
  vu16 DR1;
  u16  RESERVED1;
  vu16 DR2;
  u16  RESERVED2;
  vu16 DR3;
  u16  RESERVED3;
  vu16 DR4;
  u16  RESERVED4;
  vu16 DR5;
  u16  RESERVED5;
  vu16 DR6;
  u16  RESERVED6;
  vu16 DR7;
  u16  RESERVED7;
  vu16 DR8;
  u16  RESERVED8;
  vu16 DR9;
  u16  RESERVED9;
  vu16 DR10;
  u16  RESERVED10;
  vu16 RTCCR;
  u16  RESERVED11;
  vu16 CR;
  u16  RESERVED12;
  vu16 CSR;
  u16  RESERVED13;
} BKP_TypeDef;

/*------------------------ Controller Area Network ---------------------------*/
typedef struct
{
  vu32 TIR;
  vu32 TDTR;
  vu32 TDLR;
  vu32 TDHR;
} CAN_TxMailBox_TypeDef;

typedef struct
{
  vu32 RIR;
  vu32 RDTR;
  vu32 RDLR;
  vu32 RDHR;
} CAN_FIFOMailBox_TypeDef;

typedef struct
{
  vu32 FR0;
  vu32 FR1;
} CAN_FilterRegister_TypeDef;

typedef struct
{
  vu32 MCR;
  vu32 MSR;
  vu32 TSR;
  vu32 RF0R;
  vu32 RF1R;
  vu32 IER;
  vu32 ESR;
  vu32 BTR;
  u32 RESERVED0[88];
  CAN_TxMailBox_TypeDef sTxMailBox[3];
  CAN_FIFOMailBox_TypeDef sFIFOMailBox[2];
  u32 RESERVED1[12];
  vu32 FMR;
  vu32 FM0R;
  u32 RESERVED2[1];
  vu32 FS0R;
  u32 RESERVED3[1];
  vu32 FFA0R;
  u32 RESERVED4[1];
  vu32 FA0R;
  u32 RESERVED5[8];
  CAN_FilterRegister_TypeDef sFilterRegister[14];
} CAN_TypeDef;

/*------------------------ DMA Controller ------------------------------------*/
typedef struct
{
  vu32 CCR;
  vu32 CNDTR;
  vu32 CPAR;
  vu32 CMAR;
} DMA_Channel_TypeDef;

typedef struct
{
  vu32 ISR;
  vu32 IFCR;
} DMA_TypeDef;

/*------------------------ External Interrupt/Event Controller ---------------*/
typedef struct
{
  vu32 IMR;
  vu32 EMR;
  vu32 RTSR;
  vu32 FTSR;
  vu32 SWIER;
  vu32 PR;
} EXTI_TypeDef;

/*------------------------ FLASH and Option Bytes Registers ------------------*/
typedef struct
{
  vu32 ACR;
  vu32 KEYR;
  vu32 OPTKEYR;
  vu32 SR;
  vu32 CR;
  vu32 AR;
  vu32 RESERVED;
  vu32 OBR;
  vu32 WRPR;
} FLASH_TypeDef;

typedef struct
{
  vu16 RDP;
  vu16 USER;
  vu16 Data0;
  vu16 Data1;
  vu16 WRP0;
  vu16 WRP1;
  vu16 WRP2;
  vu16 WRP3;
} OB_TypeDef;

/*------------------------ General Purpose and Alternate Function IO ---------*/
typedef struct
{
  vu32 CRL;
  vu32 CRH;
  vu32 IDR;
  vu32 ODR;
  vu32 BSRR;
  vu32 BRR;
  vu32 LCKR;
} GPIO_TypeDef;

typedef struct
{
  vu32 EVCR;
  vu32 MAPR;
  vu32 EXTICR[4];
} AFIO_TypeDef;

/*------------------------ Inter-integrated Circuit Interface ----------------*/
typedef struct
{
  vu16 CR1;
  u16 RESERVED0;
  vu16 CR2;
  u16 RESERVED1;
  vu16 OAR1;
  u16 RESERVED2;
  vu16 OAR2;
  u16 RESERVED3;
  vu16 DR;
  u16 RESERVED4;
  vu16 SR1;
  u16 RESERVED5;
  vu16 SR2;
  u16 RESERVED6;
  vu16 CCR;
  u16 RESERVED7;
  vu16 TRISE;
  u16 RESERVED8;
} I2C_TypeDef;

/*------------------------ Independent WATCHDOG ------------------------------*/
typedef struct
{
  vu32 KR;
  vu32 PR;
  vu32 RLR;
  vu32 SR;
} IWDG_TypeDef;

/*------------------------ Nested Vectored Interrupt Controller --------------*/
typedef struct
{
  vu32 Enable[2];
  u32 RESERVED0[30];
  vu32 Disable[2];
  u32 RSERVED1[30];
  vu32 Set[2];
  u32 RESERVED2[30];
  vu32 Clear[2];
  u32 RESERVED3[30];
  vu32 Active[2];
  u32 RESERVED4[62];
  vu32 Priority[11];
} NVIC_TypeDef;

typedef struct
{
  vu32 CPUID;
  vu32 IRQControlState;
  vu32 ExceptionTableOffset;
  vu32 AIRC;
  vu32 SysCtrl;
  vu32 ConfigCtrl;
  vu32 SystemPriority[3];
  vu32 SysHandlerCtrl;
  vu32 ConfigFaultStatus;
  vu32 HardFaultStatus;
  vu32 DebugFaultStatus;
  vu32 MemoryManageFaultAddr;
  vu32 BusFaultAddr;
} SCB_TypeDef;

/*------------------------ Power Controller ----------------------------------*/
typedef struct
{
  vu32 CR;
  vu32 CSR;
} PWR_TypeDef;

/*------------------------ Reset and Clock Controller ------------------------*/
typedef struct
{
  vu32 CR;
  vu32 CFGR;
  vu32 CIR;
  vu32 APB2RSTR;
  vu32 APB1RSTR;
  vu32 AHBENR;
  vu32 APB2ENR;
  vu32 APB1ENR;
  vu32 BDCR;
  vu32 CSR;
} RCC_TypeDef;

/*------------------------ Real-Time Clock -----------------------------------*/
typedef struct
{
  vu16 CRH;
  u16 RESERVED0;
  vu16 CRL;
  u16 RESERVED1;
  vu16 PRLH;
  u16 RESERVED2;
  vu16 PRLL;
  u16 RESERVED3;
  vu16 DIVH;
  u16 RESERVED4;
  vu16 DIVL;
  u16 RESERVED5;
  vu16 CNTH;
  u16 RESERVED6;
  vu16 CNTL;
  u16 RESERVED7;
  vu16 ALRH;
  u16 RESERVED8;
  vu16 ALRL;
  u16 RESERVED9;
} RTC_TypeDef;

/*------------------------ Serial Peripheral Interface -----------------------*/
typedef struct
{
  vu16 CR1;
  u16 RESERVED0;
  vu16 CR2;
  u16 RESERVED1;
  vu16 SR;
  u16  RESERVED2;
  vu16 DR;
  u16  RESERVED3;
  vu16 CRCPR;
  u16 RESERVED4;
  vu16 RXCRCR;
  u16  RESERVED5;
  vu16 TXCRCR;
  u16  RESERVED6;
} SPI_TypeDef;

/*------------------------ SystemTick ----------------------------------------*/
typedef struct
{
  vu32 CTRL;
  vu32 LOAD;
  vu32 VAL;
  vuc32 CALIB;
} SysTick_TypeDef;

/*------------------------ Advanced Control Timer ----------------------------*/
typedef struct
{
  vu16 CR1;
  u16 RESERVED0;
  vu16 CR2;
  u16 RESERVED1;
  vu16 SMCR;
  u16 RESERVED2;
  vu16 DIER;
  u16 RESERVED3;
  vu16 SR;
  u16 RESERVED4;
  vu16 EGR;
  u16 RESERVED5;
  vu16 CCMR1;
  u16 RESERVED6;
  vu16 CCMR2;
  u16 RESERVED7;
  vu16 CCER;
  u16 RESERVED8;
  vu16 CNT;
  u16 RESERVED9;
  vu16 PSC;
  u16 RESERVED10;
  vu16 ARR;
  u16 RESERVED11;
  vu16 RCR;
  u16 RESERVED12;
  vu16 CCR1;
  u16 RESERVED13;
  vu16 CCR2;
  u16 RESERVED14;
  vu16 CCR3;
  u16 RESERVED15;
  vu16 CCR4;
  u16 RESERVED16;
  vu16 BDTR;
  u16 RESERVED17;
  vu16 DCR;
  u16 RESERVED18;
  vu16 DMAR;
  u16 RESERVED19;
} TIM1_TypeDef;

/*------------------------ General Purpose Timer -----------------------------*/
typedef struct
{
  vu16 CR1;
  u16 RESERVED0;
  vu16 CR2;
  u16 RESERVED1;
  vu16 SMCR;
  u16 RESERVED2;
  vu16 DIER;
  u16 RESERVED3;
  vu16 SR;
  u16 RESERVED4;
  vu16 EGR;
  u16 RESERVED5;
  vu16 CCMR1;
  u16 RESERVED6;
  vu16 CCMR2;
  u16 RESERVED7;
  vu16 CCER;
  u16 RESERVED8;
  vu16 CNT;
  u16 RESERVED9;
  vu16 PSC;
  u16 RESERVED10;
  vu16 ARR;
  u16 RESERVED11[3];
  vu16 CCR1;
  u16 RESERVED12;
  vu16 CCR2;
  u16 RESERVED13;
  vu16 CCR3;
  u16 RESERVED14;
  vu16 CCR4;
  u16 RESERVED15[3];
  vu16 DCR;
  u16 RESERVED16;
  vu16 DMAR;
  u16 RESERVED17;
} TIM_TypeDef;

/*----------------- Universal Synchronous Asynchronous Receiver Transmitter --*/
typedef struct
{
  vu16 SR;
  u16 RESERVED0;
  vu16 DR;
  u16 RESERVED1;
  vu16 BRR;
  u16 RESERVED2;
  vu16 CR1;
  u16 RESERVED3;
  vu16 CR2;
  u16 RESERVED4;
  vu16 CR3;
  u16 RESERVED5;
  vu16 GTPR;
  u16 RESERVED6;
} USART_TypeDef;

/*------------------------ Window WATCHDOG -----------------------------------*/
typedef struct
{
  vu32 CR;
  vu32 CFR;
  vu32 SR;
} WWDG_TypeDef;

/******************************************************************************/
/*                       Peripheral memory map                                */
/******************************************************************************/
/* Peripheral and SRAM base address in the alias region */
#define PERIPH_BB_BASE        ((u32)0x42000000)
#define SRAM_BB_BASE          ((u32)0x22000000)

/* Peripheral and SRAM base address in the bit-band region */
#define SRAM_BASE             ((u32)0x20000000)
#define PERIPH_BASE           ((u32)0x40000000)

/* Flash refisters base address */
#define FLASH_BASE            ((u32)0x40022000)
/* Flash Option Bytes base address */
#define OB_BASE               ((u32)0x1FFFF800)

/* Peripheral memory map */
#define APB1PERIPH_BASE       PERIPH_BASE
#define APB2PERIPH_BASE       (PERIPH_BASE + 0x10000)
#define AHBPERIPH_BASE        (PERIPH_BASE + 0x20000)

#define TIM2_BASE             (APB1PERIPH_BASE + 0x0000)
#define TIM3_BASE             (APB1PERIPH_BASE + 0x0400)
#define TIM4_BASE             (APB1PERIPH_BASE + 0x0800)
#define RTC_BASE              (APB1PERIPH_BASE + 0x2800)
#define WWDG_BASE             (APB1PERIPH_BASE + 0x2C00)
#define IWDG_BASE             (APB1PERIPH_BASE + 0x3000)
#define SPI2_BASE             (APB1PERIPH_BASE + 0x3800)
#define USART2_BASE           (APB1PERIPH_BASE + 0x4400)
#define USART3_BASE           (APB1PERIPH_BASE + 0x4800)
#define I2C1_BASE             (APB1PERIPH_BASE + 0x5400)
#define I2C2_BASE             (APB1PERIPH_BASE + 0x5800)
#define CAN_BASE              (APB1PERIPH_BASE + 0x6400)
#define BKP_BASE              (APB1PERIPH_BASE + 0x6C00)
#define PWR_BASE              (APB1PERIPH_BASE + 0x7000)

#define AFIO_BASE             (APB2PERIPH_BASE + 0x0000)
#define EXTI_BASE             (APB2PERIPH_BASE + 0x0400)
#define GPIOA_BASE            (APB2PERIPH_BASE + 0x0800)
#define GPIOB_BASE            (APB2PERIPH_BASE + 0x0C00)
#define GPIOC_BASE            (APB2PERIPH_BASE + 0x1000)
#define GPIOD_BASE            (APB2PERIPH_BASE + 0x1400)
#define GPIOE_BASE            (APB2PERIPH_BASE + 0x1800)
#define ADC1_BASE             (APB2PERIPH_BASE + 0x2400)
#define ADC2_BASE             (APB2PERIPH_BASE + 0x2800)
#define TIM1_BASE             (APB2PERIPH_BASE + 0x2C00)
#define SPI1_BASE             (APB2PERIPH_BASE + 0x3000)
#define USART1_BASE           (APB2PERIPH_BASE + 0x3800)

#define DMA_BASE              (AHBPERIPH_BASE + 0x0000)
#define DMA_Channel1_BASE     (AHBPERIPH_BASE + 0x0008)
#define DMA_Channel2_BASE     (AHBPERIPH_BASE + 0x001C)
#define DMA_Channel3_BASE     (AHBPERIPH_BASE + 0x0030)
#define DMA_Channel4_BASE     (AHBPERIPH_BASE + 0x0044)
#define DMA_Channel5_BASE     (AHBPERIPH_BASE + 0x0058)
#define DMA_Channel6_BASE     (AHBPERIPH_BASE + 0x006C)
#define DMA_Channel7_BASE     (AHBPERIPH_BASE + 0x0080)
#define RCC_BASE              (AHBPERIPH_BASE + 0x1000)

/* System Control Space memory map */
#define SCS_BASE              ((u32)0xE000E000)

#define SysTick_BASE          (SCS_BASE + 0x0010)
#define NVIC_BASE             (SCS_BASE + 0x0100)
#define SCB_BASE              (SCS_BASE + 0x0D00)


/******************************************************************************/
/*                            IPs' declaration                                */
/******************************************************************************/

/*------------------- Non Debug Mode -----------------------------------------*/
#ifndef DEBUG
#ifdef _TIM2
  #define TIM2                  ((TIM_TypeDef *) TIM2_BASE)
#endif /*_TIM2 */

#ifdef _TIM3
  #define TIM3                  ((TIM_TypeDef *) TIM3_BASE)
#endif /*_TIM3 */

#ifdef _TIM4
  #define TIM4                  ((TIM_TypeDef *) TIM4_BASE)
#endif /*_TIM4 */

#ifdef _RTC
  #define RTC                   ((RTC_TypeDef *) RTC_BASE)
#endif /*_RTC */

#ifdef _WWDG
  #define WWDG                  ((WWDG_TypeDef *) WWDG_BASE)
#endif /*_WWDG */

#ifdef _IWDG
  #define IWDG                  ((IWDG_TypeDef *) IWDG_BASE)
#endif /*_IWDG */

#ifdef _SPI2
  #define SPI2                  ((SPI_TypeDef *) SPI2_BASE)
#endif /*_SPI2 */

#ifdef _USART2
  #define USART2                ((USART_TypeDef *) USART2_BASE)
#endif /*_USART2 */

#ifdef _USART3
  #define USART3                ((USART_TypeDef *) USART3_BASE)
#endif /*_USART3 */

#ifdef _I2C1
  #define I2C1                  ((I2C_TypeDef *) I2C1_BASE)
#endif /*_I2C1 */

#ifdef _I2C2
  #define I2C2                  ((I2C_TypeDef *) I2C2_BASE)
#endif /*_I2C2 */

#ifdef _CAN
  #define CAN                   ((CAN_TypeDef *) CAN_BASE)
#endif /*_CAN */

#ifdef _BKP
  #define BKP                   ((BKP_TypeDef *) BKP_BASE)
#endif /*_BKP */

#ifdef _PWR
  #define PWR                   ((PWR_TypeDef *) PWR_BASE)
#endif /*_PWR */

#ifdef _AFIO
  #define AFIO                  ((AFIO_TypeDef *) AFIO_BASE)
#endif /*_AFIO */

#ifdef _EXTI
  #define EXTI                  ((EXTI_TypeDef *) EXTI_BASE)
#endif /*_EXTI */

#ifdef _GPIOA
  #define GPIOA                 ((GPIO_TypeDef *) GPIOA_BASE)
#endif /*_GPIOA */

#ifdef _GPIOB
  #define GPIOB                 ((GPIO_TypeDef *) GPIOB_BASE)
#endif /*_GPIOB */

#ifdef _GPIOC
  #define GPIOC                 ((GPIO_TypeDef *) GPIOC_BASE)
#endif /*_GPIOC */

#ifdef _GPIOD
  #define GPIOD                 ((GPIO_TypeDef *) GPIOD_BASE)
#endif /*_GPIOD */

#ifdef _GPIOE
  #define GPIOE                 ((GPIO_TypeDef *) GPIOE_BASE)
#endif /*_GPIOE */

#ifdef _ADC1
  #define ADC1                  ((ADC_TypeDef *) ADC1_BASE)
#endif /*_ADC1 */

#ifdef _ADC2
  #define ADC2                  ((ADC_TypeDef *) ADC2_BASE)
#endif /*_ADC2 */

#ifdef _TIM1
  #define TIM1                  ((TIM1_TypeDef *) TIM1_BASE)
#endif /*_TIM1 */

#ifdef _SPI1
  #define SPI1                  ((SPI_TypeDef *) SPI1_BASE)
#endif /*_SPI1 */

#ifdef _USART1
  #define USART1                ((USART_TypeDef *) USART1_BASE)
#endif /*_USART1 */

#ifdef _DMA
  #define DMA                   ((DMA_TypeDef *) DMA_BASE)
#endif /*_DMA */

#ifdef _DMA_Channel1
  #define DMA_Channel1          ((DMA_Channel_TypeDef *) DMA_Channel1_BASE)
#endif /*_DMA_Channel1 */

#ifdef _DMA_Channel2
  #define DMA_Channel2          ((DMA_Channel_TypeDef *) DMA_Channel2_BASE)
#endif /*_DMA_Channel2 */

#ifdef _DMA_Channel3
  #define DMA_Channel3          ((DMA_Channel_TypeDef *) DMA_Channel3_BASE)
#endif /*_DMA_Channel3 */

#ifdef _DMA_Channel4
  #define DMA_Channel4          ((DMA_Channel_TypeDef *) DMA_Channel4_BASE)
#endif /*_DMA_Channel4 */

#ifdef _DMA_Channel5
  #define DMA_Channel5          ((DMA_Channel_TypeDef *) DMA_Channel5_BASE)
#endif /*_DMA_Channel5 */

#ifdef _DMA_Channel6
  #define DMA_Channel6          ((DMA_Channel_TypeDef *) DMA_Channel6_BASE)
#endif /*_DMA_Channel6 */

#ifdef _DMA_Channel7
  #define DMA_Channel7          ((DMA_Channel_TypeDef *) DMA_Channel7_BASE)
#endif /*_DMA_Channel7 */

#ifdef _FLASH
  #define FLASH                 ((FLASH_TypeDef *) FLASH_BASE)
  #define OB                    ((OB_TypeDef *) OB_BASE) 
#endif /*_FLASH */

#ifdef _RCC
  #define RCC                   ((RCC_TypeDef *) RCC_BASE)
#endif /*_RCC */

#ifdef _SysTick
  #define SysTick               ((SysTick_TypeDef *) SysTick_BASE)
#endif /*_SysTick */

#ifdef _NVIC
  #define NVIC                  ((NVIC_TypeDef *) NVIC_BASE)
#endif /*_NVIC */

#ifdef _SCB
  #define SCB                   ((SCB_TypeDef *) SCB_BASE)
#endif /*_SCB */
/*----------------------  Debug Mode -----------------------------------------*/
#else   /* DEBUG */
#ifdef _TIM2
  EXT TIM_TypeDef             *TIM2;
#endif /*_TIM2 */

#ifdef _TIM3
  EXT TIM_TypeDef             *TIM3;
#endif /*_TIM3 */

#ifdef _TIM4
  EXT TIM_TypeDef             *TIM4;
#endif /*_TIM4 */

#ifdef _RTC
  EXT RTC_TypeDef             *RTC;
#endif /*_RTC */

#ifdef _WWDG
  EXT WWDG_TypeDef            *WWDG;
#endif /*_WWDG */

#ifdef _IWDG
  EXT IWDG_TypeDef            *IWDG;
#endif /*_IWDG */

#ifdef _SPI2
  EXT SPI_TypeDef             *SPI2;
#endif /*_SPI2 */

#ifdef _USART2
  EXT USART_TypeDef           *USART2;
#endif /*_USART2 */

#ifdef _USART3
  EXT USART_TypeDef           *USART3;
#endif /*_USART3 */

#ifdef _I2C1
  EXT I2C_TypeDef             *I2C1;
#endif /*_I2C1 */

#ifdef _I2C2
  EXT I2C_TypeDef             *I2C2;
#endif /*_I2C2 */

#ifdef _CAN
  EXT CAN_TypeDef             *CAN;
#endif /*_CAN */

#ifdef _BKP
  EXT BKP_TypeDef             *BKP;
#endif /*_BKP */

#ifdef _PWR
  EXT PWR_TypeDef             *PWR;
#endif /*_PWR */

#ifdef _AFIO
  EXT AFIO_TypeDef            *AFIO;
#endif /*_AFIO */

#ifdef _EXTI
  EXT EXTI_TypeDef            *EXTI;
#endif /*_EXTI */

#ifdef _GPIOA
  EXT GPIO_TypeDef            *GPIOA;
#endif /*_GPIOA */

#ifdef _GPIOB
  EXT GPIO_TypeDef            *GPIOB;
#endif /*_GPIOB */

#ifdef _GPIOC
  EXT GPIO_TypeDef            *GPIOC;
#endif /*_GPIOC */

#ifdef _GPIOD
  EXT GPIO_TypeDef            *GPIOD;
#endif /*_GPIOD */

#ifdef _GPIOE
  EXT GPIO_TypeDef            *GPIOE;
#endif /*_GPIOE */

#ifdef _ADC1
  EXT ADC_TypeDef             *ADC1;
#endif /*_ADC1 */

#ifdef _ADC2
  EXT ADC_TypeDef             *ADC2;
#endif /*_ADC2 */

#ifdef _TIM1
  EXT TIM1_TypeDef            *TIM1;
#endif /*_TIM1 */

#ifdef _SPI1
  EXT SPI_TypeDef             *SPI1;
#endif /*_SPI1 */

#ifdef _USART1
  EXT USART_TypeDef           *USART1;
#endif /*_USART1 */

#ifdef _DMA
  EXT DMA_TypeDef             *DMA;
#endif /*_DMA */

#ifdef _DMA_Channel1
  EXT DMA_Channel_TypeDef     *DMA_Channel1;
#endif /*_DMA_Channel1 */

#ifdef _DMA_Channel2
  EXT DMA_Channel_TypeDef     *DMA_Channel2;
#endif /*_DMA_Channel2 */

#ifdef _DMA_Channel3
  EXT DMA_Channel_TypeDef     *DMA_Channel3;
#endif /*_DMA_Channel3 */

#ifdef _DMA_Channel4
  EXT DMA_Channel_TypeDef     *DMA_Channel4;
#endif /*_DMA_Channel4 */

#ifdef _DMA_Channel5
  EXT DMA_Channel_TypeDef     *DMA_Channel5;
#endif /*_DMA_Channel5 */

#ifdef _DMA_Channel6
  EXT DMA_Channel_TypeDef     *DMA_Channel6;
#endif /*_DMA_Channel6 */

#ifdef _DMA_Channel7
  EXT DMA_Channel_TypeDef     *DMA_Channel7;
#endif /*_DMA_Channel7 */

#ifdef _FLASH
  EXT FLASH_TypeDef            *FLASH;
  EXT OB_TypeDef               *OB;  
#endif /*_FLASH */

#ifdef _RCC
  EXT RCC_TypeDef             *RCC;
#endif /*_RCC */

#ifdef _SysTick
  EXT SysTick_TypeDef         *SysTick;
#endif /*_SysTick */

#ifdef _NVIC
  EXT NVIC_TypeDef            *NVIC;
#endif /*_NVIC */

#ifdef _SCB
  EXT SCB_TypeDef             *SCB;
#endif /*_SCB */

#endif  /* DEBUG */

/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

#endif /* __STM32F10x_MAP_H */

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
