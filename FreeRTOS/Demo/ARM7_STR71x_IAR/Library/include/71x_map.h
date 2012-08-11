/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : 71x_map.h
* Author             : MCD Application Team
* Date First Issued  : 05/16/2003
* Description        : Peripherals memory mapping and registers structures
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

#ifndef __71x_map_H
#define __71x_map_H

#ifndef EXT
  #define EXT extern
#endif

#include "71x_conf.h"
#include "71x_type.h"


/* IP registers structures */

typedef volatile struct
{
  vu16 DATA0;
  vu16 EMPTY1[3];
  vu16 DATA1;
  vu16 EMPTY2[3];
  vu16 DATA2;
  vu16 EMPTY3[3];
  vu16 DATA3;
  vu16 EMPTY4[3];
  vu16 CSR;
  vu16 EMPTY5[7];
  vu16 CPR;
} ADC12_TypeDef;

typedef volatile struct
{
  vu32 CKDIS;
  vu32 SWRES;
} APB_TypeDef;

typedef volatile struct
{
  vu16 RXR;
  vu16 EMPTY1;
  vu16 TXR;
  vu16 EMPTY2;
  vu16 CSR1;
  vu16 EMPTY3;
  vu16 CSR2;
  vu16 EMPTY4;
  vu16 CLK;
} BSPI_TypeDef;

typedef volatile struct
{
  vu16 CRR;
  vu16 EMPTY1;
  vu16 CMR;
  vu16 EMPTY2;
  vu16 M1R;
  vu16 EMPTY3;
  vu16 M2R;
  vu16 EMPTY4;
  vu16 A1R;
  vu16 EMPTY5;
  vu16 A2R;
  vu16 EMPTY6;
  vu16 MCR;
  vu16 EMPTY7;
  vu16 DA1R;
  vu16 EMPTY8;
  vu16 DA2R;
  vu16 EMPTY9;
  vu16 DB1R;
  vu16 EMPTY10;
  vu16 DB2R;
  vu16 EMPTY11[27];
} CAN_MsgObj_TypeDef;

typedef volatile struct
{
  vu16 CR;
  vu16 EMPTY1;
  vu16 SR;
  vu16 EMPTY2;
  vu16 ERR;
  vu16 EMPTY3;
  vu16 BTR;
  vu16 EMPTY4;
  vu16 IDR;
  vu16 EMPTY5;
  vu16 TESTR;
  vu16 EMPTY6;
  vu16 BRPR;
  vu16 EMPTY7[3];
  CAN_MsgObj_TypeDef sMsgObj[2];
  vu16 EMPTY8[16];
  vu16 TR1R;
  vu16 EMPTY9;
  vu16 TR2R;
  vu16 EMPTY10[13];
  vu16 ND1R;
  vu16 EMPTY11;
  vu16 ND2R;
  vu16 EMPTY12[13];
  vu16 IP1R;
  vu16 EMPTY13;
  vu16 IP2R;
  vu16 EMPTY14[13];
  vu16 MV1R;
  vu16 EMPTY15;
  vu16 MV2R;
  vu16 EMPTY16;
} CAN_TypeDef;

typedef volatile struct
{
  vu32 ICR;
  vu32 CICR;
  vu32 CIPR;
  vu32 EMPTY1[3];
  vu32 IVR;
  vu32 FIR;
  vu32 IER;
  vu32 EMPTY2[7];
  vu32 IPR;
  vu32 EMPTY3[7];
  vu32 SIR[32];
} EIC_TypeDef;

typedef volatile struct
{
  vu16 BCON0;
  vu16 EMPTY1;
  vu16 BCON1;
  vu16 EMPTY2;
  vu16 BCON2;
  vu16 EMPTY3;
  vu16 BCON3;
  vu16 EMPTY4;
} EMI_TypeDef;

typedef volatile struct
{
  vu32 CR0;
  vu32 CR1;
  vu32 DR0;
  vu32 DR1;
  vu32 AR;
  vu32 ER;
} FLASHR_TypeDef;

typedef volatile struct
{
  vu32 NVWPAR;
  vu32 EMPTY;
  vu32 NVAPR0;
  vu32 NVAPR1;
} FLASHPR_TypeDef;

typedef volatile struct
{
  vu16 PC0;
  vu16 EMPTY1;
  vu16 PC1;
  vu16 EMPTY2;
  vu16 PC2;
  vu16 EMPTY3;
  vu16 PD;
  vu16 EMPTY4;
} GPIO_TypeDef;

typedef volatile struct
{
  vu8  CR;
  vu8  EMPTY1[3];
  vu8  SR1;
  vu8  EMPTY2[3];
  vu8  SR2;
  vu8  EMPTY3[3];
  vu8  CCR;
  vu8  EMPTY4[3];
  vu8  OAR1;
  vu8  EMPTY5[3];
  vu8  OAR2;
  vu8  EMPTY6[3];
  vu8  DR;
  vu8  EMPTY7[3];
  vu8  ECCR;
} I2C_TypeDef;

typedef volatile struct
{
  vu32 CCR;
  vu32 EMPTY1;
  vu32 CFR;
  vu32 EMPTY2[3];
  vu32 PLL1CR;
  vu32 PER;
  vu32 SMR;
} RCCU_TypeDef;

typedef volatile struct
{
  vu16 MDIVR;
  vu16 EMPTY1;
  vu16 PDIVR;
  vu16 EMPTY2;
  vu16 RSTR;
  vu16 EMPTY3;
  vu16 PLL2CR;
  vu16 EMPTY4;
  vu16 BOOTCR;
  vu16 EMPTY5;
  vu16 PWRCR;
} PCU_TypeDef;

typedef volatile struct
{
  vu16 CRH;
  vu16 EMPTY1;
  vu16 CRL;
  vu16 EMPTY2;
  vu16 PRLH;
  vu16 EMPTY3;
  vu16 PRLL;
  vu16 EMPTY4;
  vu16 DIVH;
  vu16 EMPTY5;
  vu16 DIVL;
  vu16 EMPTY6;
  vu16 CNTH;
  vu16 EMPTY7;
  vu16 CNTL;
  vu16 EMPTY8;
  vu16 ALRH;
  vu16 EMPTY9;
  vu16 ALRL;
} RTC_TypeDef;

typedef volatile struct
{
  vu16 ICAR;
  vu16 EMPTY1;
  vu16 ICBR;
  vu16 EMPTY2;
  vu16 OCAR;
  vu16 EMPTY3;
  vu16 OCBR;
  vu16 EMPTY4;
  vu16 CNTR;
  vu16 EMPTY5;
  vu16 CR1;
  vu16 EMPTY6;
  vu16 CR2;
  vu16 EMPTY7;
  vu16 SR;
} TIM_TypeDef;

typedef volatile struct
{
  vu16 BR;
  vu16 EMPTY1;
  vu16 TxBUFR;
  vu16 EMPTY2;
  vu16 RxBUFR;
  vu16 EMPTY3;
  vu16 CR;
  vu16 EMPTY4;
  vu16 IER;
  vu16 EMPTY5;
  vu16 SR;
  vu16 EMPTY6;
  vu16 GTR;
  vu16 EMPTY7;
  vu16 TOR;
  vu16 EMPTY8;
  vu16 TxRSTR;
  vu16 EMPTY9;
  vu16 RxRSTR;
} UART_TypeDef;

typedef volatile struct
{
  vu32 EP0R;
  vu32 EP1R;
  vu32 EP2R;
  vu32 EP3R;
  vu32 EP4R;
  vu32 EP5R;
  vu32 EP6R;
  vu32 EP7R;
  vu32 EP8R;
  vu32 EP9R;
  vu32 EP10R;
  vu32 EP11R;
  vu32 EP12R;
  vu32 EP13R;
  vu32 EP14R;
  vu32 EP15R;
  vu32 CNTR;
  vu32 ISTR;
  vu32 FNR;
  vu32 DADDR;
  vu32 BTABLE;
} USB_TypeDef;

typedef volatile struct
{
  vu16 CR;
  vu16 EMPTY1;
  vu16 PR;
  vu16 EMPTY2;
  vu16 VR;
  vu16 EMPTY3;
  vu16 CNT;
  vu16 EMPTY4;
  vu16 SR;
  vu16 EMPTY5;
  vu16 MR;
  vu16 EMPTY6;
  vu16 KR;
} WDG_TypeDef;

typedef volatile struct
{
  vu8  SR;
  vu8  EMPTY1[7];
  vu8  CTRL;
  vu8  EMPTY2[3];
  vu8  MRH;
  vu8  EMPTY3[3];
  vu8  MRL;
  vu8  EMPTY4[3];
  vu8  TRH;
  vu8  EMPTY5[3];
  vu8  TRL;
  vu8  EMPTY6[3];
  vu8  PRH;
  vu8  EMPTY7[3];
  vu8  PRL;
} XTI_TypeDef;


/* IRQ vectors */
typedef volatile struct
{
  vu32 T0TIMI_IRQHandler;
  vu32 FLASH_IRQHandler;
  vu32 RCCU_IRQHandler;
  vu32 RTC_IRQHandler;
  vu32 WDG_IRQHandler;
  vu32 XTI_IRQHandler;
  vu32 USBHP_IRQHandler;
  vu32 I2C0ITERR_IRQHandler;
  vu32 I2C1ITERR_IRQHandler;
  vu32 UART0_IRQHandler;
  vu32 UART1_IRQHandler;
  vu32 UART2_IRQHandler;
  vu32 UART3_IRQHandler;
  vu32 BSPI0_IRQHandler;
  vu32 BSPI1_IRQHandler;
  vu32 I2C0_IRQHandler;
  vu32 I2C1_IRQHandler;
  vu32 CAN_IRQHandler;
  vu32 ADC12_IRQHandler;
  vu32 T1TIMI_IRQHandler;
  vu32 T2TIMI_IRQHandler;
  vu32 T3TIMI_IRQHandler;
  vu32 EMPTY1[3];
  vu32 HDLC_IRQHandler;
  vu32 USBLP_IRQHandler;
  vu32 EMPTY2[2];
  vu32 T0TOI_IRQHandler;
  vu32 T0OC1_IRQHandler;
  vu32 T0OC2_IRQHandler;
} IRQVectors_TypeDef;

/*===================================================================*/

/* Memory mapping */

#define RAM_BASE        0x20000000

#define FLASHR_BASE     0x40100000
#define FLASHPR_BASE    0x4010DFB0

#define EXTMEM_BASE     0x60000000
#define RCCU_BASE       0xA0000000
#define PCU_BASE        0xA0000040
#define APB1_BASE       0xC0000000
#define APB2_BASE       0xE0000000
#define EIC_BASE        0xFFFFF800

#define I2C0_BASE       (APB1_BASE + 0x1000)
#define I2C1_BASE       (APB1_BASE + 0x2000)
#define UART0_BASE      (APB1_BASE + 0x4000)
#define UART1_BASE      (APB1_BASE + 0x5000)
#define UART2_BASE      (APB1_BASE + 0x6000)
#define UART3_BASE      (APB1_BASE + 0x7000)
#define CAN_BASE        (APB1_BASE + 0x9000)
#define BSPI0_BASE      (APB1_BASE + 0xA000)
#define BSPI1_BASE      (APB1_BASE + 0xB000)
#define USB_BASE        (APB1_BASE + 0x8800)

#define XTI_BASE        (APB2_BASE + 0x101C)
#define GPIO0_BASE      (APB2_BASE + 0x3000)
#define GPIO1_BASE      (APB2_BASE + 0x4000)
#define GPIO2_BASE      (APB2_BASE + 0x5000)
#define ADC12_BASE      (APB2_BASE + 0x7000)
#define TIM0_BASE       (APB2_BASE + 0x9000)
#define TIM1_BASE       (APB2_BASE + 0xA000)
#define TIM2_BASE       (APB2_BASE + 0xB000)
#define TIM3_BASE       (APB2_BASE + 0xC000)
#define RTC_BASE        (APB2_BASE + 0xD000)
#define WDG_BASE        (APB2_BASE + 0xE000)

#define EMI_BASE        (EXTMEM_BASE + 0x0C000000)

/*===================================================================*/

/* IP data access */

#ifndef DEBUG
  #define ADC12 ((ADC12_TypeDef *)ADC12_BASE)

  #define APB1  ((APB_TypeDef *)APB1_BASE)
  #define APB2  ((APB_TypeDef *)APB2_BASE+0x10)

  #define BSPI0 ((BSPI_TypeDef *)BSPI0_BASE)
  #define BSPI1 ((BSPI_TypeDef *)BSPI1_BASE)

  #define CAN   ((CAN_TypeDef *)CAN_BASE)

  #define EIC   ((EIC_TypeDef *)EIC_BASE)

  #define EMI   ((EMI_TypeDef *)EMI_BASE)

  #define FLASHR  ((FLASHR_TypeDef *)FLASHR_BASE)
  #define FLASHPR ((FLASHPR_TypeDef *)FLASHPR_BASE)

  #define GPIO0 ((GPIO_TypeDef *)GPIO0_BASE)
  #define GPIO1 ((GPIO_TypeDef *)GPIO1_BASE)
  #define GPIO2 ((GPIO_TypeDef *)GPIO2_BASE)

  #define I2C0  ((I2C_TypeDef *)I2C0_BASE)
  #define I2C1  ((I2C_TypeDef *)I2C1_BASE)

  #define PCU   ((PCU_TypeDef *)PCU_BASE)

  #define RCCU  ((RCCU_TypeDef *)RCCU_BASE)

  #define RTC   ((RTC_TypeDef *)RTC_BASE)

  #define TIM0  ((TIM_TypeDef *)TIM0_BASE)
  #define TIM1  ((TIM_TypeDef *)TIM1_BASE)
  #define TIM2  ((TIM_TypeDef *)TIM2_BASE)
  #define TIM3  ((TIM_TypeDef *)TIM3_BASE)

  #define UART0 ((UART_TypeDef *)UART0_BASE)
  #define UART1 ((UART_TypeDef *)UART1_BASE)
  #define UART2 ((UART_TypeDef *)UART2_BASE)
  #define UART3 ((UART_TypeDef *)UART3_BASE)

  #define USB   ((USB_TypeDef *)USB_BASE)

  #define WDG   ((WDG_TypeDef *)WDG_BASE)

  #define XTI   ((XTI_TypeDef *)XTI_BASE)

  #define IRQVectors ((IRQVectors_TypeDef *)&T0TIMI_Addr)

#else   /* DEBUG */

  #ifdef _ADC12
  EXT ADC12_TypeDef *ADC12;
  #endif

  #ifdef _APB
  #ifdef _APB1
  EXT APB_TypeDef *APB1;
  #endif
  #ifdef _APB2
  EXT APB_TypeDef *APB2;
  #endif
  #endif

  #ifdef _BSPI
  #ifdef _BSPI0
  EXT BSPI_TypeDef *BSPI0;
  #endif
  #ifdef _BSPI1
  EXT BSPI_TypeDef *BSPI1;
  #endif
  #endif

  #ifdef _CAN
  EXT CAN_TypeDef *CAN;
  #endif

  #ifdef _EIC
  EXT EIC_TypeDef *EIC;
  #endif

  #ifdef _EMI
  EXT EMI_TypeDef *EMI;
  #endif

  #ifdef _FLASH
  EXT FLASHR_TypeDef *FLASHR;
  EXT FLASHPR_TypeDef *FLASHPR;
  #endif

  #ifdef _GPIO
  #ifdef _GPIO0
  EXT GPIO_TypeDef *GPIO0;
  #endif
  #ifdef _GPIO1
  EXT GPIO_TypeDef *GPIO1;
  #endif
  #ifdef _GPIO2
  EXT GPIO_TypeDef *GPIO2;
  #endif
  #endif

  #ifdef _I2C
  #ifdef _I2C0
  EXT I2C_TypeDef *I2C0;
  #endif
  #ifdef _I2C1
  EXT I2C_TypeDef *I2C1;
  #endif
  #endif

  #ifdef _PCU
  EXT PCU_TypeDef *PCU;
  #endif

  #ifdef _RCCU
  EXT RCCU_TypeDef *RCCU;
  #endif

  #ifdef _RTC
  EXT RTC_TypeDef *RTC;
  #endif

  #ifdef _TIM
  #ifdef _TIM0
  EXT TIM_TypeDef *TIM0;
  #endif
  #ifdef _TIM1
  EXT TIM_TypeDef *TIM1;
  #endif
  #ifdef _TIM2
  EXT TIM_TypeDef *TIM2;
  #endif
  #ifdef _TIM3
  EXT TIM_TypeDef *TIM3;
  #endif
  #endif

  #ifdef _UART
  #ifdef _UART0
  EXT UART_TypeDef *UART0;
  #endif
  #ifdef _UART1
  EXT UART_TypeDef *UART1;
  #endif
  #ifdef _UART2
  EXT UART_TypeDef *UART2;
  #endif
  #ifdef _UART3
  EXT UART_TypeDef *UART3;
  #endif
  #endif

  #ifdef _USB
  EXT USB_TypeDef *USB;
  #endif

  #ifdef _WDG
  EXT WDG_TypeDef *WDG;
  #endif

  #ifdef _XTI
  EXT XTI_TypeDef *XTI;
  #endif

  #ifdef _IRQVectors
  EXT IRQVectors_TypeDef *IRQVectors;
  #endif

#endif  /* DEBUG */

#endif  /* __71x_map_H */

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
