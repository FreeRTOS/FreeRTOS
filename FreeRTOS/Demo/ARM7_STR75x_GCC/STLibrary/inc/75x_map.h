/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_map.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the peripheral register's definitions
*                      and memory mapping.
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
#ifndef __75x_MAP_H
#define __75x_MAP_H

#ifndef EXT
  #define EXT extern
#endif /* EXT */

/* Includes ------------------------------------------------------------------*/
#include "75x_conf.h"
#include "75x_type.h"

/* Exported types ------------------------------------------------------------*/
/******************************************************************************/
/*                          IP registers structures               	      */
/******************************************************************************/

/*------------------------ Analog to Digital Converter -----------------------*/
typedef struct
{
  vu16 CLR0;
  u16  EMPTY1;
  vu16 CLR1;
  u16  EMPTY2;
  vu16 CLR2;
  u16  EMPTY3;
  vu16 CLR3;
  u16  EMPTY4;
  vu16 CLR4;
  u16  EMPTY5;
  vu16 TRA0;
  u16  EMPTY6;
  vu16 TRA1;
  u16  EMPTY7;
  vu16 TRA2;
  u16  EMPTY8;
  vu16 TRA3;
  u16  EMPTY9;
  vu16 TRB0;
  u16  EMPTY10;
  vu16 TRB1;
  u16  EMPTY11;
  vu16 TRB2;
  u16  EMPTY12;
  vu16 TRB3;
  u16  EMPTY13;
  vu16 DMAR;
  u16  EMPTY14[7];
  vu16 DMAE;
  u16  EMPTY15 ;
  vu16 PBR;
  u16  EMPTY16;
  vu16 IMR;
  u16  EMPTY17;
  vu16 D0;
  u16  EMPTY18;
  vu16 D1;
  u16  EMPTY19;
  vu16 D2;
  u16  EMPTY20;
  vu16 D3;
  u16  EMPTY21;
  vu16 D4;
  u16  EMPTY22;
  vu16 D5;
  u16  EMPTY23;
  vu16 D6;
  u16  EMPTY24;
  vu16 D7;
  u16  EMPTY25;
  vu16 D8;
  u16  EMPTY26;
  vu16 D9;
  u16  EMPTY27;
  vu16 D10;
  u16  EMPTY28;
  vu16 D11;
  u16  EMPTY29;
  vu16 D12;
  u16  EMPTY30;
  vu16 D13;
  u16  EMPTY31;
  vu16 D14;
  u16  EMPTY32;
  vu16 D15;
  u16  EMPTY33;
} ADC_TypeDef;

/*------------------------ Controller Area Network ---------------------------*/
typedef struct
{
  vu16 CRR;			
  u16  EMPTY1;
  vu16 CMR;			
  u16  EMPTY2;
  vu16 M1R;			
  u16  EMPTY3;
  vu16 M2R;			
  u16  EMPTY4;
  vu16 A1R;			
  u16  EMPTY5;
  vu16 A2R;			
  u16  EMPTY6;
  vu16 MCR;			
  u16  EMPTY7;
  vu16 DA1R;		
  u16  EMPTY8;
  vu16 DA2R;		
  u16  EMPTY9;
  vu16 DB1R;		
  u16  EMPTY10;
  vu16 DB2R;		
  u16  EMPTY11[27];
} CAN_MsgObj_TypeDef;

typedef struct
{
  vu16 CR;			
  u16  EMPTY1;
  vu16 SR;			
  u16  EMPTY2;
  vu16 ERR;			
  u16  EMPTY3;
  vu16 BTR;			
  u16  EMPTY4;
  vu16 IDR;			
  u16  EMPTY5;
  vu16 TESTR;		
  u16  EMPTY6;
  vu16 BRPR;		
  u16  EMPTY7[3];
  CAN_MsgObj_TypeDef sMsgObj[2];
  u16  EMPTY8[16];
  vu16 TXR1R;		
  u16  EMPTY9;
  vu16 TXR2R;		
  u16  EMPTY10[13];
  vu16 ND1R;		
  u16  EMPTY11;
  vu16 ND2R;		
  u16  EMPTY12[13];
  vu16 IP1R;		
  u16  EMPTY13;
  vu16 IP2R;		
  u16  EMPTY14[13];
  vu16 MV1R;		
  u16  EMPTY15;
  vu16 MV2R;		
  u16  EMPTY16;
} CAN_TypeDef;

/*--------------------------- Configuration Register -------------------------*/
typedef struct
{
  vu32 GLCONF;
} CFG_TypeDef;

/*-------------------------------- DMA Controller ----------------------------*/
typedef struct
{
  vu16  SOURCEL;
  u16   EMPTY1;
  vu16  SOURCEH;
  u16   EMPTY2;
  vu16  DESTL;
  u16   EMPTY3;
  vu16  DESTH;
  u16   EMPTY4;
  vu16  MAX;
  u16   EMPTY5;
  vu16  CTRL;
  u16   EMPTY6;
  vuc16 SOCURRH;
  u16   EMPTY7;
  vuc16 SOCURRL;
  u16   EMPTY8;
  vuc16 DECURRH;
  u16   EMPTY9;
  vuc16 DECURRL;
  u16   EMPTY10;
  vuc16 TCNT;
  u16   EMPTY11;
  vu16  LUBUFF;
  u16   EMPTY12;
} DMA_Stream_TypeDef;

typedef struct
{
  vu16 MASK;
  u16  EMPTY4;
  vu16 CLR;
  u16  EMPTY5;
  vuc16 STATUS;
  u16  EMPTY6;
  vu16 LAST;       
  u16  EMPTY7;
} DMA_TypeDef;

/*----------------------- Enhanced Interrupt Controller ----------------------*/
typedef struct
{
  vu32 ICR; 
  vuc32 CICR;   
  vu32 CIPR;
  u32  EMPTY1;
  vu32 FIER;
  vu32 FIPR;
  vu32 IVR;
  vu32 FIR;
  vu32 IER;
  u32  EMPTY2[7];
  vu32 IPR;
  u32  EMPTY3[7];
  vu32 SIRn[32];
} EIC_TypeDef;

/*------------------------- External Interrupt Controller --------------------*/
typedef struct
{
  vu32 MR;
  vu32 TSR;
  vu32 SWIR;
  vu32 PR;
} EXTIT_TypeDef;

/*-------------------------- General Purpose IO ports ------------------------*/
typedef struct
{
  vu32 PC0;
  vu32 PC1;
  vu32 PC2;
  vu32 PD;
  vu32 PM;
} GPIO_TypeDef;

typedef struct
{
  vu32 REMAP0R;
  vu32 REMAP1R;
} GPIOREMAP_TypeDef;

/*--------------------------------- I2C interface ----------------------------*/
typedef struct
{
  vu8 CR; 
  u8  EMPTY1[3];
  vu8 SR1;
  u8  EMPTY2[3];
  vu8 SR2;
  u8  EMPTY3[3];
  vu8 CCR;
  u8  EMPTY4[3];
  vu8 OAR1;
  u8  EMPTY5[3];
  vu8 OAR2;
  u8  EMPTY6[3];
  vu8 DR;
  u8  EMPTY7[3];
  vu8 ECCR;
  u8  EMPTY8[3];
} I2C_TypeDef;

/*---------------------------- Power, Reset and Clocks -----------------------*/
typedef  struct
{
  vu32 CLKCTL;
  vu32 RFSR;
  vu32 PWRCTRL;
  u32  EMPTY1;
  vu32 PCLKEN;
  vu32 PSWRES;
  u32  EMPTY2[2];
  vu32 BKP0;
  vu32 BKP1;
} MRCC_TypeDef;

/*-------------------------------- Real Time Clock ---------------------------*/
typedef struct
{
  vu16 CRH;
  u16  EMPTY;
  vu16 CRL;
  u16  EMPTY1;
  vu16 PRLH;
  u16  EMPTY2;
  vu16 PRLL;
  u16  EMPTY3;
  vu16 DIVH;
  u16  EMPTY4;
  vu16 DIVL;
  u16  EMPTY5;
  vu16 CNTH;
  u16  EMPTY6;
  vu16 CNTL;
  u16  EMPTY7;
  vu16 ALRH;
  u16  EMPTY8;
  vu16 ALRL;
  u16  EMPTY9;
} RTC_TypeDef;

/*---------------------------- Serial Memory Interface -----------------------*/
typedef struct
{
  vu32 CR1;
  vu32 CR2;
  vu32 SR;
  vu32 TR;
  vuc32 RR;
} SMI_TypeDef;

/*--------------------------------- Timer Base -------------------------------*/
typedef struct
{
  vu16 CR;
  u16  EMPTY1;
  vu16 SCR;
  u16  EMPTY2;
  vu16 IMCR;
  u16  EMPTY3[7];
  vu16 RSR;
  u16  EMPTY4;
  vu16 RER;
  u16  EMPTY5;
  vu16 ISR;
  u16  EMPTY6;
  vu16 CNT;
  u16  EMPTY7;
  vu16 PSC;
  u16  EMPTY8[3];
  vu16 ARR;
  u16  EMPTY9[13];
  vu16 ICR1;
  u16  EMPTY10;
} TB_TypeDef;

/*------------------------------------ TIM -----------------------------------*/
typedef struct
{
  vu16 CR;
  u16  EMPTY1;
  vu16 SCR;
  u16  EMPTY2;
  vu16 IMCR;
  u16  EMPTY3;
  vu16 OMR1;
  u16  EMPTY4[5];
  vu16 RSR;
  u16  EMPTY5;
  vu16 RER;
  u16  EMPTY6;
  vu16 ISR;
  u16  EMPTY7;
  vu16 CNT;
  u16  EMPTY8;
  vu16 PSC;
  u16  EMPTY9[3];
  vu16 ARR;
  u16  EMPTY10;
  vu16 OCR1;
  u16  EMPTY11;
  vu16 OCR2;
  u16  EMPTY12[9];
  vu16 ICR1;
  u16  EMPTY13;
  vu16 ICR2;
  u16  EMPTY14[9];
  vu16 DMAB;
  u16  EMPTY15;
} TIM_TypeDef;

/*------------------------------------ PWM -----------------------------------*/
typedef struct
{
  vu16 CR;
  u16  EMPTY1;
  vu16 SCR;
  u16  EMPTY2[3];
  vu16 OMR1;
  u16  EMPTY3;
  vu16 OMR2;
  u16  EMPTY4[3];
  vu16 RSR;
  u16  EMPTY5;
  vu16 RER;
  u16  EMPTY6;
  vu16 ISR;
  u16  EMPTY7;
  vu16 CNT;
  u16  EMPTY8;
  vu16 PSC;
  u16  EMPTY9;
  vu16 RCR;
  u16  EMPTY10;
  vu16 ARR;
  u16  EMPTY11;
  vu16 OCR1;
  u16  EMPTY12;
  vu16 OCR2;
  u16  EMPTY13;
  vu16 OCR3;
  u16  EMPTY14[15];
  vu16 DTR;
  u16  EMPTY15;
  vu16 DMAB;
  u16  EMPTY16;
} PWM_TypeDef;

/*----------------------- Synchronous Serial Peripheral ----------------------*/
typedef struct
{
  vu32 CR0;
  vu32 CR1;
  vu32 DR;
  vu32 SR;
  vu32 PR;
  vu32 IMSCR;
  vu32 RISR;
  vu32 MISR;
  vu32 ICR;
  vu32 DMACR;
} SSP_TypeDef;

/*---------------- Universal Asynchronous Receiver Transmitter ---------------*/
typedef struct
{
  vu16 DR;
  u16  EMPTY;
  vu16 RSR;
  u16  EMPTY1[9];
  vu16 FR;
  u16  EMPTY2;
  vu16 BKR;
  u16  EMPTY3[3];
  vu16 IBRD;
  u16  EMPTY4;
  vu16 FBRD;
  u16  EMPTY5;
  vu16 LCR;
  u16  EMPTY6;
  vu16 CR;
  u16  EMPTY7;
  vu16 IFLS;
  u16  EMPTY8;
  vu16 IMSC;
  u16  EMPTY9;
  vu16 RIS;
  u16  EMPTY10;
  vu16 MIS;
  u16  EMPTY11;
  vu16 ICR;
  u16  EMPTY12;
  vu16 DMACR;
  u16  EMPTY13;
} UART_TypeDef;

/*---------------------------------- WATCHDOG --------------------------------*/
typedef struct
{
  vu16 CR;
  u16  EMPTY1;
  vu16 PR;
  u16 EMPTY2;
  vu16 VR;
  u16  EMPTY3;
  vu16 CNT;
  u16  EMPTY4;
  vu16 SR;
  u16  EMPTY5;
  vu16 MR;
  u16  EMPTY6;
  vu16 KR;
  u16  EMPTY7;
} WDG_TypeDef;

/*******************************************************************************
*                      Peripherals' Base addresses
*******************************************************************************/

#define SRAM_BASE      0x40000000

#define CONFIG_BASE    0x60000000

#define SMIR_BASE      0x90000000

#define PERIPH_BASE    0xFFFF0000

#define CFG_BASE            (CONFIG_BASE + 0x0010)
#define MRCC_BASE           (CONFIG_BASE + 0x0020)
#define ADC_BASE            (PERIPH_BASE + 0x8400)
#define TB_BASE             (PERIPH_BASE + 0x8800)
#define TIM0_BASE           (PERIPH_BASE + 0x8C00)
#define TIM1_BASE           (PERIPH_BASE + 0x9000)
#define TIM2_BASE           (PERIPH_BASE + 0x9400)
#define PWM_BASE            (PERIPH_BASE + 0x9800)
#define WDG_BASE            (PERIPH_BASE + 0xB000)
#define SSP0_BASE           (PERIPH_BASE + 0xB800)
#define SSP1_BASE           (PERIPH_BASE + 0xBC00)
#define CAN_BASE            (PERIPH_BASE + 0xC400)
#define I2C_BASE            (PERIPH_BASE + 0xCC00)
#define UART0_BASE          (PERIPH_BASE + 0xD400)
#define UART1_BASE          (PERIPH_BASE + 0xD800)
#define UART2_BASE          (PERIPH_BASE + 0xDC00)
#define GPIO0_BASE          (PERIPH_BASE + 0xE400)
#define GPIOREMAP_BASE      (PERIPH_BASE + 0xE420)
#define GPIO1_BASE          (PERIPH_BASE + 0xE440)
#define GPIO2_BASE          (PERIPH_BASE + 0xE480)
#define DMA_BASE            (PERIPH_BASE + 0xECF0)
#define DMA_Stream0_BASE    (PERIPH_BASE + 0xEC00)
#define DMA_Stream1_BASE    (PERIPH_BASE + 0xEC40)
#define DMA_Stream2_BASE    (PERIPH_BASE + 0xEC80)
#define DMA_Stream3_BASE    (PERIPH_BASE + 0xECC0)
#define RTC_BASE            (PERIPH_BASE + 0xF000)
#define EXTIT_BASE          (PERIPH_BASE + 0xF400)
#define EIC_BASE            (PERIPH_BASE + 0xF800)

/*******************************************************************************
                            IPs' declaration
*******************************************************************************/

/*------------------- Non Debug Mode -----------------------------------------*/

#ifndef DEBUG
  #define SMI            ((SMI_TypeDef *)           SMIR_BASE)
  #define CFG            ((CFG_TypeDef *)           CFG_BASE)
  #define MRCC           ((MRCC_TypeDef *)          MRCC_BASE)
  #define ADC            ((ADC_TypeDef *)           ADC_BASE)
  #define TB             ((TB_TypeDef *)            TB_BASE)
  #define TIM0           ((TIM_TypeDef *)           TIM0_BASE)
  #define TIM1           ((TIM_TypeDef *)           TIM1_BASE)
  #define TIM2           ((TIM_TypeDef *)           TIM2_BASE)
  #define PWM            ((PWM_TypeDef *)           PWM_BASE)
  #define WDG            ((WDG_TypeDef *)           WDG_BASE)
  #define SSP0           ((SSP_TypeDef *)           SSP0_BASE)
  #define SSP1           ((SSP_TypeDef *)           SSP1_BASE)
  #define CAN            ((CAN_TypeDef *)           CAN_BASE)
  #define I2C            ((I2C_TypeDef *)           I2C_BASE)
  #define UART0          ((UART_TypeDef *)          UART0_BASE)
  #define UART1          ((UART_TypeDef *)          UART1_BASE)
  #define UART2          ((UART_TypeDef *)          UART2_BASE)
  #define GPIO0          ((GPIO_TypeDef *)          GPIO0_BASE)
  #define GPIOREMAP      ((GPIOREMAP_TypeDef *)     GPIOREMAP_BASE)
  #define GPIO1          ((GPIO_TypeDef *)          GPIO1_BASE)
  #define GPIO2          ((GPIO_TypeDef *)          GPIO2_BASE)
  #define DMA            ((DMA_TypeDef *)           DMA_BASE)
  #define DMA_Stream0    ((DMA_Stream_TypeDef *)    DMA_Stream0_BASE)
  #define DMA_Stream1    ((DMA_Stream_TypeDef *)    DMA_Stream1_BASE)
  #define DMA_Stream2    ((DMA_Stream_TypeDef *)    DMA_Stream2_BASE)
  #define DMA_Stream3    ((DMA_Stream_TypeDef *)    DMA_Stream3_BASE)
  #define RTC            ((RTC_TypeDef *)           RTC_BASE)
  #define EXTIT          ((EXTIT_TypeDef *)         EXTIT_BASE)
  #define EIC            ((EIC_TypeDef *)           EIC_BASE)
#else   /* DEBUG */
  #ifdef _SMI
    EXT SMI_TypeDef           *SMI;
  #endif /*_SMI */

  #ifdef _CFG
    EXT CFG_TypeDef           *CFG;
  #endif /*_CFG */

  #ifdef _MRCC
    EXT MRCC_TypeDef          *MRCC;
  #endif /*_MRCC */

  #ifdef _ADC
    EXT ADC_TypeDef           *ADC;
  #endif /*_ADC */  

  #ifdef _TB
    EXT TB_TypeDef            *TB;
  #endif /*_TB */

  #ifdef _TIM0
    EXT TIM_TypeDef           *TIM0;
  #endif /*_TIM0 */

  #ifdef _TIM1
    EXT TIM_TypeDef           *TIM1;
  #endif /*_TIM1 */

  #ifdef _TIM2
    EXT TIM_TypeDef           *TIM2;
  #endif /*_TIM2 */

  #ifdef _PWM
    EXT PWM_TypeDef           *PWM;
  #endif /*_PWM */

  #ifdef _WDG
    EXT WDG_TypeDef           *WDG;
  #endif /*_WDG */

  #ifdef _SSP0
    EXT SSP_TypeDef           *SSP0;
  #endif /*_SSP0 */

  #ifdef _SSP1
    EXT SSP_TypeDef           *SSP1;
  #endif /*_SSP1 */

  #ifdef _CAN
    EXT CAN_TypeDef           *CAN;
  #endif /*_CAN */

  #ifdef _I2C
    EXT I2C_TypeDef           *I2C;
  #endif /*_I2C */

  #ifdef _UART0
    EXT UART_TypeDef          *UART0;
  #endif /*_UART0 */

  #ifdef _UART1
    EXT UART_TypeDef          *UART1;
  #endif /*_UART1 */

  #ifdef _UART2
    EXT UART_TypeDef          *UART2;
  #endif /*_UART2 */

  #ifdef _GPIO0
    EXT GPIO_TypeDef          *GPIO0;
  #endif /*_GPIO0 */

  #ifdef _GPIOREMAP
    EXT GPIOREMAP_TypeDef     *GPIOREMAP;
  #endif /*_GPIOREMAP */

  #ifdef _GPIO1
    EXT GPIO_TypeDef          *GPIO1;
  #endif /*_GPIO1 */

  #ifdef _GPIO2
    EXT GPIO_TypeDef          *GPIO2;
  #endif /*_GPIO2 */

  #ifdef _DMA
    EXT DMA_TypeDef           *DMA;
  #endif /*_DMA */

  #ifdef _DMA_Stream0
    EXT DMA_Stream_TypeDef    *DMA_Stream0;
  #endif /*_DMA_Stream0 */

  #ifdef _DMA_Stream1
    EXT DMA_Stream_TypeDef    *DMA_Stream1;
  #endif /*_DMA_Stream1 */

  #ifdef _DMA_Stream2
    EXT DMA_Stream_TypeDef    *DMA_Stream2;
  #endif /*_DMA_Stream2 */

  #ifdef _DMA_Stream3
    EXT DMA_Stream_TypeDef    *DMA_Stream3;
  #endif /*_DMA_Stream3 */

  #ifdef _RTC
    EXT RTC_TypeDef           *RTC;
  #endif /*_RTC */

  #ifdef _EXTIT
    EXT EXTIT_TypeDef         *EXTIT;
  #endif /*_EXTIT */

  #ifdef _EIC
    EXT EIC_TypeDef           *EIC;
  #endif /*_EIC */
  
#endif  /* DEBUG */

/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

#endif /* __75x_MAP_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
