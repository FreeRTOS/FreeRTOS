/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_map.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : Peripherals registers definition and memory mapping.
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

/* Define to prevent recursive inclusion ------------------------------------ */
#ifndef __91x_MAP_H
#define __91x_MAP_H

#ifndef EXT
  #define EXT extern
#endif /* EXT */

/* Includes ------------------------------------------------------------------*/
#include "91x_conf.h"
#include "91x_type.h"

/******************************************************************************/
/*                          IP registers structures                           */
/******************************************************************************/

/*------------------------------------ FMI -----------------------------------*/

typedef struct
{
  vu32 BBSR;        /* Boot Bank Size Register                */
  vu32 NBBSR;       /* Non-Boot Bank Size Register            */
  vu32 EMPTY1;
  vu32 BBADR;       /* Boot Bank Base Address Register        */
  vu32 NBBADR;      /* Non-Boot Bank Base Address Register    */
  vu32 EMPTY2;
  vu32 CR;          /* Control Register                       */
  vu32 SR;          /* Status Register                        */
  vu32 BCE5ADDR;    /* BC Fifth Entry Target Address Register */
} FMI_TypeDef;

/*----------------------  Analog to Digital Convertor ------------------------*/

typedef struct
{
  vu16 CR;         /* Control Register               */
  vu16 EMPTY1;
  vu16 CCR;        /* Channel Configuration Register */
  vu16 EMPTY2;
  vu16 HTR;        /* Higher Threshold Register      */
  vu16 EMPTY3;
  vu16 LTR;        /* Lower Threshold Register       */
  vu16 EMPTY4;
  vu16 CRR;        /* Compare Result Register        */
  vu16 EMPTY5;
  vu16 DR0;        /* Data Register for Channel 0    */
  vu16 EMPTY6;
  vu16 DR1;        /* Data Register for Channel 1    */
  vu16 EMPTY7;
  vu16 DR2;        /* Data Register for Channel 2    */
  vu16 EMPTY8;
  vu16 DR3;        /* Data Register for Channel 3    */
  vu16 EMPTY9;
  vu16 DR4;        /* Data Register for Channel 4    */
  vu16 EMPTY10;
  vu16 DR5;        /* Data Register for Channel 5    */
  vu16 EMPTY11;
  vu16 DR6;        /* Data Register for Channel 6    */
  vu16 EMPTY12;
  vu16 DR7;        /* Data Register for Channel 7    */
  vu16 EMPTY13;
  vu16 PRS;        /* Prescaler Value Register       */
  vu16 EMPTY14;
} ADC_TypeDef;

/*--------------------- AHB APB BRIDGE registers strcture --------------------*/

typedef struct
{
  vu32 BSR;        /* Bridge Status Register            */
  vu32 BCR;        /* Bridge Configuration Register     */
  vu32 PAER;       /* Peripheral Address Error register */
} AHBAPB_TypeDef;

/*--------------- Controller Area Network Interface Register -----------------*/

typedef struct
{
  vu16 CRR;			/* IFn Command request Register       */
  vu16 EMPTY1;
  vu16 CMR;			/* IFn Command Mask Register          */
  vu16 EMPTY2;
  vu16 M1R;			/* IFn Message Mask 1 Register        */
  vu16 EMPTY3;
  vu16 M2R;			/* IFn Message Mask 2 Register        */
  vu16 EMPTY4;
  vu16 A1R;			/* IFn Message Arbitration 1 Register */
  vu16 EMPTY5;
  vu16 A2R;			/* IFn Message Arbitration 2 Register */
  vu16 EMPTY6;
  vu16 MCR;			/* IFn Message Control Register       */
  vu16 EMPTY7;
  vu16 DA1R;		        /* IFn DATA A 1 Register              */
  vu16 EMPTY8;
  vu16 DA2R;		        /* IFn DATA A 2 Register              */
  vu16 EMPTY9;
  vu16 DB1R;		        /* IFn DATA B 1 Register              */
  vu16 EMPTY10;
  vu16 DB2R;		        /* IFn DATA B 2 Register              */
  vu16 EMPTY11[27];
} CAN_MsgObj_TypeDef;

typedef struct
{
  vu16 CR;		/* Control Register                */
  vu16 EMPTY1;
  vu16 SR;	        /* Status Register                 */
  vu16 EMPTY2;
  vu16 ERR;		/* Error counter Register          */
  vu16 EMPTY3;
  vu16 BTR;		/* Bit Timing Register             */
  vu16 EMPTY4;
  vu16 IDR;		/* Interrupt Identifier Register   */
  vu16 EMPTY5;
  vu16 TESTR;		/* Test Register                   */
  vu16 EMPTY6;
  vu16 BRPR;		/* BRP Extension Register          */
  vu16 EMPTY7[3];
  CAN_MsgObj_TypeDef sMsgObj[2];
  vu16 EMPTY8[16];
  vu16 TXR1R;		/* Transmission request 1 Register */
  vu16 EMPTY9;
  vu16 TXR2R;		/* Transmission Request 2 Register */
  vu16 EMPTY10[13];
  vu16 ND1R;		/* New Data 1 Register             */
  vu16 EMPTY11;
  vu16 ND2R;		/* New Data 2 Register             */
  vu16 EMPTY12[13];
  vu16 IP1R;		/* Interrupt Pending 1 Register    */
  vu16 EMPTY13;
  vu16 IP2R;		/* Interrupt Pending 2 Register    */
  vu16 EMPTY14[13];
  vu16 MV1R;		/* Message Valid 1 Register        */
  vu16 EMPTY15;
  vu16 MV2R;		/* Message VAlid 2 Register        */
  vu16 EMPTY16;
} CAN_TypeDef;

/*----------------------- System Control Unit---------------------------------*/

typedef struct
{
  vu32 CLKCNTR;    /* Clock Control Register                       */
  vu32 PLLCONF;    /* PLL Configuration Register                   */
  vu32 SYSSTATUS;  /* System Status Register                       */
  vu32 PWRMNG;     /* Power Management Register                    */
  vu32 ITCMSK;     /* Interrupt Mask Register                      */
  vu32 PCGRO;      /* Peripheral Clock Gating Register 0           */
  vu32 PCGR1;      /* Peripheral Clock Gating Register 1           */
  vu32 PRR0;       /* Peripheral Reset Register 0                  */
  vu32 PRR1;       /* Peripheral Reset Register 1                  */
  vu32 MGR0;       /* Idle Mode Mask Gating Register 0             */
  vu32 MGR1;       /* Idle Mode Mask Gating Register 1             */
  vu32 PECGR0;     /* Peripheral Emulation Clock Gating Register 0 */
  vu32 PECGR1;     /* Peripheral Emulation Clock Gating Register 1 */
  vu32 SCR0;       /* System Configuration Register 0              */
  vu32 SCR1;       /* System Configuration Register 1              */
  vu32 SCR2;       /* System Configuration Register 2              */
  u32 EMPTY1;
  vu32 GPIOOUT[8];   /* GPIO Output Registers                      */
  vu32 GPIOIN[8];    /* GPIO Input Registers                       */
  vu32 GPIOTYPE[10]; /* GPIO Type Registers                        */
  vu32 GPIOEMI;      /* GPIO EMI Selector Register                 */
  vu32 WKUPSEL;      /* Wake-Up Selection Register                 */
  u32 EMPTY2[2];
  vu32 GPIOANA;      /* GPIO Analag mode Register                  */
} SCU_TypeDef;

/*------------------------- DMA Channelx Registers ---------------------------*/

typedef struct
{
  vu32 SRC;      /* Channelx Source Address Register      */
  vu32 DES;      /* Channelx Destination Address Register */
  vu32 LLI;      /* Channelx Lincked List Item Register   */
  vu32 CC;       /* Channelx Contol Register              */
  vu32 CCNF;     /* Channelx Configuration Register       */
} DMA_Channel_TypeDef;

/* x can be ,0,1,2,3,4,5,6 or 7. There are eight Channels AHB BUS Master */

/*----------------------------- DMA Controller -------------------------------*/

typedef struct
{
  vu32 ISR;         /* Interrupt Status Register                    */
  vu32 TCISR;       /* Terminal Count Interrupt Status Register     */
  vu32 TCICR;       /* Terminal CountInterrupt Clear Register       */
  vu32 EISR;        /* Error Interrupt Status Register              */
  vu32 EICR;        /* Error Interrupt Clear Register               */
  vu32 TCRISR;      /* Terminal Count Raw Interrupt Status Register */
  vu32 ERISR;       /* Raw Error Interrupt Status Register          */
  vu32 ENCSR;       /* Enabled Channel Status Register              */
  vu32 SBRR;        /* Software Burst Request Register              */
  vu32 SSRR;        /* Software Single Request Register             */
  vu32 SLBRR;       /* Software Last Burst Request Register         */
  vu32 SLSRR;       /* Software Last Single Request Register        */
  vu32 CNFR;        /* Configuration Register                       */
  vu32 SYNR;        /* Syncronization Register                      */
} DMA_TypeDef;

/*--------------------------------- TIM Timer --------------------------------*/

typedef struct
{
  vu16 IC1R;        /* Input Capture 1 Register  */
  vu16 EMPTY1;
  vu16 IC2R;        /* Input Capture 2 Register  */
  vu16 EMPTY2;
  vu16 OC1R;        /* Output Compare 1 Register */
  vu16 EMPTY3;
  vu16 OC2R;        /* Output Compare 2 Register */
  vu16 EMPTY4;
  vu16 CNTR;        /* Counter Register          */
  vu16 EMPTY5;
  vu16 CR1;         /* Control Register 1        */
  vu16 EMPTY6;
  vu16 CR2;         /* Control Register 2        */
  vu16 EMPTY7;
  vu16 SR;          /* Status Register           */
  vu16 EMPTY8;
} TIM_TypeDef;

/*---------------------------- EMI Bankx Registers ---------------------------*/

typedef struct
{
  vu32 ICR;      /* Bankx   Idle Cycle Control Register                    */
  vu32 RCR;      /* Bankx   Read Wait State Control Register               */
  vu32 WCR;      /* Bankx   Write Wait State Control Register              */
  vu32 OECR;     /* Bankx   Output Enable Assertion Delay Control Register */
  vu32 WECR;     /* Bankx   Write Enable Assertion Delay Control Register  */
  vu32 BCR;      /* Bankx   Control Register                               */
 } EMI_Bank_TypeDef;

/*---------------------------- Ethernet Controller ---------------------------*/

/* MAC Registers */
typedef struct
{
  vu32 MCR;      /* ENET Control Register             */
  vu32 MAH;      /* ENET Address High Register        */
  vu32 MAL;      /* ENET Address Low Register         */
  vu32 MCHA;     /* Multicast Address High Register   */
  vu32 MCLA;     /* Multicast Address Low Register    */
  vu32 MIIA;     /* MII Address Register              */
  vu32 MIID;     /* MII Data Register                 */
  vu32 MCF;      /* ENET Control Frame Register       */
  vu32 VL1;      /* VLAN1 Register                    */
  vu32 VL2;      /* VLAN2 register                    */
  vu32 MTS;      /* ENET Transmission Status Register */
  vu32 MRS;      /* ENET Reception Status Register    */
} ENET_MAC_TypeDef;

/* DMA Registers */
typedef struct
{
  vu32 SCR;           /* DMA Status and Control Register         */
  vu32 IER;           /* DMA Interrupt Sources Enable Register   */
  vu32 ISR;           /* DMA Interrupt Status Register           */
  vu32 CCR;           /* Clock Control Relation : HCLK, PCLK and
                         ENET_CLK phase relations                */
  vu32 RXSTR;         /* Rx DMA start Register                   */
  vu32 RXCR;          /* Rx DMA Control Register                 */
  vu32 RXSAR;         /* Rx DMA Base Address Register            */
  vu32 RXNDAR;        /* Rx DMA Next Descriptor Address Register */
  vu32 RXCAR;         /* Rx DMA Current Address Register         */
  vu32 RXCTCR;        /* Rx DMA Current Transfer Count Register  */
  vu32 RXTOR;         /* Rx DMA FIFO Time Out Register           */
  vu32 RXSR;          /* Rx DMA FIFO Status Register             */
  vu32 TXSTR;         /* Tx DMA start Register                   */
  vu32 TXCR;          /* Tx DMA Control Register                 */
  vu32 TXSAR;         /* Tx DMA Base Address Register            */
  vu32 TXNDAR;        /* Tx DMA Next Descriptor Address Register */
  vu32 TXCAR;         /* Tx DMA Current Address Register         */
  vu32 TXTCR;         /* Tx DMA Current Transfer Count Register  */
  vu32 TXTOR;         /* Tx DMA FIFO Time Out Register           */
  vu32 TXSR;          /* Tx DMA FIFO Status Register             */
} ENET_DMA_TypeDef;

/*------------------------------------- GPIO ---------------------------------*/

typedef struct
{
  vu8 DR[1021];     /* Data Register                    */
  vu32 DDR;         /* Data Direction Register          */
} GPIO_TypeDef;

/*-------------------------------- I2C interface -----------------------------*/

typedef struct
{
  vu8  CR;                 /* Control Register                */
  vu8  EMPTY1[3];
  vu8  SR1;                /* Status Register 1               */
  vu8  EMPTY2[3];
  vu8  SR2;                /* Status Register 2               */
  vu8  EMPTY3[3];
  vu8  CCR;                /* Clock Control Register          */
  vu8  EMPTY4[3];
  vu8  OAR1;               /* Own Address Register 1          */
  vu8  EMPTY5[3];
  vu8  OAR2;               /* Own Address Register 2          */
  vu8  EMPTY6[3];
  vu8  DR;                 /* Data Register                   */
  vu8  EMPTY7[3];
  vu8  ECCR;               /* Extended Clock Control Register */
  vu8  EMPTY8[3];
} I2C_TypeDef;

/*------------------------------------- VIC ----------------------------------*/

typedef struct
{
  vu32 ISR;                /* IRQ Status Register               */
  vu32 FSR;                /* FIQ Status Register               */
  vu32 RINTSR;             /* Raw Interrupt Status Register     */
  vu32 INTSR;              /* Interrupt Select Register         */
  vu32 INTER;              /* Interrupt Enable Register         */
  vu32 INTECR;             /* Interrupt Enable Clear Register   */
  vu32 SWINTR;             /* Software Interrupt Register       */
  vu32 SWINTCR;            /* Software Interrupt clear Register */
  vu32 PER;                /* Protection Enable Register        */
  vu32 EMPTY1[3];
  vu32 VAR;                /* Vector Address Register           */
  vu32 DVAR;               /* Default Vector Address Register   */
  vu32 EMPTY2[50];
  vu32 VAiR[16];           /* Vector Address 0-15 Register      */
  vu32 EMPTY3[48];
  vu32 VCiR[16];           /* Vector Control 0-15 Register      */
} VIC_TypeDef;

/*-------------------------------- Motor Control -----------------------------*/

typedef struct
{
  vu16 TCPT;          /* Tacho Capture Register           */
  vu16 EMPTY1;
  vu16 TCMP;          /* Tacho Compare Register           */
  vu16 EMPTY2;
  vu16 IPR;           /* Input Pending Register           */
  vu16 EMPTY3;
  vu16 TPRS;          /* Tacho Prescaler Register         */
  vu16 EMPTY4;
  vu16 CPRS;          /* PWM Counter Prescaler Register   */
  vu16 EMPTY5;
  vu16 REP;           /* Repetition Counter Register      */
  vu16 EMPTY6;
  vu16 CMPW;          /* Compare Phase W Preload Register */
  vu16 EMPTY7;
  vu16 CMPV;          /* Compare Phase V Preload Register */
  vu16 EMPTY8;
  vu16 CMPU;          /* Compare Phase U Preload Register */
  vu16 EMPTY9;
  vu16 CMP0;          /* Compare 0 Preload Register       */
  vu16 EMPTY10;
  vu16 PCR0;          /* Peripheral Control Register 0    */
  vu16 EMPTY11;
  vu16 PCR1;          /* Peripheral Control Register 1    */
  vu16 EMPTY12;
  vu16 PCR2;          /* Peripheral Control Register 2    */
  vu16 EMPTY13;
  vu16 PSR;           /* Polarity Selection Register      */
  vu16 EMPTY14;
  vu16 OPR;           /* Output Peripheral Register       */
  vu16 EMPTY15;
  vu16 IMR;           /* Interrupt Mask Register          */
  vu16 EMPTY16;
  vu16 DTG;           /* Dead Time Generator Register     */
  vu16 EMPTY17;
  vu16 ESC;           /* Emergency Stop Clear Register    */
  vu16 EMPTY18;
}MC_TypeDef;

/*------------------------------------- RTC ----------------------------------*/

typedef struct
{
  vu32 TR;         /* Time Register       */
  vu32 DTR;        /* Date Register       */
  vu32 ATR;        /* Alarm time Register */
  vu32 CR;         /* Control Register    */
  vu32 SR;         /* Status Register     */
  vu32 MILR;       /* Millisec Register   */
}RTC_TypeDef;

/*------------------------------------- SSP ----------------------------------*/

typedef struct
{
  vu16 CR0;        /* Control Register 1                   */
  vu16 EMPTY1;
  vu16 CR1;        /* Control Register 2                   */
  vu16 EMPTY2;
  vu16 DR;         /* Data Register                        */
  vu16 EMPTY3;
  vu16 SR;         /* Status Register                      */
  vu16 EMPTY4;
  vu16 PR;         /* Clock Prescale Register              */
  vu16 EMPTY5;
  vu16 IMSCR;      /* Interrupt Mask Set or Clear Register */
  vu16 EMPTY6;
  vu16 RISR;       /* Raw Interrupt Status Register        */
  vu16 EMPTY7;
  vu16 MISR;       /* Masked Interrupt Status Register     */
  vu16 EMPTY8;
  vu16 ICR;        /* Interrupt Clear Register             */
  vu16 EMPTY9;
  vu16 DMACR;      /* DMA Control Register                 */
  vu16 EMPTY10;
}SSP_TypeDef;

/*------------------------------------ UART ----------------------------------*/

typedef struct
{
  vu16 DR;        /* Data Register                                               */
  vu16 EMPTY1;
  vu16 RSECR;     /* Receive Status Register (read)/Error Clear Register (write) */
  vu16 EMPTY2[9];
  vu16 FR;        /* Flag Register                                               */
  vu16 EMPTY3[3];
  vu16 ILPR;      /* IrDA Low-Power counter Register                             */
  vu16 EMPTY4;
  vu16 IBRD;      /* Integer Baud Rate Divisor Register                          */
  vu16 EMPTY5;
  vu16 FBRD;      /* Fractional Baud Rate Divisor Register                       */
  vu16 EMPTY6;
  vu16 LCR;       /* Line Control Register, High byte                            */
  vu16 EMPTY7;
  vu16 CR;        /* Control Register                                            */
  vu16 EMPTY8;
  vu16 IFLS;      /* Interrupt FIFO Level Select Register                        */
  vu16 EMPTY9;
  vu16 IMSC;      /* Interrupt Mask Set/Clear Register                           */
  vu16 EMPTY10;
  vu16 RIS;       /* Raw Interrupt Status Register                               */
  vu16 EMPTY11;
  vu16 MIS;       /* Masked Interrupt Status Register                            */
  vu16 EMPTY12;
  vu16 ICR;       /* Interrupt Clear Register                                    */
  vu16 EMPTY13;
  vu16 DMACR;     /* DMA Control Register                                        */
  vu16 EMPTY14;
}UART_TypeDef;

/*------------------------------- Wake-up System -----------------------------*/

typedef struct
{
  vu32  CTRL;   /* Control Register            */
  vu32  MR;     /* Mask Register               */
  vu32  TR;     /* Trigger Register            */
  vu32  PR;     /* Pending Register            */
  vu32  INTR;   /* Software Interrupt Register */
} WIU_TypeDef;

/*------------------------------- WatchDog Timer -----------------------------*/

typedef struct
{
  vu16 CR;        /* Control Register        */
  vu16 EMPTY1;
  vu16 PR;        /* Presclar Register       */
  vu16 EMPTY2;
  vu16 VR;        /* Pre-load Value Register */
  vu16 EMPTY3;
  vu16 CNT;       /* Counter Register        */
  vu16 EMPTY4;
  vu16 SR;        /* Status Register         */
  vu16 EMPTY5;
  vu16 MR;        /* Mask Register           */
  vu16 EMPTY6;
  vu16 KR;        /* Key Register            */
  vu16 EMPTY7;
} WDG_TypeDef;

/*******************************************************************************
*                         Memory Mapping of STR91x                             *
*******************************************************************************/

#define AHB_APB_BRDG0_U    (0x58000000) /* AHB/APB Bridge 0 UnBuffered Space */
#define AHB_APB_BRDG0_B    (0x48000000) /* AHB/APB Bridge 0 Buffered Space   */

#define AHB_APB_BRDG1_U    (0x5C000000) /* AHB/APB Bridge 1 UnBuffered Space */
#define AHB_APB_BRDG1_B    (0x4C000000) /* AHB/APB Bridge 1 Buffered Space   */

#define AHB_EMI_U          (0x74000000) /* EMI UnBuffered Space */
#define AHB_EMI_B          (0x64000000) /* EMI Buffered Space   */

#define AHB_DMA_U          (0x78000000) /* DMA UnBuffered Space */
#define AHB_DMA_B          (0x68000000) /* DMA Buffered Space   */

#define AHB_ENET_MAC_U     (0x7C000400) /* ENET_MAC  UnBuffered Space */
#define AHB_ENET_MAC_B     (0x6C000400) /* ENET_MAC  Buffered Space   */

#define AHB_ENET_DMA_U     (0x7C000000) /* ENET_DMA  Unbuffered Space */
#define AHB_ENET_DMA_B     (0x6C000000) /* ENET_DMA  Buffered Space    */

#define AHB_VIC1_U         (0xFC000000) /* Secondary VIC1 UnBuffered Space */
#define AHB_VIC0_U         (0xFFFFF000) /* Primary VIC0 UnBuffered Space   */

#define AHB_FMI_U          (0x54000000) /* FMI Unbuffered Space */
#define AHB_FMI_B          (0x44000000) /* FMI buffered Space   */

/*******************************************************************************
*                Addresses related to the VICs' peripherals                    *
*******************************************************************************/

#define VIC0_BASE          (AHB_VIC0_U)
#define VIC1_BASE          (AHB_VIC1_U)

/*******************************************************************************
*                    Addresses related to the EMI banks                        *
*******************************************************************************/

#define AHB_EMIB3_OFST      (0x00000040)   /* Offset of EMI bank3 */
#define AHB_EMIB2_OFST      (0x00000020)   /* Offset of EMI bank2 */
#define AHB_EMIB1_OFST      (0x00000000)   /* Offset of EMI bank1 */
#define AHB_EMIB0_OFST      (0x000000E0)   /* Offset of EMI bank0 */

/*******************************************************************************
*                 Addresses related to the DMA peripheral                      *
*******************************************************************************/

#define AHB_DMA_Channel0_OFST    (0x00000100)   /* Offset of Channel 0 */
#define AHB_DMA_Channel1_OFST    (0x00000120)   /* Offset of Channel 1 */
#define AHB_DMA_Channel2_OFST    (0x00000140)   /* Offset of Channel 2 */
#define AHB_DMA_Channel3_OFST    (0x00000160)   /* Offset of Channel 3 */
#define AHB_DMA_Channel4_OFST    (0x00000180)   /* Offset of Channel 4 */
#define AHB_DMA_Channel5_OFST    (0x000001A0)   /* Offset of Channel 5 */
#define AHB_DMA_Channel6_OFST    (0x000001C0)   /* Offset of Channel 6 */
#define AHB_DMA_Channel7_OFST    (0x000001E0)   /* Offset of Channel 7 */

/*******************************************************************************
*                 Addresses related to the APB0 sub-system                     *
*******************************************************************************/

#define APB_WIU_OFST       (0x00001000)   /* Offset of WIU   */
#define APB_TIM0_OFST      (0x00002000)   /* Offset of TIM0  */
#define APB_TIM1_OFST      (0x00003000)   /* Offset of TIM1  */
#define APB_TIM2_OFST      (0x00004000)   /* Offset of TIM2  */
#define APB_TIM3_OFST      (0x00005000)   /* Offset of TIM3  */
#define APB_GPIO0_OFST     (0x00006000)   /* Offset of GPIO0 */
#define APB_GPIO1_OFST     (0x00007000)   /* Offset of GPIO1 */
#define APB_GPIO2_OFST     (0x00008000)   /* Offset of GPIO2 */
#define APB_GPIO3_OFST     (0x00009000)   /* Offset of GPIO3 */
#define APB_GPIO4_OFST     (0x0000A000)   /* Offset of GPIO4 */
#define APB_GPIO5_OFST     (0x0000B000)   /* Offset of GPIO5 */
#define APB_GPIO6_OFST     (0x0000C000)   /* Offset of GPIO6 */
#define APB_GPIO7_OFST     (0x0000D000)   /* Offset of GPIO7 */
#define APB_GPIO8_OFST     (0x0000E000)   /* Offset of GPIO8 */
#define APB_GPIO9_OFST     (0x0000F000)   /* Offset of GPIO9 */

/*******************************************************************************
*                   Addresses related to the APB1 sub-system                   *
*******************************************************************************/

#define APB_RTC_OFST       (0x00001000) /* Offset of RTC               */
#define APB_SCU_OFST       (0x00002000) /* Offset of System Controller */
#define APB_MC_OFST        (0x00003000) /* Offset of Motor Control     */
#define APB_UART0_OFST     (0x00004000) /* Offset of UART0             */
#define APB_UART1_OFST     (0x00005000) /* Offset of UART1             */
#define APB_UART2_OFST     (0x00006000) /* Offset of UART2             */
#define APB_SSP0_OFST      (0x00007000) /* Offset of SSP0              */
#define APB_SSP1_OFST      (0x00008000) /* Offset of SSPI              */
#define APB_CAN_OFST       (0x00009000) /* Offset of CAN               */
#define APB_ADC_OFST       (0x0000A000) /* Offset of ADC               */
#define APB_WDG_OFST       (0x0000B000) /* Offset of WDG               */
#define APB_I2C0_OFST      (0x0000C000) /* Offset of I2C0              */
#define APB_I2C1_OFST      (0x0000D000) /* Offset of I2C1              */

/*----------------------------------------------------------------------------*/
/*----------------------------- Unbuffered Mode ------------------------------*/
/*----------------------------------------------------------------------------*/

#ifndef Buffered

/*******************************************************************************
*                  AHBAPB peripheral Unbuffered Base Address                   *
*******************************************************************************/

#define AHBAPB0_BASE           (AHB_APB_BRDG0_U)
#define AHBAPB1_BASE           (AHB_APB_BRDG1_U)

/*******************************************************************************
*                  ENET peripheral Unbuffered Base Address                     *
*******************************************************************************/

#define ENET_MAC_BASE          (AHB_ENET_MAC_U)
#define ENET_DMA_BASE          (AHB_ENET_DMA_U)

/*******************************************************************************
*                  DMA peripheral Unbuffered Base Address                      *
*******************************************************************************/

#define DMA_BASE           (AHB_DMA_U)

/*******************************************************************************
*                  EMI peripheral Unbuffered Base Address                      *
*******************************************************************************/

#define EMI_BASE           (AHB_EMI_U)

/*******************************************************************************
*                  FMI peripheral Unbuffered Base Address                      *
*******************************************************************************/

#define FMI_BASE           (AHB_FMI_U)


#else /* Buffered */

/*----------------------------------------------------------------------------*/
/*------------------------------ Buffered Mode -------------------------------*/
/*----------------------------------------------------------------------------*/

/*******************************************************************************
*                   AHBAPB peripheral Buffered Base Address                    *
*******************************************************************************/

#define AHBAPB0_BASE           (AHB_APB_BRDG0_B)
#define AHBAPB1_BASE           (AHB_APB_BRDG1_B)

/*******************************************************************************
*                  ENET peripheral Unbuffered Base Address                     *
*******************************************************************************/

#define ENET_MAC_BASE          (AHB_ENET_MAC_B)
#define ENET_DMA_BASE          (AHB_ENET_DMA_B)

/*******************************************************************************
*                    DMA peripheral Buffered Base Address                      *
*******************************************************************************/

#define DMA_BASE           (AHB_DMA_B)

/*******************************************************************************
*                      EMI peripheral Buffered Base Address                    *
*******************************************************************************/

#define EMI_BASE           (AHB_EMI_B)

/*******************************************************************************
*                      FMI peripheral Buffered Base Address                    *
*******************************************************************************/

#define FMI_BASE           (AHB_FMI_B)

#endif /* Buffered */

/*******************************************************************************
*                          DMA channels Base Address                           *
*******************************************************************************/
#define DMA_Channel0_BASE  (DMA_BASE + AHB_DMA_Channel0_OFST)
#define DMA_Channel1_BASE  (DMA_BASE + AHB_DMA_Channel1_OFST)
#define DMA_Channel2_BASE  (DMA_BASE + AHB_DMA_Channel2_OFST)
#define DMA_Channel3_BASE  (DMA_BASE + AHB_DMA_Channel3_OFST)
#define DMA_Channel4_BASE  (DMA_BASE + AHB_DMA_Channel4_OFST)
#define DMA_Channel5_BASE  (DMA_BASE + AHB_DMA_Channel5_OFST)
#define DMA_Channel6_BASE  (DMA_BASE + AHB_DMA_Channel6_OFST)
#define DMA_Channel7_BASE  (DMA_BASE + AHB_DMA_Channel7_OFST)

/*******************************************************************************
*                     EMI Banks peripheral Base Address                        *
*******************************************************************************/

#define EMI_Bank0_BASE  (EMI_BASE + AHB_EMIB0_OFST)
#define EMI_Bank1_BASE  (EMI_BASE + AHB_EMIB1_OFST)
#define EMI_Bank2_BASE  (EMI_BASE + AHB_EMIB2_OFST)
#define EMI_Bank3_BASE  (EMI_BASE + AHB_EMIB3_OFST)

/*******************************************************************************
*                     APB0 Peripherals' Base addresses                         *
*******************************************************************************/

#define WIU_BASE           (AHBAPB0_BASE + APB_WIU_OFST)
#define TIM0_BASE          (AHBAPB0_BASE + APB_TIM0_OFST)
#define TIM1_BASE          (AHBAPB0_BASE + APB_TIM1_OFST)
#define TIM2_BASE          (AHBAPB0_BASE + APB_TIM2_OFST)
#define TIM3_BASE          (AHBAPB0_BASE + APB_TIM3_OFST)
#define GPIO0_BASE         (AHBAPB0_BASE + APB_GPIO0_OFST)
#define GPIO1_BASE         (AHBAPB0_BASE + APB_GPIO1_OFST)
#define GPIO2_BASE         (AHBAPB0_BASE + APB_GPIO2_OFST)
#define GPIO3_BASE         (AHBAPB0_BASE + APB_GPIO3_OFST)
#define GPIO4_BASE         (AHBAPB0_BASE + APB_GPIO4_OFST)
#define GPIO5_BASE         (AHBAPB0_BASE + APB_GPIO5_OFST)
#define GPIO6_BASE         (AHBAPB0_BASE + APB_GPIO6_OFST)
#define GPIO7_BASE         (AHBAPB0_BASE + APB_GPIO7_OFST)
#define GPIO8_BASE         (AHBAPB0_BASE + APB_GPIO8_OFST)
#define GPIO9_BASE         (AHBAPB0_BASE + APB_GPIO9_OFST)

/*******************************************************************************
*                      APB1 Peripherals' Base addresses                        *
*******************************************************************************/

#define RTC_BASE           (AHBAPB1_BASE + APB_RTC_OFST)
#define SCU_BASE           (AHBAPB1_BASE + APB_SCU_OFST)
#define MC_BASE            (AHBAPB1_BASE + APB_MC_OFST)
#define UART0_BASE         (AHBAPB1_BASE + APB_UART0_OFST)
#define UART1_BASE         (AHBAPB1_BASE + APB_UART1_OFST)
#define UART2_BASE         (AHBAPB1_BASE + APB_UART2_OFST)
#define SSP0_BASE          (AHBAPB1_BASE + APB_SSP0_OFST)
#define SSP1_BASE          (AHBAPB1_BASE + APB_SSP1_OFST)
#define CAN_BASE           (AHBAPB1_BASE + APB_CAN_OFST)
#define ADC_BASE           (AHBAPB1_BASE + APB_ADC_OFST)
#define WDG_BASE           (AHBAPB1_BASE + APB_WDG_OFST)
#define I2C0_BASE          (AHBAPB1_BASE + APB_I2C0_OFST)
#define I2C1_BASE          (AHBAPB1_BASE + APB_I2C1_OFST)

/*******************************************************************************
*                                IPs' declaration                              *
*******************************************************************************/

/*------------------------------ Non Debug Mode ------------------------------*/

#ifndef DEBUG

/*********************************** AHBAPB ***********************************/

#define AHBAPB0               ((AHBAPB_TypeDef *)AHBAPB0_BASE)
#define AHBAPB1               ((AHBAPB_TypeDef *)AHBAPB1_BASE)

/************************************* EMI ************************************/

#define EMI                ((EMI_TypeDef *)EMI_BASE)

/************************************* DMA ************************************/

#define DMA                ((DMA_TypeDef *)DMA_BASE)
#define DMA_Channel0       ((DMA_Channel_TypeDef *)DMA_Channel0_BASE)
#define DMA_Channel1       ((DMA_Channel_TypeDef *)DMA_Channel1_BASE)
#define DMA_Channel2       ((DMA_Channel_TypeDef *)DMA_Channel2_BASE)
#define DMA_Channel3       ((DMA_Channel_TypeDef *)DMA_Channel3_BASE)
#define DMA_Channel4       ((DMA_Channel_TypeDef *)DMA_Channel4_BASE)
#define DMA_Channel5       ((DMA_Channel_TypeDef *)DMA_Channel5_BASE)
#define DMA_Channel6       ((DMA_Channel_TypeDef *)DMA_Channel6_BASE)
#define DMA_Channel7       ((DMA_Channel_TypeDef *)DMA_Channel7_BASE)

/************************************* EMI ************************************/

#define EMI_Bank0         ((EMI_Bank_TypeDef *)EMI_Bank0_BASE)
#define EMI_Bank1         ((EMI_Bank_TypeDef *)EMI_Bank1_BASE)
#define EMI_Bank2         ((EMI_Bank_TypeDef *)EMI_Bank2_BASE)
#define EMI_Bank3         ((EMI_Bank_TypeDef *)EMI_Bank3_BASE)

/************************************* ENET_MAC ************************************/

#define ENET_MAC              ((ENET_MAC_TypeDef *)ENET_MAC_BASE)

/************************************* ENET_DMA ************************************/

#define ENET_DMA              ((ENET_DMA_TypeDef *)ENET_DMA_BASE)

/************************************* FMI ************************************/

#define FMI                ((FMI_TypeDef *)FMI_BASE)

/************************************* VIC ************************************/

#define VIC0               ((VIC_TypeDef *)VIC0_BASE)
#define VIC1               ((VIC_TypeDef *)VIC1_BASE)

/*******************************************************************************
*                              APB0 Peripherals'                               *
*******************************************************************************/
#define WIU                ((WIU_TypeDef *)WIU_BASE)
#define TIM0               ((TIM_TypeDef *)TIM0_BASE)
#define TIM1               ((TIM_TypeDef *)TIM1_BASE)
#define TIM2               ((TIM_TypeDef *)TIM2_BASE)
#define TIM3               ((TIM_TypeDef *)TIM3_BASE)
#define GPIO0              ((GPIO_TypeDef *)GPIO0_BASE)
#define GPIO1              ((GPIO_TypeDef *)GPIO1_BASE)
#define GPIO2              ((GPIO_TypeDef *)GPIO2_BASE)
#define GPIO3              ((GPIO_TypeDef *)GPIO3_BASE)
#define GPIO4              ((GPIO_TypeDef *)GPIO4_BASE)
#define GPIO5              ((GPIO_TypeDef *)GPIO5_BASE)
#define GPIO6              ((GPIO_TypeDef *)GPIO6_BASE)
#define GPIO7              ((GPIO_TypeDef *)GPIO7_BASE)
#define GPIO8              ((GPIO_TypeDef *)GPIO8_BASE)
#define GPIO9              ((GPIO_TypeDef *)GPIO9_BASE)
/*******************************************************************************
*                              APB1 Peripherals'                               *
*******************************************************************************/
#define RTC                ((RTC_TypeDef *)RTC_BASE)
#define SCU                ((SCU_TypeDef *)SCU_BASE)
#define MC                 ((MC_TypeDef *)MC_BASE)
#define UART0              ((UART_TypeDef *)UART0_BASE)
#define UART1              ((UART_TypeDef *)UART1_BASE)
#define UART2              ((UART_TypeDef *)UART2_BASE)
#define SSP0               ((SSP_TypeDef *)SSP0_BASE)
#define SSP1               ((SSP_TypeDef *)SSP1_BASE)
#define CAN                ((CAN_TypeDef *)CAN_BASE)
#define ADC                ((ADC_TypeDef *)ADC_BASE)
#define WDG                ((WDG_TypeDef *)WDG_BASE)
#define I2C0               ((I2C_TypeDef *)I2C0_BASE)
#define I2C1               ((I2C_TypeDef *)I2C1_BASE)
#define ENET_MAC           ((ENET_MAC_TypeDef *)ENET_MAC_BASE)
#define ENET_DMA           ((ENET_DMA_TypeDef *)ENET_DMA_BASE)

#else   /* DEBUG */

/*-------------------------------- Debug Mode --------------------------------*/

EXT AHBAPB_TypeDef         *AHBAPB0;
EXT AHBAPB_TypeDef         *AHBAPB1;
EXT DMA_TypeDef            *DMA;
EXT DMA_Channel_TypeDef    *DMA_Channel0;
EXT DMA_Channel_TypeDef    *DMA_Channel1;
EXT DMA_Channel_TypeDef    *DMA_Channel2;
EXT DMA_Channel_TypeDef    *DMA_Channel3;
EXT DMA_Channel_TypeDef    *DMA_Channel4;
EXT DMA_Channel_TypeDef    *DMA_Channel5;
EXT DMA_Channel_TypeDef    *DMA_Channel6;
EXT DMA_Channel_TypeDef    *DMA_Channel7;
EXT EMI_Bank_TypeDef       *EMI_Bank0;
EXT EMI_Bank_TypeDef       *EMI_Bank1;
EXT EMI_Bank_TypeDef       *EMI_Bank2;
EXT EMI_Bank_TypeDef       *EMI_Bank3;
EXT FMI_TypeDef            *FMI;
EXT VIC_TypeDef            *VIC0;
EXT VIC_TypeDef            *VIC1;
EXT WIU_TypeDef            *WIU;
EXT TIM_TypeDef            *TIM0;
EXT TIM_TypeDef            *TIM1;
EXT TIM_TypeDef            *TIM2;
EXT TIM_TypeDef            *TIM3;
EXT GPIO_TypeDef           *GPIO0;
EXT GPIO_TypeDef           *GPIO1;
EXT GPIO_TypeDef           *GPIO2;
EXT GPIO_TypeDef           *GPIO3;
EXT GPIO_TypeDef           *GPIO4;
EXT GPIO_TypeDef           *GPIO5;
EXT GPIO_TypeDef           *GPIO6;
EXT GPIO_TypeDef           *GPIO7;
EXT GPIO_TypeDef           *GPIO8;
EXT GPIO_TypeDef           *GPIO9;
EXT RTC_TypeDef            *RTC;
EXT SCU_TypeDef            *SCU;
EXT MC_TypeDef             *MC;
EXT UART_TypeDef           *UART0;
EXT UART_TypeDef           *UART1;
EXT UART_TypeDef           *UART2;
EXT SSP_TypeDef            *SSP0;
EXT SSP_TypeDef            *SSP1;
EXT CAN_TypeDef            *CAN;
EXT ADC_TypeDef            *ADC;
EXT WDG_TypeDef            *WDG;
EXT I2C_TypeDef            *I2C0;
EXT I2C_TypeDef            *I2C1;
EXT ENET_MAC_TypeDef       *ENET_MAC;
EXT ENET_DMA_TypeDef       *ENET_DMA;


#endif  /* DEBUG */

#endif  /* __91x_MAP_H*/

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/

