/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 *  SmartFusion A2FxxxM3 Cortex Microcontroller Software Interface - Peripheral
 *  Access Layer.
 *
 *  This file describes the interrupt assignment and peripheral registers for
 *  the SmartFusion A2FxxxM3 familly of devices. 
 *
 * SVN $Revision: 2331 $
 * SVN $Date: 2010-02-26 12:02:06 +0000 (Fri, 26 Feb 2010) $
 */
#ifndef __A2FXXXM3_H__
#define __A2FXXXM3_H__

#ifdef __cplusplus
extern "C" {
#endif 

/*
 * ==========================================================================
 * ---------- Interrupt Number Definition -----------------------------------
 * ==========================================================================
 */

typedef enum IRQn
{
/******  Cortex-M3 Processor Exceptions Numbers *********************************************************/
  NonMaskableInt_IRQn             = -14,      /*!< 2 Non Maskable Interrupt                             */
  HardFault_IRQn                  = -13,      /*!< 2 Hard Fault Interrupt                               */
  MemoryManagement_IRQn           = -12,      /*!< 4 Cortex-M3 Memory Management Interrupt              */
  BusFault_IRQn                   = -11,      /*!< 5 Cortex-M3 Bus Fault Interrupt                      */
  UsageFault_IRQn                 = -10,      /*!< 6 Cortex-M3 Usage Fault Interrupt                    */
  SVCall_IRQn                     = -5,       /*!< 11 Cortex-M3 SV Call Interrupt                       */
  DebugMonitor_IRQn               = -4,       /*!< 12 Cortex-M3 Debug Monitor Interrupt                 */
  PendSV_IRQn                     = -2,       /*!< 14 Cortex-M3 Pend SV Interrupt                       */
  SysTick_IRQn                    = -1,       /*!< 15 Cortex-M3 System Tick Interrupt                   */

/******  SmartFusion specific Interrupt Numbers *********************************************************/
  WdogWakeup_IRQn                 = 0,        /*!< WatchDog wakeup interrupt                            */
  BrownOut_1_5V_IRQn              = 1,        /*!< Supply dropped below 1.5V                            */
  BrownOut_3_3V_IRQn              = 2,        /*!< Supply dropped below 1.5V                            */
  RTC_Match_IRQn                  = 3,        /*!< RTC match interrupt                                  */
  RTCIF_Pub_IRQn                  = 4,        /*!< RTC interface push button interrupt                  */
  EthernetMAC_IRQn                = 5,        /*!< Ethernet MAC interrupt                               */
  IAP_IRQn                        = 6,        /*!< In Application Programming (IAP) interrupt           */
  ENVM0_IRQn                      = 7,        /*!< eNVM0 operation completion interrupt                 */
  ENVM1_IRQn                      = 8,        /*!< eNVM1 operation completion interrupt                 */
  DMA_IRQn                        = 9,        /*!< Peripheral DMA interrupt                             */
  UART0_IRQn                      = 10,       /*!< UART0 interrupt                                      */
  UART1_IRQn                      = 11,       /*!< UART1 interrupt                                      */
  SPI0_IRQn                       = 12,       /*!< SPI0 interrupt                                       */
  SPI1_IRQn                       = 13,       /*!< SP1 interrupt                                        */
  I2C0_IRQn                       = 14,       /*!< I2C0 interrupt                                       */
  I2C0_SMBAlert_IRQn              = 15,       /*!< I2C0 SMBus Alert interrupt                           */
  I2C0_SMBus_IRQn                 = 16,       /*!< I2C0 SMBus Suspend interrupt                         */
  I2C1_IRQn                       = 17,       /*!< I2C1 interrupt                                       */
  I2C1_SMBAlert_IRQn              = 18,       /*!< I2C1 SMBus Alert interrupt                           */
  I2C1_SMBus_IRQn                 = 19,       /*!< I2C1 SMBus Suspend interrupt                         */
  Timer1_IRQn                     = 20,       /*!< Timer1 interrupt                                     */
  Timer2_IRQn                     = 21,       /*!< Timer2 interrupt                                     */
  PLL_Lock_IRQn                   = 22,       /*!< PLL lock interrupt                                   */
  PLL_LockLost_IRQn               = 23,       /*!< PLL loss of lock interrupt                           */
  CommError_IRQn                  = 24,       /*!< Communications Matrix error interrupt                */
  Fabric_IRQn                     = 31,       /*!< FPGA fabric interrupt                                */
  GPIO0_IRQn                      = 32,       /*!< GPIO 0 interrupt                                     */
  GPIO1_IRQn                      = 33,       /*!< GPIO 1 interrupt                                     */
  GPIO2_IRQn                      = 34,       /*!< GPIO 2 interrupt                                     */
  GPIO3_IRQn                      = 35,       /*!< GPIO 3 interrupt                                     */
  GPIO4_IRQn                      = 36,       /*!< GPIO 4 interrupt                                     */
  GPIO5_IRQn                      = 37,       /*!< GPIO 5 interrupt                                     */
  GPIO6_IRQn                      = 38,       /*!< GPIO 6 interrupt                                     */
  GPIO7_IRQn                      = 39,       /*!< GPIO 7 interrupt                                     */
  GPIO8_IRQn                      = 40,       /*!< GPIO 8 interrupt                                     */
  GPIO9_IRQn                      = 41,       /*!< GPIO 9 interrupt                                     */
  GPIO10_IRQn                     = 42,       /*!< GPIO 10 interrupt                                    */
  GPIO11_IRQn                     = 43,       /*!< GPIO 11 interrupt                                    */
  GPIO12_IRQn                     = 44,       /*!< GPIO 12 interrupt                                    */
  GPIO13_IRQn                     = 45,       /*!< GPIO 13 interrupt                                    */
  GPIO14_IRQn                     = 46,       /*!< GPIO 14 interrupt                                    */
  GPIO15_IRQn                     = 47,       /*!< GPIO 15 interrupt                                    */
  GPIO16_IRQn                     = 48,       /*!< GPIO 16 interrupt                                    */
  GPIO17_IRQn                     = 49,       /*!< GPIO 17 interrupt                                    */
  GPIO18_IRQn                     = 50,       /*!< GPIO 18 interrupt                                    */
  GPIO19_IRQn                     = 51,       /*!< GPIO 19 interrupt                                    */
  GPIO20_IRQn                     = 52,       /*!< GPIO 20 interrupt                                    */
  GPIO21_IRQn                     = 53,       /*!< GPIO 21 interrupt                                    */
  GPIO22_IRQn                     = 54,       /*!< GPIO 22 interrupt                                    */
  GPIO23_IRQn                     = 55,       /*!< GPIO 23 interrupt                                    */
  GPIO24_IRQn                     = 56,       /*!< GPIO 24 interrupt                                    */
  GPIO25_IRQn                     = 57,       /*!< GPIO 25 interrupt                                    */
  GPIO26_IRQn                     = 58,       /*!< GPIO 26 interrupt                                    */
  GPIO27_IRQn                     = 59,       /*!< GPIO 27 interrupt                                    */
  GPIO28_IRQn                     = 60,       /*!< GPIO 28 interrupt                                    */
  GPIO29_IRQn                     = 61,       /*!< GPIO 29 interrupt                                    */
  GPIO30_IRQn                     = 62,       /*!< GPIO 30 interrupt                                    */
  GPIO31_IRQn                     = 63,       /*!< GPIO 31 interrupt                                    */
  ACE_PC0_Flag0_IRQn              = 64,       /*!< ACE SSE program counter 0 flag 0 interrupt           */
  ACE_PC0_Flag1_IRQn              = 65,       /*!< ACE SSE program counter 0 flag 1 interrupt           */
  ACE_PC0_Flag2_IRQn              = 66,       /*!< ACE SSE program counter 0 flag 2 interrupt           */
  ACE_PC0_Flag3_IRQn              = 67,       /*!< ACE SSE program counter 0 flag 3 interrupt           */
  ACE_PC1_Flag0_IRQn              = 68,       /*!< ACE SSE program counter 1 flag 0 interrupt           */
  ACE_PC1_Flag1_IRQn              = 69,       /*!< ACE SSE program counter 1 flag 1 interrupt           */
  ACE_PC1_Flag2_IRQn              = 70,       /*!< ACE SSE program counter 1 flag 2 interrupt           */
  ACE_PC1_Flag3_IRQn              = 71,       /*!< ACE SSE program counter 1 flag 3 interrupt           */
  ACE_PC2_Flag0_IRQn              = 72,       /*!< ACE SSE program counter 2 flag 0 interrupt           */
  ACE_PC2_Flag1_IRQn              = 73,       /*!< ACE SSE program counter 2 flag 1 interrupt           */
  ACE_PC2_Flag2_IRQn              = 74,       /*!< ACE SSE program counter 2 flag 2 interrupt           */
  ACE_PC2_Flag3_IRQn              = 75,       /*!< ACE SSE program counter 2 flag 3 interrupt           */
  ACE_ADC0_DataValid_IRQn         = 76,       /*!< ACE ADC0 data valid interrupt                        */
  ACE_ADC1_DataValid_IRQn         = 77,       /*!< ACE ADC1 data valid interrupt		     			*/
  ACE_ADC2_DataValid_IRQn         = 78,       /*!< ACE ADC2 data valid interrupt		     			*/
  ACE_ADC0_CalDone_IRQn           = 79,       /*!< ACE ADC0 calibration done interrupt                  */
  ACE_ADC1_CalDone_IRQn           = 80,       /*!< ACE ADC1 calibration done interrupt                  */
  ACE_ADC2_CalDone_IRQn           = 81,       /*!< ACE ADC2 calibration done interrupt                  */
  ACE_ADC0_CalStart_IRQn          = 82,       /*!< ACE ADC0 calibration start interrupt                 */
  ACE_ADC1_CalStart_IRQn          = 83,       /*!< ACE ADC1 calibration start interrupt                 */
  ACE_ADC2_CalStart_IRQn          = 84,       /*!< ACE ADC2 calibration start interrupt                 */
  ACE_Comp0_Fall_IRQn             = 85,       /*!< ACE comparator 0 falling under reference interrupt   */
  ACE_Comp1_Fall_IRQn             = 86,       /*!< ACE comparator 1 falling under reference interrupt   */
  ACE_Comp2_Fall_IRQn             = 87,       /*!< ACE comparator 2 falling under reference interrupt   */
  ACE_Comp3_Fall_IRQn             = 88,       /*!< ACE comparator 3 falling under reference interrupt   */
  ACE_Comp4_Fall_IRQn             = 89,       /*!< ACE comparator 4 falling under reference interrupt   */
  ACE_Comp5_Fall_IRQn             = 90,       /*!< ACE comparator 5 falling under reference interrupt   */
  ACE_Comp6_Fall_IRQn             = 91,       /*!< ACE comparator 6 falling under reference interrupt   */
  ACE_Comp7_Fall_IRQn             = 92,       /*!< ACE comparator 7 falling under reference interrupt   */
  ACE_Comp8_Fall_IRQn             = 93,       /*!< ACE comparator 8 falling under reference interrupt   */
  ACE_Comp9_Fall_IRQn             = 94,       /*!< ACE comparator 9 falling under reference interrupt   */
  ACE_Comp10_Fall_IRQn            = 95,       /*!< ACE comparator 10 falling under reference interrupt  */
  ACE_Comp11_Fall_IRQn            = 96,       /*!< ACE comparator 11 falling under reference interrupt  */
  ACE_Comp0_Rise_IRQn             = 97,       /*!< ACE comparator 0 rising over reference interrupt     */
  ACE_Comp1_Rise_IRQn             = 98,       /*!< ACE comparator 1 rising over reference interrupt     */
  ACE_Comp2_Rise_IRQn             = 99,       /*!< ACE comparator 2 rising over reference interrupt     */
  ACE_Comp3_Rise_IRQn             = 100,      /*!< ACE comparator 3 rising over reference interrupt     */
  ACE_Comp4_Rise_IRQn             = 101,      /*!< ACE comparator 4 rising over reference interrupt     */
  ACE_Comp5_Rise_IRQn             = 102,      /*!< ACE comparator 5 rising over reference interrupt     */
  ACE_Comp6_Rise_IRQn             = 103,      /*!< ACE comparator 6 rising over reference interrupt     */
  ACE_Comp7_Rise_IRQn             = 104,      /*!< ACE comparator 7 rising over reference interrupt     */
  ACE_Comp8_Rise_IRQn             = 105,      /*!< ACE comparator 8 rising over reference interrupt     */
  ACE_Comp9_Rise_IRQn             = 106,      /*!< ACE comparator 9 rising over reference interrupt     */
  ACE_Comp10_Rise_IRQn            = 107,      /*!< ACE comparator 10 rising over reference interrupt    */
  ACE_Comp11_Rise_IRQn            = 108,      /*!< ACE comparator 11 rising over reference interrupt    */
  ACE_ADC0_FifoFull_IRQn          = 109,      /*!< ACE ADC0 FIFO full interrupt                         */
  ACE_ADC0_FifoAFull_IRQn         = 110,      /*!< ACE ADC0 FIFO almost full interrupt                  */
  ACE_ADC0_FifoEmpty_IRQn         = 111,      /*!< ACE ADC0 FIFO empty interrupt                        */
  ACE_ADC1_FifoFull_IRQn          = 112,      /*!< ACE ADC1 FIFO full interrupt                         */
  ACE_ADC1_FifoAFull_IRQn         = 113,      /*!< ACE ADC1 FIFO almost full interrupt                  */
  ACE_ADC1_FifoEmpty_IRQn         = 114,      /*!< ACE ADC1 FIFO empty interrupt                        */
  ACE_ADC2_FifoFull_IRQn          = 115,      /*!< ACE ADC2 FIFO full interrupt                         */
  ACE_ADC2_FifoAFull_IRQn         = 116,      /*!< ACE ADC2 FIFO almost full interrupt                  */
  ACE_ADC2_FifoEmpty_IRQn         = 117,      /*!< ACE ADC2 FIFO empty interrupt                        */
  ACE_PPE_Flag0_IRQn              = 118,      /*!< ACE post processing engine flag 0 interrupt          */
  ACE_PPE_Flag1_IRQn              = 119,      /*!< ACE post processing engine flag 1 interrupt          */
  ACE_PPE_Flag2_IRQn              = 120,      /*!< ACE post processing engine flag 2 interrupt          */
  ACE_PPE_Flag3_IRQn              = 121,      /*!< ACE post processing engine flag 3 interrupt          */
  ACE_PPE_Flag4_IRQn              = 122,      /*!< ACE post processing engine flag 4 interrupt          */
  ACE_PPE_Flag5_IRQn              = 123,      /*!< ACE post processing engine flag 5 interrupt          */
  ACE_PPE_Flag6_IRQn              = 124,      /*!< ACE post processing engine flag 6 interrupt          */
  ACE_PPE_Flag7_IRQn              = 125,      /*!< ACE post processing engine flag 7 interrupt          */
  ACE_PPE_Flag8_IRQn              = 126,      /*!< ACE post processing engine flag 8 interrupt          */
  ACE_PPE_Flag9_IRQn              = 127,      /*!< ACE post processing engine flag 9 interrupt          */
  ACE_PPE_Flag10_IRQn             = 128,      /*!< ACE post processing engine flag 10 interrupt         */
  ACE_PPE_Flag11_IRQn             = 129,      /*!< ACE post processing engine flag 11 interrupt         */
  ACE_PPE_Flag12_IRQn             = 130,      /*!< ACE post processing engine flag 12 interrupt         */
  ACE_PPE_Flag13_IRQn             = 131,      /*!< ACE post processing engine flag 13 interrupt         */
  ACE_PPE_Flag14_IRQn             = 132,      /*!< ACE post processing engine flag 14 interrupt         */
  ACE_PPE_Flag15_IRQn             = 133,      /*!< ACE post processing engine flag 15 interrupt         */
  ACE_PPE_Flag16_IRQn             = 134,      /*!< ACE post processing engine flag 16 interrupt         */
  ACE_PPE_Flag17_IRQn             = 135,      /*!< ACE post processing engine flag 17 interrupt         */
  ACE_PPE_Flag18_IRQn             = 136,      /*!< ACE post processing engine flag 18 interrupt         */
  ACE_PPE_Flag19_IRQn             = 137,      /*!< ACE post processing engine flag 19 interrupt         */
  ACE_PPE_Flag20_IRQn             = 138,      /*!< ACE post processing engine flag 20 interrupt         */
  ACE_PPE_Flag21_IRQn             = 139,      /*!< ACE post processing engine flag 21 interrupt         */
  ACE_PPE_Flag22_IRQn             = 140,      /*!< ACE post processing engine flag 22 interrupt         */
  ACE_PPE_Flag23_IRQn             = 141,      /*!< ACE post processing engine flag 23 interrupt         */
  ACE_PPE_Flag24_IRQn             = 142,      /*!< ACE post processing engine flag 24 interrupt         */
  ACE_PPE_Flag25_IRQn             = 143,      /*!< ACE post processing engine flag 25 interrupt         */
  ACE_PPE_Flag26_IRQn             = 144,      /*!< ACE post processing engine flag 26 interrupt         */
  ACE_PPE_Flag27_IRQn             = 145,      /*!< ACE post processing engine flag 27 interrupt         */
  ACE_PPE_Flag28_IRQn             = 146,      /*!< ACE post processing engine flag 28 interrupt         */
  ACE_PPE_Flag29_IRQn             = 147,      /*!< ACE post processing engine flag 29 interrupt         */
  ACE_PPE_Flag30_IRQn             = 148,      /*!< ACE post processing engine flag 30 interrupt         */
  ACE_PPE_Flag31_IRQn             = 149       /*!< ACE post processing engine flag 31 interrupt         */
} IRQn_Type;


/*
 * ==========================================================================
 * ----------- Processor and Core Peripheral Section ------------------------
 * ==========================================================================
 */

/* Configuration of the Cortex-M3 Processor and Core Peripherals */
#define __MPU_PRESENT             1           /*!< SmartFusion includes a MPU                       */
#define __NVIC_PRIO_BITS          5           /*!< SmartFusion uses 5 Bits for the Priority Levels  */
#define __Vendor_SysTickConfig    0           /*!< Set to 1 if different SysTick Config is used     */


#include "core_cm3.h"                         /* Cortex-M3 processor and core peripherals           */
#include "system_a2fxxxm3.h"                  /* SmartFusion System                                 */

/******************************************************************************/
/*                Device Specific Peripheral registers structures             */
/******************************************************************************/
#if defined   ( __CC_ARM   )
  /* Enable anonymous unions when building using Keil-MDK */
  #pragma anon_unions
#endif
/*----------------------------------------------------------------------------*/
/*----------------------------------- UART -----------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    union
    {
        __I  uint8_t    RBR;
        __O  uint8_t    THR;
        __IO uint8_t    DLR;
             uint32_t   RESERVED0;
    };

    union
    {
        __IO uint8_t  DMR;
        __IO uint8_t  IER;
             uint32_t RESERVED1;
    };

    union
    {
        __IO uint8_t  IIR;
        __IO uint8_t  FCR;
             uint32_t RESERVED2;
    };    

    __IO uint8_t  LCR;
         uint8_t  RESERVED3;
         uint16_t RESERVED4;
    __IO uint8_t  MCR;
         uint8_t  RESERVED5;
         uint16_t RESERVED6;
    __I  uint8_t  LSR;
         uint8_t  RESERVED7;
         uint16_t RESERVED8;
    __I  uint8_t  MSR;
         uint8_t  RESERVED9;
         uint16_t RESERVED10;
    __IO uint8_t  SR;
         uint8_t  RESERVED11;
         uint16_t RESERVED12;
} UART_TypeDef;

/*------------------------------------------------------------------------------
 *
 */
typedef struct
{
         uint32_t RESERVED0[32];
         
    __IO uint32_t IER_ERBFI;
    __IO uint32_t IER_ETBEI;
    __IO uint32_t IER_ELSI;
    __IO uint32_t IER_EDSSI;
    
         uint32_t RESERVED1[28];
    
    __IO uint32_t FCR_ENABLE;
    __IO uint32_t FCR_CLEAR_RX_FIFO;
    __IO uint32_t FCR_CLEAR_TX_FIFO;
    __IO uint32_t FCR_RXRDY_TXRDYN_EN;
    __IO uint32_t FCR_RESERVED0;
    __IO uint32_t FCR_RESERVED1;
    __IO uint32_t FCR_RX_TRIG0;
    __IO uint32_t FCR_RX_TRIG1;
      
         uint32_t RESERVED2[24];
    
    __IO uint32_t LCR_WLS0;
    __IO uint32_t LCR_WLS1;
    __IO uint32_t LCR_STB;
    __IO uint32_t LCR_PEN;
    __IO uint32_t LCR_EPS;
    __IO uint32_t LCR_SP;
    __IO uint32_t LCR_SB;
    __IO uint32_t LCR_DLAB;
      
         uint32_t RESERVED3[24];
    
    __IO uint32_t MCR_DTR;
    __IO uint32_t MCR_RTS;
    __IO uint32_t MCR_OUT1;
    __IO uint32_t MCR_OUT2;
    __IO uint32_t MCR_LOOP;
      
         uint32_t RESERVED4[27];
        
    __I  uint32_t LSR_DR;
    __I  uint32_t LSR_OE;
    __I  uint32_t LSR_PE;
    __I  uint32_t LSR_FE;
    __I  uint32_t LSR_BI;
    __I  uint32_t LSR_THRE;
    __I  uint32_t LSR_TEMT;
    __I  uint32_t LSR_FIER;
            
         uint32_t RESERVED5[24];
         
    __I  uint32_t MSR_DCTS;
    __I  uint32_t MSR_DDSR;
    __I  uint32_t MSR_TERI;
    __I  uint32_t MSR_DDCD;
    __I  uint32_t MSR_CTS;
    __I  uint32_t MSR_DSR;
    __I  uint32_t MSR_RI;
    __I  uint32_t MSR_DCD;
  
} UART_BitBand_TypeDef;

/*----------------------------------------------------------------------------*/
/*----------------------------------- I2C ------------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint8_t  CTRL;
         uint8_t  RESERVED0;
         uint16_t RESERVED1;
         uint8_t  STATUS;
         uint8_t  RESERVED2;
         uint16_t RESERVED3;
    __IO uint8_t  DATA;
         uint8_t  RESERVED4;
         uint16_t RESERVED5;
    __IO uint8_t  ADDR;
         uint8_t  RESERVED6;
         uint16_t RESERVED7;
    __IO uint8_t  SMBUS;
         uint8_t  RESERVED8;
         uint16_t RESERVED9;
    __IO uint8_t  FREQ;
         uint8_t  RESERVED10;
         uint16_t RESERVED11;
    __IO uint8_t  GLITCHREG;
         uint8_t  RESERVED12;
         uint16_t RESERVED13;
} I2C_TypeDef;

/*------------------------------------------------------------------------------
 *
 */
typedef struct
{
    uint32_t CTRL_CR0;
    uint32_t CTRL_CR1;
    uint32_t CTRL_AA;
    uint32_t CTRL_SI;
    uint32_t CTRL_STO;
    uint32_t CTRL_STA;
    uint32_t CTRL_ENS1;
    uint32_t CTRL_CR2;
    uint32_t RESERVED0[56];
    uint32_t DATA_DIR;
    uint32_t RESERVED1[31];
    uint32_t ADDR_GC;
} I2C_BitBand_TypeDef;

/*----------------------------------------------------------------------------*/
/*----------------------------------- SPI ------------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t CONTROL;
    __IO uint32_t TXRXDF_SIZE;
    __I  uint32_t STATUS;
    __O  uint32_t INT_CLEAR;
    __I  uint32_t RX_DATA;
    __O  uint32_t TX_DATA;
    __IO uint32_t CLK_GEN;
    __IO uint32_t SLAVE_SELECT;
    __I  uint32_t MIS;
    __I  uint32_t RIS;
} SPI_TypeDef;

typedef struct
{
    __IO uint32_t CTRL_ENABLE;
    __IO uint32_t CTRL_MASTER;
    __IO uint32_t CTRL_MODE[2];
    __IO uint32_t CTRL_RX_INT_EN;
    __IO uint32_t CTRL_TX_INT_EN;
    __IO uint32_t CTRL_RX_OVERFLOW_INT_EN;
    __IO uint32_t CTRL_TX_UNDERRUN_INT_EN;
    __IO uint32_t CTRL_TXRXDFCOUNT[16];
    __IO uint32_t CTRL_SPO;
    __IO uint32_t CTRL_SPH;
    __IO uint32_t CTRL_RESERVED[6];
    
    __IO uint32_t TXRXDF_SIZE[32];
    
    __I  uint32_t STATUS_TX_DONE;
    __I  uint32_t STATUS_RX_RDY;
    __I  uint32_t STATUS_RX_CH_OV;
    __I  uint32_t STATUS_TX_CH_UV;
    __I  uint32_t STATUS_RX_FIFO_FULL;
    __I  uint32_t STATUS_RX_FIFO_FULL_NEXT;
    __I  uint32_t STATUS_RX_FIFO_EMPTY;
    __I  uint32_t STATUS_RX_FIFO_EMPTY_NEXT;
    __I  uint32_t STATUS_TX_FIFO_FULL;
    __I  uint32_t STATUS_TX_FIFO_FULL_NEXT;
    __I  uint32_t STATUS_TX_FIFO_EMPTY;
    __I  uint32_t STATUS_TX_FIFO_EMPTY_NEXT;
    __I  uint32_t STATUS_RESERVED[20];
    
    __O  uint32_t INT_CLEAR_TX_DONE;
    __O  uint32_t INT_CLEAR_RX_RDY;
    __O  uint32_t INT_CLEAR_RX_OVER;
    __O  uint32_t INT_CLEAR_TX_UNDER;
    __O  uint32_t INT_CLEAR[28];
    
    __I  uint32_t RX_DATA[32];
    __O  uint32_t TX_DATA[32];
    __IO uint32_t CLK_GEN[32];
    __IO uint32_t SLAVE_SELECT[32];
    __I  uint32_t MIS_TX_DONE;
    __I  uint32_t MIS_RX_RDY;
    __I  uint32_t MIS_RX_OVER;
    __I  uint32_t MIS_TX_UNDER;
    __I  uint32_t MIS[28];
    __I  uint32_t RIS[32];
} SPI_BitBand_TypeDef;

/*----------------------------------------------------------------------------*/
/*----------------------------------- GPIO -----------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t GPIO_0_CFG;
    __IO uint32_t GPIO_1_CFG;
    __IO uint32_t GPIO_2_CFG;
    __IO uint32_t GPIO_3_CFG;
    __IO uint32_t GPIO_4_CFG;
    __IO uint32_t GPIO_5_CFG;
    __IO uint32_t GPIO_6_CFG;
    __IO uint32_t GPIO_7_CFG;
    __IO uint32_t GPIO_8_CFG;
    __IO uint32_t GPIO_9_CFG;
    __IO uint32_t GPIO_10_CFG;
    __IO uint32_t GPIO_11_CFG;
    __IO uint32_t GPIO_12_CFG;
    __IO uint32_t GPIO_13_CFG;
    __IO uint32_t GPIO_14_CFG;
    __IO uint32_t GPIO_15_CFG;
    __IO uint32_t GPIO_16_CFG;
    __IO uint32_t GPIO_17_CFG;
    __IO uint32_t GPIO_18_CFG;
    __IO uint32_t GPIO_19_CFG;
    __IO uint32_t GPIO_20_CFG;
    __IO uint32_t GPIO_21_CFG;
    __IO uint32_t GPIO_22_CFG;
    __IO uint32_t GPIO_23_CFG;
    __IO uint32_t GPIO_24_CFG;
    __IO uint32_t GPIO_25_CFG;
    __IO uint32_t GPIO_26_CFG;
    __IO uint32_t GPIO_27_CFG;
    __IO uint32_t GPIO_28_CFG;
    __IO uint32_t GPIO_29_CFG;
    __IO uint32_t GPIO_30_CFG;
    __IO uint32_t GPIO_31_CFG;
    __IO uint32_t GPIO_IRQ;
    __I  uint32_t GPIO_IN;
    __IO uint32_t GPIO_OUT;
} GPIO_TypeDef;

typedef struct
{
    __IO uint32_t GPIO_0_CFG[32];
    __IO uint32_t GPIO_1_CFG[32];
    __IO uint32_t GPIO_2_CFG[32];
    __IO uint32_t GPIO_3_CFG[32];
    __IO uint32_t GPIO_4_CFG[32];
    __IO uint32_t GPIO_5_CFG[32];
    __IO uint32_t GPIO_6_CFG[32];
    __IO uint32_t GPIO_7_CFG[32];
    __IO uint32_t GPIO_8_CFG[32];
    __IO uint32_t GPIO_9_CFG[32];
    __IO uint32_t GPIO_10_CFG[32];
    __IO uint32_t GPIO_11_CFG[32];
    __IO uint32_t GPIO_12_CFG[32];
    __IO uint32_t GPIO_13_CFG[32];
    __IO uint32_t GPIO_14_CFG[32];
    __IO uint32_t GPIO_15_CFG[32];
    __IO uint32_t GPIO_16_CFG[32];
    __IO uint32_t GPIO_17_CFG[32];
    __IO uint32_t GPIO_18_CFG[32];
    __IO uint32_t GPIO_19_CFG[32];
    __IO uint32_t GPIO_20_CFG[32];
    __IO uint32_t GPIO_21_CFG[32];
    __IO uint32_t GPIO_22_CFG[32];
    __IO uint32_t GPIO_23_CFG[32];
    __IO uint32_t GPIO_24_CFG[32];
    __IO uint32_t GPIO_25_CFG[32];
    __IO uint32_t GPIO_26_CFG[32];
    __IO uint32_t GPIO_27_CFG[32];
    __IO uint32_t GPIO_28_CFG[32];
    __IO uint32_t GPIO_29_CFG[32];
    __IO uint32_t GPIO_30_CFG[32];
    __IO uint32_t GPIO_31_CFG[32];
    __IO uint32_t GPIO_IRQ[32];
    __I  uint32_t GPIO_IN[32];
    __IO uint32_t GPIO_OUT[32];
} GPIO_BitBand_TypeDef;


/*----------------------------------------------------------------------------*/
/*----------------------------------- RTC ------------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t COUNTER0_REG;
    __IO uint32_t COUNTER1_REG;
    __IO uint32_t COUNTER2_REG;
    __IO uint32_t COUNTER3_REG;
    __IO uint32_t COUNTER4_REG;

    __IO uint32_t RESERVED0[3];
    
    __IO uint32_t MATCHREG0_REG;
    __IO uint32_t MATCHREG1_REG;
    __IO uint32_t MATCHREG2_REG;
    __IO uint32_t MATCHREG3_REG;
    __IO uint32_t MATCHREG4_REG;

    __IO uint32_t RESERVED1[3];
    
    __IO uint32_t MATCHBITS0_REG;
    __IO uint32_t MATCHBITS1_REG;
    __IO uint32_t MATCHBITS2_REG;
    __IO uint32_t MATCHBITS3_REG;
    __IO uint32_t MATCHBITS4_REG;

    __IO uint32_t RESERVED2[3];
    
    __IO uint32_t CTRL_STAT_REG;
} RTC_TypeDef;

/*----------------------------------------------------------------------------*/
/*---------------------------------- Timer -----------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __I  uint32_t TIM1_VAL;
    __IO uint32_t TIM1_LOADVAL;
    __IO uint32_t TIM1_BGLOADVAL;
    __IO uint32_t TIM1_CTRL;
    __IO uint32_t TIM1_RIS;
    __I  uint32_t TIM1_MIS;
	
    __I  uint32_t TIM2_VAL;
    __IO uint32_t TIM2_LOADVAL;
    __IO uint32_t TIM2_BGLOADVAL;
    __IO uint32_t TIM2_CTRL;
    __IO uint32_t TIM2_RIS;
    __I  uint32_t TIM2_MIS;
	
    __I  uint32_t TIM64_VAL_U;
    __I  uint32_t TIM64_VAL_L;
    __IO uint32_t TIM64_LOADVAL_U;
    __IO uint32_t TIM64_LOADVAL_L;
    __IO uint32_t TIM64_BGLOADVAL_U;
    __IO uint32_t TIM64_BGLOADVAL_L;
    __IO uint32_t TIM64_CTRL;
    __IO uint32_t TIM64_RIS;
    __I  uint32_t TIM64_MIS;
    __IO uint32_t TIM64_MODE;
} TIMER_TypeDef;

/*------------------------------------------------------------------------------
 * Timer bit band
 */
typedef struct
{
    __I  uint32_t TIM1_VALUE_BIT[32];
    __IO uint32_t TIM1_LOADVAL[32];
    __IO uint32_t TIM1_BGLOADVAL[32];
    
    __IO uint32_t TIM1ENABLE;
    __IO uint32_t TIM1MODE;
    __IO uint32_t TIM1INTEN;
    __IO uint32_t TIM1_CTRL_RESERVED[29];
    __IO uint32_t TIM1_RIS[32];
    __I  uint32_t TIM1_MIS[32];
	
    __I  uint32_t TIM2_VALUE[32];
    __IO uint32_t TIM2_LOADVAL[32];
    __IO uint32_t TIM2_BGLOADVAL[32];
    
    __IO uint32_t TIM2ENABLE;
    __IO uint32_t TIM2MODE;
    __IO uint32_t TIM2INTEN;
    __IO uint32_t TIM2_CTRL[29];
    __IO uint32_t TIM2_RIS[32];
    __I  uint32_t TIM2_MIS[32];
	
    __I  uint32_t TIM64VALUEU[32];
    __I  uint32_t TIM64VALUEL[32];
    __IO uint32_t TIM64LOADVALUEU[32];
    __IO uint32_t TIM64LOADVALUEL[32];
    __IO uint32_t TIM64BGLOADVALUEU[32];
    __IO uint32_t TIM64BGLOADVALUEL[32];
    __IO uint32_t TIM64ENABLE;
    __IO uint32_t TIM64MODE;
    __IO uint32_t TIM64INTEN;
    __IO uint32_t TIM64_CTRL[29];
    __IO uint32_t TIM64_RIS[32];
    __I  uint32_t TIM64_MIS[32];
    __IO uint32_t TIM64_MODE[32];
} TIMER_BitBand_TypeDef;

/*----------------------------------------------------------------------------*/
/*--------------------------------- Watchdog ---------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __I  uint32_t WDOGVALUE;
    __IO uint32_t WDOGLOAD;
    __IO uint32_t WDOGMVRP;
    __O  uint32_t WDOGREFRESH;
    __IO uint32_t WDOGENABLE;
    __IO uint32_t WDOGCONTROL;
    __I  uint32_t WDOGSTATUS;
    __IO uint32_t WDOGRIS;
    __I  uint32_t WDOGMIS;
} WATCHDOG_TypeDef;

/*----------------------------------------------------------------------------*/
/*----------------------------- Real Time Clock ------------------------------*/
/*----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------*/
/*----------------------------- Peripherals DMA ------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t CRTL;
    __IO uint32_t STATUS;
    __IO uint32_t BUFFER_A_SRC_ADDR;
    __IO uint32_t BUFFER_A_DEST_ADDR;
    __IO uint32_t BUFFER_A_TRANSFER_COUNT;
    __IO uint32_t BUFFER_B_SRC_ADDR;
    __IO uint32_t BUFFER_B_DEST_ADDR;
    __IO uint32_t BUFFER_B_TRANSFER_COUNT;
} PDMA_Channel_TypeDef;

typedef struct
{
    __IO uint32_t RATIO_HIGH_LOW;
    __IO uint32_t BUFFER_STATUS;
	     uint32_t RESERVED[6];
    PDMA_Channel_TypeDef CHANNEL[8];
} PDMA_TypeDef;

/*----------------------------------------------------------------------------*/
/*------------------------------ Ethernet MAC --------------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t CSR0;
         uint32_t RESERVED0;
    __IO uint32_t CSR1;
         uint32_t RESERVED1;
    __IO uint32_t CSR2;
         uint32_t RESERVED2;
    __IO uint32_t CSR3;
         uint32_t RESERVED3;
    __IO uint32_t CSR4;
         uint32_t RESERVED4;
    __IO uint32_t CSR5;
         uint32_t RESERVED5;
    __IO uint32_t CSR6;
         uint32_t RESERVED6;
    __IO uint32_t CSR7;
         uint32_t RESERVED7;
    __IO uint32_t CSR8;
         uint32_t RESERVED8;
    __IO uint32_t CSR9;
         uint32_t RESERVED9;
         uint32_t RESERVED10;
         uint32_t RESERVED11;
    __IO uint32_t CSR11;
} MAC_TypeDef;

/*----------------------------------------------------------------------------*/
/*---------------------- Analog Conversion Engine (ACE) ----------------------*/
/*----------------------------------------------------------------------------*/
/* Analog quad configuration */
typedef struct
{
    __IO uint8_t b0;
         uint8_t reserved0_0;
         uint16_t reserved0_1;
    __IO uint8_t b1;
         uint8_t reserved1_0;
         uint16_t reserved1_1;
    __IO uint8_t b2;
         uint8_t reserved2_0;
         uint16_t reserved2_1;
    __IO uint8_t b3;
         uint8_t reserved3_0;
         uint16_t reserved3_1;
    __IO uint8_t b4;
         uint8_t reserved4_0;
         uint16_t reserved4_1;
    __IO uint8_t b5;
         uint8_t reserved5_0;
         uint16_t reserved5_1;
    __IO uint8_t b6;
         uint8_t reserved6_0;
         uint16_t reserved6_1;
    __IO uint8_t b7;
         uint8_t reserved7_0;
         uint16_t reserved7_1;
    __IO uint8_t b8;
         uint8_t reserved8_0;
         uint16_t reserved8_1;
    __IO uint8_t b9;
         uint8_t reserved9_0;
         uint16_t reserved9_1;
    __IO uint8_t b10;
         uint8_t reserved10_0;
         uint16_t reserved10_1;
    __IO uint8_t b11;
         uint8_t reserved11_0;
         uint16_t reserved11_1;
} AQ_config_t;

/* ACE memory map layout */
typedef struct
{
    __O  uint32_t NOP;
    __IO uint32_t SSE_TS_CTRL;
    __IO uint32_t ADC_SYNC_CONV;
    __IO uint32_t ANA_COMM_CTRL;
    __IO uint32_t DAC_SYNC_CTRL;
    __IO uint32_t PDMA_REQUEST;
	     uint32_t RESERVED0[10];
    __O  uint32_t PC0_LO;
    __O  uint32_t PC0_HI;
    __IO uint32_t PC0_CTRL;
    __IO uint32_t PC0_DLY;
    __IO uint32_t ADC0_CONV_CTRL;
    __IO uint32_t ADC0_STC;
    __IO uint32_t ADC0_TVC;
    __IO uint32_t ADC0_MISC_CTRL;
    __IO uint32_t DAC0_CTRL;
    __IO uint32_t DAC0_BYTE0;
    __IO uint32_t DAC0_BYTE1;
    __IO uint32_t DAC0_BYTE2;
    __IO uint32_t LC0;
    __O  uint32_t LC0_JMP_LO;
    __O  uint32_t LC0_JMP_HI;
    __O  uint32_t PC0_FLAGS;
    __O  uint32_t PC1_LO;
    __O  uint32_t PC1_HI;
    __IO uint32_t PC1_CTRL;
    __IO uint32_t PC1_DLY;
    __IO uint32_t ADC1_CONV_CTRL;
    __IO uint32_t ADC1_STC;
    __IO uint32_t ADC1_TVC;
    __IO uint32_t ADC1_MISC_CTRL;
    __IO uint32_t DAC1_CTRL;
    __IO uint32_t DAC1_BYTE0;
    __IO uint32_t DAC1_BYTE1;
    __IO uint32_t DAC1_BYTE2;
    __IO uint32_t LC1;
    __O  uint32_t LC1_JMP_LO;
    __O  uint32_t LC1_JMP_HI;
    __O  uint32_t PC1_FLAGS;
    __O  uint32_t PC2_LO;
    __O  uint32_t PC2_HI;
    __IO uint32_t PC2_CTRL;
    __IO uint32_t PC2_DLY;
    __IO uint32_t ADC2_CONV_CTRL;
    __IO uint32_t ADC2_STC;
    __IO uint32_t ADC2_TVC;
    __IO uint32_t ADC2_MISC_CTRL;
    __IO uint32_t DAC2_CTRL;
    __IO uint32_t DAC2_BYTE0;
    __IO uint32_t DAC2_BYTE1;
    __IO uint32_t DAC2_BYTE2;
    __IO uint32_t LC2;
    __O  uint32_t LC2_JMP_LO;
    __O  uint32_t LC2_JMP_HI;
    __O  uint32_t PC2_FLAGS;
	     uint32_t RESERVED1;
		 uint32_t RESERVED2;
    __IO uint32_t SSE_RAM_LO_IDATA;
    __IO uint32_t SSE_RAM_HI_IDATA;
	     uint32_t RESERVED3[61];
         AQ_config_t ACB_DATA[6];        
	     uint32_t RESERVED4[59];
    __IO uint32_t SSE_PC0;
    __IO uint32_t SSE_PC1;
    __IO uint32_t SSE_PC2;
	     uint32_t RESERVED5[57];
    __IO uint32_t SSE_DAC0_BYTES01;
    __IO uint32_t SSE_DAC1_BYTES01;
    __IO uint32_t SSE_DAC2_BYTES01;
	     uint32_t RESERVED6[61];
    __O  uint32_t SSE_ADC0_RESULTS;
    __O  uint32_t SSE_ADC1_RESULTS;
    __O  uint32_t SSE_ADC2_RESULTS;
		 uint32_t RESERVED7[61];
    __O  uint32_t SSE_PDMA_DATAIN;
		 uint32_t RESERVED8[63];
    __IO uint32_t SSE_RAM_DATA[512];
    __I  uint32_t ADC0_STATUS;
    __I  uint32_t ADC1_STATUS;
    __I  uint32_t ADC2_STATUS;
    __I  uint32_t COMPARATOR_STATUS;
	     uint32_t RESERVED9[124];
    __IO uint32_t SSE_IRQ_EN;
    __I  uint32_t SSE_IRQ;
    __O  uint32_t SSE_IRQ_CLR;
    __IO uint32_t COMP_IRQ_EN;
    __I  uint32_t COMP_IRQ;
    __O  uint32_t COMP_IRQ_CLR;
    __IO uint32_t PPE_FIFO_IRQ_EN;
    __I  uint32_t PPE_FIFO_IRQ;
    __O  uint32_t PPE_FIFO_IRQ_CLR;
    __IO uint32_t PPE_FLAGS0_IRQ_EN;
    __I  uint32_t PPE_FLAGS0_IRQ;
    __O  uint32_t PPE_FLAGS0_IRQ_CLR;
    __IO uint32_t PPE_FLAGS1_IRQ_EN;
    __I  uint32_t PPE_FLAGS1_IRQ;
    __O  uint32_t PPE_FLAGS1_IRQ_CLR;
    __IO uint32_t PPE_FLAGS2_IRQ_EN;
    __I  uint32_t PPE_FLAGS2_IRQ;
    __O  uint32_t PPE_FLAGS2_IRQ_CLR;
    __IO uint32_t PPE_FLAGS3_IRQ_EN;
    __I  uint32_t PPE_FLAGS3_IRQ;
    __O  uint32_t PPE_FLAGS3_IRQ_CLR;
    __IO uint32_t PPE_SFFLAGS_IRQ_EN;
    __I  uint32_t PPE_SFFLAGS_IRQ;
    __O  uint32_t PPE_SFFLAGS_IRQ_CLR;
    __IO uint32_t FPGA_FLAGS_SEL;
	     uint32_t RESERVED10[39];
    __IO uint32_t PPE_PDMA_CTRL;
    __I  uint32_t PDMA_STATUS;
    __IO uint32_t PPE_PDMA_DATAOUT;
	     uint32_t RESERVED11[61];
    __I  uint32_t PPE_NOP;
    __IO uint32_t PPE_CTRL;
    __IO uint32_t PPE_PC_ETC;
    __IO uint32_t PPE_SF;
    __IO uint32_t PPE_SCRATCH;
         uint32_t RESERVED12;
    __IO uint32_t ALU_CTRL;
    __I  uint32_t ALU_STATUS;
    __IO uint32_t ALU_A;
         uint32_t RESERVED50;
    __IO uint32_t ALU_B;
         uint32_t RESERVED53;
    __IO uint32_t ALU_C;
         uint32_t RESERVED51;
    __IO uint32_t ALU_D;
         uint32_t RESERVED52;
    __IO uint32_t ALU_E;
         uint32_t RESERVED54;
    __IO uint32_t PPE_FPTR;
         uint32_t RESERVED55;
    __IO uint32_t PPE_FLAGS0;
    __IO uint32_t PPE_FLAGS1;
    __IO uint32_t PPE_FLAGS2;
    __IO uint32_t PPE_FLAGS3;
    __IO uint32_t PPE_SFFLAGS;
         uint32_t RESERVED13[11];
    __IO uint32_t ADC0_FIFO_CTRL;
    __I  uint32_t ADC0_FIFO_STATUS;
    __IO uint32_t ADC0_FIFO_DATA;
    __IO uint32_t ADC1_FIFO_CTRL;
    __I  uint32_t ADC1_FIFO_STATUS;
    __IO uint32_t ADC1_FIFO_DATA;
    __IO uint32_t ADC2_FIFO_CTRL;
    __I  uint32_t ADC2_FIFO_STATUS;
    __IO uint32_t ADC2_FIFO_DATA;
         uint32_t RESERVED14[19];
    __I  uint32_t ADC0_FIFO_DATA_PEEK;
    __I  uint32_t ADC0_FIFO_DATA0;
    __I  uint32_t ADC0_FIFO_DATA1;
    __I  uint32_t ADC0_FIFO_DATA2;
    __I  uint32_t ADC0_FIFO_DATA3;
    __I  uint32_t ADC1_FIFO_DATA_PEEK;
    __I  uint32_t ADC1_FIFO_DATA0;
    __I  uint32_t ADC1_FIFO_DATA1;
    __I  uint32_t ADC1_FIFO_DATA2;
    __I  uint32_t ADC1_FIFO_DATA3;
    __I  uint32_t ADC2_FIFO_DATA_PEEK;
    __I  uint32_t ADC2_FIFO_DATA0;
    __I  uint32_t ADC2_FIFO_DATA1;
    __I  uint32_t ADC2_FIFO_DATA2;
    __I  uint32_t ADC2_FIFO_DATA3;
		 uint32_t RESERVED15[177];  
    __IO uint32_t PPE_RAM_DATA[512];
} ACE_TypeDef;

/*----------------------------------------------------------------------------*/
/*------------------------ In Application Programming ------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t IAP_IR;
    __IO uint32_t IAP_DR2;
    __IO uint32_t IAP_DR3;
    __IO uint32_t IAP_DR5;
    __IO uint32_t IAP_DR26;
    __IO uint32_t IAP_DR32;
    __IO uint32_t IAP_DR;
    __IO uint32_t IAP_DR_LENGTH;
    __IO uint32_t IAP_TAP_NEW_STATE;
    __IO uint32_t IAP_TAP_CONTROL;
    __I  uint32_t IAP_STATUS;
} IAP_TypeDef;

/*----------------------------------------------------------------------------*/
/*---------------------- eNVM Special Function Registers ---------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t STATUS;
    __IO uint32_t CONTROL;
    __IO uint32_t ENABLE;
         uint32_t RESERVED0;
    __IO uint32_t CONFIG_0;
    __IO uint32_t CONFIG_1;
    __IO uint32_t PAGE_STATUS_0;
    __IO uint32_t PAGE_STATUS_1;
    __IO uint32_t SEGMENT;
	__IO uint32_t ENVM_SELECT;
} NVM_TypeDef;

/*----------------------------------------------------------------------------*/
/*---------------------- eNVM Special Function Registers ---------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t MSSIRQ_EN0;
    __IO uint32_t MSSIRQ_EN1;
    __IO uint32_t MSSIRQ_EN2;
    __IO uint32_t MSSIRQ_EN3;
    __IO uint32_t MSSIRQ_EN4;
    __IO uint32_t MSSIRQ_EN5;
    __IO uint32_t MSSIRQ_EN6;
    __IO uint32_t MSSIRQ_EN7;
    __I  uint32_t MSSIRQ_SRC0;
    __I  uint32_t MSSIRQ_SRC1;
    __I  uint32_t MSSIRQ_SRC2;
    __I  uint32_t MSSIRQ_SRC3;
    __I  uint32_t MSSIRQ_SRC4;
    __I  uint32_t MSSIRQ_SRC5;
    __I  uint32_t MSSIRQ_SRC6;
    __I  uint32_t MSSIRQ_SRC7;
    __IO uint32_t FIIC_MR;
} MSS_IRQ_CTRL_TypeDef;

/*----------------------------------------------------------------------------*/
/*------------------------------ System Registers ----------------------------*/
/*----------------------------------------------------------------------------*/
typedef struct
{
    __IO uint32_t ESRAM_CR;
    __IO uint32_t ENVM_CR;
    __IO uint32_t ENVM_REMAP_SYS_CR;
    __IO uint32_t ENVM_REMAP_FAB_CR;
    __IO uint32_t FAB_PROT_SIZE_CR;
    __IO uint32_t FAB_PROT_BASE_CR;
    __IO uint32_t AHB_MATRIX_CR;
    __IO uint32_t MSS_SR;
    __IO uint32_t CLR_MSS_SR;
    __IO uint32_t EFROM_CR;
    __IO uint32_t IAP_CR;
    __IO uint32_t SOFT_IRQ_CR;
    __IO uint32_t SOFT_RST_CR;
    __IO uint32_t DEVICE_SR;
    __IO uint32_t SYSTICK_CR;
    __IO uint32_t EMC_MUX_CR;
    __IO uint32_t EMC_CS_0_CR;
    __IO uint32_t EMC_CS_1_CR;
    __IO uint32_t MSS_CLK_CR;
    __IO uint32_t MSS_CCC_DIV_CR;
    __IO uint32_t MSS_CCC_MUX_CR;
    __IO uint32_t MSS_CCC_PLL_CR;
    __IO uint32_t MSS_CCC_DLY_CR;
    __IO uint32_t MSS_CCC_SR;
    __IO uint32_t MSS_RCOSC_CR;
    __IO uint32_t VRPSM_CR;
    __IO uint32_t RESERVED;
    __IO uint32_t FAB_IF_CR;
    __IO uint32_t FAB_APB_HIWORD_DR;
    __IO uint32_t LOOPBACK_CR;
    __IO uint32_t MSS_IO_BANK_CR;
    __IO uint32_t GPIN_SOURCE_CR;
    __IO uint32_t TEST_SR;
    __IO uint32_t RED_REP_ADDR0;
    __I  uint32_t RED_REP_LOW_LOCS0;
    __I  uint32_t RED_REP_HIGH_LOCS0;
    __IO uint32_t RED_REP_ADDR1;
    __I  uint32_t RED_REP_LOW_LOCS1;
    __I  uint32_t RED_REP_HIGH_LOCS1;
    __IO uint32_t FABRIC_CR;
         uint32_t RESERVED1[24];
    __IO uint32_t IOMUX_CR[83];
} SYSREG_TypeDef;

#define SYSREG_ENVM_SOFTRESET_MASK      (uint32_t)0x00000001
#define SYSREG_ESRAM0_SOFTRESET_MASK    (uint32_t)0x00000002
#define SYSREG_ESRAM1_SOFTRESET_MASK    (uint32_t)0x00000004
#define SYSREG_EMC_SOFTRESET_MASK       (uint32_t)0x00000008
#define SYSREG_MAC_SOFTRESET_MASK       (uint32_t)0x00000010
#define SYSREG_PDMA_SOFTRESET_MASK      (uint32_t)0x00000020
#define SYSREG_TIMER_SOFTRESET_MASK     (uint32_t)0x00000040
#define SYSREG_UART0_SOFTRESET_MASK     (uint32_t)0x00000080
#define SYSREG_UART1_SOFTRESET_MASK     (uint32_t)0x00000100
#define SYSREG_SPI0_SOFTRESET_MASK      (uint32_t)0x00000200
#define SYSREG_SPI1_SOFTRESET_MASK      (uint32_t)0x00000400
#define SYSREG_I2C0_SOFTRESET_MASK      (uint32_t)0x00000800
#define SYSREG_I2C1_SOFTRESET_MASK      (uint32_t)0x00001000
#define SYSREG_ACE_SOFTRESET_MASK       (uint32_t)0x00002000
#define SYSREG_GPIO_SOFTRESET_MASK      (uint32_t)0x00004000
#define SYSREG_IAP_SOFTRESET_MASK       (uint32_t)0x00008000
#define SYSREG_EXT_SOFTRESET_MASK       (uint32_t)0x00010000
#define SYSREG_FPGA_SOFTRESET_MASK      (uint32_t)0x00020000
#define SYSREG_F2M_RESET_ENABLE_MASK    (uint32_t)0x00040000        
#define SYSREG_PADRESET_ENABLE_MASK     (uint32_t)0x00080000

/******************************************************************************/
/*                         Peripheral memory map                              */
/******************************************************************************/
#define UART0_BASE              0x40000000U
#define SPI0_BASE               0x40001000U
#define I2C0_BASE               0x40002000U
#define MAC_BASE                0x40003000U
#define PDMA_BASE               0x40004000U
#define TIMER_BASE              0x40005000U
#define WATCHDOG_BASE		    0x40006000U
#define H2F_IRQ_CTRL_BASE       0x40007000U
#define UART1_BASE              0x40010000U
#define SPI1_BASE               0x40011000U
#define I2C1_BASE               0x40012000U
#define GPIO_BASE               0x40013000U
#define RTC_BASE                0x40014100U
#define FROM_BASE               0x40015000U
#define IAP_BASE                0x40016000U
#define ACE_BASE                0x40020000U
#define FPGA_FABRIC_RAM_BASE    0x40040000U
#define FPGA_FABRIC_BASE        0x40050000U
#define ENVM_BASE               0x60000000U
#define ENVM_REGS_BASE          0x60100000U
#define SYSREG_BASE             0xE0042000U

/******************************************************************************/
/* bitband address calcualtion macro                             */
/******************************************************************************/
#define BITBAND_ADDRESS(X)  ((X & 0xF0000000U) + 0x02000000U + ((X & 0xFFFFFU) << 5))

/******************************************************************************/
/*                         Peripheral declaration                             */
/******************************************************************************/
#define UART0                ((UART_TypeDef *) UART0_BASE)
#define UART0_BITBAND        ((UART_BitBand_TypeDef *) BITBAND_ADDRESS(UART0_BASE))
#define SPI0                 ((SPI_TypeDef *) SPI0_BASE)
#define SPI0_BITBAND         ((SPI_BitBand_TypeDef *) BITBAND_ADDRESS(SPI0_BASE))
#define I2C0                 ((I2C_TypeDef *) I2C0_BASE)
#define I2C0_BITBAND         ((I2C_BitBand_TypeDef *) BITBAND_ADDRESS(I2C0_BASE))
#define MAC                  ((MAC_TypeDef *) MAC_BASE)
#define PDMA                 ((PDMA_TypeDef *) PDMA_BASE)
#define TIMER                ((TIMER_TypeDef *) TIMER_BASE)
#define TIMER_BITBAND        ((TIMER_BitBand_TypeDef *) BITBAND_ADDRESS(TIMER_BASE))
#define WATCHDOG             ((WATCHDOG_TypeDef *) WATCHDOG_BASE)
#define MSS_IRQ_CTRL         ((MSS_IRQ_CTRL_TypeDef *) H2F_IRQ_CTRL_BASE)
#define UART1                ((UART_TypeDef *) UART1_BASE)
#define UART1_BITBAND        ((UART_BitBand_TypeDef *) BITBAND_ADDRESS(UART1_BASE))
#define SPI1                 ((SPI_TypeDef *) SPI1_BASE)
#define SPI1_BITBAND         ((SPI_BitBand_TypeDef *) BITBAND_ADDRESS(SPI1_BASE))
#define I2C1                 ((I2C_TypeDef *) I2C1_BASE)
#define I2C1_BITBAND         ((I2C_BitBand_TypeDef *) BITBAND_ADDRESS(I2C1_BASE))
#define GPIO                 ((GPIO_TypeDef *) GPIO_BASE)
#define GPIO_BITBAND         ((GPIO_BitBand_TypeDef *) BITBAND_ADDRESS(GPIO_BASE))
#define RTC                  ((RTC_TypeDef *) RTC_BASE)
#define FROM                 ((void *) FROM_BASE)
#define IAP                  ((IAP_TypeDef *) IAP_BASE)
#define ACE                  ((ACE_TypeDef *) ACE_BASE)
#define FPGA_FABRIC_RAM      ((void *) FPGA_FABRIC_RAM_BASE)
#define FPGA_FABRIC          ((void *) FPGA_FABRIC_BASE)
#define ENVM                 ((void *) ENVM_BASE)
#define ENVM_REGS            ((NVM_TypeDef *) ENVM_REGS_BASE)
#define SYSREG               ((SYSREG_TypeDef *) SYSREG_BASE)

#ifdef __cplusplus
}
#endif

#endif	/* __A2FXXXM3_H__ */

