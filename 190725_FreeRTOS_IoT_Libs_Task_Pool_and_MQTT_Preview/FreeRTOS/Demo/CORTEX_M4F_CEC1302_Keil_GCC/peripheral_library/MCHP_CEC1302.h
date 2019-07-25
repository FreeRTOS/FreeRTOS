
/****************************************************************************************************//**
 * @file     MCHP_CEC1302.h
 *
 * @brief    CMSIS Cortex-M4 Peripheral Access Layer Header File for
 *           MCHP_CEC1302 from Microchip Technology Inc..
 *
 * @version  V1.1
 * @date     6. November 2015
 *
 * @note     Generated with SVDConv V2.87e 
 *           from CMSIS SVD File 'MCHP_CEC1302.svd' Version 1.1,
 *
 * @par      ARM Limited (ARM) is supplying this software for use with Cortex-M processor based 
 *           microcontroller, but can be equally used for other suitable processor architectures.
 *           This file can be freely distributed. Modifications to this file shall be clearly marked.
 *           
 *           THIS SOFTWARE IS PROVIDED "AS IS". NO WARRANTIES, WHETHER EXPRESS, IMPLIED
 *           OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
 *           MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
 *           ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
 *           CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER. 
 *
 *******************************************************************************************************/



/** @addtogroup Microchip Technology Inc.
  * @{
  */

/** @addtogroup MCHP_CEC1302
  * @{
  */

#ifndef MCHP_CEC1302_H
#define MCHP_CEC1302_H

#ifdef __cplusplus
extern "C" {
#endif


/* -------------------------  Interrupt Number Definition  ------------------------ */

typedef enum {
/* -------------------  Cortex-M4 Processor Exceptions Numbers  ------------------- */
  Reset_IRQn                    = -15,              /*!<   1  Reset Vector, invoked on Power up and warm reset                 */
  NonMaskableInt_IRQn           = -14,              /*!<   2  Non maskable Interrupt, cannot be stopped or preempted           */
  HardFault_IRQn                = -13,              /*!<   3  Hard Fault, all classes of Fault                                 */
  MemoryManagement_IRQn         = -12,              /*!<   4  Memory Management, MPU mismatch, including Access Violation
                                                         and No Match                                                          */
  BusFault_IRQn                 = -11,              /*!<   5  Bus Fault, Pre-Fetch-, Memory Access Fault, other address/memory
                                                         related Fault                                                         */
  UsageFault_IRQn               = -10,              /*!<   6  Usage Fault, i.e. Undef Instruction, Illegal State Transition    */
  SVCall_IRQn                   =  -5,              /*!<  11  System Service Call via SVC instruction                          */
  DebugMonitor_IRQn             =  -4,              /*!<  12  Debug Monitor                                                    */
  PendSV_IRQn                   =  -2,              /*!<  14  Pendable request for system service                              */
  SysTick_IRQn                  =  -1,              /*!<  15  System Tick Timer                                                */
/* -------------------  MCHP_CEC1302 Specific Interrupt Numbers  ------------------ */
  I2C0_IRQn                     =   0,              /*!<   0  I2C0 / SMB0 Interrupt ................. Also see GIRQ 12.0       */
  I2C1_IRQn                     =   1,              /*!<   1  I2C1 / SMB1 Interrupt ................. Also see GIRQ 12.1       */
  I2C2_IRQn                     =   2,              /*!<   2  I2C2 / SMB2 Interrupt ................. Also see GIRQ 12.2       */
  I2C3_IRQn                     =   3,              /*!<   3  I2C3 / SMB3 Interrupt ................. Also see GIRQ 12.3       */
  DMA0_IRQn                     =   4,              /*!<   4  DMA_CH0 Interrupt ..................... Also see GIRQ 13.16      */
  DMA1_IRQn                     =   5,              /*!<   5  DMA_CH1 Interrupt ..................... Also see GIRQ 13.17      */
  DMA2_IRQn                     =   6,              /*!<   6  DMA_CH2 Interrupt ..................... Also see GIRQ 13.18      */
  DMA3_IRQn                     =   7,              /*!<   7  DMA_CH3 Interrupt ..................... Also see GIRQ 13.19      */
  DMA4_IRQn                     =   8,              /*!<   8  DMA_CH4 Interrupt ..................... Also see GIRQ 13.20      */
  DMA5_IRQn                     =   9,              /*!<   9  DMA_CH5 Interrupt ..................... Also see GIRQ 13.21      */
  DMA6_IRQn                     =  10,              /*!<  10  DMA_CH6 Interrupt ..................... Also see GIRQ 13.22      */
  DMA7_IRQn                     =  11,              /*!<  11  DMA_CH7 Interrupt ..................... Also see GIRQ 13.23      */
  LPC_IRQn                      =  12,              /*!<  12  LPC Interrupt ......................... Also see GIRQ 14.2       */
  UART_IRQn                     =  13,              /*!<  13  UART Interrupt ........................ Also see GIRQ 15.0       */
  EMI_0_IRQn                    =  14,              /*!<  14  EMI_0 (IMAP) Interrupt ................ Also see GIRQ 15.2       */
  ACPIEC0_IBF_IRQn              =  15,              /*!<  15  ACPIEC[0] IBF Interrupt ............... Also see GIRQ 15.6       */
  ACPIEC0_OBF_IRQn              =  16,              /*!<  16  ACPIEC[0] OBF Interrupt ............... Also see GIRQ 15.7       */
  ACPIEC1_IBF_IRQn              =  17,              /*!<  17  ACPIEC[1] IBF Interrupt ............... Also see GIRQ 15.8       */
  ACPIEC1_OBF_IRQn              =  18,              /*!<  18  ACPIEC[1] OBF Interrupt ............... Also see GIRQ 15.9       */
  ACPIPM1_CTL_IRQn              =  19,              /*!<  19  ACPIPM1_CTL Interrupt ................. Also see GIRQ 15.10      */
  ACPIPM1_EN_IRQn               =  20,              /*!<  20  ACPIPM1_EN Interrupt .................. Also see GIRQ 15.11      */
  ACPIPM1_STS_IRQn              =  21,              /*!<  21  ACPIPM1_STS Interrupt ................. Also see GIRQ 15.12      */
  KBC8042_OBF_IRQn              =  22,              /*!<  22  8042EM OBF Interrupt .................. Also see GIRQ 15.13      */
  KBC8042_IBF_IRQn              =  23,              /*!<  23  8042EM IBF Interrupt .................. Also see GIRQ 15.14      */
  MAILBOX_IRQn                  =  24,              /*!<  24  MAILBOX Interrupt ..................... Also see GIRQ 15.15      */
  PECIHOST_IRQn                 =  25,              /*!<  25  PECIHOST Interrupt .................... Also see GIRQ 16.3       */
  TACH_0_IRQn                   =  26,              /*!<  26  TACH_0 Interrupt ...................... Also see GIRQ 17.0       */
  TACH_1_IRQn                   =  27,              /*!<  27  TACH_1 Interrupt ...................... Also see GIRQ 17.1       */
  ADC_SNGL_IRQn                 =  28,              /*!<  28  ADC_SNGL Interrupt .................... Also see GIRQ 17.10      */
  ADC_RPT_IRQn                  =  29,              /*!<  29  ADC_RPT Interrupt ..................... Also see GIRQ 17.11      */
  ADC2PWM_N1_IRQn               =  30,              /*!<  30  MCHP Reserved ADC2PWM_INT_N1 .......... Also see GIRQ 17.12      */
  ADC2PWM_N2_IRQn               =  31,              /*!<  31  MCHP Reserved ADC2PWM_INT_N2 .......... Also see GIRQ 17.13      */
  PS2_0_IRQn                    =  32,              /*!<  32  PS2_0 Interrupt ....................... Also see GIRQ 17.14      */
  PS2_1_IRQn                    =  33,              /*!<  33  PS2_1 Interrupt ....................... Also see GIRQ 17.15      */
  PS2_2_IRQn                    =  34,              /*!<  34  PS2_2 Interrupt ....................... Also see GIRQ 17.16      */
  PS2_3_IRQn                    =  35,              /*!<  35  PS2_3 Interrupt ....................... Also see GIRQ 17.17      */
  SPI0_TX_IRQn                  =  36,              /*!<  36  SPI0 TX Interrupt ..................... Also see GIRQ 18.0       */
  SPI0_RX_IRQn                  =  37,              /*!<  37  SPI0 RX Interrupt ..................... Also see GIRQ 18.1       */
  HTIMER_IRQn                   =  38,              /*!<  38  HTIMER Interrupt ...................... Also see GIRQ 17.20      */
  KEYSCAN_IRQn                  =  39,              /*!<  39  KSC Interrupt ......................... Also see GIRQ 17.21      */
  MAILBOX_DATA_IRQn             =  40,              /*!<  40  MAILBOX DATA Interrupt ................ Also see GIRQ 15.16      */
  RPM_STALL_IRQn                =  41,              /*!<  41  RPM_INT Stall Interrupt ............... Also see GIRQ 17.23      */
  RPM_SPIN_IRQn                 =  42,              /*!<  42  RPM_INT Spin Interrupt ................ Also see GIRQ 17.24      */
  PFR_STS_IRQn                  =  43,              /*!<  43  PFR_STS Interrupt ..................... Also see GIRQ 17.25      */
  PWM_WDT0_IRQn                 =  44,              /*!<  44  PWM_WDT0 Interrupt .................... Also see GIRQ 17.26      */
  PWM_WDT1_IRQn                 =  45,              /*!<  45  PWM_WDT1 Interrupt .................... Also see GIRQ 17.27      */
  PWM_WDT2_IRQn                 =  46,              /*!<  46  PWM_WDT2 Interrupt .................... Also see GIRQ 17.28      */
  BCM_ERR_IRQn                  =  47,              /*!<  47  BCM_INT Err Interrupt ................. Also see GIRQ 17.29      */
  BCM_BUSY_IRQn                 =  48,              /*!<  48  BCM_INT Busy Interrupt ................ Also see GIRQ 17.30      */
  TIMER0_IRQn                   =  49,              /*!<  49  TIMER_16_0 Interrupt .................. Also see GIRQ 23.0       */
  TIMER1_IRQn                   =  50,              /*!<  50  TIMER_16_1 Interrupt .................. Also see GIRQ 23.1       */
  TIMER2_IRQn                   =  51,              /*!<  51  TIMER_16_2 Interrupt .................. Also see GIRQ 23.2       */
  TIMER3_IRQn                   =  52,              /*!<  52  TIMER_16_3 Interrupt .................. Also see GIRQ 23.3       */
  TIMER4_IRQn                   =  53,              /*!<  53  TIMER_32_0 Interrupt .................. Also see GIRQ 23.4       */
  TIMER5_IRQn                   =  54,              /*!<  54  TIMER_32_1 Interrupt .................. Also see GIRQ 23.5       */
  SPI1_TX_IRQn                  =  55,              /*!<  55  SPI1 TX Interrupt ..................... Also see GIRQ 18.2       */
  SPI1_RX_IRQn                  =  56,              /*!<  56  SPI1 RX Interrupt ..................... Also see GIRQ 18.3       */
  GIRQ08_IRQn                   =  57,              /*!<  57  GIRQ08 ................................ Interrupt Aggregator     */
  GIRQ09_IRQn                   =  58,              /*!<  58  GIRQ09 ................................ Interrupt Aggregator     */
  GIRQ10_IRQn                   =  59,              /*!<  59  GIRQ10 ................................ Interrupt Aggregator     */
  GIRQ11_IRQn                   =  60,              /*!<  60  GIRQ11 ................................ Interrupt Aggregator     */
  GIRQ12_IRQn                   =  61,              /*!<  61  GIRQ12 ................................ Interrupt Aggregator     */
  GIRQ13_IRQn                   =  62,              /*!<  62  GIRQ13 ................................ Interrupt Aggregator     */
  GIRQ14_IRQn                   =  63,              /*!<  63  GIRQ14 ................................ Interrupt Aggregator     */
  GIRQ15_IRQn                   =  64,              /*!<  64  GIRQ15 ................................ Interrupt Aggregator     */
  GIRQ16_IRQn                   =  65,              /*!<  65  GIRQ16 ................................ Interrupt Aggregator     */
  GIRQ17_IRQn                   =  66,              /*!<  66  GIRQ17 ................................ Interrupt Aggregator     */
  GIRQ18_IRQn                   =  67,              /*!<  67  GIRQ18 ................................ Interrupt Aggregator     */
  GIRQ19_IRQn                   =  68,              /*!<  68  GIRQ19 ................................ Interrupt Aggregator     */
  GIRQ20_IRQn                   =  69,              /*!<  69  GIRQ20 ................................ Interrupt Aggregator     */
  GIRQ21_IRQn                   =  70,              /*!<  70  GIRQ21 ................................ Interrupt Aggregator     */
  GIRQ22_IRQn                   =  71,              /*!<  71  GIRQ22 ................................ Interrupt Aggregator     */
  GIRQ23_IRQn                   =  72,              /*!<  72  GIRQ23 ................................ Interrupt Aggregator     */
  DMA8_IRQn                     =  81,              /*!<  81  DMA_CH8 Interrupt ..................... Also see GIRQ 13.24      */
  DMA9_IRQn                     =  82,              /*!<  82  DMA_CH9 Interrupt ..................... Also see GIRQ 13.25      */
  DMA10_IRQn                    =  83,              /*!<  83  DMA_CH10 Interrupt .................... Also see GIRQ 13.26      */
  DMA11_IRQn                    =  84,              /*!<  84  DMA_CH11 Interrupt .................... Also see GIRQ 13.27      */
  PWM_WDT3_IRQn                 =  85,              /*!<  85  PWM_WDT3 Interrupt .................... Also see GIRQ 18.4       */
  RTC_IRQn                      =  91,              /*!<  91  RTC Interrupt ......................... Also see GIRQ 17.18      */
  RTC_ALARM_IRQn                =  92,              /*!<  92  RTC ALARM Interrupt ................... Also see GIRQ 17.19      */
	MAX_IRQn
} IRQn_Type;


/** @addtogroup Configuration_of_CMSIS
  * @{
  */


/* ================================================================================ */
/* ================      Processor and Core Peripheral Section     ================ */
/* ================================================================================ */

/* ----------------Configuration of the Cortex-M4 Processor and Core Peripherals---------------- */
#define __CM4_REV                 0x0100            /*!< Cortex-M4 Core Revision                                               */
#define __MPU_PRESENT                  0            /*!< MPU present or not                                                    */
#define __NVIC_PRIO_BITS               3            /*!< Number of Bits used for Priority Levels                               */
#define __Vendor_SysTickConfig         0            /*!< Set to 1 if different SysTick Config is used                          */
#define __FPU_PRESENT                  1            /*!< FPU present or not                                                    */
/** @} */ /* End of group Configuration_of_CMSIS */

#include "core_cm4.h"                               /*!< Cortex-M4 processor and core peripherals                              */

/* ================================================================================ */
/* ================       Custom Defines (added manually)          ================ */
/* ================================================================================ */

/* Register Union */
typedef union
{
    uint32_t w;
    uint16_t h[2];
    uint8_t  b[4];
} REG32_U;

/* ================================================================================ */
/* ================       Device Specific Peripheral Section       ================ */
/* ================================================================================ */


/** @addtogroup Device_Peripheral_Registers
  * @{
  */


/* -------------------  Start of section using anonymous unions  ------------------ */
#if defined(__CC_ARM)
  #pragma push
  #pragma anon_unions
#elif defined(__ICCARM__)
  #pragma language=extended
#elif defined(__GNUC__)
  /* anonymous unions are enabled by default */
#elif defined(__TMS470__)
/* anonymous unions are enabled by default */
#elif defined(__TASKING__)
  #pragma warning 586
#else
  #warning Not supported compiler type
#endif


typedef struct {
  union {
    __IO uint16_t  CR;                              /*!< MEM_BAR Control [15:0]                                                */
    
    struct {
      __IO uint16_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint16_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
           uint16_t             :  1;
      __IO uint16_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
    } CR_b;                                         /*!< BitSize                                                               */
  };
  __IO uint16_t  HOST_LO_ADDR;                      /*!< HOST_ADDRESS[15:0]                                                    */
  __IO uint16_t  HOST_HI_ADDR;                      /*!< HOST_ADDRESS[31:16]                                                   */
} LPC_CONFIG_MEM_BAR_Type;

typedef struct {
  __IO uint32_t  SOURCE;                            /*!< GIRQx Source Register(R/WC)                                           */
  __IO uint32_t  ENABLE_SET;                        /*!< GIRQx Enable Set Register (R/WS)                                      */
  __I  uint32_t  RESULT;                            /*!< GIRQx Result Register                                                 */
  __IO uint32_t  ENABLE_CLEAR;                      /*!< GIRQx Enable Clear Register.                                          */
  __I  uint32_t  RESERVED;
} INTR_IRQ_Type;

typedef struct {
  union {
    __IO uint8_t   ACTIVATE;                        /*!< Enable this channel for operation.                                    */
    
    struct {
      __IO uint8_t   EN         :  1;               /*!< Enable this channel for operation.                                    */
    } ACTIVATE_b;                                   /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED1[3];
  __IO uint32_t  MEM_START_ADDR;                    /*!< starting address for the Memory device.                               */
  __IO uint32_t  MEM_END_ADDR;                      /*!< ending address for the Memory device.                                 */
  __IO uint32_t  DEVICE_ADDR;                       /*!< This is the Master Device address.                                    */
  
  union {
    __IO uint32_t  CONTROL;                         /*!< DMA Channel N Control                                                 */
    
    struct {
      __IO uint32_t  RUN        :  1;               /*!< 1= enabled and will service transfer requests                         */
      __I  uint32_t  REQUEST    :  1;               /*!< 1= transfer request from the Master Device                            */
      __I  uint32_t  DONE       :  1;               /*!< status signal. 1=Channel is done                                      */
      __I  uint32_t  STATUS     :  2;               /*!< 3: Error,2/1: ext/locally done,0:Disabled                             */
      __IO uint32_t  BUSY       :  1;               /*!< 1=Channel is busy (FSM is not IDLE)                                   */
           uint32_t             :  2;
      __IO uint32_t  TX_DIRECTION:  1;              /*!< direction of Transfer. 1=Memory to Device                             */
      __IO uint32_t  HARDWARE_FLOW_CONTROL_DEVICE:  7;/*!< device as its Hardware Flow Control master.                         */
      __IO uint32_t  INCREMENT_MEM_ADDR:  1;        /*!< auto-increment DMA Channel Memory Address.                            */
      __IO uint32_t  INCREMENT_DEVICE_ADDR:  1;     /*!< auto-increment DMA Channel Device Address.                            */
      __IO uint32_t  LOCK       :  1;               /*!< lock the arbitration of Channel Arbiter                               */
      __IO uint32_t  DISABLE_HW_FLOW_CONTROL:  1;   /*!< Disable the Hardware Flow Control.                                    */
      __IO uint32_t  TRANSFER_SIZE:  3;             /*!< transfer size in Bytes of each Data Packet                            */
           uint32_t             :  1;
      __IO uint32_t  TRANSFER_GO:  1;               /*!< Firmware Flow Control DMA transfer.                                   */
      __IO uint32_t  TRANSFER_ABORT:  1;            /*!< abort the current transfer                                            */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint8_t   INT_STATUS;                      /*!< DMA Channel N Interrupt Status                                        */
    
    struct {
      __IO uint8_t   BUS_ERROR  :  1;               /*!< interrupt source. 1: Error detected.(R/WC)                            */
      __IO uint8_t   FLOW_CONTROL:  1;              /*!< Intr source.1=HW Flow Ctrl is requesting                              */
      __IO uint8_t   DONE       :  1;               /*!< intr source. 1= Start Address equals End                              */
    } INT_STATUS_b;                                 /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED2[3];
  
  union {
    __IO uint8_t   INT_EN;                          /*!< DMA CHANNEL N INTERRUPT ENABLE                                        */
    
    struct {
      __IO uint8_t   BUS_ERROR  :  1;               /*!< 1=enable Interrupt:Status AMBA Bus Error.                             */
      __IO uint8_t   FLOW_CONTROL:  1;              /*!< 1=enable Interrupt:Status Flow Control Error.                         */
      __IO uint8_t   DONE       :  1;               /*!< 1=enable Interrupt:Status Done.
                                                                                                                               */
    } INT_EN_b;                                     /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED3[7];
} DMA_CH_Type;


/* ================================================================================ */
/* ================                       PCR                      ================ */
/* ================================================================================ */


/**
  * @brief The Power, Clocks, and Resets (PCR) chapter identifies all the power supplies,
 clock sources, and reset inputs to the chip and defines all the derived power, clock, and reset signals.  (PCR)
  */

typedef struct {                                    /*!< PCR Structure                                                         */
  __IO uint32_t  CHIP_SLP_EN;                       /*!< Chip Sleep Enable Register. (MCHP Reserved)                           */
  __I  uint32_t  CHIP_CLK_REQ_STS;                  /*!< Chip Clock Required Status. (MCHP Reserved)                           */
  
  union {
    __IO uint32_t  EC_SLP_EN;                       /*!< EC Sleep Enable Register (EC_SLP_EN)                                  */
    
    struct {
      __IO uint32_t  INT_SLP_EN :  1;               /*!< INT Sleep Enable (INT_SLP_EN)                                         */
      __IO uint32_t  PECI_SLP_EN:  1;               /*!< PECI Sleep Enable (PECI_SLP_EN)                                       */
      __IO uint32_t  TACH0_SLP_EN:  1;              /*!< TACH0 Sleep Enable (TACH0_SLP_EN)                                     */
           uint32_t             :  1;
      __IO uint32_t  PWM0_SLP_EN:  1;               /*!< PWM0 Sleep Enable (PWM0_SLP_EN)                                       */
      __IO uint32_t  PMC_SLP_EN :  1;               /*!< PMC Sleep Enable (PMC_SLP_EN)                                         */
      __IO uint32_t  DMA_SLP_EN :  1;               /*!< DMA Sleep Enable (DMA_SLP_EN)                                         */
      __IO uint32_t  TFDP_SLP_EN:  1;               /*!< TFDP Sleep Enable (TFDP_SLP_EN)                                       */
      __IO uint32_t  PROCESSOR_SLP_EN:  1;          /*!< PROCESSOR Sleep Enable (PROCESSOR_SLP_EN)                             */
      __IO uint32_t  WDT_SLP_EN :  1;               /*!< WDT Sleep Enable (WDT_SLP_EN)                                         */
      __IO uint32_t  SMB0_SLP_EN:  1;               /*!< SMB0 Sleep Enable (SMB0_SLP_EN)                                       */
      __IO uint32_t  TACH1_SLP_EN:  1;              /*!< TACH1 Sleep Enable (TACH1_SLP_EN)                                     */
           uint32_t             :  8;
      __IO uint32_t  PWM1_SLP_EN:  1;               /*!< PWM1 Sleep Enable (PWM1_SLP_EN)                                       */
      __IO uint32_t  PWM2_SLP_EN:  1;               /*!< PWM2 Sleep Enable (PWM2_SLP_EN)                                       */
      __IO uint32_t  PWM3_SLP_EN:  1;               /*!< PWM3 Sleep Enable (PWM3_SLP_EN)                                       */
           uint32_t             :  6;
      __IO uint32_t  EC_REG_BANK_SLP_EN:  1;        /*!< EC_REG_BANK Sleep Enable (EC_REG_BANK_SLP_EN)                         */
      __IO uint32_t  TIMER16_0_SLP_EN:  1;          /*!< TIMER16_0 Sleep Enable (TIMER16_0_SLP_EN)                             */
      __IO uint32_t  TIMER16_1_SLP_EN:  1;          /*!< TIMER16_1 Sleep Enable (TIMER16_1_SLP_EN)                             */
    } EC_SLP_EN_b;                                  /*!< BitSize                                                               */
  };
  
  union {
    __I  uint32_t  EC_CLK_REQ_STS;                  /*!< EC Clock Required Status Registers                                    */
    
    struct {
      __I  uint32_t  INT_CLK_REQ:  1;               /*!< INT Clock Required (INT_CLK_REQ)                                      */
      __I  uint32_t  PECI_CLK_REQ:  1;              /*!< PECI Clock Required (PECI_CLK_REQ)                                    */
      __I  uint32_t  TACH0_CLK_REQ:  1;             /*!< TACH0 Clock Required (TACH0_CLK_REQ)                                  */
           uint32_t             :  1;
      __I  uint32_t  PWM0_CLK_REQ:  1;              /*!< PWM0 Clock Required (PWM0_CLK_REQ)                                    */
      __I  uint32_t  PMC_CLK_REQ:  1;               /*!< PMC Clock Required (PMC_CLK_REQ)                                      */
      __I  uint32_t  DMA_CLK_REQ:  1;               /*!< DMA Clock Required (DMA_CLK_REQ)                                      */
      __I  uint32_t  TFDP_CLK_REQ:  1;              /*!< TFDP Clock Required (TFDP_CLK_REQ)                                    */
      __I  uint32_t  PROCESSOR_CLK_REQ:  1;         /*!< PROCESSOR Clock Required (PROCESSOR_CLK_REQ)                          */
      __I  uint32_t  WDT_CLK_REQ:  1;               /*!< WDT Clock Required (WDT_CLK_REQ)                                      */
      __I  uint32_t  SMB0_CLK_REQ:  1;              /*!< SMB0 Clock Required (SMB0_CLK_REQ)                                    */
      __I  uint32_t  TACH1_CLK_REQ:  1;             /*!< TACH1 Clock Required (TACH1_CLK_REQ)                                  */
           uint32_t             :  8;
      __I  uint32_t  PWM1_CLK_REQ:  1;              /*!< PWM1 Clock Required (PWM1_CLK_REQ)                                    */
      __I  uint32_t  PWM2_CLK_REQ:  1;              /*!< PWM2 Clock Required (PWM2_CLK_REQ)                                    */
      __I  uint32_t  PWM3_CLK_REQ:  1;              /*!< PWM3 Clock Required (PWM3_CLK_REQ)                                    */
           uint32_t             :  6;
      __I  uint32_t  EC_REG_BANK_CLK_REQ:  1;       /*!< EC_REG_BANK Clock Required (EC_REG_BANK_CLK_REQ)                      */
      __I  uint32_t  TIMER16_0_CLK_REQ:  1;         /*!< TIMER16_0 Clock Required (TIMER16_0_CLK_REQ)                          */
      __I  uint32_t  TIMER16_1_CLK_REQ:  1;         /*!< TIMER16_1 Clock Required (TIMER16_1_CLK_REQ)                          */
    } EC_CLK_REQ_STS_b;                             /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  HOST_SLP_EN;                     /*!< Host Sleep Enable Register (HOST_SLP_EN)                              */
    
    struct {
      __IO uint32_t  LPC_SLP_EN :  1;               /*!< LPC Sleep Enable (LPC_SLP_EN)                                         */
      __IO uint32_t  UART_0_SLP_EN:  1;             /*!< UART 0 Sleep Enable (UART_0_SLP_EN)                                   */
           uint32_t             : 10;
      __IO uint32_t  GLBL_CFG_SLP_EN:  1;           /*!< GLBL_CFG (GLBL_CFG_SLP_EN)                                            */
      __IO uint32_t  ACPI_EC_0_SLP_EN:  1;          /*!< ACPI EC 0 Sleep Enable (ACPI_EC_0_SLP_EN)                             */
      __IO uint32_t  ACPI_EC_1_SLP_EN:  1;          /*!< ACPI EC 1 Sleep Enable (ACPI_EC_1_SLP_EN)                             */
      __IO uint32_t  ACPI_PM1_SLP_EN:  1;           /*!< ACPI PM1 Sleep Enable (ACPI_PM1_SLP_EN)                               */
      __IO uint32_t  KBCEM_SLP_EN:  1;              /*!< 8042EM Sleep Enable (8042EM_SLP_EN)                                   */
           uint32_t             :  1;
      __IO uint32_t  RTC_SLP_EN :  1;               /*!< RTC Sleep Enable (RTC_SLP_EN)                                         */
    } HOST_SLP_EN_b;                                /*!< BitSize                                                               */
  };
  
  union {
    __I  uint32_t  HOST_CLK_REQ;                    /*!< Host Clock Required Status Registers                                  */
    
    struct {
      __I  uint32_t  LPC_CLK_REQ:  1;               /*!< LPC Clock Required (LPC_CLK_REQ)                                      */
      __I  uint32_t  UART_0_CLK_REQ:  1;            /*!< UART 0 Clock Required (UART_0_CLK_REQ)                                */
           uint32_t             : 10;
      __I  uint32_t  GLBL_CFG_CLK_REQ:  1;          /*!< GLBL_CFG Clock Required (GLBL_CFG_CLK_REQ)                            */
      __I  uint32_t  ACPI_EC_0_CLK_REQ:  1;         /*!< ACPI EC 0 Clock Required (ACPI_EC_0_CLK_REQ)                          */
      __I  uint32_t  ACPI_EC_1_CLK_REQ:  1;         /*!< ACPI EC 1 Clock Required (ACPI_EC_1_CLK_REQ)                          */
      __I  uint32_t  ACPI_PM1_CLK_REQ:  1;          /*!< ACPI PM1 Clock Required (ACPI_PM1_CLK_REQ)                            */
      __I  uint32_t  KBCEM_CLK_REQ:  1;             /*!< 8042EM Clock Required (8042EM_CLK_REQ)                                */
           uint32_t             :  1;
      __I  uint32_t  RTC_CLK_REQ:  1;               /*!< RTC Clock Required (RTC_CLK_REQ)                                      */
    } HOST_CLK_REQ_b;                               /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  SYS_SLP_CNTRL;                   /*!< System Sleep Control Register                                         */
    
    struct {
      __IO uint32_t  ROSC_PD    :  1;               /*!< Ring oscillator power down (ROSC_PD)                                  */
      __IO uint32_t  ROSC_GATE  :  1;               /*!< Ring oscillator output gate (ROSC_GATE)                               */
      __IO uint32_t  REGULATOR_STDBY:  1;           /*!< Core regulator standby                                                */
    } SYS_SLP_CNTRL_b;                              /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED;
  __IO uint32_t  PROC_CLK_CNTRL;                    /*!< Processor Clock Control Register (PROC_CLK_CNTRL) [7:0] Processor
                                                         Clock Divide Value (PROC_DIV)
                                                          1: divide 48 MHz Ring Oscillator by 1.
                                                          4: divide 48 MHz Ring Oscillator by 4.(default)
                                                          16: divide 48 MHz Ring Oscillator by 16.
                                                          48: divide 48 MHz Ring Oscillator by 48.
                                                          No other values are supported 
                                                          ---------------------------------------------------------            */
  
  union {
    __IO uint32_t  EC_SLP_EN2;                      /*!< EC Sleep Enable 2 Register (EC_SLP_EN2)                               */
    
    struct {
           uint32_t             :  3;
      __IO uint32_t  ADC_SLP_EN :  1;               /*!< ADC Sleep Enable (ADC_SLP_EN)                                         */
           uint32_t             :  1;
      __IO uint32_t  PS2_0_SLP_EN:  1;              /*!< PS2_0 Sleep Enable (PS2_0_SLP_EN)                                     */
      __IO uint32_t  PS2_1_SLP_EN:  1;              /*!< PS2_1 Sleep Enable (PS2_1_SLP_EN)                                     */
      __IO uint32_t  PS2_2_SLP_EN:  1;              /*!< PS2_2 Sleep Enable (PS2_2_SLP_EN)                                     */
      __IO uint32_t  PS2_3_SLP_EN:  1;              /*!< PS2_3 Sleep Enable (PS2_3_SLP_EN)                                     */
      __IO uint32_t  SPI0_SLP_EN:  1;               /*!< SPI0 Sleep Enable (SPI0_SLP_EN)                                       */
      __IO uint32_t  HTIMER_SLP_EN:  1;             /*!< HTIMER Sleep Enable (HTIMER_SLP_EN)                                   */
      __IO uint32_t  KEYSCAN_SLP_EN:  1;            /*!< KEYSCAN Sleep Enable (KEYSCAN_SLP_EN)                                 */
      __IO uint32_t  RPMPWM_SLP_EN:  1;             /*!< RPM-PWM Sleep Enable (RPMPWM_SLP_EN)                                  */
      __IO uint32_t  SMB1_SLP_EN:  1;               /*!< SMB1 Sleep Enable (SMB1_SLP_EN)                                       */
      __IO uint32_t  SMB2_SLP_EN:  1;               /*!< SMB2 Sleep Enable (SMB2_SLP_EN)                                       */
      __IO uint32_t  SMB3_SLP_EN:  1;               /*!< SMB3 Sleep Enable (SMB3_SLP_EN)                                       */
      __IO uint32_t  LED0_SLP_EN:  1;               /*!< LED0 Sleep Enable (LED0_SLP_EN)                                       */
      __IO uint32_t  LED1_SLP_EN:  1;               /*!< LED1 Sleep Enable (LED1_SLP_EN)                                       */
      __IO uint32_t  LED2_SLP_EN:  1;               /*!< LED2 Sleep Enable (LED2_SLP_EN)                                       */
      __IO uint32_t  BCM_SLP_EN :  1;               /*!< BCM Sleep Enable (BCM_SLP_EN)                                         */
      __IO uint32_t  SPI1_SLP_EN:  1;               /*!< SPI1 Sleep Enable (SPI1_SLP_EN)                                       */
      __IO uint32_t  TIMER16_2_SLP_EN:  1;          /*!< TIMER16_2_Sleep Enable (TIMER16_2_SLP_EN)                             */
      __IO uint32_t  TIMER16_3_SLP_EN:  1;          /*!< TIMER16_3 Sleep Enable (TIMER16_3_SLP_EN)                             */
      __IO uint32_t  TIMER32_0_SLP_EN:  1;          /*!< TIMER32_0 Sleep Enable (TIMER32_0_SLP_EN)                             */
      __IO uint32_t  TIMER32_1_SLP_EN:  1;          /*!< TIMER32_1 Sleep Enable (TIMER32_1_SLP_EN)                             */
      __IO uint32_t  LED3_SLP_EN:  1;               /*!< LED3 Sleep Enable (LED3_SLP_EN)                                       */
    } EC_SLP_EN2_b;                                 /*!< BitSize                                                               */
  };
  
  union {
    __I  uint32_t  EC_CLK_REQ2_STS;                 /*!< EC Clock Required 2 Status Register                                   */
    
    struct {
           uint32_t             :  3;
      __I  uint32_t  ADC_CLK_REQ:  1;               /*!< ADC Clock Required (ADC_CLK_REQ)                                      */
           uint32_t             :  1;
      __I  uint32_t  PS2_0_SLP_CLK_REQ:  1;         /*!< PS2_0 Clock Required (PS2_0_SLP_CLK_REQ)                              */
      __I  uint32_t  PS2_1_SLP_CLK_REQ:  1;         /*!< PS2_1 Clock Required (PS2_1_SLP_CLK_REQ)                              */
      __I  uint32_t  PS2_2_SLP_CLK_REQ:  1;         /*!< PS2_2 Clock Required (PS2_2_SLP_CLK_REQ)                              */
      __I  uint32_t  PS2_3_SLP_CLK_REQ:  1;         /*!< PS2_3 Clock Required (PS2_3_SLP_CLK_REQ)                              */
      __I  uint32_t  SPI0_SLP_CLK_REQ:  1;          /*!< SPI0 Clock Required (SPI0_SLP_CLK_REQ)                                */
      __I  uint32_t  HTIMER_SLP_CLK_REQ:  1;        /*!< HTIMER Clock Required (HTIMER_SLP_CLK_REQ)                            */
      __I  uint32_t  KEYSCAN_SLP_CLK_REQ:  1;       /*!< KEYSCAN Clock Required (KEYSCAN_SLP_CLK_REQ)                          */
      __I  uint32_t  RPMPWM_SLP_CLK_REQ:  1;        /*!< RPM-PWM Clock Required (RPMPWM_SLP_CLK_REQ)                           */
      __I  uint32_t  SMB1_SLP_CLK_REQ:  1;          /*!< SMB1 Clock Required (SMB1_SLP_CLK_REQ)                                */
      __I  uint32_t  SMB2_SLP_CLK_REQ:  1;          /*!< SMB2 Clock Required (SMB2_SLP_CLK_REQ)                                */
      __I  uint32_t  SMB3_SLP_CLK_REQ:  1;          /*!< SMB3 Clock Required (SMB3_SLP_CLK_REQ)                                */
      __I  uint32_t  LED0_SLP_CLK_REQ:  1;          /*!< LED0 Clock Required (LED0_SLP_CLK_REQ)                                */
      __I  uint32_t  LED1_SLP_CLK_REQ:  1;          /*!< LED1 Clock Required (LED1_SLP_CLK_REQ)                                */
      __I  uint32_t  LED2_SLP_CLK_REQ:  1;          /*!< LED2 Clock Required (LED2_SLP_CLK_REQ)                                */
      __I  uint32_t  BCM_SLP_CLK_REQ:  1;           /*!< BCM Clock Required (BCM_SLP_CLK_REQ)                                  */
      __I  uint32_t  SPI1_SLP_CLK_REQ:  1;          /*!< SPI1 Clock Required (SPI1_SLP_CLK_REQ)                                */
      __I  uint32_t  TIMER16_2_SLP_CLK_REQ:  1;     /*!< TIMER16_2_Clock Required (TIMER16_2_SLP_CLK_REQ)                      */
      __I  uint32_t  TIMER16_3_SLP_CLK_REQ:  1;     /*!< TIMER16_3 Clock Required (TIMER16_3_SLP_CLK_REQ)                      */
      __I  uint32_t  TIMER32_0_SLP_CLK_REQ:  1;     /*!< TIMER32_0 Clock Required (TIMER32_0_SLP_CLK_REQ)                      */
      __I  uint32_t  TIMER32_1_SLP_CLK_REQ:  1;     /*!< TIMER32_1 Clock Required (TIMER32_1_SLP_CLK_REQ)                      */
      __I  uint32_t  LED3_SLP_CLK_REQ:  1;          /*!< LED3 Clock Required (LED3_SLP_CLK_REQ)                                */
    } EC_CLK_REQ2_STS_b;                            /*!< BitSize                                                               */
  };
  __IO uint32_t  SLOW_CLK_CNTRL;                    /*!< Slow Clock Control Register (SLOW_CLK_CNTRL) Slow Clock (100
                                                         kHz) Divide Value (slow_div) Configures the 100kHz_Clk.
                                                          0: Clock off 
                                                          n: divide by n.
                                                          Note: The default setting is for 100 kHz. 
                                                          ---------------------------------------------------------            */
  
  union {
    __I  uint32_t  CHIP_OSC_ID;                     /*!< Oscillator ID Register (CHIP_OSC_ID)                                  */
    
    struct {
           uint32_t             :  8;
      __I  uint32_t  OSC_LOCK   :  1;               /*!< OSC_LOCK (OSC_LOCK)                                                   */
    } CHIP_OSC_ID_b;                                /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  CHIP_PWR_RST_STS;                /*!< PCR chip sub-system power reset status                                */
    
    struct {
           uint32_t             :  2;
      __I  uint32_t  VCC_nRST   :  1;               /*!< 0=active, 1=not active (PWRGD asserted).                              */
      __I  uint32_t  SIO_nRST   :  1;               /*!< nSIO_RESET. 0=active, 1=not active.                                   */
           uint32_t             :  1;
      __IO uint32_t  VBAT_RST   :  1;               /*!< VBAT: 0=No reset, 1=reset occurred.(R/WC)                             */
      __IO uint32_t  VCC1_RST   :  1;               /*!< VCC1: 0=No reset, 1=reset occurred.(R/WC)                             */
           uint32_t             :  3;
      __I  uint32_t  _32K_ACTIVE:  1;               /*!< 32K_ACTIVE (32K_ACTIVE)                                               */
      __I  uint32_t  PCICLK_ACTIVE:  1;             /*!< PCICLK_ACTIVE (PCICLK_ACTIVE)                                         */
    } CHIP_PWR_RST_STS_b;                           /*!< BitSize                                                               */
  };
  __IO uint32_t  CHIP_RST_EN;                       /*!< Chip Reset Enable (MCHP Reserved)                                     */
  
  union {
    __IO uint32_t  HOST_RST_EN;                     /*!< Host Reset Enable Register                                            */
    
    struct {
      __IO uint32_t  LPC_RST_EN :  1;               /*!< LPC Reset Enable (LPC_RST_EN)                                         */
      __IO uint32_t  UART_0_RST_EN:  1;             /*!< UART 0 Reset Enable                                                   */
           uint32_t             : 10;
      __IO uint32_t  GLBL_CFG_RST_EN:  1;           /*!< GLBL_CFG Reset Enable                                                 */
      __IO uint32_t  ACPI_EC_0_RST_EN:  1;          /*!< ACPI EC 0 Reset Enable                                                */
      __IO uint32_t  ACPI_EC_1_RST_EN:  1;          /*!< ACPI EC 1 Reset Enable                                                */
      __IO uint32_t  ACPI_PM1_RST_EN:  1;           /*!< ACPI PM1 Reset Enable                                                 */
      __IO uint32_t  KBCEM_RST_EN:  1;              /*!< 8042EM Reset Enable                                                   */
           uint32_t             :  1;
      __IO uint32_t  RTC_RST_EN :  1;               /*!< RTC Reset Enable (RTC_RST_EN)                                         */
    } HOST_RST_EN_b;                                /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  EC_RST_EN;                       /*!< EC Reset Enable Register                                              */
    
    struct {
      __IO uint32_t  INT_RST_EN :  1;               /*!< INT Reset Enable (INT_RST_EN)                                         */
      __IO uint32_t  PECI_RST_EN:  1;               /*!< PECI Reset Enable (PECI_RST_EN)                                       */
      __IO uint32_t  TACH0_RST_EN:  1;              /*!< TACH0 Reset Enable (TACH0_RST_EN)                                     */
           uint32_t             :  1;
      __IO uint32_t  PWM0_RST_EN:  1;               /*!< PWM0 Reset Enable (PWM0_RST_EN)                                       */
      __IO uint32_t  PMC_RST_EN :  1;               /*!< PMC Reset Enable (PMC_RST_EN)                                         */
      __IO uint32_t  DMA_RST_EN :  1;               /*!< DMA Reset Enable (DMA_RST_EN)                                         */
      __IO uint32_t  TFDP_RST_EN:  1;               /*!< TFDP Reset Enable (TFDP_RST_EN)                                       */
      __IO uint32_t  PROCESSOR_RST_EN:  1;          /*!< PROCESSOR Sleep Enable (PROCESSOR_RST_EN)                             */
      __IO uint32_t  WDT_RST_EN :  1;               /*!< WDT Reset Enable (WDT_RST_EN)                                         */
      __IO uint32_t  SMB0_RST_EN:  1;               /*!< SMB0 Reset Enable (SMB0_RST_EN)                                       */
      __IO uint32_t  TACH1_RST_EN:  1;              /*!< TACH1 Reset Enable (TACH1_RST_EN)                                     */
           uint32_t             :  8;
      __IO uint32_t  PWM1_RST_EN:  1;               /*!< PWM1 Reset Enable (PWM1_RST_EN)                                       */
      __IO uint32_t  PWM2_RST_EN:  1;               /*!< PWM2 Reset Enable (PWM2_RST_EN)                                       */
      __IO uint32_t  PWM3_RST_EN:  1;               /*!< PWM3 Reset Enable (PWM3_RST_EN)                                       */
           uint32_t             :  6;
      __IO uint32_t  EC_REG_BANK_RST_EN:  1;        /*!< EC_REG_BANK Reset Enable (EC_REG_BANK_RST_EN)                         */
      __IO uint32_t  TIMER16_0_RST_EN:  1;          /*!< TIMER16_0 Reset Enable (TIMER16_0_RST_EN)                             */
      __IO uint32_t  TIMER16_1_RST_EN:  1;          /*!< TIMER16_1 Reset Enable (TIMER16_1_RST_EN)                             */
    } EC_RST_EN_b;                                  /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  EC_RST_EN2;                      /*!< EC Reset Enable 2 Register                                            */
    
    struct {
           uint32_t             :  3;
      __IO uint32_t  ADC_RST_EN :  1;               /*!< ADC Reset Enable (ADC_RST_EN)                                         */
           uint32_t             :  1;
      __IO uint32_t  PS2_0_RST_EN:  1;              /*!< PS2_0 Reset Enable (PS2_0_RST_EN)                                     */
      __IO uint32_t  PS2_1_RST_EN:  1;              /*!< PS2_1 Reset Enable (PS2_1_RST_EN)                                     */
      __IO uint32_t  PS2_2_RST_EN:  1;              /*!< PS2_2 Reset Enable (PS2_2_RST_EN)                                     */
      __IO uint32_t  PS2_3_RST_EN:  1;              /*!< PS2_3 Reset Enable (PS2_3_RST_EN)                                     */
      __IO uint32_t  SPI0_SLP_EN:  1;               /*!< SPI0 Reset Enable (SPI0_SLP_EN)                                       */
      __IO uint32_t  HTIMER_RST_EN:  1;             /*!< HTIMER Reset Enable (HTIMER_RST_EN)                                   */
      __IO uint32_t  KEYSCAN_RST_EN:  1;            /*!< KEYSCAN Reset Enable (KEYSCAN_RST_EN)                                 */
      __IO uint32_t  RPMPWM_RST_EN:  1;             /*!< RPM-PWM Reset Enable (RPMPWM_RST_EN)                                  */
      __IO uint32_t  SMB1_RST_EN:  1;               /*!< SMB1 Reset Enable (SMB1_RST_EN)                                       */
      __IO uint32_t  SMB2_RST_EN:  1;               /*!< SMB2 Reset Enable (SMB2_RST_EN)                                       */
      __IO uint32_t  SMB3_RST_EN:  1;               /*!< SMB3 Reset Enable (SMB3_RST_EN)                                       */
      __IO uint32_t  LED0_RST_EN:  1;               /*!< LED0 Reset Enable (LED0_RST_EN)                                       */
      __IO uint32_t  LED1_RST_EN:  1;               /*!< LED1 Reset Enable (LED1_RST_EN)                                       */
      __IO uint32_t  LED2_RST_EN:  1;               /*!< LED2 Reset Enable (LED2_RST_EN)                                       */
      __IO uint32_t  BCM_RST_EN :  1;               /*!< BCM Reset Enable (BCM_RST_EN)                                         */
      __IO uint32_t  SPI1_RST_EN:  1;               /*!< SPI1 Reset Enable (SPI1_RST_EN)                                       */
      __IO uint32_t  TIMER16_2_RST_EN:  1;          /*!< TIMER16_2_Reset Enable (TIMER16_2_RST_EN)                             */
      __IO uint32_t  TIMER16_3_RST_EN:  1;          /*!< TIMER16_3 Reset Enable (TIMER16_3_RST_EN)                             */
      __IO uint32_t  TIMER32_0_RST_EN:  1;          /*!< TIMER32_0 Reset Enable (TIMER32_0_RST_EN)                             */
      __IO uint32_t  TIMER32_1_RST_EN:  1;          /*!< TIMER32_1 Reset Enable (TIMER32_1_RST_EN)                             */
      __IO uint32_t  LED3_RST_EN:  1;               /*!< LED3 Reset Enable (LED3_RST_EN)                                       */
    } EC_RST_EN2_b;                                 /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  PWR_RST_CTRL;                    /*!< Power Reset Control (PWR_RST_CTRL) Register                           */
    
    struct {
      __IO uint32_t  IRESET_OUT :  1;               /*!< iRESET_OUT (IRESET_OUT)                                               */
    } PWR_RST_CTRL_b;                               /*!< BitSize                                                               */
  };
} PCR_Type;


/* ================================================================================ */
/* ================                      VBAT                      ================ */
/* ================================================================================ */


/**
  * @brief The VBAT Register Bank block is a block implemented for aggregating miscellaneous battery-backed registers 
 required the host and by the Embedded Controller (EC) Subsystem that are not unique to a block implemented in the EC subsystem.
 The VBAT Powered RAM provides a 64 Byte Random Accessed Memory that is operational while the main power rail is operational, 
 and will retain its values powered by battery power while the main rail is unpowered.  (VBAT)
  */

typedef struct {                                    /*!< VBAT Structure                                                        */
  
  union {
    __IO uint8_t   PFR_STS;                         /*!< Power-Fail and Reset Status Register                                  */
    
    struct {
      __I  uint8_t   DET32K_IN  :  1;               /*!< XTAL[1:2] 0=No clock, 1= Clock detected                               */
           uint8_t              :  4;
      __IO uint8_t   WDT        :  1;               /*!< 1=Watch-Dog Timer Forced Reset (R/WC).                                */
           uint8_t              :  1;
      __IO uint8_t   VBAT_RST   :  1;               /*!< 1=VBAT_POR is detected.(R/WC)                                         */
    } PFR_STS_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED[7];
  
  union {
    __IO uint32_t  CLOCK_EN;                        /*!< CLOCK ENABLE Control                                                  */
    
    struct {
      __IO uint32_t  XOSEL      :  1;               /*!< 32KHz, 1=single-ended, 0=crystal (default).                           */
      __IO uint32_t  _32K_EN    :  1;               /*!< 1=32K_ON, 0=OFF (VBAT_POR default)                                    */
    } CLOCK_EN_b;                                   /*!< BitSize                                                               */
  };
} VBAT_Type;


/* ================================================================================ */
/* ================                       LPC                      ================ */
/* ================================================================================ */


/**
  * @brief Section 5.10, "EC-Only Registers"and Section 5.11, "Runtime Registers".  (LPC)
  */

typedef struct {                                    /*!< LPC Structure                                                         */
  __IO uint8_t   INDEX;                             /*!< A pointer to a Configuration Reg. Address.                            */
  __IO uint8_t   DATA_REG;                          /*!< To rd/wt data with the INDEX Register.                                */
  __I  uint16_t  RESERVED[129];
  
  union {
    __I  uint32_t  BUS_MONITOR;                     /*!< LPC BUS MONITOR REGISTER                                              */
    
    struct {
           uint32_t             :  1;
      __I  uint32_t  LRESET_STATUS:  1;             /*!< Reflects the inverse state of LRESET# pin.                            */
    } BUS_MONITOR_b;                                /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  HOST_BUS_ERROR;                  /*!< Host Bus Error Register                                               */
    
    struct {
      __IO uint32_t  LPC_ERR    :  1;               /*!< A BAR conflict or an internal bus error. (R/WC)                       */
      __IO uint32_t  EN_ERR     :  1;               /*!< Internal bus errors. (R/WC)                                           */
      __IO uint32_t  BAR_ERR    :  1;               /*!< a BAR conflict occurs on an LPC address. (R/WC)                       */
      __IO uint32_t  RUNTIME_ERR:  1;               /*!< A BAR is misconfigured. (R/WC)                                        */
      __IO uint32_t  CONFIG_ERR :  1;               /*!< LPC Config access causes a bus error.(R/WC)                           */
      __IO uint32_t  DMA_ERR    :  1;               /*!< LPC DMA access causes a bus error. (R/WC)                             */
           uint32_t             :  2;
      __I  uint32_t  ERR_ADDR   : 24;               /*!< 24-bit internal addr. of LPC transaction                              */
    } HOST_BUS_ERROR_b;                             /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  EC_SERIRQ;                       /*!< the interrupt source of EC SERIRQ                                     */
    
    struct {
      __IO uint32_t  EC_IRQ     :  1;               /*!< interrupt source of a LPC Logical Device                              */
    } EC_SERIRQ_b;                                  /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  CLK_CTRL;                        /*!< Controls throughput of LPC transactions.                              */
    
    struct {
      __IO uint32_t  CR         :  2;               /*!< controls ring oscillator to be shut down.                             */
      __IO uint32_t  HANDSHAKE  :  1;               /*!< controls throughput of LPC transactions.                              */
    } CLK_CTRL_b;                                   /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED1[3];
  __IO uint32_t  BAR_INHIBIT;                       /*!< The BAR for Logical Device i is disabled                              */
  __I  uint32_t  RESERVED2[3];
  __IO uint32_t  BAR_INIT;                          /*!< Init value of LPC BAR at offset 60h on nSIO_RESET.                    */
} LPC_Type;


/* ================================================================================ */
/* ================                   LPC_CONFIG                   ================ */
/* ================================================================================ */


/**
  * @brief LPC Configuration Registers. See Section 5.9  (LPC_CONFIG)
  */

typedef struct {                                    /*!< LPC_CONFIG Structure                                                  */
  __I  uint32_t  RESERVED[12];
  __IO uint8_t   ACTIVATE;                          /*!< 1=LPC Logical Device is powered/functional                            */
  __I  uint8_t   RESERVED1[15];
  
  union {
    __IO uint8_t   SIRQ[16];                        /*!< 16 SIRQ channels                                                      */
    
    struct {
      __IO uint8_t   FRAME      :  6;               /*!< Six bits select the Logical Device.                                   */
      __IO uint8_t   DEVICE     :  1;               /*!< Set to 0 in order to enable a SERIRQ.                                 */
      __IO uint8_t   SELECT     :  1;               /*!< 1: 1st LD's intr is selected,0: 2nd intr.                             */
    } SIRQ_b[16];                                   /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED2[4];
  
  union {
    __IO uint32_t  LPC_BAR;                         /*!< LPC Interface BAR Register                                            */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } LPC_BAR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  EM_BAR;                          /*!< EM Interface 0 BAR                                                    */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } EM_BAR_b;                                     /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  UART_BAR;                        /*!< UART 0 BAR Register                                                   */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } UART_BAR_b;                                   /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED3[3];
  
  union {
    __IO uint32_t  KBC_BAR;                         /*!< Keyboard Controller (8042) BAR                                        */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } KBC_BAR_b;                                    /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED4[3];
  
  union {
    __IO uint32_t  EC0_BAR;                         /*!< ACPI EC Interface 0 BAR                                               */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } EC0_BAR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  EC1_BAR;                         /*!< ACPI EC Interface 1 BAR                                               */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } EC1_BAR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  PM1_BAR;                         /*!< ACPI PM1 Interface BAR                                                */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } PM1_BAR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  LGC_BAR;                         /*!< Legacy (GATEA20) Interface BAR                                        */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } LGC_BAR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  MBX_BAR;                         /*!< Mailbox Registers Interface BAR                                       */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } MBX_BAR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  RTC_BAR;                         /*!< RTC Registers Interface BAR                                           */
    
    struct {
      __IO uint32_t  MASK       :  8;               /*!< Mask off LPC I/O address bits                                         */
      __IO uint32_t  FRAME      :  6;               /*!< Specify a logical device frame number                                 */
      __IO uint32_t  DEVICE     :  1;               /*!< combined w FRAME Logical Device Number.                               */
      __IO uint32_t  VALID      :  1;               /*!< 1=the BAR is valid, 0= BAR is ignored                                 */
      __IO uint32_t  LPC_HOST_ADDR: 16;             /*!< To match LPC I/O addresses                                            */
    } RTC_BAR_b;                                    /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED5[8];
  
  union {
    LPC_CONFIG_MEM_BAR_Type MBX_MEM_BAR;            /*!< Mailbox Registers I/F Memory BAR                                      */
    LPC_CONFIG_MEM_BAR_Type MEM_BAR;                /*!< Mailbox Registers I/F Memory BAR                                      */
  };
  LPC_CONFIG_MEM_BAR_Type EC0_MEM_BAR;              /*!< ACPI EC Interface 0 Memory BAR                                        */
  LPC_CONFIG_MEM_BAR_Type EC1_MEM_BAR;              /*!< ACPI EC Interface 1 Memory BAR                                        */
  LPC_CONFIG_MEM_BAR_Type EMI_MEM_BAR;              /*!< EM Interface 0 Memory BAR                                             */
} LPC_CONFIG_Type;


/* ================================================================================ */
/* ================                       GCR                      ================ */
/* ================================================================================ */


/**
  * @brief The Logical Device Configuration registers support motherboard designs in which the resources required 
 by their components are known and assigned by the BIOS at POST.  (GCR)
  */

typedef struct {                                    /*!< GCR Structure                                                         */
  __I  uint8_t   RESERVED[7];
  __IO uint8_t   LOGICAL_DEVICE_NUMBER;             /*!< Selects the current logical device.                                   */
  __I  uint32_t  RESERVED1[6];
  __I  uint8_t   DEVICE_ID;                         /*!< provides device identification.                                       */
  __I  uint8_t   DEVICE_REVISION;                   /*!< provides device revision information.                                 */
} GCR_Type;


/* ================================================================================ */
/* ================                       EMI                      ================ */
/* ================================================================================ */


/**
  * @brief The Embedded Memory Interface (EMI) provides a standard run-time mechanism for the system host 
 to communicate with the Embedded Controller (EC) and other logical components.  (EMI)
  */

typedef struct {                                    /*!< EMI Structure                                                         */
  __IO uint8_t   HOST_EC_MBX;                       /*!< Host-to-EC Mailbox Register                                           */
  __IO uint8_t   EC_HOST_MBX;                       /*!< EC-to-Host Mailbox Register (R/WC)                                    */
  
  union {
    __IO uint16_t  EC_ADDRESS;                      /*!< EC Address Access Control Register                                    */
    
    struct {
      __IO uint16_t  ACCESS_TYPE:  2;               /*!< defines the type of EC Data rd/wt access                              */
      __IO uint16_t  EC_ADDRESS : 13;               /*!< defines bits[14:2] of EC_Address [15:0].                              */
      __IO uint16_t  REGION     :  1;               /*!< Selector of two segments.                                             */
    } EC_ADDRESS_b;                                 /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  EC_DATA;                         /*!< EC Data Register                                                      */
    __IO uint8_t   EC_DATA_BYTE[4];                 /*!< EC Data Byte Register                                                 */
  };
  
  union {
    __IO uint16_t  EC_SWI;                          /*!< Notification of EC Software Interrupt                                 */
    
    struct {
      __I  uint16_t  EC_WR      :  1;               /*!< EC Mailbox Write.                                                     */
      __IO uint16_t  NOTIFICATION: 15;              /*!< EC to notify the host of an event(R/WC)                               */
    } EC_SWI_b;                                     /*!< BitSize                                                               */
  };
  __IO uint16_t  EC_SWI_EN;                         /*!< [15:1] enables generation of Event interrupts                         */
  __IO uint8_t   APPLICATION_ID;                    /*!< Application ID Register                                               */
  __I  uint8_t   RESERVED[243];
  __IO uint8_t   HOST2EC_MBX;                       /*!< Host-to-EC Mailbox Register(R/WC)                                     */
  __IO uint8_t   EC2HOST_MBX;                       /*!< EC-to-Host Mailbox Register                                           */
  __I  uint16_t  RESERVED1;
  __IO uint32_t  MEMORY_BASE_ADDRESS_0;             /*!< [31:2] defines the beginning of region 0                              */
  __IO uint16_t  MEMORY_READ_LIMIT_0;               /*!< [14:2]Memory Read Limit 0 Register                                    */
  __IO uint16_t  MEMORY_WRITE_LIMIT_0;              /*!< [14:2] Memory Write Limit 0 Register                                  */
  __IO uint32_t  MEMORY_BASE_ADDRESS_1;             /*!< [31:2] defines the beginning of region 1                              */
  __IO uint16_t  MEMORY_READ_LIMIT_1;               /*!< [14:2]Memory Read Limit 1 Register                                    */
  __IO uint16_t  MEMORY_WRITE_LIMIT_1;              /*!< [14:2] Memory Write Limit 1 Register                                  */
  __IO uint16_t  EC_SWI_SET;                        /*!< [15:1] Interrupt Set Register                                         */
  __IO uint16_t  EC_SWI_CLR;                        /*!< [15:1] Host Clear Enable Register                                     */
} EMI_Type;


/* ================================================================================ */
/* ================                    ACPI_EC0                    ================ */
/* ================================================================================ */


/**
  * @brief The ACPI Embedded Controller Interface (ACPI-ECI) provides a four byte full duplex data interface 
 which is a superset of the standard ACPI Embedded Controller Interface (ACPI-ECI) one byte data interface. The
 ACPI Embedded Controller Interface (ACPI-ECI) defaults to the standard one byte interface.  (ACPI_EC0)
  */

typedef struct {                                    /*!< ACPI_EC0 Structure                                                    */
  
  union {
    __IO uint32_t  OS_DATA;                         /*!< ACPI OS Data Register                                                 */
    __IO uint8_t   OS_DATA_BYTE[4];                 /*!< aliased to the OS2EC DATA BYTES[n].                                   */
  };
  
  union {
    union {
      __I  uint8_t   OS_STATUS;                     /*!< aliased to the EC STATUS Register                                     */
      
      struct {
        __I  uint8_t   OBF      :  1;               /*!< Output Buffer Full bit                                                */
        __I  uint8_t   IBF      :  1;               /*!< Input Buffer Full bit                                                 */
        __I  uint8_t   UD1B     :  1;               /*!< User Defined                                                          */
        __I  uint8_t   CMD      :  1;               /*!< OS2EC Data contains a command byte                                    */
        __I  uint8_t   BURST    :  1;               /*!< set when the ACPI_EC is in Burst Mode                                 */
        __I  uint8_t   SCI_EVT  :  1;               /*!< set when an SCI event is pending                                      */
        __I  uint8_t   SMI_EVT  :  1;               /*!< set when an SMI event is pending                                      */
        __I  uint8_t   UD0B     :  1;               /*!< User Defined                                                          */
      } OS_STATUS_b;                                /*!< BitSize                                                               */
    };
    __O  uint8_t   OS_COMMAND;                      /*!< aliased to the OS2EC Data Byte0                                       */
  };
  __I  uint8_t   OS_BYTE_CONTROL;                   /*!< OS Control [0:0] FOUR_BYTE_ACCESS                                     */
  __I  uint16_t  RESERVED[125];
  
  union {
    __IO uint32_t  EC2OS_DATA;                      /*!< EC2OS Data                                                            */
    __IO uint8_t   EC2OS_DATA_BYTE[4];              /*!< EC2OS Data Bytes                                                      */
  };
  
  union {
    __IO uint8_t   EC_STATUS;                       /*!< EC STATUS                                                             */
    
    struct {
      __I  uint8_t   OBF        :  1;               /*!< Output Buffer Full bit                                                */
      __I  uint8_t   IBF        :  1;               /*!< Input Buffer Full bit                                                 */
      __IO uint8_t   UD1A       :  1;               /*!< User Defined                                                          */
      __I  uint8_t   CMD        :  1;               /*!< OS2EC Data contains a command byte                                    */
      __IO uint8_t   BURST      :  1;               /*!< set when the ACPI_EC is in Burst Mode                                 */
      __IO uint8_t   SCI_EVT    :  1;               /*!< set when an SCI event is pending                                      */
      __IO uint8_t   SMI_EVT    :  1;               /*!< set when an SMI event is pending                                      */
      __IO uint8_t   UD0A       :  1;               /*!< User Defined                                                          */
    } EC_STATUS_b;                                  /*!< BitSize                                                               */
  };
  __IO uint8_t   EC_BYTE_CONTROL;                   /*!< OS Control [0:0] FOUR_BYTE_ACCESS                                     */
  __I  uint16_t  RESERVED1;
  
  union {
    __I uint32_t  OS2EC_DATA;                       /*!< OS2EC Data EC-Register                                                */
    __I uint8_t   OS2EC_DATA_BYTE[4];               /*!< OS2EC Data Bytes                                                      */
  };
} ACPI_EC0_Type;


/* ================================================================================ */
/* ================                       KBC                      ================ */
/* ================================================================================ */


/**
  * @brief The CEC1302 keyboard controller uses the EC to produce a superset of the
 features provided by the industry-standard 8042 keyboard controller. The 8042 Emulated
 Keyboard Controller is a Host/EC Message Interface with hardware assists to emulate 8042
 behavior and provide Legacy GATEA20 support.  (KBC)
  */

typedef struct {                                    /*!< KBC Structure                                                         */
  
  union {
    __O  uint8_t   WT_PORT60_DATA;                  /*!< Host_EC Data Register (=Host Write 60h)                               */
    __I  uint8_t   RD_PORT60_DATA;                  /*!< EC_Host Data/Aux Register (=Host Read 60h)                            */
  };
  __I  uint8_t   RESERVED[3];
  
  union {
    union {
      __I  uint8_t   RD_PORT64_STATUS;              /*!< Keyboard Status Register (=Host Read 64h)                             */
      
      struct {
        __I  uint8_t   OBF      :  1;               /*!< Output Buffer Full.                                                   */
        __I  uint8_t   IBF      :  1;               /*!< Input Buffer Full.                                                    */
        __I  uint8_t   UD0      :  1;               /*!< User-defined data.                                                    */
        __I  uint8_t   CMDnDATA :  1;               /*!< data register contains data(0) or command(1)                          */
        __I  uint8_t   UD1      :  1;               /*!< User-defined data.                                                    */
        __I  uint8_t   AUXOBF   :  1;               /*!< Auxiliary Output Buffer Full.                                         */
        __I  uint8_t   UD2      :  2;               /*!< User-defined data.                                                    */
      } RD_PORT64_STATUS_b;                         /*!< BitSize                                                               */
    };
    __O  uint8_t   WT_PORT64_CMD;                   /*!< Host_EC Command Register (=Host Write 64h)                            */
  };
  __I  uint8_t   RESERVED1[251];
  
  union {
    __O  uint8_t   EC_DATA;                         /*!< EC2Host Data Register                                                 */
    __I  uint8_t   HOST2EC_DATA;                    /*!< Host2EC Data/Cmd Register                                             */
  };
  __I  uint8_t   RESERVED2[3];
  
  union {
    __IO uint8_t   STATUS;                          /*!< EC KEYBOARD STATUS REGISTER                                           */
    
    struct {
      __I  uint8_t   OBF        :  1;               /*!< Output Buffer Full.                                                   */
      __I  uint8_t   IBF        :  1;               /*!< Input Buffer Full.                                                    */
      __IO uint8_t   UD0        :  1;               /*!< User-defined data.                                                    */
      __I  uint8_t   CMDnDATA   :  1;               /*!< data register contains data(0) or command(1)                          */
      __IO uint8_t   UD1        :  1;               /*!< User-defined data.                                                    */
      __I  uint8_t   AUXOBF     :  1;               /*!< Auxiliary Output Buffer Full.                                         */
      __IO uint8_t   UD2        :  2;               /*!< User-defined data.                                                    */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED3[3];
  
  union {
    __IO uint8_t   CONTROL;                         /*!< Keyboard Control Register                                             */
    
    struct {
      __IO uint8_t   UD3        :  1;               /*!< User-defined data.                                                    */
      __IO uint8_t   SAEN       :  1;               /*!< Software-assist enable.                                               */
      __IO uint8_t   PCOBFEN    :  1;               /*!< 1=write to PCOBF, 0=writes to EC Data Reg.                            */
      __IO uint8_t   UD4        :  2;               /*!< User-defined data.                                                    */
      __IO uint8_t   OBFEN      :  1;               /*!< 1=KIRQ is driven by PCOBF and MIRQ                                    */
      __IO uint8_t   UD5        :  1;               /*!< User-defined data.                                                    */
      __IO uint8_t   AUXH       :  1;               /*!< AUX in Hardware.                                                      */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED4[3];
  __O  uint8_t   AUX_DATA;                          /*!< EC_Host Aux Register                                                  */
  __I  uint8_t   RESERVED5[7];
  __IO uint8_t   PCOBF;                             /*!< [0:0] PCOBF Register                                                  */
  __I  uint8_t   RESERVED6[539];
  __IO uint8_t   ACTIVATE;                          /*!< [0:0] 1=8042 I/F is powered/functional                                */
} KBC_Type;


/* ================================================================================ */
/* ================                     PORT92                     ================ */
/* ================================================================================ */


/**
  * @brief The registers listed in the Configuration Register Summary table are for a 
 single instance of the Legacy Port92 and GATEA20 logic.  (PORT92)
  */

typedef struct {                                    /*!< PORT92 Structure                                                      */
  
  union {
    __IO uint8_t   PORT92;                          /*!< Support GATE_A20 CPU_RESET control                                    */
    
    struct {
      __IO uint8_t   ALT_CPU_RESET:  1;             /*!< provides to generate a CPU_RESET pulse.                               */
      __IO uint8_t   ALT_GATE_A20:  1;              /*!< provides system to control GATEA20 pin.                               */
    } PORT92_b;                                     /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED[255];
  __IO uint8_t   GATEA20;                           /*!< [0:0] 0=GATEA20 output low, 1=outputn high                            */
  __I  uint8_t   RESERVED1[7];
  __O  uint8_t   SETGA20L;                          /*!< write to set GATEA20 in GATEA20 Control Reg                           */
  __I  uint8_t   RESERVED2[3];
  __O  uint8_t   RSTGA20L;                          /*!< write to set GATEA20 in GATEA20 Control Reg                           */
  __I  uint8_t   RESERVED3[547];
  __IO uint8_t   PORT92_ENABLE;                     /*!< [0:0] 1= Port92h Register is enabled.                                 */
} PORT92_Type;


/* ================================================================================ */
/* ================                       MBX                      ================ */
/* ================================================================================ */


/**
  * @brief The Mailbox provides a standard run-time mechanism for the host to
 communicate with the Embedded Controller (EC)  (MBX)
  */

typedef struct {                                    /*!< MBX Structure                                                         */
  __IO uint8_t   INDEX;                             /*!< MBX_Index Register                                                    */
  __IO uint8_t   DATA_REG;                          /*!< MBX_Data_Register                                                     */
  __I  uint16_t  RESERVED[127];
  __IO uint8_t   HOST_TO_EC;                        /*!< HOST-to-EC Mailbox Register                                           */
  __I  uint8_t   RESERVED1[3];
  __IO uint8_t   EC_TO_HOST;                        /*!< EC-to-Host Mailbox Register                                           */
  __I  uint8_t   RESERVED2[3];
  
  union {
    __IO uint8_t   SMI_SOURCE;                      /*!< SMI Interrupt Source Register                                         */
    
    struct {
      __I  uint8_t   EC_WR      :  1;               /*!< EC Mailbox Write (flag).                                              */
      __IO uint8_t   EC_SMI     :  7;               /*!< EC Software Interrupt source control                                  */
    } SMI_SOURCE_b;                                 /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED3[3];
  
  union {
    __IO uint8_t   SMI_MASK;                        /*!< SMI Interrupt Mask Register                                           */
    
    struct {
      __IO uint8_t   EC_WR_EN   :  1;               /*!< EC Mailbox Write Interrupt Enable.                                    */
      __IO uint8_t   EC_SMI_EN  :  7;               /*!< EC Software Interrupt Enable.                                         */
    } SMI_MASK_b;                                   /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED4[3];
  __IO uint8_t   REG[42];                           /*!< Mailbox Register                                                      */
} MBX_Type;


/* ================================================================================ */
/* ================                       PM1                      ================ */
/* ================================================================================ */


/**
  * @brief The CEC1302 implements the ACPI fixed registers but includes only those bits that apply to the power
 button sleep button and RTC alarm events. The ACPI WAK_STS, SLP_TYP, and SLP_EN bits are also supported.  (PM1)
  */

typedef struct {                                    /*!< PM1 Structure                                                         */
  __I  uint8_t   RESERVED;
  
  union {
    __IO uint8_t   STS2;                            /*!< PM1 Status 2                                                          */
    
    struct {
      __IO uint8_t   PWRBTN_STS :  1;               /*!< simulate a Power button status (R/WC)                                 */
      __IO uint8_t   SLPBTN_STS :  1;               /*!< simulate a Sleep button status (R/WC)                                 */
      __IO uint8_t   RTC_STS    :  1;               /*!< simulate a RTC status. (R/WC)                                         */
      __IO uint8_t   PWRBTNOR_STS:  1;              /*!< simulate a Power button override status(R/WC)                         */
           uint8_t              :  3;
      __IO uint8_t   WAK_STS    :  1;               /*!< Host writing a one to this bit. (R/WC)                                */
    } STS2_b;                                       /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED1;
  
  union {
    __IO uint8_t   EN2;                             /*!< PM1 Enable 2                                                          */
    
    struct {
      __IO uint8_t   PWRBTN_EN  :  1;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   SLPBTN_EN  :  1;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   RTC_EN     :  1;               /*!< Controlled by Host. read by the EC.                                   */
    } EN2_b;                                        /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED2;
  
  union {
    __IO uint8_t   CTRL2;                           /*!< PM1 Control 2                                                         */
    
    struct {
           uint8_t              :  1;
      __IO uint8_t   PWRBTNOR_EN:  1;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   SLP_TYP    :  3;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   SLP_EN     :  1;               /*!< Host Wt 1 to set, EC wt 1 to Clr                                      */
    } CTRL2_b;                                      /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED3[251];
  
  union {
    __IO uint8_t   STS_2;                           /*!< PM1 Status 2                                                          */
    
    struct {
      __IO uint8_t   PWRBTN_STS :  1;               /*!< simulate a Power button status (R/WC)                                 */
      __IO uint8_t   SLPBTN_STS :  1;               /*!< simulate a Sleep button status (R/WC)                                 */
      __IO uint8_t   RTC_STS    :  1;               /*!< simulate a RTC status. (R/WC)                                         */
      __IO uint8_t   PWRBTNOR_STS:  1;              /*!< simulate a Power button override status(R/WC)                         */
           uint8_t              :  3;
      __IO uint8_t   WAK_STS    :  1;               /*!< Host writing a one to this bit. (R/WC)                                */
    } STS_2_b;                                      /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED4;
  
  union {
    __IO uint8_t   EN_2;                            /*!< PM1 Enable 2                                                          */
    
    struct {
      __IO uint8_t   PWRBTN_EN  :  1;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   SLPBTN_EN  :  1;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   RTC_EN     :  1;               /*!< Controlled by Host. read by the EC.                                   */
    } EN_2_b;                                       /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED5;
  
  union {
    __IO uint8_t   CTRL_2;                          /*!< PM1 Control 2                                                         */
    
    struct {
           uint8_t              :  1;
      __IO uint8_t   PWRBTNOR_EN:  1;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   SLP_TYP    :  3;               /*!< Controlled by Host. read by the EC.                                   */
      __IO uint8_t   SLP_EN     :  1;               /*!< Host Wt 1 to set, EC wt 1 to Clr                                      */
    } CTRL_2_b;                                     /*!< BitSize                                                               */
  };
  __I  uint16_t  RESERVED6[5];
  __IO uint8_t   PM_STS;                            /*!< [0:0]wt 1 interrupt is generated on EC_SCI#                           */
} PM1_Type;


/* ================================================================================ */
/* ================                      UART                      ================ */
/* ================================================================================ */


/**
  * @brief The 16550 UART (Universal Asynchronous Receiver/Transmitter) is a full-function
 Two Pin Serial Port that supports the standard RS-232 Interface.  (UART)
  */

typedef struct {                                    /*!< UART Structure                                                        */
  
  union {
    __O  uint8_t   TX_DATA;                         /*!< UART Transmit Buffer Register                                         */
    __I  uint8_t   RX_DATA;                         /*!< UART Receive Buffer Register                                          */
    __IO uint8_t   BAUDRATE_LSB;                    /*!< Programmable BAUD Rate Generator (LSB) Reg.                           */
  };
  
  union {
    union {
      __IO uint8_t   INT_EN;                        /*!< UART Interrupt Enable Register                                        */
      
      struct {
        __IO uint8_t   ERDAI    :  1;               /*!< enables Received Data Available Interrupt                             */
        __IO uint8_t   ETHREI   :  1;               /*!< enables Transmitter Holding Empty Interrupt                           */
        __IO uint8_t   ELSI     :  1;               /*!< enables Received Line Status Interrupt                                */
        __IO uint8_t   EMSI     :  1;               /*!< enables the MODEM Status Interrupt                                    */
      } INT_EN_b;                                   /*!< BitSize                                                               */
    };
    __IO uint8_t   BAUDRATE_MSB;                    /*!< [6:0]BAUD_RATE_DIVISOR_MSB [7]BAUD_CLK_SEL                            */
  };
  
  union {
    union {
      __I  uint8_t   INT_ID;                        /*!< UART Interrupt Identification Register                                */
      
      struct {
        __I  uint8_t   IPEND    :  1;               /*!< indicate whether an interrupt is pending.                             */
        __I  uint8_t   INTID    :  3;               /*!< highest priority interrupt pending                                    */
             uint8_t            :  2;
        __I  uint8_t   FIFO_EN  :  2;               /*!< two bits are set when FIFO CONTROL bit 0=1                            */
      } INT_ID_b;                                   /*!< BitSize                                                               */
    };
    
    union {
      __O  uint8_t   FIFO_CR;                       /*!< UART FIFO Control Register                                            */
      
      struct {
        __O  uint8_t   EXRF     :  1;               /*!< Enable XMIT and RECV FIFO.                                            */
        __O  uint8_t   CLEAR_RECV_FIFO:  1;         /*!< clears all bytes in RCVR FIFO, resets counter                         */
        __O  uint8_t   CLEAR_XMIT_FIFO:  1;         /*!< clears all bytes in XMIT FIFO, resets counter                         */
        __IO uint8_t   DMA_MODE_SELECT:  1;         /*!< RXRDY,TXRDY pins functions are reserved.                              */
             uint8_t            :  2;
        __IO uint8_t   RECV_FIFO_TRIGGER_LEVEL:  2; /*!< set trigger level for RCVR FIFO Intr                                  */
      } FIFO_CR_b;                                  /*!< BitSize                                                               */
    };
  };
  
  union {
    __IO uint8_t   LINE_CR;                         /*!< UART Line Control Register                                            */
    
    struct {
      __IO uint8_t   WORD_LENGTH:  2;               /*!< number of bits in transmitted or received                             */
      __IO uint8_t   STOP_BITS  :  1;               /*!< number of stop bits in transmitted or received                        */
      __IO uint8_t   ENABLE_PARITY:  1;             /*!< Parity Enable bit.                                                    */
      __IO uint8_t   PARITY_SELECT:  1;             /*!< Even Parity Select bit.                                               */
      __IO uint8_t   STICK_PARITY:  1;              /*!< Stick Parity bit.                                                     */
      __IO uint8_t   BREAK_CONTROL:  1;             /*!< Set Break Control bit                                                 */
      __IO uint8_t   DLAB       :  1;               /*!< DLAB Divisor Latch Access Bit (DLAB).                                 */
    } LINE_CR_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint8_t   MODEM_CR;                        /*!< UART Modem Control Register                                           */
    
    struct {
      __IO uint8_t   DTR        :  1;               /*!< Data Terminal Ready (nDTR) output.                                    */
      __IO uint8_t   RTS        :  1;               /*!< Request To Send (nRTS) output.                                        */
      __IO uint8_t   OUT1       :  1;               /*!< controls the Output 1 (OUT1) bit.                                     */
      __IO uint8_t   OUT2       :  1;               /*!< enable an UART interrupt.                                             */
      __IO uint8_t   LOOPBACK   :  1;               /*!< provides loopback for diagnostic                                      */
    } MODEM_CR_b;                                   /*!< BitSize                                                               */
  };
  
  union {
    __I  uint8_t   LINE_STS;                        /*!< UART Line Status Register                                             */
    
    struct {
      __I  uint8_t   DATA_READY :  1;               /*!< 1= data into Rx Buffer Register or FIFO                               */
      __I  uint8_t   OVERRUN    :  1;               /*!< OVERRUN Overrun Error.                                                */
      __I  uint8_t   PE         :  1;               /*!< PARITY ERROR Parity Error.                                            */
      __I  uint8_t   FRAME_ERROR:  1;               /*!< FRAME_ERROR Framing Error.                                            */
      __I  uint8_t   BREAK_INTERRUPT:  1;           /*!< BREAK_INTERRUPT Break Interrupt.                                      */
      __I  uint8_t   TRANSMIT_EMPTY:  1;            /*!< Transmitter Holding Register Empty                                    */
      __I  uint8_t   TRANSMIT_ERROR:  1;            /*!< Transmitter Holding/Shift are both empty.                             */
      __I  uint8_t   FIFO_ERROR :  1;               /*!< FIFO_ERROR                                                            */
    } LINE_STS_b;                                   /*!< BitSize                                                               */
  };
  
  union {
    __I  uint8_t   MODEM_STS;                       /*!< UART Modem Status Register                                            */
    
    struct {
      __I  uint8_t   CTS        :  1;               /*!< CTS Delta Clear To Send (DCTS).                                       */
      __I  uint8_t   DSR        :  1;               /*!< DSR Delta Data Set Ready (DDSR).                                      */
      __I  uint8_t   RI         :  1;               /*!< Trailing Edge of Ring Indicator (TERI).                               */
      __I  uint8_t   DCD        :  1;               /*!< DCD Delta Data Carrier Detect (DDCD).                                 */
      __IO uint8_t   nCTS       :  1;               /*!< complement of Clear To Send (nCTS) input.                             */
      __IO uint8_t   nDSR       :  1;               /*!< complement of Data Set Ready (nDSR) input.                            */
      __IO uint8_t   nRI        :  1;               /*!< complement of Ring Indicator (nRI) input.                             */
      __IO uint8_t   nDCD       :  1;               /*!< complement of Data Carrier Detect (nDCD) input.                       */
    } MODEM_STS_b;                                  /*!< BitSize                                                               */
  };
  __IO uint8_t   SCRATCHPAD;                        /*!< as a scratchpad reg. be used by programmer                            */
  __I  uint32_t  RESERVED[202];
  __IO uint8_t   ACTIVATE;                          /*!< [0:0] 1= UART is powered/functional.                                  */
  __I  uint8_t   RESERVED1[191];
  
  union {
    __IO uint8_t   CONFIG;                          /*!< UART Config Select Register                                           */
    
    struct {
      __IO uint8_t   CLK_SRC    :  1;               /*!< 1=Baud Clock from external clock, 0=internal                          */
      __IO uint8_t   POWER      :  1;               /*!< 1=reset from nSIO_RESET, 0=VCC1_RESET                                 */
      __IO uint8_t   POLARITY   :  1;               /*!< 1=UART_TX and UART_RX pins are inverted                               */
    } CONFIG_b;                                     /*!< BitSize                                                               */
  };
} UART_Type;


/* ================================================================================ */
/* ================                      INTR                      ================ */
/* ================================================================================ */


/**
  * @brief The interrupt generation logic is made of 16 groups of signals, each of which
 consist of a Status register, a Enable register and a Result register. The Status and Enable
 are latched registers. The Result register is a bit by bit AND function of the Source and Enable
 registers. All the bits of the Result register are OR'ed together and AND'ed with the corresponding
 bit in the Block Select register to form the interrupt signal that is routed to the ARM interrupt controller.  (INTR)
  */

typedef struct {                                    /*!< INTR Structure                                                        */
  INTR_IRQ_Type IRQ[16];                            /*!< DEFINITIONS FOR GIRQi SOURCE/ENABLE/RESULT                            */
  __I  uint32_t  RESERVED[48];
  __IO uint32_t  BLOCK_ENABLE_SET;                  /*!< [23:8] IRQ Vector Enable Set                                          */
  __IO uint32_t  BLOCK_ENABLE_CLEAR;                /*!< [23:8] IRQ Vector Enable Clear                                        */
  __I  uint32_t  IRQ_VECTOR_STATE;                  /*!< [23:8] reflects current state of IRQi                                 */
} INTR_Type;


/* ================================================================================ */
/* ================                       WDT                      ================ */
/* ================================================================================ */


/**
  * @brief The function of the Watchdog Timer is to provide a mechanism to detect if the
 internal embedded controller has failed. When enabled, the Watchdog Timer (WDT) circuit will generate
 a WDT Event if the user program fails to reload the WDT within a specified length of time known as the WDT Interval.  (WDT)
  */

typedef struct {                                    /*!< WDT Structure                                                         */
  __IO uint16_t  LOAD;                              /*!< Writing to reload Watch Dog Timer counter                             */
  __I  uint16_t  RESERVED;
  
  union {
    __IO uint8_t   CONTROL;                         /*!< WDT Control Register                                                  */
    
    struct {
      __IO uint8_t   ENABLE     :  1;               /*!< WDT Block enabled                                                     */
      __IO uint8_t   STATUS     :  1;               /*!< last reset was caused by an underflow (R/WC)                          */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED1[3];
  __O  uint8_t   KICK;                              /*!< Writes to reload and start decrementing                               */
  __I  uint8_t   RESERVED2[3];
  __I  uint16_t  COUNT;                             /*!< current WDT count.                                                    */
} WDT_Type;


/* ================================================================================ */
/* ================                   TIMER_16_0                   ================ */
/* ================================================================================ */


/**
  * @brief This timer block offers a simple mechanism for firmware to maintain a time
 base. This timer may be instantiated as 16 bits or 32 bits.  (TIMER_16_0)
  */

typedef struct {                                    /*!< TIMER_16_0 Structure                                                  */
  __IO uint32_t  COUNT;                             /*!< Timer counter. may be set by Firmware.                                */
  __IO uint32_t  PRE_LOAD;                          /*!< Timer pre-load for counter upon restart.                              */
  __IO uint32_t  INTERRUPT_STATUS;                  /*!< [0:0] Interrupt status (R/WC)                                         */
  __IO uint32_t  INTERRUPT_ENABLE;                  /*!< [0:0] interrupt enable                                                */
  
  union {
    __IO REG32_U  CONTROL;                         /*!< Timer Control Register                                                */
    
    struct {
      __IO uint32_t  ENABLE     :  1;               /*!< This enables the block for operation.                                 */
           uint32_t             :  1;
      __IO uint32_t  COUNT_UP   :  1;               /*!< This selects the counter direction.                                   */
      __IO uint32_t  AUTO_RESTART:  1;              /*!< select action taken upon completing a count.                          */
      __IO uint32_t  SOFT_RESET :  1;               /*!< soft reset. self clearing 1 cycle.                                    */
      __IO uint32_t  START      :  1;               /*!< This bit triggers the timer counter.                                  */
      __IO uint32_t  RELOAD     :  1;               /*!< reloads counter without interrupting.                                 */
      __IO uint32_t  HALT       :  1;               /*!< halt bit.                                                             */
           uint32_t             :  8;
      __IO uint32_t  PRE_SCALE  : 16;               /*!< to divide down system clock                                           */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
} TIMER_16_0_Type;


/* ================================================================================ */
/* ================                       HTM                      ================ */
/* ================================================================================ */


/**
  * @brief The Hibernation Timer can generate a wake event to the Embedded Controller (EC)
 when it is in a hibernation mode. This block supports wake events up to 2 hours in duration. 
 The timer is a 16-bit binary count-down timer that can be programmed in 30.5us and 0.125 second 
 increments for period ranges of 30.5us to 2s or 0.125s to 136.5 minutes, respectively.  (HTM)
  */

typedef struct {                                    /*!< HTM Structure                                                         */
  __IO uint16_t  PRELOAD;                           /*!< [15:0] set Hibernation Timer Preload value                            */
  __I  uint16_t  RESERVED;
  __IO uint16_t  CONTROL;                           /*!< [0:0] 1= resolution 0.125s, 0= 30.5us                                 */
  __I  uint16_t  RESERVED1;
  __I  uint16_t  COUNT;                             /*!< Count of the Hibernation Timer.                                       */
} HTM_Type;


/* ================================================================================ */
/* ================                       RTC                      ================ */
/* ================================================================================ */


/**
  * @brief This is the set of registers that are automatically counted by hardware
 every 1 second while the block is enabled to run and to update. These registers are:
 Seconds, Minutes, Hours, Day of Week, Day of Month, Month, and Year.  (RTC)
  */

typedef struct {                                    /*!< RTC Structure                                                         */
  __IO uint8_t   SEC;                               /*!< Seconds Register                                                      */
  __IO uint8_t   SEC_ALARM;                         /*!< Seconds Alarm Register                                                */
  __IO uint8_t   MIN;                               /*!< Minutes Register                                                      */
  __IO uint8_t   MIN_ALARM;                         /*!< Minutes Alarm Register                                                */
  __IO uint8_t   HR;                                /*!< Hours Register                                                        */
  __IO uint8_t   HR_ALARM;                          /*!< Hours Alarm Register                                                  */
  __IO uint8_t   DAY_WEEK;                          /*!< Day of Week Register                                                  */
  __IO uint8_t   DAY_MONTH;                         /*!< Day of Month Register                                                 */
  __IO uint8_t   MONTH;                             /*!< Month Register                                                        */
  __IO uint8_t   YEAR;                              /*!< Year Register                                                         */
  __IO uint8_t   REG_A;                             /*!< Register A                                                            */
  __IO uint8_t   REG_B;                             /*!< Register B                                                            */
  __IO uint8_t   REG_C;                             /*!< Register C                                                            */
  __IO uint8_t   REG_D;                             /*!< Register D                                                            */
  __I  uint16_t  RESERVED;
  
  union {
    __IO uint8_t   CONTROL;                         /*!< RTC Control Register                                                  */
    
    struct {
      __IO uint8_t   BLOCK_ENABLE:  1;              /*!< 1= block to function internally                                       */
      __IO uint8_t   SOFT_RESET :  1;               /*!< 1= RTC_RST reset (self-clearing no waiting)                           */
           uint8_t              :  1;
      __IO uint8_t   ALARM_ENABLE:  1;              /*!< 1=Enables Alarm, 0=Disables                                           */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED1[3];
  __IO uint8_t   WEEK_ALARM;                        /*!< Set value in range 1-7                                                */
  __I  uint8_t   RESERVED2[3];
  
  union {
    __IO uint32_t  DAYLIGHT_SAVINGS_FORWARD;        /*!< Daylight Savings Forward Register                                     */
    
    struct {
      __IO uint32_t  DST_MONTH  :  8;               /*!< This field matches the Month Register.                                */
      __IO uint32_t  DST_DAY_OF_WEEK:  3;           /*!< matches the Day of Week Register bits[2:0].                           */
           uint32_t             :  5;
      __IO uint32_t  DST_WEEK   :  3;               /*!< week number (1,,5) within current month.                              */
           uint32_t             :  5;
      __IO uint32_t  DST_HOUR   :  7;               /*!< matching value for bits[6:0] of Hours register                        */
      __IO uint32_t  DST_AM_PM  :  1;               /*!< This bit selects AM vs. PM.                                           */
    } DAYLIGHT_SAVINGS_FORWARD_b;                   /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  DAYLIGHT_SAVINGS_BACKWARD;       /*!< Daylight Savings Backward Register                                    */
    
    struct {
      __IO uint32_t  DST_MONTH  :  8;               /*!< This field matches the Month Register.                                */
      __IO uint32_t  DST_DAY_OF_WEEK:  3;           /*!< matches the Day of Week Register bits[2:0].                           */
           uint32_t             :  5;
      __IO uint32_t  DST_WEEK   :  3;               /*!< week number (1,,5) within current month.                              */
           uint32_t             :  5;
      __IO uint32_t  DST_HOUR   :  7;               /*!< matching value for bits[6:0] of Hours register                        */
      __IO uint32_t  DST_AM_PM  :  1;               /*!< This bit selects AM vs. PM.                                           */
    } DAYLIGHT_SAVINGS_BACKWARD_b;                  /*!< BitSize                                                               */
  };
} RTC_Type;


/* ================================================================================ */
/* ================                      GPIO                      ================ */
/* ================================================================================ */


/**
  * @brief The CEC1302/24 GPIO Interface provides general purpose input monitoring and output control,
 as well as managing many aspects of pin functionality; including, multi-function Pin Multiplexing Control, GPIO
 Direction control, PU/PD (PU_PD) resistors, asynchronous wakeup and synchronous Interrupt Detection (int_det),
 GPIO Direction, and Polarity control, as well as control of pin drive strength and slew rate.  (GPIO)
  */

typedef struct {                                    /*!< GPIO Structure                                                        */
  
  union {
    __IO uint32_t  PIN_CONTROL[160];                /*!< 1st Pin Control Register                                              */
    
    struct {
      __IO uint32_t  PU_PD      :  2;               /*!< 01= Pull Up, 10= Pull Down, 11/00= None                               */
      __IO uint32_t  PWR        :  2;               /*!< 00= VCC1, 01= VCC2 Power Rail 1x = Reserved                           */
      __IO uint32_t  INT_DET    :  3;               /*!< 
                                                          [7654] --------------------------------------------
                                                          0 000 = Low Level Sensitive 
                                                          0 001 = High Level Sensitive
                                                          0 100 = Interrupt events are disabled
                                                          1 101 = Rising Edge Triggered 
                                                          1 110 = Falling Edge Triggered 
                                                          1 111 = Either edge triggered 
                                                          ---------------------------------------------------                  */
      __IO uint32_t  EDGE_EN    :  1;               /*!< 1= Edge detection enabled                                             */
      __IO uint32_t  BUFFER     :  1;               /*!< Output Buffer Type. 0 = Push-Pull, 1 = Open Drain                     */
      __IO uint32_t  DIR        :  1;               /*!< GPIO Direction. 0 = Input, 1 = Output                                 */
      __IO uint32_t  OUTPUT_WRITE_EN:  1;           /*!< 0= Alternative GPIO data write enabled                                */
      __IO uint32_t  POLARITY   :  1;               /*!< 0 = Non-inverted, 1 = Inverted                                        */
      __IO uint32_t  MUX        :  2;               /*!< 00= GPIO Function, 01/10/11=Func 1/2/3                                */
           uint32_t             :  2;
      __IO uint32_t  OUTPUT     :  1;               /*!< 0: GPIO[x] out = '0', 1: GPIO[x] out = '1'                            */
           uint32_t             :  7;
      __I  uint32_t  INPUT      :  1;               /*!< reflects the state of GPIO input                                      */
    } PIN_CONTROL_b[160];                           /*!< BitSize                                                               */
  };
  __IO uint32_t  OUTPUT[5];                         /*!< Group 0: GPIO[x] out =0, 1: =1                                        */
  __I  uint32_t  RESERVED[27];
  __IO uint32_t  INPUT[5];                          /*!< Group GPIO Input Registers                                            */
  __I  uint32_t  RESERVED1[123];
  
  union {
    __IO uint32_t  CONTROL2_000_067[56];            /*!< PIN CONTROL REGISTER 2, from 000 - 067                                */
    
    struct {
      __IO uint32_t  SLEW_RATE  :  1;               /*!< slew rate 0= slow (half freq), 1= fast                                */
           uint32_t             :  3;
      __IO uint32_t  DRIVE_STRENGTH:  2;            /*!< drive strength 00=2, 01=4, 10=8, 11=12(mA)                            */
    } CONTROL2_000_067_b[56];                       /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  CONTROL2_100_167[56];            /*!< PIN CONTROL REGISTER 2, from 100 - 167                                */
    
    struct {
      __IO uint32_t  SLEW_RATE  :  1;               /*!< slew rate 0= slow (half freq), 1= fast                                */
           uint32_t             :  3;
      __IO uint32_t  DRIVE_STRENGTH:  2;            /*!< drive strength 00=2, 01=4, 10=8, 11=12(mA)                            */
    } CONTROL2_100_167_b[56];                       /*!< BitSize                                                               */
  };
  __I  uint32_t  RESERVED2[24];
  
  union {
    __IO uint32_t  CONTROL2_200_267[56];            /*!< PIN CONTROL REGISTER 2, from 200 - 267                                */
    
    struct {
      __IO uint32_t  SLEW_RATE  :  1;               /*!< slew rate 0= slow (half freq), 1= fast                                */
           uint32_t             :  3;
      __IO uint32_t  DRIVE_STRENGTH:  2;            /*!< drive strength 00=2, 01=4, 10=8, 11=12(mA)                            */
    } CONTROL2_200_267_b[56];                       /*!< BitSize                                                               */
  };
} GPIO_Type;


/* ================================================================================ */
/* ================                       DMA                      ================ */
/* ================================================================================ */


/**
  * @brief The Internal DMA Controller transfers data to/from the source from/to the
 destination. The firmware is responsible for setting up each channel. Afterwards either the
 firmware or the hardware may perform the flow control. The hardware flow control exists entirely
 inside the source device. Each transfer may be 1, 2, or 4 bytes in size, so long as the device
 supports a transfer of that size. Every device must be on the internal 32-bit address space.  (DMA)
  */

typedef struct {                                    /*!< DMA Structure                                                         */
  
  union {
    __IO uint8_t   CONTROL;                         /*!< Soft reset. Enable the blocks operation.                              */
    
    struct {
      __IO uint8_t   ACTIVATE   :  1;               /*!< Enable the blocks operation. (R/WS)                                   */
      __O  uint8_t   SOFT_RESET :  1;               /*!< Soft reset entire module. self-clearing.                              */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED[3];
  __I  uint32_t  DATA_PACKET;                       /*!< data from currently active transfer source                            */
  __I  uint32_t  RESERVED1[2];
  DMA_CH_Type CH[12];                               /*!< registers to determine channel's operation.                           */
} DMA_Type;


/* ================================================================================ */
/* ================                      SMB0                      ================ */
/* ================================================================================ */


/**
  * @brief The SMBus interface can handle standard SMBus 2.0 protocols as well as I2C interface.  (SMB0)
  */

typedef struct {                                    /*!< SMB0 Structure                                                        */
  
  union {
    union {
      __I  uint8_t   STATUS;                        /*!< Status Register                                                       */
      
      struct {
        __I  uint8_t   nBB      :  1;               /*!< 0= Bus Busy                                                           */
        __I  uint8_t   LAB      :  1;               /*!< Lost Arbitration Bit                                                  */
        __I  uint8_t   AAS      :  1;               /*!< Addressed As Slave                                                    */
        __I  uint8_t   LRB_AD0  :  1;               /*!< "Last Received Bit"/Address 0 (general call)                          */
        __I  uint8_t   BER      :  1;               /*!< Bus Error (BER)                                                       */
        __I  uint8_t   STS      :  1;               /*!< 1=ext generated STOP condition is detected.                           */
        __I  uint8_t   SAD      :  1;               /*!< SMBus Address Decoded (SAD)                                           */
        __I  uint8_t   PIN      :  1;               /*!< Pending Interrupt bit                                                 */
      } STATUS_b;                                   /*!< BitSize                                                               */
    };
    
    union {
      __O  uint8_t   CONTROL;                       /*!< Control Register                                                      */
      
      struct {
        __IO uint8_t   ACK      :  1;               /*!< 1= send an acknowledge automatically                                  */
        __IO uint8_t   STO      :  1;               /*!< See STA description                                                   */
        __IO uint8_t   STA      :  1;               /*!< generation of repeated Start and Stop condition                       */
        __IO uint8_t   ENI      :  1;               /*!< Enable Interrupt bit                                                  */
             uint8_t            :  2;
        __IO uint8_t   ESO      :  1;               /*!< enables/disables SMB serial data output                               */
        __IO uint8_t   PIN      :  1;               /*!< Pending Interrupt Not (PIN) software reset                            */
      } CONTROL_b;                                  /*!< BitSize                                                               */
    };
  };
  __I  uint8_t   RESERVED[3];
  
  union {
    __IO uint16_t  OWN;                             /*!< Own Address Reg. wt 55h= AAh addr                                     */
    
    struct {
      __IO uint16_t  ADDRESS_1  :  7;               /*!< Own Address 1 addressed as a slave.                                   */
           uint16_t             :  1;
      __IO uint16_t  ADDRESS_2  :  7;               /*!< Own Address 2 addressed as a slave.                                   */
    } OWN_b;                                        /*!< BitSize                                                               */
  };
  __I  uint16_t  RESERVED1;
  __IO uint8_t   DATA_REG;                          /*!< Data                                                                  */
  __I  uint8_t   RESERVED2[3];
  
  union {
    __IO uint32_t  MASTER_COMMAND;                  /*!< SMBus Master Command Register                                         */
    
    struct {
      __IO uint32_t  MRUN       :  1;               /*!< 1= transfer bytes over SMBus.                                         */
      __IO uint32_t  MPROCEED   :  1;               /*!< 1:WAIT-BUSBUSY and MRUN-RECEIVE                                       */
           uint32_t             :  6;
      __IO uint32_t  START0     :  1;               /*!< 1: send a Start bit on the SMBus                                      */
      __IO uint32_t  STARTN     :  1;               /*!< 1: send a Start before the last byte                                  */
      __IO uint32_t  STOP       :  1;               /*!< 1: send a Stop bit after transaction completes                        */
      __IO uint32_t  PEC_TERM   :  1;               /*!< 1: PEC is transmitted when WriteCount is 0.                           */
      __IO uint32_t  READM      :  1;               /*!< 1: ReadCount field is replaced by byte                                */
      __IO uint32_t  READ_PEC   :  1;               /*!< 1: reading when ReadCount is 0 for one more byte                      */
           uint32_t             :  2;
      __IO uint32_t  WRITECOUNT :  8;               /*!< number of Master Transmit Buffer bytes                                */
      __IO uint32_t  READCOUNT  :  8;               /*!< number of Master Receive Buffer bytes                                 */
    } MASTER_COMMAND_b;                             /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  SLAVE_COMMAND;                   /*!< SMBus Slave Command Register                                          */
    
    struct {
      __IO uint32_t  SRUN       :  1;               /*!< 1:enables the Slave State Machine to operate                          */
      __IO uint32_t  SPROCEED   :  1;               /*!< Slave to START_WAIT/RECEIVE/TRANSMIT states                           */
      __IO uint32_t  SLAVE_PEC  :  1;               /*!< 1:PEC is copied to the DATA register                                  */
           uint32_t             :  5;
      __IO uint32_t  SLAVE_WRITECOUNT:  8;          /*!< number bytes software expects to send to Master                       */
      __IO uint32_t  SLAVE_READCOUNT:  8;           /*!< number copied from DATA to Slave Receive Buffer                       */
    } SLAVE_COMMAND_b;                              /*!< BitSize                                                               */
  };
  __IO uint8_t   PEC;                               /*!< PEC byte                                                              */
  __I  uint8_t   RESERVED3[3];
  __IO uint8_t   DATA_TIMING2;                      /*!< HOLD TIME (clock) START BIT                                           */
  __I  uint8_t   RESERVED4[7];
  
  union {
    __IO uint32_t  COMPLETION;                      /*!< Completion Register                                                   */
    
    struct {
           uint32_t             :  2;
      __IO uint32_t  DTEN       :  1;               /*!< 1: Device Time-out checking is enabled.                               */
      __IO uint32_t  MCEN       :  1;               /*!< 1: enable Master Cumulative Time-Out checking                         */
      __IO uint32_t  SCEN       :  1;               /*!< 1:enable Slave Cumulative Time-Out checking                           */
      __IO uint32_t  BIDEN      :  1;               /*!< 1:Bus Idle Detect Time-Out checking is enabled                        */
      __I  uint32_t  TIMERR     :  1;               /*!< 1:timeout error detect status are asserted.                           */
           uint32_t             :  1;
      __IO uint32_t  DTO        :  1;               /*!< DTO is the Device Time-out bit. (R/WC)                                */
      __IO uint32_t  MCTO       :  1;               /*!< Master Cumulative Time-out bit. (R/WC)                                */
      __IO uint32_t  SCTO       :  1;               /*!< SCTO is the Slave Cumulative Time-out bit(R/WC)                       */
      __IO uint32_t  CHDL       :  1;               /*!< CHDL is the clock high time-out detect bit(R/WC)                      */
      __IO uint32_t  CHDH       :  1;               /*!< CHDH is the bus idle time-out detect bit(R/WC)                        */
      __IO uint32_t  BER        :  1;               /*!< 1: BER in Status was set (R/WC)                                       */
      __IO uint32_t  LAB        :  1;               /*!< 1: LAB in Status was set (R/WC)                                       */
           uint32_t             :  1;
      __IO uint32_t  SNAKR      :  1;               /*!< 1: Slave sent NACK to transmitting Master                             */
      __I  uint32_t  STR        :  1;               /*!< 0: finished receive, 1:finished transmit phase                        */
           uint32_t             :  1;
      __IO uint32_t  SPROT      :  1;               /*!< 1: WriteCount in Slave counted down to 0(R/WC)                        */
      __IO uint32_t  REPEAT_READ:  1;               /*!< 1: Slave stopped because a Repeat Start for Rd                        */
      __IO uint32_t  REPEAT_WRITE:  1;              /*!< 1: Slave stopped because a Repeat Start for Wt                        */
           uint32_t             :  2;
      __IO uint32_t  MNAKX      :  1;               /*!< 1: Master received a NACK while transmitting                          */
      __I  uint32_t  MTR        :  1;               /*!< Master finished 0: receive 1: transmit                                */
           uint32_t             :  3;
      __IO uint32_t  IDLE       :  1;               /*!< 1: I2C bus becomes idle (R/WC)                                        */
      __IO uint32_t  MDONE      :  1;               /*!< 1: Master completed operation (R/WC)                                  */
      __IO uint32_t  SDONE      :  1;               /*!< 1: Slave completed operation (R/WC)                                   */
    } COMPLETION_b;                                 /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  IDLE_SCALING;                    /*!< Idle Scaling Register                                                 */
    
    struct {
      __IO uint32_t  FAIR_BUS_IDLE_MIN: 12;         /*!< number ticks to satisfy the fairness protocol                         */
           uint32_t             :  4;
      __IO uint32_t  FAIR_IDLE_DELAY: 12;           /*!< number ticks to program the delay                                     */
    } IDLE_SCALING_b;                               /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  CONFIGURATION;                   /*!< Configuration Register                                                */
    
    struct {
      __IO uint32_t  PORT_SEL   :  4;               /*!< determine one of 16 bus ports apply to SDAT/SCLK                      */
      __IO uint32_t  TCEN       :  1;               /*!< 1: Bus Time-Outs are enabled                                          */
      __I  uint32_t  SLOW_CLOCK :  1;               /*!< 1: Bus Clock multiplied by 4, thus frequency/4                        */
           uint32_t             :  1;
      __IO uint32_t  PECEN      :  1;               /*!< 1: Hardware PEC Support is enabled                                    */
      __IO uint32_t  DFEN       :  1;               /*!< 1: Digital Filter is enabled. 0: bypassed.                            */
      __IO uint32_t  RESET      :  1;               /*!< 1: initialized to power-on default state.                             */
      __IO uint32_t  ENAB       :  1;               /*!< 1: normal operation, 0: lowest power                                  */
      __IO uint32_t  DSA        :  1;               /*!< 0: Slave Address I2C Compatibility, 1: SMBus                          */
      __IO uint32_t  FAIR       :  1;               /*!< 1: MCTP Fairness protocol is in effect.                               */
           uint32_t             :  1;
      __I  uint32_t  GC_DIS     :  1;               /*!< General Call address 0: enabled, 1: disabled                          */
           uint32_t             :  1;
      __O  uint32_t  FLUSH_SXBUF:  1;               /*!< 1: Slave Transmit Buffer to be marked empty.                          */
      __O  uint32_t  FLUSH_SRBUF:  1;               /*!< 1: Slave Receive Buffer to be marked empty.                           */
      __O  uint32_t  FLUSH_MXBUF:  1;               /*!< 1: Master Transmit Buffer to be marked empty.                         */
      __O  uint32_t  FLUSH_MRBUF:  1;               /*!< 1: Master Receive Buffer to be marked empty.                          */
           uint32_t             :  8;
      __I  uint32_t  EN_AAS     :  1;               /*!< 0: Disable AAS Interrupt, 1: Enable                                   */
      __IO uint32_t  ENIDI      :  1;               /*!< 1: Idle interrupt is enabled. 0: disabled.                            */
      __IO uint32_t  ENMI       :  1;               /*!< 1: Master Done interrupt is enabled. 0: disabled                      */
      __IO uint32_t  ENSI       :  1;               /*!< 1: Slave Done interrupt is enabled. 0: disabled                       */
    } CONFIGURATION_b;                              /*!< BitSize                                                               */
  };
  
  union {
    __IO uint16_t  BUS_CLOCK;                       /*!< Bus Clock Register                                                    */
    
    struct {
      __IO uint16_t  LOW_PERIOD :  8;               /*!< number of I2C Baud Clock to make up low phase                         */
      __IO uint16_t  HIGH_PERIOD:  8;               /*!< number of I2C Baud Clock to make up high phase                        */
    } BUS_CLOCK_b;                                  /*!< BitSize                                                               */
  };
  __I  uint16_t  RESERVED5;
  __I  uint8_t   BLOCK_ID;                          /*!< Block ID Register                                                     */
  __I  uint8_t   RESERVED6[3];
  __I  uint8_t   REVISION;                          /*!< Revision Register                                                     */
  __I  uint8_t   RESERVED7[3];
  
  union {
    __IO uint8_t   BIT_BANG_CONTROL;                /*!< Bit-Bang Control Register                                             */
    
    struct {
      __IO uint8_t   BBEN       :  1;               /*!< 1: Bit-Bang Mode Enable.                                              */
      __IO uint8_t   CLDIR      :  1;               /*!< Bit-Bang Clock Direction. 0 - Input, 1 - Output                       */
      __IO uint8_t   DADIR      :  1;               /*!< Bit-Bang Data Direction. 0 - Input. 1 - Output                        */
      __IO uint8_t   BBCLK      :  1;               /*!< controls state of SCLK when BBEN = CLDIR = 1                          */
      __IO uint8_t   BBDAT      :  1;               /*!< controls state of SDAT when BBEN = DADIR = 1                          */
      __I  uint8_t   BBCLKI     :  1;               /*!< Bit-Bang Clock In. returns the state of SCLK.                         */
      __I  uint8_t   BBDATI     :  1;               /*!< Bit-Bang Data In. returns the state of SDAT                           */
    } BIT_BANG_CONTROL_b;                           /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED8[7];
  
  union {
    __IO uint32_t  DATA_TIMING;                     /*!< Data Timing Register                                                  */
    
    struct {
      __IO uint32_t  DATA_HOLD  :  8;               /*!< SDAT hold time following SCLK driven low.                             */
      __IO uint32_t  RESTART_SETUP:  8;             /*!< SDAT setup time for a repeated START condition.                       */
      __IO uint32_t  STOP_SETUP :  8;               /*!< SDAT setup time for a STOP condition.                                 */
      __IO uint32_t  START_HOLD :  8;               /*!< SCLK hold time during a START condition.                              */
    } DATA_TIMING_b;                                /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  TIME_OUT_SCALING;                /*!< Time-Out Scaling Register                                             */
    
    struct {
      __IO uint32_t  CLOCK_HIGH :  8;               /*!< = Clock High Time-Out x Baud_Clock_Period x 2                         */
      __IO uint32_t  SLAVE_CUM  :  8;               /*!< = Slave Cum Time-Out x Baud_Clock_Period x 1024                       */
      __IO uint32_t  MASTER_CUM :  8;               /*!< = Master Cum Time-Out x Baud_Clock_Periodx 512                        */
      __IO uint32_t  BUS_IDLE_MIN:  8;              /*!< = Bus Idle Min [7:0] x Baud_Clock_Period                              */
    } TIME_OUT_SCALING_b;                           /*!< BitSize                                                               */
  };
  __IO uint8_t   SLAVE_TRANSMIT_BUFFER;             /*!< SMBus Slave Transmit Buffer Register                                  */
  __I  uint8_t   RESERVED9[3];
  __IO uint8_t   SLAVE_RECEIVE_BUFFER;              /*!< SMBus Slave Receive Buffer Register                                   */
  __I  uint8_t   RESERVED10[3];
  __IO uint8_t   MASTER_TRANSMIT_BUFER;             /*!< SMBus Master Transmit Bufer Register                                  */
  __I  uint8_t   RESERVED11[3];
  __IO uint8_t   MASTER_RECEIVE_BUFFER;             /*!< SMBus Master Receive Buffer Register                                  */
} SMB0_Type;


/* ================================================================================ */
/* ================                      PECI                      ================ */
/* ================================================================================ */


/**
  * @brief The CEC1302 includes a PECI Interface to allow the EC to retrieve temperature readings from PECI-compliant devices.  (PECI)
  */

typedef struct {                                    /*!< PECI Structure                                                        */
  __IO uint8_t   WRITE_DATA;                        /*!< Tprovides access to a 32-byte Transmit FIFO.                          */
  __I  uint8_t   RESERVED[3];
  __IO uint8_t   READ_DATA;                         /*!< provides access to a 32-byte Receive FIFO.                            */
  __I  uint8_t   RESERVED1[3];
  
  union {
    __IO uint8_t   CONTROL;                         /*!< Control Register                                                      */
    
    struct {
      __IO uint8_t   PD         :  1;               /*!< Power Down controls Power Management Interface                        */
           uint8_t              :  2;
      __IO uint8_t   RST        :  1;               /*!< RST indicates that the PECI Core should be reset.                     */
           uint8_t              :  1;
      __IO uint8_t   FRST       :  1;               /*!< FRST is the FIFO Reset bit.                                           */
      __IO uint8_t   TXEN       :  1;               /*!< TXEN is the Transmit Enable bit.                                      */
      __IO uint8_t   MIEN       :  1;               /*!< MIEN is the Master Interrupt Enable                                   */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED2[3];
  
  union {
    __IO uint8_t   STATUS1;                         /*!< Status Register 1                                                     */
    
    struct {
      __IO uint8_t   BOF        :  1;               /*!< PECI begins Address Timing Negotiation(R/WC)                          */
      __IO uint8_t   nEOF       :  1;               /*!< End of Frame asserted following Message Stop(R/WC)                    */
      __I  uint8_t   ERR        :  1;               /*!< error for current transaction has been detected                       */
      __I  uint8_t   RDY        :  1;               /*!< state of the READY signal function                                    */
      __IO uint8_t   RDYLO      :  1;               /*!< 1: falling edge of the READY signal function(R/WC)                    */
      __IO uint8_t   RDYHI      :  1;               /*!< 1: rising edge of the READY signal function (R/WC)                    */
           uint8_t              :  1;
      __I  uint8_t   MINT       :  1;               /*!< asserted when any interrupt status is asserted.                       */
    } STATUS1_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED3[3];
  
  union {
    __I  uint8_t   STATUS2;                         /*!< Status Register 2                                                     */
    
    struct {
      __I  uint8_t   WFF        :  1;               /*!< Write Data Register FIFO is full. No interrupt.                       */
      __I  uint8_t   WFE        :  1;               /*!< Write Data Register FIFO is empty.                                    */
      __I  uint8_t   RFF        :  1;               /*!< RFF indicates Read Data Register FIFO is full.                        */
      __I  uint8_t   RFE        :  1;               /*!< Read Data Register FIFO is empty. No interrupt.                       */
           uint8_t              :  3;
      __I  uint8_t   IDLE       :  1;               /*!< SST/PECI bus is idle, a new transaction may begin                     */
    } STATUS2_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED4[3];
  
  union {
    __IO uint8_t   ERROR;                           /*!< Error Register                                                        */
    
    struct {
      __IO uint8_t   FERR       :  1;               /*!< FERR (Frame Check Sequence Error). (R/WC)                             */
      __IO uint8_t   BERR       :  1;               /*!< reads value different from it has driven (R/WC)                       */
           uint8_t              :  1;
      __IO uint8_t   REQERR     :  1;               /*!< READY is not asserted when counts down to zero                        */
      __IO uint8_t   WROV       :  1;               /*!< WROV (Write Overrun). (R/WC)                                          */
      __IO uint8_t   WRUN       :  1;               /*!< WRUN (Write Underrun). (R/WC)                                         */
      __IO uint8_t   RDOV       :  1;               /*!< indicates read buffer has overflowed (R/WC)                           */
      __IO uint8_t   CLKERR     :  1;               /*!< READY de-asserted in middle of a transaction(R/WC)                    */
    } ERROR_b;                                      /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED5[3];
  
  union {
    __IO uint8_t   INT_EN1;                         /*!< Interrupt Enable 1 Register                                           */
    
    struct {
      __IO uint8_t   BIEN       :  1;               /*!< '1' the BOF interrupt is enabled.                                     */
      __IO uint8_t   EIEN       :  1;               /*!< '1' the EOF interrupt is enabled.                                     */
      __IO uint8_t   EREN       :  1;               /*!< '1' the ERR interrupt is enabled.                                     */
           uint8_t              :  1;
      __IO uint8_t   RLEN       :  1;               /*!< '1' the RDYLO interrupt is enabled.                                   */
      __IO uint8_t   RHEN       :  1;               /*!< '1' the RDYHI interrupt is enabled.                                   */
    } INT_EN1_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED6[3];
  
  union {
    __IO uint8_t   INT_EN2;                         /*!< Interrupt Enable 2 Register                                           */
    
    struct {
           uint8_t              :  1;
      __IO uint8_t   ENWFE      :  1;               /*!< '1' the WFE interrupt is enabled.                                     */
      __IO uint8_t   ENRFF      :  1;               /*!< '1' the RFF interrupt is enabled.                                     */
    } INT_EN2_b;                                    /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED7[3];
  __IO uint8_t   OBT1;                              /*!< Optimal Bit Time Register (Low Byte)                                  */
  __I  uint8_t   RESERVED8[3];
  __IO uint8_t   OBT2;                              /*!< Optimal Bit Time Register (High Byte)                                 */
  __I  uint8_t   RESERVED9[27];
  __IO uint32_t  ID;                                /*!< Block ID Register                                                     */
  __IO uint32_t  REV;                               /*!< Revision Register                                                     */
} PECI_Type;


/* ================================================================================ */
/* ================                     TACH_0                     ================ */
/* ================================================================================ */


/**
  * @brief This block monitors TACH output signals (or locked rotor signals) from
 various types of fans, and determines their speed.  (TACH_0)
  */

typedef struct {                                    /*!< TACH_0 Structure                                                      */
  
  union {
    __IO uint32_t  CONTROL;                         /*!< TACHx Control Register                                                */
    
    struct {
      __IO uint32_t  OUT_LIMIT_ENABLE:  1;          /*!< 1=Enable interrupt output from Tach block                             */
      __IO uint32_t  TACH_EN    :  1;               /*!< 1= TACH Monitoring/ clock enabled, 0= TACH Idle                       */
           uint32_t             :  6;
      __IO uint32_t  FILTER_EN  :  1;               /*!< remove high frequency glitches. 1=Filter enabled                      */
           uint32_t             :  1;
      __IO uint32_t  MODE_SELECT:  1;               /*!< 1=Counter is incremented on rising edge                               */
      __IO uint32_t  EDGES      :  2;               /*!< 00/01/10/11: 2/3/5/9 Tach edges                                       */
           uint32_t             :  1;
      __IO uint32_t  READY_INT_EN:  1;              /*!< 1=Enable Count Ready interrupt, 0=Disable                             */
      __IO uint32_t  INPUT_INT_EN:  1;              /*!< 1=Enable Tach Input toggle interrupt, 0=Disable                       */
      __I  uint32_t  COUNTER    : 16;               /*!< latched value of the internal Tach pulse counter                      */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  STATUS;                          /*!< TACHx Status Register                                                 */
    
    struct {
      __IO uint32_t  OUT_LIMIT  :  1;               /*!< 1=Tach is outside of limits (R/WC)                                    */
      __I  uint32_t  PIN        :  1;               /*!< 1= Tach Input is high, 0= Input is low                                */
      __IO uint32_t  TOGGLE     :  1;               /*!< 1=Tach Input changed state, 0= stable (R/WC)                          */
      __IO uint32_t  COUNT_READY:  1;               /*!< 1=Reading ready, 0=Reading not ready                                  */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
  __IO uint16_t  HIGH_LIMIT;                        /*!< value is compared with TACHX_COUNTER field.                           */
  __I  uint16_t  RESERVED;
  __IO uint16_t  LOW_LIMIT;                         /*!< value is compared with TACHX_COUNTER field.                           */
} TACH_0_Type;


/* ================================================================================ */
/* ================                      PWM_0                     ================ */
/* ================================================================================ */


/**
  * @brief This block generates a PWM output that can be used to control 4-wire fans, blinking LEDs, and 
 other similar devices. Each PWM can generate an arbitrary duty cycle output at frequencies from less than 0.1 Hz to 24 MHz. 
 The PWM controller can also used to generate the PROCHOT output and Speaker output.  (PWM_0)
  */

typedef struct {                                    /*!< PWM_0 Structure                                                       */
  __IO uint32_t  COUNTER_ON_TIME;                   /*!< determine both frequency and duty cycle                               */
  __IO uint32_t  COUNTER_OFF_TIME;                  /*!< determine both frequency and duty cycle                               */
  
  union {
    __IO uint32_t  CONFIG;                          /*!< PWMx CONFIGURATION REGISTER                                           */
    
    struct {
      __IO uint32_t  EN         :  1;               /*!< 1=Enabled (default), 0=Disabled                                       */
      __IO uint32_t  CLK_SELECT :  1;               /*!< determines clock source, 1=CLOCK_LOW, 0=HIGH                          */
      __IO uint32_t  INVERT     :  1;               /*!< 1= PWM_OUTPUT ON State is active low, 0=high                          */
      __IO uint32_t  CLK_PRE_DIVIDER:  4;           /*!< Clock source is divided by Pre-Divider+1                              */
    } CONFIG_b;                                     /*!< BitSize                                                               */
  };
} PWM_0_Type;


/* ================================================================================ */
/* ================                     RPM_FAN                    ================ */
/* ================================================================================ */


/**
  * @brief The RPM-PWM Interface is an RPM based Fan Control Algorithm that monitors
 the fan's speed and automatically adjusts the drive to maintain the desired fan speed. This
 RPM based Fan Control Algorithm controls a PWM output based on a tachometer input.  (RPM_FAN)
  */

typedef struct {                                    /*!< RPM_FAN Structure                                                     */
  __IO uint8_t   SETTING;                           /*!< Drive = (FAN_SETTING VALUE/255) x 100%.                               */
  __IO uint8_t   PWM_DIVIDE;                        /*!< PWM_Frequency = base_clk / PWM_DIVIDE                                 */
  
  union {
    __IO uint16_t  CONFIGURATION;                   /*!< general operation of Fan Control Algorithm                            */
    
    struct {
      __IO uint16_t  UPDATE     :  3;               /*!< Determines base time between fan driver updates                       */
      __IO uint16_t  EDGES      :  2;               /*!< minimum number of edges that must be detected                         */
      __IO uint16_t  RANGE      :  2;               /*!< Adjusts the range of tachometer reading values.                       */
      __IO uint16_t  EN_ALGO    :  1;               /*!< Enables the RPM based Fan Control Algorithm.                          */
      __IO uint16_t  POLARITY   :  1;               /*!< 1: The Polarity of the PWM driver is inverted.                        */
      __IO uint16_t  ERR_RNG    :  2;               /*!< Control advanced options that affect error window.                    */
      __IO uint16_t  DER_OPT    :  2;               /*!< Control portion of RPM fan control algorithm                          */
      __IO uint16_t  DIS_GLITCH :  1;               /*!< 1: The glitch filter is disabled.                                     */
      __IO uint16_t  EN_RRC     :  1;               /*!< Enables the ramp rate control circuitry                               */
    } CONFIGURATION_b;                              /*!< BitSize                                                               */
  };
  __I  uint8_t   RESERVED;
  
  union {
    __IO uint8_t   GAIN;                            /*!< gain for proportional/integral portion                                */
    
    struct {
      __IO uint8_t   GAINP      :  2;               /*!< derivative gain term                                                  */
      __IO uint8_t   GAINI      :  2;               /*!< derivative gain term                                                  */
      __IO uint8_t   GAIND      :  2;               /*!< derivative gain term                                                  */
    } GAIN_b;                                       /*!< BitSize                                                               */
  };
  
  union {
    __IO uint8_t   SPIN_UP_CONFIGURATION;           /*!< settings of Spin Up Routine.                                          */
    
    struct {
      __IO uint8_t   SPINUP_TIME:  2;               /*!< maximum Spin Time that Spin Up Routine run                            */
      __IO uint8_t   SPIN_LVL   :  3;               /*!< final drive level used by the Spin Up Routine                         */
      __IO uint8_t   NOKICK     :  1;               /*!< 1: Spin Routine will not drive fan to 100%                            */
      __IO uint8_t   DRIVE_FAIL_CNT:  2;            /*!< update cycles are used for Drive Fail detection                       */
    } SPIN_UP_CONFIGURATION_b;                      /*!< BitSize                                                               */
  };
  __IO uint8_t   STEP;                              /*!< max step driver take between update                                   */
  __IO uint8_t   MINIMUM_DRIVE;                     /*!< minimum drive setting for Fan Algorithm.                              */
  __IO uint8_t   VALID_TACH_COUNT;                  /*!< max value to indicate fan spin properly                               */
  __IO uint16_t  DRIVE_FAIL_BAND;                   /*!< [15:3]counts for Drive Fail circuitry                                 */
  __IO uint16_t  TACH_TARGET;                       /*!< [12:0] The target tachometer value.                                   */
  __IO uint16_t  TACH_READING;                      /*!< [15:3]current tachometer reading value.                               */
  __IO uint8_t   DRIVER_BASE_FREQUENCY;             /*!< [1:0]frequency range of the PWM fan driver                            */
  
  union {
    __IO uint8_t   STATUS;                          /*!< The bits are routed to interrupts                                     */
    
    struct {
      __IO uint8_t   FAN_STALL  :  1;               /*!< 1 - Stalled fan detected. (R/WC)                                      */
      __IO uint8_t   FAN_SPIN   :  1;               /*!< 1: Spin up Routine not detect a valid tachometer                      */
           uint8_t              :  3;
      __IO uint8_t   DRIVE_FAIL :  1;               /*!< 1- cannot drive to target setting (R/WC)                              */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
} RPM_FAN_Type;


/* ================================================================================ */
/* ================                      SPI_0                     ================ */
/* ================================================================================ */


/**
  * @brief The General Purpose Serial Peripheral Interface (GP-SPI) may be used
 to communicate with various peripheral devices, e.g., EEPROMS, DACs, ADCs, that use a
 standard Serial Peripheral Interface.  (SPI_0)
  */

typedef struct {                                    /*!< SPI_0 Structure                                                       */
  __IO uint32_t  ENABLE;                            /*!< [0:0] 1=Enabled. device is fully operational                          */
  
  union {
    __IO uint32_t  CONTROL;                         /*!< SPI Control                                                           */
    
    struct {
      __IO uint32_t  LSBF       :  1;               /*!< Least Significant Bit First                                           */
      __IO uint32_t  BIOEN      :  1;               /*!< Bidirectional Output Enable control.                                  */
      __IO uint32_t  SPDIN_SELECT:  2;              /*!< [3:2]1xb=SPDIN1,SPDIN2. Select Dual Mode                              */
      __IO uint32_t  SOFT_RESET :  1;               /*!< Wt 1 to Soft Reset. self-clearing                                     */
      __IO uint32_t  AUTO_READ  :  1;               /*!< Auto Read Enable.                                                     */
      __IO uint32_t  CE         :  1;               /*!< SPI Chip Select Enable.                                               */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __I  uint32_t  STATUS;                          /*!< SPI Status                                                            */
    
    struct {
      __I  uint32_t  TXBE       :  1;               /*!< 1=TX_Data buffer is empty                                             */
      __I  uint32_t  RXBF       :  1;               /*!< 1=RX_Data buffer is full                                              */
      __I  uint32_t  ACTIVE     :  1;               /*!< ACTIVE status                                                         */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
  __IO uint32_t  TX_DATA;                           /*!< [7:0]wt to initiate a SPI transaction.                                */
  __IO uint32_t  RX_DATA;                           /*!< [7:0]read value returned by ext SPI device                            */
  
  union {
    __IO uint32_t  CLOCK_Control;                   /*!< SPI Clock Control.                                                    */
    
    struct {
      __IO uint32_t  TCLKPH     :  1;               /*!< Valid data is clocked out on 1st SPI_CLK                              */
      __IO uint32_t  RCLKPH     :  1;               /*!< Valid data is expected after 1st SPI_CLK edge                         */
      __IO uint32_t  CLKPOL     :  1;               /*!< SPI_CLK is high when 1st clock edge falling                           */
           uint32_t             :  1;
      __IO uint32_t  CLKSRC     :  1;               /*!< 1=2MHz, 0=48 MHz Ring Oscillator                                      */
    } CLOCK_Control_b;                              /*!< BitSize                                                               */
  };
  __IO uint32_t  CLOCK_GENERATOR;                   /*!< [5:0] PRELOAD SPI Clock Generator Preload value.                      */
} SPI_0_Type;


/* ================================================================================ */
/* ================                      LED_0                     ================ */
/* ================================================================================ */


/**
  * @brief The blinking/breathing hardware is implemented using a PWM. The PWM can be
 driven either by the 48 MHz clock or by a 32.768 KHz clock input. When driven by the 48 MHz clock,
 the PWM can be used as a standard 8-bit PWM in order to control a fan. When used to drive blinking
 or breathing LEDs, the 32.768 KHz clock source is used.  (LED_0)
  */

typedef struct {                                    /*!< LED_0 Structure                                                       */
  
  union {
    __IO uint32_t  CONFIG;                          /*!< LED Configuration                                                     */
    
    struct {
      __IO uint32_t  CONTROL    :  2;               /*!< 3=on,2=blinking,1=breathing,0=off                                     */
      __IO uint32_t  CLOCK_SOURCE:  1;              /*!< 1=48MHz, 0=32.768 KHz clock                                           */
      __IO uint32_t  SYNCHRONIZE:  1;               /*!< 1: all LEDs are reset to initial values.                              */
      __IO uint32_t  PWM_SIZE   :  2;               /*!< 3:reserved, 2:6bit, 1:7bit,0:8bit PWM                                 */
      __IO uint32_t  ENABLE_UPDATE:  1;             /*!< ENABLE_UPDATE                                                         */
      __O  uint32_t  RESET      :  1;               /*!< 1 resets PWM to default values self clearing                          */
      __IO uint32_t  WDT_RELOAD :  8;               /*!< PWM Watchdog Timer counter reload value                               */
      __IO uint32_t  SYMMETRY   :  1;               /*!< 1=rising/falling ramp are in Asymmetric mode                          */
    } CONFIG_b;                                     /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  LIMITS;                          /*!< LED Limits                                                            */
    
    struct {
      __IO uint32_t  MINIMUM    :  8;               /*!< wait in breathing if current cycle less this value                    */
      __IO uint32_t  MAXIMUM    :  8;               /*!< wait, breathing if current cycle great this value                     */
    } LIMITS_b;                                     /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  DELAY;                           /*!< LED Delay                                                             */
    
    struct {
      __IO uint32_t  LOWPULSE        : 12;          /*!< number to wait before updating current cycle                          */
      __IO uint32_t  HIGHPULSE       : 12;          /*!< number to wait before updating current cycle                          */
    } DELAY_b;                                      /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  UPDATE_STEPSIZE;                 /*!< provide amount duty cycle to adjust                                   */
    
    struct {
      __IO uint32_t  STEP0      :  4;               /*!< when the segment index is equal to 000.                               */
      __IO uint32_t  STEP1      :  4;               /*!< when the segment index is equal to 001.                               */
      __IO uint32_t  STEP2      :  4;               /*!< when the segment index is equal to 010.                               */
      __IO uint32_t  STEP3      :  4;               /*!< when the segment index is equal to 011.                               */
      __IO uint32_t  STEP4      :  4;               /*!< when the segment index is equal to 100.                               */
      __IO uint32_t  STEP5      :  4;               /*!< when the segment index is equal to 101                                */
      __IO uint32_t  STEP6      :  4;               /*!< when the segment index is equal to 110.                               */
      __IO uint32_t  STEP7      :  4;               /*!< when the segment index is equal to 111.                               */
    } UPDATE_STEPSIZE_b;                            /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  UPDATE_INTERVAL;                 /*!< LED Update Interval                                                   */
    
    struct {
      __IO uint32_t  INTERVAL0  :  4;               /*!< when the segment index is equal to 000b.                              */
      __IO uint32_t  INTERVAL1  :  4;               /*!< when the segment index is equal to 001b.                              */
      __IO uint32_t  INTERVAL2  :  4;               /*!< when the segment index is equal to 010b.                              */
      __IO uint32_t  INTERVAL3  :  4;               /*!< when the segment index is equal to 011b.                              */
      __IO uint32_t  INTERVAL4  :  4;               /*!< when the segment index is equal to 100b.                              */
      __IO uint32_t  INTERVAL5  :  4;               /*!< when the segment index is equal to 101b.                              */
      __IO uint32_t  INTERVAL6  :  4;               /*!< when the segment index is equal to 110b.                              */
      __IO uint32_t  INTERVAL7  :  4;               /*!< when the segment index is equal to 111b.                              */
    } UPDATE_INTERVAL_b;                            /*!< BitSize                                                               */
  };
} LED_0_Type;


/* ================================================================================ */
/* ================                      PS2_0                     ================ */
/* ================================================================================ */


/**
  * @brief There are four PS/2 Ports in the MEC1320 which are directly controlled
 by the EC. The hardware implementation eliminates the need to bit bang I/O ports to generate
 PS/2 traffic, however bit banging is available via the associated GPIO pins.  (PS2_0)
  */

typedef struct {                                    /*!< PS2_0 Structure                                                       */
  
  union {
    __I  uint32_t  RX_DATA;                         /*!< Data received from a peripheral                                       */
    __O  uint32_t  TX_DATA;                         /*!< Writes to start a transmission                                        */
  };
  
  union {
    __IO uint32_t  CONTROL;                         /*!< PS2 Control Register                                                  */
    
    struct {
      __IO uint32_t  TR         :  1;               /*!< PS/2 1:Transmit, 0:Receive data                                       */
      __IO uint32_t  EN         :  1;               /*!< 1: PS/2 Enable                                                        */
      __IO uint32_t  PARITY     :  2;               /*!< 00b=Receiver expects Odd Parity (default).                            */
      __IO uint32_t  STOP       :  2;               /*!< 00b=Receiver expects an active high stop bit                          */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  STATUS;                          /*!< PS2 Status Register                                                   */
    
    struct {
      __I  uint32_t  RDATA_RDY  :  1;               /*!< Data Ready. Reading Receive data to clears                            */
      __IO uint32_t  REC_TIMEOUT:  1;               /*!< REC_TIMEOUT is cleared when Status is read                            */
      __IO uint32_t  PE         :  1;               /*!< Parity Error                                                          */
      __IO uint32_t  FE         :  1;               /*!< Framing Error                                                         */
      __I  uint32_t  XMIT_IDLE  :  1;               /*!< 0=actively transmitting PS/2 data. 1=Idle                             */
      __IO uint32_t  XMIT_TIME_OUT:  1;             /*!< Transmitter Time-out                                                  */
      __I  uint32_t  RX_BUSY    :  1;               /*!< 0=actively receiving PS/2 data, 1=Idle                                */
      __IO uint32_t  XMIT_START_TIMEOUT:  1;        /*!< Transmit Start Timeout (over 25 ms)                                   */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
} PS2_0_Type;


/* ================================================================================ */
/* ================                     KEYSCAN                    ================ */
/* ================================================================================ */


/**
  * @brief The Keyboard Scan Interface block provides a register interface to the EC
 to directly scan an external keyboard matrix of size up to 18x8.  (KEYSCAN)
  */

typedef struct {                                    /*!< KEYSCAN Structure                                                     */
  __I  uint32_t  RESERVED;
  
  union {
    __IO uint32_t  CONTROL;                         /*!< KSO Select and control                                                */
    
    struct {
      __IO uint32_t  SELECT     :  5;               /*!< selects a KSO line (00000b=KSO[0] etc.)                               */
      __IO uint32_t  ALL        :  1;               /*!< 0=KSO_SELECT set KSO, 1=KSO[x] driven high                            */
      __IO uint32_t  KSEN       :  1;               /*!< 0=Keyboard scan enabled, 1=disabled.                                  */
      __IO uint32_t  INVERT     :  1;               /*!< 0=KSO[x] driven low, 1=high when selected.                            */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  __I  uint32_t  KSI;                               /*!< [7:0]returns the current state of KSI pins                            */
  __IO uint32_t  STATUS;                            /*!< [7:0]set on falling edge of KSI                                       */
  __IO uint32_t  INT_EN;                            /*!< [7:0]enables int due to H2L on a KSI                                  */
  __IO uint32_t  EXTENDED_CONTROL;                  /*!< [0:0] 1=Enable predrive on KSO pins.                                  */
} KEYSCAN_Type;


/* ================================================================================ */
/* ================                     BC_LINK                    ================ */
/* ================================================================================ */


/**
  * @brief This block provides BC-Link connectivity to a slave device. The BC-Link protocol
 includes a start bit to signal the beginning of a message and a turnaround (TAR) period
 for bus transfer between the Master and Companion devices.  (BC_LINK)
  */

typedef struct {                                    /*!< BC_LINK Structure                                                     */
  
  union {
    __IO uint32_t  STATUS;                          /*!< BC-Link Status                                                        */
    
    struct {
      __I  uint32_t  BUSY       :  1;               /*!< 1: BC is transferring data and on reset                               */
           uint32_t             :  3;
      __IO uint32_t  BUSY_CLR_INT_EN:  1;           /*!< enable for generating an interrupt                                    */
      __IO uint32_t  ERR_INT_EN :  1;               /*!< enable interrupt when BC_ERR bit set                                  */
      __IO uint32_t  ERROR      :  1;               /*!< indicates a BC Bus Error has occurred. (R/WC)                         */
      __IO uint32_t  RESET      :  1;               /*!< 1: Reset BC_Link Master Interface                                     */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
  __IO uint32_t  ADDRESS;                           /*!< Address in Companion for BC-Link                                      */
  __IO uint32_t  DATA_REG;                          /*!< hold data used in a BC-Link transaction.                              */
  __IO uint32_t  CLOCK_SELECT;                      /*!< [7:0] DIVIDER 48MHz/ (Divider +1).                                    */
} BC_LINK_Type;


/* ================================================================================ */
/* ================                      TFDP                      ================ */
/* ================================================================================ */


/**
  * @brief The TFDP serially transmits Embedded Controller (EC)-originated 
 diagnostic vectors to an external debug trace system.  (TFDP)
  */

typedef struct {                                    /*!< TFDP Structure                                                        */
  __IO uint8_t   DATA_REG;                          /*!< Debug data to be shifted out on TFDP port                             */
  __I  uint8_t   RESERVED[3];
  
  union {
    __IO uint8_t   CONTROL;                         /*!< Debug Control Register                                                */
    
    struct {
      __IO uint8_t   EN         :  1;               /*!< 1=Clock enabled, 0=Clock is disabled (Default)                        */
      __IO uint8_t   EDGE_SEL   :  1;               /*!< 1= shifted out on falling edge, 0= rising                             */
      __IO uint8_t   DIVSEL     :  2;               /*!< Clock Divider Select.                                                 */
      __IO uint8_t   IP_DELAY   :  3;               /*!< Inter-packet Delay.                                                   */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
} TFDP_Type;


/* ================================================================================ */
/* ================                       ADC                      ================ */
/* ================================================================================ */


/**
  * @brief This block is designed to convert external analog voltage readings into digital values.  (ADC)
  */

typedef struct {                                    /*!< ADC Structure                                                         */
  
  union {
    __IO uint32_t  CONTROL;                         /*!< control behavior of ADC                                               */
    
    struct {
      __IO uint32_t  ACTIVATE   :  1;               /*!< 1: ADC is enabled for operation.                                      */
      __IO uint32_t  START_SINGLE:  1;              /*!< 1: ADC Single Mode is enabled. self-clearing                          */
      __IO uint32_t  START_REPEAT:  1;              /*!< 1: ADC Repeat Mode is enabled.                                        */
      __IO uint32_t  POWER_SAVER_DIS:  1;           /*!< 0: Power saving enabled. 1: disabled.                                 */
      __IO uint32_t  SOFT_RESET :  1;               /*!< 1: reset of ADC                                                       */
           uint32_t             :  1;
      __IO uint32_t  REPEAT_DONE_STAT:  1;          /*!< 1: ADC repeat conversion is completed.(R/WC)                          */
      __IO uint32_t  SINGLE_DONE_STAT:  1;          /*!< 1: ADC single conversion is completed.(R/WC)                          */
    } CONTROL_b;                                    /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  DELAY;                           /*!< delay fm set Start_Repeat and conversion                              */
    
    struct {
      __IO uint32_t  START      : 16;               /*!< start delay before conv. when Start_Repeat=1                          */
      __IO uint32_t  REPEAT     : 16;               /*!< interval between conversion when Start_Repeat=1                       */
    } DELAY_b;                                      /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  STATUS;                          /*!< 1: conversion is complete (R/WC)                                      */
    
    struct {
      __IO uint32_t  CH0        :  1;               /*!< ADC_Ch0_Status                                                        */
      __IO uint32_t  CH1        :  1;               /*!< ADC_Ch1_Status                                                        */
      __IO uint32_t  CH2        :  1;               /*!< ADC_Ch2_Status                                                        */
      __IO uint32_t  CH3        :  1;               /*!< ADC_Ch3_Status                                                        */
      __IO uint32_t  CH4        :  1;               /*!< ADC_Ch4_Status                                                        */
    } STATUS_b;                                     /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  SINGLE_EN;                       /*!< ADC Single-Sample conversion control                                  */
    
    struct {
      __IO uint32_t  CH0        :  1;               /*!< Ch0 single conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH1        :  1;               /*!< Ch1 single conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH2        :  1;               /*!< Ch2 single conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH3        :  1;               /*!< Ch3 single conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH4        :  1;               /*!< Ch4 single conversions, 1:enabled/0:disabled                          */
    } SINGLE_EN_b;                                  /*!< BitSize                                                               */
  };
  
  union {
    __IO uint32_t  REPEAT;                          /*!< ADC channels repeat conversion control                                */
    
    struct {
      __IO uint32_t  CH0        :  1;               /*!< Ch0 repeat conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH1        :  1;               /*!< Ch1 repeat conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH2        :  1;               /*!< Ch2 repeat conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH3        :  1;               /*!< Ch3 repeat conversions, 1:enabled/0:disabled                          */
      __IO uint32_t  CH4        :  1;               /*!< Ch4 repeat conversions, 1:enabled/0:disabled                          */
    } REPEAT_b;                                     /*!< BitSize                                                               */
  };
  __IO uint32_t  READING[5];                        /*!< ADC channels 32-bit reading register.                                 */
} ADC_Type;


/* ================================================================================ */
/* ================                   EC_REG_BANK                  ================ */
/* ================================================================================ */


/**
  * @brief This block is designed to be accessed internally by the EC via the register interface.  (EC_REG_BANK)
  */

typedef struct {                                    /*!< EC_REG_BANK Structure                                                 */
  __I  uint32_t  RESERVED[5];
  __IO uint8_t   AHB_ERROR_CONTROL;                 /*!< 1: EC memory exceptions are disabled.                                 */
  __I  uint8_t   RESERVED1[3];
  __IO uint32_t  INTERRUPT_CONTROL;                 /*!< 1= Alternate NVIC vectors enabled                                     */
  __IO uint32_t  ETM_TRACE_ENABLE;                  /*!< 1= ARM TRACE port enabled                                             */
  __IO uint32_t  JTAG_Enable;                       /*!< 1= JTAG port enabled.                                                 */
  __I  uint32_t  RESERVED2;
  __IO uint32_t  WDT_EVENT_COUNT;                   /*!< [3:0]EC Rd/Wt are cleared to 0 on VCC1 POR                            */
  __I  uint32_t  RESERVED3[3];
  __IO uint32_t  ADC_VREF_PD;                       /*!< [0:0] ADC VREF Power down. 0=on 1=off                                 */
} EC_REG_BANK_Type;


/* ================================================================================ */
/* ================                      JTAG                      ================ */
/* ================================================================================ */


/**
  * @brief The Controller, which is an IEEE compliant JTAG Port, has implemented all
 the mandatory JTAG instructions. This interface may be used to access the embedded controller's
 test access port (TAP).  (JTAG)
  */

typedef struct {                                    /*!< JTAG Structure                                                        */
  __IO uint32_t  MESSAGE_OBF;                       /*!< JTAG Message OBF                                                      */
  __IO uint32_t  MESSAGE_IBF;                       /*!< JTAG Message IBF                                                      */
  __IO uint8_t   OBF_STATUS;                        /*!< JTAG OBF Status                                                       */
  __IO uint8_t   IBF_STATUS;                        /*!< JTAG IBF Status                                                       */
  __I  uint16_t  RESERVED;
  __IO uint32_t  DBG_CTRL;                          /*!< JTAG DBG Ctrl                                                         */
} JTAG_Type;


/*------------- Public Key Encryption Subsystem (PKE) -----------------------------*/
/** @addtogroup CEC1302_PKE Public Key Encryption (PKE)
  @{
*/
typedef struct
{
    __IO    uint32_t CONFIG;                /*!< Offset: 0x0000  Configuration */
    __IO    uint32_t COMMAND;               /*!< Offset: 0x0004  Command */
    __IO    uint32_t CONTROL;               /*!< Offset: 0x0008  Control */
    __I     uint32_t STATUS;                /*!< Offset: 0x000C  Status */
    __I     uint32_t VERSION;               /*!< Offset: 0x0010  Version */
    __IO    uint32_t LOAD_MICRO_CODE;       /*!< Offset: 0x0014  Load Micro Code */
} PKE_TypeDef;
/*@}*/ /* end of group CEC1302_PKE */

/*------------- Random Number Generator Subsystem (TRNG) -----------------------------*/
/** @addtogroup CEC1302_TRNG Random Number Generator (TRNG)
  @{
*/
typedef struct
{
    __IO    uint32_t CONTROL;               /*!< Offset: 0x0000  Control */
    __I     uint32_t FIFO_LEVEL;            /*!< Offset: 0x0004  FIFO Level */
    __I     uint32_t VERSION;               /*!< Offset: 0x0008  Version */
} TRNG_TypeDef;
/*@}*/ /* end of group CEC1302_TRNG */

/*------------- Hash Subsystem (HASH) -----------------------------*/
/** @addtogroup CEC1302_HASH Hash Security (HASH)
  @{
*/
typedef struct
{
    __IO    uint32_t SHA_MODE;              /*!< Offset: 0x0000  SHA Mode */
    __IO    uint32_t NB_BLOCK;              /*!< Offset: 0x0004  NbBlock */
    __IO    uint32_t CONTROL;               /*!< Offset: 0x0008  Config */
    __I     uint32_t STATUS;                /*!< Offset: 0x000C  Status, Read to clear interrupt */
    __I     uint32_t VERSION;               /*!< Offset: 0x0010  Version */
    __I     uint32_t GENERIC_VALUE;         /*!< Offset: 0x0014  Generic Value */
    __IO    uint32_t INIT_HASH_ADDR;        /*!< Offset: 0x0018  Initial Hash value Address */
    __IO    uint32_t DATA_SOURCE_ADDR;      /*!< Offset: 0x001C  Data to hash Address */
    __IO    uint32_t HASH_RESULT_ADDR;      /*!< Offset: 0x0020  Hash result address */
} HASH_TypeDef;
/*@}*/ /* end of group CEC1302_HASH */



/*------------- Advanced Encryption Subsystem (AES) -----------------------------*/
/** @addtogroup CEC1302_AES Advanced Encryption Subsys (AES)
  @{
*/

#define AES_MAX_KEY_WLEN    (8)
#define AES_MAX_IV_WLEN     (4)

typedef struct
{
    __IO    uint32_t CONFIG;                /*!< Offset: 0x0000  Configuration */
    __IO    uint32_t COMMAND;               /*!< Offset: 0x0004  Command */
    __IO    uint32_t CONTROL;               /*!< Offset: 0x0008  Control */
    __I     uint32_t STATUS;                /*!< Offset: 0x000C  Status */
    __I     uint32_t VERSION;               /*!< Offset: 0x0010  Version */
    __IO    uint32_t NB_HEADER;             /*!< Offset: 0x0014  Number of Headers */
    __IO    uint32_t LAST_HEADER;           /*!< Offset: 0x0018  Last Header */
    __IO    uint32_t NB_BLOCK;              /*!< Offset: 0x001C  Number of Blocks */
    __IO    uint32_t LAST_BLOCK;            /*!< Offset: 0x0020  Last Block */
    __IO    uint32_t DMA_IN;                /*!< Offset: 0x0024  DMA Input Address */
    __IO    uint32_t DMA_OUT;               /*!< Offset: 0x0028  DMA Output Address */
            uint32_t RESERVEDA[(0xFC - 0x2C)/4 + 1];
    __IO    uint32_t KEY1[AES_MAX_KEY_WLEN];/*!< Offset: 0x0100  KeyIn1[159:128] 
                                              !< Offset: 0x0104  KeyIn1[191:160] 
                                              !< Offset: 0x0108  KeyIn1[223:192] 
                                              !< Offset: 0x010C  KeyIn1[255:224] 
                                              !< Offset: 0x0110  KeyIn1[31:0] 
                                              !< Offset: 0x0114  KeyIn1[63:32] 
                                              !< Offset: 0x0118  KeyIn1[95:64] 
                                              !< Offset: 0x011C  KeyIn1[127:96] */
    __IO    uint32_t IV[AES_MAX_IV_WLEN];   /*!< Offset: 0x0120  IV[31:0] 
                                              !< Offset: 0x0124  IV[63:32] 
                                              !< Offset: 0x0128  IV[95:64] 
                                              !< Offset: 0x012C  IV[127:96] */
            uint32_t RESERVEDB[4];
    __IO    uint32_t KEY2[AES_MAX_KEY_WLEN];/*!< Offset: 0x0140  KeyIn1[159:128] 
                                              !< Offset: 0x0144  KeyIn1[191:160] 
                                              !< Offset: 0x0148  KeyIn1[223:192] 
                                              !< Offset: 0x014C  KeyIn1[255:224] 
                                              !< Offset: 0x0150  KeyIn1[31:0] 
                                              !< Offset: 0x0154  KeyIn1[63:32] 
                                              !< Offset: 0x0158  KeyIn1[95:64] 
                                              !< Offset: 0x015C  KeyIn1[127:96] */
} AES_TypeDef;
/*@}*/ /* end of group CEC1302_AES */

/* --------------------  End of section using anonymous unions  ------------------- */
#if defined(__CC_ARM)
  #pragma pop
#elif defined(__ICCARM__)
  /* leave anonymous unions enabled */
#elif defined(__GNUC__)
  /* anonymous unions are enabled by default */
#elif defined(__TMS470__)
  /* anonymous unions are enabled by default */
#elif defined(__TASKING__)
  #pragma warning restore
#else
  #warning Not supported compiler type
#endif



/* ================================================================================ */
/* ================          struct 'PCR' Position & Mask          ================ */
/* ================================================================================ */


/* --------------------------------  PCR_EC_SLP_EN  ------------------------------- */
#define PCR_EC_SLP_EN_INT_SLP_EN_Pos          (0UL)                     /*!< PCR EC_SLP_EN: INT_SLP_EN (Bit 0)                           */
#define PCR_EC_SLP_EN_INT_SLP_EN_Msk          (0x1UL)                   /*!< PCR EC_SLP_EN: INT_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_SLP_EN_PECI_SLP_EN_Pos         (1UL)                     /*!< PCR EC_SLP_EN: PECI_SLP_EN (Bit 1)                          */
#define PCR_EC_SLP_EN_PECI_SLP_EN_Msk         (0x2UL)                   /*!< PCR EC_SLP_EN: PECI_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_TACH0_SLP_EN_Pos        (2UL)                     /*!< PCR EC_SLP_EN: TACH0_SLP_EN (Bit 2)                         */
#define PCR_EC_SLP_EN_TACH0_SLP_EN_Msk        (0x4UL)                   /*!< PCR EC_SLP_EN: TACH0_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN_PWM0_SLP_EN_Pos         (4UL)                     /*!< PCR EC_SLP_EN: PWM0_SLP_EN (Bit 4)                          */
#define PCR_EC_SLP_EN_PWM0_SLP_EN_Msk         (0x10UL)                  /*!< PCR EC_SLP_EN: PWM0_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_PMC_SLP_EN_Pos          (5UL)                     /*!< PCR EC_SLP_EN: PMC_SLP_EN (Bit 5)                           */
#define PCR_EC_SLP_EN_PMC_SLP_EN_Msk          (0x20UL)                  /*!< PCR EC_SLP_EN: PMC_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_SLP_EN_DMA_SLP_EN_Pos          (6UL)                     /*!< PCR EC_SLP_EN: DMA_SLP_EN (Bit 6)                           */
#define PCR_EC_SLP_EN_DMA_SLP_EN_Msk          (0x40UL)                  /*!< PCR EC_SLP_EN: DMA_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_SLP_EN_TFDP_SLP_EN_Pos         (7UL)                     /*!< PCR EC_SLP_EN: TFDP_SLP_EN (Bit 7)                          */
#define PCR_EC_SLP_EN_TFDP_SLP_EN_Msk         (0x80UL)                  /*!< PCR EC_SLP_EN: TFDP_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_PROCESSOR_SLP_EN_Pos    (8UL)                     /*!< PCR EC_SLP_EN: PROCESSOR_SLP_EN (Bit 8)                     */
#define PCR_EC_SLP_EN_PROCESSOR_SLP_EN_Msk    (0x100UL)                 /*!< PCR EC_SLP_EN: PROCESSOR_SLP_EN (Bitfield-Mask: 0x01)       */
#define PCR_EC_SLP_EN_WDT_SLP_EN_Pos          (9UL)                     /*!< PCR EC_SLP_EN: WDT_SLP_EN (Bit 9)                           */
#define PCR_EC_SLP_EN_WDT_SLP_EN_Msk          (0x200UL)                 /*!< PCR EC_SLP_EN: WDT_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_SLP_EN_SMB0_SLP_EN_Pos         (10UL)                    /*!< PCR EC_SLP_EN: SMB0_SLP_EN (Bit 10)                         */
#define PCR_EC_SLP_EN_SMB0_SLP_EN_Msk         (0x400UL)                 /*!< PCR EC_SLP_EN: SMB0_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_TACH1_SLP_EN_Pos        (11UL)                    /*!< PCR EC_SLP_EN: TACH1_SLP_EN (Bit 11)                        */
#define PCR_EC_SLP_EN_TACH1_SLP_EN_Msk        (0x800UL)                 /*!< PCR EC_SLP_EN: TACH1_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN_PWM1_SLP_EN_Pos         (20UL)                    /*!< PCR EC_SLP_EN: PWM1_SLP_EN (Bit 20)                         */
#define PCR_EC_SLP_EN_PWM1_SLP_EN_Msk         (0x100000UL)              /*!< PCR EC_SLP_EN: PWM1_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_PWM2_SLP_EN_Pos         (21UL)                    /*!< PCR EC_SLP_EN: PWM2_SLP_EN (Bit 21)                         */
#define PCR_EC_SLP_EN_PWM2_SLP_EN_Msk         (0x200000UL)              /*!< PCR EC_SLP_EN: PWM2_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_PWM3_SLP_EN_Pos         (22UL)                    /*!< PCR EC_SLP_EN: PWM3_SLP_EN (Bit 22)                         */
#define PCR_EC_SLP_EN_PWM3_SLP_EN_Msk         (0x400000UL)              /*!< PCR EC_SLP_EN: PWM3_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN_EC_REG_BANK_SLP_EN_Pos  (29UL)                    /*!< PCR EC_SLP_EN: EC_REG_BANK_SLP_EN (Bit 29)                  */
#define PCR_EC_SLP_EN_EC_REG_BANK_SLP_EN_Msk  (0x20000000UL)            /*!< PCR EC_SLP_EN: EC_REG_BANK_SLP_EN (Bitfield-Mask: 0x01)     */
#define PCR_EC_SLP_EN_TIMER16_0_SLP_EN_Pos    (30UL)                    /*!< PCR EC_SLP_EN: TIMER16_0_SLP_EN (Bit 30)                    */
#define PCR_EC_SLP_EN_TIMER16_0_SLP_EN_Msk    (0x40000000UL)            /*!< PCR EC_SLP_EN: TIMER16_0_SLP_EN (Bitfield-Mask: 0x01)       */
#define PCR_EC_SLP_EN_TIMER16_1_SLP_EN_Pos    (31UL)                    /*!< PCR EC_SLP_EN: TIMER16_1_SLP_EN (Bit 31)                    */
#define PCR_EC_SLP_EN_TIMER16_1_SLP_EN_Msk    (0x80000000UL)            /*!< PCR EC_SLP_EN: TIMER16_1_SLP_EN (Bitfield-Mask: 0x01)       */

/* -----------------------------  PCR_EC_CLK_REQ_STS  ----------------------------- */
#define PCR_EC_CLK_REQ_STS_INT_CLK_REQ_Pos    (0UL)                     /*!< PCR EC_CLK_REQ_STS: INT_CLK_REQ (Bit 0)                     */
#define PCR_EC_CLK_REQ_STS_INT_CLK_REQ_Msk    (0x1UL)                   /*!< PCR EC_CLK_REQ_STS: INT_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_EC_CLK_REQ_STS_PECI_CLK_REQ_Pos   (1UL)                     /*!< PCR EC_CLK_REQ_STS: PECI_CLK_REQ (Bit 1)                    */
#define PCR_EC_CLK_REQ_STS_PECI_CLK_REQ_Msk   (0x2UL)                   /*!< PCR EC_CLK_REQ_STS: PECI_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_TACH0_CLK_REQ_Pos  (2UL)                     /*!< PCR EC_CLK_REQ_STS: TACH0_CLK_REQ (Bit 2)                   */
#define PCR_EC_CLK_REQ_STS_TACH0_CLK_REQ_Msk  (0x4UL)                   /*!< PCR EC_CLK_REQ_STS: TACH0_CLK_REQ (Bitfield-Mask: 0x01)     */
#define PCR_EC_CLK_REQ_STS_PWM0_CLK_REQ_Pos   (4UL)                     /*!< PCR EC_CLK_REQ_STS: PWM0_CLK_REQ (Bit 4)                    */
#define PCR_EC_CLK_REQ_STS_PWM0_CLK_REQ_Msk   (0x10UL)                  /*!< PCR EC_CLK_REQ_STS: PWM0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_PMC_CLK_REQ_Pos    (5UL)                     /*!< PCR EC_CLK_REQ_STS: PMC_CLK_REQ (Bit 5)                     */
#define PCR_EC_CLK_REQ_STS_PMC_CLK_REQ_Msk    (0x20UL)                  /*!< PCR EC_CLK_REQ_STS: PMC_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_EC_CLK_REQ_STS_DMA_CLK_REQ_Pos    (6UL)                     /*!< PCR EC_CLK_REQ_STS: DMA_CLK_REQ (Bit 6)                     */
#define PCR_EC_CLK_REQ_STS_DMA_CLK_REQ_Msk    (0x40UL)                  /*!< PCR EC_CLK_REQ_STS: DMA_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_EC_CLK_REQ_STS_TFDP_CLK_REQ_Pos   (7UL)                     /*!< PCR EC_CLK_REQ_STS: TFDP_CLK_REQ (Bit 7)                    */
#define PCR_EC_CLK_REQ_STS_TFDP_CLK_REQ_Msk   (0x80UL)                  /*!< PCR EC_CLK_REQ_STS: TFDP_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_PROCESSOR_CLK_REQ_Pos (8UL)                  /*!< PCR EC_CLK_REQ_STS: PROCESSOR_CLK_REQ (Bit 8)               */
#define PCR_EC_CLK_REQ_STS_PROCESSOR_CLK_REQ_Msk (0x100UL)              /*!< PCR EC_CLK_REQ_STS: PROCESSOR_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ_STS_WDT_CLK_REQ_Pos    (9UL)                     /*!< PCR EC_CLK_REQ_STS: WDT_CLK_REQ (Bit 9)                     */
#define PCR_EC_CLK_REQ_STS_WDT_CLK_REQ_Msk    (0x200UL)                 /*!< PCR EC_CLK_REQ_STS: WDT_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_EC_CLK_REQ_STS_SMB0_CLK_REQ_Pos   (10UL)                    /*!< PCR EC_CLK_REQ_STS: SMB0_CLK_REQ (Bit 10)                   */
#define PCR_EC_CLK_REQ_STS_SMB0_CLK_REQ_Msk   (0x400UL)                 /*!< PCR EC_CLK_REQ_STS: SMB0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_TACH1_CLK_REQ_Pos  (11UL)                    /*!< PCR EC_CLK_REQ_STS: TACH1_CLK_REQ (Bit 11)                  */
#define PCR_EC_CLK_REQ_STS_TACH1_CLK_REQ_Msk  (0x800UL)                 /*!< PCR EC_CLK_REQ_STS: TACH1_CLK_REQ (Bitfield-Mask: 0x01)     */
#define PCR_EC_CLK_REQ_STS_PWM1_CLK_REQ_Pos   (20UL)                    /*!< PCR EC_CLK_REQ_STS: PWM1_CLK_REQ (Bit 20)                   */
#define PCR_EC_CLK_REQ_STS_PWM1_CLK_REQ_Msk   (0x100000UL)              /*!< PCR EC_CLK_REQ_STS: PWM1_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_PWM2_CLK_REQ_Pos   (21UL)                    /*!< PCR EC_CLK_REQ_STS: PWM2_CLK_REQ (Bit 21)                   */
#define PCR_EC_CLK_REQ_STS_PWM2_CLK_REQ_Msk   (0x200000UL)              /*!< PCR EC_CLK_REQ_STS: PWM2_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_PWM3_CLK_REQ_Pos   (22UL)                    /*!< PCR EC_CLK_REQ_STS: PWM3_CLK_REQ (Bit 22)                   */
#define PCR_EC_CLK_REQ_STS_PWM3_CLK_REQ_Msk   (0x400000UL)              /*!< PCR EC_CLK_REQ_STS: PWM3_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ_STS_EC_REG_BANK_CLK_REQ_Pos (29UL)               /*!< PCR EC_CLK_REQ_STS: EC_REG_BANK_CLK_REQ (Bit 29)            */
#define PCR_EC_CLK_REQ_STS_EC_REG_BANK_CLK_REQ_Msk (0x20000000UL)       /*!< PCR EC_CLK_REQ_STS: EC_REG_BANK_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ_STS_TIMER16_0_CLK_REQ_Pos (30UL)                 /*!< PCR EC_CLK_REQ_STS: TIMER16_0_CLK_REQ (Bit 30)              */
#define PCR_EC_CLK_REQ_STS_TIMER16_0_CLK_REQ_Msk (0x40000000UL)         /*!< PCR EC_CLK_REQ_STS: TIMER16_0_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ_STS_TIMER16_1_CLK_REQ_Pos (31UL)                 /*!< PCR EC_CLK_REQ_STS: TIMER16_1_CLK_REQ (Bit 31)              */
#define PCR_EC_CLK_REQ_STS_TIMER16_1_CLK_REQ_Msk (0x80000000UL)         /*!< PCR EC_CLK_REQ_STS: TIMER16_1_CLK_REQ (Bitfield-Mask: 0x01) */

/* -------------------------------  PCR_HOST_SLP_EN  ------------------------------ */
#define PCR_HOST_SLP_EN_LPC_SLP_EN_Pos        (0UL)                     /*!< PCR HOST_SLP_EN: LPC_SLP_EN (Bit 0)                         */
#define PCR_HOST_SLP_EN_LPC_SLP_EN_Msk        (0x1UL)                   /*!< PCR HOST_SLP_EN: LPC_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_HOST_SLP_EN_UART_0_SLP_EN_Pos     (1UL)                     /*!< PCR HOST_SLP_EN: UART_0_SLP_EN (Bit 1)                      */
#define PCR_HOST_SLP_EN_UART_0_SLP_EN_Msk     (0x2UL)                   /*!< PCR HOST_SLP_EN: UART_0_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_HOST_SLP_EN_GLBL_CFG_SLP_EN_Pos   (12UL)                    /*!< PCR HOST_SLP_EN: GLBL_CFG_SLP_EN (Bit 12)                   */
#define PCR_HOST_SLP_EN_GLBL_CFG_SLP_EN_Msk   (0x1000UL)                /*!< PCR HOST_SLP_EN: GLBL_CFG_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_HOST_SLP_EN_ACPI_EC_0_SLP_EN_Pos  (13UL)                    /*!< PCR HOST_SLP_EN: ACPI_EC_0_SLP_EN (Bit 13)                  */
#define PCR_HOST_SLP_EN_ACPI_EC_0_SLP_EN_Msk  (0x2000UL)                /*!< PCR HOST_SLP_EN: ACPI_EC_0_SLP_EN (Bitfield-Mask: 0x01)     */
#define PCR_HOST_SLP_EN_ACPI_EC_1_SLP_EN_Pos  (14UL)                    /*!< PCR HOST_SLP_EN: ACPI_EC_1_SLP_EN (Bit 14)                  */
#define PCR_HOST_SLP_EN_ACPI_EC_1_SLP_EN_Msk  (0x4000UL)                /*!< PCR HOST_SLP_EN: ACPI_EC_1_SLP_EN (Bitfield-Mask: 0x01)     */
#define PCR_HOST_SLP_EN_ACPI_PM1_SLP_EN_Pos   (15UL)                    /*!< PCR HOST_SLP_EN: ACPI_PM1_SLP_EN (Bit 15)                   */
#define PCR_HOST_SLP_EN_ACPI_PM1_SLP_EN_Msk   (0x8000UL)                /*!< PCR HOST_SLP_EN: ACPI_PM1_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_HOST_SLP_EN_KBCEM_SLP_EN_Pos      (16UL)                    /*!< PCR HOST_SLP_EN: KBCEM_SLP_EN (Bit 16)                      */
#define PCR_HOST_SLP_EN_KBCEM_SLP_EN_Msk      (0x10000UL)               /*!< PCR HOST_SLP_EN: KBCEM_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_HOST_SLP_EN_RTC_SLP_EN_Pos        (18UL)                    /*!< PCR HOST_SLP_EN: RTC_SLP_EN (Bit 18)                        */
#define PCR_HOST_SLP_EN_RTC_SLP_EN_Msk        (0x40000UL)               /*!< PCR HOST_SLP_EN: RTC_SLP_EN (Bitfield-Mask: 0x01)           */

/* ------------------------------  PCR_HOST_CLK_REQ  ------------------------------ */
#define PCR_HOST_CLK_REQ_LPC_CLK_REQ_Pos      (0UL)                     /*!< PCR HOST_CLK_REQ: LPC_CLK_REQ (Bit 0)                       */
#define PCR_HOST_CLK_REQ_LPC_CLK_REQ_Msk      (0x1UL)                   /*!< PCR HOST_CLK_REQ: LPC_CLK_REQ (Bitfield-Mask: 0x01)         */
#define PCR_HOST_CLK_REQ_UART_0_CLK_REQ_Pos   (1UL)                     /*!< PCR HOST_CLK_REQ: UART_0_CLK_REQ (Bit 1)                    */
#define PCR_HOST_CLK_REQ_UART_0_CLK_REQ_Msk   (0x2UL)                   /*!< PCR HOST_CLK_REQ: UART_0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_HOST_CLK_REQ_GLBL_CFG_CLK_REQ_Pos (12UL)                    /*!< PCR HOST_CLK_REQ: GLBL_CFG_CLK_REQ (Bit 12)                 */
#define PCR_HOST_CLK_REQ_GLBL_CFG_CLK_REQ_Msk (0x1000UL)                /*!< PCR HOST_CLK_REQ: GLBL_CFG_CLK_REQ (Bitfield-Mask: 0x01)    */
#define PCR_HOST_CLK_REQ_ACPI_EC_0_CLK_REQ_Pos (13UL)                   /*!< PCR HOST_CLK_REQ: ACPI_EC_0_CLK_REQ (Bit 13)                */
#define PCR_HOST_CLK_REQ_ACPI_EC_0_CLK_REQ_Msk (0x2000UL)               /*!< PCR HOST_CLK_REQ: ACPI_EC_0_CLK_REQ (Bitfield-Mask: 0x01)   */
#define PCR_HOST_CLK_REQ_ACPI_EC_1_CLK_REQ_Pos (14UL)                   /*!< PCR HOST_CLK_REQ: ACPI_EC_1_CLK_REQ (Bit 14)                */
#define PCR_HOST_CLK_REQ_ACPI_EC_1_CLK_REQ_Msk (0x4000UL)               /*!< PCR HOST_CLK_REQ: ACPI_EC_1_CLK_REQ (Bitfield-Mask: 0x01)   */
#define PCR_HOST_CLK_REQ_ACPI_PM1_CLK_REQ_Pos (15UL)                    /*!< PCR HOST_CLK_REQ: ACPI_PM1_CLK_REQ (Bit 15)                 */
#define PCR_HOST_CLK_REQ_ACPI_PM1_CLK_REQ_Msk (0x8000UL)                /*!< PCR HOST_CLK_REQ: ACPI_PM1_CLK_REQ (Bitfield-Mask: 0x01)    */
#define PCR_HOST_CLK_REQ_KBCEM_CLK_REQ_Pos    (16UL)                    /*!< PCR HOST_CLK_REQ: KBCEM_CLK_REQ (Bit 16)                    */
#define PCR_HOST_CLK_REQ_KBCEM_CLK_REQ_Msk    (0x10000UL)               /*!< PCR HOST_CLK_REQ: KBCEM_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_HOST_CLK_REQ_RTC_CLK_REQ_Pos      (18UL)                    /*!< PCR HOST_CLK_REQ: RTC_CLK_REQ (Bit 18)                      */
#define PCR_HOST_CLK_REQ_RTC_CLK_REQ_Msk      (0x40000UL)               /*!< PCR HOST_CLK_REQ: RTC_CLK_REQ (Bitfield-Mask: 0x01)         */

/* ------------------------------  PCR_SYS_SLP_CNTRL  ----------------------------- */
#define PCR_SYS_SLP_CNTRL_ROSC_PD_Pos         (0UL)                     /*!< PCR SYS_SLP_CNTRL: ROSC_PD (Bit 0)                          */
#define PCR_SYS_SLP_CNTRL_ROSC_PD_Msk         (0x1UL)                   /*!< PCR SYS_SLP_CNTRL: ROSC_PD (Bitfield-Mask: 0x01)            */
#define PCR_SYS_SLP_CNTRL_ROSC_GATE_Pos       (1UL)                     /*!< PCR SYS_SLP_CNTRL: ROSC_GATE (Bit 1)                        */
#define PCR_SYS_SLP_CNTRL_ROSC_GATE_Msk       (0x2UL)                   /*!< PCR SYS_SLP_CNTRL: ROSC_GATE (Bitfield-Mask: 0x01)          */
#define PCR_SYS_SLP_CNTRL_REGULATOR_STDBY_Pos (2UL)                     /*!< PCR SYS_SLP_CNTRL: REGULATOR_STDBY (Bit 2)                  */
#define PCR_SYS_SLP_CNTRL_REGULATOR_STDBY_Msk (0x4UL)                   /*!< PCR SYS_SLP_CNTRL: REGULATOR_STDBY (Bitfield-Mask: 0x01)    */

/* -------------------------------  PCR_EC_SLP_EN2  ------------------------------- */
#define PCR_EC_SLP_EN2_ADC_SLP_EN_Pos         (3UL)                     /*!< PCR EC_SLP_EN2: ADC_SLP_EN (Bit 3)                          */
#define PCR_EC_SLP_EN2_ADC_SLP_EN_Msk         (0x8UL)                   /*!< PCR EC_SLP_EN2: ADC_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN2_PS2_0_SLP_EN_Pos       (5UL)                     /*!< PCR EC_SLP_EN2: PS2_0_SLP_EN (Bit 5)                        */
#define PCR_EC_SLP_EN2_PS2_0_SLP_EN_Msk       (0x20UL)                  /*!< PCR EC_SLP_EN2: PS2_0_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_SLP_EN2_PS2_1_SLP_EN_Pos       (6UL)                     /*!< PCR EC_SLP_EN2: PS2_1_SLP_EN (Bit 6)                        */
#define PCR_EC_SLP_EN2_PS2_1_SLP_EN_Msk       (0x40UL)                  /*!< PCR EC_SLP_EN2: PS2_1_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_SLP_EN2_PS2_2_SLP_EN_Pos       (7UL)                     /*!< PCR EC_SLP_EN2: PS2_2_SLP_EN (Bit 7)                        */
#define PCR_EC_SLP_EN2_PS2_2_SLP_EN_Msk       (0x80UL)                  /*!< PCR EC_SLP_EN2: PS2_2_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_SLP_EN2_PS2_3_SLP_EN_Pos       (8UL)                     /*!< PCR EC_SLP_EN2: PS2_3_SLP_EN (Bit 8)                        */
#define PCR_EC_SLP_EN2_PS2_3_SLP_EN_Msk       (0x100UL)                 /*!< PCR EC_SLP_EN2: PS2_3_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_SLP_EN2_SPI0_SLP_EN_Pos        (9UL)                     /*!< PCR EC_SLP_EN2: SPI0_SLP_EN (Bit 9)                         */
#define PCR_EC_SLP_EN2_SPI0_SLP_EN_Msk        (0x200UL)                 /*!< PCR EC_SLP_EN2: SPI0_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_HTIMER_SLP_EN_Pos      (10UL)                    /*!< PCR EC_SLP_EN2: HTIMER_SLP_EN (Bit 10)                      */
#define PCR_EC_SLP_EN2_HTIMER_SLP_EN_Msk      (0x400UL)                 /*!< PCR EC_SLP_EN2: HTIMER_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_EC_SLP_EN2_KEYSCAN_SLP_EN_Pos     (11UL)                    /*!< PCR EC_SLP_EN2: KEYSCAN_SLP_EN (Bit 11)                     */
#define PCR_EC_SLP_EN2_KEYSCAN_SLP_EN_Msk     (0x800UL)                 /*!< PCR EC_SLP_EN2: KEYSCAN_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_EC_SLP_EN2_RPMPWM_SLP_EN_Pos      (12UL)                    /*!< PCR EC_SLP_EN2: RPMPWM_SLP_EN (Bit 12)                      */
#define PCR_EC_SLP_EN2_RPMPWM_SLP_EN_Msk      (0x1000UL)                /*!< PCR EC_SLP_EN2: RPMPWM_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_EC_SLP_EN2_SMB1_SLP_EN_Pos        (13UL)                    /*!< PCR EC_SLP_EN2: SMB1_SLP_EN (Bit 13)                        */
#define PCR_EC_SLP_EN2_SMB1_SLP_EN_Msk        (0x2000UL)                /*!< PCR EC_SLP_EN2: SMB1_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_SMB2_SLP_EN_Pos        (14UL)                    /*!< PCR EC_SLP_EN2: SMB2_SLP_EN (Bit 14)                        */
#define PCR_EC_SLP_EN2_SMB2_SLP_EN_Msk        (0x4000UL)                /*!< PCR EC_SLP_EN2: SMB2_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_SMB3_SLP_EN_Pos        (15UL)                    /*!< PCR EC_SLP_EN2: SMB3_SLP_EN (Bit 15)                        */
#define PCR_EC_SLP_EN2_SMB3_SLP_EN_Msk        (0x8000UL)                /*!< PCR EC_SLP_EN2: SMB3_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_LED0_SLP_EN_Pos        (16UL)                    /*!< PCR EC_SLP_EN2: LED0_SLP_EN (Bit 16)                        */
#define PCR_EC_SLP_EN2_LED0_SLP_EN_Msk        (0x10000UL)               /*!< PCR EC_SLP_EN2: LED0_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_LED1_SLP_EN_Pos        (17UL)                    /*!< PCR EC_SLP_EN2: LED1_SLP_EN (Bit 17)                        */
#define PCR_EC_SLP_EN2_LED1_SLP_EN_Msk        (0x20000UL)               /*!< PCR EC_SLP_EN2: LED1_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_LED2_SLP_EN_Pos        (18UL)                    /*!< PCR EC_SLP_EN2: LED2_SLP_EN (Bit 18)                        */
#define PCR_EC_SLP_EN2_LED2_SLP_EN_Msk        (0x40000UL)               /*!< PCR EC_SLP_EN2: LED2_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_BCM_SLP_EN_Pos         (19UL)                    /*!< PCR EC_SLP_EN2: BCM_SLP_EN (Bit 19)                         */
#define PCR_EC_SLP_EN2_BCM_SLP_EN_Msk         (0x80000UL)               /*!< PCR EC_SLP_EN2: BCM_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_SLP_EN2_SPI1_SLP_EN_Pos        (20UL)                    /*!< PCR EC_SLP_EN2: SPI1_SLP_EN (Bit 20)                        */
#define PCR_EC_SLP_EN2_SPI1_SLP_EN_Msk        (0x100000UL)              /*!< PCR EC_SLP_EN2: SPI1_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_SLP_EN2_TIMER16_2_SLP_EN_Pos   (21UL)                    /*!< PCR EC_SLP_EN2: TIMER16_2_SLP_EN (Bit 21)                   */
#define PCR_EC_SLP_EN2_TIMER16_2_SLP_EN_Msk   (0x200000UL)              /*!< PCR EC_SLP_EN2: TIMER16_2_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_SLP_EN2_TIMER16_3_SLP_EN_Pos   (22UL)                    /*!< PCR EC_SLP_EN2: TIMER16_3_SLP_EN (Bit 22)                   */
#define PCR_EC_SLP_EN2_TIMER16_3_SLP_EN_Msk   (0x400000UL)              /*!< PCR EC_SLP_EN2: TIMER16_3_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_SLP_EN2_TIMER32_0_SLP_EN_Pos   (23UL)                    /*!< PCR EC_SLP_EN2: TIMER32_0_SLP_EN (Bit 23)                   */
#define PCR_EC_SLP_EN2_TIMER32_0_SLP_EN_Msk   (0x800000UL)              /*!< PCR EC_SLP_EN2: TIMER32_0_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_SLP_EN2_TIMER32_1_SLP_EN_Pos   (24UL)                    /*!< PCR EC_SLP_EN2: TIMER32_1_SLP_EN (Bit 24)                   */
#define PCR_EC_SLP_EN2_TIMER32_1_SLP_EN_Msk   (0x1000000UL)             /*!< PCR EC_SLP_EN2: TIMER32_1_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_SLP_EN2_LED3_SLP_EN_Pos        (25UL)                    /*!< PCR EC_SLP_EN2: LED3_SLP_EN (Bit 25)                        */
#define PCR_EC_SLP_EN2_LED3_SLP_EN_Msk        (0x2000000UL)             /*!< PCR EC_SLP_EN2: LED3_SLP_EN (Bitfield-Mask: 0x01)           */

/* -----------------------------  PCR_EC_CLK_REQ2_STS  ---------------------------- */
#define PCR_EC_CLK_REQ2_STS_ADC_CLK_REQ_Pos   (3UL)                     /*!< PCR EC_CLK_REQ2_STS: ADC_CLK_REQ (Bit 3)                    */
#define PCR_EC_CLK_REQ2_STS_ADC_CLK_REQ_Msk   (0x8UL)                   /*!< PCR EC_CLK_REQ2_STS: ADC_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_EC_CLK_REQ2_STS_PS2_0_SLP_CLK_REQ_Pos (5UL)                 /*!< PCR EC_CLK_REQ2_STS: PS2_0_SLP_CLK_REQ (Bit 5)              */
#define PCR_EC_CLK_REQ2_STS_PS2_0_SLP_CLK_REQ_Msk (0x20UL)              /*!< PCR EC_CLK_REQ2_STS: PS2_0_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_PS2_1_SLP_CLK_REQ_Pos (6UL)                 /*!< PCR EC_CLK_REQ2_STS: PS2_1_SLP_CLK_REQ (Bit 6)              */
#define PCR_EC_CLK_REQ2_STS_PS2_1_SLP_CLK_REQ_Msk (0x40UL)              /*!< PCR EC_CLK_REQ2_STS: PS2_1_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_PS2_2_SLP_CLK_REQ_Pos (7UL)                 /*!< PCR EC_CLK_REQ2_STS: PS2_2_SLP_CLK_REQ (Bit 7)              */
#define PCR_EC_CLK_REQ2_STS_PS2_2_SLP_CLK_REQ_Msk (0x80UL)              /*!< PCR EC_CLK_REQ2_STS: PS2_2_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_PS2_3_SLP_CLK_REQ_Pos (8UL)                 /*!< PCR EC_CLK_REQ2_STS: PS2_3_SLP_CLK_REQ (Bit 8)              */
#define PCR_EC_CLK_REQ2_STS_PS2_3_SLP_CLK_REQ_Msk (0x100UL)             /*!< PCR EC_CLK_REQ2_STS: PS2_3_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_SPI0_SLP_CLK_REQ_Pos (9UL)                  /*!< PCR EC_CLK_REQ2_STS: SPI0_SLP_CLK_REQ (Bit 9)               */
#define PCR_EC_CLK_REQ2_STS_SPI0_SLP_CLK_REQ_Msk (0x200UL)              /*!< PCR EC_CLK_REQ2_STS: SPI0_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_HTIMER_SLP_CLK_REQ_Pos (10UL)               /*!< PCR EC_CLK_REQ2_STS: HTIMER_SLP_CLK_REQ (Bit 10)            */
#define PCR_EC_CLK_REQ2_STS_HTIMER_SLP_CLK_REQ_Msk (0x400UL)            /*!< PCR EC_CLK_REQ2_STS: HTIMER_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_KEYSCAN_SLP_CLK_REQ_Pos (11UL)              /*!< PCR EC_CLK_REQ2_STS: KEYSCAN_SLP_CLK_REQ (Bit 11)           */
#define PCR_EC_CLK_REQ2_STS_KEYSCAN_SLP_CLK_REQ_Msk (0x800UL)           /*!< PCR EC_CLK_REQ2_STS: KEYSCAN_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_RPMPWM_SLP_CLK_REQ_Pos (12UL)               /*!< PCR EC_CLK_REQ2_STS: RPMPWM_SLP_CLK_REQ (Bit 12)            */
#define PCR_EC_CLK_REQ2_STS_RPMPWM_SLP_CLK_REQ_Msk (0x1000UL)           /*!< PCR EC_CLK_REQ2_STS: RPMPWM_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_SMB1_SLP_CLK_REQ_Pos (13UL)                 /*!< PCR EC_CLK_REQ2_STS: SMB1_SLP_CLK_REQ (Bit 13)              */
#define PCR_EC_CLK_REQ2_STS_SMB1_SLP_CLK_REQ_Msk (0x2000UL)             /*!< PCR EC_CLK_REQ2_STS: SMB1_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_SMB2_SLP_CLK_REQ_Pos (14UL)                 /*!< PCR EC_CLK_REQ2_STS: SMB2_SLP_CLK_REQ (Bit 14)              */
#define PCR_EC_CLK_REQ2_STS_SMB2_SLP_CLK_REQ_Msk (0x4000UL)             /*!< PCR EC_CLK_REQ2_STS: SMB2_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_SMB3_SLP_CLK_REQ_Pos (15UL)                 /*!< PCR EC_CLK_REQ2_STS: SMB3_SLP_CLK_REQ (Bit 15)              */
#define PCR_EC_CLK_REQ2_STS_SMB3_SLP_CLK_REQ_Msk (0x8000UL)             /*!< PCR EC_CLK_REQ2_STS: SMB3_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_LED0_SLP_CLK_REQ_Pos (16UL)                 /*!< PCR EC_CLK_REQ2_STS: LED0_SLP_CLK_REQ (Bit 16)              */
#define PCR_EC_CLK_REQ2_STS_LED0_SLP_CLK_REQ_Msk (0x10000UL)            /*!< PCR EC_CLK_REQ2_STS: LED0_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_LED1_SLP_CLK_REQ_Pos (17UL)                 /*!< PCR EC_CLK_REQ2_STS: LED1_SLP_CLK_REQ (Bit 17)              */
#define PCR_EC_CLK_REQ2_STS_LED1_SLP_CLK_REQ_Msk (0x20000UL)            /*!< PCR EC_CLK_REQ2_STS: LED1_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_LED2_SLP_CLK_REQ_Pos (18UL)                 /*!< PCR EC_CLK_REQ2_STS: LED2_SLP_CLK_REQ (Bit 18)              */
#define PCR_EC_CLK_REQ2_STS_LED2_SLP_CLK_REQ_Msk (0x40000UL)            /*!< PCR EC_CLK_REQ2_STS: LED2_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_BCM_SLP_CLK_REQ_Pos (19UL)                  /*!< PCR EC_CLK_REQ2_STS: BCM_SLP_CLK_REQ (Bit 19)               */
#define PCR_EC_CLK_REQ2_STS_BCM_SLP_CLK_REQ_Msk (0x80000UL)             /*!< PCR EC_CLK_REQ2_STS: BCM_SLP_CLK_REQ (Bitfield-Mask: 0x01)  */
#define PCR_EC_CLK_REQ2_STS_SPI1_SLP_CLK_REQ_Pos (20UL)                 /*!< PCR EC_CLK_REQ2_STS: SPI1_SLP_CLK_REQ (Bit 20)              */
#define PCR_EC_CLK_REQ2_STS_SPI1_SLP_CLK_REQ_Msk (0x100000UL)           /*!< PCR EC_CLK_REQ2_STS: SPI1_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_TIMER16_2_SLP_CLK_REQ_Pos (21UL)            /*!< PCR EC_CLK_REQ2_STS: TIMER16_2_SLP_CLK_REQ (Bit 21)         */
#define PCR_EC_CLK_REQ2_STS_TIMER16_2_SLP_CLK_REQ_Msk (0x200000UL)      /*!< PCR EC_CLK_REQ2_STS: TIMER16_2_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_TIMER16_3_SLP_CLK_REQ_Pos (22UL)            /*!< PCR EC_CLK_REQ2_STS: TIMER16_3_SLP_CLK_REQ (Bit 22)         */
#define PCR_EC_CLK_REQ2_STS_TIMER16_3_SLP_CLK_REQ_Msk (0x400000UL)      /*!< PCR EC_CLK_REQ2_STS: TIMER16_3_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_TIMER32_0_SLP_CLK_REQ_Pos (23UL)            /*!< PCR EC_CLK_REQ2_STS: TIMER32_0_SLP_CLK_REQ (Bit 23)         */
#define PCR_EC_CLK_REQ2_STS_TIMER32_0_SLP_CLK_REQ_Msk (0x800000UL)      /*!< PCR EC_CLK_REQ2_STS: TIMER32_0_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_TIMER32_1_SLP_CLK_REQ_Pos (24UL)            /*!< PCR EC_CLK_REQ2_STS: TIMER32_1_SLP_CLK_REQ (Bit 24)         */
#define PCR_EC_CLK_REQ2_STS_TIMER32_1_SLP_CLK_REQ_Msk (0x1000000UL)     /*!< PCR EC_CLK_REQ2_STS: TIMER32_1_SLP_CLK_REQ (Bitfield-Mask: 0x01) */
#define PCR_EC_CLK_REQ2_STS_LED3_SLP_CLK_REQ_Pos (25UL)                 /*!< PCR EC_CLK_REQ2_STS: LED3_SLP_CLK_REQ (Bit 25)              */
#define PCR_EC_CLK_REQ2_STS_LED3_SLP_CLK_REQ_Msk (0x2000000UL)          /*!< PCR EC_CLK_REQ2_STS: LED3_SLP_CLK_REQ (Bitfield-Mask: 0x01) */

/* -------------------------------  PCR_CHIP_OSC_ID  ------------------------------ */
#define PCR_CHIP_OSC_ID_OSC_LOCK_Pos          (8UL)                     /*!< PCR CHIP_OSC_ID: OSC_LOCK (Bit 8)                           */
#define PCR_CHIP_OSC_ID_OSC_LOCK_Msk          (0x100UL)                 /*!< PCR CHIP_OSC_ID: OSC_LOCK (Bitfield-Mask: 0x01)             */

/* ----------------------------  PCR_CHIP_PWR_RST_STS  ---------------------------- */
#define PCR_CHIP_PWR_RST_STS_VCC_nRST_Pos     (2UL)                     /*!< PCR CHIP_PWR_RST_STS: VCC_nRST (Bit 2)                      */
#define PCR_CHIP_PWR_RST_STS_VCC_nRST_Msk     (0x4UL)                   /*!< PCR CHIP_PWR_RST_STS: VCC_nRST (Bitfield-Mask: 0x01)        */
#define PCR_CHIP_PWR_RST_STS_SIO_nRST_Pos     (3UL)                     /*!< PCR CHIP_PWR_RST_STS: SIO_nRST (Bit 3)                      */
#define PCR_CHIP_PWR_RST_STS_SIO_nRST_Msk     (0x8UL)                   /*!< PCR CHIP_PWR_RST_STS: SIO_nRST (Bitfield-Mask: 0x01)        */
#define PCR_CHIP_PWR_RST_STS_VBAT_RST_Pos     (5UL)                     /*!< PCR CHIP_PWR_RST_STS: VBAT_RST (Bit 5)                      */
#define PCR_CHIP_PWR_RST_STS_VBAT_RST_Msk     (0x20UL)                  /*!< PCR CHIP_PWR_RST_STS: VBAT_RST (Bitfield-Mask: 0x01)        */
#define PCR_CHIP_PWR_RST_STS_VCC1_RST_Pos     (6UL)                     /*!< PCR CHIP_PWR_RST_STS: VCC1_RST (Bit 6)                      */
#define PCR_CHIP_PWR_RST_STS_VCC1_RST_Msk     (0x40UL)                  /*!< PCR CHIP_PWR_RST_STS: VCC1_RST (Bitfield-Mask: 0x01)        */
#define PCR_CHIP_PWR_RST_STS__32K_ACTIVE_Pos  (10UL)                    /*!< PCR CHIP_PWR_RST_STS: _32K_ACTIVE (Bit 10)                  */
#define PCR_CHIP_PWR_RST_STS__32K_ACTIVE_Msk  (0x400UL)                 /*!< PCR CHIP_PWR_RST_STS: _32K_ACTIVE (Bitfield-Mask: 0x01)     */
#define PCR_CHIP_PWR_RST_STS_PCICLK_ACTIVE_Pos (11UL)                   /*!< PCR CHIP_PWR_RST_STS: PCICLK_ACTIVE (Bit 11)                */
#define PCR_CHIP_PWR_RST_STS_PCICLK_ACTIVE_Msk (0x800UL)                /*!< PCR CHIP_PWR_RST_STS: PCICLK_ACTIVE (Bitfield-Mask: 0x01)   */

/* -------------------------------  PCR_HOST_RST_EN  ------------------------------ */
#define PCR_HOST_RST_EN_LPC_RST_EN_Pos        (0UL)                     /*!< PCR HOST_RST_EN: LPC_RST_EN (Bit 0)                         */
#define PCR_HOST_RST_EN_LPC_RST_EN_Msk        (0x1UL)                   /*!< PCR HOST_RST_EN: LPC_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_HOST_RST_EN_UART_0_RST_EN_Pos     (1UL)                     /*!< PCR HOST_RST_EN: UART_0_RST_EN (Bit 1)                      */
#define PCR_HOST_RST_EN_UART_0_RST_EN_Msk     (0x2UL)                   /*!< PCR HOST_RST_EN: UART_0_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_HOST_RST_EN_GLBL_CFG_RST_EN_Pos   (12UL)                    /*!< PCR HOST_RST_EN: GLBL_CFG_RST_EN (Bit 12)                   */
#define PCR_HOST_RST_EN_GLBL_CFG_RST_EN_Msk   (0x1000UL)                /*!< PCR HOST_RST_EN: GLBL_CFG_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_HOST_RST_EN_ACPI_EC_0_RST_EN_Pos  (13UL)                    /*!< PCR HOST_RST_EN: ACPI_EC_0_RST_EN (Bit 13)                  */
#define PCR_HOST_RST_EN_ACPI_EC_0_RST_EN_Msk  (0x2000UL)                /*!< PCR HOST_RST_EN: ACPI_EC_0_RST_EN (Bitfield-Mask: 0x01)     */
#define PCR_HOST_RST_EN_ACPI_EC_1_RST_EN_Pos  (14UL)                    /*!< PCR HOST_RST_EN: ACPI_EC_1_RST_EN (Bit 14)                  */
#define PCR_HOST_RST_EN_ACPI_EC_1_RST_EN_Msk  (0x4000UL)                /*!< PCR HOST_RST_EN: ACPI_EC_1_RST_EN (Bitfield-Mask: 0x01)     */
#define PCR_HOST_RST_EN_ACPI_PM1_RST_EN_Pos   (15UL)                    /*!< PCR HOST_RST_EN: ACPI_PM1_RST_EN (Bit 15)                   */
#define PCR_HOST_RST_EN_ACPI_PM1_RST_EN_Msk   (0x8000UL)                /*!< PCR HOST_RST_EN: ACPI_PM1_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_HOST_RST_EN_KBCEM_RST_EN_Pos      (16UL)                    /*!< PCR HOST_RST_EN: KBCEM_RST_EN (Bit 16)                      */
#define PCR_HOST_RST_EN_KBCEM_RST_EN_Msk      (0x10000UL)               /*!< PCR HOST_RST_EN: KBCEM_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_HOST_RST_EN_RTC_RST_EN_Pos        (18UL)                    /*!< PCR HOST_RST_EN: RTC_RST_EN (Bit 18)                        */
#define PCR_HOST_RST_EN_RTC_RST_EN_Msk        (0x40000UL)               /*!< PCR HOST_RST_EN: RTC_RST_EN (Bitfield-Mask: 0x01)           */

/* --------------------------------  PCR_EC_RST_EN  ------------------------------- */
#define PCR_EC_RST_EN_INT_RST_EN_Pos          (0UL)                     /*!< PCR EC_RST_EN: INT_RST_EN (Bit 0)                           */
#define PCR_EC_RST_EN_INT_RST_EN_Msk          (0x1UL)                   /*!< PCR EC_RST_EN: INT_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_RST_EN_PECI_RST_EN_Pos         (1UL)                     /*!< PCR EC_RST_EN: PECI_RST_EN (Bit 1)                          */
#define PCR_EC_RST_EN_PECI_RST_EN_Msk         (0x2UL)                   /*!< PCR EC_RST_EN: PECI_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_TACH0_RST_EN_Pos        (2UL)                     /*!< PCR EC_RST_EN: TACH0_RST_EN (Bit 2)                         */
#define PCR_EC_RST_EN_TACH0_RST_EN_Msk        (0x4UL)                   /*!< PCR EC_RST_EN: TACH0_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN_PWM0_RST_EN_Pos         (4UL)                     /*!< PCR EC_RST_EN: PWM0_RST_EN (Bit 4)                          */
#define PCR_EC_RST_EN_PWM0_RST_EN_Msk         (0x10UL)                  /*!< PCR EC_RST_EN: PWM0_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_PMC_RST_EN_Pos          (5UL)                     /*!< PCR EC_RST_EN: PMC_RST_EN (Bit 5)                           */
#define PCR_EC_RST_EN_PMC_RST_EN_Msk          (0x20UL)                  /*!< PCR EC_RST_EN: PMC_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_RST_EN_DMA_RST_EN_Pos          (6UL)                     /*!< PCR EC_RST_EN: DMA_RST_EN (Bit 6)                           */
#define PCR_EC_RST_EN_DMA_RST_EN_Msk          (0x40UL)                  /*!< PCR EC_RST_EN: DMA_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_RST_EN_TFDP_RST_EN_Pos         (7UL)                     /*!< PCR EC_RST_EN: TFDP_RST_EN (Bit 7)                          */
#define PCR_EC_RST_EN_TFDP_RST_EN_Msk         (0x80UL)                  /*!< PCR EC_RST_EN: TFDP_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_PROCESSOR_RST_EN_Pos    (8UL)                     /*!< PCR EC_RST_EN: PROCESSOR_RST_EN (Bit 8)                     */
#define PCR_EC_RST_EN_PROCESSOR_RST_EN_Msk    (0x100UL)                 /*!< PCR EC_RST_EN: PROCESSOR_RST_EN (Bitfield-Mask: 0x01)       */
#define PCR_EC_RST_EN_WDT_RST_EN_Pos          (9UL)                     /*!< PCR EC_RST_EN: WDT_RST_EN (Bit 9)                           */
#define PCR_EC_RST_EN_WDT_RST_EN_Msk          (0x200UL)                 /*!< PCR EC_RST_EN: WDT_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_EC_RST_EN_SMB0_RST_EN_Pos         (10UL)                    /*!< PCR EC_RST_EN: SMB0_RST_EN (Bit 10)                         */
#define PCR_EC_RST_EN_SMB0_RST_EN_Msk         (0x400UL)                 /*!< PCR EC_RST_EN: SMB0_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_TACH1_RST_EN_Pos        (11UL)                    /*!< PCR EC_RST_EN: TACH1_RST_EN (Bit 11)                        */
#define PCR_EC_RST_EN_TACH1_RST_EN_Msk        (0x800UL)                 /*!< PCR EC_RST_EN: TACH1_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN_PWM1_RST_EN_Pos         (20UL)                    /*!< PCR EC_RST_EN: PWM1_RST_EN (Bit 20)                         */
#define PCR_EC_RST_EN_PWM1_RST_EN_Msk         (0x100000UL)              /*!< PCR EC_RST_EN: PWM1_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_PWM2_RST_EN_Pos         (21UL)                    /*!< PCR EC_RST_EN: PWM2_RST_EN (Bit 21)                         */
#define PCR_EC_RST_EN_PWM2_RST_EN_Msk         (0x200000UL)              /*!< PCR EC_RST_EN: PWM2_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_PWM3_RST_EN_Pos         (22UL)                    /*!< PCR EC_RST_EN: PWM3_RST_EN (Bit 22)                         */
#define PCR_EC_RST_EN_PWM3_RST_EN_Msk         (0x400000UL)              /*!< PCR EC_RST_EN: PWM3_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN_EC_REG_BANK_RST_EN_Pos  (29UL)                    /*!< PCR EC_RST_EN: EC_REG_BANK_RST_EN (Bit 29)                  */
#define PCR_EC_RST_EN_EC_REG_BANK_RST_EN_Msk  (0x20000000UL)            /*!< PCR EC_RST_EN: EC_REG_BANK_RST_EN (Bitfield-Mask: 0x01)     */
#define PCR_EC_RST_EN_TIMER16_0_RST_EN_Pos    (30UL)                    /*!< PCR EC_RST_EN: TIMER16_0_RST_EN (Bit 30)                    */
#define PCR_EC_RST_EN_TIMER16_0_RST_EN_Msk    (0x40000000UL)            /*!< PCR EC_RST_EN: TIMER16_0_RST_EN (Bitfield-Mask: 0x01)       */
#define PCR_EC_RST_EN_TIMER16_1_RST_EN_Pos    (31UL)                    /*!< PCR EC_RST_EN: TIMER16_1_RST_EN (Bit 31)                    */
#define PCR_EC_RST_EN_TIMER16_1_RST_EN_Msk    (0x80000000UL)            /*!< PCR EC_RST_EN: TIMER16_1_RST_EN (Bitfield-Mask: 0x01)       */

/* -------------------------------  PCR_EC_RST_EN2  ------------------------------- */
#define PCR_EC_RST_EN2_ADC_RST_EN_Pos         (3UL)                     /*!< PCR EC_RST_EN2: ADC_RST_EN (Bit 3)                          */
#define PCR_EC_RST_EN2_ADC_RST_EN_Msk         (0x8UL)                   /*!< PCR EC_RST_EN2: ADC_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN2_PS2_0_RST_EN_Pos       (5UL)                     /*!< PCR EC_RST_EN2: PS2_0_RST_EN (Bit 5)                        */
#define PCR_EC_RST_EN2_PS2_0_RST_EN_Msk       (0x20UL)                  /*!< PCR EC_RST_EN2: PS2_0_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_RST_EN2_PS2_1_RST_EN_Pos       (6UL)                     /*!< PCR EC_RST_EN2: PS2_1_RST_EN (Bit 6)                        */
#define PCR_EC_RST_EN2_PS2_1_RST_EN_Msk       (0x40UL)                  /*!< PCR EC_RST_EN2: PS2_1_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_RST_EN2_PS2_2_RST_EN_Pos       (7UL)                     /*!< PCR EC_RST_EN2: PS2_2_RST_EN (Bit 7)                        */
#define PCR_EC_RST_EN2_PS2_2_RST_EN_Msk       (0x80UL)                  /*!< PCR EC_RST_EN2: PS2_2_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_RST_EN2_PS2_3_RST_EN_Pos       (8UL)                     /*!< PCR EC_RST_EN2: PS2_3_RST_EN (Bit 8)                        */
#define PCR_EC_RST_EN2_PS2_3_RST_EN_Msk       (0x100UL)                 /*!< PCR EC_RST_EN2: PS2_3_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_EC_RST_EN2_SPI0_SLP_EN_Pos        (9UL)                     /*!< PCR EC_RST_EN2: SPI0_SLP_EN (Bit 9)                         */
#define PCR_EC_RST_EN2_SPI0_SLP_EN_Msk        (0x200UL)                 /*!< PCR EC_RST_EN2: SPI0_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_HTIMER_RST_EN_Pos      (10UL)                    /*!< PCR EC_RST_EN2: HTIMER_RST_EN (Bit 10)                      */
#define PCR_EC_RST_EN2_HTIMER_RST_EN_Msk      (0x400UL)                 /*!< PCR EC_RST_EN2: HTIMER_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_EC_RST_EN2_KEYSCAN_RST_EN_Pos     (11UL)                    /*!< PCR EC_RST_EN2: KEYSCAN_RST_EN (Bit 11)                     */
#define PCR_EC_RST_EN2_KEYSCAN_RST_EN_Msk     (0x800UL)                 /*!< PCR EC_RST_EN2: KEYSCAN_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_EC_RST_EN2_RPMPWM_RST_EN_Pos      (12UL)                    /*!< PCR EC_RST_EN2: RPMPWM_RST_EN (Bit 12)                      */
#define PCR_EC_RST_EN2_RPMPWM_RST_EN_Msk      (0x1000UL)                /*!< PCR EC_RST_EN2: RPMPWM_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_EC_RST_EN2_SMB1_RST_EN_Pos        (13UL)                    /*!< PCR EC_RST_EN2: SMB1_RST_EN (Bit 13)                        */
#define PCR_EC_RST_EN2_SMB1_RST_EN_Msk        (0x2000UL)                /*!< PCR EC_RST_EN2: SMB1_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_SMB2_RST_EN_Pos        (14UL)                    /*!< PCR EC_RST_EN2: SMB2_RST_EN (Bit 14)                        */
#define PCR_EC_RST_EN2_SMB2_RST_EN_Msk        (0x4000UL)                /*!< PCR EC_RST_EN2: SMB2_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_SMB3_RST_EN_Pos        (15UL)                    /*!< PCR EC_RST_EN2: SMB3_RST_EN (Bit 15)                        */
#define PCR_EC_RST_EN2_SMB3_RST_EN_Msk        (0x8000UL)                /*!< PCR EC_RST_EN2: SMB3_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_LED0_RST_EN_Pos        (16UL)                    /*!< PCR EC_RST_EN2: LED0_RST_EN (Bit 16)                        */
#define PCR_EC_RST_EN2_LED0_RST_EN_Msk        (0x10000UL)               /*!< PCR EC_RST_EN2: LED0_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_LED1_RST_EN_Pos        (17UL)                    /*!< PCR EC_RST_EN2: LED1_RST_EN (Bit 17)                        */
#define PCR_EC_RST_EN2_LED1_RST_EN_Msk        (0x20000UL)               /*!< PCR EC_RST_EN2: LED1_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_LED2_RST_EN_Pos        (18UL)                    /*!< PCR EC_RST_EN2: LED2_RST_EN (Bit 18)                        */
#define PCR_EC_RST_EN2_LED2_RST_EN_Msk        (0x40000UL)               /*!< PCR EC_RST_EN2: LED2_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_BCM_RST_EN_Pos         (19UL)                    /*!< PCR EC_RST_EN2: BCM_RST_EN (Bit 19)                         */
#define PCR_EC_RST_EN2_BCM_RST_EN_Msk         (0x80000UL)               /*!< PCR EC_RST_EN2: BCM_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_EC_RST_EN2_SPI1_RST_EN_Pos        (20UL)                    /*!< PCR EC_RST_EN2: SPI1_RST_EN (Bit 20)                        */
#define PCR_EC_RST_EN2_SPI1_RST_EN_Msk        (0x100000UL)              /*!< PCR EC_RST_EN2: SPI1_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_EC_RST_EN2_TIMER16_2_RST_EN_Pos   (21UL)                    /*!< PCR EC_RST_EN2: TIMER16_2_RST_EN (Bit 21)                   */
#define PCR_EC_RST_EN2_TIMER16_2_RST_EN_Msk   (0x200000UL)              /*!< PCR EC_RST_EN2: TIMER16_2_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_RST_EN2_TIMER16_3_RST_EN_Pos   (22UL)                    /*!< PCR EC_RST_EN2: TIMER16_3_RST_EN (Bit 22)                   */
#define PCR_EC_RST_EN2_TIMER16_3_RST_EN_Msk   (0x400000UL)              /*!< PCR EC_RST_EN2: TIMER16_3_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_RST_EN2_TIMER32_0_RST_EN_Pos   (23UL)                    /*!< PCR EC_RST_EN2: TIMER32_0_RST_EN (Bit 23)                   */
#define PCR_EC_RST_EN2_TIMER32_0_RST_EN_Msk   (0x800000UL)              /*!< PCR EC_RST_EN2: TIMER32_0_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_RST_EN2_TIMER32_1_RST_EN_Pos   (24UL)                    /*!< PCR EC_RST_EN2: TIMER32_1_RST_EN (Bit 24)                   */
#define PCR_EC_RST_EN2_TIMER32_1_RST_EN_Msk   (0x1000000UL)             /*!< PCR EC_RST_EN2: TIMER32_1_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_EC_RST_EN2_LED3_RST_EN_Pos        (25UL)                    /*!< PCR EC_RST_EN2: LED3_RST_EN (Bit 25)                        */
#define PCR_EC_RST_EN2_LED3_RST_EN_Msk        (0x2000000UL)             /*!< PCR EC_RST_EN2: LED3_RST_EN (Bitfield-Mask: 0x01)           */

/* ------------------------------  PCR_PWR_RST_CTRL  ------------------------------ */
#define PCR_PWR_RST_CTRL_IRESET_OUT_Pos       (0UL)                     /*!< PCR PWR_RST_CTRL: IRESET_OUT (Bit 0)                        */
#define PCR_PWR_RST_CTRL_IRESET_OUT_Msk       (0x1UL)                   /*!< PCR PWR_RST_CTRL: IRESET_OUT (Bitfield-Mask: 0x01)          */


/* ================================================================================ */
/* ================          struct 'VBAT' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  VBAT_PFR_STS  -------------------------------- */
#define VBAT_PFR_STS_DET32K_IN_Pos            (0UL)                     /*!< VBAT PFR_STS: DET32K_IN (Bit 0)                             */
#define VBAT_PFR_STS_DET32K_IN_Msk            (0x1UL)                   /*!< VBAT PFR_STS: DET32K_IN (Bitfield-Mask: 0x01)               */
#define VBAT_PFR_STS_WDT_Pos                  (5UL)                     /*!< VBAT PFR_STS: WDT (Bit 5)                                   */
#define VBAT_PFR_STS_WDT_Msk                  (0x20UL)                  /*!< VBAT PFR_STS: WDT (Bitfield-Mask: 0x01)                     */
#define VBAT_PFR_STS_VBAT_RST_Pos             (7UL)                     /*!< VBAT PFR_STS: VBAT_RST (Bit 7)                              */
#define VBAT_PFR_STS_VBAT_RST_Msk             (0x80UL)                  /*!< VBAT PFR_STS: VBAT_RST (Bitfield-Mask: 0x01)                */

/* --------------------------------  VBAT_CLOCK_EN  ------------------------------- */
#define VBAT_CLOCK_EN_XOSEL_Pos               (0UL)                     /*!< VBAT CLOCK_EN: XOSEL (Bit 0)                                */
#define VBAT_CLOCK_EN_XOSEL_Msk               (0x1UL)                   /*!< VBAT CLOCK_EN: XOSEL (Bitfield-Mask: 0x01)                  */
#define VBAT_CLOCK_EN__32K_EN_Pos             (1UL)                     /*!< VBAT CLOCK_EN: _32K_EN (Bit 1)                              */
#define VBAT_CLOCK_EN__32K_EN_Msk             (0x2UL)                   /*!< VBAT CLOCK_EN: _32K_EN (Bitfield-Mask: 0x01)                */


/* ================================================================================ */
/* ================          struct 'LPC' Position & Mask          ================ */
/* ================================================================================ */


/* -------------------------------  LPC_BUS_MONITOR  ------------------------------ */
#define LPC_BUS_MONITOR_LRESET_STATUS_Pos     (1UL)                     /*!< LPC BUS_MONITOR: LRESET_STATUS (Bit 1)                      */
#define LPC_BUS_MONITOR_LRESET_STATUS_Msk     (0x2UL)                   /*!< LPC BUS_MONITOR: LRESET_STATUS (Bitfield-Mask: 0x01)        */

/* -----------------------------  LPC_HOST_BUS_ERROR  ----------------------------- */
#define LPC_HOST_BUS_ERROR_LPC_ERR_Pos        (0UL)                     /*!< LPC HOST_BUS_ERROR: LPC_ERR (Bit 0)                         */
#define LPC_HOST_BUS_ERROR_LPC_ERR_Msk        (0x1UL)                   /*!< LPC HOST_BUS_ERROR: LPC_ERR (Bitfield-Mask: 0x01)           */
#define LPC_HOST_BUS_ERROR_EN_ERR_Pos         (1UL)                     /*!< LPC HOST_BUS_ERROR: EN_ERR (Bit 1)                          */
#define LPC_HOST_BUS_ERROR_EN_ERR_Msk         (0x2UL)                   /*!< LPC HOST_BUS_ERROR: EN_ERR (Bitfield-Mask: 0x01)            */
#define LPC_HOST_BUS_ERROR_BAR_ERR_Pos        (2UL)                     /*!< LPC HOST_BUS_ERROR: BAR_ERR (Bit 2)                         */
#define LPC_HOST_BUS_ERROR_BAR_ERR_Msk        (0x4UL)                   /*!< LPC HOST_BUS_ERROR: BAR_ERR (Bitfield-Mask: 0x01)           */
#define LPC_HOST_BUS_ERROR_RUNTIME_ERR_Pos    (3UL)                     /*!< LPC HOST_BUS_ERROR: RUNTIME_ERR (Bit 3)                     */
#define LPC_HOST_BUS_ERROR_RUNTIME_ERR_Msk    (0x8UL)                   /*!< LPC HOST_BUS_ERROR: RUNTIME_ERR (Bitfield-Mask: 0x01)       */
#define LPC_HOST_BUS_ERROR_CONFIG_ERR_Pos     (4UL)                     /*!< LPC HOST_BUS_ERROR: CONFIG_ERR (Bit 4)                      */
#define LPC_HOST_BUS_ERROR_CONFIG_ERR_Msk     (0x10UL)                  /*!< LPC HOST_BUS_ERROR: CONFIG_ERR (Bitfield-Mask: 0x01)        */
#define LPC_HOST_BUS_ERROR_DMA_ERR_Pos        (5UL)                     /*!< LPC HOST_BUS_ERROR: DMA_ERR (Bit 5)                         */
#define LPC_HOST_BUS_ERROR_DMA_ERR_Msk        (0x20UL)                  /*!< LPC HOST_BUS_ERROR: DMA_ERR (Bitfield-Mask: 0x01)           */
#define LPC_HOST_BUS_ERROR_ERR_ADDR_Pos       (8UL)                     /*!< LPC HOST_BUS_ERROR: ERR_ADDR (Bit 8)                        */
#define LPC_HOST_BUS_ERROR_ERR_ADDR_Msk       (0xffffff00UL)            /*!< LPC HOST_BUS_ERROR: ERR_ADDR (Bitfield-Mask: 0xffffff)      */

/* --------------------------------  LPC_EC_SERIRQ  ------------------------------- */
#define LPC_EC_SERIRQ_EC_IRQ_Pos              (0UL)                     /*!< LPC EC_SERIRQ: EC_IRQ (Bit 0)                               */
#define LPC_EC_SERIRQ_EC_IRQ_Msk              (0x1UL)                   /*!< LPC EC_SERIRQ: EC_IRQ (Bitfield-Mask: 0x01)                 */

/* --------------------------------  LPC_CLK_CTRL  -------------------------------- */
#define LPC_CLK_CTRL_CR_Pos                   (0UL)                     /*!< LPC CLK_CTRL: CR (Bit 0)                                    */
#define LPC_CLK_CTRL_CR_Msk                   (0x3UL)                   /*!< LPC CLK_CTRL: CR (Bitfield-Mask: 0x03)                      */
#define LPC_CLK_CTRL_HANDSHAKE_Pos            (2UL)                     /*!< LPC CLK_CTRL: HANDSHAKE (Bit 2)                             */
#define LPC_CLK_CTRL_HANDSHAKE_Msk            (0x4UL)                   /*!< LPC CLK_CTRL: HANDSHAKE (Bitfield-Mask: 0x01)               */


/* ================================================================================ */
/* ================       struct 'LPC_CONFIG' Position & Mask      ================ */
/* ================================================================================ */


/* -------------------------------  LPC_CONFIG_SIRQ  ------------------------------ */
#define LPC_CONFIG_SIRQ_FRAME_Pos             (0UL)                     /*!< LPC_CONFIG SIRQ: FRAME (Bit 0)                              */
#define LPC_CONFIG_SIRQ_FRAME_Msk             (0x3fUL)                  /*!< LPC_CONFIG SIRQ: FRAME (Bitfield-Mask: 0x3f)                */
#define LPC_CONFIG_SIRQ_DEVICE_Pos            (6UL)                     /*!< LPC_CONFIG SIRQ: DEVICE (Bit 6)                             */
#define LPC_CONFIG_SIRQ_DEVICE_Msk            (0x40UL)                  /*!< LPC_CONFIG SIRQ: DEVICE (Bitfield-Mask: 0x01)               */
#define LPC_CONFIG_SIRQ_SELECT_Pos            (7UL)                     /*!< LPC_CONFIG SIRQ: SELECT (Bit 7)                             */
#define LPC_CONFIG_SIRQ_SELECT_Msk            (0x80UL)                  /*!< LPC_CONFIG SIRQ: SELECT (Bitfield-Mask: 0x01)               */

/* -----------------------------  LPC_CONFIG_LPC_BAR  ----------------------------- */
#define LPC_CONFIG_LPC_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG LPC_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_LPC_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG LPC_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_LPC_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG LPC_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_LPC_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG LPC_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_LPC_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG LPC_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_LPC_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG LPC_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_LPC_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG LPC_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_LPC_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG LPC_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_LPC_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG LPC_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_LPC_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG LPC_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* ------------------------------  LPC_CONFIG_EM_BAR  ----------------------------- */
#define LPC_CONFIG_EM_BAR_MASK_Pos            (0UL)                     /*!< LPC_CONFIG EM_BAR: MASK (Bit 0)                             */
#define LPC_CONFIG_EM_BAR_MASK_Msk            (0xffUL)                  /*!< LPC_CONFIG EM_BAR: MASK (Bitfield-Mask: 0xff)               */
#define LPC_CONFIG_EM_BAR_FRAME_Pos           (8UL)                     /*!< LPC_CONFIG EM_BAR: FRAME (Bit 8)                            */
#define LPC_CONFIG_EM_BAR_FRAME_Msk           (0x3f00UL)                /*!< LPC_CONFIG EM_BAR: FRAME (Bitfield-Mask: 0x3f)              */
#define LPC_CONFIG_EM_BAR_DEVICE_Pos          (14UL)                    /*!< LPC_CONFIG EM_BAR: DEVICE (Bit 14)                          */
#define LPC_CONFIG_EM_BAR_DEVICE_Msk          (0x4000UL)                /*!< LPC_CONFIG EM_BAR: DEVICE (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_EM_BAR_VALID_Pos           (15UL)                    /*!< LPC_CONFIG EM_BAR: VALID (Bit 15)                           */
#define LPC_CONFIG_EM_BAR_VALID_Msk           (0x8000UL)                /*!< LPC_CONFIG EM_BAR: VALID (Bitfield-Mask: 0x01)              */
#define LPC_CONFIG_EM_BAR_LPC_HOST_ADDR_Pos   (16UL)                    /*!< LPC_CONFIG EM_BAR: LPC_HOST_ADDR (Bit 16)                   */
#define LPC_CONFIG_EM_BAR_LPC_HOST_ADDR_Msk   (0xffff0000UL)            /*!< LPC_CONFIG EM_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)    */

/* -----------------------------  LPC_CONFIG_UART_BAR  ---------------------------- */
#define LPC_CONFIG_UART_BAR_MASK_Pos          (0UL)                     /*!< LPC_CONFIG UART_BAR: MASK (Bit 0)                           */
#define LPC_CONFIG_UART_BAR_MASK_Msk          (0xffUL)                  /*!< LPC_CONFIG UART_BAR: MASK (Bitfield-Mask: 0xff)             */
#define LPC_CONFIG_UART_BAR_FRAME_Pos         (8UL)                     /*!< LPC_CONFIG UART_BAR: FRAME (Bit 8)                          */
#define LPC_CONFIG_UART_BAR_FRAME_Msk         (0x3f00UL)                /*!< LPC_CONFIG UART_BAR: FRAME (Bitfield-Mask: 0x3f)            */
#define LPC_CONFIG_UART_BAR_DEVICE_Pos        (14UL)                    /*!< LPC_CONFIG UART_BAR: DEVICE (Bit 14)                        */
#define LPC_CONFIG_UART_BAR_DEVICE_Msk        (0x4000UL)                /*!< LPC_CONFIG UART_BAR: DEVICE (Bitfield-Mask: 0x01)           */
#define LPC_CONFIG_UART_BAR_VALID_Pos         (15UL)                    /*!< LPC_CONFIG UART_BAR: VALID (Bit 15)                         */
#define LPC_CONFIG_UART_BAR_VALID_Msk         (0x8000UL)                /*!< LPC_CONFIG UART_BAR: VALID (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_UART_BAR_LPC_HOST_ADDR_Pos (16UL)                    /*!< LPC_CONFIG UART_BAR: LPC_HOST_ADDR (Bit 16)                 */
#define LPC_CONFIG_UART_BAR_LPC_HOST_ADDR_Msk (0xffff0000UL)            /*!< LPC_CONFIG UART_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)  */

/* -----------------------------  LPC_CONFIG_KBC_BAR  ----------------------------- */
#define LPC_CONFIG_KBC_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG KBC_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_KBC_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG KBC_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_KBC_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG KBC_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_KBC_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG KBC_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_KBC_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG KBC_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_KBC_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG KBC_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_KBC_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG KBC_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_KBC_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG KBC_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_KBC_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG KBC_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_KBC_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG KBC_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* -----------------------------  LPC_CONFIG_EC0_BAR  ----------------------------- */
#define LPC_CONFIG_EC0_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG EC0_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_EC0_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG EC0_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_EC0_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG EC0_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_EC0_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG EC0_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_EC0_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG EC0_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_EC0_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG EC0_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_EC0_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG EC0_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_EC0_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG EC0_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_EC0_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG EC0_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_EC0_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG EC0_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* -----------------------------  LPC_CONFIG_EC1_BAR  ----------------------------- */
#define LPC_CONFIG_EC1_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG EC1_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_EC1_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG EC1_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_EC1_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG EC1_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_EC1_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG EC1_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_EC1_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG EC1_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_EC1_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG EC1_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_EC1_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG EC1_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_EC1_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG EC1_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_EC1_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG EC1_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_EC1_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG EC1_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* -----------------------------  LPC_CONFIG_PM1_BAR  ----------------------------- */
#define LPC_CONFIG_PM1_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG PM1_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_PM1_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG PM1_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_PM1_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG PM1_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_PM1_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG PM1_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_PM1_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG PM1_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_PM1_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG PM1_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_PM1_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG PM1_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_PM1_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG PM1_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_PM1_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG PM1_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_PM1_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG PM1_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* -----------------------------  LPC_CONFIG_LGC_BAR  ----------------------------- */
#define LPC_CONFIG_LGC_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG LGC_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_LGC_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG LGC_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_LGC_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG LGC_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_LGC_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG LGC_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_LGC_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG LGC_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_LGC_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG LGC_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_LGC_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG LGC_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_LGC_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG LGC_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_LGC_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG LGC_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_LGC_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG LGC_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* -----------------------------  LPC_CONFIG_MBX_BAR  ----------------------------- */
#define LPC_CONFIG_MBX_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG MBX_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_MBX_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG MBX_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_MBX_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG MBX_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_MBX_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG MBX_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_MBX_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG MBX_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_MBX_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG MBX_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_MBX_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG MBX_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_MBX_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG MBX_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_MBX_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG MBX_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_MBX_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG MBX_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */

/* -----------------------------  LPC_CONFIG_RTC_BAR  ----------------------------- */
#define LPC_CONFIG_RTC_BAR_MASK_Pos           (0UL)                     /*!< LPC_CONFIG RTC_BAR: MASK (Bit 0)                            */
#define LPC_CONFIG_RTC_BAR_MASK_Msk           (0xffUL)                  /*!< LPC_CONFIG RTC_BAR: MASK (Bitfield-Mask: 0xff)              */
#define LPC_CONFIG_RTC_BAR_FRAME_Pos          (8UL)                     /*!< LPC_CONFIG RTC_BAR: FRAME (Bit 8)                           */
#define LPC_CONFIG_RTC_BAR_FRAME_Msk          (0x3f00UL)                /*!< LPC_CONFIG RTC_BAR: FRAME (Bitfield-Mask: 0x3f)             */
#define LPC_CONFIG_RTC_BAR_DEVICE_Pos         (14UL)                    /*!< LPC_CONFIG RTC_BAR: DEVICE (Bit 14)                         */
#define LPC_CONFIG_RTC_BAR_DEVICE_Msk         (0x4000UL)                /*!< LPC_CONFIG RTC_BAR: DEVICE (Bitfield-Mask: 0x01)            */
#define LPC_CONFIG_RTC_BAR_VALID_Pos          (15UL)                    /*!< LPC_CONFIG RTC_BAR: VALID (Bit 15)                          */
#define LPC_CONFIG_RTC_BAR_VALID_Msk          (0x8000UL)                /*!< LPC_CONFIG RTC_BAR: VALID (Bitfield-Mask: 0x01)             */
#define LPC_CONFIG_RTC_BAR_LPC_HOST_ADDR_Pos  (16UL)                    /*!< LPC_CONFIG RTC_BAR: LPC_HOST_ADDR (Bit 16)                  */
#define LPC_CONFIG_RTC_BAR_LPC_HOST_ADDR_Msk  (0xffff0000UL)            /*!< LPC_CONFIG RTC_BAR: LPC_HOST_ADDR (Bitfield-Mask: 0xffff)   */


/* ================================================================================ */
/* ================        struct 'MEM_BAR' Position & Mask        ================ */
/* ================================================================================ */


/* ---------------------------------  MEM_BAR_CR  --------------------------------- */
#define MEM_BAR_CR_MASK_Pos                   (0UL)                     /*!< MEM_BAR CR: MASK (Bit 0)                                    */
#define MEM_BAR_CR_MASK_Msk                   (0xffUL)                  /*!< MEM_BAR CR: MASK (Bitfield-Mask: 0xff)                      */
#define MEM_BAR_CR_FRAME_Pos                  (8UL)                     /*!< MEM_BAR CR: FRAME (Bit 8)                                   */
#define MEM_BAR_CR_FRAME_Msk                  (0x3f00UL)                /*!< MEM_BAR CR: FRAME (Bitfield-Mask: 0x3f)                     */
#define MEM_BAR_CR_VALID_Pos                  (15UL)                    /*!< MEM_BAR CR: VALID (Bit 15)                                  */
#define MEM_BAR_CR_VALID_Msk                  (0x8000UL)                /*!< MEM_BAR CR: VALID (Bitfield-Mask: 0x01)                     */


/* ================================================================================ */
/* ================      struct 'MBX_MEM_BAR' Position & Mask      ================ */
/* ================================================================================ */


/* --------------------------  LPC_CONFIG_MBX_MEM_BAR_CR  ------------------------- */
#define LPC_CONFIG_MBX_MEM_BAR_CR_MASK_Pos    (0UL)                     /*!< LPC_CONFIG_MBX_MEM_BAR CR: MASK (Bit 0)                     */
#define LPC_CONFIG_MBX_MEM_BAR_CR_MASK_Msk    (0xffUL)                  /*!< LPC_CONFIG_MBX_MEM_BAR CR: MASK (Bitfield-Mask: 0xff)       */
#define LPC_CONFIG_MBX_MEM_BAR_CR_FRAME_Pos   (8UL)                     /*!< LPC_CONFIG_MBX_MEM_BAR CR: FRAME (Bit 8)                    */
#define LPC_CONFIG_MBX_MEM_BAR_CR_FRAME_Msk   (0x3f00UL)                /*!< LPC_CONFIG_MBX_MEM_BAR CR: FRAME (Bitfield-Mask: 0x3f)      */
#define LPC_CONFIG_MBX_MEM_BAR_CR_VALID_Pos   (15UL)                    /*!< LPC_CONFIG_MBX_MEM_BAR CR: VALID (Bit 15)                   */
#define LPC_CONFIG_MBX_MEM_BAR_CR_VALID_Msk   (0x8000UL)                /*!< LPC_CONFIG_MBX_MEM_BAR CR: VALID (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================      struct 'EC0_MEM_BAR' Position & Mask      ================ */
/* ================================================================================ */


/* --------------------------  LPC_CONFIG_EC0_MEM_BAR_CR  ------------------------- */
#define LPC_CONFIG_EC0_MEM_BAR_CR_MASK_Pos    (0UL)                     /*!< LPC_CONFIG_EC0_MEM_BAR CR: MASK (Bit 0)                     */
#define LPC_CONFIG_EC0_MEM_BAR_CR_MASK_Msk    (0xffUL)                  /*!< LPC_CONFIG_EC0_MEM_BAR CR: MASK (Bitfield-Mask: 0xff)       */
#define LPC_CONFIG_EC0_MEM_BAR_CR_FRAME_Pos   (8UL)                     /*!< LPC_CONFIG_EC0_MEM_BAR CR: FRAME (Bit 8)                    */
#define LPC_CONFIG_EC0_MEM_BAR_CR_FRAME_Msk   (0x3f00UL)                /*!< LPC_CONFIG_EC0_MEM_BAR CR: FRAME (Bitfield-Mask: 0x3f)      */
#define LPC_CONFIG_EC0_MEM_BAR_CR_VALID_Pos   (15UL)                    /*!< LPC_CONFIG_EC0_MEM_BAR CR: VALID (Bit 15)                   */
#define LPC_CONFIG_EC0_MEM_BAR_CR_VALID_Msk   (0x8000UL)                /*!< LPC_CONFIG_EC0_MEM_BAR CR: VALID (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================      struct 'EC1_MEM_BAR' Position & Mask      ================ */
/* ================================================================================ */


/* --------------------------  LPC_CONFIG_EC1_MEM_BAR_CR  ------------------------- */
#define LPC_CONFIG_EC1_MEM_BAR_CR_MASK_Pos    (0UL)                     /*!< LPC_CONFIG_EC1_MEM_BAR CR: MASK (Bit 0)                     */
#define LPC_CONFIG_EC1_MEM_BAR_CR_MASK_Msk    (0xffUL)                  /*!< LPC_CONFIG_EC1_MEM_BAR CR: MASK (Bitfield-Mask: 0xff)       */
#define LPC_CONFIG_EC1_MEM_BAR_CR_FRAME_Pos   (8UL)                     /*!< LPC_CONFIG_EC1_MEM_BAR CR: FRAME (Bit 8)                    */
#define LPC_CONFIG_EC1_MEM_BAR_CR_FRAME_Msk   (0x3f00UL)                /*!< LPC_CONFIG_EC1_MEM_BAR CR: FRAME (Bitfield-Mask: 0x3f)      */
#define LPC_CONFIG_EC1_MEM_BAR_CR_VALID_Pos   (15UL)                    /*!< LPC_CONFIG_EC1_MEM_BAR CR: VALID (Bit 15)                   */
#define LPC_CONFIG_EC1_MEM_BAR_CR_VALID_Msk   (0x8000UL)                /*!< LPC_CONFIG_EC1_MEM_BAR CR: VALID (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================      struct 'EMI_MEM_BAR' Position & Mask      ================ */
/* ================================================================================ */


/* --------------------------  LPC_CONFIG_EMI_MEM_BAR_CR  ------------------------- */
#define LPC_CONFIG_EMI_MEM_BAR_CR_MASK_Pos    (0UL)                     /*!< LPC_CONFIG_EMI_MEM_BAR CR: MASK (Bit 0)                     */
#define LPC_CONFIG_EMI_MEM_BAR_CR_MASK_Msk    (0xffUL)                  /*!< LPC_CONFIG_EMI_MEM_BAR CR: MASK (Bitfield-Mask: 0xff)       */
#define LPC_CONFIG_EMI_MEM_BAR_CR_FRAME_Pos   (8UL)                     /*!< LPC_CONFIG_EMI_MEM_BAR CR: FRAME (Bit 8)                    */
#define LPC_CONFIG_EMI_MEM_BAR_CR_FRAME_Msk   (0x3f00UL)                /*!< LPC_CONFIG_EMI_MEM_BAR CR: FRAME (Bitfield-Mask: 0x3f)      */
#define LPC_CONFIG_EMI_MEM_BAR_CR_VALID_Pos   (15UL)                    /*!< LPC_CONFIG_EMI_MEM_BAR CR: VALID (Bit 15)                   */
#define LPC_CONFIG_EMI_MEM_BAR_CR_VALID_Msk   (0x8000UL)                /*!< LPC_CONFIG_EMI_MEM_BAR CR: VALID (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================          struct 'EMI' Position & Mask          ================ */
/* ================================================================================ */


/* -------------------------------  EMI_EC_ADDRESS  ------------------------------- */
#define EMI_EC_ADDRESS_ACCESS_TYPE_Pos        (0UL)                     /*!< EMI EC_ADDRESS: ACCESS_TYPE (Bit 0)                         */
#define EMI_EC_ADDRESS_ACCESS_TYPE_Msk        (0x3UL)                   /*!< EMI EC_ADDRESS: ACCESS_TYPE (Bitfield-Mask: 0x03)           */
#define EMI_EC_ADDRESS_EC_ADDRESS_Pos         (2UL)                     /*!< EMI EC_ADDRESS: EC_ADDRESS (Bit 2)                          */
#define EMI_EC_ADDRESS_EC_ADDRESS_Msk         (0x7ffcUL)                /*!< EMI EC_ADDRESS: EC_ADDRESS (Bitfield-Mask: 0x1fff)          */
#define EMI_EC_ADDRESS_REGION_Pos             (15UL)                    /*!< EMI EC_ADDRESS: REGION (Bit 15)                             */
#define EMI_EC_ADDRESS_REGION_Msk             (0x8000UL)                /*!< EMI EC_ADDRESS: REGION (Bitfield-Mask: 0x01)                */

/* ---------------------------------  EMI_EC_SWI  --------------------------------- */
#define EMI_EC_SWI_EC_WR_Pos                  (0UL)                     /*!< EMI EC_SWI: EC_WR (Bit 0)                                   */
#define EMI_EC_SWI_EC_WR_Msk                  (0x1UL)                   /*!< EMI EC_SWI: EC_WR (Bitfield-Mask: 0x01)                     */
#define EMI_EC_SWI_NOTIFICATION_Pos           (1UL)                     /*!< EMI EC_SWI: NOTIFICATION (Bit 1)                            */
#define EMI_EC_SWI_NOTIFICATION_Msk           (0xfffeUL)                /*!< EMI EC_SWI: NOTIFICATION (Bitfield-Mask: 0x7fff)            */


/* ================================================================================ */
/* ================        struct 'ACPI_EC0' Position & Mask       ================ */
/* ================================================================================ */


/* -----------------------------  ACPI_EC0_OS_STATUS  ----------------------------- */
#define ACPI_EC0_OS_STATUS_OBF_Pos            (0UL)                     /*!< ACPI_EC0 OS_STATUS: OBF (Bit 0)                             */
#define ACPI_EC0_OS_STATUS_OBF_Msk            (0x1UL)                   /*!< ACPI_EC0 OS_STATUS: OBF (Bitfield-Mask: 0x01)               */
#define ACPI_EC0_OS_STATUS_IBF_Pos            (1UL)                     /*!< ACPI_EC0 OS_STATUS: IBF (Bit 1)                             */
#define ACPI_EC0_OS_STATUS_IBF_Msk            (0x2UL)                   /*!< ACPI_EC0 OS_STATUS: IBF (Bitfield-Mask: 0x01)               */
#define ACPI_EC0_OS_STATUS_UD1B_Pos           (2UL)                     /*!< ACPI_EC0 OS_STATUS: UD1B (Bit 2)                            */
#define ACPI_EC0_OS_STATUS_UD1B_Msk           (0x4UL)                   /*!< ACPI_EC0 OS_STATUS: UD1B (Bitfield-Mask: 0x01)              */
#define ACPI_EC0_OS_STATUS_CMD_Pos            (3UL)                     /*!< ACPI_EC0 OS_STATUS: CMD (Bit 3)                             */
#define ACPI_EC0_OS_STATUS_CMD_Msk            (0x8UL)                   /*!< ACPI_EC0 OS_STATUS: CMD (Bitfield-Mask: 0x01)               */
#define ACPI_EC0_OS_STATUS_BURST_Pos          (4UL)                     /*!< ACPI_EC0 OS_STATUS: BURST (Bit 4)                           */
#define ACPI_EC0_OS_STATUS_BURST_Msk          (0x10UL)                  /*!< ACPI_EC0 OS_STATUS: BURST (Bitfield-Mask: 0x01)             */
#define ACPI_EC0_OS_STATUS_SCI_EVT_Pos        (5UL)                     /*!< ACPI_EC0 OS_STATUS: SCI_EVT (Bit 5)                         */
#define ACPI_EC0_OS_STATUS_SCI_EVT_Msk        (0x20UL)                  /*!< ACPI_EC0 OS_STATUS: SCI_EVT (Bitfield-Mask: 0x01)           */
#define ACPI_EC0_OS_STATUS_SMI_EVT_Pos        (6UL)                     /*!< ACPI_EC0 OS_STATUS: SMI_EVT (Bit 6)                         */
#define ACPI_EC0_OS_STATUS_SMI_EVT_Msk        (0x40UL)                  /*!< ACPI_EC0 OS_STATUS: SMI_EVT (Bitfield-Mask: 0x01)           */
#define ACPI_EC0_OS_STATUS_UD0B_Pos           (7UL)                     /*!< ACPI_EC0 OS_STATUS: UD0B (Bit 7)                            */
#define ACPI_EC0_OS_STATUS_UD0B_Msk           (0x80UL)                  /*!< ACPI_EC0 OS_STATUS: UD0B (Bitfield-Mask: 0x01)              */

/* -----------------------------  ACPI_EC0_EC_STATUS  ----------------------------- */
#define ACPI_EC0_EC_STATUS_OBF_Pos            (0UL)                     /*!< ACPI_EC0 EC_STATUS: OBF (Bit 0)                             */
#define ACPI_EC0_EC_STATUS_OBF_Msk            (0x1UL)                   /*!< ACPI_EC0 EC_STATUS: OBF (Bitfield-Mask: 0x01)               */
#define ACPI_EC0_EC_STATUS_IBF_Pos            (1UL)                     /*!< ACPI_EC0 EC_STATUS: IBF (Bit 1)                             */
#define ACPI_EC0_EC_STATUS_IBF_Msk            (0x2UL)                   /*!< ACPI_EC0 EC_STATUS: IBF (Bitfield-Mask: 0x01)               */
#define ACPI_EC0_EC_STATUS_UD1A_Pos           (2UL)                     /*!< ACPI_EC0 EC_STATUS: UD1A (Bit 2)                            */
#define ACPI_EC0_EC_STATUS_UD1A_Msk           (0x4UL)                   /*!< ACPI_EC0 EC_STATUS: UD1A (Bitfield-Mask: 0x01)              */
#define ACPI_EC0_EC_STATUS_CMD_Pos            (3UL)                     /*!< ACPI_EC0 EC_STATUS: CMD (Bit 3)                             */
#define ACPI_EC0_EC_STATUS_CMD_Msk            (0x8UL)                   /*!< ACPI_EC0 EC_STATUS: CMD (Bitfield-Mask: 0x01)               */
#define ACPI_EC0_EC_STATUS_BURST_Pos          (4UL)                     /*!< ACPI_EC0 EC_STATUS: BURST (Bit 4)                           */
#define ACPI_EC0_EC_STATUS_BURST_Msk          (0x10UL)                  /*!< ACPI_EC0 EC_STATUS: BURST (Bitfield-Mask: 0x01)             */
#define ACPI_EC0_EC_STATUS_SCI_EVT_Pos        (5UL)                     /*!< ACPI_EC0 EC_STATUS: SCI_EVT (Bit 5)                         */
#define ACPI_EC0_EC_STATUS_SCI_EVT_Msk        (0x20UL)                  /*!< ACPI_EC0 EC_STATUS: SCI_EVT (Bitfield-Mask: 0x01)           */
#define ACPI_EC0_EC_STATUS_SMI_EVT_Pos        (6UL)                     /*!< ACPI_EC0 EC_STATUS: SMI_EVT (Bit 6)                         */
#define ACPI_EC0_EC_STATUS_SMI_EVT_Msk        (0x40UL)                  /*!< ACPI_EC0 EC_STATUS: SMI_EVT (Bitfield-Mask: 0x01)           */
#define ACPI_EC0_EC_STATUS_UD0A_Pos           (7UL)                     /*!< ACPI_EC0 EC_STATUS: UD0A (Bit 7)                            */
#define ACPI_EC0_EC_STATUS_UD0A_Msk           (0x80UL)                  /*!< ACPI_EC0 EC_STATUS: UD0A (Bitfield-Mask: 0x01)              */


/* ================================================================================ */
/* ================          struct 'MBX' Position & Mask          ================ */
/* ================================================================================ */


/* -------------------------------  MBX_SMI_SOURCE  ------------------------------- */
#define MBX_SMI_SOURCE_EC_WR_Pos              (0UL)                     /*!< MBX SMI_SOURCE: EC_WR (Bit 0)                               */
#define MBX_SMI_SOURCE_EC_WR_Msk              (0x1UL)                   /*!< MBX SMI_SOURCE: EC_WR (Bitfield-Mask: 0x01)                 */
#define MBX_SMI_SOURCE_EC_SMI_Pos             (1UL)                     /*!< MBX SMI_SOURCE: EC_SMI (Bit 1)                              */
#define MBX_SMI_SOURCE_EC_SMI_Msk             (0xfeUL)                  /*!< MBX SMI_SOURCE: EC_SMI (Bitfield-Mask: 0x7f)                */

/* --------------------------------  MBX_SMI_MASK  -------------------------------- */
#define MBX_SMI_MASK_EC_WR_EN_Pos             (0UL)                     /*!< MBX SMI_MASK: EC_WR_EN (Bit 0)                              */
#define MBX_SMI_MASK_EC_WR_EN_Msk             (0x1UL)                   /*!< MBX SMI_MASK: EC_WR_EN (Bitfield-Mask: 0x01)                */
#define MBX_SMI_MASK_EC_SMI_EN_Pos            (1UL)                     /*!< MBX SMI_MASK: EC_SMI_EN (Bit 1)                             */
#define MBX_SMI_MASK_EC_SMI_EN_Msk            (0xfeUL)                  /*!< MBX SMI_MASK: EC_SMI_EN (Bitfield-Mask: 0x7f)               */


/* ================================================================================ */
/* ================          struct 'PM1' Position & Mask          ================ */
/* ================================================================================ */


/* ----------------------------------  PM1_STS2  ---------------------------------- */
#define PM1_STS2_PWRBTN_STS_Pos               (0UL)                     /*!< PM1 STS2: PWRBTN_STS (Bit 0)                                */
#define PM1_STS2_PWRBTN_STS_Msk               (0x1UL)                   /*!< PM1 STS2: PWRBTN_STS (Bitfield-Mask: 0x01)                  */
#define PM1_STS2_SLPBTN_STS_Pos               (1UL)                     /*!< PM1 STS2: SLPBTN_STS (Bit 1)                                */
#define PM1_STS2_SLPBTN_STS_Msk               (0x2UL)                   /*!< PM1 STS2: SLPBTN_STS (Bitfield-Mask: 0x01)                  */
#define PM1_STS2_RTC_STS_Pos                  (2UL)                     /*!< PM1 STS2: RTC_STS (Bit 2)                                   */
#define PM1_STS2_RTC_STS_Msk                  (0x4UL)                   /*!< PM1 STS2: RTC_STS (Bitfield-Mask: 0x01)                     */
#define PM1_STS2_PWRBTNOR_STS_Pos             (3UL)                     /*!< PM1 STS2: PWRBTNOR_STS (Bit 3)                              */
#define PM1_STS2_PWRBTNOR_STS_Msk             (0x8UL)                   /*!< PM1 STS2: PWRBTNOR_STS (Bitfield-Mask: 0x01)                */
#define PM1_STS2_WAK_STS_Pos                  (7UL)                     /*!< PM1 STS2: WAK_STS (Bit 7)                                   */
#define PM1_STS2_WAK_STS_Msk                  (0x80UL)                  /*!< PM1 STS2: WAK_STS (Bitfield-Mask: 0x01)                     */

/* -----------------------------------  PM1_EN2  ---------------------------------- */
#define PM1_EN2_PWRBTN_EN_Pos                 (0UL)                     /*!< PM1 EN2: PWRBTN_EN (Bit 0)                                  */
#define PM1_EN2_PWRBTN_EN_Msk                 (0x1UL)                   /*!< PM1 EN2: PWRBTN_EN (Bitfield-Mask: 0x01)                    */
#define PM1_EN2_SLPBTN_EN_Pos                 (1UL)                     /*!< PM1 EN2: SLPBTN_EN (Bit 1)                                  */
#define PM1_EN2_SLPBTN_EN_Msk                 (0x2UL)                   /*!< PM1 EN2: SLPBTN_EN (Bitfield-Mask: 0x01)                    */
#define PM1_EN2_RTC_EN_Pos                    (2UL)                     /*!< PM1 EN2: RTC_EN (Bit 2)                                     */
#define PM1_EN2_RTC_EN_Msk                    (0x4UL)                   /*!< PM1 EN2: RTC_EN (Bitfield-Mask: 0x01)                       */

/* ----------------------------------  PM1_CTRL2  --------------------------------- */
#define PM1_CTRL2_PWRBTNOR_EN_Pos             (1UL)                     /*!< PM1 CTRL2: PWRBTNOR_EN (Bit 1)                              */
#define PM1_CTRL2_PWRBTNOR_EN_Msk             (0x2UL)                   /*!< PM1 CTRL2: PWRBTNOR_EN (Bitfield-Mask: 0x01)                */
#define PM1_CTRL2_SLP_TYP_Pos                 (2UL)                     /*!< PM1 CTRL2: SLP_TYP (Bit 2)                                  */
#define PM1_CTRL2_SLP_TYP_Msk                 (0x1cUL)                  /*!< PM1 CTRL2: SLP_TYP (Bitfield-Mask: 0x07)                    */
#define PM1_CTRL2_SLP_EN_Pos                  (5UL)                     /*!< PM1 CTRL2: SLP_EN (Bit 5)                                   */
#define PM1_CTRL2_SLP_EN_Msk                  (0x20UL)                  /*!< PM1 CTRL2: SLP_EN (Bitfield-Mask: 0x01)                     */

/* ----------------------------------  PM1_STS_2  --------------------------------- */
#define PM1_STS_2_PWRBTN_STS_Pos              (0UL)                     /*!< PM1 STS_2: PWRBTN_STS (Bit 0)                               */
#define PM1_STS_2_PWRBTN_STS_Msk              (0x1UL)                   /*!< PM1 STS_2: PWRBTN_STS (Bitfield-Mask: 0x01)                 */
#define PM1_STS_2_SLPBTN_STS_Pos              (1UL)                     /*!< PM1 STS_2: SLPBTN_STS (Bit 1)                               */
#define PM1_STS_2_SLPBTN_STS_Msk              (0x2UL)                   /*!< PM1 STS_2: SLPBTN_STS (Bitfield-Mask: 0x01)                 */
#define PM1_STS_2_RTC_STS_Pos                 (2UL)                     /*!< PM1 STS_2: RTC_STS (Bit 2)                                  */
#define PM1_STS_2_RTC_STS_Msk                 (0x4UL)                   /*!< PM1 STS_2: RTC_STS (Bitfield-Mask: 0x01)                    */
#define PM1_STS_2_PWRBTNOR_STS_Pos            (3UL)                     /*!< PM1 STS_2: PWRBTNOR_STS (Bit 3)                             */
#define PM1_STS_2_PWRBTNOR_STS_Msk            (0x8UL)                   /*!< PM1 STS_2: PWRBTNOR_STS (Bitfield-Mask: 0x01)               */
#define PM1_STS_2_WAK_STS_Pos                 (7UL)                     /*!< PM1 STS_2: WAK_STS (Bit 7)                                  */
#define PM1_STS_2_WAK_STS_Msk                 (0x80UL)                  /*!< PM1 STS_2: WAK_STS (Bitfield-Mask: 0x01)                    */

/* ----------------------------------  PM1_EN_2  ---------------------------------- */
#define PM1_EN_2_PWRBTN_EN_Pos                (0UL)                     /*!< PM1 EN_2: PWRBTN_EN (Bit 0)                                 */
#define PM1_EN_2_PWRBTN_EN_Msk                (0x1UL)                   /*!< PM1 EN_2: PWRBTN_EN (Bitfield-Mask: 0x01)                   */
#define PM1_EN_2_SLPBTN_EN_Pos                (1UL)                     /*!< PM1 EN_2: SLPBTN_EN (Bit 1)                                 */
#define PM1_EN_2_SLPBTN_EN_Msk                (0x2UL)                   /*!< PM1 EN_2: SLPBTN_EN (Bitfield-Mask: 0x01)                   */
#define PM1_EN_2_RTC_EN_Pos                   (2UL)                     /*!< PM1 EN_2: RTC_EN (Bit 2)                                    */
#define PM1_EN_2_RTC_EN_Msk                   (0x4UL)                   /*!< PM1 EN_2: RTC_EN (Bitfield-Mask: 0x01)                      */

/* ---------------------------------  PM1_CTRL_2  --------------------------------- */
#define PM1_CTRL_2_PWRBTNOR_EN_Pos            (1UL)                     /*!< PM1 CTRL_2: PWRBTNOR_EN (Bit 1)                             */
#define PM1_CTRL_2_PWRBTNOR_EN_Msk            (0x2UL)                   /*!< PM1 CTRL_2: PWRBTNOR_EN (Bitfield-Mask: 0x01)               */
#define PM1_CTRL_2_SLP_TYP_Pos                (2UL)                     /*!< PM1 CTRL_2: SLP_TYP (Bit 2)                                 */
#define PM1_CTRL_2_SLP_TYP_Msk                (0x1cUL)                  /*!< PM1 CTRL_2: SLP_TYP (Bitfield-Mask: 0x07)                   */
#define PM1_CTRL_2_SLP_EN_Pos                 (5UL)                     /*!< PM1 CTRL_2: SLP_EN (Bit 5)                                  */
#define PM1_CTRL_2_SLP_EN_Msk                 (0x20UL)                  /*!< PM1 CTRL_2: SLP_EN (Bitfield-Mask: 0x01)                    */


/* ================================================================================ */
/* ================          struct 'UART' Position & Mask         ================ */
/* ================================================================================ */


/* ---------------------------------  UART_INT_EN  -------------------------------- */
#define UART_INT_EN_ERDAI_Pos                 (0UL)                     /*!< UART INT_EN: ERDAI (Bit 0)                                  */
#define UART_INT_EN_ERDAI_Msk                 (0x1UL)                   /*!< UART INT_EN: ERDAI (Bitfield-Mask: 0x01)                    */
#define UART_INT_EN_ETHREI_Pos                (1UL)                     /*!< UART INT_EN: ETHREI (Bit 1)                                 */
#define UART_INT_EN_ETHREI_Msk                (0x2UL)                   /*!< UART INT_EN: ETHREI (Bitfield-Mask: 0x01)                   */
#define UART_INT_EN_ELSI_Pos                  (2UL)                     /*!< UART INT_EN: ELSI (Bit 2)                                   */
#define UART_INT_EN_ELSI_Msk                  (0x4UL)                   /*!< UART INT_EN: ELSI (Bitfield-Mask: 0x01)                     */
#define UART_INT_EN_EMSI_Pos                  (3UL)                     /*!< UART INT_EN: EMSI (Bit 3)                                   */
#define UART_INT_EN_EMSI_Msk                  (0x8UL)                   /*!< UART INT_EN: EMSI (Bitfield-Mask: 0x01)                     */

/* --------------------------------  UART_FIFO_CR  -------------------------------- */
#define UART_FIFO_CR_EXRF_Pos                 (0UL)                     /*!< UART FIFO_CR: EXRF (Bit 0)                                  */
#define UART_FIFO_CR_EXRF_Msk                 (0x1UL)                   /*!< UART FIFO_CR: EXRF (Bitfield-Mask: 0x01)                    */
#define UART_FIFO_CR_CLEAR_RECV_FIFO_Pos      (1UL)                     /*!< UART FIFO_CR: CLEAR_RECV_FIFO (Bit 1)                       */
#define UART_FIFO_CR_CLEAR_RECV_FIFO_Msk      (0x2UL)                   /*!< UART FIFO_CR: CLEAR_RECV_FIFO (Bitfield-Mask: 0x01)         */
#define UART_FIFO_CR_CLEAR_XMIT_FIFO_Pos      (2UL)                     /*!< UART FIFO_CR: CLEAR_XMIT_FIFO (Bit 2)                       */
#define UART_FIFO_CR_CLEAR_XMIT_FIFO_Msk      (0x4UL)                   /*!< UART FIFO_CR: CLEAR_XMIT_FIFO (Bitfield-Mask: 0x01)         */
#define UART_FIFO_CR_DMA_MODE_SELECT_Pos      (3UL)                     /*!< UART FIFO_CR: DMA_MODE_SELECT (Bit 3)                       */
#define UART_FIFO_CR_DMA_MODE_SELECT_Msk      (0x8UL)                   /*!< UART FIFO_CR: DMA_MODE_SELECT (Bitfield-Mask: 0x01)         */
#define UART_FIFO_CR_RECV_FIFO_TRIGGER_LEVEL_Pos (6UL)                  /*!< UART FIFO_CR: RECV_FIFO_TRIGGER_LEVEL (Bit 6)               */
#define UART_FIFO_CR_RECV_FIFO_TRIGGER_LEVEL_Msk (0xc0UL)               /*!< UART FIFO_CR: RECV_FIFO_TRIGGER_LEVEL (Bitfield-Mask: 0x03) */

/* ---------------------------------  UART_INT_ID  -------------------------------- */
#define UART_INT_ID_IPEND_Pos                 (0UL)                     /*!< UART INT_ID: IPEND (Bit 0)                                  */
#define UART_INT_ID_IPEND_Msk                 (0x1UL)                   /*!< UART INT_ID: IPEND (Bitfield-Mask: 0x01)                    */
#define UART_INT_ID_INTID_Pos                 (1UL)                     /*!< UART INT_ID: INTID (Bit 1)                                  */
#define UART_INT_ID_INTID_Msk                 (0xeUL)                   /*!< UART INT_ID: INTID (Bitfield-Mask: 0x07)                    */
#define UART_INT_ID_FIFO_EN_Pos               (6UL)                     /*!< UART INT_ID: FIFO_EN (Bit 6)                                */
#define UART_INT_ID_FIFO_EN_Msk               (0xc0UL)                  /*!< UART INT_ID: FIFO_EN (Bitfield-Mask: 0x03)                  */

/* --------------------------------  UART_LINE_CR  -------------------------------- */
#define UART_LINE_CR_WORD_LENGTH_Pos          (0UL)                     /*!< UART LINE_CR: WORD_LENGTH (Bit 0)                           */
#define UART_LINE_CR_WORD_LENGTH_Msk          (0x3UL)                   /*!< UART LINE_CR: WORD_LENGTH (Bitfield-Mask: 0x03)             */
#define UART_LINE_CR_STOP_BITS_Pos            (2UL)                     /*!< UART LINE_CR: STOP_BITS (Bit 2)                             */
#define UART_LINE_CR_STOP_BITS_Msk            (0x4UL)                   /*!< UART LINE_CR: STOP_BITS (Bitfield-Mask: 0x01)               */
#define UART_LINE_CR_ENABLE_PARITY_Pos        (3UL)                     /*!< UART LINE_CR: ENABLE_PARITY (Bit 3)                         */
#define UART_LINE_CR_ENABLE_PARITY_Msk        (0x8UL)                   /*!< UART LINE_CR: ENABLE_PARITY (Bitfield-Mask: 0x01)           */
#define UART_LINE_CR_PARITY_SELECT_Pos        (4UL)                     /*!< UART LINE_CR: PARITY_SELECT (Bit 4)                         */
#define UART_LINE_CR_PARITY_SELECT_Msk        (0x10UL)                  /*!< UART LINE_CR: PARITY_SELECT (Bitfield-Mask: 0x01)           */
#define UART_LINE_CR_STICK_PARITY_Pos         (5UL)                     /*!< UART LINE_CR: STICK_PARITY (Bit 5)                          */
#define UART_LINE_CR_STICK_PARITY_Msk         (0x20UL)                  /*!< UART LINE_CR: STICK_PARITY (Bitfield-Mask: 0x01)            */
#define UART_LINE_CR_BREAK_CONTROL_Pos        (6UL)                     /*!< UART LINE_CR: BREAK_CONTROL (Bit 6)                         */
#define UART_LINE_CR_BREAK_CONTROL_Msk        (0x40UL)                  /*!< UART LINE_CR: BREAK_CONTROL (Bitfield-Mask: 0x01)           */
#define UART_LINE_CR_DLAB_Pos                 (7UL)                     /*!< UART LINE_CR: DLAB (Bit 7)                                  */
#define UART_LINE_CR_DLAB_Msk                 (0x80UL)                  /*!< UART LINE_CR: DLAB (Bitfield-Mask: 0x01)                    */

/* --------------------------------  UART_MODEM_CR  ------------------------------- */
#define UART_MODEM_CR_DTR_Pos                 (0UL)                     /*!< UART MODEM_CR: DTR (Bit 0)                                  */
#define UART_MODEM_CR_DTR_Msk                 (0x1UL)                   /*!< UART MODEM_CR: DTR (Bitfield-Mask: 0x01)                    */
#define UART_MODEM_CR_RTS_Pos                 (1UL)                     /*!< UART MODEM_CR: RTS (Bit 1)                                  */
#define UART_MODEM_CR_RTS_Msk                 (0x2UL)                   /*!< UART MODEM_CR: RTS (Bitfield-Mask: 0x01)                    */
#define UART_MODEM_CR_OUT1_Pos                (2UL)                     /*!< UART MODEM_CR: OUT1 (Bit 2)                                 */
#define UART_MODEM_CR_OUT1_Msk                (0x4UL)                   /*!< UART MODEM_CR: OUT1 (Bitfield-Mask: 0x01)                   */
#define UART_MODEM_CR_OUT2_Pos                (3UL)                     /*!< UART MODEM_CR: OUT2 (Bit 3)                                 */
#define UART_MODEM_CR_OUT2_Msk                (0x8UL)                   /*!< UART MODEM_CR: OUT2 (Bitfield-Mask: 0x01)                   */
#define UART_MODEM_CR_LOOPBACK_Pos            (4UL)                     /*!< UART MODEM_CR: LOOPBACK (Bit 4)                             */
#define UART_MODEM_CR_LOOPBACK_Msk            (0x10UL)                  /*!< UART MODEM_CR: LOOPBACK (Bitfield-Mask: 0x01)               */

/* --------------------------------  UART_LINE_STS  ------------------------------- */
#define UART_LINE_STS_DATA_READY_Pos          (0UL)                     /*!< UART LINE_STS: DATA_READY (Bit 0)                           */
#define UART_LINE_STS_DATA_READY_Msk          (0x1UL)                   /*!< UART LINE_STS: DATA_READY (Bitfield-Mask: 0x01)             */
#define UART_LINE_STS_OVERRUN_Pos             (1UL)                     /*!< UART LINE_STS: OVERRUN (Bit 1)                              */
#define UART_LINE_STS_OVERRUN_Msk             (0x2UL)                   /*!< UART LINE_STS: OVERRUN (Bitfield-Mask: 0x01)                */
#define UART_LINE_STS_PE_Pos                  (2UL)                     /*!< UART LINE_STS: PE (Bit 2)                                   */
#define UART_LINE_STS_PE_Msk                  (0x4UL)                   /*!< UART LINE_STS: PE (Bitfield-Mask: 0x01)                     */
#define UART_LINE_STS_FRAME_ERROR_Pos         (3UL)                     /*!< UART LINE_STS: FRAME_ERROR (Bit 3)                          */
#define UART_LINE_STS_FRAME_ERROR_Msk         (0x8UL)                   /*!< UART LINE_STS: FRAME_ERROR (Bitfield-Mask: 0x01)            */
#define UART_LINE_STS_BREAK_INTERRUPT_Pos     (4UL)                     /*!< UART LINE_STS: BREAK_INTERRUPT (Bit 4)                      */
#define UART_LINE_STS_BREAK_INTERRUPT_Msk     (0x10UL)                  /*!< UART LINE_STS: BREAK_INTERRUPT (Bitfield-Mask: 0x01)        */
#define UART_LINE_STS_TRANSMIT_EMPTY_Pos      (5UL)                     /*!< UART LINE_STS: TRANSMIT_EMPTY (Bit 5)                       */
#define UART_LINE_STS_TRANSMIT_EMPTY_Msk      (0x20UL)                  /*!< UART LINE_STS: TRANSMIT_EMPTY (Bitfield-Mask: 0x01)         */
#define UART_LINE_STS_TRANSMIT_ERROR_Pos      (6UL)                     /*!< UART LINE_STS: TRANSMIT_ERROR (Bit 6)                       */
#define UART_LINE_STS_TRANSMIT_ERROR_Msk      (0x40UL)                  /*!< UART LINE_STS: TRANSMIT_ERROR (Bitfield-Mask: 0x01)         */
#define UART_LINE_STS_FIFO_ERROR_Pos          (7UL)                     /*!< UART LINE_STS: FIFO_ERROR (Bit 7)                           */
#define UART_LINE_STS_FIFO_ERROR_Msk          (0x80UL)                  /*!< UART LINE_STS: FIFO_ERROR (Bitfield-Mask: 0x01)             */

/* -------------------------------  UART_MODEM_STS  ------------------------------- */
#define UART_MODEM_STS_CTS_Pos                (0UL)                     /*!< UART MODEM_STS: CTS (Bit 0)                                 */
#define UART_MODEM_STS_CTS_Msk                (0x1UL)                   /*!< UART MODEM_STS: CTS (Bitfield-Mask: 0x01)                   */
#define UART_MODEM_STS_DSR_Pos                (1UL)                     /*!< UART MODEM_STS: DSR (Bit 1)                                 */
#define UART_MODEM_STS_DSR_Msk                (0x2UL)                   /*!< UART MODEM_STS: DSR (Bitfield-Mask: 0x01)                   */
#define UART_MODEM_STS_RI_Pos                 (2UL)                     /*!< UART MODEM_STS: RI (Bit 2)                                  */
#define UART_MODEM_STS_RI_Msk                 (0x4UL)                   /*!< UART MODEM_STS: RI (Bitfield-Mask: 0x01)                    */
#define UART_MODEM_STS_DCD_Pos                (3UL)                     /*!< UART MODEM_STS: DCD (Bit 3)                                 */
#define UART_MODEM_STS_DCD_Msk                (0x8UL)                   /*!< UART MODEM_STS: DCD (Bitfield-Mask: 0x01)                   */
#define UART_MODEM_STS_nCTS_Pos               (4UL)                     /*!< UART MODEM_STS: nCTS (Bit 4)                                */
#define UART_MODEM_STS_nCTS_Msk               (0x10UL)                  /*!< UART MODEM_STS: nCTS (Bitfield-Mask: 0x01)                  */
#define UART_MODEM_STS_nDSR_Pos               (5UL)                     /*!< UART MODEM_STS: nDSR (Bit 5)                                */
#define UART_MODEM_STS_nDSR_Msk               (0x20UL)                  /*!< UART MODEM_STS: nDSR (Bitfield-Mask: 0x01)                  */
#define UART_MODEM_STS_nRI_Pos                (6UL)                     /*!< UART MODEM_STS: nRI (Bit 6)                                 */
#define UART_MODEM_STS_nRI_Msk                (0x40UL)                  /*!< UART MODEM_STS: nRI (Bitfield-Mask: 0x01)                   */
#define UART_MODEM_STS_nDCD_Pos               (7UL)                     /*!< UART MODEM_STS: nDCD (Bit 7)                                */
#define UART_MODEM_STS_nDCD_Msk               (0x80UL)                  /*!< UART MODEM_STS: nDCD (Bitfield-Mask: 0x01)                  */

/* ---------------------------------  UART_CONFIG  -------------------------------- */
#define UART_CONFIG_CLK_SRC_Pos               (0UL)                     /*!< UART CONFIG: CLK_SRC (Bit 0)                                */
#define UART_CONFIG_CLK_SRC_Msk               (0x1UL)                   /*!< UART CONFIG: CLK_SRC (Bitfield-Mask: 0x01)                  */
#define UART_CONFIG_POWER_Pos                 (1UL)                     /*!< UART CONFIG: POWER (Bit 1)                                  */
#define UART_CONFIG_POWER_Msk                 (0x2UL)                   /*!< UART CONFIG: POWER (Bitfield-Mask: 0x01)                    */
#define UART_CONFIG_POLARITY_Pos              (2UL)                     /*!< UART CONFIG: POLARITY (Bit 2)                               */
#define UART_CONFIG_POLARITY_Msk              (0x4UL)                   /*!< UART CONFIG: POLARITY (Bitfield-Mask: 0x01)                 */


/* ================================================================================ */
/* ================          struct 'WDT' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  WDT_CONTROL  -------------------------------- */
#define WDT_CONTROL_ENABLE_Pos                (0UL)                     /*!< WDT CONTROL: ENABLE (Bit 0)                                 */
#define WDT_CONTROL_ENABLE_Msk                (0x1UL)                   /*!< WDT CONTROL: ENABLE (Bitfield-Mask: 0x01)                   */
#define WDT_CONTROL_STATUS_Pos                (1UL)                     /*!< WDT CONTROL: STATUS (Bit 1)                                 */
#define WDT_CONTROL_STATUS_Msk                (0x2UL)                   /*!< WDT CONTROL: STATUS (Bitfield-Mask: 0x01)                   */


/* ================================================================================ */
/* ================       struct 'TIMER_16_0' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  TIMER_16_0_CONTROL  ----------------------------- */
#define TIMER_16_0_CONTROL_ENABLE_Pos         (0UL)                     /*!< TIMER_16_0 CONTROL: ENABLE (Bit 0)                          */
#define TIMER_16_0_CONTROL_ENABLE_Msk         (0x1UL)                   /*!< TIMER_16_0 CONTROL: ENABLE (Bitfield-Mask: 0x01)            */
#define TIMER_16_0_CONTROL_COUNT_UP_Pos       (2UL)                     /*!< TIMER_16_0 CONTROL: COUNT_UP (Bit 2)                        */
#define TIMER_16_0_CONTROL_COUNT_UP_Msk       (0x4UL)                   /*!< TIMER_16_0 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)          */
#define TIMER_16_0_CONTROL_AUTO_RESTART_Pos   (3UL)                     /*!< TIMER_16_0 CONTROL: AUTO_RESTART (Bit 3)                    */
#define TIMER_16_0_CONTROL_AUTO_RESTART_Msk   (0x8UL)                   /*!< TIMER_16_0 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)      */
#define TIMER_16_0_CONTROL_SOFT_RESET_Pos     (4UL)                     /*!< TIMER_16_0 CONTROL: SOFT_RESET (Bit 4)                      */
#define TIMER_16_0_CONTROL_SOFT_RESET_Msk     (0x10UL)                  /*!< TIMER_16_0 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)        */
#define TIMER_16_0_CONTROL_START_Pos          (5UL)                     /*!< TIMER_16_0 CONTROL: START (Bit 5)                           */
#define TIMER_16_0_CONTROL_START_Msk          (0x20UL)                  /*!< TIMER_16_0 CONTROL: START (Bitfield-Mask: 0x01)             */
#define TIMER_16_0_CONTROL_RELOAD_Pos         (6UL)                     /*!< TIMER_16_0 CONTROL: RELOAD (Bit 6)                          */
#define TIMER_16_0_CONTROL_RELOAD_Msk         (0x40UL)                  /*!< TIMER_16_0 CONTROL: RELOAD (Bitfield-Mask: 0x01)            */
#define TIMER_16_0_CONTROL_HALT_Pos           (7UL)                     /*!< TIMER_16_0 CONTROL: HALT (Bit 7)                            */
#define TIMER_16_0_CONTROL_HALT_Msk           (0x80UL)                  /*!< TIMER_16_0 CONTROL: HALT (Bitfield-Mask: 0x01)              */
#define TIMER_16_0_CONTROL_PRE_SCALE_Pos      (16UL)                    /*!< TIMER_16_0 CONTROL: PRE_SCALE (Bit 16)                      */
#define TIMER_16_0_CONTROL_PRE_SCALE_Msk      (0xffff0000UL)            /*!< TIMER_16_0 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)       */


/* ================================================================================ */
/* ================       struct 'TIMER_16_1' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  TIMER_16_1_CONTROL  ----------------------------- */
#define TIMER_16_1_CONTROL_ENABLE_Pos         (0UL)                     /*!< TIMER_16_1 CONTROL: ENABLE (Bit 0)                          */
#define TIMER_16_1_CONTROL_ENABLE_Msk         (0x1UL)                   /*!< TIMER_16_1 CONTROL: ENABLE (Bitfield-Mask: 0x01)            */
#define TIMER_16_1_CONTROL_COUNT_UP_Pos       (2UL)                     /*!< TIMER_16_1 CONTROL: COUNT_UP (Bit 2)                        */
#define TIMER_16_1_CONTROL_COUNT_UP_Msk       (0x4UL)                   /*!< TIMER_16_1 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)          */
#define TIMER_16_1_CONTROL_AUTO_RESTART_Pos   (3UL)                     /*!< TIMER_16_1 CONTROL: AUTO_RESTART (Bit 3)                    */
#define TIMER_16_1_CONTROL_AUTO_RESTART_Msk   (0x8UL)                   /*!< TIMER_16_1 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)      */
#define TIMER_16_1_CONTROL_SOFT_RESET_Pos     (4UL)                     /*!< TIMER_16_1 CONTROL: SOFT_RESET (Bit 4)                      */
#define TIMER_16_1_CONTROL_SOFT_RESET_Msk     (0x10UL)                  /*!< TIMER_16_1 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)        */
#define TIMER_16_1_CONTROL_START_Pos          (5UL)                     /*!< TIMER_16_1 CONTROL: START (Bit 5)                           */
#define TIMER_16_1_CONTROL_START_Msk          (0x20UL)                  /*!< TIMER_16_1 CONTROL: START (Bitfield-Mask: 0x01)             */
#define TIMER_16_1_CONTROL_RELOAD_Pos         (6UL)                     /*!< TIMER_16_1 CONTROL: RELOAD (Bit 6)                          */
#define TIMER_16_1_CONTROL_RELOAD_Msk         (0x40UL)                  /*!< TIMER_16_1 CONTROL: RELOAD (Bitfield-Mask: 0x01)            */
#define TIMER_16_1_CONTROL_HALT_Pos           (7UL)                     /*!< TIMER_16_1 CONTROL: HALT (Bit 7)                            */
#define TIMER_16_1_CONTROL_HALT_Msk           (0x80UL)                  /*!< TIMER_16_1 CONTROL: HALT (Bitfield-Mask: 0x01)              */
#define TIMER_16_1_CONTROL_PRE_SCALE_Pos      (16UL)                    /*!< TIMER_16_1 CONTROL: PRE_SCALE (Bit 16)                      */
#define TIMER_16_1_CONTROL_PRE_SCALE_Msk      (0xffff0000UL)            /*!< TIMER_16_1 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)       */


/* ================================================================================ */
/* ================       struct 'TIMER_16_2' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  TIMER_16_2_CONTROL  ----------------------------- */
#define TIMER_16_2_CONTROL_ENABLE_Pos         (0UL)                     /*!< TIMER_16_2 CONTROL: ENABLE (Bit 0)                          */
#define TIMER_16_2_CONTROL_ENABLE_Msk         (0x1UL)                   /*!< TIMER_16_2 CONTROL: ENABLE (Bitfield-Mask: 0x01)            */
#define TIMER_16_2_CONTROL_COUNT_UP_Pos       (2UL)                     /*!< TIMER_16_2 CONTROL: COUNT_UP (Bit 2)                        */
#define TIMER_16_2_CONTROL_COUNT_UP_Msk       (0x4UL)                   /*!< TIMER_16_2 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)          */
#define TIMER_16_2_CONTROL_AUTO_RESTART_Pos   (3UL)                     /*!< TIMER_16_2 CONTROL: AUTO_RESTART (Bit 3)                    */
#define TIMER_16_2_CONTROL_AUTO_RESTART_Msk   (0x8UL)                   /*!< TIMER_16_2 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)      */
#define TIMER_16_2_CONTROL_SOFT_RESET_Pos     (4UL)                     /*!< TIMER_16_2 CONTROL: SOFT_RESET (Bit 4)                      */
#define TIMER_16_2_CONTROL_SOFT_RESET_Msk     (0x10UL)                  /*!< TIMER_16_2 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)        */
#define TIMER_16_2_CONTROL_START_Pos          (5UL)                     /*!< TIMER_16_2 CONTROL: START (Bit 5)                           */
#define TIMER_16_2_CONTROL_START_Msk          (0x20UL)                  /*!< TIMER_16_2 CONTROL: START (Bitfield-Mask: 0x01)             */
#define TIMER_16_2_CONTROL_RELOAD_Pos         (6UL)                     /*!< TIMER_16_2 CONTROL: RELOAD (Bit 6)                          */
#define TIMER_16_2_CONTROL_RELOAD_Msk         (0x40UL)                  /*!< TIMER_16_2 CONTROL: RELOAD (Bitfield-Mask: 0x01)            */
#define TIMER_16_2_CONTROL_HALT_Pos           (7UL)                     /*!< TIMER_16_2 CONTROL: HALT (Bit 7)                            */
#define TIMER_16_2_CONTROL_HALT_Msk           (0x80UL)                  /*!< TIMER_16_2 CONTROL: HALT (Bitfield-Mask: 0x01)              */
#define TIMER_16_2_CONTROL_PRE_SCALE_Pos      (16UL)                    /*!< TIMER_16_2 CONTROL: PRE_SCALE (Bit 16)                      */
#define TIMER_16_2_CONTROL_PRE_SCALE_Msk      (0xffff0000UL)            /*!< TIMER_16_2 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)       */


/* ================================================================================ */
/* ================       struct 'TIMER_16_3' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  TIMER_16_3_CONTROL  ----------------------------- */
#define TIMER_16_3_CONTROL_ENABLE_Pos         (0UL)                     /*!< TIMER_16_3 CONTROL: ENABLE (Bit 0)                          */
#define TIMER_16_3_CONTROL_ENABLE_Msk         (0x1UL)                   /*!< TIMER_16_3 CONTROL: ENABLE (Bitfield-Mask: 0x01)            */
#define TIMER_16_3_CONTROL_COUNT_UP_Pos       (2UL)                     /*!< TIMER_16_3 CONTROL: COUNT_UP (Bit 2)                        */
#define TIMER_16_3_CONTROL_COUNT_UP_Msk       (0x4UL)                   /*!< TIMER_16_3 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)          */
#define TIMER_16_3_CONTROL_AUTO_RESTART_Pos   (3UL)                     /*!< TIMER_16_3 CONTROL: AUTO_RESTART (Bit 3)                    */
#define TIMER_16_3_CONTROL_AUTO_RESTART_Msk   (0x8UL)                   /*!< TIMER_16_3 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)      */
#define TIMER_16_3_CONTROL_SOFT_RESET_Pos     (4UL)                     /*!< TIMER_16_3 CONTROL: SOFT_RESET (Bit 4)                      */
#define TIMER_16_3_CONTROL_SOFT_RESET_Msk     (0x10UL)                  /*!< TIMER_16_3 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)        */
#define TIMER_16_3_CONTROL_START_Pos          (5UL)                     /*!< TIMER_16_3 CONTROL: START (Bit 5)                           */
#define TIMER_16_3_CONTROL_START_Msk          (0x20UL)                  /*!< TIMER_16_3 CONTROL: START (Bitfield-Mask: 0x01)             */
#define TIMER_16_3_CONTROL_RELOAD_Pos         (6UL)                     /*!< TIMER_16_3 CONTROL: RELOAD (Bit 6)                          */
#define TIMER_16_3_CONTROL_RELOAD_Msk         (0x40UL)                  /*!< TIMER_16_3 CONTROL: RELOAD (Bitfield-Mask: 0x01)            */
#define TIMER_16_3_CONTROL_HALT_Pos           (7UL)                     /*!< TIMER_16_3 CONTROL: HALT (Bit 7)                            */
#define TIMER_16_3_CONTROL_HALT_Msk           (0x80UL)                  /*!< TIMER_16_3 CONTROL: HALT (Bitfield-Mask: 0x01)              */
#define TIMER_16_3_CONTROL_PRE_SCALE_Pos      (16UL)                    /*!< TIMER_16_3 CONTROL: PRE_SCALE (Bit 16)                      */
#define TIMER_16_3_CONTROL_PRE_SCALE_Msk      (0xffff0000UL)            /*!< TIMER_16_3 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)       */


/* ================================================================================ */
/* ================       struct 'TIMER_32_0' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  TIMER_32_0_CONTROL  ----------------------------- */
#define TIMER_32_0_CONTROL_ENABLE_Pos         (0UL)                     /*!< TIMER_32_0 CONTROL: ENABLE (Bit 0)                          */
#define TIMER_32_0_CONTROL_ENABLE_Msk         (0x1UL)                   /*!< TIMER_32_0 CONTROL: ENABLE (Bitfield-Mask: 0x01)            */
#define TIMER_32_0_CONTROL_COUNT_UP_Pos       (2UL)                     /*!< TIMER_32_0 CONTROL: COUNT_UP (Bit 2)                        */
#define TIMER_32_0_CONTROL_COUNT_UP_Msk       (0x4UL)                   /*!< TIMER_32_0 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)          */
#define TIMER_32_0_CONTROL_AUTO_RESTART_Pos   (3UL)                     /*!< TIMER_32_0 CONTROL: AUTO_RESTART (Bit 3)                    */
#define TIMER_32_0_CONTROL_AUTO_RESTART_Msk   (0x8UL)                   /*!< TIMER_32_0 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)      */
#define TIMER_32_0_CONTROL_SOFT_RESET_Pos     (4UL)                     /*!< TIMER_32_0 CONTROL: SOFT_RESET (Bit 4)                      */
#define TIMER_32_0_CONTROL_SOFT_RESET_Msk     (0x10UL)                  /*!< TIMER_32_0 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)        */
#define TIMER_32_0_CONTROL_START_Pos          (5UL)                     /*!< TIMER_32_0 CONTROL: START (Bit 5)                           */
#define TIMER_32_0_CONTROL_START_Msk          (0x20UL)                  /*!< TIMER_32_0 CONTROL: START (Bitfield-Mask: 0x01)             */
#define TIMER_32_0_CONTROL_RELOAD_Pos         (6UL)                     /*!< TIMER_32_0 CONTROL: RELOAD (Bit 6)                          */
#define TIMER_32_0_CONTROL_RELOAD_Msk         (0x40UL)                  /*!< TIMER_32_0 CONTROL: RELOAD (Bitfield-Mask: 0x01)            */
#define TIMER_32_0_CONTROL_HALT_Pos           (7UL)                     /*!< TIMER_32_0 CONTROL: HALT (Bit 7)                            */
#define TIMER_32_0_CONTROL_HALT_Msk           (0x80UL)                  /*!< TIMER_32_0 CONTROL: HALT (Bitfield-Mask: 0x01)              */
#define TIMER_32_0_CONTROL_PRE_SCALE_Pos      (16UL)                    /*!< TIMER_32_0 CONTROL: PRE_SCALE (Bit 16)                      */
#define TIMER_32_0_CONTROL_PRE_SCALE_Msk      (0xffff0000UL)            /*!< TIMER_32_0 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)       */


/* ================================================================================ */
/* ================       struct 'TIMER_32_1' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  TIMER_32_1_CONTROL  ----------------------------- */
#define TIMER_32_1_CONTROL_ENABLE_Pos         (0UL)                     /*!< TIMER_32_1 CONTROL: ENABLE (Bit 0)                          */
#define TIMER_32_1_CONTROL_ENABLE_Msk         (0x1UL)                   /*!< TIMER_32_1 CONTROL: ENABLE (Bitfield-Mask: 0x01)            */
#define TIMER_32_1_CONTROL_COUNT_UP_Pos       (2UL)                     /*!< TIMER_32_1 CONTROL: COUNT_UP (Bit 2)                        */
#define TIMER_32_1_CONTROL_COUNT_UP_Msk       (0x4UL)                   /*!< TIMER_32_1 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)          */
#define TIMER_32_1_CONTROL_AUTO_RESTART_Pos   (3UL)                     /*!< TIMER_32_1 CONTROL: AUTO_RESTART (Bit 3)                    */
#define TIMER_32_1_CONTROL_AUTO_RESTART_Msk   (0x8UL)                   /*!< TIMER_32_1 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)      */
#define TIMER_32_1_CONTROL_SOFT_RESET_Pos     (4UL)                     /*!< TIMER_32_1 CONTROL: SOFT_RESET (Bit 4)                      */
#define TIMER_32_1_CONTROL_SOFT_RESET_Msk     (0x10UL)                  /*!< TIMER_32_1 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)        */
#define TIMER_32_1_CONTROL_START_Pos          (5UL)                     /*!< TIMER_32_1 CONTROL: START (Bit 5)                           */
#define TIMER_32_1_CONTROL_START_Msk          (0x20UL)                  /*!< TIMER_32_1 CONTROL: START (Bitfield-Mask: 0x01)             */
#define TIMER_32_1_CONTROL_RELOAD_Pos         (6UL)                     /*!< TIMER_32_1 CONTROL: RELOAD (Bit 6)                          */
#define TIMER_32_1_CONTROL_RELOAD_Msk         (0x40UL)                  /*!< TIMER_32_1 CONTROL: RELOAD (Bitfield-Mask: 0x01)            */
#define TIMER_32_1_CONTROL_HALT_Pos           (7UL)                     /*!< TIMER_32_1 CONTROL: HALT (Bit 7)                            */
#define TIMER_32_1_CONTROL_HALT_Msk           (0x80UL)                  /*!< TIMER_32_1 CONTROL: HALT (Bitfield-Mask: 0x01)              */
#define TIMER_32_1_CONTROL_PRE_SCALE_Pos      (16UL)                    /*!< TIMER_32_1 CONTROL: PRE_SCALE (Bit 16)                      */
#define TIMER_32_1_CONTROL_PRE_SCALE_Msk      (0xffff0000UL)            /*!< TIMER_32_1 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)       */


/* ================================================================================ */
/* ================          struct 'RTC' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  RTC_CONTROL  -------------------------------- */
#define RTC_CONTROL_BLOCK_ENABLE_Pos          (0UL)                     /*!< RTC CONTROL: BLOCK_ENABLE (Bit 0)                           */
#define RTC_CONTROL_BLOCK_ENABLE_Msk          (0x1UL)                   /*!< RTC CONTROL: BLOCK_ENABLE (Bitfield-Mask: 0x01)             */
#define RTC_CONTROL_SOFT_RESET_Pos            (1UL)                     /*!< RTC CONTROL: SOFT_RESET (Bit 1)                             */
#define RTC_CONTROL_SOFT_RESET_Msk            (0x2UL)                   /*!< RTC CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)               */
#define RTC_CONTROL_ALARM_ENABLE_Pos          (3UL)                     /*!< RTC CONTROL: ALARM_ENABLE (Bit 3)                           */
#define RTC_CONTROL_ALARM_ENABLE_Msk          (0x8UL)                   /*!< RTC CONTROL: ALARM_ENABLE (Bitfield-Mask: 0x01)             */

/* ------------------------  RTC_DAYLIGHT_SAVINGS_FORWARD  ------------------------ */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_MONTH_Pos (0UL)                /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_MONTH (Bit 0)             */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_MONTH_Msk (0xffUL)             /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_MONTH (Bitfield-Mask: 0xff) */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_DAY_OF_WEEK_Pos (8UL)          /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_DAY_OF_WEEK (Bit 8)       */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_DAY_OF_WEEK_Msk (0x700UL)      /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_DAY_OF_WEEK (Bitfield-Mask: 0x07) */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_WEEK_Pos (16UL)                /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_WEEK (Bit 16)             */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_WEEK_Msk (0x70000UL)           /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_WEEK (Bitfield-Mask: 0x07) */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_HOUR_Pos (24UL)                /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_HOUR (Bit 24)             */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_HOUR_Msk (0x7f000000UL)        /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_HOUR (Bitfield-Mask: 0x7f) */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_AM_PM_Pos (31UL)               /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_AM_PM (Bit 31)            */
#define RTC_DAYLIGHT_SAVINGS_FORWARD_DST_AM_PM_Msk (0x80000000UL)       /*!< RTC DAYLIGHT_SAVINGS_FORWARD: DST_AM_PM (Bitfield-Mask: 0x01) */

/* ------------------------  RTC_DAYLIGHT_SAVINGS_BACKWARD  ----------------------- */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_MONTH_Pos (0UL)               /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_MONTH (Bit 0)            */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_MONTH_Msk (0xffUL)            /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_MONTH (Bitfield-Mask: 0xff) */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_DAY_OF_WEEK_Pos (8UL)         /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_DAY_OF_WEEK (Bit 8)      */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_DAY_OF_WEEK_Msk (0x700UL)     /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_DAY_OF_WEEK (Bitfield-Mask: 0x07) */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_WEEK_Pos (16UL)               /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_WEEK (Bit 16)            */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_WEEK_Msk (0x70000UL)          /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_WEEK (Bitfield-Mask: 0x07) */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_HOUR_Pos (24UL)               /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_HOUR (Bit 24)            */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_HOUR_Msk (0x7f000000UL)       /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_HOUR (Bitfield-Mask: 0x7f) */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_AM_PM_Pos (31UL)              /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_AM_PM (Bit 31)           */
#define RTC_DAYLIGHT_SAVINGS_BACKWARD_DST_AM_PM_Msk (0x80000000UL)      /*!< RTC DAYLIGHT_SAVINGS_BACKWARD: DST_AM_PM (Bitfield-Mask: 0x01) */


/* ================================================================================ */
/* ================          struct 'GPIO' Position & Mask         ================ */
/* ================================================================================ */


/* ------------------------------  GPIO_PIN_CONTROL  ------------------------------ */
#define GPIO_PIN_CONTROL_PU_PD_Pos            (0UL)                     /*!< GPIO PIN_CONTROL: PU_PD (Bit 0)                             */
#define GPIO_PIN_CONTROL_PU_PD_Msk            (0x3UL)                   /*!< GPIO PIN_CONTROL: PU_PD (Bitfield-Mask: 0x03)               */
#define GPIO_PIN_CONTROL_PWR_Pos              (2UL)                     /*!< GPIO PIN_CONTROL: PWR (Bit 2)                               */
#define GPIO_PIN_CONTROL_PWR_Msk              (0xcUL)                   /*!< GPIO PIN_CONTROL: PWR (Bitfield-Mask: 0x03)                 */
#define GPIO_PIN_CONTROL_INT_DET_Pos          (4UL)                     /*!< GPIO PIN_CONTROL: INT_DET (Bit 4)                           */
#define GPIO_PIN_CONTROL_INT_DET_Msk          (0x70UL)                  /*!< GPIO PIN_CONTROL: INT_DET (Bitfield-Mask: 0x07)             */
#define GPIO_PIN_CONTROL_EDGE_EN_Pos          (7UL)                     /*!< GPIO PIN_CONTROL: EDGE_EN (Bit 7)                           */
#define GPIO_PIN_CONTROL_EDGE_EN_Msk          (0x80UL)                  /*!< GPIO PIN_CONTROL: EDGE_EN (Bitfield-Mask: 0x01)             */
#define GPIO_PIN_CONTROL_BUFFER_Pos           (8UL)                     /*!< GPIO PIN_CONTROL: BUFFER (Bit 8)                            */
#define GPIO_PIN_CONTROL_BUFFER_Msk           (0x100UL)                 /*!< GPIO PIN_CONTROL: BUFFER (Bitfield-Mask: 0x01)              */
#define GPIO_PIN_CONTROL_DIR_Pos              (9UL)                     /*!< GPIO PIN_CONTROL: DIR (Bit 9)                               */
#define GPIO_PIN_CONTROL_DIR_Msk              (0x200UL)                 /*!< GPIO PIN_CONTROL: DIR (Bitfield-Mask: 0x01)                 */
#define GPIO_PIN_CONTROL_OUTPUT_WRITE_EN_Pos  (10UL)                    /*!< GPIO PIN_CONTROL: OUTPUT_WRITE_EN (Bit 10)                  */
#define GPIO_PIN_CONTROL_OUTPUT_WRITE_EN_Msk  (0x400UL)                 /*!< GPIO PIN_CONTROL: OUTPUT_WRITE_EN (Bitfield-Mask: 0x01)     */
#define GPIO_PIN_CONTROL_POLARITY_Pos         (11UL)                    /*!< GPIO PIN_CONTROL: POLARITY (Bit 11)                         */
#define GPIO_PIN_CONTROL_POLARITY_Msk         (0x800UL)                 /*!< GPIO PIN_CONTROL: POLARITY (Bitfield-Mask: 0x01)            */
#define GPIO_PIN_CONTROL_MUX_Pos              (12UL)                    /*!< GPIO PIN_CONTROL: MUX (Bit 12)                              */
#define GPIO_PIN_CONTROL_MUX_Msk              (0x3000UL)                /*!< GPIO PIN_CONTROL: MUX (Bitfield-Mask: 0x03)                 */
#define GPIO_PIN_CONTROL_OUTPUT_Pos           (16UL)                    /*!< GPIO PIN_CONTROL: OUTPUT (Bit 16)                           */
#define GPIO_PIN_CONTROL_OUTPUT_Msk           (0x10000UL)               /*!< GPIO PIN_CONTROL: OUTPUT (Bitfield-Mask: 0x01)              */
#define GPIO_PIN_CONTROL_INPUT_Pos            (24UL)                    /*!< GPIO PIN_CONTROL: INPUT (Bit 24)                            */
#define GPIO_PIN_CONTROL_INPUT_Msk            (0x1000000UL)             /*!< GPIO PIN_CONTROL: INPUT (Bitfield-Mask: 0x01)               */

/* ----------------------------  GPIO_CONTROL2_000_067  --------------------------- */
#define GPIO_CONTROL2_000_067_SLEW_RATE_Pos   (0UL)                     /*!< GPIO CONTROL2_000_067: SLEW_RATE (Bit 0)                    */
#define GPIO_CONTROL2_000_067_SLEW_RATE_Msk   (0x1UL)                   /*!< GPIO CONTROL2_000_067: SLEW_RATE (Bitfield-Mask: 0x01)      */
#define GPIO_CONTROL2_000_067_DRIVE_STRENGTH_Pos (4UL)                  /*!< GPIO CONTROL2_000_067: DRIVE_STRENGTH (Bit 4)               */
#define GPIO_CONTROL2_000_067_DRIVE_STRENGTH_Msk (0x30UL)               /*!< GPIO CONTROL2_000_067: DRIVE_STRENGTH (Bitfield-Mask: 0x03) */

/* ----------------------------  GPIO_CONTROL2_100_167  --------------------------- */
#define GPIO_CONTROL2_100_167_SLEW_RATE_Pos   (0UL)                     /*!< GPIO CONTROL2_100_167: SLEW_RATE (Bit 0)                    */
#define GPIO_CONTROL2_100_167_SLEW_RATE_Msk   (0x1UL)                   /*!< GPIO CONTROL2_100_167: SLEW_RATE (Bitfield-Mask: 0x01)      */
#define GPIO_CONTROL2_100_167_DRIVE_STRENGTH_Pos (4UL)                  /*!< GPIO CONTROL2_100_167: DRIVE_STRENGTH (Bit 4)               */
#define GPIO_CONTROL2_100_167_DRIVE_STRENGTH_Msk (0x30UL)               /*!< GPIO CONTROL2_100_167: DRIVE_STRENGTH (Bitfield-Mask: 0x03) */

/* ----------------------------  GPIO_CONTROL2_200_267  --------------------------- */
#define GPIO_CONTROL2_200_267_SLEW_RATE_Pos   (0UL)                     /*!< GPIO CONTROL2_200_267: SLEW_RATE (Bit 0)                    */
#define GPIO_CONTROL2_200_267_SLEW_RATE_Msk   (0x1UL)                   /*!< GPIO CONTROL2_200_267: SLEW_RATE (Bitfield-Mask: 0x01)      */
#define GPIO_CONTROL2_200_267_DRIVE_STRENGTH_Pos (4UL)                  /*!< GPIO CONTROL2_200_267: DRIVE_STRENGTH (Bit 4)               */
#define GPIO_CONTROL2_200_267_DRIVE_STRENGTH_Msk (0x30UL)               /*!< GPIO CONTROL2_200_267: DRIVE_STRENGTH (Bitfield-Mask: 0x03) */


/* ================================================================================ */
/* ================          struct 'DMA' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  DMA_CONTROL  -------------------------------- */
#define DMA_CONTROL_ACTIVATE_Pos              (0UL)                     /*!< DMA CONTROL: ACTIVATE (Bit 0)                               */
#define DMA_CONTROL_ACTIVATE_Msk              (0x1UL)                   /*!< DMA CONTROL: ACTIVATE (Bitfield-Mask: 0x01)                 */
#define DMA_CONTROL_SOFT_RESET_Pos            (1UL)                     /*!< DMA CONTROL: SOFT_RESET (Bit 1)                             */
#define DMA_CONTROL_SOFT_RESET_Msk            (0x2UL)                   /*!< DMA CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)               */


/* ================================================================================ */
/* ================           struct 'CH' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  CH_ACTIVATE  -------------------------------- */
#define CH_ACTIVATE_EN_Pos                    (0UL)                     /*!< CH ACTIVATE: EN (Bit 0)                                     */
#define CH_ACTIVATE_EN_Msk                    (0x1UL)                   /*!< CH ACTIVATE: EN (Bitfield-Mask: 0x01)                       */

/* ---------------------------------  CH_CONTROL  --------------------------------- */
#define CH_CONTROL_RUN_Pos                    (0UL)                     /*!< CH CONTROL: RUN (Bit 0)                                     */
#define CH_CONTROL_RUN_Msk                    (0x1UL)                   /*!< CH CONTROL: RUN (Bitfield-Mask: 0x01)                       */
#define CH_CONTROL_REQUEST_Pos                (1UL)                     /*!< CH CONTROL: REQUEST (Bit 1)                                 */
#define CH_CONTROL_REQUEST_Msk                (0x2UL)                   /*!< CH CONTROL: REQUEST (Bitfield-Mask: 0x01)                   */
#define CH_CONTROL_DONE_Pos                   (2UL)                     /*!< CH CONTROL: DONE (Bit 2)                                    */
#define CH_CONTROL_DONE_Msk                   (0x4UL)                   /*!< CH CONTROL: DONE (Bitfield-Mask: 0x01)                      */
#define CH_CONTROL_STATUS_Pos                 (3UL)                     /*!< CH CONTROL: STATUS (Bit 3)                                  */
#define CH_CONTROL_STATUS_Msk                 (0x18UL)                  /*!< CH CONTROL: STATUS (Bitfield-Mask: 0x03)                    */
#define CH_CONTROL_BUSY_Pos                   (5UL)                     /*!< CH CONTROL: BUSY (Bit 5)                                    */
#define CH_CONTROL_BUSY_Msk                   (0x20UL)                  /*!< CH CONTROL: BUSY (Bitfield-Mask: 0x01)                      */
#define CH_CONTROL_TX_DIRECTION_Pos           (8UL)                     /*!< CH CONTROL: TX_DIRECTION (Bit 8)                            */
#define CH_CONTROL_TX_DIRECTION_Msk           (0x100UL)                 /*!< CH CONTROL: TX_DIRECTION (Bitfield-Mask: 0x01)              */
#define CH_CONTROL_HARDWARE_FLOW_CONTROL_DEVICE_Pos (9UL)               /*!< CH CONTROL: HARDWARE_FLOW_CONTROL_DEVICE (Bit 9)            */
#define CH_CONTROL_HARDWARE_FLOW_CONTROL_DEVICE_Msk (0xfe00UL)          /*!< CH CONTROL: HARDWARE_FLOW_CONTROL_DEVICE (Bitfield-Mask: 0x7f) */
#define CH_CONTROL_INCREMENT_MEM_ADDR_Pos     (16UL)                    /*!< CH CONTROL: INCREMENT_MEM_ADDR (Bit 16)                     */
#define CH_CONTROL_INCREMENT_MEM_ADDR_Msk     (0x10000UL)               /*!< CH CONTROL: INCREMENT_MEM_ADDR (Bitfield-Mask: 0x01)        */
#define CH_CONTROL_INCREMENT_DEVICE_ADDR_Pos  (17UL)                    /*!< CH CONTROL: INCREMENT_DEVICE_ADDR (Bit 17)                  */
#define CH_CONTROL_INCREMENT_DEVICE_ADDR_Msk  (0x20000UL)               /*!< CH CONTROL: INCREMENT_DEVICE_ADDR (Bitfield-Mask: 0x01)     */
#define CH_CONTROL_LOCK_Pos                   (18UL)                    /*!< CH CONTROL: LOCK (Bit 18)                                   */
#define CH_CONTROL_LOCK_Msk                   (0x40000UL)               /*!< CH CONTROL: LOCK (Bitfield-Mask: 0x01)                      */
#define CH_CONTROL_DISABLE_HW_FLOW_CONTROL_Pos (19UL)                   /*!< CH CONTROL: DISABLE_HW_FLOW_CONTROL (Bit 19)                */
#define CH_CONTROL_DISABLE_HW_FLOW_CONTROL_Msk (0x80000UL)              /*!< CH CONTROL: DISABLE_HW_FLOW_CONTROL (Bitfield-Mask: 0x01)   */
#define CH_CONTROL_TRANSFER_SIZE_Pos          (20UL)                    /*!< CH CONTROL: TRANSFER_SIZE (Bit 20)                          */
#define CH_CONTROL_TRANSFER_SIZE_Msk          (0x700000UL)              /*!< CH CONTROL: TRANSFER_SIZE (Bitfield-Mask: 0x07)             */
#define CH_CONTROL_TRANSFER_GO_Pos            (24UL)                    /*!< CH CONTROL: TRANSFER_GO (Bit 24)                            */
#define CH_CONTROL_TRANSFER_GO_Msk            (0x1000000UL)             /*!< CH CONTROL: TRANSFER_GO (Bitfield-Mask: 0x01)               */
#define CH_CONTROL_TRANSFER_ABORT_Pos         (25UL)                    /*!< CH CONTROL: TRANSFER_ABORT (Bit 25)                         */
#define CH_CONTROL_TRANSFER_ABORT_Msk         (0x2000000UL)             /*!< CH CONTROL: TRANSFER_ABORT (Bitfield-Mask: 0x01)            */

/* --------------------------------  CH_INT_STATUS  ------------------------------- */
#define CH_INT_STATUS_BUS_ERROR_Pos           (0UL)                     /*!< CH INT_STATUS: BUS_ERROR (Bit 0)                            */
#define CH_INT_STATUS_BUS_ERROR_Msk           (0x1UL)                   /*!< CH INT_STATUS: BUS_ERROR (Bitfield-Mask: 0x01)              */
#define CH_INT_STATUS_FLOW_CONTROL_Pos        (1UL)                     /*!< CH INT_STATUS: FLOW_CONTROL (Bit 1)                         */
#define CH_INT_STATUS_FLOW_CONTROL_Msk        (0x2UL)                   /*!< CH INT_STATUS: FLOW_CONTROL (Bitfield-Mask: 0x01)           */
#define CH_INT_STATUS_DONE_Pos                (2UL)                     /*!< CH INT_STATUS: DONE (Bit 2)                                 */
#define CH_INT_STATUS_DONE_Msk                (0x4UL)                   /*!< CH INT_STATUS: DONE (Bitfield-Mask: 0x01)                   */

/* ----------------------------------  CH_INT_EN  --------------------------------- */
#define CH_INT_EN_BUS_ERROR_Pos               (0UL)                     /*!< CH INT_EN: BUS_ERROR (Bit 0)                                */
#define CH_INT_EN_BUS_ERROR_Msk               (0x1UL)                   /*!< CH INT_EN: BUS_ERROR (Bitfield-Mask: 0x01)                  */
#define CH_INT_EN_FLOW_CONTROL_Pos            (1UL)                     /*!< CH INT_EN: FLOW_CONTROL (Bit 1)                             */
#define CH_INT_EN_FLOW_CONTROL_Msk            (0x2UL)                   /*!< CH INT_EN: FLOW_CONTROL (Bitfield-Mask: 0x01)               */
#define CH_INT_EN_DONE_Pos                    (2UL)                     /*!< CH INT_EN: DONE (Bit 2)                                     */
#define CH_INT_EN_DONE_Msk                    (0x4UL)                   /*!< CH INT_EN: DONE (Bitfield-Mask: 0x01)                       */


/* ================================================================================ */
/* ================          struct 'SMB0' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  SMB0_CONTROL  -------------------------------- */
#define SMB0_CONTROL_ACK_Pos                  (0UL)                     /*!< SMB0 CONTROL: ACK (Bit 0)                                   */
#define SMB0_CONTROL_ACK_Msk                  (0x1UL)                   /*!< SMB0 CONTROL: ACK (Bitfield-Mask: 0x01)                     */
#define SMB0_CONTROL_STO_Pos                  (1UL)                     /*!< SMB0 CONTROL: STO (Bit 1)                                   */
#define SMB0_CONTROL_STO_Msk                  (0x2UL)                   /*!< SMB0 CONTROL: STO (Bitfield-Mask: 0x01)                     */
#define SMB0_CONTROL_STA_Pos                  (2UL)                     /*!< SMB0 CONTROL: STA (Bit 2)                                   */
#define SMB0_CONTROL_STA_Msk                  (0x4UL)                   /*!< SMB0 CONTROL: STA (Bitfield-Mask: 0x01)                     */
#define SMB0_CONTROL_ENI_Pos                  (3UL)                     /*!< SMB0 CONTROL: ENI (Bit 3)                                   */
#define SMB0_CONTROL_ENI_Msk                  (0x8UL)                   /*!< SMB0 CONTROL: ENI (Bitfield-Mask: 0x01)                     */
#define SMB0_CONTROL_ESO_Pos                  (6UL)                     /*!< SMB0 CONTROL: ESO (Bit 6)                                   */
#define SMB0_CONTROL_ESO_Msk                  (0x40UL)                  /*!< SMB0 CONTROL: ESO (Bitfield-Mask: 0x01)                     */
#define SMB0_CONTROL_PIN_Pos                  (7UL)                     /*!< SMB0 CONTROL: PIN (Bit 7)                                   */
#define SMB0_CONTROL_PIN_Msk                  (0x80UL)                  /*!< SMB0 CONTROL: PIN (Bitfield-Mask: 0x01)                     */

/* ---------------------------------  SMB0_STATUS  -------------------------------- */
#define SMB0_STATUS_nBB_Pos                   (0UL)                     /*!< SMB0 STATUS: nBB (Bit 0)                                    */
#define SMB0_STATUS_nBB_Msk                   (0x1UL)                   /*!< SMB0 STATUS: nBB (Bitfield-Mask: 0x01)                      */
#define SMB0_STATUS_LAB_Pos                   (1UL)                     /*!< SMB0 STATUS: LAB (Bit 1)                                    */
#define SMB0_STATUS_LAB_Msk                   (0x2UL)                   /*!< SMB0 STATUS: LAB (Bitfield-Mask: 0x01)                      */
#define SMB0_STATUS_AAS_Pos                   (2UL)                     /*!< SMB0 STATUS: AAS (Bit 2)                                    */
#define SMB0_STATUS_AAS_Msk                   (0x4UL)                   /*!< SMB0 STATUS: AAS (Bitfield-Mask: 0x01)                      */
#define SMB0_STATUS_LRB_AD0_Pos               (3UL)                     /*!< SMB0 STATUS: LRB_AD0 (Bit 3)                                */
#define SMB0_STATUS_LRB_AD0_Msk               (0x8UL)                   /*!< SMB0 STATUS: LRB_AD0 (Bitfield-Mask: 0x01)                  */
#define SMB0_STATUS_BER_Pos                   (4UL)                     /*!< SMB0 STATUS: BER (Bit 4)                                    */
#define SMB0_STATUS_BER_Msk                   (0x10UL)                  /*!< SMB0 STATUS: BER (Bitfield-Mask: 0x01)                      */
#define SMB0_STATUS_STS_Pos                   (5UL)                     /*!< SMB0 STATUS: STS (Bit 5)                                    */
#define SMB0_STATUS_STS_Msk                   (0x20UL)                  /*!< SMB0 STATUS: STS (Bitfield-Mask: 0x01)                      */
#define SMB0_STATUS_SAD_Pos                   (6UL)                     /*!< SMB0 STATUS: SAD (Bit 6)                                    */
#define SMB0_STATUS_SAD_Msk                   (0x40UL)                  /*!< SMB0 STATUS: SAD (Bitfield-Mask: 0x01)                      */
#define SMB0_STATUS_PIN_Pos                   (7UL)                     /*!< SMB0 STATUS: PIN (Bit 7)                                    */
#define SMB0_STATUS_PIN_Msk                   (0x80UL)                  /*!< SMB0 STATUS: PIN (Bitfield-Mask: 0x01)                      */

/* ----------------------------------  SMB0_OWN  ---------------------------------- */
#define SMB0_OWN_ADDRESS_1_Pos                (0UL)                     /*!< SMB0 OWN: ADDRESS_1 (Bit 0)                                 */
#define SMB0_OWN_ADDRESS_1_Msk                (0x7fUL)                  /*!< SMB0 OWN: ADDRESS_1 (Bitfield-Mask: 0x7f)                   */
#define SMB0_OWN_ADDRESS_2_Pos                (8UL)                     /*!< SMB0 OWN: ADDRESS_2 (Bit 8)                                 */
#define SMB0_OWN_ADDRESS_2_Msk                (0x7f00UL)                /*!< SMB0 OWN: ADDRESS_2 (Bitfield-Mask: 0x7f)                   */

/* -----------------------------  SMB0_MASTER_COMMAND  ---------------------------- */
#define SMB0_MASTER_COMMAND_MRUN_Pos          (0UL)                     /*!< SMB0 MASTER_COMMAND: MRUN (Bit 0)                           */
#define SMB0_MASTER_COMMAND_MRUN_Msk          (0x1UL)                   /*!< SMB0 MASTER_COMMAND: MRUN (Bitfield-Mask: 0x01)             */
#define SMB0_MASTER_COMMAND_MPROCEED_Pos      (1UL)                     /*!< SMB0 MASTER_COMMAND: MPROCEED (Bit 1)                       */
#define SMB0_MASTER_COMMAND_MPROCEED_Msk      (0x2UL)                   /*!< SMB0 MASTER_COMMAND: MPROCEED (Bitfield-Mask: 0x01)         */
#define SMB0_MASTER_COMMAND_START0_Pos        (8UL)                     /*!< SMB0 MASTER_COMMAND: START0 (Bit 8)                         */
#define SMB0_MASTER_COMMAND_START0_Msk        (0x100UL)                 /*!< SMB0 MASTER_COMMAND: START0 (Bitfield-Mask: 0x01)           */
#define SMB0_MASTER_COMMAND_STARTN_Pos        (9UL)                     /*!< SMB0 MASTER_COMMAND: STARTN (Bit 9)                         */
#define SMB0_MASTER_COMMAND_STARTN_Msk        (0x200UL)                 /*!< SMB0 MASTER_COMMAND: STARTN (Bitfield-Mask: 0x01)           */
#define SMB0_MASTER_COMMAND_STOP_Pos          (10UL)                    /*!< SMB0 MASTER_COMMAND: STOP (Bit 10)                          */
#define SMB0_MASTER_COMMAND_STOP_Msk          (0x400UL)                 /*!< SMB0 MASTER_COMMAND: STOP (Bitfield-Mask: 0x01)             */
#define SMB0_MASTER_COMMAND_PEC_TERM_Pos      (11UL)                    /*!< SMB0 MASTER_COMMAND: PEC_TERM (Bit 11)                      */
#define SMB0_MASTER_COMMAND_PEC_TERM_Msk      (0x800UL)                 /*!< SMB0 MASTER_COMMAND: PEC_TERM (Bitfield-Mask: 0x01)         */
#define SMB0_MASTER_COMMAND_READM_Pos         (12UL)                    /*!< SMB0 MASTER_COMMAND: READM (Bit 12)                         */
#define SMB0_MASTER_COMMAND_READM_Msk         (0x1000UL)                /*!< SMB0 MASTER_COMMAND: READM (Bitfield-Mask: 0x01)            */
#define SMB0_MASTER_COMMAND_READ_PEC_Pos      (13UL)                    /*!< SMB0 MASTER_COMMAND: READ_PEC (Bit 13)                      */
#define SMB0_MASTER_COMMAND_READ_PEC_Msk      (0x2000UL)                /*!< SMB0 MASTER_COMMAND: READ_PEC (Bitfield-Mask: 0x01)         */
#define SMB0_MASTER_COMMAND_WRITECOUNT_Pos    (16UL)                    /*!< SMB0 MASTER_COMMAND: WRITECOUNT (Bit 16)                    */
#define SMB0_MASTER_COMMAND_WRITECOUNT_Msk    (0xff0000UL)              /*!< SMB0 MASTER_COMMAND: WRITECOUNT (Bitfield-Mask: 0xff)       */
#define SMB0_MASTER_COMMAND_READCOUNT_Pos     (24UL)                    /*!< SMB0 MASTER_COMMAND: READCOUNT (Bit 24)                     */
#define SMB0_MASTER_COMMAND_READCOUNT_Msk     (0xff000000UL)            /*!< SMB0 MASTER_COMMAND: READCOUNT (Bitfield-Mask: 0xff)        */

/* -----------------------------  SMB0_SLAVE_COMMAND  ----------------------------- */
#define SMB0_SLAVE_COMMAND_SRUN_Pos           (0UL)                     /*!< SMB0 SLAVE_COMMAND: SRUN (Bit 0)                            */
#define SMB0_SLAVE_COMMAND_SRUN_Msk           (0x1UL)                   /*!< SMB0 SLAVE_COMMAND: SRUN (Bitfield-Mask: 0x01)              */
#define SMB0_SLAVE_COMMAND_SPROCEED_Pos       (1UL)                     /*!< SMB0 SLAVE_COMMAND: SPROCEED (Bit 1)                        */
#define SMB0_SLAVE_COMMAND_SPROCEED_Msk       (0x2UL)                   /*!< SMB0 SLAVE_COMMAND: SPROCEED (Bitfield-Mask: 0x01)          */
#define SMB0_SLAVE_COMMAND_SLAVE_PEC_Pos      (2UL)                     /*!< SMB0 SLAVE_COMMAND: SLAVE_PEC (Bit 2)                       */
#define SMB0_SLAVE_COMMAND_SLAVE_PEC_Msk      (0x4UL)                   /*!< SMB0 SLAVE_COMMAND: SLAVE_PEC (Bitfield-Mask: 0x01)         */
#define SMB0_SLAVE_COMMAND_SLAVE_WRITECOUNT_Pos (8UL)                   /*!< SMB0 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bit 8)                */
#define SMB0_SLAVE_COMMAND_SLAVE_WRITECOUNT_Msk (0xff00UL)              /*!< SMB0 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bitfield-Mask: 0xff)  */
#define SMB0_SLAVE_COMMAND_SLAVE_READCOUNT_Pos (16UL)                   /*!< SMB0 SLAVE_COMMAND: SLAVE_READCOUNT (Bit 16)                */
#define SMB0_SLAVE_COMMAND_SLAVE_READCOUNT_Msk (0xff0000UL)             /*!< SMB0 SLAVE_COMMAND: SLAVE_READCOUNT (Bitfield-Mask: 0xff)   */

/* -------------------------------  SMB0_COMPLETION  ------------------------------ */
#define SMB0_COMPLETION_DTEN_Pos              (2UL)                     /*!< SMB0 COMPLETION: DTEN (Bit 2)                               */
#define SMB0_COMPLETION_DTEN_Msk              (0x4UL)                   /*!< SMB0 COMPLETION: DTEN (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_MCEN_Pos              (3UL)                     /*!< SMB0 COMPLETION: MCEN (Bit 3)                               */
#define SMB0_COMPLETION_MCEN_Msk              (0x8UL)                   /*!< SMB0 COMPLETION: MCEN (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_SCEN_Pos              (4UL)                     /*!< SMB0 COMPLETION: SCEN (Bit 4)                               */
#define SMB0_COMPLETION_SCEN_Msk              (0x10UL)                  /*!< SMB0 COMPLETION: SCEN (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_BIDEN_Pos             (5UL)                     /*!< SMB0 COMPLETION: BIDEN (Bit 5)                              */
#define SMB0_COMPLETION_BIDEN_Msk             (0x20UL)                  /*!< SMB0 COMPLETION: BIDEN (Bitfield-Mask: 0x01)                */
#define SMB0_COMPLETION_TIMERR_Pos            (6UL)                     /*!< SMB0 COMPLETION: TIMERR (Bit 6)                             */
#define SMB0_COMPLETION_TIMERR_Msk            (0x40UL)                  /*!< SMB0 COMPLETION: TIMERR (Bitfield-Mask: 0x01)               */
#define SMB0_COMPLETION_DTO_Pos               (8UL)                     /*!< SMB0 COMPLETION: DTO (Bit 8)                                */
#define SMB0_COMPLETION_DTO_Msk               (0x100UL)                 /*!< SMB0 COMPLETION: DTO (Bitfield-Mask: 0x01)                  */
#define SMB0_COMPLETION_MCTO_Pos              (9UL)                     /*!< SMB0 COMPLETION: MCTO (Bit 9)                               */
#define SMB0_COMPLETION_MCTO_Msk              (0x200UL)                 /*!< SMB0 COMPLETION: MCTO (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_SCTO_Pos              (10UL)                    /*!< SMB0 COMPLETION: SCTO (Bit 10)                              */
#define SMB0_COMPLETION_SCTO_Msk              (0x400UL)                 /*!< SMB0 COMPLETION: SCTO (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_CHDL_Pos              (11UL)                    /*!< SMB0 COMPLETION: CHDL (Bit 11)                              */
#define SMB0_COMPLETION_CHDL_Msk              (0x800UL)                 /*!< SMB0 COMPLETION: CHDL (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_CHDH_Pos              (12UL)                    /*!< SMB0 COMPLETION: CHDH (Bit 12)                              */
#define SMB0_COMPLETION_CHDH_Msk              (0x1000UL)                /*!< SMB0 COMPLETION: CHDH (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_BER_Pos               (13UL)                    /*!< SMB0 COMPLETION: BER (Bit 13)                               */
#define SMB0_COMPLETION_BER_Msk               (0x2000UL)                /*!< SMB0 COMPLETION: BER (Bitfield-Mask: 0x01)                  */
#define SMB0_COMPLETION_LAB_Pos               (14UL)                    /*!< SMB0 COMPLETION: LAB (Bit 14)                               */
#define SMB0_COMPLETION_LAB_Msk               (0x4000UL)                /*!< SMB0 COMPLETION: LAB (Bitfield-Mask: 0x01)                  */
#define SMB0_COMPLETION_SNAKR_Pos             (16UL)                    /*!< SMB0 COMPLETION: SNAKR (Bit 16)                             */
#define SMB0_COMPLETION_SNAKR_Msk             (0x10000UL)               /*!< SMB0 COMPLETION: SNAKR (Bitfield-Mask: 0x01)                */
#define SMB0_COMPLETION_STR_Pos               (17UL)                    /*!< SMB0 COMPLETION: STR (Bit 17)                               */
#define SMB0_COMPLETION_STR_Msk               (0x20000UL)               /*!< SMB0 COMPLETION: STR (Bitfield-Mask: 0x01)                  */
#define SMB0_COMPLETION_SPROT_Pos             (19UL)                    /*!< SMB0 COMPLETION: SPROT (Bit 19)                             */
#define SMB0_COMPLETION_SPROT_Msk             (0x80000UL)               /*!< SMB0 COMPLETION: SPROT (Bitfield-Mask: 0x01)                */
#define SMB0_COMPLETION_REPEAT_READ_Pos       (20UL)                    /*!< SMB0 COMPLETION: REPEAT_READ (Bit 20)                       */
#define SMB0_COMPLETION_REPEAT_READ_Msk       (0x100000UL)              /*!< SMB0 COMPLETION: REPEAT_READ (Bitfield-Mask: 0x01)          */
#define SMB0_COMPLETION_REPEAT_WRITE_Pos      (21UL)                    /*!< SMB0 COMPLETION: REPEAT_WRITE (Bit 21)                      */
#define SMB0_COMPLETION_REPEAT_WRITE_Msk      (0x200000UL)              /*!< SMB0 COMPLETION: REPEAT_WRITE (Bitfield-Mask: 0x01)         */
#define SMB0_COMPLETION_MNAKX_Pos             (24UL)                    /*!< SMB0 COMPLETION: MNAKX (Bit 24)                             */
#define SMB0_COMPLETION_MNAKX_Msk             (0x1000000UL)             /*!< SMB0 COMPLETION: MNAKX (Bitfield-Mask: 0x01)                */
#define SMB0_COMPLETION_MTR_Pos               (25UL)                    /*!< SMB0 COMPLETION: MTR (Bit 25)                               */
#define SMB0_COMPLETION_MTR_Msk               (0x2000000UL)             /*!< SMB0 COMPLETION: MTR (Bitfield-Mask: 0x01)                  */
#define SMB0_COMPLETION_IDLE_Pos              (29UL)                    /*!< SMB0 COMPLETION: IDLE (Bit 29)                              */
#define SMB0_COMPLETION_IDLE_Msk              (0x20000000UL)            /*!< SMB0 COMPLETION: IDLE (Bitfield-Mask: 0x01)                 */
#define SMB0_COMPLETION_MDONE_Pos             (30UL)                    /*!< SMB0 COMPLETION: MDONE (Bit 30)                             */
#define SMB0_COMPLETION_MDONE_Msk             (0x40000000UL)            /*!< SMB0 COMPLETION: MDONE (Bitfield-Mask: 0x01)                */
#define SMB0_COMPLETION_SDONE_Pos             (31UL)                    /*!< SMB0 COMPLETION: SDONE (Bit 31)                             */
#define SMB0_COMPLETION_SDONE_Msk             (0x80000000UL)            /*!< SMB0 COMPLETION: SDONE (Bitfield-Mask: 0x01)                */

/* ------------------------------  SMB0_IDLE_SCALING  ----------------------------- */
#define SMB0_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Pos (0UL)                   /*!< SMB0 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bit 0)                */
#define SMB0_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Msk (0xfffUL)               /*!< SMB0 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bitfield-Mask: 0xfff) */
#define SMB0_IDLE_SCALING_FAIR_IDLE_DELAY_Pos (16UL)                    /*!< SMB0 IDLE_SCALING: FAIR_IDLE_DELAY (Bit 16)                 */
#define SMB0_IDLE_SCALING_FAIR_IDLE_DELAY_Msk (0xfff0000UL)             /*!< SMB0 IDLE_SCALING: FAIR_IDLE_DELAY (Bitfield-Mask: 0xfff)   */

/* -----------------------------  SMB0_CONFIGURATION  ----------------------------- */
#define SMB0_CONFIGURATION_PORT_SEL_Pos       (0UL)                     /*!< SMB0 CONFIGURATION: PORT_SEL (Bit 0)                        */
#define SMB0_CONFIGURATION_PORT_SEL_Msk       (0xfUL)                   /*!< SMB0 CONFIGURATION: PORT_SEL (Bitfield-Mask: 0x0f)          */
#define SMB0_CONFIGURATION_TCEN_Pos           (4UL)                     /*!< SMB0 CONFIGURATION: TCEN (Bit 4)                            */
#define SMB0_CONFIGURATION_TCEN_Msk           (0x10UL)                  /*!< SMB0 CONFIGURATION: TCEN (Bitfield-Mask: 0x01)              */
#define SMB0_CONFIGURATION_SLOW_CLOCK_Pos     (5UL)                     /*!< SMB0 CONFIGURATION: SLOW_CLOCK (Bit 5)                      */
#define SMB0_CONFIGURATION_SLOW_CLOCK_Msk     (0x20UL)                  /*!< SMB0 CONFIGURATION: SLOW_CLOCK (Bitfield-Mask: 0x01)        */
#define SMB0_CONFIGURATION_PECEN_Pos          (7UL)                     /*!< SMB0 CONFIGURATION: PECEN (Bit 7)                           */
#define SMB0_CONFIGURATION_PECEN_Msk          (0x80UL)                  /*!< SMB0 CONFIGURATION: PECEN (Bitfield-Mask: 0x01)             */
#define SMB0_CONFIGURATION_DFEN_Pos           (8UL)                     /*!< SMB0 CONFIGURATION: DFEN (Bit 8)                            */
#define SMB0_CONFIGURATION_DFEN_Msk           (0x100UL)                 /*!< SMB0 CONFIGURATION: DFEN (Bitfield-Mask: 0x01)              */
#define SMB0_CONFIGURATION_RESET_Pos          (9UL)                     /*!< SMB0 CONFIGURATION: RESET (Bit 9)                           */
#define SMB0_CONFIGURATION_RESET_Msk          (0x200UL)                 /*!< SMB0 CONFIGURATION: RESET (Bitfield-Mask: 0x01)             */
#define SMB0_CONFIGURATION_ENAB_Pos           (10UL)                    /*!< SMB0 CONFIGURATION: ENAB (Bit 10)                           */
#define SMB0_CONFIGURATION_ENAB_Msk           (0x400UL)                 /*!< SMB0 CONFIGURATION: ENAB (Bitfield-Mask: 0x01)              */
#define SMB0_CONFIGURATION_DSA_Pos            (11UL)                    /*!< SMB0 CONFIGURATION: DSA (Bit 11)                            */
#define SMB0_CONFIGURATION_DSA_Msk            (0x800UL)                 /*!< SMB0 CONFIGURATION: DSA (Bitfield-Mask: 0x01)               */
#define SMB0_CONFIGURATION_FAIR_Pos           (12UL)                    /*!< SMB0 CONFIGURATION: FAIR (Bit 12)                           */
#define SMB0_CONFIGURATION_FAIR_Msk           (0x1000UL)                /*!< SMB0 CONFIGURATION: FAIR (Bitfield-Mask: 0x01)              */
#define SMB0_CONFIGURATION_GC_DIS_Pos         (14UL)                    /*!< SMB0 CONFIGURATION: GC_DIS (Bit 14)                         */
#define SMB0_CONFIGURATION_GC_DIS_Msk         (0x4000UL)                /*!< SMB0 CONFIGURATION: GC_DIS (Bitfield-Mask: 0x01)            */
#define SMB0_CONFIGURATION_FLUSH_SXBUF_Pos    (16UL)                    /*!< SMB0 CONFIGURATION: FLUSH_SXBUF (Bit 16)                    */
#define SMB0_CONFIGURATION_FLUSH_SXBUF_Msk    (0x10000UL)               /*!< SMB0 CONFIGURATION: FLUSH_SXBUF (Bitfield-Mask: 0x01)       */
#define SMB0_CONFIGURATION_FLUSH_SRBUF_Pos    (17UL)                    /*!< SMB0 CONFIGURATION: FLUSH_SRBUF (Bit 17)                    */
#define SMB0_CONFIGURATION_FLUSH_SRBUF_Msk    (0x20000UL)               /*!< SMB0 CONFIGURATION: FLUSH_SRBUF (Bitfield-Mask: 0x01)       */
#define SMB0_CONFIGURATION_FLUSH_MXBUF_Pos    (18UL)                    /*!< SMB0 CONFIGURATION: FLUSH_MXBUF (Bit 18)                    */
#define SMB0_CONFIGURATION_FLUSH_MXBUF_Msk    (0x40000UL)               /*!< SMB0 CONFIGURATION: FLUSH_MXBUF (Bitfield-Mask: 0x01)       */
#define SMB0_CONFIGURATION_FLUSH_MRBUF_Pos    (19UL)                    /*!< SMB0 CONFIGURATION: FLUSH_MRBUF (Bit 19)                    */
#define SMB0_CONFIGURATION_FLUSH_MRBUF_Msk    (0x80000UL)               /*!< SMB0 CONFIGURATION: FLUSH_MRBUF (Bitfield-Mask: 0x01)       */
#define SMB0_CONFIGURATION_EN_AAS_Pos         (28UL)                    /*!< SMB0 CONFIGURATION: EN_AAS (Bit 28)                         */
#define SMB0_CONFIGURATION_EN_AAS_Msk         (0x10000000UL)            /*!< SMB0 CONFIGURATION: EN_AAS (Bitfield-Mask: 0x01)            */
#define SMB0_CONFIGURATION_ENIDI_Pos          (29UL)                    /*!< SMB0 CONFIGURATION: ENIDI (Bit 29)                          */
#define SMB0_CONFIGURATION_ENIDI_Msk          (0x20000000UL)            /*!< SMB0 CONFIGURATION: ENIDI (Bitfield-Mask: 0x01)             */
#define SMB0_CONFIGURATION_ENMI_Pos           (30UL)                    /*!< SMB0 CONFIGURATION: ENMI (Bit 30)                           */
#define SMB0_CONFIGURATION_ENMI_Msk           (0x40000000UL)            /*!< SMB0 CONFIGURATION: ENMI (Bitfield-Mask: 0x01)              */
#define SMB0_CONFIGURATION_ENSI_Pos           (31UL)                    /*!< SMB0 CONFIGURATION: ENSI (Bit 31)                           */
#define SMB0_CONFIGURATION_ENSI_Msk           (0x80000000UL)            /*!< SMB0 CONFIGURATION: ENSI (Bitfield-Mask: 0x01)              */

/* -------------------------------  SMB0_BUS_CLOCK  ------------------------------- */
#define SMB0_BUS_CLOCK_LOW_PERIOD_Pos         (0UL)                     /*!< SMB0 BUS_CLOCK: LOW_PERIOD (Bit 0)                          */
#define SMB0_BUS_CLOCK_LOW_PERIOD_Msk         (0xffUL)                  /*!< SMB0 BUS_CLOCK: LOW_PERIOD (Bitfield-Mask: 0xff)            */
#define SMB0_BUS_CLOCK_HIGH_PERIOD_Pos        (8UL)                     /*!< SMB0 BUS_CLOCK: HIGH_PERIOD (Bit 8)                         */
#define SMB0_BUS_CLOCK_HIGH_PERIOD_Msk        (0xff00UL)                /*!< SMB0 BUS_CLOCK: HIGH_PERIOD (Bitfield-Mask: 0xff)           */

/* ----------------------------  SMB0_BIT_BANG_CONTROL  --------------------------- */
#define SMB0_BIT_BANG_CONTROL_BBEN_Pos        (0UL)                     /*!< SMB0 BIT_BANG_CONTROL: BBEN (Bit 0)                         */
#define SMB0_BIT_BANG_CONTROL_BBEN_Msk        (0x1UL)                   /*!< SMB0 BIT_BANG_CONTROL: BBEN (Bitfield-Mask: 0x01)           */
#define SMB0_BIT_BANG_CONTROL_CLDIR_Pos       (1UL)                     /*!< SMB0 BIT_BANG_CONTROL: CLDIR (Bit 1)                        */
#define SMB0_BIT_BANG_CONTROL_CLDIR_Msk       (0x2UL)                   /*!< SMB0 BIT_BANG_CONTROL: CLDIR (Bitfield-Mask: 0x01)          */
#define SMB0_BIT_BANG_CONTROL_DADIR_Pos       (2UL)                     /*!< SMB0 BIT_BANG_CONTROL: DADIR (Bit 2)                        */
#define SMB0_BIT_BANG_CONTROL_DADIR_Msk       (0x4UL)                   /*!< SMB0 BIT_BANG_CONTROL: DADIR (Bitfield-Mask: 0x01)          */
#define SMB0_BIT_BANG_CONTROL_BBCLK_Pos       (3UL)                     /*!< SMB0 BIT_BANG_CONTROL: BBCLK (Bit 3)                        */
#define SMB0_BIT_BANG_CONTROL_BBCLK_Msk       (0x8UL)                   /*!< SMB0 BIT_BANG_CONTROL: BBCLK (Bitfield-Mask: 0x01)          */
#define SMB0_BIT_BANG_CONTROL_BBDAT_Pos       (4UL)                     /*!< SMB0 BIT_BANG_CONTROL: BBDAT (Bit 4)                        */
#define SMB0_BIT_BANG_CONTROL_BBDAT_Msk       (0x10UL)                  /*!< SMB0 BIT_BANG_CONTROL: BBDAT (Bitfield-Mask: 0x01)          */
#define SMB0_BIT_BANG_CONTROL_BBCLKI_Pos      (5UL)                     /*!< SMB0 BIT_BANG_CONTROL: BBCLKI (Bit 5)                       */
#define SMB0_BIT_BANG_CONTROL_BBCLKI_Msk      (0x20UL)                  /*!< SMB0 BIT_BANG_CONTROL: BBCLKI (Bitfield-Mask: 0x01)         */
#define SMB0_BIT_BANG_CONTROL_BBDATI_Pos      (6UL)                     /*!< SMB0 BIT_BANG_CONTROL: BBDATI (Bit 6)                       */
#define SMB0_BIT_BANG_CONTROL_BBDATI_Msk      (0x40UL)                  /*!< SMB0 BIT_BANG_CONTROL: BBDATI (Bitfield-Mask: 0x01)         */

/* ------------------------------  SMB0_DATA_TIMING  ------------------------------ */
#define SMB0_DATA_TIMING_DATA_HOLD_Pos        (0UL)                     /*!< SMB0 DATA_TIMING: DATA_HOLD (Bit 0)                         */
#define SMB0_DATA_TIMING_DATA_HOLD_Msk        (0xffUL)                  /*!< SMB0 DATA_TIMING: DATA_HOLD (Bitfield-Mask: 0xff)           */
#define SMB0_DATA_TIMING_RESTART_SETUP_Pos    (8UL)                     /*!< SMB0 DATA_TIMING: RESTART_SETUP (Bit 8)                     */
#define SMB0_DATA_TIMING_RESTART_SETUP_Msk    (0xff00UL)                /*!< SMB0 DATA_TIMING: RESTART_SETUP (Bitfield-Mask: 0xff)       */
#define SMB0_DATA_TIMING_STOP_SETUP_Pos       (16UL)                    /*!< SMB0 DATA_TIMING: STOP_SETUP (Bit 16)                       */
#define SMB0_DATA_TIMING_STOP_SETUP_Msk       (0xff0000UL)              /*!< SMB0 DATA_TIMING: STOP_SETUP (Bitfield-Mask: 0xff)          */
#define SMB0_DATA_TIMING_START_HOLD_Pos       (24UL)                    /*!< SMB0 DATA_TIMING: START_HOLD (Bit 24)                       */
#define SMB0_DATA_TIMING_START_HOLD_Msk       (0xff000000UL)            /*!< SMB0 DATA_TIMING: START_HOLD (Bitfield-Mask: 0xff)          */

/* ----------------------------  SMB0_TIME_OUT_SCALING  --------------------------- */
#define SMB0_TIME_OUT_SCALING_CLOCK_HIGH_Pos  (0UL)                     /*!< SMB0 TIME_OUT_SCALING: CLOCK_HIGH (Bit 0)                   */
#define SMB0_TIME_OUT_SCALING_CLOCK_HIGH_Msk  (0xffUL)                  /*!< SMB0 TIME_OUT_SCALING: CLOCK_HIGH (Bitfield-Mask: 0xff)     */
#define SMB0_TIME_OUT_SCALING_SLAVE_CUM_Pos   (8UL)                     /*!< SMB0 TIME_OUT_SCALING: SLAVE_CUM (Bit 8)                    */
#define SMB0_TIME_OUT_SCALING_SLAVE_CUM_Msk   (0xff00UL)                /*!< SMB0 TIME_OUT_SCALING: SLAVE_CUM (Bitfield-Mask: 0xff)      */
#define SMB0_TIME_OUT_SCALING_MASTER_CUM_Pos  (16UL)                    /*!< SMB0 TIME_OUT_SCALING: MASTER_CUM (Bit 16)                  */
#define SMB0_TIME_OUT_SCALING_MASTER_CUM_Msk  (0xff0000UL)              /*!< SMB0 TIME_OUT_SCALING: MASTER_CUM (Bitfield-Mask: 0xff)     */
#define SMB0_TIME_OUT_SCALING_BUS_IDLE_MIN_Pos (24UL)                   /*!< SMB0 TIME_OUT_SCALING: BUS_IDLE_MIN (Bit 24)                */
#define SMB0_TIME_OUT_SCALING_BUS_IDLE_MIN_Msk (0xff000000UL)           /*!< SMB0 TIME_OUT_SCALING: BUS_IDLE_MIN (Bitfield-Mask: 0xff)   */


/* ================================================================================ */
/* ================          struct 'SMB1' Position & Mask         ================ */
/* ================================================================================ */


/* ---------------------------------  SMB1_STATUS  -------------------------------- */
#define SMB1_STATUS_nBB_Pos                   (0UL)                     /*!< SMB1 STATUS: nBB (Bit 0)                                    */
#define SMB1_STATUS_nBB_Msk                   (0x1UL)                   /*!< SMB1 STATUS: nBB (Bitfield-Mask: 0x01)                      */
#define SMB1_STATUS_LAB_Pos                   (1UL)                     /*!< SMB1 STATUS: LAB (Bit 1)                                    */
#define SMB1_STATUS_LAB_Msk                   (0x2UL)                   /*!< SMB1 STATUS: LAB (Bitfield-Mask: 0x01)                      */
#define SMB1_STATUS_AAS_Pos                   (2UL)                     /*!< SMB1 STATUS: AAS (Bit 2)                                    */
#define SMB1_STATUS_AAS_Msk                   (0x4UL)                   /*!< SMB1 STATUS: AAS (Bitfield-Mask: 0x01)                      */
#define SMB1_STATUS_LRB_AD0_Pos               (3UL)                     /*!< SMB1 STATUS: LRB_AD0 (Bit 3)                                */
#define SMB1_STATUS_LRB_AD0_Msk               (0x8UL)                   /*!< SMB1 STATUS: LRB_AD0 (Bitfield-Mask: 0x01)                  */
#define SMB1_STATUS_BER_Pos                   (4UL)                     /*!< SMB1 STATUS: BER (Bit 4)                                    */
#define SMB1_STATUS_BER_Msk                   (0x10UL)                  /*!< SMB1 STATUS: BER (Bitfield-Mask: 0x01)                      */
#define SMB1_STATUS_STS_Pos                   (5UL)                     /*!< SMB1 STATUS: STS (Bit 5)                                    */
#define SMB1_STATUS_STS_Msk                   (0x20UL)                  /*!< SMB1 STATUS: STS (Bitfield-Mask: 0x01)                      */
#define SMB1_STATUS_SAD_Pos                   (6UL)                     /*!< SMB1 STATUS: SAD (Bit 6)                                    */
#define SMB1_STATUS_SAD_Msk                   (0x40UL)                  /*!< SMB1 STATUS: SAD (Bitfield-Mask: 0x01)                      */
#define SMB1_STATUS_PIN_Pos                   (7UL)                     /*!< SMB1 STATUS: PIN (Bit 7)                                    */
#define SMB1_STATUS_PIN_Msk                   (0x80UL)                  /*!< SMB1 STATUS: PIN (Bitfield-Mask: 0x01)                      */

/* --------------------------------  SMB1_CONTROL  -------------------------------- */
#define SMB1_CONTROL_ACK_Pos                  (0UL)                     /*!< SMB1 CONTROL: ACK (Bit 0)                                   */
#define SMB1_CONTROL_ACK_Msk                  (0x1UL)                   /*!< SMB1 CONTROL: ACK (Bitfield-Mask: 0x01)                     */
#define SMB1_CONTROL_STO_Pos                  (1UL)                     /*!< SMB1 CONTROL: STO (Bit 1)                                   */
#define SMB1_CONTROL_STO_Msk                  (0x2UL)                   /*!< SMB1 CONTROL: STO (Bitfield-Mask: 0x01)                     */
#define SMB1_CONTROL_STA_Pos                  (2UL)                     /*!< SMB1 CONTROL: STA (Bit 2)                                   */
#define SMB1_CONTROL_STA_Msk                  (0x4UL)                   /*!< SMB1 CONTROL: STA (Bitfield-Mask: 0x01)                     */
#define SMB1_CONTROL_ENI_Pos                  (3UL)                     /*!< SMB1 CONTROL: ENI (Bit 3)                                   */
#define SMB1_CONTROL_ENI_Msk                  (0x8UL)                   /*!< SMB1 CONTROL: ENI (Bitfield-Mask: 0x01)                     */
#define SMB1_CONTROL_ESO_Pos                  (6UL)                     /*!< SMB1 CONTROL: ESO (Bit 6)                                   */
#define SMB1_CONTROL_ESO_Msk                  (0x40UL)                  /*!< SMB1 CONTROL: ESO (Bitfield-Mask: 0x01)                     */
#define SMB1_CONTROL_PIN_Pos                  (7UL)                     /*!< SMB1 CONTROL: PIN (Bit 7)                                   */
#define SMB1_CONTROL_PIN_Msk                  (0x80UL)                  /*!< SMB1 CONTROL: PIN (Bitfield-Mask: 0x01)                     */

/* ----------------------------------  SMB1_OWN  ---------------------------------- */
#define SMB1_OWN_ADDRESS_1_Pos                (0UL)                     /*!< SMB1 OWN: ADDRESS_1 (Bit 0)                                 */
#define SMB1_OWN_ADDRESS_1_Msk                (0x7fUL)                  /*!< SMB1 OWN: ADDRESS_1 (Bitfield-Mask: 0x7f)                   */
#define SMB1_OWN_ADDRESS_2_Pos                (8UL)                     /*!< SMB1 OWN: ADDRESS_2 (Bit 8)                                 */
#define SMB1_OWN_ADDRESS_2_Msk                (0x7f00UL)                /*!< SMB1 OWN: ADDRESS_2 (Bitfield-Mask: 0x7f)                   */

/* -----------------------------  SMB1_MASTER_COMMAND  ---------------------------- */
#define SMB1_MASTER_COMMAND_MRUN_Pos          (0UL)                     /*!< SMB1 MASTER_COMMAND: MRUN (Bit 0)                           */
#define SMB1_MASTER_COMMAND_MRUN_Msk          (0x1UL)                   /*!< SMB1 MASTER_COMMAND: MRUN (Bitfield-Mask: 0x01)             */
#define SMB1_MASTER_COMMAND_MPROCEED_Pos      (1UL)                     /*!< SMB1 MASTER_COMMAND: MPROCEED (Bit 1)                       */
#define SMB1_MASTER_COMMAND_MPROCEED_Msk      (0x2UL)                   /*!< SMB1 MASTER_COMMAND: MPROCEED (Bitfield-Mask: 0x01)         */
#define SMB1_MASTER_COMMAND_START0_Pos        (8UL)                     /*!< SMB1 MASTER_COMMAND: START0 (Bit 8)                         */
#define SMB1_MASTER_COMMAND_START0_Msk        (0x100UL)                 /*!< SMB1 MASTER_COMMAND: START0 (Bitfield-Mask: 0x01)           */
#define SMB1_MASTER_COMMAND_STARTN_Pos        (9UL)                     /*!< SMB1 MASTER_COMMAND: STARTN (Bit 9)                         */
#define SMB1_MASTER_COMMAND_STARTN_Msk        (0x200UL)                 /*!< SMB1 MASTER_COMMAND: STARTN (Bitfield-Mask: 0x01)           */
#define SMB1_MASTER_COMMAND_STOP_Pos          (10UL)                    /*!< SMB1 MASTER_COMMAND: STOP (Bit 10)                          */
#define SMB1_MASTER_COMMAND_STOP_Msk          (0x400UL)                 /*!< SMB1 MASTER_COMMAND: STOP (Bitfield-Mask: 0x01)             */
#define SMB1_MASTER_COMMAND_PEC_TERM_Pos      (11UL)                    /*!< SMB1 MASTER_COMMAND: PEC_TERM (Bit 11)                      */
#define SMB1_MASTER_COMMAND_PEC_TERM_Msk      (0x800UL)                 /*!< SMB1 MASTER_COMMAND: PEC_TERM (Bitfield-Mask: 0x01)         */
#define SMB1_MASTER_COMMAND_READM_Pos         (12UL)                    /*!< SMB1 MASTER_COMMAND: READM (Bit 12)                         */
#define SMB1_MASTER_COMMAND_READM_Msk         (0x1000UL)                /*!< SMB1 MASTER_COMMAND: READM (Bitfield-Mask: 0x01)            */
#define SMB1_MASTER_COMMAND_READ_PEC_Pos      (13UL)                    /*!< SMB1 MASTER_COMMAND: READ_PEC (Bit 13)                      */
#define SMB1_MASTER_COMMAND_READ_PEC_Msk      (0x2000UL)                /*!< SMB1 MASTER_COMMAND: READ_PEC (Bitfield-Mask: 0x01)         */
#define SMB1_MASTER_COMMAND_WRITECOUNT_Pos    (16UL)                    /*!< SMB1 MASTER_COMMAND: WRITECOUNT (Bit 16)                    */
#define SMB1_MASTER_COMMAND_WRITECOUNT_Msk    (0xff0000UL)              /*!< SMB1 MASTER_COMMAND: WRITECOUNT (Bitfield-Mask: 0xff)       */
#define SMB1_MASTER_COMMAND_READCOUNT_Pos     (24UL)                    /*!< SMB1 MASTER_COMMAND: READCOUNT (Bit 24)                     */
#define SMB1_MASTER_COMMAND_READCOUNT_Msk     (0xff000000UL)            /*!< SMB1 MASTER_COMMAND: READCOUNT (Bitfield-Mask: 0xff)        */

/* -----------------------------  SMB1_SLAVE_COMMAND  ----------------------------- */
#define SMB1_SLAVE_COMMAND_SRUN_Pos           (0UL)                     /*!< SMB1 SLAVE_COMMAND: SRUN (Bit 0)                            */
#define SMB1_SLAVE_COMMAND_SRUN_Msk           (0x1UL)                   /*!< SMB1 SLAVE_COMMAND: SRUN (Bitfield-Mask: 0x01)              */
#define SMB1_SLAVE_COMMAND_SPROCEED_Pos       (1UL)                     /*!< SMB1 SLAVE_COMMAND: SPROCEED (Bit 1)                        */
#define SMB1_SLAVE_COMMAND_SPROCEED_Msk       (0x2UL)                   /*!< SMB1 SLAVE_COMMAND: SPROCEED (Bitfield-Mask: 0x01)          */
#define SMB1_SLAVE_COMMAND_SLAVE_PEC_Pos      (2UL)                     /*!< SMB1 SLAVE_COMMAND: SLAVE_PEC (Bit 2)                       */
#define SMB1_SLAVE_COMMAND_SLAVE_PEC_Msk      (0x4UL)                   /*!< SMB1 SLAVE_COMMAND: SLAVE_PEC (Bitfield-Mask: 0x01)         */
#define SMB1_SLAVE_COMMAND_SLAVE_WRITECOUNT_Pos (8UL)                   /*!< SMB1 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bit 8)                */
#define SMB1_SLAVE_COMMAND_SLAVE_WRITECOUNT_Msk (0xff00UL)              /*!< SMB1 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bitfield-Mask: 0xff)  */
#define SMB1_SLAVE_COMMAND_SLAVE_READCOUNT_Pos (16UL)                   /*!< SMB1 SLAVE_COMMAND: SLAVE_READCOUNT (Bit 16)                */
#define SMB1_SLAVE_COMMAND_SLAVE_READCOUNT_Msk (0xff0000UL)             /*!< SMB1 SLAVE_COMMAND: SLAVE_READCOUNT (Bitfield-Mask: 0xff)   */

/* -------------------------------  SMB1_COMPLETION  ------------------------------ */
#define SMB1_COMPLETION_DTEN_Pos              (2UL)                     /*!< SMB1 COMPLETION: DTEN (Bit 2)                               */
#define SMB1_COMPLETION_DTEN_Msk              (0x4UL)                   /*!< SMB1 COMPLETION: DTEN (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_MCEN_Pos              (3UL)                     /*!< SMB1 COMPLETION: MCEN (Bit 3)                               */
#define SMB1_COMPLETION_MCEN_Msk              (0x8UL)                   /*!< SMB1 COMPLETION: MCEN (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_SCEN_Pos              (4UL)                     /*!< SMB1 COMPLETION: SCEN (Bit 4)                               */
#define SMB1_COMPLETION_SCEN_Msk              (0x10UL)                  /*!< SMB1 COMPLETION: SCEN (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_BIDEN_Pos             (5UL)                     /*!< SMB1 COMPLETION: BIDEN (Bit 5)                              */
#define SMB1_COMPLETION_BIDEN_Msk             (0x20UL)                  /*!< SMB1 COMPLETION: BIDEN (Bitfield-Mask: 0x01)                */
#define SMB1_COMPLETION_TIMERR_Pos            (6UL)                     /*!< SMB1 COMPLETION: TIMERR (Bit 6)                             */
#define SMB1_COMPLETION_TIMERR_Msk            (0x40UL)                  /*!< SMB1 COMPLETION: TIMERR (Bitfield-Mask: 0x01)               */
#define SMB1_COMPLETION_DTO_Pos               (8UL)                     /*!< SMB1 COMPLETION: DTO (Bit 8)                                */
#define SMB1_COMPLETION_DTO_Msk               (0x100UL)                 /*!< SMB1 COMPLETION: DTO (Bitfield-Mask: 0x01)                  */
#define SMB1_COMPLETION_MCTO_Pos              (9UL)                     /*!< SMB1 COMPLETION: MCTO (Bit 9)                               */
#define SMB1_COMPLETION_MCTO_Msk              (0x200UL)                 /*!< SMB1 COMPLETION: MCTO (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_SCTO_Pos              (10UL)                    /*!< SMB1 COMPLETION: SCTO (Bit 10)                              */
#define SMB1_COMPLETION_SCTO_Msk              (0x400UL)                 /*!< SMB1 COMPLETION: SCTO (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_CHDL_Pos              (11UL)                    /*!< SMB1 COMPLETION: CHDL (Bit 11)                              */
#define SMB1_COMPLETION_CHDL_Msk              (0x800UL)                 /*!< SMB1 COMPLETION: CHDL (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_CHDH_Pos              (12UL)                    /*!< SMB1 COMPLETION: CHDH (Bit 12)                              */
#define SMB1_COMPLETION_CHDH_Msk              (0x1000UL)                /*!< SMB1 COMPLETION: CHDH (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_BER_Pos               (13UL)                    /*!< SMB1 COMPLETION: BER (Bit 13)                               */
#define SMB1_COMPLETION_BER_Msk               (0x2000UL)                /*!< SMB1 COMPLETION: BER (Bitfield-Mask: 0x01)                  */
#define SMB1_COMPLETION_LAB_Pos               (14UL)                    /*!< SMB1 COMPLETION: LAB (Bit 14)                               */
#define SMB1_COMPLETION_LAB_Msk               (0x4000UL)                /*!< SMB1 COMPLETION: LAB (Bitfield-Mask: 0x01)                  */
#define SMB1_COMPLETION_SNAKR_Pos             (16UL)                    /*!< SMB1 COMPLETION: SNAKR (Bit 16)                             */
#define SMB1_COMPLETION_SNAKR_Msk             (0x10000UL)               /*!< SMB1 COMPLETION: SNAKR (Bitfield-Mask: 0x01)                */
#define SMB1_COMPLETION_STR_Pos               (17UL)                    /*!< SMB1 COMPLETION: STR (Bit 17)                               */
#define SMB1_COMPLETION_STR_Msk               (0x20000UL)               /*!< SMB1 COMPLETION: STR (Bitfield-Mask: 0x01)                  */
#define SMB1_COMPLETION_SPROT_Pos             (19UL)                    /*!< SMB1 COMPLETION: SPROT (Bit 19)                             */
#define SMB1_COMPLETION_SPROT_Msk             (0x80000UL)               /*!< SMB1 COMPLETION: SPROT (Bitfield-Mask: 0x01)                */
#define SMB1_COMPLETION_REPEAT_READ_Pos       (20UL)                    /*!< SMB1 COMPLETION: REPEAT_READ (Bit 20)                       */
#define SMB1_COMPLETION_REPEAT_READ_Msk       (0x100000UL)              /*!< SMB1 COMPLETION: REPEAT_READ (Bitfield-Mask: 0x01)          */
#define SMB1_COMPLETION_REPEAT_WRITE_Pos      (21UL)                    /*!< SMB1 COMPLETION: REPEAT_WRITE (Bit 21)                      */
#define SMB1_COMPLETION_REPEAT_WRITE_Msk      (0x200000UL)              /*!< SMB1 COMPLETION: REPEAT_WRITE (Bitfield-Mask: 0x01)         */
#define SMB1_COMPLETION_MNAKX_Pos             (24UL)                    /*!< SMB1 COMPLETION: MNAKX (Bit 24)                             */
#define SMB1_COMPLETION_MNAKX_Msk             (0x1000000UL)             /*!< SMB1 COMPLETION: MNAKX (Bitfield-Mask: 0x01)                */
#define SMB1_COMPLETION_MTR_Pos               (25UL)                    /*!< SMB1 COMPLETION: MTR (Bit 25)                               */
#define SMB1_COMPLETION_MTR_Msk               (0x2000000UL)             /*!< SMB1 COMPLETION: MTR (Bitfield-Mask: 0x01)                  */
#define SMB1_COMPLETION_IDLE_Pos              (29UL)                    /*!< SMB1 COMPLETION: IDLE (Bit 29)                              */
#define SMB1_COMPLETION_IDLE_Msk              (0x20000000UL)            /*!< SMB1 COMPLETION: IDLE (Bitfield-Mask: 0x01)                 */
#define SMB1_COMPLETION_MDONE_Pos             (30UL)                    /*!< SMB1 COMPLETION: MDONE (Bit 30)                             */
#define SMB1_COMPLETION_MDONE_Msk             (0x40000000UL)            /*!< SMB1 COMPLETION: MDONE (Bitfield-Mask: 0x01)                */
#define SMB1_COMPLETION_SDONE_Pos             (31UL)                    /*!< SMB1 COMPLETION: SDONE (Bit 31)                             */
#define SMB1_COMPLETION_SDONE_Msk             (0x80000000UL)            /*!< SMB1 COMPLETION: SDONE (Bitfield-Mask: 0x01)                */

/* ------------------------------  SMB1_IDLE_SCALING  ----------------------------- */
#define SMB1_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Pos (0UL)                   /*!< SMB1 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bit 0)                */
#define SMB1_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Msk (0xfffUL)               /*!< SMB1 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bitfield-Mask: 0xfff) */
#define SMB1_IDLE_SCALING_FAIR_IDLE_DELAY_Pos (16UL)                    /*!< SMB1 IDLE_SCALING: FAIR_IDLE_DELAY (Bit 16)                 */
#define SMB1_IDLE_SCALING_FAIR_IDLE_DELAY_Msk (0xfff0000UL)             /*!< SMB1 IDLE_SCALING: FAIR_IDLE_DELAY (Bitfield-Mask: 0xfff)   */

/* -----------------------------  SMB1_CONFIGURATION  ----------------------------- */
#define SMB1_CONFIGURATION_PORT_SEL_Pos       (0UL)                     /*!< SMB1 CONFIGURATION: PORT_SEL (Bit 0)                        */
#define SMB1_CONFIGURATION_PORT_SEL_Msk       (0xfUL)                   /*!< SMB1 CONFIGURATION: PORT_SEL (Bitfield-Mask: 0x0f)          */
#define SMB1_CONFIGURATION_TCEN_Pos           (4UL)                     /*!< SMB1 CONFIGURATION: TCEN (Bit 4)                            */
#define SMB1_CONFIGURATION_TCEN_Msk           (0x10UL)                  /*!< SMB1 CONFIGURATION: TCEN (Bitfield-Mask: 0x01)              */
#define SMB1_CONFIGURATION_SLOW_CLOCK_Pos     (5UL)                     /*!< SMB1 CONFIGURATION: SLOW_CLOCK (Bit 5)                      */
#define SMB1_CONFIGURATION_SLOW_CLOCK_Msk     (0x20UL)                  /*!< SMB1 CONFIGURATION: SLOW_CLOCK (Bitfield-Mask: 0x01)        */
#define SMB1_CONFIGURATION_PECEN_Pos          (7UL)                     /*!< SMB1 CONFIGURATION: PECEN (Bit 7)                           */
#define SMB1_CONFIGURATION_PECEN_Msk          (0x80UL)                  /*!< SMB1 CONFIGURATION: PECEN (Bitfield-Mask: 0x01)             */
#define SMB1_CONFIGURATION_DFEN_Pos           (8UL)                     /*!< SMB1 CONFIGURATION: DFEN (Bit 8)                            */
#define SMB1_CONFIGURATION_DFEN_Msk           (0x100UL)                 /*!< SMB1 CONFIGURATION: DFEN (Bitfield-Mask: 0x01)              */
#define SMB1_CONFIGURATION_RESET_Pos          (9UL)                     /*!< SMB1 CONFIGURATION: RESET (Bit 9)                           */
#define SMB1_CONFIGURATION_RESET_Msk          (0x200UL)                 /*!< SMB1 CONFIGURATION: RESET (Bitfield-Mask: 0x01)             */
#define SMB1_CONFIGURATION_ENAB_Pos           (10UL)                    /*!< SMB1 CONFIGURATION: ENAB (Bit 10)                           */
#define SMB1_CONFIGURATION_ENAB_Msk           (0x400UL)                 /*!< SMB1 CONFIGURATION: ENAB (Bitfield-Mask: 0x01)              */
#define SMB1_CONFIGURATION_DSA_Pos            (11UL)                    /*!< SMB1 CONFIGURATION: DSA (Bit 11)                            */
#define SMB1_CONFIGURATION_DSA_Msk            (0x800UL)                 /*!< SMB1 CONFIGURATION: DSA (Bitfield-Mask: 0x01)               */
#define SMB1_CONFIGURATION_FAIR_Pos           (12UL)                    /*!< SMB1 CONFIGURATION: FAIR (Bit 12)                           */
#define SMB1_CONFIGURATION_FAIR_Msk           (0x1000UL)                /*!< SMB1 CONFIGURATION: FAIR (Bitfield-Mask: 0x01)              */
#define SMB1_CONFIGURATION_GC_DIS_Pos         (14UL)                    /*!< SMB1 CONFIGURATION: GC_DIS (Bit 14)                         */
#define SMB1_CONFIGURATION_GC_DIS_Msk         (0x4000UL)                /*!< SMB1 CONFIGURATION: GC_DIS (Bitfield-Mask: 0x01)            */
#define SMB1_CONFIGURATION_FLUSH_SXBUF_Pos    (16UL)                    /*!< SMB1 CONFIGURATION: FLUSH_SXBUF (Bit 16)                    */
#define SMB1_CONFIGURATION_FLUSH_SXBUF_Msk    (0x10000UL)               /*!< SMB1 CONFIGURATION: FLUSH_SXBUF (Bitfield-Mask: 0x01)       */
#define SMB1_CONFIGURATION_FLUSH_SRBUF_Pos    (17UL)                    /*!< SMB1 CONFIGURATION: FLUSH_SRBUF (Bit 17)                    */
#define SMB1_CONFIGURATION_FLUSH_SRBUF_Msk    (0x20000UL)               /*!< SMB1 CONFIGURATION: FLUSH_SRBUF (Bitfield-Mask: 0x01)       */
#define SMB1_CONFIGURATION_FLUSH_MXBUF_Pos    (18UL)                    /*!< SMB1 CONFIGURATION: FLUSH_MXBUF (Bit 18)                    */
#define SMB1_CONFIGURATION_FLUSH_MXBUF_Msk    (0x40000UL)               /*!< SMB1 CONFIGURATION: FLUSH_MXBUF (Bitfield-Mask: 0x01)       */
#define SMB1_CONFIGURATION_FLUSH_MRBUF_Pos    (19UL)                    /*!< SMB1 CONFIGURATION: FLUSH_MRBUF (Bit 19)                    */
#define SMB1_CONFIGURATION_FLUSH_MRBUF_Msk    (0x80000UL)               /*!< SMB1 CONFIGURATION: FLUSH_MRBUF (Bitfield-Mask: 0x01)       */
#define SMB1_CONFIGURATION_EN_AAS_Pos         (28UL)                    /*!< SMB1 CONFIGURATION: EN_AAS (Bit 28)                         */
#define SMB1_CONFIGURATION_EN_AAS_Msk         (0x10000000UL)            /*!< SMB1 CONFIGURATION: EN_AAS (Bitfield-Mask: 0x01)            */
#define SMB1_CONFIGURATION_ENIDI_Pos          (29UL)                    /*!< SMB1 CONFIGURATION: ENIDI (Bit 29)                          */
#define SMB1_CONFIGURATION_ENIDI_Msk          (0x20000000UL)            /*!< SMB1 CONFIGURATION: ENIDI (Bitfield-Mask: 0x01)             */
#define SMB1_CONFIGURATION_ENMI_Pos           (30UL)                    /*!< SMB1 CONFIGURATION: ENMI (Bit 30)                           */
#define SMB1_CONFIGURATION_ENMI_Msk           (0x40000000UL)            /*!< SMB1 CONFIGURATION: ENMI (Bitfield-Mask: 0x01)              */
#define SMB1_CONFIGURATION_ENSI_Pos           (31UL)                    /*!< SMB1 CONFIGURATION: ENSI (Bit 31)                           */
#define SMB1_CONFIGURATION_ENSI_Msk           (0x80000000UL)            /*!< SMB1 CONFIGURATION: ENSI (Bitfield-Mask: 0x01)              */

/* -------------------------------  SMB1_BUS_CLOCK  ------------------------------- */
#define SMB1_BUS_CLOCK_LOW_PERIOD_Pos         (0UL)                     /*!< SMB1 BUS_CLOCK: LOW_PERIOD (Bit 0)                          */
#define SMB1_BUS_CLOCK_LOW_PERIOD_Msk         (0xffUL)                  /*!< SMB1 BUS_CLOCK: LOW_PERIOD (Bitfield-Mask: 0xff)            */
#define SMB1_BUS_CLOCK_HIGH_PERIOD_Pos        (8UL)                     /*!< SMB1 BUS_CLOCK: HIGH_PERIOD (Bit 8)                         */
#define SMB1_BUS_CLOCK_HIGH_PERIOD_Msk        (0xff00UL)                /*!< SMB1 BUS_CLOCK: HIGH_PERIOD (Bitfield-Mask: 0xff)           */

/* ----------------------------  SMB1_BIT_BANG_CONTROL  --------------------------- */
#define SMB1_BIT_BANG_CONTROL_BBEN_Pos        (0UL)                     /*!< SMB1 BIT_BANG_CONTROL: BBEN (Bit 0)                         */
#define SMB1_BIT_BANG_CONTROL_BBEN_Msk        (0x1UL)                   /*!< SMB1 BIT_BANG_CONTROL: BBEN (Bitfield-Mask: 0x01)           */
#define SMB1_BIT_BANG_CONTROL_CLDIR_Pos       (1UL)                     /*!< SMB1 BIT_BANG_CONTROL: CLDIR (Bit 1)                        */
#define SMB1_BIT_BANG_CONTROL_CLDIR_Msk       (0x2UL)                   /*!< SMB1 BIT_BANG_CONTROL: CLDIR (Bitfield-Mask: 0x01)          */
#define SMB1_BIT_BANG_CONTROL_DADIR_Pos       (2UL)                     /*!< SMB1 BIT_BANG_CONTROL: DADIR (Bit 2)                        */
#define SMB1_BIT_BANG_CONTROL_DADIR_Msk       (0x4UL)                   /*!< SMB1 BIT_BANG_CONTROL: DADIR (Bitfield-Mask: 0x01)          */
#define SMB1_BIT_BANG_CONTROL_BBCLK_Pos       (3UL)                     /*!< SMB1 BIT_BANG_CONTROL: BBCLK (Bit 3)                        */
#define SMB1_BIT_BANG_CONTROL_BBCLK_Msk       (0x8UL)                   /*!< SMB1 BIT_BANG_CONTROL: BBCLK (Bitfield-Mask: 0x01)          */
#define SMB1_BIT_BANG_CONTROL_BBDAT_Pos       (4UL)                     /*!< SMB1 BIT_BANG_CONTROL: BBDAT (Bit 4)                        */
#define SMB1_BIT_BANG_CONTROL_BBDAT_Msk       (0x10UL)                  /*!< SMB1 BIT_BANG_CONTROL: BBDAT (Bitfield-Mask: 0x01)          */
#define SMB1_BIT_BANG_CONTROL_BBCLKI_Pos      (5UL)                     /*!< SMB1 BIT_BANG_CONTROL: BBCLKI (Bit 5)                       */
#define SMB1_BIT_BANG_CONTROL_BBCLKI_Msk      (0x20UL)                  /*!< SMB1 BIT_BANG_CONTROL: BBCLKI (Bitfield-Mask: 0x01)         */
#define SMB1_BIT_BANG_CONTROL_BBDATI_Pos      (6UL)                     /*!< SMB1 BIT_BANG_CONTROL: BBDATI (Bit 6)                       */
#define SMB1_BIT_BANG_CONTROL_BBDATI_Msk      (0x40UL)                  /*!< SMB1 BIT_BANG_CONTROL: BBDATI (Bitfield-Mask: 0x01)         */

/* ------------------------------  SMB1_DATA_TIMING  ------------------------------ */
#define SMB1_DATA_TIMING_DATA_HOLD_Pos        (0UL)                     /*!< SMB1 DATA_TIMING: DATA_HOLD (Bit 0)                         */
#define SMB1_DATA_TIMING_DATA_HOLD_Msk        (0xffUL)                  /*!< SMB1 DATA_TIMING: DATA_HOLD (Bitfield-Mask: 0xff)           */
#define SMB1_DATA_TIMING_RESTART_SETUP_Pos    (8UL)                     /*!< SMB1 DATA_TIMING: RESTART_SETUP (Bit 8)                     */
#define SMB1_DATA_TIMING_RESTART_SETUP_Msk    (0xff00UL)                /*!< SMB1 DATA_TIMING: RESTART_SETUP (Bitfield-Mask: 0xff)       */
#define SMB1_DATA_TIMING_STOP_SETUP_Pos       (16UL)                    /*!< SMB1 DATA_TIMING: STOP_SETUP (Bit 16)                       */
#define SMB1_DATA_TIMING_STOP_SETUP_Msk       (0xff0000UL)              /*!< SMB1 DATA_TIMING: STOP_SETUP (Bitfield-Mask: 0xff)          */
#define SMB1_DATA_TIMING_START_HOLD_Pos       (24UL)                    /*!< SMB1 DATA_TIMING: START_HOLD (Bit 24)                       */
#define SMB1_DATA_TIMING_START_HOLD_Msk       (0xff000000UL)            /*!< SMB1 DATA_TIMING: START_HOLD (Bitfield-Mask: 0xff)          */

/* ----------------------------  SMB1_TIME_OUT_SCALING  --------------------------- */
#define SMB1_TIME_OUT_SCALING_CLOCK_HIGH_Pos  (0UL)                     /*!< SMB1 TIME_OUT_SCALING: CLOCK_HIGH (Bit 0)                   */
#define SMB1_TIME_OUT_SCALING_CLOCK_HIGH_Msk  (0xffUL)                  /*!< SMB1 TIME_OUT_SCALING: CLOCK_HIGH (Bitfield-Mask: 0xff)     */
#define SMB1_TIME_OUT_SCALING_SLAVE_CUM_Pos   (8UL)                     /*!< SMB1 TIME_OUT_SCALING: SLAVE_CUM (Bit 8)                    */
#define SMB1_TIME_OUT_SCALING_SLAVE_CUM_Msk   (0xff00UL)                /*!< SMB1 TIME_OUT_SCALING: SLAVE_CUM (Bitfield-Mask: 0xff)      */
#define SMB1_TIME_OUT_SCALING_MASTER_CUM_Pos  (16UL)                    /*!< SMB1 TIME_OUT_SCALING: MASTER_CUM (Bit 16)                  */
#define SMB1_TIME_OUT_SCALING_MASTER_CUM_Msk  (0xff0000UL)              /*!< SMB1 TIME_OUT_SCALING: MASTER_CUM (Bitfield-Mask: 0xff)     */
#define SMB1_TIME_OUT_SCALING_BUS_IDLE_MIN_Pos (24UL)                   /*!< SMB1 TIME_OUT_SCALING: BUS_IDLE_MIN (Bit 24)                */
#define SMB1_TIME_OUT_SCALING_BUS_IDLE_MIN_Msk (0xff000000UL)           /*!< SMB1 TIME_OUT_SCALING: BUS_IDLE_MIN (Bitfield-Mask: 0xff)   */


/* ================================================================================ */
/* ================          struct 'SMB2' Position & Mask         ================ */
/* ================================================================================ */


/* ---------------------------------  SMB2_STATUS  -------------------------------- */
#define SMB2_STATUS_nBB_Pos                   (0UL)                     /*!< SMB2 STATUS: nBB (Bit 0)                                    */
#define SMB2_STATUS_nBB_Msk                   (0x1UL)                   /*!< SMB2 STATUS: nBB (Bitfield-Mask: 0x01)                      */
#define SMB2_STATUS_LAB_Pos                   (1UL)                     /*!< SMB2 STATUS: LAB (Bit 1)                                    */
#define SMB2_STATUS_LAB_Msk                   (0x2UL)                   /*!< SMB2 STATUS: LAB (Bitfield-Mask: 0x01)                      */
#define SMB2_STATUS_AAS_Pos                   (2UL)                     /*!< SMB2 STATUS: AAS (Bit 2)                                    */
#define SMB2_STATUS_AAS_Msk                   (0x4UL)                   /*!< SMB2 STATUS: AAS (Bitfield-Mask: 0x01)                      */
#define SMB2_STATUS_LRB_AD0_Pos               (3UL)                     /*!< SMB2 STATUS: LRB_AD0 (Bit 3)                                */
#define SMB2_STATUS_LRB_AD0_Msk               (0x8UL)                   /*!< SMB2 STATUS: LRB_AD0 (Bitfield-Mask: 0x01)                  */
#define SMB2_STATUS_BER_Pos                   (4UL)                     /*!< SMB2 STATUS: BER (Bit 4)                                    */
#define SMB2_STATUS_BER_Msk                   (0x10UL)                  /*!< SMB2 STATUS: BER (Bitfield-Mask: 0x01)                      */
#define SMB2_STATUS_STS_Pos                   (5UL)                     /*!< SMB2 STATUS: STS (Bit 5)                                    */
#define SMB2_STATUS_STS_Msk                   (0x20UL)                  /*!< SMB2 STATUS: STS (Bitfield-Mask: 0x01)                      */
#define SMB2_STATUS_SAD_Pos                   (6UL)                     /*!< SMB2 STATUS: SAD (Bit 6)                                    */
#define SMB2_STATUS_SAD_Msk                   (0x40UL)                  /*!< SMB2 STATUS: SAD (Bitfield-Mask: 0x01)                      */
#define SMB2_STATUS_PIN_Pos                   (7UL)                     /*!< SMB2 STATUS: PIN (Bit 7)                                    */
#define SMB2_STATUS_PIN_Msk                   (0x80UL)                  /*!< SMB2 STATUS: PIN (Bitfield-Mask: 0x01)                      */

/* --------------------------------  SMB2_CONTROL  -------------------------------- */
#define SMB2_CONTROL_ACK_Pos                  (0UL)                     /*!< SMB2 CONTROL: ACK (Bit 0)                                   */
#define SMB2_CONTROL_ACK_Msk                  (0x1UL)                   /*!< SMB2 CONTROL: ACK (Bitfield-Mask: 0x01)                     */
#define SMB2_CONTROL_STO_Pos                  (1UL)                     /*!< SMB2 CONTROL: STO (Bit 1)                                   */
#define SMB2_CONTROL_STO_Msk                  (0x2UL)                   /*!< SMB2 CONTROL: STO (Bitfield-Mask: 0x01)                     */
#define SMB2_CONTROL_STA_Pos                  (2UL)                     /*!< SMB2 CONTROL: STA (Bit 2)                                   */
#define SMB2_CONTROL_STA_Msk                  (0x4UL)                   /*!< SMB2 CONTROL: STA (Bitfield-Mask: 0x01)                     */
#define SMB2_CONTROL_ENI_Pos                  (3UL)                     /*!< SMB2 CONTROL: ENI (Bit 3)                                   */
#define SMB2_CONTROL_ENI_Msk                  (0x8UL)                   /*!< SMB2 CONTROL: ENI (Bitfield-Mask: 0x01)                     */
#define SMB2_CONTROL_ESO_Pos                  (6UL)                     /*!< SMB2 CONTROL: ESO (Bit 6)                                   */
#define SMB2_CONTROL_ESO_Msk                  (0x40UL)                  /*!< SMB2 CONTROL: ESO (Bitfield-Mask: 0x01)                     */
#define SMB2_CONTROL_PIN_Pos                  (7UL)                     /*!< SMB2 CONTROL: PIN (Bit 7)                                   */
#define SMB2_CONTROL_PIN_Msk                  (0x80UL)                  /*!< SMB2 CONTROL: PIN (Bitfield-Mask: 0x01)                     */

/* ----------------------------------  SMB2_OWN  ---------------------------------- */
#define SMB2_OWN_ADDRESS_1_Pos                (0UL)                     /*!< SMB2 OWN: ADDRESS_1 (Bit 0)                                 */
#define SMB2_OWN_ADDRESS_1_Msk                (0x7fUL)                  /*!< SMB2 OWN: ADDRESS_1 (Bitfield-Mask: 0x7f)                   */
#define SMB2_OWN_ADDRESS_2_Pos                (8UL)                     /*!< SMB2 OWN: ADDRESS_2 (Bit 8)                                 */
#define SMB2_OWN_ADDRESS_2_Msk                (0x7f00UL)                /*!< SMB2 OWN: ADDRESS_2 (Bitfield-Mask: 0x7f)                   */

/* -----------------------------  SMB2_MASTER_COMMAND  ---------------------------- */
#define SMB2_MASTER_COMMAND_MRUN_Pos          (0UL)                     /*!< SMB2 MASTER_COMMAND: MRUN (Bit 0)                           */
#define SMB2_MASTER_COMMAND_MRUN_Msk          (0x1UL)                   /*!< SMB2 MASTER_COMMAND: MRUN (Bitfield-Mask: 0x01)             */
#define SMB2_MASTER_COMMAND_MPROCEED_Pos      (1UL)                     /*!< SMB2 MASTER_COMMAND: MPROCEED (Bit 1)                       */
#define SMB2_MASTER_COMMAND_MPROCEED_Msk      (0x2UL)                   /*!< SMB2 MASTER_COMMAND: MPROCEED (Bitfield-Mask: 0x01)         */
#define SMB2_MASTER_COMMAND_START0_Pos        (8UL)                     /*!< SMB2 MASTER_COMMAND: START0 (Bit 8)                         */
#define SMB2_MASTER_COMMAND_START0_Msk        (0x100UL)                 /*!< SMB2 MASTER_COMMAND: START0 (Bitfield-Mask: 0x01)           */
#define SMB2_MASTER_COMMAND_STARTN_Pos        (9UL)                     /*!< SMB2 MASTER_COMMAND: STARTN (Bit 9)                         */
#define SMB2_MASTER_COMMAND_STARTN_Msk        (0x200UL)                 /*!< SMB2 MASTER_COMMAND: STARTN (Bitfield-Mask: 0x01)           */
#define SMB2_MASTER_COMMAND_STOP_Pos          (10UL)                    /*!< SMB2 MASTER_COMMAND: STOP (Bit 10)                          */
#define SMB2_MASTER_COMMAND_STOP_Msk          (0x400UL)                 /*!< SMB2 MASTER_COMMAND: STOP (Bitfield-Mask: 0x01)             */
#define SMB2_MASTER_COMMAND_PEC_TERM_Pos      (11UL)                    /*!< SMB2 MASTER_COMMAND: PEC_TERM (Bit 11)                      */
#define SMB2_MASTER_COMMAND_PEC_TERM_Msk      (0x800UL)                 /*!< SMB2 MASTER_COMMAND: PEC_TERM (Bitfield-Mask: 0x01)         */
#define SMB2_MASTER_COMMAND_READM_Pos         (12UL)                    /*!< SMB2 MASTER_COMMAND: READM (Bit 12)                         */
#define SMB2_MASTER_COMMAND_READM_Msk         (0x1000UL)                /*!< SMB2 MASTER_COMMAND: READM (Bitfield-Mask: 0x01)            */
#define SMB2_MASTER_COMMAND_READ_PEC_Pos      (13UL)                    /*!< SMB2 MASTER_COMMAND: READ_PEC (Bit 13)                      */
#define SMB2_MASTER_COMMAND_READ_PEC_Msk      (0x2000UL)                /*!< SMB2 MASTER_COMMAND: READ_PEC (Bitfield-Mask: 0x01)         */
#define SMB2_MASTER_COMMAND_WRITECOUNT_Pos    (16UL)                    /*!< SMB2 MASTER_COMMAND: WRITECOUNT (Bit 16)                    */
#define SMB2_MASTER_COMMAND_WRITECOUNT_Msk    (0xff0000UL)              /*!< SMB2 MASTER_COMMAND: WRITECOUNT (Bitfield-Mask: 0xff)       */
#define SMB2_MASTER_COMMAND_READCOUNT_Pos     (24UL)                    /*!< SMB2 MASTER_COMMAND: READCOUNT (Bit 24)                     */
#define SMB2_MASTER_COMMAND_READCOUNT_Msk     (0xff000000UL)            /*!< SMB2 MASTER_COMMAND: READCOUNT (Bitfield-Mask: 0xff)        */

/* -----------------------------  SMB2_SLAVE_COMMAND  ----------------------------- */
#define SMB2_SLAVE_COMMAND_SRUN_Pos           (0UL)                     /*!< SMB2 SLAVE_COMMAND: SRUN (Bit 0)                            */
#define SMB2_SLAVE_COMMAND_SRUN_Msk           (0x1UL)                   /*!< SMB2 SLAVE_COMMAND: SRUN (Bitfield-Mask: 0x01)              */
#define SMB2_SLAVE_COMMAND_SPROCEED_Pos       (1UL)                     /*!< SMB2 SLAVE_COMMAND: SPROCEED (Bit 1)                        */
#define SMB2_SLAVE_COMMAND_SPROCEED_Msk       (0x2UL)                   /*!< SMB2 SLAVE_COMMAND: SPROCEED (Bitfield-Mask: 0x01)          */
#define SMB2_SLAVE_COMMAND_SLAVE_PEC_Pos      (2UL)                     /*!< SMB2 SLAVE_COMMAND: SLAVE_PEC (Bit 2)                       */
#define SMB2_SLAVE_COMMAND_SLAVE_PEC_Msk      (0x4UL)                   /*!< SMB2 SLAVE_COMMAND: SLAVE_PEC (Bitfield-Mask: 0x01)         */
#define SMB2_SLAVE_COMMAND_SLAVE_WRITECOUNT_Pos (8UL)                   /*!< SMB2 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bit 8)                */
#define SMB2_SLAVE_COMMAND_SLAVE_WRITECOUNT_Msk (0xff00UL)              /*!< SMB2 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bitfield-Mask: 0xff)  */
#define SMB2_SLAVE_COMMAND_SLAVE_READCOUNT_Pos (16UL)                   /*!< SMB2 SLAVE_COMMAND: SLAVE_READCOUNT (Bit 16)                */
#define SMB2_SLAVE_COMMAND_SLAVE_READCOUNT_Msk (0xff0000UL)             /*!< SMB2 SLAVE_COMMAND: SLAVE_READCOUNT (Bitfield-Mask: 0xff)   */

/* -------------------------------  SMB2_COMPLETION  ------------------------------ */
#define SMB2_COMPLETION_DTEN_Pos              (2UL)                     /*!< SMB2 COMPLETION: DTEN (Bit 2)                               */
#define SMB2_COMPLETION_DTEN_Msk              (0x4UL)                   /*!< SMB2 COMPLETION: DTEN (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_MCEN_Pos              (3UL)                     /*!< SMB2 COMPLETION: MCEN (Bit 3)                               */
#define SMB2_COMPLETION_MCEN_Msk              (0x8UL)                   /*!< SMB2 COMPLETION: MCEN (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_SCEN_Pos              (4UL)                     /*!< SMB2 COMPLETION: SCEN (Bit 4)                               */
#define SMB2_COMPLETION_SCEN_Msk              (0x10UL)                  /*!< SMB2 COMPLETION: SCEN (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_BIDEN_Pos             (5UL)                     /*!< SMB2 COMPLETION: BIDEN (Bit 5)                              */
#define SMB2_COMPLETION_BIDEN_Msk             (0x20UL)                  /*!< SMB2 COMPLETION: BIDEN (Bitfield-Mask: 0x01)                */
#define SMB2_COMPLETION_TIMERR_Pos            (6UL)                     /*!< SMB2 COMPLETION: TIMERR (Bit 6)                             */
#define SMB2_COMPLETION_TIMERR_Msk            (0x40UL)                  /*!< SMB2 COMPLETION: TIMERR (Bitfield-Mask: 0x01)               */
#define SMB2_COMPLETION_DTO_Pos               (8UL)                     /*!< SMB2 COMPLETION: DTO (Bit 8)                                */
#define SMB2_COMPLETION_DTO_Msk               (0x100UL)                 /*!< SMB2 COMPLETION: DTO (Bitfield-Mask: 0x01)                  */
#define SMB2_COMPLETION_MCTO_Pos              (9UL)                     /*!< SMB2 COMPLETION: MCTO (Bit 9)                               */
#define SMB2_COMPLETION_MCTO_Msk              (0x200UL)                 /*!< SMB2 COMPLETION: MCTO (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_SCTO_Pos              (10UL)                    /*!< SMB2 COMPLETION: SCTO (Bit 10)                              */
#define SMB2_COMPLETION_SCTO_Msk              (0x400UL)                 /*!< SMB2 COMPLETION: SCTO (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_CHDL_Pos              (11UL)                    /*!< SMB2 COMPLETION: CHDL (Bit 11)                              */
#define SMB2_COMPLETION_CHDL_Msk              (0x800UL)                 /*!< SMB2 COMPLETION: CHDL (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_CHDH_Pos              (12UL)                    /*!< SMB2 COMPLETION: CHDH (Bit 12)                              */
#define SMB2_COMPLETION_CHDH_Msk              (0x1000UL)                /*!< SMB2 COMPLETION: CHDH (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_BER_Pos               (13UL)                    /*!< SMB2 COMPLETION: BER (Bit 13)                               */
#define SMB2_COMPLETION_BER_Msk               (0x2000UL)                /*!< SMB2 COMPLETION: BER (Bitfield-Mask: 0x01)                  */
#define SMB2_COMPLETION_LAB_Pos               (14UL)                    /*!< SMB2 COMPLETION: LAB (Bit 14)                               */
#define SMB2_COMPLETION_LAB_Msk               (0x4000UL)                /*!< SMB2 COMPLETION: LAB (Bitfield-Mask: 0x01)                  */
#define SMB2_COMPLETION_SNAKR_Pos             (16UL)                    /*!< SMB2 COMPLETION: SNAKR (Bit 16)                             */
#define SMB2_COMPLETION_SNAKR_Msk             (0x10000UL)               /*!< SMB2 COMPLETION: SNAKR (Bitfield-Mask: 0x01)                */
#define SMB2_COMPLETION_STR_Pos               (17UL)                    /*!< SMB2 COMPLETION: STR (Bit 17)                               */
#define SMB2_COMPLETION_STR_Msk               (0x20000UL)               /*!< SMB2 COMPLETION: STR (Bitfield-Mask: 0x01)                  */
#define SMB2_COMPLETION_SPROT_Pos             (19UL)                    /*!< SMB2 COMPLETION: SPROT (Bit 19)                             */
#define SMB2_COMPLETION_SPROT_Msk             (0x80000UL)               /*!< SMB2 COMPLETION: SPROT (Bitfield-Mask: 0x01)                */
#define SMB2_COMPLETION_REPEAT_READ_Pos       (20UL)                    /*!< SMB2 COMPLETION: REPEAT_READ (Bit 20)                       */
#define SMB2_COMPLETION_REPEAT_READ_Msk       (0x100000UL)              /*!< SMB2 COMPLETION: REPEAT_READ (Bitfield-Mask: 0x01)          */
#define SMB2_COMPLETION_REPEAT_WRITE_Pos      (21UL)                    /*!< SMB2 COMPLETION: REPEAT_WRITE (Bit 21)                      */
#define SMB2_COMPLETION_REPEAT_WRITE_Msk      (0x200000UL)              /*!< SMB2 COMPLETION: REPEAT_WRITE (Bitfield-Mask: 0x01)         */
#define SMB2_COMPLETION_MNAKX_Pos             (24UL)                    /*!< SMB2 COMPLETION: MNAKX (Bit 24)                             */
#define SMB2_COMPLETION_MNAKX_Msk             (0x1000000UL)             /*!< SMB2 COMPLETION: MNAKX (Bitfield-Mask: 0x01)                */
#define SMB2_COMPLETION_MTR_Pos               (25UL)                    /*!< SMB2 COMPLETION: MTR (Bit 25)                               */
#define SMB2_COMPLETION_MTR_Msk               (0x2000000UL)             /*!< SMB2 COMPLETION: MTR (Bitfield-Mask: 0x01)                  */
#define SMB2_COMPLETION_IDLE_Pos              (29UL)                    /*!< SMB2 COMPLETION: IDLE (Bit 29)                              */
#define SMB2_COMPLETION_IDLE_Msk              (0x20000000UL)            /*!< SMB2 COMPLETION: IDLE (Bitfield-Mask: 0x01)                 */
#define SMB2_COMPLETION_MDONE_Pos             (30UL)                    /*!< SMB2 COMPLETION: MDONE (Bit 30)                             */
#define SMB2_COMPLETION_MDONE_Msk             (0x40000000UL)            /*!< SMB2 COMPLETION: MDONE (Bitfield-Mask: 0x01)                */
#define SMB2_COMPLETION_SDONE_Pos             (31UL)                    /*!< SMB2 COMPLETION: SDONE (Bit 31)                             */
#define SMB2_COMPLETION_SDONE_Msk             (0x80000000UL)            /*!< SMB2 COMPLETION: SDONE (Bitfield-Mask: 0x01)                */

/* ------------------------------  SMB2_IDLE_SCALING  ----------------------------- */
#define SMB2_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Pos (0UL)                   /*!< SMB2 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bit 0)                */
#define SMB2_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Msk (0xfffUL)               /*!< SMB2 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bitfield-Mask: 0xfff) */
#define SMB2_IDLE_SCALING_FAIR_IDLE_DELAY_Pos (16UL)                    /*!< SMB2 IDLE_SCALING: FAIR_IDLE_DELAY (Bit 16)                 */
#define SMB2_IDLE_SCALING_FAIR_IDLE_DELAY_Msk (0xfff0000UL)             /*!< SMB2 IDLE_SCALING: FAIR_IDLE_DELAY (Bitfield-Mask: 0xfff)   */

/* -----------------------------  SMB2_CONFIGURATION  ----------------------------- */
#define SMB2_CONFIGURATION_PORT_SEL_Pos       (0UL)                     /*!< SMB2 CONFIGURATION: PORT_SEL (Bit 0)                        */
#define SMB2_CONFIGURATION_PORT_SEL_Msk       (0xfUL)                   /*!< SMB2 CONFIGURATION: PORT_SEL (Bitfield-Mask: 0x0f)          */
#define SMB2_CONFIGURATION_TCEN_Pos           (4UL)                     /*!< SMB2 CONFIGURATION: TCEN (Bit 4)                            */
#define SMB2_CONFIGURATION_TCEN_Msk           (0x10UL)                  /*!< SMB2 CONFIGURATION: TCEN (Bitfield-Mask: 0x01)              */
#define SMB2_CONFIGURATION_SLOW_CLOCK_Pos     (5UL)                     /*!< SMB2 CONFIGURATION: SLOW_CLOCK (Bit 5)                      */
#define SMB2_CONFIGURATION_SLOW_CLOCK_Msk     (0x20UL)                  /*!< SMB2 CONFIGURATION: SLOW_CLOCK (Bitfield-Mask: 0x01)        */
#define SMB2_CONFIGURATION_PECEN_Pos          (7UL)                     /*!< SMB2 CONFIGURATION: PECEN (Bit 7)                           */
#define SMB2_CONFIGURATION_PECEN_Msk          (0x80UL)                  /*!< SMB2 CONFIGURATION: PECEN (Bitfield-Mask: 0x01)             */
#define SMB2_CONFIGURATION_DFEN_Pos           (8UL)                     /*!< SMB2 CONFIGURATION: DFEN (Bit 8)                            */
#define SMB2_CONFIGURATION_DFEN_Msk           (0x100UL)                 /*!< SMB2 CONFIGURATION: DFEN (Bitfield-Mask: 0x01)              */
#define SMB2_CONFIGURATION_RESET_Pos          (9UL)                     /*!< SMB2 CONFIGURATION: RESET (Bit 9)                           */
#define SMB2_CONFIGURATION_RESET_Msk          (0x200UL)                 /*!< SMB2 CONFIGURATION: RESET (Bitfield-Mask: 0x01)             */
#define SMB2_CONFIGURATION_ENAB_Pos           (10UL)                    /*!< SMB2 CONFIGURATION: ENAB (Bit 10)                           */
#define SMB2_CONFIGURATION_ENAB_Msk           (0x400UL)                 /*!< SMB2 CONFIGURATION: ENAB (Bitfield-Mask: 0x01)              */
#define SMB2_CONFIGURATION_DSA_Pos            (11UL)                    /*!< SMB2 CONFIGURATION: DSA (Bit 11)                            */
#define SMB2_CONFIGURATION_DSA_Msk            (0x800UL)                 /*!< SMB2 CONFIGURATION: DSA (Bitfield-Mask: 0x01)               */
#define SMB2_CONFIGURATION_FAIR_Pos           (12UL)                    /*!< SMB2 CONFIGURATION: FAIR (Bit 12)                           */
#define SMB2_CONFIGURATION_FAIR_Msk           (0x1000UL)                /*!< SMB2 CONFIGURATION: FAIR (Bitfield-Mask: 0x01)              */
#define SMB2_CONFIGURATION_GC_DIS_Pos         (14UL)                    /*!< SMB2 CONFIGURATION: GC_DIS (Bit 14)                         */
#define SMB2_CONFIGURATION_GC_DIS_Msk         (0x4000UL)                /*!< SMB2 CONFIGURATION: GC_DIS (Bitfield-Mask: 0x01)            */
#define SMB2_CONFIGURATION_FLUSH_SXBUF_Pos    (16UL)                    /*!< SMB2 CONFIGURATION: FLUSH_SXBUF (Bit 16)                    */
#define SMB2_CONFIGURATION_FLUSH_SXBUF_Msk    (0x10000UL)               /*!< SMB2 CONFIGURATION: FLUSH_SXBUF (Bitfield-Mask: 0x01)       */
#define SMB2_CONFIGURATION_FLUSH_SRBUF_Pos    (17UL)                    /*!< SMB2 CONFIGURATION: FLUSH_SRBUF (Bit 17)                    */
#define SMB2_CONFIGURATION_FLUSH_SRBUF_Msk    (0x20000UL)               /*!< SMB2 CONFIGURATION: FLUSH_SRBUF (Bitfield-Mask: 0x01)       */
#define SMB2_CONFIGURATION_FLUSH_MXBUF_Pos    (18UL)                    /*!< SMB2 CONFIGURATION: FLUSH_MXBUF (Bit 18)                    */
#define SMB2_CONFIGURATION_FLUSH_MXBUF_Msk    (0x40000UL)               /*!< SMB2 CONFIGURATION: FLUSH_MXBUF (Bitfield-Mask: 0x01)       */
#define SMB2_CONFIGURATION_FLUSH_MRBUF_Pos    (19UL)                    /*!< SMB2 CONFIGURATION: FLUSH_MRBUF (Bit 19)                    */
#define SMB2_CONFIGURATION_FLUSH_MRBUF_Msk    (0x80000UL)               /*!< SMB2 CONFIGURATION: FLUSH_MRBUF (Bitfield-Mask: 0x01)       */
#define SMB2_CONFIGURATION_EN_AAS_Pos         (28UL)                    /*!< SMB2 CONFIGURATION: EN_AAS (Bit 28)                         */
#define SMB2_CONFIGURATION_EN_AAS_Msk         (0x10000000UL)            /*!< SMB2 CONFIGURATION: EN_AAS (Bitfield-Mask: 0x01)            */
#define SMB2_CONFIGURATION_ENIDI_Pos          (29UL)                    /*!< SMB2 CONFIGURATION: ENIDI (Bit 29)                          */
#define SMB2_CONFIGURATION_ENIDI_Msk          (0x20000000UL)            /*!< SMB2 CONFIGURATION: ENIDI (Bitfield-Mask: 0x01)             */
#define SMB2_CONFIGURATION_ENMI_Pos           (30UL)                    /*!< SMB2 CONFIGURATION: ENMI (Bit 30)                           */
#define SMB2_CONFIGURATION_ENMI_Msk           (0x40000000UL)            /*!< SMB2 CONFIGURATION: ENMI (Bitfield-Mask: 0x01)              */
#define SMB2_CONFIGURATION_ENSI_Pos           (31UL)                    /*!< SMB2 CONFIGURATION: ENSI (Bit 31)                           */
#define SMB2_CONFIGURATION_ENSI_Msk           (0x80000000UL)            /*!< SMB2 CONFIGURATION: ENSI (Bitfield-Mask: 0x01)              */

/* -------------------------------  SMB2_BUS_CLOCK  ------------------------------- */
#define SMB2_BUS_CLOCK_LOW_PERIOD_Pos         (0UL)                     /*!< SMB2 BUS_CLOCK: LOW_PERIOD (Bit 0)                          */
#define SMB2_BUS_CLOCK_LOW_PERIOD_Msk         (0xffUL)                  /*!< SMB2 BUS_CLOCK: LOW_PERIOD (Bitfield-Mask: 0xff)            */
#define SMB2_BUS_CLOCK_HIGH_PERIOD_Pos        (8UL)                     /*!< SMB2 BUS_CLOCK: HIGH_PERIOD (Bit 8)                         */
#define SMB2_BUS_CLOCK_HIGH_PERIOD_Msk        (0xff00UL)                /*!< SMB2 BUS_CLOCK: HIGH_PERIOD (Bitfield-Mask: 0xff)           */

/* ----------------------------  SMB2_BIT_BANG_CONTROL  --------------------------- */
#define SMB2_BIT_BANG_CONTROL_BBEN_Pos        (0UL)                     /*!< SMB2 BIT_BANG_CONTROL: BBEN (Bit 0)                         */
#define SMB2_BIT_BANG_CONTROL_BBEN_Msk        (0x1UL)                   /*!< SMB2 BIT_BANG_CONTROL: BBEN (Bitfield-Mask: 0x01)           */
#define SMB2_BIT_BANG_CONTROL_CLDIR_Pos       (1UL)                     /*!< SMB2 BIT_BANG_CONTROL: CLDIR (Bit 1)                        */
#define SMB2_BIT_BANG_CONTROL_CLDIR_Msk       (0x2UL)                   /*!< SMB2 BIT_BANG_CONTROL: CLDIR (Bitfield-Mask: 0x01)          */
#define SMB2_BIT_BANG_CONTROL_DADIR_Pos       (2UL)                     /*!< SMB2 BIT_BANG_CONTROL: DADIR (Bit 2)                        */
#define SMB2_BIT_BANG_CONTROL_DADIR_Msk       (0x4UL)                   /*!< SMB2 BIT_BANG_CONTROL: DADIR (Bitfield-Mask: 0x01)          */
#define SMB2_BIT_BANG_CONTROL_BBCLK_Pos       (3UL)                     /*!< SMB2 BIT_BANG_CONTROL: BBCLK (Bit 3)                        */
#define SMB2_BIT_BANG_CONTROL_BBCLK_Msk       (0x8UL)                   /*!< SMB2 BIT_BANG_CONTROL: BBCLK (Bitfield-Mask: 0x01)          */
#define SMB2_BIT_BANG_CONTROL_BBDAT_Pos       (4UL)                     /*!< SMB2 BIT_BANG_CONTROL: BBDAT (Bit 4)                        */
#define SMB2_BIT_BANG_CONTROL_BBDAT_Msk       (0x10UL)                  /*!< SMB2 BIT_BANG_CONTROL: BBDAT (Bitfield-Mask: 0x01)          */
#define SMB2_BIT_BANG_CONTROL_BBCLKI_Pos      (5UL)                     /*!< SMB2 BIT_BANG_CONTROL: BBCLKI (Bit 5)                       */
#define SMB2_BIT_BANG_CONTROL_BBCLKI_Msk      (0x20UL)                  /*!< SMB2 BIT_BANG_CONTROL: BBCLKI (Bitfield-Mask: 0x01)         */
#define SMB2_BIT_BANG_CONTROL_BBDATI_Pos      (6UL)                     /*!< SMB2 BIT_BANG_CONTROL: BBDATI (Bit 6)                       */
#define SMB2_BIT_BANG_CONTROL_BBDATI_Msk      (0x40UL)                  /*!< SMB2 BIT_BANG_CONTROL: BBDATI (Bitfield-Mask: 0x01)         */

/* ------------------------------  SMB2_DATA_TIMING  ------------------------------ */
#define SMB2_DATA_TIMING_DATA_HOLD_Pos        (0UL)                     /*!< SMB2 DATA_TIMING: DATA_HOLD (Bit 0)                         */
#define SMB2_DATA_TIMING_DATA_HOLD_Msk        (0xffUL)                  /*!< SMB2 DATA_TIMING: DATA_HOLD (Bitfield-Mask: 0xff)           */
#define SMB2_DATA_TIMING_RESTART_SETUP_Pos    (8UL)                     /*!< SMB2 DATA_TIMING: RESTART_SETUP (Bit 8)                     */
#define SMB2_DATA_TIMING_RESTART_SETUP_Msk    (0xff00UL)                /*!< SMB2 DATA_TIMING: RESTART_SETUP (Bitfield-Mask: 0xff)       */
#define SMB2_DATA_TIMING_STOP_SETUP_Pos       (16UL)                    /*!< SMB2 DATA_TIMING: STOP_SETUP (Bit 16)                       */
#define SMB2_DATA_TIMING_STOP_SETUP_Msk       (0xff0000UL)              /*!< SMB2 DATA_TIMING: STOP_SETUP (Bitfield-Mask: 0xff)          */
#define SMB2_DATA_TIMING_START_HOLD_Pos       (24UL)                    /*!< SMB2 DATA_TIMING: START_HOLD (Bit 24)                       */
#define SMB2_DATA_TIMING_START_HOLD_Msk       (0xff000000UL)            /*!< SMB2 DATA_TIMING: START_HOLD (Bitfield-Mask: 0xff)          */

/* ----------------------------  SMB2_TIME_OUT_SCALING  --------------------------- */
#define SMB2_TIME_OUT_SCALING_CLOCK_HIGH_Pos  (0UL)                     /*!< SMB2 TIME_OUT_SCALING: CLOCK_HIGH (Bit 0)                   */
#define SMB2_TIME_OUT_SCALING_CLOCK_HIGH_Msk  (0xffUL)                  /*!< SMB2 TIME_OUT_SCALING: CLOCK_HIGH (Bitfield-Mask: 0xff)     */
#define SMB2_TIME_OUT_SCALING_SLAVE_CUM_Pos   (8UL)                     /*!< SMB2 TIME_OUT_SCALING: SLAVE_CUM (Bit 8)                    */
#define SMB2_TIME_OUT_SCALING_SLAVE_CUM_Msk   (0xff00UL)                /*!< SMB2 TIME_OUT_SCALING: SLAVE_CUM (Bitfield-Mask: 0xff)      */
#define SMB2_TIME_OUT_SCALING_MASTER_CUM_Pos  (16UL)                    /*!< SMB2 TIME_OUT_SCALING: MASTER_CUM (Bit 16)                  */
#define SMB2_TIME_OUT_SCALING_MASTER_CUM_Msk  (0xff0000UL)              /*!< SMB2 TIME_OUT_SCALING: MASTER_CUM (Bitfield-Mask: 0xff)     */
#define SMB2_TIME_OUT_SCALING_BUS_IDLE_MIN_Pos (24UL)                   /*!< SMB2 TIME_OUT_SCALING: BUS_IDLE_MIN (Bit 24)                */
#define SMB2_TIME_OUT_SCALING_BUS_IDLE_MIN_Msk (0xff000000UL)           /*!< SMB2 TIME_OUT_SCALING: BUS_IDLE_MIN (Bitfield-Mask: 0xff)   */


/* ================================================================================ */
/* ================          struct 'SMB3' Position & Mask         ================ */
/* ================================================================================ */


/* ---------------------------------  SMB3_STATUS  -------------------------------- */
#define SMB3_STATUS_nBB_Pos                   (0UL)                     /*!< SMB3 STATUS: nBB (Bit 0)                                    */
#define SMB3_STATUS_nBB_Msk                   (0x1UL)                   /*!< SMB3 STATUS: nBB (Bitfield-Mask: 0x01)                      */
#define SMB3_STATUS_LAB_Pos                   (1UL)                     /*!< SMB3 STATUS: LAB (Bit 1)                                    */
#define SMB3_STATUS_LAB_Msk                   (0x2UL)                   /*!< SMB3 STATUS: LAB (Bitfield-Mask: 0x01)                      */
#define SMB3_STATUS_AAS_Pos                   (2UL)                     /*!< SMB3 STATUS: AAS (Bit 2)                                    */
#define SMB3_STATUS_AAS_Msk                   (0x4UL)                   /*!< SMB3 STATUS: AAS (Bitfield-Mask: 0x01)                      */
#define SMB3_STATUS_LRB_AD0_Pos               (3UL)                     /*!< SMB3 STATUS: LRB_AD0 (Bit 3)                                */
#define SMB3_STATUS_LRB_AD0_Msk               (0x8UL)                   /*!< SMB3 STATUS: LRB_AD0 (Bitfield-Mask: 0x01)                  */
#define SMB3_STATUS_BER_Pos                   (4UL)                     /*!< SMB3 STATUS: BER (Bit 4)                                    */
#define SMB3_STATUS_BER_Msk                   (0x10UL)                  /*!< SMB3 STATUS: BER (Bitfield-Mask: 0x01)                      */
#define SMB3_STATUS_STS_Pos                   (5UL)                     /*!< SMB3 STATUS: STS (Bit 5)                                    */
#define SMB3_STATUS_STS_Msk                   (0x20UL)                  /*!< SMB3 STATUS: STS (Bitfield-Mask: 0x01)                      */
#define SMB3_STATUS_SAD_Pos                   (6UL)                     /*!< SMB3 STATUS: SAD (Bit 6)                                    */
#define SMB3_STATUS_SAD_Msk                   (0x40UL)                  /*!< SMB3 STATUS: SAD (Bitfield-Mask: 0x01)                      */
#define SMB3_STATUS_PIN_Pos                   (7UL)                     /*!< SMB3 STATUS: PIN (Bit 7)                                    */
#define SMB3_STATUS_PIN_Msk                   (0x80UL)                  /*!< SMB3 STATUS: PIN (Bitfield-Mask: 0x01)                      */

/* --------------------------------  SMB3_CONTROL  -------------------------------- */
#define SMB3_CONTROL_ACK_Pos                  (0UL)                     /*!< SMB3 CONTROL: ACK (Bit 0)                                   */
#define SMB3_CONTROL_ACK_Msk                  (0x1UL)                   /*!< SMB3 CONTROL: ACK (Bitfield-Mask: 0x01)                     */
#define SMB3_CONTROL_STO_Pos                  (1UL)                     /*!< SMB3 CONTROL: STO (Bit 1)                                   */
#define SMB3_CONTROL_STO_Msk                  (0x2UL)                   /*!< SMB3 CONTROL: STO (Bitfield-Mask: 0x01)                     */
#define SMB3_CONTROL_STA_Pos                  (2UL)                     /*!< SMB3 CONTROL: STA (Bit 2)                                   */
#define SMB3_CONTROL_STA_Msk                  (0x4UL)                   /*!< SMB3 CONTROL: STA (Bitfield-Mask: 0x01)                     */
#define SMB3_CONTROL_ENI_Pos                  (3UL)                     /*!< SMB3 CONTROL: ENI (Bit 3)                                   */
#define SMB3_CONTROL_ENI_Msk                  (0x8UL)                   /*!< SMB3 CONTROL: ENI (Bitfield-Mask: 0x01)                     */
#define SMB3_CONTROL_ESO_Pos                  (6UL)                     /*!< SMB3 CONTROL: ESO (Bit 6)                                   */
#define SMB3_CONTROL_ESO_Msk                  (0x40UL)                  /*!< SMB3 CONTROL: ESO (Bitfield-Mask: 0x01)                     */
#define SMB3_CONTROL_PIN_Pos                  (7UL)                     /*!< SMB3 CONTROL: PIN (Bit 7)                                   */
#define SMB3_CONTROL_PIN_Msk                  (0x80UL)                  /*!< SMB3 CONTROL: PIN (Bitfield-Mask: 0x01)                     */

/* ----------------------------------  SMB3_OWN  ---------------------------------- */
#define SMB3_OWN_ADDRESS_1_Pos                (0UL)                     /*!< SMB3 OWN: ADDRESS_1 (Bit 0)                                 */
#define SMB3_OWN_ADDRESS_1_Msk                (0x7fUL)                  /*!< SMB3 OWN: ADDRESS_1 (Bitfield-Mask: 0x7f)                   */
#define SMB3_OWN_ADDRESS_2_Pos                (8UL)                     /*!< SMB3 OWN: ADDRESS_2 (Bit 8)                                 */
#define SMB3_OWN_ADDRESS_2_Msk                (0x7f00UL)                /*!< SMB3 OWN: ADDRESS_2 (Bitfield-Mask: 0x7f)                   */

/* -----------------------------  SMB3_MASTER_COMMAND  ---------------------------- */
#define SMB3_MASTER_COMMAND_MRUN_Pos          (0UL)                     /*!< SMB3 MASTER_COMMAND: MRUN (Bit 0)                           */
#define SMB3_MASTER_COMMAND_MRUN_Msk          (0x1UL)                   /*!< SMB3 MASTER_COMMAND: MRUN (Bitfield-Mask: 0x01)             */
#define SMB3_MASTER_COMMAND_MPROCEED_Pos      (1UL)                     /*!< SMB3 MASTER_COMMAND: MPROCEED (Bit 1)                       */
#define SMB3_MASTER_COMMAND_MPROCEED_Msk      (0x2UL)                   /*!< SMB3 MASTER_COMMAND: MPROCEED (Bitfield-Mask: 0x01)         */
#define SMB3_MASTER_COMMAND_START0_Pos        (8UL)                     /*!< SMB3 MASTER_COMMAND: START0 (Bit 8)                         */
#define SMB3_MASTER_COMMAND_START0_Msk        (0x100UL)                 /*!< SMB3 MASTER_COMMAND: START0 (Bitfield-Mask: 0x01)           */
#define SMB3_MASTER_COMMAND_STARTN_Pos        (9UL)                     /*!< SMB3 MASTER_COMMAND: STARTN (Bit 9)                         */
#define SMB3_MASTER_COMMAND_STARTN_Msk        (0x200UL)                 /*!< SMB3 MASTER_COMMAND: STARTN (Bitfield-Mask: 0x01)           */
#define SMB3_MASTER_COMMAND_STOP_Pos          (10UL)                    /*!< SMB3 MASTER_COMMAND: STOP (Bit 10)                          */
#define SMB3_MASTER_COMMAND_STOP_Msk          (0x400UL)                 /*!< SMB3 MASTER_COMMAND: STOP (Bitfield-Mask: 0x01)             */
#define SMB3_MASTER_COMMAND_PEC_TERM_Pos      (11UL)                    /*!< SMB3 MASTER_COMMAND: PEC_TERM (Bit 11)                      */
#define SMB3_MASTER_COMMAND_PEC_TERM_Msk      (0x800UL)                 /*!< SMB3 MASTER_COMMAND: PEC_TERM (Bitfield-Mask: 0x01)         */
#define SMB3_MASTER_COMMAND_READM_Pos         (12UL)                    /*!< SMB3 MASTER_COMMAND: READM (Bit 12)                         */
#define SMB3_MASTER_COMMAND_READM_Msk         (0x1000UL)                /*!< SMB3 MASTER_COMMAND: READM (Bitfield-Mask: 0x01)            */
#define SMB3_MASTER_COMMAND_READ_PEC_Pos      (13UL)                    /*!< SMB3 MASTER_COMMAND: READ_PEC (Bit 13)                      */
#define SMB3_MASTER_COMMAND_READ_PEC_Msk      (0x2000UL)                /*!< SMB3 MASTER_COMMAND: READ_PEC (Bitfield-Mask: 0x01)         */
#define SMB3_MASTER_COMMAND_WRITECOUNT_Pos    (16UL)                    /*!< SMB3 MASTER_COMMAND: WRITECOUNT (Bit 16)                    */
#define SMB3_MASTER_COMMAND_WRITECOUNT_Msk    (0xff0000UL)              /*!< SMB3 MASTER_COMMAND: WRITECOUNT (Bitfield-Mask: 0xff)       */
#define SMB3_MASTER_COMMAND_READCOUNT_Pos     (24UL)                    /*!< SMB3 MASTER_COMMAND: READCOUNT (Bit 24)                     */
#define SMB3_MASTER_COMMAND_READCOUNT_Msk     (0xff000000UL)            /*!< SMB3 MASTER_COMMAND: READCOUNT (Bitfield-Mask: 0xff)        */

/* -----------------------------  SMB3_SLAVE_COMMAND  ----------------------------- */
#define SMB3_SLAVE_COMMAND_SRUN_Pos           (0UL)                     /*!< SMB3 SLAVE_COMMAND: SRUN (Bit 0)                            */
#define SMB3_SLAVE_COMMAND_SRUN_Msk           (0x1UL)                   /*!< SMB3 SLAVE_COMMAND: SRUN (Bitfield-Mask: 0x01)              */
#define SMB3_SLAVE_COMMAND_SPROCEED_Pos       (1UL)                     /*!< SMB3 SLAVE_COMMAND: SPROCEED (Bit 1)                        */
#define SMB3_SLAVE_COMMAND_SPROCEED_Msk       (0x2UL)                   /*!< SMB3 SLAVE_COMMAND: SPROCEED (Bitfield-Mask: 0x01)          */
#define SMB3_SLAVE_COMMAND_SLAVE_PEC_Pos      (2UL)                     /*!< SMB3 SLAVE_COMMAND: SLAVE_PEC (Bit 2)                       */
#define SMB3_SLAVE_COMMAND_SLAVE_PEC_Msk      (0x4UL)                   /*!< SMB3 SLAVE_COMMAND: SLAVE_PEC (Bitfield-Mask: 0x01)         */
#define SMB3_SLAVE_COMMAND_SLAVE_WRITECOUNT_Pos (8UL)                   /*!< SMB3 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bit 8)                */
#define SMB3_SLAVE_COMMAND_SLAVE_WRITECOUNT_Msk (0xff00UL)              /*!< SMB3 SLAVE_COMMAND: SLAVE_WRITECOUNT (Bitfield-Mask: 0xff)  */
#define SMB3_SLAVE_COMMAND_SLAVE_READCOUNT_Pos (16UL)                   /*!< SMB3 SLAVE_COMMAND: SLAVE_READCOUNT (Bit 16)                */
#define SMB3_SLAVE_COMMAND_SLAVE_READCOUNT_Msk (0xff0000UL)             /*!< SMB3 SLAVE_COMMAND: SLAVE_READCOUNT (Bitfield-Mask: 0xff)   */

/* -------------------------------  SMB3_COMPLETION  ------------------------------ */
#define SMB3_COMPLETION_DTEN_Pos              (2UL)                     /*!< SMB3 COMPLETION: DTEN (Bit 2)                               */
#define SMB3_COMPLETION_DTEN_Msk              (0x4UL)                   /*!< SMB3 COMPLETION: DTEN (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_MCEN_Pos              (3UL)                     /*!< SMB3 COMPLETION: MCEN (Bit 3)                               */
#define SMB3_COMPLETION_MCEN_Msk              (0x8UL)                   /*!< SMB3 COMPLETION: MCEN (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_SCEN_Pos              (4UL)                     /*!< SMB3 COMPLETION: SCEN (Bit 4)                               */
#define SMB3_COMPLETION_SCEN_Msk              (0x10UL)                  /*!< SMB3 COMPLETION: SCEN (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_BIDEN_Pos             (5UL)                     /*!< SMB3 COMPLETION: BIDEN (Bit 5)                              */
#define SMB3_COMPLETION_BIDEN_Msk             (0x20UL)                  /*!< SMB3 COMPLETION: BIDEN (Bitfield-Mask: 0x01)                */
#define SMB3_COMPLETION_TIMERR_Pos            (6UL)                     /*!< SMB3 COMPLETION: TIMERR (Bit 6)                             */
#define SMB3_COMPLETION_TIMERR_Msk            (0x40UL)                  /*!< SMB3 COMPLETION: TIMERR (Bitfield-Mask: 0x01)               */
#define SMB3_COMPLETION_DTO_Pos               (8UL)                     /*!< SMB3 COMPLETION: DTO (Bit 8)                                */
#define SMB3_COMPLETION_DTO_Msk               (0x100UL)                 /*!< SMB3 COMPLETION: DTO (Bitfield-Mask: 0x01)                  */
#define SMB3_COMPLETION_MCTO_Pos              (9UL)                     /*!< SMB3 COMPLETION: MCTO (Bit 9)                               */
#define SMB3_COMPLETION_MCTO_Msk              (0x200UL)                 /*!< SMB3 COMPLETION: MCTO (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_SCTO_Pos              (10UL)                    /*!< SMB3 COMPLETION: SCTO (Bit 10)                              */
#define SMB3_COMPLETION_SCTO_Msk              (0x400UL)                 /*!< SMB3 COMPLETION: SCTO (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_CHDL_Pos              (11UL)                    /*!< SMB3 COMPLETION: CHDL (Bit 11)                              */
#define SMB3_COMPLETION_CHDL_Msk              (0x800UL)                 /*!< SMB3 COMPLETION: CHDL (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_CHDH_Pos              (12UL)                    /*!< SMB3 COMPLETION: CHDH (Bit 12)                              */
#define SMB3_COMPLETION_CHDH_Msk              (0x1000UL)                /*!< SMB3 COMPLETION: CHDH (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_BER_Pos               (13UL)                    /*!< SMB3 COMPLETION: BER (Bit 13)                               */
#define SMB3_COMPLETION_BER_Msk               (0x2000UL)                /*!< SMB3 COMPLETION: BER (Bitfield-Mask: 0x01)                  */
#define SMB3_COMPLETION_LAB_Pos               (14UL)                    /*!< SMB3 COMPLETION: LAB (Bit 14)                               */
#define SMB3_COMPLETION_LAB_Msk               (0x4000UL)                /*!< SMB3 COMPLETION: LAB (Bitfield-Mask: 0x01)                  */
#define SMB3_COMPLETION_SNAKR_Pos             (16UL)                    /*!< SMB3 COMPLETION: SNAKR (Bit 16)                             */
#define SMB3_COMPLETION_SNAKR_Msk             (0x10000UL)               /*!< SMB3 COMPLETION: SNAKR (Bitfield-Mask: 0x01)                */
#define SMB3_COMPLETION_STR_Pos               (17UL)                    /*!< SMB3 COMPLETION: STR (Bit 17)                               */
#define SMB3_COMPLETION_STR_Msk               (0x20000UL)               /*!< SMB3 COMPLETION: STR (Bitfield-Mask: 0x01)                  */
#define SMB3_COMPLETION_SPROT_Pos             (19UL)                    /*!< SMB3 COMPLETION: SPROT (Bit 19)                             */
#define SMB3_COMPLETION_SPROT_Msk             (0x80000UL)               /*!< SMB3 COMPLETION: SPROT (Bitfield-Mask: 0x01)                */
#define SMB3_COMPLETION_REPEAT_READ_Pos       (20UL)                    /*!< SMB3 COMPLETION: REPEAT_READ (Bit 20)                       */
#define SMB3_COMPLETION_REPEAT_READ_Msk       (0x100000UL)              /*!< SMB3 COMPLETION: REPEAT_READ (Bitfield-Mask: 0x01)          */
#define SMB3_COMPLETION_REPEAT_WRITE_Pos      (21UL)                    /*!< SMB3 COMPLETION: REPEAT_WRITE (Bit 21)                      */
#define SMB3_COMPLETION_REPEAT_WRITE_Msk      (0x200000UL)              /*!< SMB3 COMPLETION: REPEAT_WRITE (Bitfield-Mask: 0x01)         */
#define SMB3_COMPLETION_MNAKX_Pos             (24UL)                    /*!< SMB3 COMPLETION: MNAKX (Bit 24)                             */
#define SMB3_COMPLETION_MNAKX_Msk             (0x1000000UL)             /*!< SMB3 COMPLETION: MNAKX (Bitfield-Mask: 0x01)                */
#define SMB3_COMPLETION_MTR_Pos               (25UL)                    /*!< SMB3 COMPLETION: MTR (Bit 25)                               */
#define SMB3_COMPLETION_MTR_Msk               (0x2000000UL)             /*!< SMB3 COMPLETION: MTR (Bitfield-Mask: 0x01)                  */
#define SMB3_COMPLETION_IDLE_Pos              (29UL)                    /*!< SMB3 COMPLETION: IDLE (Bit 29)                              */
#define SMB3_COMPLETION_IDLE_Msk              (0x20000000UL)            /*!< SMB3 COMPLETION: IDLE (Bitfield-Mask: 0x01)                 */
#define SMB3_COMPLETION_MDONE_Pos             (30UL)                    /*!< SMB3 COMPLETION: MDONE (Bit 30)                             */
#define SMB3_COMPLETION_MDONE_Msk             (0x40000000UL)            /*!< SMB3 COMPLETION: MDONE (Bitfield-Mask: 0x01)                */
#define SMB3_COMPLETION_SDONE_Pos             (31UL)                    /*!< SMB3 COMPLETION: SDONE (Bit 31)                             */
#define SMB3_COMPLETION_SDONE_Msk             (0x80000000UL)            /*!< SMB3 COMPLETION: SDONE (Bitfield-Mask: 0x01)                */

/* ------------------------------  SMB3_IDLE_SCALING  ----------------------------- */
#define SMB3_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Pos (0UL)                   /*!< SMB3 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bit 0)                */
#define SMB3_IDLE_SCALING_FAIR_BUS_IDLE_MIN_Msk (0xfffUL)               /*!< SMB3 IDLE_SCALING: FAIR_BUS_IDLE_MIN (Bitfield-Mask: 0xfff) */
#define SMB3_IDLE_SCALING_FAIR_IDLE_DELAY_Pos (16UL)                    /*!< SMB3 IDLE_SCALING: FAIR_IDLE_DELAY (Bit 16)                 */
#define SMB3_IDLE_SCALING_FAIR_IDLE_DELAY_Msk (0xfff0000UL)             /*!< SMB3 IDLE_SCALING: FAIR_IDLE_DELAY (Bitfield-Mask: 0xfff)   */

/* -----------------------------  SMB3_CONFIGURATION  ----------------------------- */
#define SMB3_CONFIGURATION_PORT_SEL_Pos       (0UL)                     /*!< SMB3 CONFIGURATION: PORT_SEL (Bit 0)                        */
#define SMB3_CONFIGURATION_PORT_SEL_Msk       (0xfUL)                   /*!< SMB3 CONFIGURATION: PORT_SEL (Bitfield-Mask: 0x0f)          */
#define SMB3_CONFIGURATION_TCEN_Pos           (4UL)                     /*!< SMB3 CONFIGURATION: TCEN (Bit 4)                            */
#define SMB3_CONFIGURATION_TCEN_Msk           (0x10UL)                  /*!< SMB3 CONFIGURATION: TCEN (Bitfield-Mask: 0x01)              */
#define SMB3_CONFIGURATION_SLOW_CLOCK_Pos     (5UL)                     /*!< SMB3 CONFIGURATION: SLOW_CLOCK (Bit 5)                      */
#define SMB3_CONFIGURATION_SLOW_CLOCK_Msk     (0x20UL)                  /*!< SMB3 CONFIGURATION: SLOW_CLOCK (Bitfield-Mask: 0x01)        */
#define SMB3_CONFIGURATION_PECEN_Pos          (7UL)                     /*!< SMB3 CONFIGURATION: PECEN (Bit 7)                           */
#define SMB3_CONFIGURATION_PECEN_Msk          (0x80UL)                  /*!< SMB3 CONFIGURATION: PECEN (Bitfield-Mask: 0x01)             */
#define SMB3_CONFIGURATION_DFEN_Pos           (8UL)                     /*!< SMB3 CONFIGURATION: DFEN (Bit 8)                            */
#define SMB3_CONFIGURATION_DFEN_Msk           (0x100UL)                 /*!< SMB3 CONFIGURATION: DFEN (Bitfield-Mask: 0x01)              */
#define SMB3_CONFIGURATION_RESET_Pos          (9UL)                     /*!< SMB3 CONFIGURATION: RESET (Bit 9)                           */
#define SMB3_CONFIGURATION_RESET_Msk          (0x200UL)                 /*!< SMB3 CONFIGURATION: RESET (Bitfield-Mask: 0x01)             */
#define SMB3_CONFIGURATION_ENAB_Pos           (10UL)                    /*!< SMB3 CONFIGURATION: ENAB (Bit 10)                           */
#define SMB3_CONFIGURATION_ENAB_Msk           (0x400UL)                 /*!< SMB3 CONFIGURATION: ENAB (Bitfield-Mask: 0x01)              */
#define SMB3_CONFIGURATION_DSA_Pos            (11UL)                    /*!< SMB3 CONFIGURATION: DSA (Bit 11)                            */
#define SMB3_CONFIGURATION_DSA_Msk            (0x800UL)                 /*!< SMB3 CONFIGURATION: DSA (Bitfield-Mask: 0x01)               */
#define SMB3_CONFIGURATION_FAIR_Pos           (12UL)                    /*!< SMB3 CONFIGURATION: FAIR (Bit 12)                           */
#define SMB3_CONFIGURATION_FAIR_Msk           (0x1000UL)                /*!< SMB3 CONFIGURATION: FAIR (Bitfield-Mask: 0x01)              */
#define SMB3_CONFIGURATION_GC_DIS_Pos         (14UL)                    /*!< SMB3 CONFIGURATION: GC_DIS (Bit 14)                         */
#define SMB3_CONFIGURATION_GC_DIS_Msk         (0x4000UL)                /*!< SMB3 CONFIGURATION: GC_DIS (Bitfield-Mask: 0x01)            */
#define SMB3_CONFIGURATION_FLUSH_SXBUF_Pos    (16UL)                    /*!< SMB3 CONFIGURATION: FLUSH_SXBUF (Bit 16)                    */
#define SMB3_CONFIGURATION_FLUSH_SXBUF_Msk    (0x10000UL)               /*!< SMB3 CONFIGURATION: FLUSH_SXBUF (Bitfield-Mask: 0x01)       */
#define SMB3_CONFIGURATION_FLUSH_SRBUF_Pos    (17UL)                    /*!< SMB3 CONFIGURATION: FLUSH_SRBUF (Bit 17)                    */
#define SMB3_CONFIGURATION_FLUSH_SRBUF_Msk    (0x20000UL)               /*!< SMB3 CONFIGURATION: FLUSH_SRBUF (Bitfield-Mask: 0x01)       */
#define SMB3_CONFIGURATION_FLUSH_MXBUF_Pos    (18UL)                    /*!< SMB3 CONFIGURATION: FLUSH_MXBUF (Bit 18)                    */
#define SMB3_CONFIGURATION_FLUSH_MXBUF_Msk    (0x40000UL)               /*!< SMB3 CONFIGURATION: FLUSH_MXBUF (Bitfield-Mask: 0x01)       */
#define SMB3_CONFIGURATION_FLUSH_MRBUF_Pos    (19UL)                    /*!< SMB3 CONFIGURATION: FLUSH_MRBUF (Bit 19)                    */
#define SMB3_CONFIGURATION_FLUSH_MRBUF_Msk    (0x80000UL)               /*!< SMB3 CONFIGURATION: FLUSH_MRBUF (Bitfield-Mask: 0x01)       */
#define SMB3_CONFIGURATION_EN_AAS_Pos         (28UL)                    /*!< SMB3 CONFIGURATION: EN_AAS (Bit 28)                         */
#define SMB3_CONFIGURATION_EN_AAS_Msk         (0x10000000UL)            /*!< SMB3 CONFIGURATION: EN_AAS (Bitfield-Mask: 0x01)            */
#define SMB3_CONFIGURATION_ENIDI_Pos          (29UL)                    /*!< SMB3 CONFIGURATION: ENIDI (Bit 29)                          */
#define SMB3_CONFIGURATION_ENIDI_Msk          (0x20000000UL)            /*!< SMB3 CONFIGURATION: ENIDI (Bitfield-Mask: 0x01)             */
#define SMB3_CONFIGURATION_ENMI_Pos           (30UL)                    /*!< SMB3 CONFIGURATION: ENMI (Bit 30)                           */
#define SMB3_CONFIGURATION_ENMI_Msk           (0x40000000UL)            /*!< SMB3 CONFIGURATION: ENMI (Bitfield-Mask: 0x01)              */
#define SMB3_CONFIGURATION_ENSI_Pos           (31UL)                    /*!< SMB3 CONFIGURATION: ENSI (Bit 31)                           */
#define SMB3_CONFIGURATION_ENSI_Msk           (0x80000000UL)            /*!< SMB3 CONFIGURATION: ENSI (Bitfield-Mask: 0x01)              */

/* -------------------------------  SMB3_BUS_CLOCK  ------------------------------- */
#define SMB3_BUS_CLOCK_LOW_PERIOD_Pos         (0UL)                     /*!< SMB3 BUS_CLOCK: LOW_PERIOD (Bit 0)                          */
#define SMB3_BUS_CLOCK_LOW_PERIOD_Msk         (0xffUL)                  /*!< SMB3 BUS_CLOCK: LOW_PERIOD (Bitfield-Mask: 0xff)            */
#define SMB3_BUS_CLOCK_HIGH_PERIOD_Pos        (8UL)                     /*!< SMB3 BUS_CLOCK: HIGH_PERIOD (Bit 8)                         */
#define SMB3_BUS_CLOCK_HIGH_PERIOD_Msk        (0xff00UL)                /*!< SMB3 BUS_CLOCK: HIGH_PERIOD (Bitfield-Mask: 0xff)           */

/* ----------------------------  SMB3_BIT_BANG_CONTROL  --------------------------- */
#define SMB3_BIT_BANG_CONTROL_BBEN_Pos        (0UL)                     /*!< SMB3 BIT_BANG_CONTROL: BBEN (Bit 0)                         */
#define SMB3_BIT_BANG_CONTROL_BBEN_Msk        (0x1UL)                   /*!< SMB3 BIT_BANG_CONTROL: BBEN (Bitfield-Mask: 0x01)           */
#define SMB3_BIT_BANG_CONTROL_CLDIR_Pos       (1UL)                     /*!< SMB3 BIT_BANG_CONTROL: CLDIR (Bit 1)                        */
#define SMB3_BIT_BANG_CONTROL_CLDIR_Msk       (0x2UL)                   /*!< SMB3 BIT_BANG_CONTROL: CLDIR (Bitfield-Mask: 0x01)          */
#define SMB3_BIT_BANG_CONTROL_DADIR_Pos       (2UL)                     /*!< SMB3 BIT_BANG_CONTROL: DADIR (Bit 2)                        */
#define SMB3_BIT_BANG_CONTROL_DADIR_Msk       (0x4UL)                   /*!< SMB3 BIT_BANG_CONTROL: DADIR (Bitfield-Mask: 0x01)          */
#define SMB3_BIT_BANG_CONTROL_BBCLK_Pos       (3UL)                     /*!< SMB3 BIT_BANG_CONTROL: BBCLK (Bit 3)                        */
#define SMB3_BIT_BANG_CONTROL_BBCLK_Msk       (0x8UL)                   /*!< SMB3 BIT_BANG_CONTROL: BBCLK (Bitfield-Mask: 0x01)          */
#define SMB3_BIT_BANG_CONTROL_BBDAT_Pos       (4UL)                     /*!< SMB3 BIT_BANG_CONTROL: BBDAT (Bit 4)                        */
#define SMB3_BIT_BANG_CONTROL_BBDAT_Msk       (0x10UL)                  /*!< SMB3 BIT_BANG_CONTROL: BBDAT (Bitfield-Mask: 0x01)          */
#define SMB3_BIT_BANG_CONTROL_BBCLKI_Pos      (5UL)                     /*!< SMB3 BIT_BANG_CONTROL: BBCLKI (Bit 5)                       */
#define SMB3_BIT_BANG_CONTROL_BBCLKI_Msk      (0x20UL)                  /*!< SMB3 BIT_BANG_CONTROL: BBCLKI (Bitfield-Mask: 0x01)         */
#define SMB3_BIT_BANG_CONTROL_BBDATI_Pos      (6UL)                     /*!< SMB3 BIT_BANG_CONTROL: BBDATI (Bit 6)                       */
#define SMB3_BIT_BANG_CONTROL_BBDATI_Msk      (0x40UL)                  /*!< SMB3 BIT_BANG_CONTROL: BBDATI (Bitfield-Mask: 0x01)         */

/* ------------------------------  SMB3_DATA_TIMING  ------------------------------ */
#define SMB3_DATA_TIMING_DATA_HOLD_Pos        (0UL)                     /*!< SMB3 DATA_TIMING: DATA_HOLD (Bit 0)                         */
#define SMB3_DATA_TIMING_DATA_HOLD_Msk        (0xffUL)                  /*!< SMB3 DATA_TIMING: DATA_HOLD (Bitfield-Mask: 0xff)           */
#define SMB3_DATA_TIMING_RESTART_SETUP_Pos    (8UL)                     /*!< SMB3 DATA_TIMING: RESTART_SETUP (Bit 8)                     */
#define SMB3_DATA_TIMING_RESTART_SETUP_Msk    (0xff00UL)                /*!< SMB3 DATA_TIMING: RESTART_SETUP (Bitfield-Mask: 0xff)       */
#define SMB3_DATA_TIMING_STOP_SETUP_Pos       (16UL)                    /*!< SMB3 DATA_TIMING: STOP_SETUP (Bit 16)                       */
#define SMB3_DATA_TIMING_STOP_SETUP_Msk       (0xff0000UL)              /*!< SMB3 DATA_TIMING: STOP_SETUP (Bitfield-Mask: 0xff)          */
#define SMB3_DATA_TIMING_START_HOLD_Pos       (24UL)                    /*!< SMB3 DATA_TIMING: START_HOLD (Bit 24)                       */
#define SMB3_DATA_TIMING_START_HOLD_Msk       (0xff000000UL)            /*!< SMB3 DATA_TIMING: START_HOLD (Bitfield-Mask: 0xff)          */

/* ----------------------------  SMB3_TIME_OUT_SCALING  --------------------------- */
#define SMB3_TIME_OUT_SCALING_CLOCK_HIGH_Pos  (0UL)                     /*!< SMB3 TIME_OUT_SCALING: CLOCK_HIGH (Bit 0)                   */
#define SMB3_TIME_OUT_SCALING_CLOCK_HIGH_Msk  (0xffUL)                  /*!< SMB3 TIME_OUT_SCALING: CLOCK_HIGH (Bitfield-Mask: 0xff)     */
#define SMB3_TIME_OUT_SCALING_SLAVE_CUM_Pos   (8UL)                     /*!< SMB3 TIME_OUT_SCALING: SLAVE_CUM (Bit 8)                    */
#define SMB3_TIME_OUT_SCALING_SLAVE_CUM_Msk   (0xff00UL)                /*!< SMB3 TIME_OUT_SCALING: SLAVE_CUM (Bitfield-Mask: 0xff)      */
#define SMB3_TIME_OUT_SCALING_MASTER_CUM_Pos  (16UL)                    /*!< SMB3 TIME_OUT_SCALING: MASTER_CUM (Bit 16)                  */
#define SMB3_TIME_OUT_SCALING_MASTER_CUM_Msk  (0xff0000UL)              /*!< SMB3 TIME_OUT_SCALING: MASTER_CUM (Bitfield-Mask: 0xff)     */
#define SMB3_TIME_OUT_SCALING_BUS_IDLE_MIN_Pos (24UL)                   /*!< SMB3 TIME_OUT_SCALING: BUS_IDLE_MIN (Bit 24)                */
#define SMB3_TIME_OUT_SCALING_BUS_IDLE_MIN_Msk (0xff000000UL)           /*!< SMB3 TIME_OUT_SCALING: BUS_IDLE_MIN (Bitfield-Mask: 0xff)   */


/* ================================================================================ */
/* ================          struct 'PECI' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PECI_CONTROL  -------------------------------- */
#define PECI_CONTROL_PD_Pos                   (0UL)                     /*!< PECI CONTROL: PD (Bit 0)                                    */
#define PECI_CONTROL_PD_Msk                   (0x1UL)                   /*!< PECI CONTROL: PD (Bitfield-Mask: 0x01)                      */
#define PECI_CONTROL_RST_Pos                  (3UL)                     /*!< PECI CONTROL: RST (Bit 3)                                   */
#define PECI_CONTROL_RST_Msk                  (0x8UL)                   /*!< PECI CONTROL: RST (Bitfield-Mask: 0x01)                     */
#define PECI_CONTROL_FRST_Pos                 (5UL)                     /*!< PECI CONTROL: FRST (Bit 5)                                  */
#define PECI_CONTROL_FRST_Msk                 (0x20UL)                  /*!< PECI CONTROL: FRST (Bitfield-Mask: 0x01)                    */
#define PECI_CONTROL_TXEN_Pos                 (6UL)                     /*!< PECI CONTROL: TXEN (Bit 6)                                  */
#define PECI_CONTROL_TXEN_Msk                 (0x40UL)                  /*!< PECI CONTROL: TXEN (Bitfield-Mask: 0x01)                    */
#define PECI_CONTROL_MIEN_Pos                 (7UL)                     /*!< PECI CONTROL: MIEN (Bit 7)                                  */
#define PECI_CONTROL_MIEN_Msk                 (0x80UL)                  /*!< PECI CONTROL: MIEN (Bitfield-Mask: 0x01)                    */

/* --------------------------------  PECI_STATUS1  -------------------------------- */
#define PECI_STATUS1_BOF_Pos                  (0UL)                     /*!< PECI STATUS1: BOF (Bit 0)                                   */
#define PECI_STATUS1_BOF_Msk                  (0x1UL)                   /*!< PECI STATUS1: BOF (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS1_EOF_Pos                  (1UL)                     /*!< PECI STATUS1: EOF (Bit 1)                                   */
#define PECI_STATUS1_EOF_Msk                  (0x2UL)                   /*!< PECI STATUS1: EOF (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS1_ERR_Pos                  (2UL)                     /*!< PECI STATUS1: ERR (Bit 2)                                   */
#define PECI_STATUS1_ERR_Msk                  (0x4UL)                   /*!< PECI STATUS1: ERR (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS1_RDY_Pos                  (3UL)                     /*!< PECI STATUS1: RDY (Bit 3)                                   */
#define PECI_STATUS1_RDY_Msk                  (0x8UL)                   /*!< PECI STATUS1: RDY (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS1_RDYLO_Pos                (4UL)                     /*!< PECI STATUS1: RDYLO (Bit 4)                                 */
#define PECI_STATUS1_RDYLO_Msk                (0x10UL)                  /*!< PECI STATUS1: RDYLO (Bitfield-Mask: 0x01)                   */
#define PECI_STATUS1_RDYHI_Pos                (5UL)                     /*!< PECI STATUS1: RDYHI (Bit 5)                                 */
#define PECI_STATUS1_RDYHI_Msk                (0x20UL)                  /*!< PECI STATUS1: RDYHI (Bitfield-Mask: 0x01)                   */
#define PECI_STATUS1_MINT_Pos                 (7UL)                     /*!< PECI STATUS1: MINT (Bit 7)                                  */
#define PECI_STATUS1_MINT_Msk                 (0x80UL)                  /*!< PECI STATUS1: MINT (Bitfield-Mask: 0x01)                    */

/* --------------------------------  PECI_STATUS2  -------------------------------- */
#define PECI_STATUS2_WFF_Pos                  (0UL)                     /*!< PECI STATUS2: WFF (Bit 0)                                   */
#define PECI_STATUS2_WFF_Msk                  (0x1UL)                   /*!< PECI STATUS2: WFF (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS2_WFE_Pos                  (1UL)                     /*!< PECI STATUS2: WFE (Bit 1)                                   */
#define PECI_STATUS2_WFE_Msk                  (0x2UL)                   /*!< PECI STATUS2: WFE (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS2_RFF_Pos                  (2UL)                     /*!< PECI STATUS2: RFF (Bit 2)                                   */
#define PECI_STATUS2_RFF_Msk                  (0x4UL)                   /*!< PECI STATUS2: RFF (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS2_RFE_Pos                  (3UL)                     /*!< PECI STATUS2: RFE (Bit 3)                                   */
#define PECI_STATUS2_RFE_Msk                  (0x8UL)                   /*!< PECI STATUS2: RFE (Bitfield-Mask: 0x01)                     */
#define PECI_STATUS2_IDLE_Pos                 (7UL)                     /*!< PECI STATUS2: IDLE (Bit 7)                                  */
#define PECI_STATUS2_IDLE_Msk                 (0x80UL)                  /*!< PECI STATUS2: IDLE (Bitfield-Mask: 0x01)                    */

/* ---------------------------------  PECI_ERROR  --------------------------------- */
#define PECI_ERROR_FERR_Pos                   (0UL)                     /*!< PECI ERROR: FERR (Bit 0)                                    */
#define PECI_ERROR_FERR_Msk                   (0x1UL)                   /*!< PECI ERROR: FERR (Bitfield-Mask: 0x01)                      */
#define PECI_ERROR_BERR_Pos                   (1UL)                     /*!< PECI ERROR: BERR (Bit 1)                                    */
#define PECI_ERROR_BERR_Msk                   (0x2UL)                   /*!< PECI ERROR: BERR (Bitfield-Mask: 0x01)                      */
#define PECI_ERROR_REQERR_Pos                 (3UL)                     /*!< PECI ERROR: REQERR (Bit 3)                                  */
#define PECI_ERROR_REQERR_Msk                 (0x8UL)                   /*!< PECI ERROR: REQERR (Bitfield-Mask: 0x01)                    */
#define PECI_ERROR_WROV_Pos                   (4UL)                     /*!< PECI ERROR: WROV (Bit 4)                                    */
#define PECI_ERROR_WROV_Msk                   (0x10UL)                  /*!< PECI ERROR: WROV (Bitfield-Mask: 0x01)                      */
#define PECI_ERROR_WRUN_Pos                   (5UL)                     /*!< PECI ERROR: WRUN (Bit 5)                                    */
#define PECI_ERROR_WRUN_Msk                   (0x20UL)                  /*!< PECI ERROR: WRUN (Bitfield-Mask: 0x01)                      */
#define PECI_ERROR_RDOV_Pos                   (6UL)                     /*!< PECI ERROR: RDOV (Bit 6)                                    */
#define PECI_ERROR_RDOV_Msk                   (0x40UL)                  /*!< PECI ERROR: RDOV (Bitfield-Mask: 0x01)                      */
#define PECI_ERROR_CLKERR_Pos                 (7UL)                     /*!< PECI ERROR: CLKERR (Bit 7)                                  */
#define PECI_ERROR_CLKERR_Msk                 (0x80UL)                  /*!< PECI ERROR: CLKERR (Bitfield-Mask: 0x01)                    */

/* --------------------------------  PECI_INT_EN1  -------------------------------- */
#define PECI_INT_EN1_BIEN_Pos                 (0UL)                     /*!< PECI INT_EN1: BIEN (Bit 0)                                  */
#define PECI_INT_EN1_BIEN_Msk                 (0x1UL)                   /*!< PECI INT_EN1: BIEN (Bitfield-Mask: 0x01)                    */
#define PECI_INT_EN1_EIEN_Pos                 (1UL)                     /*!< PECI INT_EN1: EIEN (Bit 1)                                  */
#define PECI_INT_EN1_EIEN_Msk                 (0x2UL)                   /*!< PECI INT_EN1: EIEN (Bitfield-Mask: 0x01)                    */
#define PECI_INT_EN1_EREN_Pos                 (2UL)                     /*!< PECI INT_EN1: EREN (Bit 2)                                  */
#define PECI_INT_EN1_EREN_Msk                 (0x4UL)                   /*!< PECI INT_EN1: EREN (Bitfield-Mask: 0x01)                    */
#define PECI_INT_EN1_RLEN_Pos                 (4UL)                     /*!< PECI INT_EN1: RLEN (Bit 4)                                  */
#define PECI_INT_EN1_RLEN_Msk                 (0x10UL)                  /*!< PECI INT_EN1: RLEN (Bitfield-Mask: 0x01)                    */
#define PECI_INT_EN1_RHEN_Pos                 (5UL)                     /*!< PECI INT_EN1: RHEN (Bit 5)                                  */
#define PECI_INT_EN1_RHEN_Msk                 (0x20UL)                  /*!< PECI INT_EN1: RHEN (Bitfield-Mask: 0x01)                    */

/* --------------------------------  PECI_INT_EN2  -------------------------------- */
#define PECI_INT_EN2_ENWFE_Pos                (1UL)                     /*!< PECI INT_EN2: ENWFE (Bit 1)                                 */
#define PECI_INT_EN2_ENWFE_Msk                (0x2UL)                   /*!< PECI INT_EN2: ENWFE (Bitfield-Mask: 0x01)                   */
#define PECI_INT_EN2_ENRFF_Pos                (2UL)                     /*!< PECI INT_EN2: ENRFF (Bit 2)                                 */
#define PECI_INT_EN2_ENRFF_Msk                (0x4UL)                   /*!< PECI INT_EN2: ENRFF (Bitfield-Mask: 0x01)                   */


/* ================================================================================ */
/* ================         struct 'TACH_0' Position & Mask        ================ */
/* ================================================================================ */


/* -------------------------------  TACH_0_CONTROL  ------------------------------- */
#define TACH_0_CONTROL_OUT_LIMIT_ENABLE_Pos   (0UL)                     /*!< TACH_0 CONTROL: OUT_LIMIT_ENABLE (Bit 0)                    */
#define TACH_0_CONTROL_OUT_LIMIT_ENABLE_Msk   (0x1UL)                   /*!< TACH_0 CONTROL: OUT_LIMIT_ENABLE (Bitfield-Mask: 0x01)      */
#define TACH_0_CONTROL_TACH_EN_Pos            (1UL)                     /*!< TACH_0 CONTROL: TACH_EN (Bit 1)                             */
#define TACH_0_CONTROL_TACH_EN_Msk            (0x2UL)                   /*!< TACH_0 CONTROL: TACH_EN (Bitfield-Mask: 0x01)               */
#define TACH_0_CONTROL_FILTER_EN_Pos          (8UL)                     /*!< TACH_0 CONTROL: FILTER_EN (Bit 8)                           */
#define TACH_0_CONTROL_FILTER_EN_Msk          (0x100UL)                 /*!< TACH_0 CONTROL: FILTER_EN (Bitfield-Mask: 0x01)             */
#define TACH_0_CONTROL_MODE_SELECT_Pos        (10UL)                    /*!< TACH_0 CONTROL: MODE_SELECT (Bit 10)                        */
#define TACH_0_CONTROL_MODE_SELECT_Msk        (0x400UL)                 /*!< TACH_0 CONTROL: MODE_SELECT (Bitfield-Mask: 0x01)           */
#define TACH_0_CONTROL_EDGES_Pos              (11UL)                    /*!< TACH_0 CONTROL: EDGES (Bit 11)                              */
#define TACH_0_CONTROL_EDGES_Msk              (0x1800UL)                /*!< TACH_0 CONTROL: EDGES (Bitfield-Mask: 0x03)                 */
#define TACH_0_CONTROL_READY_INT_EN_Pos       (14UL)                    /*!< TACH_0 CONTROL: READY_INT_EN (Bit 14)                       */
#define TACH_0_CONTROL_READY_INT_EN_Msk       (0x4000UL)                /*!< TACH_0 CONTROL: READY_INT_EN (Bitfield-Mask: 0x01)          */
#define TACH_0_CONTROL_INPUT_INT_EN_Pos       (15UL)                    /*!< TACH_0 CONTROL: INPUT_INT_EN (Bit 15)                       */
#define TACH_0_CONTROL_INPUT_INT_EN_Msk       (0x8000UL)                /*!< TACH_0 CONTROL: INPUT_INT_EN (Bitfield-Mask: 0x01)          */
#define TACH_0_CONTROL_COUNTER_Pos            (16UL)                    /*!< TACH_0 CONTROL: COUNTER (Bit 16)                            */
#define TACH_0_CONTROL_COUNTER_Msk            (0xffff0000UL)            /*!< TACH_0 CONTROL: COUNTER (Bitfield-Mask: 0xffff)             */

/* --------------------------------  TACH_0_STATUS  ------------------------------- */
#define TACH_0_STATUS_OUT_LIMIT_Pos           (0UL)                     /*!< TACH_0 STATUS: OUT_LIMIT (Bit 0)                            */
#define TACH_0_STATUS_OUT_LIMIT_Msk           (0x1UL)                   /*!< TACH_0 STATUS: OUT_LIMIT (Bitfield-Mask: 0x01)              */
#define TACH_0_STATUS_PIN_Pos                 (1UL)                     /*!< TACH_0 STATUS: PIN (Bit 1)                                  */
#define TACH_0_STATUS_PIN_Msk                 (0x2UL)                   /*!< TACH_0 STATUS: PIN (Bitfield-Mask: 0x01)                    */
#define TACH_0_STATUS_TOGGLE_Pos              (2UL)                     /*!< TACH_0 STATUS: TOGGLE (Bit 2)                               */
#define TACH_0_STATUS_TOGGLE_Msk              (0x4UL)                   /*!< TACH_0 STATUS: TOGGLE (Bitfield-Mask: 0x01)                 */
#define TACH_0_STATUS_COUNT_READY_Pos         (3UL)                     /*!< TACH_0 STATUS: COUNT_READY (Bit 3)                          */
#define TACH_0_STATUS_COUNT_READY_Msk         (0x8UL)                   /*!< TACH_0 STATUS: COUNT_READY (Bitfield-Mask: 0x01)            */


/* ================================================================================ */
/* ================         struct 'TACH_1' Position & Mask        ================ */
/* ================================================================================ */


/* -------------------------------  TACH_1_CONTROL  ------------------------------- */
#define TACH_1_CONTROL_OUT_LIMIT_ENABLE_Pos   (0UL)                     /*!< TACH_1 CONTROL: OUT_LIMIT_ENABLE (Bit 0)                    */
#define TACH_1_CONTROL_OUT_LIMIT_ENABLE_Msk   (0x1UL)                   /*!< TACH_1 CONTROL: OUT_LIMIT_ENABLE (Bitfield-Mask: 0x01)      */
#define TACH_1_CONTROL_TACH_EN_Pos            (1UL)                     /*!< TACH_1 CONTROL: TACH_EN (Bit 1)                             */
#define TACH_1_CONTROL_TACH_EN_Msk            (0x2UL)                   /*!< TACH_1 CONTROL: TACH_EN (Bitfield-Mask: 0x01)               */
#define TACH_1_CONTROL_FILTER_EN_Pos          (8UL)                     /*!< TACH_1 CONTROL: FILTER_EN (Bit 8)                           */
#define TACH_1_CONTROL_FILTER_EN_Msk          (0x100UL)                 /*!< TACH_1 CONTROL: FILTER_EN (Bitfield-Mask: 0x01)             */
#define TACH_1_CONTROL_MODE_SELECT_Pos        (10UL)                    /*!< TACH_1 CONTROL: MODE_SELECT (Bit 10)                        */
#define TACH_1_CONTROL_MODE_SELECT_Msk        (0x400UL)                 /*!< TACH_1 CONTROL: MODE_SELECT (Bitfield-Mask: 0x01)           */
#define TACH_1_CONTROL_EDGES_Pos              (11UL)                    /*!< TACH_1 CONTROL: EDGES (Bit 11)                              */
#define TACH_1_CONTROL_EDGES_Msk              (0x1800UL)                /*!< TACH_1 CONTROL: EDGES (Bitfield-Mask: 0x03)                 */
#define TACH_1_CONTROL_READY_INT_EN_Pos       (14UL)                    /*!< TACH_1 CONTROL: READY_INT_EN (Bit 14)                       */
#define TACH_1_CONTROL_READY_INT_EN_Msk       (0x4000UL)                /*!< TACH_1 CONTROL: READY_INT_EN (Bitfield-Mask: 0x01)          */
#define TACH_1_CONTROL_INPUT_INT_EN_Pos       (15UL)                    /*!< TACH_1 CONTROL: INPUT_INT_EN (Bit 15)                       */
#define TACH_1_CONTROL_INPUT_INT_EN_Msk       (0x8000UL)                /*!< TACH_1 CONTROL: INPUT_INT_EN (Bitfield-Mask: 0x01)          */
#define TACH_1_CONTROL_COUNTER_Pos            (16UL)                    /*!< TACH_1 CONTROL: COUNTER (Bit 16)                            */
#define TACH_1_CONTROL_COUNTER_Msk            (0xffff0000UL)            /*!< TACH_1 CONTROL: COUNTER (Bitfield-Mask: 0xffff)             */

/* --------------------------------  TACH_1_STATUS  ------------------------------- */
#define TACH_1_STATUS_OUT_LIMIT_Pos           (0UL)                     /*!< TACH_1 STATUS: OUT_LIMIT (Bit 0)                            */
#define TACH_1_STATUS_OUT_LIMIT_Msk           (0x1UL)                   /*!< TACH_1 STATUS: OUT_LIMIT (Bitfield-Mask: 0x01)              */
#define TACH_1_STATUS_PIN_Pos                 (1UL)                     /*!< TACH_1 STATUS: PIN (Bit 1)                                  */
#define TACH_1_STATUS_PIN_Msk                 (0x2UL)                   /*!< TACH_1 STATUS: PIN (Bitfield-Mask: 0x01)                    */
#define TACH_1_STATUS_TOGGLE_Pos              (2UL)                     /*!< TACH_1 STATUS: TOGGLE (Bit 2)                               */
#define TACH_1_STATUS_TOGGLE_Msk              (0x4UL)                   /*!< TACH_1 STATUS: TOGGLE (Bitfield-Mask: 0x01)                 */
#define TACH_1_STATUS_COUNT_READY_Pos         (3UL)                     /*!< TACH_1 STATUS: COUNT_READY (Bit 3)                          */
#define TACH_1_STATUS_COUNT_READY_Msk         (0x8UL)                   /*!< TACH_1 STATUS: COUNT_READY (Bitfield-Mask: 0x01)            */


/* ================================================================================ */
/* ================         struct 'PWM_0' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PWM_0_CONFIG  -------------------------------- */
#define PWM_0_CONFIG_EN_Pos                   (0UL)                     /*!< PWM_0 CONFIG: EN (Bit 0)                                    */
#define PWM_0_CONFIG_EN_Msk                   (0x1UL)                   /*!< PWM_0 CONFIG: EN (Bitfield-Mask: 0x01)                      */
#define PWM_0_CONFIG_CLK_SELECT_Pos           (1UL)                     /*!< PWM_0 CONFIG: CLK_SELECT (Bit 1)                            */
#define PWM_0_CONFIG_CLK_SELECT_Msk           (0x2UL)                   /*!< PWM_0 CONFIG: CLK_SELECT (Bitfield-Mask: 0x01)              */
#define PWM_0_CONFIG_INVERT_Pos               (2UL)                     /*!< PWM_0 CONFIG: INVERT (Bit 2)                                */
#define PWM_0_CONFIG_INVERT_Msk               (0x4UL)                   /*!< PWM_0 CONFIG: INVERT (Bitfield-Mask: 0x01)                  */
#define PWM_0_CONFIG_CLK_PRE_DIVIDER_Pos      (3UL)                     /*!< PWM_0 CONFIG: CLK_PRE_DIVIDER (Bit 3)                       */
#define PWM_0_CONFIG_CLK_PRE_DIVIDER_Msk      (0x78UL)                  /*!< PWM_0 CONFIG: CLK_PRE_DIVIDER (Bitfield-Mask: 0x0f)         */


/* ================================================================================ */
/* ================         struct 'PWM_1' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PWM_1_CONFIG  -------------------------------- */
#define PWM_1_CONFIG_EN_Pos                   (0UL)                     /*!< PWM_1 CONFIG: EN (Bit 0)                                    */
#define PWM_1_CONFIG_EN_Msk                   (0x1UL)                   /*!< PWM_1 CONFIG: EN (Bitfield-Mask: 0x01)                      */
#define PWM_1_CONFIG_CLK_SELECT_Pos           (1UL)                     /*!< PWM_1 CONFIG: CLK_SELECT (Bit 1)                            */
#define PWM_1_CONFIG_CLK_SELECT_Msk           (0x2UL)                   /*!< PWM_1 CONFIG: CLK_SELECT (Bitfield-Mask: 0x01)              */
#define PWM_1_CONFIG_INVERT_Pos               (2UL)                     /*!< PWM_1 CONFIG: INVERT (Bit 2)                                */
#define PWM_1_CONFIG_INVERT_Msk               (0x4UL)                   /*!< PWM_1 CONFIG: INVERT (Bitfield-Mask: 0x01)                  */
#define PWM_1_CONFIG_CLK_PRE_DIVIDER_Pos      (3UL)                     /*!< PWM_1 CONFIG: CLK_PRE_DIVIDER (Bit 3)                       */
#define PWM_1_CONFIG_CLK_PRE_DIVIDER_Msk      (0x78UL)                  /*!< PWM_1 CONFIG: CLK_PRE_DIVIDER (Bitfield-Mask: 0x0f)         */


/* ================================================================================ */
/* ================         struct 'PWM_2' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PWM_2_CONFIG  -------------------------------- */
#define PWM_2_CONFIG_EN_Pos                   (0UL)                     /*!< PWM_2 CONFIG: EN (Bit 0)                                    */
#define PWM_2_CONFIG_EN_Msk                   (0x1UL)                   /*!< PWM_2 CONFIG: EN (Bitfield-Mask: 0x01)                      */
#define PWM_2_CONFIG_CLK_SELECT_Pos           (1UL)                     /*!< PWM_2 CONFIG: CLK_SELECT (Bit 1)                            */
#define PWM_2_CONFIG_CLK_SELECT_Msk           (0x2UL)                   /*!< PWM_2 CONFIG: CLK_SELECT (Bitfield-Mask: 0x01)              */
#define PWM_2_CONFIG_INVERT_Pos               (2UL)                     /*!< PWM_2 CONFIG: INVERT (Bit 2)                                */
#define PWM_2_CONFIG_INVERT_Msk               (0x4UL)                   /*!< PWM_2 CONFIG: INVERT (Bitfield-Mask: 0x01)                  */
#define PWM_2_CONFIG_CLK_PRE_DIVIDER_Pos      (3UL)                     /*!< PWM_2 CONFIG: CLK_PRE_DIVIDER (Bit 3)                       */
#define PWM_2_CONFIG_CLK_PRE_DIVIDER_Msk      (0x78UL)                  /*!< PWM_2 CONFIG: CLK_PRE_DIVIDER (Bitfield-Mask: 0x0f)         */


/* ================================================================================ */
/* ================         struct 'PWM_3' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PWM_3_CONFIG  -------------------------------- */
#define PWM_3_CONFIG_EN_Pos                   (0UL)                     /*!< PWM_3 CONFIG: EN (Bit 0)                                    */
#define PWM_3_CONFIG_EN_Msk                   (0x1UL)                   /*!< PWM_3 CONFIG: EN (Bitfield-Mask: 0x01)                      */
#define PWM_3_CONFIG_CLK_SELECT_Pos           (1UL)                     /*!< PWM_3 CONFIG: CLK_SELECT (Bit 1)                            */
#define PWM_3_CONFIG_CLK_SELECT_Msk           (0x2UL)                   /*!< PWM_3 CONFIG: CLK_SELECT (Bitfield-Mask: 0x01)              */
#define PWM_3_CONFIG_INVERT_Pos               (2UL)                     /*!< PWM_3 CONFIG: INVERT (Bit 2)                                */
#define PWM_3_CONFIG_INVERT_Msk               (0x4UL)                   /*!< PWM_3 CONFIG: INVERT (Bitfield-Mask: 0x01)                  */
#define PWM_3_CONFIG_CLK_PRE_DIVIDER_Pos      (3UL)                     /*!< PWM_3 CONFIG: CLK_PRE_DIVIDER (Bit 3)                       */
#define PWM_3_CONFIG_CLK_PRE_DIVIDER_Msk      (0x78UL)                  /*!< PWM_3 CONFIG: CLK_PRE_DIVIDER (Bitfield-Mask: 0x0f)         */


/* ================================================================================ */
/* ================        struct 'RPM_FAN' Position & Mask        ================ */
/* ================================================================================ */


/* ----------------------------  RPM_FAN_CONFIGURATION  --------------------------- */
#define RPM_FAN_CONFIGURATION_UPDATE_Pos      (0UL)                     /*!< RPM_FAN CONFIGURATION: UPDATE (Bit 0)                       */
#define RPM_FAN_CONFIGURATION_UPDATE_Msk      (0x7UL)                   /*!< RPM_FAN CONFIGURATION: UPDATE (Bitfield-Mask: 0x07)         */
#define RPM_FAN_CONFIGURATION_EDGES_Pos       (3UL)                     /*!< RPM_FAN CONFIGURATION: EDGES (Bit 3)                        */
#define RPM_FAN_CONFIGURATION_EDGES_Msk       (0x18UL)                  /*!< RPM_FAN CONFIGURATION: EDGES (Bitfield-Mask: 0x03)          */
#define RPM_FAN_CONFIGURATION_RANGE_Pos       (5UL)                     /*!< RPM_FAN CONFIGURATION: RANGE (Bit 5)                        */
#define RPM_FAN_CONFIGURATION_RANGE_Msk       (0x60UL)                  /*!< RPM_FAN CONFIGURATION: RANGE (Bitfield-Mask: 0x03)          */
#define RPM_FAN_CONFIGURATION_EN_ALGO_Pos     (7UL)                     /*!< RPM_FAN CONFIGURATION: EN_ALGO (Bit 7)                      */
#define RPM_FAN_CONFIGURATION_EN_ALGO_Msk     (0x80UL)                  /*!< RPM_FAN CONFIGURATION: EN_ALGO (Bitfield-Mask: 0x01)        */
#define RPM_FAN_CONFIGURATION_POLARITY_Pos    (8UL)                     /*!< RPM_FAN CONFIGURATION: POLARITY (Bit 8)                     */
#define RPM_FAN_CONFIGURATION_POLARITY_Msk    (0x100UL)                 /*!< RPM_FAN CONFIGURATION: POLARITY (Bitfield-Mask: 0x01)       */
#define RPM_FAN_CONFIGURATION_ERR_RNG_Pos     (9UL)                     /*!< RPM_FAN CONFIGURATION: ERR_RNG (Bit 9)                      */
#define RPM_FAN_CONFIGURATION_ERR_RNG_Msk     (0x600UL)                 /*!< RPM_FAN CONFIGURATION: ERR_RNG (Bitfield-Mask: 0x03)        */
#define RPM_FAN_CONFIGURATION_DER_OPT_Pos     (11UL)                    /*!< RPM_FAN CONFIGURATION: DER_OPT (Bit 11)                     */
#define RPM_FAN_CONFIGURATION_DER_OPT_Msk     (0x1800UL)                /*!< RPM_FAN CONFIGURATION: DER_OPT (Bitfield-Mask: 0x03)        */
#define RPM_FAN_CONFIGURATION_DIS_GLITCH_Pos  (13UL)                    /*!< RPM_FAN CONFIGURATION: DIS_GLITCH (Bit 13)                  */
#define RPM_FAN_CONFIGURATION_DIS_GLITCH_Msk  (0x2000UL)                /*!< RPM_FAN CONFIGURATION: DIS_GLITCH (Bitfield-Mask: 0x01)     */
#define RPM_FAN_CONFIGURATION_EN_RRC_Pos      (14UL)                    /*!< RPM_FAN CONFIGURATION: EN_RRC (Bit 14)                      */
#define RPM_FAN_CONFIGURATION_EN_RRC_Msk      (0x4000UL)                /*!< RPM_FAN CONFIGURATION: EN_RRC (Bitfield-Mask: 0x01)         */

/* --------------------------------  RPM_FAN_GAIN  -------------------------------- */
#define RPM_FAN_GAIN_GAINP_Pos                (0UL)                     /*!< RPM_FAN GAIN: GAINP (Bit 0)                                 */
#define RPM_FAN_GAIN_GAINP_Msk                (0x3UL)                   /*!< RPM_FAN GAIN: GAINP (Bitfield-Mask: 0x03)                   */
#define RPM_FAN_GAIN_GAINI_Pos                (2UL)                     /*!< RPM_FAN GAIN: GAINI (Bit 2)                                 */
#define RPM_FAN_GAIN_GAINI_Msk                (0xcUL)                   /*!< RPM_FAN GAIN: GAINI (Bitfield-Mask: 0x03)                   */
#define RPM_FAN_GAIN_GAIND_Pos                (4UL)                     /*!< RPM_FAN GAIN: GAIND (Bit 4)                                 */
#define RPM_FAN_GAIN_GAIND_Msk                (0x30UL)                  /*!< RPM_FAN GAIN: GAIND (Bitfield-Mask: 0x03)                   */

/* ------------------------  RPM_FAN_SPIN_UP_CONFIGURATION  ----------------------- */
#define RPM_FAN_SPIN_UP_CONFIGURATION_SPINUP_TIME_Pos (0UL)             /*!< RPM_FAN SPIN_UP_CONFIGURATION: SPINUP_TIME (Bit 0)          */
#define RPM_FAN_SPIN_UP_CONFIGURATION_SPINUP_TIME_Msk (0x3UL)           /*!< RPM_FAN SPIN_UP_CONFIGURATION: SPINUP_TIME (Bitfield-Mask: 0x03) */
#define RPM_FAN_SPIN_UP_CONFIGURATION_SPIN_LVL_Pos (2UL)                /*!< RPM_FAN SPIN_UP_CONFIGURATION: SPIN_LVL (Bit 2)             */
#define RPM_FAN_SPIN_UP_CONFIGURATION_SPIN_LVL_Msk (0x1cUL)             /*!< RPM_FAN SPIN_UP_CONFIGURATION: SPIN_LVL (Bitfield-Mask: 0x07) */
#define RPM_FAN_SPIN_UP_CONFIGURATION_NOKICK_Pos (5UL)                  /*!< RPM_FAN SPIN_UP_CONFIGURATION: NOKICK (Bit 5)               */
#define RPM_FAN_SPIN_UP_CONFIGURATION_NOKICK_Msk (0x20UL)               /*!< RPM_FAN SPIN_UP_CONFIGURATION: NOKICK (Bitfield-Mask: 0x01) */
#define RPM_FAN_SPIN_UP_CONFIGURATION_DRIVE_FAIL_CNT_Pos (6UL)          /*!< RPM_FAN SPIN_UP_CONFIGURATION: DRIVE_FAIL_CNT (Bit 6)       */
#define RPM_FAN_SPIN_UP_CONFIGURATION_DRIVE_FAIL_CNT_Msk (0xc0UL)       /*!< RPM_FAN SPIN_UP_CONFIGURATION: DRIVE_FAIL_CNT (Bitfield-Mask: 0x03) */

/* -------------------------------  RPM_FAN_STATUS  ------------------------------- */
#define RPM_FAN_STATUS_FAN_STALL_Pos          (0UL)                     /*!< RPM_FAN STATUS: FAN_STALL (Bit 0)                           */
#define RPM_FAN_STATUS_FAN_STALL_Msk          (0x1UL)                   /*!< RPM_FAN STATUS: FAN_STALL (Bitfield-Mask: 0x01)             */
#define RPM_FAN_STATUS_FAN_SPIN_Pos           (1UL)                     /*!< RPM_FAN STATUS: FAN_SPIN (Bit 1)                            */
#define RPM_FAN_STATUS_FAN_SPIN_Msk           (0x2UL)                   /*!< RPM_FAN STATUS: FAN_SPIN (Bitfield-Mask: 0x01)              */
#define RPM_FAN_STATUS_DRIVE_FAIL_Pos         (5UL)                     /*!< RPM_FAN STATUS: DRIVE_FAIL (Bit 5)                          */
#define RPM_FAN_STATUS_DRIVE_FAIL_Msk         (0x20UL)                  /*!< RPM_FAN STATUS: DRIVE_FAIL (Bitfield-Mask: 0x01)            */


/* ================================================================================ */
/* ================         struct 'SPI_0' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  SPI_0_CONTROL  ------------------------------- */
#define SPI_0_CONTROL_LSBF_Pos                (0UL)                     /*!< SPI_0 CONTROL: LSBF (Bit 0)                                 */
#define SPI_0_CONTROL_LSBF_Msk                (0x1UL)                   /*!< SPI_0 CONTROL: LSBF (Bitfield-Mask: 0x01)                   */
#define SPI_0_CONTROL_BIOEN_Pos               (1UL)                     /*!< SPI_0 CONTROL: BIOEN (Bit 1)                                */
#define SPI_0_CONTROL_BIOEN_Msk               (0x2UL)                   /*!< SPI_0 CONTROL: BIOEN (Bitfield-Mask: 0x01)                  */
#define SPI_0_CONTROL_SPDIN_SELECT_Pos        (2UL)                     /*!< SPI_0 CONTROL: SPDIN_SELECT (Bit 2)                         */
#define SPI_0_CONTROL_SPDIN_SELECT_Msk        (0xcUL)                   /*!< SPI_0 CONTROL: SPDIN_SELECT (Bitfield-Mask: 0x03)           */
#define SPI_0_CONTROL_SOFT_RESET_Pos          (4UL)                     /*!< SPI_0 CONTROL: SOFT_RESET (Bit 4)                           */
#define SPI_0_CONTROL_SOFT_RESET_Msk          (0x10UL)                  /*!< SPI_0 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)             */
#define SPI_0_CONTROL_AUTO_READ_Pos           (5UL)                     /*!< SPI_0 CONTROL: AUTO_READ (Bit 5)                            */
#define SPI_0_CONTROL_AUTO_READ_Msk           (0x20UL)                  /*!< SPI_0 CONTROL: AUTO_READ (Bitfield-Mask: 0x01)              */
#define SPI_0_CONTROL_CE_Pos                  (6UL)                     /*!< SPI_0 CONTROL: CE (Bit 6)                                   */
#define SPI_0_CONTROL_CE_Msk                  (0x40UL)                  /*!< SPI_0 CONTROL: CE (Bitfield-Mask: 0x01)                     */

/* --------------------------------  SPI_0_STATUS  -------------------------------- */
#define SPI_0_STATUS_TXBE_Pos                 (0UL)                     /*!< SPI_0 STATUS: TXBE (Bit 0)                                  */
#define SPI_0_STATUS_TXBE_Msk                 (0x1UL)                   /*!< SPI_0 STATUS: TXBE (Bitfield-Mask: 0x01)                    */
#define SPI_0_STATUS_RXBF_Pos                 (1UL)                     /*!< SPI_0 STATUS: RXBF (Bit 1)                                  */
#define SPI_0_STATUS_RXBF_Msk                 (0x2UL)                   /*!< SPI_0 STATUS: RXBF (Bitfield-Mask: 0x01)                    */
#define SPI_0_STATUS_ACTIVE_Pos               (2UL)                     /*!< SPI_0 STATUS: ACTIVE (Bit 2)                                */
#define SPI_0_STATUS_ACTIVE_Msk               (0x4UL)                   /*!< SPI_0 STATUS: ACTIVE (Bitfield-Mask: 0x01)                  */

/* -----------------------------  SPI_0_CLOCK_Control  ---------------------------- */
#define SPI_0_CLOCK_Control_TCLKPH_Pos        (0UL)                     /*!< SPI_0 CLOCK_Control: TCLKPH (Bit 0)                         */
#define SPI_0_CLOCK_Control_TCLKPH_Msk        (0x1UL)                   /*!< SPI_0 CLOCK_Control: TCLKPH (Bitfield-Mask: 0x01)           */
#define SPI_0_CLOCK_Control_RCLKPH_Pos        (1UL)                     /*!< SPI_0 CLOCK_Control: RCLKPH (Bit 1)                         */
#define SPI_0_CLOCK_Control_RCLKPH_Msk        (0x2UL)                   /*!< SPI_0 CLOCK_Control: RCLKPH (Bitfield-Mask: 0x01)           */
#define SPI_0_CLOCK_Control_CLKPOL_Pos        (2UL)                     /*!< SPI_0 CLOCK_Control: CLKPOL (Bit 2)                         */
#define SPI_0_CLOCK_Control_CLKPOL_Msk        (0x4UL)                   /*!< SPI_0 CLOCK_Control: CLKPOL (Bitfield-Mask: 0x01)           */
#define SPI_0_CLOCK_Control_CLKSRC_Pos        (4UL)                     /*!< SPI_0 CLOCK_Control: CLKSRC (Bit 4)                         */
#define SPI_0_CLOCK_Control_CLKSRC_Msk        (0x10UL)                  /*!< SPI_0 CLOCK_Control: CLKSRC (Bitfield-Mask: 0x01)           */


/* ================================================================================ */
/* ================         struct 'SPI_1' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  SPI_1_CONTROL  ------------------------------- */
#define SPI_1_CONTROL_LSBF_Pos                (0UL)                     /*!< SPI_1 CONTROL: LSBF (Bit 0)                                 */
#define SPI_1_CONTROL_LSBF_Msk                (0x1UL)                   /*!< SPI_1 CONTROL: LSBF (Bitfield-Mask: 0x01)                   */
#define SPI_1_CONTROL_BIOEN_Pos               (1UL)                     /*!< SPI_1 CONTROL: BIOEN (Bit 1)                                */
#define SPI_1_CONTROL_BIOEN_Msk               (0x2UL)                   /*!< SPI_1 CONTROL: BIOEN (Bitfield-Mask: 0x01)                  */
#define SPI_1_CONTROL_SPDIN_SELECT_Pos        (2UL)                     /*!< SPI_1 CONTROL: SPDIN_SELECT (Bit 2)                         */
#define SPI_1_CONTROL_SPDIN_SELECT_Msk        (0xcUL)                   /*!< SPI_1 CONTROL: SPDIN_SELECT (Bitfield-Mask: 0x03)           */
#define SPI_1_CONTROL_SOFT_RESET_Pos          (4UL)                     /*!< SPI_1 CONTROL: SOFT_RESET (Bit 4)                           */
#define SPI_1_CONTROL_SOFT_RESET_Msk          (0x10UL)                  /*!< SPI_1 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)             */
#define SPI_1_CONTROL_AUTO_READ_Pos           (5UL)                     /*!< SPI_1 CONTROL: AUTO_READ (Bit 5)                            */
#define SPI_1_CONTROL_AUTO_READ_Msk           (0x20UL)                  /*!< SPI_1 CONTROL: AUTO_READ (Bitfield-Mask: 0x01)              */
#define SPI_1_CONTROL_CE_Pos                  (6UL)                     /*!< SPI_1 CONTROL: CE (Bit 6)                                   */
#define SPI_1_CONTROL_CE_Msk                  (0x40UL)                  /*!< SPI_1 CONTROL: CE (Bitfield-Mask: 0x01)                     */

/* --------------------------------  SPI_1_STATUS  -------------------------------- */
#define SPI_1_STATUS_TXBE_Pos                 (0UL)                     /*!< SPI_1 STATUS: TXBE (Bit 0)                                  */
#define SPI_1_STATUS_TXBE_Msk                 (0x1UL)                   /*!< SPI_1 STATUS: TXBE (Bitfield-Mask: 0x01)                    */
#define SPI_1_STATUS_RXBF_Pos                 (1UL)                     /*!< SPI_1 STATUS: RXBF (Bit 1)                                  */
#define SPI_1_STATUS_RXBF_Msk                 (0x2UL)                   /*!< SPI_1 STATUS: RXBF (Bitfield-Mask: 0x01)                    */
#define SPI_1_STATUS_ACTIVE_Pos               (2UL)                     /*!< SPI_1 STATUS: ACTIVE (Bit 2)                                */
#define SPI_1_STATUS_ACTIVE_Msk               (0x4UL)                   /*!< SPI_1 STATUS: ACTIVE (Bitfield-Mask: 0x01)                  */

/* -----------------------------  SPI_1_CLOCK_Control  ---------------------------- */
#define SPI_1_CLOCK_Control_TCLKPH_Pos        (0UL)                     /*!< SPI_1 CLOCK_Control: TCLKPH (Bit 0)                         */
#define SPI_1_CLOCK_Control_TCLKPH_Msk        (0x1UL)                   /*!< SPI_1 CLOCK_Control: TCLKPH (Bitfield-Mask: 0x01)           */
#define SPI_1_CLOCK_Control_RCLKPH_Pos        (1UL)                     /*!< SPI_1 CLOCK_Control: RCLKPH (Bit 1)                         */
#define SPI_1_CLOCK_Control_RCLKPH_Msk        (0x2UL)                   /*!< SPI_1 CLOCK_Control: RCLKPH (Bitfield-Mask: 0x01)           */
#define SPI_1_CLOCK_Control_CLKPOL_Pos        (2UL)                     /*!< SPI_1 CLOCK_Control: CLKPOL (Bit 2)                         */
#define SPI_1_CLOCK_Control_CLKPOL_Msk        (0x4UL)                   /*!< SPI_1 CLOCK_Control: CLKPOL (Bitfield-Mask: 0x01)           */
#define SPI_1_CLOCK_Control_CLKSRC_Pos        (4UL)                     /*!< SPI_1 CLOCK_Control: CLKSRC (Bit 4)                         */
#define SPI_1_CLOCK_Control_CLKSRC_Msk        (0x10UL)                  /*!< SPI_1 CLOCK_Control: CLKSRC (Bitfield-Mask: 0x01)           */


/* ================================================================================ */
/* ================         struct 'LED_0' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  LED_0_CONFIG  -------------------------------- */
#define LED_0_CONFIG_CONTROL_Pos              (0UL)                     /*!< LED_0 CONFIG: CONTROL (Bit 0)                               */
#define LED_0_CONFIG_CONTROL_Msk              (0x3UL)                   /*!< LED_0 CONFIG: CONTROL (Bitfield-Mask: 0x03)                 */
#define LED_0_CONFIG_CLOCK_SOURCE_Pos         (2UL)                     /*!< LED_0 CONFIG: CLOCK_SOURCE (Bit 2)                          */
#define LED_0_CONFIG_CLOCK_SOURCE_Msk         (0x4UL)                   /*!< LED_0 CONFIG: CLOCK_SOURCE (Bitfield-Mask: 0x01)            */
#define LED_0_CONFIG_SYNCHRONIZE_Pos          (3UL)                     /*!< LED_0 CONFIG: SYNCHRONIZE (Bit 3)                           */
#define LED_0_CONFIG_SYNCHRONIZE_Msk          (0x8UL)                   /*!< LED_0 CONFIG: SYNCHRONIZE (Bitfield-Mask: 0x01)             */
#define LED_0_CONFIG_PWM_SIZE_Pos             (4UL)                     /*!< LED_0 CONFIG: PWM_SIZE (Bit 4)                              */
#define LED_0_CONFIG_PWM_SIZE_Msk             (0x30UL)                  /*!< LED_0 CONFIG: PWM_SIZE (Bitfield-Mask: 0x03)                */
#define LED_0_CONFIG_ENABLE_UPDATE_Pos        (6UL)                     /*!< LED_0 CONFIG: ENABLE_UPDATE (Bit 6)                         */
#define LED_0_CONFIG_ENABLE_UPDATE_Msk        (0x40UL)                  /*!< LED_0 CONFIG: ENABLE_UPDATE (Bitfield-Mask: 0x01)           */
#define LED_0_CONFIG_RESET_Pos                (7UL)                     /*!< LED_0 CONFIG: RESET (Bit 7)                                 */
#define LED_0_CONFIG_RESET_Msk                (0x80UL)                  /*!< LED_0 CONFIG: RESET (Bitfield-Mask: 0x01)                   */
#define LED_0_CONFIG_WDT_RELOAD_Pos           (8UL)                     /*!< LED_0 CONFIG: WDT_RELOAD (Bit 8)                            */
#define LED_0_CONFIG_WDT_RELOAD_Msk           (0xff00UL)                /*!< LED_0 CONFIG: WDT_RELOAD (Bitfield-Mask: 0xff)              */
#define LED_0_CONFIG_SYMMETRY_Pos             (16UL)                    /*!< LED_0 CONFIG: SYMMETRY (Bit 16)                             */
#define LED_0_CONFIG_SYMMETRY_Msk             (0x10000UL)               /*!< LED_0 CONFIG: SYMMETRY (Bitfield-Mask: 0x01)                */

/* --------------------------------  LED_0_LIMITS  -------------------------------- */
#define LED_0_LIMITS_MINIMUM_Pos              (0UL)                     /*!< LED_0 LIMITS: MINIMUM (Bit 0)                               */
#define LED_0_LIMITS_MINIMUM_Msk              (0xffUL)                  /*!< LED_0 LIMITS: MINIMUM (Bitfield-Mask: 0xff)                 */
#define LED_0_LIMITS_MAXIMUM_Pos              (8UL)                     /*!< LED_0 LIMITS: MAXIMUM (Bit 8)                               */
#define LED_0_LIMITS_MAXIMUM_Msk              (0xff00UL)                /*!< LED_0 LIMITS: MAXIMUM (Bitfield-Mask: 0xff)                 */

/* ---------------------------------  LED_0_DELAY  -------------------------------- */
#define LED_0_DELAY_LOW_Pos                   (0UL)                     /*!< LED_0 DELAY: LOW (Bit 0)                                    */
#define LED_0_DELAY_LOW_Msk                   (0xfffUL)                 /*!< LED_0 DELAY: LOW (Bitfield-Mask: 0xfff)                     */
#define LED_0_DELAY_HIGH_Pos                  (12UL)                    /*!< LED_0 DELAY: HIGH (Bit 12)                                  */
#define LED_0_DELAY_HIGH_Msk                  (0xfff000UL)              /*!< LED_0 DELAY: HIGH (Bitfield-Mask: 0xfff)                    */

/* ----------------------------  LED_0_UPDATE_STEPSIZE  --------------------------- */
#define LED_0_UPDATE_STEPSIZE_STEP0_Pos       (0UL)                     /*!< LED_0 UPDATE_STEPSIZE: STEP0 (Bit 0)                        */
#define LED_0_UPDATE_STEPSIZE_STEP0_Msk       (0xfUL)                   /*!< LED_0 UPDATE_STEPSIZE: STEP0 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP1_Pos       (4UL)                     /*!< LED_0 UPDATE_STEPSIZE: STEP1 (Bit 4)                        */
#define LED_0_UPDATE_STEPSIZE_STEP1_Msk       (0xf0UL)                  /*!< LED_0 UPDATE_STEPSIZE: STEP1 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP2_Pos       (8UL)                     /*!< LED_0 UPDATE_STEPSIZE: STEP2 (Bit 8)                        */
#define LED_0_UPDATE_STEPSIZE_STEP2_Msk       (0xf00UL)                 /*!< LED_0 UPDATE_STEPSIZE: STEP2 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP3_Pos       (12UL)                    /*!< LED_0 UPDATE_STEPSIZE: STEP3 (Bit 12)                       */
#define LED_0_UPDATE_STEPSIZE_STEP3_Msk       (0xf000UL)                /*!< LED_0 UPDATE_STEPSIZE: STEP3 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP4_Pos       (16UL)                    /*!< LED_0 UPDATE_STEPSIZE: STEP4 (Bit 16)                       */
#define LED_0_UPDATE_STEPSIZE_STEP4_Msk       (0xf0000UL)               /*!< LED_0 UPDATE_STEPSIZE: STEP4 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP5_Pos       (20UL)                    /*!< LED_0 UPDATE_STEPSIZE: STEP5 (Bit 20)                       */
#define LED_0_UPDATE_STEPSIZE_STEP5_Msk       (0xf00000UL)              /*!< LED_0 UPDATE_STEPSIZE: STEP5 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP6_Pos       (24UL)                    /*!< LED_0 UPDATE_STEPSIZE: STEP6 (Bit 24)                       */
#define LED_0_UPDATE_STEPSIZE_STEP6_Msk       (0xf000000UL)             /*!< LED_0 UPDATE_STEPSIZE: STEP6 (Bitfield-Mask: 0x0f)          */
#define LED_0_UPDATE_STEPSIZE_STEP7_Pos       (28UL)                    /*!< LED_0 UPDATE_STEPSIZE: STEP7 (Bit 28)                       */
#define LED_0_UPDATE_STEPSIZE_STEP7_Msk       (0xf0000000UL)            /*!< LED_0 UPDATE_STEPSIZE: STEP7 (Bitfield-Mask: 0x0f)          */

/* ----------------------------  LED_0_UPDATE_INTERVAL  --------------------------- */
#define LED_0_UPDATE_INTERVAL_INTERVAL0_Pos   (0UL)                     /*!< LED_0 UPDATE_INTERVAL: INTERVAL0 (Bit 0)                    */
#define LED_0_UPDATE_INTERVAL_INTERVAL0_Msk   (0xfUL)                   /*!< LED_0 UPDATE_INTERVAL: INTERVAL0 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL1_Pos   (4UL)                     /*!< LED_0 UPDATE_INTERVAL: INTERVAL1 (Bit 4)                    */
#define LED_0_UPDATE_INTERVAL_INTERVAL1_Msk   (0xf0UL)                  /*!< LED_0 UPDATE_INTERVAL: INTERVAL1 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL2_Pos   (8UL)                     /*!< LED_0 UPDATE_INTERVAL: INTERVAL2 (Bit 8)                    */
#define LED_0_UPDATE_INTERVAL_INTERVAL2_Msk   (0xf00UL)                 /*!< LED_0 UPDATE_INTERVAL: INTERVAL2 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL3_Pos   (12UL)                    /*!< LED_0 UPDATE_INTERVAL: INTERVAL3 (Bit 12)                   */
#define LED_0_UPDATE_INTERVAL_INTERVAL3_Msk   (0xf000UL)                /*!< LED_0 UPDATE_INTERVAL: INTERVAL3 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL4_Pos   (16UL)                    /*!< LED_0 UPDATE_INTERVAL: INTERVAL4 (Bit 16)                   */
#define LED_0_UPDATE_INTERVAL_INTERVAL4_Msk   (0xf0000UL)               /*!< LED_0 UPDATE_INTERVAL: INTERVAL4 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL5_Pos   (20UL)                    /*!< LED_0 UPDATE_INTERVAL: INTERVAL5 (Bit 20)                   */
#define LED_0_UPDATE_INTERVAL_INTERVAL5_Msk   (0xf00000UL)              /*!< LED_0 UPDATE_INTERVAL: INTERVAL5 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL6_Pos   (24UL)                    /*!< LED_0 UPDATE_INTERVAL: INTERVAL6 (Bit 24)                   */
#define LED_0_UPDATE_INTERVAL_INTERVAL6_Msk   (0xf000000UL)             /*!< LED_0 UPDATE_INTERVAL: INTERVAL6 (Bitfield-Mask: 0x0f)      */
#define LED_0_UPDATE_INTERVAL_INTERVAL7_Pos   (28UL)                    /*!< LED_0 UPDATE_INTERVAL: INTERVAL7 (Bit 28)                   */
#define LED_0_UPDATE_INTERVAL_INTERVAL7_Msk   (0xf0000000UL)            /*!< LED_0 UPDATE_INTERVAL: INTERVAL7 (Bitfield-Mask: 0x0f)      */


/* ================================================================================ */
/* ================         struct 'LED_1' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  LED_1_CONFIG  -------------------------------- */
#define LED_1_CONFIG_CONTROL_Pos              (0UL)                     /*!< LED_1 CONFIG: CONTROL (Bit 0)                               */
#define LED_1_CONFIG_CONTROL_Msk              (0x3UL)                   /*!< LED_1 CONFIG: CONTROL (Bitfield-Mask: 0x03)                 */
#define LED_1_CONFIG_CLOCK_SOURCE_Pos         (2UL)                     /*!< LED_1 CONFIG: CLOCK_SOURCE (Bit 2)                          */
#define LED_1_CONFIG_CLOCK_SOURCE_Msk         (0x4UL)                   /*!< LED_1 CONFIG: CLOCK_SOURCE (Bitfield-Mask: 0x01)            */
#define LED_1_CONFIG_SYNCHRONIZE_Pos          (3UL)                     /*!< LED_1 CONFIG: SYNCHRONIZE (Bit 3)                           */
#define LED_1_CONFIG_SYNCHRONIZE_Msk          (0x8UL)                   /*!< LED_1 CONFIG: SYNCHRONIZE (Bitfield-Mask: 0x01)             */
#define LED_1_CONFIG_PWM_SIZE_Pos             (4UL)                     /*!< LED_1 CONFIG: PWM_SIZE (Bit 4)                              */
#define LED_1_CONFIG_PWM_SIZE_Msk             (0x30UL)                  /*!< LED_1 CONFIG: PWM_SIZE (Bitfield-Mask: 0x03)                */
#define LED_1_CONFIG_ENABLE_UPDATE_Pos        (6UL)                     /*!< LED_1 CONFIG: ENABLE_UPDATE (Bit 6)                         */
#define LED_1_CONFIG_ENABLE_UPDATE_Msk        (0x40UL)                  /*!< LED_1 CONFIG: ENABLE_UPDATE (Bitfield-Mask: 0x01)           */
#define LED_1_CONFIG_RESET_Pos                (7UL)                     /*!< LED_1 CONFIG: RESET (Bit 7)                                 */
#define LED_1_CONFIG_RESET_Msk                (0x80UL)                  /*!< LED_1 CONFIG: RESET (Bitfield-Mask: 0x01)                   */
#define LED_1_CONFIG_WDT_RELOAD_Pos           (8UL)                     /*!< LED_1 CONFIG: WDT_RELOAD (Bit 8)                            */
#define LED_1_CONFIG_WDT_RELOAD_Msk           (0xff00UL)                /*!< LED_1 CONFIG: WDT_RELOAD (Bitfield-Mask: 0xff)              */
#define LED_1_CONFIG_SYMMETRY_Pos             (16UL)                    /*!< LED_1 CONFIG: SYMMETRY (Bit 16)                             */
#define LED_1_CONFIG_SYMMETRY_Msk             (0x10000UL)               /*!< LED_1 CONFIG: SYMMETRY (Bitfield-Mask: 0x01)                */

/* --------------------------------  LED_1_LIMITS  -------------------------------- */
#define LED_1_LIMITS_MINIMUM_Pos              (0UL)                     /*!< LED_1 LIMITS: MINIMUM (Bit 0)                               */
#define LED_1_LIMITS_MINIMUM_Msk              (0xffUL)                  /*!< LED_1 LIMITS: MINIMUM (Bitfield-Mask: 0xff)                 */
#define LED_1_LIMITS_MAXIMUM_Pos              (8UL)                     /*!< LED_1 LIMITS: MAXIMUM (Bit 8)                               */
#define LED_1_LIMITS_MAXIMUM_Msk              (0xff00UL)                /*!< LED_1 LIMITS: MAXIMUM (Bitfield-Mask: 0xff)                 */

/* ---------------------------------  LED_1_DELAY  -------------------------------- */
#define LED_1_DELAY_LOW_Pos                   (0UL)                     /*!< LED_1 DELAY: LOW (Bit 0)                                    */
#define LED_1_DELAY_LOW_Msk                   (0xfffUL)                 /*!< LED_1 DELAY: LOW (Bitfield-Mask: 0xfff)                     */
#define LED_1_DELAY_HIGH_Pos                  (12UL)                    /*!< LED_1 DELAY: HIGH (Bit 12)                                  */
#define LED_1_DELAY_HIGH_Msk                  (0xfff000UL)              /*!< LED_1 DELAY: HIGH (Bitfield-Mask: 0xfff)                    */

/* ----------------------------  LED_1_UPDATE_STEPSIZE  --------------------------- */
#define LED_1_UPDATE_STEPSIZE_STEP0_Pos       (0UL)                     /*!< LED_1 UPDATE_STEPSIZE: STEP0 (Bit 0)                        */
#define LED_1_UPDATE_STEPSIZE_STEP0_Msk       (0xfUL)                   /*!< LED_1 UPDATE_STEPSIZE: STEP0 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP1_Pos       (4UL)                     /*!< LED_1 UPDATE_STEPSIZE: STEP1 (Bit 4)                        */
#define LED_1_UPDATE_STEPSIZE_STEP1_Msk       (0xf0UL)                  /*!< LED_1 UPDATE_STEPSIZE: STEP1 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP2_Pos       (8UL)                     /*!< LED_1 UPDATE_STEPSIZE: STEP2 (Bit 8)                        */
#define LED_1_UPDATE_STEPSIZE_STEP2_Msk       (0xf00UL)                 /*!< LED_1 UPDATE_STEPSIZE: STEP2 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP3_Pos       (12UL)                    /*!< LED_1 UPDATE_STEPSIZE: STEP3 (Bit 12)                       */
#define LED_1_UPDATE_STEPSIZE_STEP3_Msk       (0xf000UL)                /*!< LED_1 UPDATE_STEPSIZE: STEP3 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP4_Pos       (16UL)                    /*!< LED_1 UPDATE_STEPSIZE: STEP4 (Bit 16)                       */
#define LED_1_UPDATE_STEPSIZE_STEP4_Msk       (0xf0000UL)               /*!< LED_1 UPDATE_STEPSIZE: STEP4 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP5_Pos       (20UL)                    /*!< LED_1 UPDATE_STEPSIZE: STEP5 (Bit 20)                       */
#define LED_1_UPDATE_STEPSIZE_STEP5_Msk       (0xf00000UL)              /*!< LED_1 UPDATE_STEPSIZE: STEP5 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP6_Pos       (24UL)                    /*!< LED_1 UPDATE_STEPSIZE: STEP6 (Bit 24)                       */
#define LED_1_UPDATE_STEPSIZE_STEP6_Msk       (0xf000000UL)             /*!< LED_1 UPDATE_STEPSIZE: STEP6 (Bitfield-Mask: 0x0f)          */
#define LED_1_UPDATE_STEPSIZE_STEP7_Pos       (28UL)                    /*!< LED_1 UPDATE_STEPSIZE: STEP7 (Bit 28)                       */
#define LED_1_UPDATE_STEPSIZE_STEP7_Msk       (0xf0000000UL)            /*!< LED_1 UPDATE_STEPSIZE: STEP7 (Bitfield-Mask: 0x0f)          */

/* ----------------------------  LED_1_UPDATE_INTERVAL  --------------------------- */
#define LED_1_UPDATE_INTERVAL_INTERVAL0_Pos   (0UL)                     /*!< LED_1 UPDATE_INTERVAL: INTERVAL0 (Bit 0)                    */
#define LED_1_UPDATE_INTERVAL_INTERVAL0_Msk   (0xfUL)                   /*!< LED_1 UPDATE_INTERVAL: INTERVAL0 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL1_Pos   (4UL)                     /*!< LED_1 UPDATE_INTERVAL: INTERVAL1 (Bit 4)                    */
#define LED_1_UPDATE_INTERVAL_INTERVAL1_Msk   (0xf0UL)                  /*!< LED_1 UPDATE_INTERVAL: INTERVAL1 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL2_Pos   (8UL)                     /*!< LED_1 UPDATE_INTERVAL: INTERVAL2 (Bit 8)                    */
#define LED_1_UPDATE_INTERVAL_INTERVAL2_Msk   (0xf00UL)                 /*!< LED_1 UPDATE_INTERVAL: INTERVAL2 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL3_Pos   (12UL)                    /*!< LED_1 UPDATE_INTERVAL: INTERVAL3 (Bit 12)                   */
#define LED_1_UPDATE_INTERVAL_INTERVAL3_Msk   (0xf000UL)                /*!< LED_1 UPDATE_INTERVAL: INTERVAL3 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL4_Pos   (16UL)                    /*!< LED_1 UPDATE_INTERVAL: INTERVAL4 (Bit 16)                   */
#define LED_1_UPDATE_INTERVAL_INTERVAL4_Msk   (0xf0000UL)               /*!< LED_1 UPDATE_INTERVAL: INTERVAL4 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL5_Pos   (20UL)                    /*!< LED_1 UPDATE_INTERVAL: INTERVAL5 (Bit 20)                   */
#define LED_1_UPDATE_INTERVAL_INTERVAL5_Msk   (0xf00000UL)              /*!< LED_1 UPDATE_INTERVAL: INTERVAL5 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL6_Pos   (24UL)                    /*!< LED_1 UPDATE_INTERVAL: INTERVAL6 (Bit 24)                   */
#define LED_1_UPDATE_INTERVAL_INTERVAL6_Msk   (0xf000000UL)             /*!< LED_1 UPDATE_INTERVAL: INTERVAL6 (Bitfield-Mask: 0x0f)      */
#define LED_1_UPDATE_INTERVAL_INTERVAL7_Pos   (28UL)                    /*!< LED_1 UPDATE_INTERVAL: INTERVAL7 (Bit 28)                   */
#define LED_1_UPDATE_INTERVAL_INTERVAL7_Msk   (0xf0000000UL)            /*!< LED_1 UPDATE_INTERVAL: INTERVAL7 (Bitfield-Mask: 0x0f)      */


/* ================================================================================ */
/* ================         struct 'LED_2' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  LED_2_CONFIG  -------------------------------- */
#define LED_2_CONFIG_CONTROL_Pos              (0UL)                     /*!< LED_2 CONFIG: CONTROL (Bit 0)                               */
#define LED_2_CONFIG_CONTROL_Msk              (0x3UL)                   /*!< LED_2 CONFIG: CONTROL (Bitfield-Mask: 0x03)                 */
#define LED_2_CONFIG_CLOCK_SOURCE_Pos         (2UL)                     /*!< LED_2 CONFIG: CLOCK_SOURCE (Bit 2)                          */
#define LED_2_CONFIG_CLOCK_SOURCE_Msk         (0x4UL)                   /*!< LED_2 CONFIG: CLOCK_SOURCE (Bitfield-Mask: 0x01)            */
#define LED_2_CONFIG_SYNCHRONIZE_Pos          (3UL)                     /*!< LED_2 CONFIG: SYNCHRONIZE (Bit 3)                           */
#define LED_2_CONFIG_SYNCHRONIZE_Msk          (0x8UL)                   /*!< LED_2 CONFIG: SYNCHRONIZE (Bitfield-Mask: 0x01)             */
#define LED_2_CONFIG_PWM_SIZE_Pos             (4UL)                     /*!< LED_2 CONFIG: PWM_SIZE (Bit 4)                              */
#define LED_2_CONFIG_PWM_SIZE_Msk             (0x30UL)                  /*!< LED_2 CONFIG: PWM_SIZE (Bitfield-Mask: 0x03)                */
#define LED_2_CONFIG_ENABLE_UPDATE_Pos        (6UL)                     /*!< LED_2 CONFIG: ENABLE_UPDATE (Bit 6)                         */
#define LED_2_CONFIG_ENABLE_UPDATE_Msk        (0x40UL)                  /*!< LED_2 CONFIG: ENABLE_UPDATE (Bitfield-Mask: 0x01)           */
#define LED_2_CONFIG_RESET_Pos                (7UL)                     /*!< LED_2 CONFIG: RESET (Bit 7)                                 */
#define LED_2_CONFIG_RESET_Msk                (0x80UL)                  /*!< LED_2 CONFIG: RESET (Bitfield-Mask: 0x01)                   */
#define LED_2_CONFIG_WDT_RELOAD_Pos           (8UL)                     /*!< LED_2 CONFIG: WDT_RELOAD (Bit 8)                            */
#define LED_2_CONFIG_WDT_RELOAD_Msk           (0xff00UL)                /*!< LED_2 CONFIG: WDT_RELOAD (Bitfield-Mask: 0xff)              */
#define LED_2_CONFIG_SYMMETRY_Pos             (16UL)                    /*!< LED_2 CONFIG: SYMMETRY (Bit 16)                             */
#define LED_2_CONFIG_SYMMETRY_Msk             (0x10000UL)               /*!< LED_2 CONFIG: SYMMETRY (Bitfield-Mask: 0x01)                */

/* --------------------------------  LED_2_LIMITS  -------------------------------- */
#define LED_2_LIMITS_MINIMUM_Pos              (0UL)                     /*!< LED_2 LIMITS: MINIMUM (Bit 0)                               */
#define LED_2_LIMITS_MINIMUM_Msk              (0xffUL)                  /*!< LED_2 LIMITS: MINIMUM (Bitfield-Mask: 0xff)                 */
#define LED_2_LIMITS_MAXIMUM_Pos              (8UL)                     /*!< LED_2 LIMITS: MAXIMUM (Bit 8)                               */
#define LED_2_LIMITS_MAXIMUM_Msk              (0xff00UL)                /*!< LED_2 LIMITS: MAXIMUM (Bitfield-Mask: 0xff)                 */

/* ---------------------------------  LED_2_DELAY  -------------------------------- */
#define LED_2_DELAY_LOW_Pos                   (0UL)                     /*!< LED_2 DELAY: LOW (Bit 0)                                    */
#define LED_2_DELAY_LOW_Msk                   (0xfffUL)                 /*!< LED_2 DELAY: LOW (Bitfield-Mask: 0xfff)                     */
#define LED_2_DELAY_HIGH_Pos                  (12UL)                    /*!< LED_2 DELAY: HIGH (Bit 12)                                  */
#define LED_2_DELAY_HIGH_Msk                  (0xfff000UL)              /*!< LED_2 DELAY: HIGH (Bitfield-Mask: 0xfff)                    */

/* ----------------------------  LED_2_UPDATE_STEPSIZE  --------------------------- */
#define LED_2_UPDATE_STEPSIZE_STEP0_Pos       (0UL)                     /*!< LED_2 UPDATE_STEPSIZE: STEP0 (Bit 0)                        */
#define LED_2_UPDATE_STEPSIZE_STEP0_Msk       (0xfUL)                   /*!< LED_2 UPDATE_STEPSIZE: STEP0 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP1_Pos       (4UL)                     /*!< LED_2 UPDATE_STEPSIZE: STEP1 (Bit 4)                        */
#define LED_2_UPDATE_STEPSIZE_STEP1_Msk       (0xf0UL)                  /*!< LED_2 UPDATE_STEPSIZE: STEP1 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP2_Pos       (8UL)                     /*!< LED_2 UPDATE_STEPSIZE: STEP2 (Bit 8)                        */
#define LED_2_UPDATE_STEPSIZE_STEP2_Msk       (0xf00UL)                 /*!< LED_2 UPDATE_STEPSIZE: STEP2 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP3_Pos       (12UL)                    /*!< LED_2 UPDATE_STEPSIZE: STEP3 (Bit 12)                       */
#define LED_2_UPDATE_STEPSIZE_STEP3_Msk       (0xf000UL)                /*!< LED_2 UPDATE_STEPSIZE: STEP3 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP4_Pos       (16UL)                    /*!< LED_2 UPDATE_STEPSIZE: STEP4 (Bit 16)                       */
#define LED_2_UPDATE_STEPSIZE_STEP4_Msk       (0xf0000UL)               /*!< LED_2 UPDATE_STEPSIZE: STEP4 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP5_Pos       (20UL)                    /*!< LED_2 UPDATE_STEPSIZE: STEP5 (Bit 20)                       */
#define LED_2_UPDATE_STEPSIZE_STEP5_Msk       (0xf00000UL)              /*!< LED_2 UPDATE_STEPSIZE: STEP5 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP6_Pos       (24UL)                    /*!< LED_2 UPDATE_STEPSIZE: STEP6 (Bit 24)                       */
#define LED_2_UPDATE_STEPSIZE_STEP6_Msk       (0xf000000UL)             /*!< LED_2 UPDATE_STEPSIZE: STEP6 (Bitfield-Mask: 0x0f)          */
#define LED_2_UPDATE_STEPSIZE_STEP7_Pos       (28UL)                    /*!< LED_2 UPDATE_STEPSIZE: STEP7 (Bit 28)                       */
#define LED_2_UPDATE_STEPSIZE_STEP7_Msk       (0xf0000000UL)            /*!< LED_2 UPDATE_STEPSIZE: STEP7 (Bitfield-Mask: 0x0f)          */

/* ----------------------------  LED_2_UPDATE_INTERVAL  --------------------------- */
#define LED_2_UPDATE_INTERVAL_INTERVAL0_Pos   (0UL)                     /*!< LED_2 UPDATE_INTERVAL: INTERVAL0 (Bit 0)                    */
#define LED_2_UPDATE_INTERVAL_INTERVAL0_Msk   (0xfUL)                   /*!< LED_2 UPDATE_INTERVAL: INTERVAL0 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL1_Pos   (4UL)                     /*!< LED_2 UPDATE_INTERVAL: INTERVAL1 (Bit 4)                    */
#define LED_2_UPDATE_INTERVAL_INTERVAL1_Msk   (0xf0UL)                  /*!< LED_2 UPDATE_INTERVAL: INTERVAL1 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL2_Pos   (8UL)                     /*!< LED_2 UPDATE_INTERVAL: INTERVAL2 (Bit 8)                    */
#define LED_2_UPDATE_INTERVAL_INTERVAL2_Msk   (0xf00UL)                 /*!< LED_2 UPDATE_INTERVAL: INTERVAL2 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL3_Pos   (12UL)                    /*!< LED_2 UPDATE_INTERVAL: INTERVAL3 (Bit 12)                   */
#define LED_2_UPDATE_INTERVAL_INTERVAL3_Msk   (0xf000UL)                /*!< LED_2 UPDATE_INTERVAL: INTERVAL3 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL4_Pos   (16UL)                    /*!< LED_2 UPDATE_INTERVAL: INTERVAL4 (Bit 16)                   */
#define LED_2_UPDATE_INTERVAL_INTERVAL4_Msk   (0xf0000UL)               /*!< LED_2 UPDATE_INTERVAL: INTERVAL4 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL5_Pos   (20UL)                    /*!< LED_2 UPDATE_INTERVAL: INTERVAL5 (Bit 20)                   */
#define LED_2_UPDATE_INTERVAL_INTERVAL5_Msk   (0xf00000UL)              /*!< LED_2 UPDATE_INTERVAL: INTERVAL5 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL6_Pos   (24UL)                    /*!< LED_2 UPDATE_INTERVAL: INTERVAL6 (Bit 24)                   */
#define LED_2_UPDATE_INTERVAL_INTERVAL6_Msk   (0xf000000UL)             /*!< LED_2 UPDATE_INTERVAL: INTERVAL6 (Bitfield-Mask: 0x0f)      */
#define LED_2_UPDATE_INTERVAL_INTERVAL7_Pos   (28UL)                    /*!< LED_2 UPDATE_INTERVAL: INTERVAL7 (Bit 28)                   */
#define LED_2_UPDATE_INTERVAL_INTERVAL7_Msk   (0xf0000000UL)            /*!< LED_2 UPDATE_INTERVAL: INTERVAL7 (Bitfield-Mask: 0x0f)      */


/* ================================================================================ */
/* ================         struct 'LED_3' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  LED_3_CONFIG  -------------------------------- */
#define LED_3_CONFIG_CONTROL_Pos              (0UL)                     /*!< LED_3 CONFIG: CONTROL (Bit 0)                               */
#define LED_3_CONFIG_CONTROL_Msk              (0x3UL)                   /*!< LED_3 CONFIG: CONTROL (Bitfield-Mask: 0x03)                 */
#define LED_3_CONFIG_CLOCK_SOURCE_Pos         (2UL)                     /*!< LED_3 CONFIG: CLOCK_SOURCE (Bit 2)                          */
#define LED_3_CONFIG_CLOCK_SOURCE_Msk         (0x4UL)                   /*!< LED_3 CONFIG: CLOCK_SOURCE (Bitfield-Mask: 0x01)            */
#define LED_3_CONFIG_SYNCHRONIZE_Pos          (3UL)                     /*!< LED_3 CONFIG: SYNCHRONIZE (Bit 3)                           */
#define LED_3_CONFIG_SYNCHRONIZE_Msk          (0x8UL)                   /*!< LED_3 CONFIG: SYNCHRONIZE (Bitfield-Mask: 0x01)             */
#define LED_3_CONFIG_PWM_SIZE_Pos             (4UL)                     /*!< LED_3 CONFIG: PWM_SIZE (Bit 4)                              */
#define LED_3_CONFIG_PWM_SIZE_Msk             (0x30UL)                  /*!< LED_3 CONFIG: PWM_SIZE (Bitfield-Mask: 0x03)                */
#define LED_3_CONFIG_ENABLE_UPDATE_Pos        (6UL)                     /*!< LED_3 CONFIG: ENABLE_UPDATE (Bit 6)                         */
#define LED_3_CONFIG_ENABLE_UPDATE_Msk        (0x40UL)                  /*!< LED_3 CONFIG: ENABLE_UPDATE (Bitfield-Mask: 0x01)           */
#define LED_3_CONFIG_RESET_Pos                (7UL)                     /*!< LED_3 CONFIG: RESET (Bit 7)                                 */
#define LED_3_CONFIG_RESET_Msk                (0x80UL)                  /*!< LED_3 CONFIG: RESET (Bitfield-Mask: 0x01)                   */
#define LED_3_CONFIG_WDT_RELOAD_Pos           (8UL)                     /*!< LED_3 CONFIG: WDT_RELOAD (Bit 8)                            */
#define LED_3_CONFIG_WDT_RELOAD_Msk           (0xff00UL)                /*!< LED_3 CONFIG: WDT_RELOAD (Bitfield-Mask: 0xff)              */
#define LED_3_CONFIG_SYMMETRY_Pos             (16UL)                    /*!< LED_3 CONFIG: SYMMETRY (Bit 16)                             */
#define LED_3_CONFIG_SYMMETRY_Msk             (0x10000UL)               /*!< LED_3 CONFIG: SYMMETRY (Bitfield-Mask: 0x01)                */

/* --------------------------------  LED_3_LIMITS  -------------------------------- */
#define LED_3_LIMITS_MINIMUM_Pos              (0UL)                     /*!< LED_3 LIMITS: MINIMUM (Bit 0)                               */
#define LED_3_LIMITS_MINIMUM_Msk              (0xffUL)                  /*!< LED_3 LIMITS: MINIMUM (Bitfield-Mask: 0xff)                 */
#define LED_3_LIMITS_MAXIMUM_Pos              (8UL)                     /*!< LED_3 LIMITS: MAXIMUM (Bit 8)                               */
#define LED_3_LIMITS_MAXIMUM_Msk              (0xff00UL)                /*!< LED_3 LIMITS: MAXIMUM (Bitfield-Mask: 0xff)                 */

/* ---------------------------------  LED_3_DELAY  -------------------------------- */
#define LED_3_DELAY_LOW_Pos                   (0UL)                     /*!< LED_3 DELAY: LOW (Bit 0)                                    */
#define LED_3_DELAY_LOW_Msk                   (0xfffUL)                 /*!< LED_3 DELAY: LOW (Bitfield-Mask: 0xfff)                     */
#define LED_3_DELAY_HIGH_Pos                  (12UL)                    /*!< LED_3 DELAY: HIGH (Bit 12)                                  */
#define LED_3_DELAY_HIGH_Msk                  (0xfff000UL)              /*!< LED_3 DELAY: HIGH (Bitfield-Mask: 0xfff)                    */

/* ----------------------------  LED_3_UPDATE_STEPSIZE  --------------------------- */
#define LED_3_UPDATE_STEPSIZE_STEP0_Pos       (0UL)                     /*!< LED_3 UPDATE_STEPSIZE: STEP0 (Bit 0)                        */
#define LED_3_UPDATE_STEPSIZE_STEP0_Msk       (0xfUL)                   /*!< LED_3 UPDATE_STEPSIZE: STEP0 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP1_Pos       (4UL)                     /*!< LED_3 UPDATE_STEPSIZE: STEP1 (Bit 4)                        */
#define LED_3_UPDATE_STEPSIZE_STEP1_Msk       (0xf0UL)                  /*!< LED_3 UPDATE_STEPSIZE: STEP1 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP2_Pos       (8UL)                     /*!< LED_3 UPDATE_STEPSIZE: STEP2 (Bit 8)                        */
#define LED_3_UPDATE_STEPSIZE_STEP2_Msk       (0xf00UL)                 /*!< LED_3 UPDATE_STEPSIZE: STEP2 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP3_Pos       (12UL)                    /*!< LED_3 UPDATE_STEPSIZE: STEP3 (Bit 12)                       */
#define LED_3_UPDATE_STEPSIZE_STEP3_Msk       (0xf000UL)                /*!< LED_3 UPDATE_STEPSIZE: STEP3 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP4_Pos       (16UL)                    /*!< LED_3 UPDATE_STEPSIZE: STEP4 (Bit 16)                       */
#define LED_3_UPDATE_STEPSIZE_STEP4_Msk       (0xf0000UL)               /*!< LED_3 UPDATE_STEPSIZE: STEP4 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP5_Pos       (20UL)                    /*!< LED_3 UPDATE_STEPSIZE: STEP5 (Bit 20)                       */
#define LED_3_UPDATE_STEPSIZE_STEP5_Msk       (0xf00000UL)              /*!< LED_3 UPDATE_STEPSIZE: STEP5 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP6_Pos       (24UL)                    /*!< LED_3 UPDATE_STEPSIZE: STEP6 (Bit 24)                       */
#define LED_3_UPDATE_STEPSIZE_STEP6_Msk       (0xf000000UL)             /*!< LED_3 UPDATE_STEPSIZE: STEP6 (Bitfield-Mask: 0x0f)          */
#define LED_3_UPDATE_STEPSIZE_STEP7_Pos       (28UL)                    /*!< LED_3 UPDATE_STEPSIZE: STEP7 (Bit 28)                       */
#define LED_3_UPDATE_STEPSIZE_STEP7_Msk       (0xf0000000UL)            /*!< LED_3 UPDATE_STEPSIZE: STEP7 (Bitfield-Mask: 0x0f)          */

/* ----------------------------  LED_3_UPDATE_INTERVAL  --------------------------- */
#define LED_3_UPDATE_INTERVAL_INTERVAL0_Pos   (0UL)                     /*!< LED_3 UPDATE_INTERVAL: INTERVAL0 (Bit 0)                    */
#define LED_3_UPDATE_INTERVAL_INTERVAL0_Msk   (0xfUL)                   /*!< LED_3 UPDATE_INTERVAL: INTERVAL0 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL1_Pos   (4UL)                     /*!< LED_3 UPDATE_INTERVAL: INTERVAL1 (Bit 4)                    */
#define LED_3_UPDATE_INTERVAL_INTERVAL1_Msk   (0xf0UL)                  /*!< LED_3 UPDATE_INTERVAL: INTERVAL1 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL2_Pos   (8UL)                     /*!< LED_3 UPDATE_INTERVAL: INTERVAL2 (Bit 8)                    */
#define LED_3_UPDATE_INTERVAL_INTERVAL2_Msk   (0xf00UL)                 /*!< LED_3 UPDATE_INTERVAL: INTERVAL2 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL3_Pos   (12UL)                    /*!< LED_3 UPDATE_INTERVAL: INTERVAL3 (Bit 12)                   */
#define LED_3_UPDATE_INTERVAL_INTERVAL3_Msk   (0xf000UL)                /*!< LED_3 UPDATE_INTERVAL: INTERVAL3 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL4_Pos   (16UL)                    /*!< LED_3 UPDATE_INTERVAL: INTERVAL4 (Bit 16)                   */
#define LED_3_UPDATE_INTERVAL_INTERVAL4_Msk   (0xf0000UL)               /*!< LED_3 UPDATE_INTERVAL: INTERVAL4 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL5_Pos   (20UL)                    /*!< LED_3 UPDATE_INTERVAL: INTERVAL5 (Bit 20)                   */
#define LED_3_UPDATE_INTERVAL_INTERVAL5_Msk   (0xf00000UL)              /*!< LED_3 UPDATE_INTERVAL: INTERVAL5 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL6_Pos   (24UL)                    /*!< LED_3 UPDATE_INTERVAL: INTERVAL6 (Bit 24)                   */
#define LED_3_UPDATE_INTERVAL_INTERVAL6_Msk   (0xf000000UL)             /*!< LED_3 UPDATE_INTERVAL: INTERVAL6 (Bitfield-Mask: 0x0f)      */
#define LED_3_UPDATE_INTERVAL_INTERVAL7_Pos   (28UL)                    /*!< LED_3 UPDATE_INTERVAL: INTERVAL7 (Bit 28)                   */
#define LED_3_UPDATE_INTERVAL_INTERVAL7_Msk   (0xf0000000UL)            /*!< LED_3 UPDATE_INTERVAL: INTERVAL7 (Bitfield-Mask: 0x0f)      */


/* ================================================================================ */
/* ================         struct 'PS2_0' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PS2_0_CONTROL  ------------------------------- */
#define PS2_0_CONTROL_TR_Pos                  (0UL)                     /*!< PS2_0 CONTROL: TR (Bit 0)                                   */
#define PS2_0_CONTROL_TR_Msk                  (0x1UL)                   /*!< PS2_0 CONTROL: TR (Bitfield-Mask: 0x01)                     */
#define PS2_0_CONTROL_EN_Pos                  (1UL)                     /*!< PS2_0 CONTROL: EN (Bit 1)                                   */
#define PS2_0_CONTROL_EN_Msk                  (0x2UL)                   /*!< PS2_0 CONTROL: EN (Bitfield-Mask: 0x01)                     */
#define PS2_0_CONTROL_PARITY_Pos              (2UL)                     /*!< PS2_0 CONTROL: PARITY (Bit 2)                               */
#define PS2_0_CONTROL_PARITY_Msk              (0xcUL)                   /*!< PS2_0 CONTROL: PARITY (Bitfield-Mask: 0x03)                 */
#define PS2_0_CONTROL_STOP_Pos                (4UL)                     /*!< PS2_0 CONTROL: STOP (Bit 4)                                 */
#define PS2_0_CONTROL_STOP_Msk                (0x30UL)                  /*!< PS2_0 CONTROL: STOP (Bitfield-Mask: 0x03)                   */

/* --------------------------------  PS2_0_STATUS  -------------------------------- */
#define PS2_0_STATUS_RDATA_RDY_Pos            (0UL)                     /*!< PS2_0 STATUS: RDATA_RDY (Bit 0)                             */
#define PS2_0_STATUS_RDATA_RDY_Msk            (0x1UL)                   /*!< PS2_0 STATUS: RDATA_RDY (Bitfield-Mask: 0x01)               */
#define PS2_0_STATUS_REC_TIMEOUT_Pos          (1UL)                     /*!< PS2_0 STATUS: REC_TIMEOUT (Bit 1)                           */
#define PS2_0_STATUS_REC_TIMEOUT_Msk          (0x2UL)                   /*!< PS2_0 STATUS: REC_TIMEOUT (Bitfield-Mask: 0x01)             */
#define PS2_0_STATUS_PE_Pos                   (2UL)                     /*!< PS2_0 STATUS: PE (Bit 2)                                    */
#define PS2_0_STATUS_PE_Msk                   (0x4UL)                   /*!< PS2_0 STATUS: PE (Bitfield-Mask: 0x01)                      */
#define PS2_0_STATUS_FE_Pos                   (3UL)                     /*!< PS2_0 STATUS: FE (Bit 3)                                    */
#define PS2_0_STATUS_FE_Msk                   (0x8UL)                   /*!< PS2_0 STATUS: FE (Bitfield-Mask: 0x01)                      */
#define PS2_0_STATUS_XMIT_IDLE_Pos            (4UL)                     /*!< PS2_0 STATUS: XMIT_IDLE (Bit 4)                             */
#define PS2_0_STATUS_XMIT_IDLE_Msk            (0x10UL)                  /*!< PS2_0 STATUS: XMIT_IDLE (Bitfield-Mask: 0x01)               */
#define PS2_0_STATUS_XMIT_TIME_OUT_Pos        (5UL)                     /*!< PS2_0 STATUS: XMIT_TIME_OUT (Bit 5)                         */
#define PS2_0_STATUS_XMIT_TIME_OUT_Msk        (0x20UL)                  /*!< PS2_0 STATUS: XMIT_TIME_OUT (Bitfield-Mask: 0x01)           */
#define PS2_0_STATUS_RX_BUSY_Pos              (6UL)                     /*!< PS2_0 STATUS: RX_BUSY (Bit 6)                               */
#define PS2_0_STATUS_RX_BUSY_Msk              (0x40UL)                  /*!< PS2_0 STATUS: RX_BUSY (Bitfield-Mask: 0x01)                 */
#define PS2_0_STATUS_XMIT_START_TIMEOUT_Pos   (7UL)                     /*!< PS2_0 STATUS: XMIT_START_TIMEOUT (Bit 7)                    */
#define PS2_0_STATUS_XMIT_START_TIMEOUT_Msk   (0x80UL)                  /*!< PS2_0 STATUS: XMIT_START_TIMEOUT (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================         struct 'PS2_1' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PS2_1_CONTROL  ------------------------------- */
#define PS2_1_CONTROL_TR_Pos                  (0UL)                     /*!< PS2_1 CONTROL: TR (Bit 0)                                   */
#define PS2_1_CONTROL_TR_Msk                  (0x1UL)                   /*!< PS2_1 CONTROL: TR (Bitfield-Mask: 0x01)                     */
#define PS2_1_CONTROL_EN_Pos                  (1UL)                     /*!< PS2_1 CONTROL: EN (Bit 1)                                   */
#define PS2_1_CONTROL_EN_Msk                  (0x2UL)                   /*!< PS2_1 CONTROL: EN (Bitfield-Mask: 0x01)                     */
#define PS2_1_CONTROL_PARITY_Pos              (2UL)                     /*!< PS2_1 CONTROL: PARITY (Bit 2)                               */
#define PS2_1_CONTROL_PARITY_Msk              (0xcUL)                   /*!< PS2_1 CONTROL: PARITY (Bitfield-Mask: 0x03)                 */
#define PS2_1_CONTROL_STOP_Pos                (4UL)                     /*!< PS2_1 CONTROL: STOP (Bit 4)                                 */
#define PS2_1_CONTROL_STOP_Msk                (0x30UL)                  /*!< PS2_1 CONTROL: STOP (Bitfield-Mask: 0x03)                   */

/* --------------------------------  PS2_1_STATUS  -------------------------------- */
#define PS2_1_STATUS_RDATA_RDY_Pos            (0UL)                     /*!< PS2_1 STATUS: RDATA_RDY (Bit 0)                             */
#define PS2_1_STATUS_RDATA_RDY_Msk            (0x1UL)                   /*!< PS2_1 STATUS: RDATA_RDY (Bitfield-Mask: 0x01)               */
#define PS2_1_STATUS_REC_TIMEOUT_Pos          (1UL)                     /*!< PS2_1 STATUS: REC_TIMEOUT (Bit 1)                           */
#define PS2_1_STATUS_REC_TIMEOUT_Msk          (0x2UL)                   /*!< PS2_1 STATUS: REC_TIMEOUT (Bitfield-Mask: 0x01)             */
#define PS2_1_STATUS_PE_Pos                   (2UL)                     /*!< PS2_1 STATUS: PE (Bit 2)                                    */
#define PS2_1_STATUS_PE_Msk                   (0x4UL)                   /*!< PS2_1 STATUS: PE (Bitfield-Mask: 0x01)                      */
#define PS2_1_STATUS_FE_Pos                   (3UL)                     /*!< PS2_1 STATUS: FE (Bit 3)                                    */
#define PS2_1_STATUS_FE_Msk                   (0x8UL)                   /*!< PS2_1 STATUS: FE (Bitfield-Mask: 0x01)                      */
#define PS2_1_STATUS_XMIT_IDLE_Pos            (4UL)                     /*!< PS2_1 STATUS: XMIT_IDLE (Bit 4)                             */
#define PS2_1_STATUS_XMIT_IDLE_Msk            (0x10UL)                  /*!< PS2_1 STATUS: XMIT_IDLE (Bitfield-Mask: 0x01)               */
#define PS2_1_STATUS_XMIT_TIME_OUT_Pos        (5UL)                     /*!< PS2_1 STATUS: XMIT_TIME_OUT (Bit 5)                         */
#define PS2_1_STATUS_XMIT_TIME_OUT_Msk        (0x20UL)                  /*!< PS2_1 STATUS: XMIT_TIME_OUT (Bitfield-Mask: 0x01)           */
#define PS2_1_STATUS_RX_BUSY_Pos              (6UL)                     /*!< PS2_1 STATUS: RX_BUSY (Bit 6)                               */
#define PS2_1_STATUS_RX_BUSY_Msk              (0x40UL)                  /*!< PS2_1 STATUS: RX_BUSY (Bitfield-Mask: 0x01)                 */
#define PS2_1_STATUS_XMIT_START_TIMEOUT_Pos   (7UL)                     /*!< PS2_1 STATUS: XMIT_START_TIMEOUT (Bit 7)                    */
#define PS2_1_STATUS_XMIT_START_TIMEOUT_Msk   (0x80UL)                  /*!< PS2_1 STATUS: XMIT_START_TIMEOUT (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================         struct 'PS2_2' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PS2_2_CONTROL  ------------------------------- */
#define PS2_2_CONTROL_TR_Pos                  (0UL)                     /*!< PS2_2 CONTROL: TR (Bit 0)                                   */
#define PS2_2_CONTROL_TR_Msk                  (0x1UL)                   /*!< PS2_2 CONTROL: TR (Bitfield-Mask: 0x01)                     */
#define PS2_2_CONTROL_EN_Pos                  (1UL)                     /*!< PS2_2 CONTROL: EN (Bit 1)                                   */
#define PS2_2_CONTROL_EN_Msk                  (0x2UL)                   /*!< PS2_2 CONTROL: EN (Bitfield-Mask: 0x01)                     */
#define PS2_2_CONTROL_PARITY_Pos              (2UL)                     /*!< PS2_2 CONTROL: PARITY (Bit 2)                               */
#define PS2_2_CONTROL_PARITY_Msk              (0xcUL)                   /*!< PS2_2 CONTROL: PARITY (Bitfield-Mask: 0x03)                 */
#define PS2_2_CONTROL_STOP_Pos                (4UL)                     /*!< PS2_2 CONTROL: STOP (Bit 4)                                 */
#define PS2_2_CONTROL_STOP_Msk                (0x30UL)                  /*!< PS2_2 CONTROL: STOP (Bitfield-Mask: 0x03)                   */

/* --------------------------------  PS2_2_STATUS  -------------------------------- */
#define PS2_2_STATUS_RDATA_RDY_Pos            (0UL)                     /*!< PS2_2 STATUS: RDATA_RDY (Bit 0)                             */
#define PS2_2_STATUS_RDATA_RDY_Msk            (0x1UL)                   /*!< PS2_2 STATUS: RDATA_RDY (Bitfield-Mask: 0x01)               */
#define PS2_2_STATUS_REC_TIMEOUT_Pos          (1UL)                     /*!< PS2_2 STATUS: REC_TIMEOUT (Bit 1)                           */
#define PS2_2_STATUS_REC_TIMEOUT_Msk          (0x2UL)                   /*!< PS2_2 STATUS: REC_TIMEOUT (Bitfield-Mask: 0x01)             */
#define PS2_2_STATUS_PE_Pos                   (2UL)                     /*!< PS2_2 STATUS: PE (Bit 2)                                    */
#define PS2_2_STATUS_PE_Msk                   (0x4UL)                   /*!< PS2_2 STATUS: PE (Bitfield-Mask: 0x01)                      */
#define PS2_2_STATUS_FE_Pos                   (3UL)                     /*!< PS2_2 STATUS: FE (Bit 3)                                    */
#define PS2_2_STATUS_FE_Msk                   (0x8UL)                   /*!< PS2_2 STATUS: FE (Bitfield-Mask: 0x01)                      */
#define PS2_2_STATUS_XMIT_IDLE_Pos            (4UL)                     /*!< PS2_2 STATUS: XMIT_IDLE (Bit 4)                             */
#define PS2_2_STATUS_XMIT_IDLE_Msk            (0x10UL)                  /*!< PS2_2 STATUS: XMIT_IDLE (Bitfield-Mask: 0x01)               */
#define PS2_2_STATUS_XMIT_TIME_OUT_Pos        (5UL)                     /*!< PS2_2 STATUS: XMIT_TIME_OUT (Bit 5)                         */
#define PS2_2_STATUS_XMIT_TIME_OUT_Msk        (0x20UL)                  /*!< PS2_2 STATUS: XMIT_TIME_OUT (Bitfield-Mask: 0x01)           */
#define PS2_2_STATUS_RX_BUSY_Pos              (6UL)                     /*!< PS2_2 STATUS: RX_BUSY (Bit 6)                               */
#define PS2_2_STATUS_RX_BUSY_Msk              (0x40UL)                  /*!< PS2_2 STATUS: RX_BUSY (Bitfield-Mask: 0x01)                 */
#define PS2_2_STATUS_XMIT_START_TIMEOUT_Pos   (7UL)                     /*!< PS2_2 STATUS: XMIT_START_TIMEOUT (Bit 7)                    */
#define PS2_2_STATUS_XMIT_START_TIMEOUT_Msk   (0x80UL)                  /*!< PS2_2 STATUS: XMIT_START_TIMEOUT (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================         struct 'PS2_3' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  PS2_3_CONTROL  ------------------------------- */
#define PS2_3_CONTROL_TR_Pos                  (0UL)                     /*!< PS2_3 CONTROL: TR (Bit 0)                                   */
#define PS2_3_CONTROL_TR_Msk                  (0x1UL)                   /*!< PS2_3 CONTROL: TR (Bitfield-Mask: 0x01)                     */
#define PS2_3_CONTROL_EN_Pos                  (1UL)                     /*!< PS2_3 CONTROL: EN (Bit 1)                                   */
#define PS2_3_CONTROL_EN_Msk                  (0x2UL)                   /*!< PS2_3 CONTROL: EN (Bitfield-Mask: 0x01)                     */
#define PS2_3_CONTROL_PARITY_Pos              (2UL)                     /*!< PS2_3 CONTROL: PARITY (Bit 2)                               */
#define PS2_3_CONTROL_PARITY_Msk              (0xcUL)                   /*!< PS2_3 CONTROL: PARITY (Bitfield-Mask: 0x03)                 */
#define PS2_3_CONTROL_STOP_Pos                (4UL)                     /*!< PS2_3 CONTROL: STOP (Bit 4)                                 */
#define PS2_3_CONTROL_STOP_Msk                (0x30UL)                  /*!< PS2_3 CONTROL: STOP (Bitfield-Mask: 0x03)                   */

/* --------------------------------  PS2_3_STATUS  -------------------------------- */
#define PS2_3_STATUS_RDATA_RDY_Pos            (0UL)                     /*!< PS2_3 STATUS: RDATA_RDY (Bit 0)                             */
#define PS2_3_STATUS_RDATA_RDY_Msk            (0x1UL)                   /*!< PS2_3 STATUS: RDATA_RDY (Bitfield-Mask: 0x01)               */
#define PS2_3_STATUS_REC_TIMEOUT_Pos          (1UL)                     /*!< PS2_3 STATUS: REC_TIMEOUT (Bit 1)                           */
#define PS2_3_STATUS_REC_TIMEOUT_Msk          (0x2UL)                   /*!< PS2_3 STATUS: REC_TIMEOUT (Bitfield-Mask: 0x01)             */
#define PS2_3_STATUS_PE_Pos                   (2UL)                     /*!< PS2_3 STATUS: PE (Bit 2)                                    */
#define PS2_3_STATUS_PE_Msk                   (0x4UL)                   /*!< PS2_3 STATUS: PE (Bitfield-Mask: 0x01)                      */
#define PS2_3_STATUS_FE_Pos                   (3UL)                     /*!< PS2_3 STATUS: FE (Bit 3)                                    */
#define PS2_3_STATUS_FE_Msk                   (0x8UL)                   /*!< PS2_3 STATUS: FE (Bitfield-Mask: 0x01)                      */
#define PS2_3_STATUS_XMIT_IDLE_Pos            (4UL)                     /*!< PS2_3 STATUS: XMIT_IDLE (Bit 4)                             */
#define PS2_3_STATUS_XMIT_IDLE_Msk            (0x10UL)                  /*!< PS2_3 STATUS: XMIT_IDLE (Bitfield-Mask: 0x01)               */
#define PS2_3_STATUS_XMIT_TIME_OUT_Pos        (5UL)                     /*!< PS2_3 STATUS: XMIT_TIME_OUT (Bit 5)                         */
#define PS2_3_STATUS_XMIT_TIME_OUT_Msk        (0x20UL)                  /*!< PS2_3 STATUS: XMIT_TIME_OUT (Bitfield-Mask: 0x01)           */
#define PS2_3_STATUS_RX_BUSY_Pos              (6UL)                     /*!< PS2_3 STATUS: RX_BUSY (Bit 6)                               */
#define PS2_3_STATUS_RX_BUSY_Msk              (0x40UL)                  /*!< PS2_3 STATUS: RX_BUSY (Bitfield-Mask: 0x01)                 */
#define PS2_3_STATUS_XMIT_START_TIMEOUT_Pos   (7UL)                     /*!< PS2_3 STATUS: XMIT_START_TIMEOUT (Bit 7)                    */
#define PS2_3_STATUS_XMIT_START_TIMEOUT_Msk   (0x80UL)                  /*!< PS2_3 STATUS: XMIT_START_TIMEOUT (Bitfield-Mask: 0x01)      */


/* ================================================================================ */
/* ================        struct 'KEYSCAN' Position & Mask        ================ */
/* ================================================================================ */


/* -------------------------------  KEYSCAN_CONTROL  ------------------------------ */
#define KEYSCAN_CONTROL_SELECT_Pos            (0UL)                     /*!< KEYSCAN CONTROL: SELECT (Bit 0)                             */
#define KEYSCAN_CONTROL_SELECT_Msk            (0x1fUL)                  /*!< KEYSCAN CONTROL: SELECT (Bitfield-Mask: 0x1f)               */
#define KEYSCAN_CONTROL_ALL_Pos               (5UL)                     /*!< KEYSCAN CONTROL: ALL (Bit 5)                                */
#define KEYSCAN_CONTROL_ALL_Msk               (0x20UL)                  /*!< KEYSCAN CONTROL: ALL (Bitfield-Mask: 0x01)                  */
#define KEYSCAN_CONTROL_KSEN_Pos              (6UL)                     /*!< KEYSCAN CONTROL: KSEN (Bit 6)                               */
#define KEYSCAN_CONTROL_KSEN_Msk              (0x40UL)                  /*!< KEYSCAN CONTROL: KSEN (Bitfield-Mask: 0x01)                 */
#define KEYSCAN_CONTROL_INVERT_Pos            (7UL)                     /*!< KEYSCAN CONTROL: INVERT (Bit 7)                             */
#define KEYSCAN_CONTROL_INVERT_Msk            (0x80UL)                  /*!< KEYSCAN CONTROL: INVERT (Bitfield-Mask: 0x01)               */


/* ================================================================================ */
/* ================        struct 'BC_LINK' Position & Mask        ================ */
/* ================================================================================ */


/* -------------------------------  BC_LINK_STATUS  ------------------------------- */
#define BC_LINK_STATUS_BUSY_Pos               (0UL)                     /*!< BC_LINK STATUS: BUSY (Bit 0)                                */
#define BC_LINK_STATUS_BUSY_Msk               (0x1UL)                   /*!< BC_LINK STATUS: BUSY (Bitfield-Mask: 0x01)                  */
#define BC_LINK_STATUS_BUSY_CLR_INT_EN_Pos    (4UL)                     /*!< BC_LINK STATUS: BUSY_CLR_INT_EN (Bit 4)                     */
#define BC_LINK_STATUS_BUSY_CLR_INT_EN_Msk    (0x10UL)                  /*!< BC_LINK STATUS: BUSY_CLR_INT_EN (Bitfield-Mask: 0x01)       */
#define BC_LINK_STATUS_ERR_INT_EN_Pos         (5UL)                     /*!< BC_LINK STATUS: ERR_INT_EN (Bit 5)                          */
#define BC_LINK_STATUS_ERR_INT_EN_Msk         (0x20UL)                  /*!< BC_LINK STATUS: ERR_INT_EN (Bitfield-Mask: 0x01)            */
#define BC_LINK_STATUS_ERROR_Pos              (6UL)                     /*!< BC_LINK STATUS: ERROR (Bit 6)                               */
#define BC_LINK_STATUS_ERROR_Msk              (0x40UL)                  /*!< BC_LINK STATUS: ERROR (Bitfield-Mask: 0x01)                 */
#define BC_LINK_STATUS_RESET_Pos              (7UL)                     /*!< BC_LINK STATUS: RESET (Bit 7)                               */
#define BC_LINK_STATUS_RESET_Msk              (0x80UL)                  /*!< BC_LINK STATUS: RESET (Bitfield-Mask: 0x01)                 */


/* ================================================================================ */
/* ================          struct 'TFDP' Position & Mask         ================ */
/* ================================================================================ */


/* --------------------------------  TFDP_CONTROL  -------------------------------- */
#define TFDP_CONTROL_EN_Pos                   (0UL)                     /*!< TFDP CONTROL: EN (Bit 0)                                    */
#define TFDP_CONTROL_EN_Msk                   (0x1UL)                   /*!< TFDP CONTROL: EN (Bitfield-Mask: 0x01)                      */
#define TFDP_CONTROL_EDGE_SEL_Pos             (1UL)                     /*!< TFDP CONTROL: EDGE_SEL (Bit 1)                              */
#define TFDP_CONTROL_EDGE_SEL_Msk             (0x2UL)                   /*!< TFDP CONTROL: EDGE_SEL (Bitfield-Mask: 0x01)                */
#define TFDP_CONTROL_DIVSEL_Pos               (2UL)                     /*!< TFDP CONTROL: DIVSEL (Bit 2)                                */
#define TFDP_CONTROL_DIVSEL_Msk               (0xcUL)                   /*!< TFDP CONTROL: DIVSEL (Bitfield-Mask: 0x03)                  */
#define TFDP_CONTROL_IP_DELAY_Pos             (4UL)                     /*!< TFDP CONTROL: IP_DELAY (Bit 4)                              */
#define TFDP_CONTROL_IP_DELAY_Msk             (0x70UL)                  /*!< TFDP CONTROL: IP_DELAY (Bitfield-Mask: 0x07)                */


/* ================================================================================ */
/* ================          struct 'ADC' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  ADC_CONTROL  -------------------------------- */
#define ADC_CONTROL_ACTIVATE_Pos              (0UL)                     /*!< ADC CONTROL: ACTIVATE (Bit 0)                               */
#define ADC_CONTROL_ACTIVATE_Msk              (0x1UL)                   /*!< ADC CONTROL: ACTIVATE (Bitfield-Mask: 0x01)                 */
#define ADC_CONTROL_START_SINGLE_Pos          (1UL)                     /*!< ADC CONTROL: START_SINGLE (Bit 1)                           */
#define ADC_CONTROL_START_SINGLE_Msk          (0x2UL)                   /*!< ADC CONTROL: START_SINGLE (Bitfield-Mask: 0x01)             */
#define ADC_CONTROL_START_REPEAT_Pos          (2UL)                     /*!< ADC CONTROL: START_REPEAT (Bit 2)                           */
#define ADC_CONTROL_START_REPEAT_Msk          (0x4UL)                   /*!< ADC CONTROL: START_REPEAT (Bitfield-Mask: 0x01)             */
#define ADC_CONTROL_POWER_SAVER_DIS_Pos       (3UL)                     /*!< ADC CONTROL: POWER_SAVER_DIS (Bit 3)                        */
#define ADC_CONTROL_POWER_SAVER_DIS_Msk       (0x8UL)                   /*!< ADC CONTROL: POWER_SAVER_DIS (Bitfield-Mask: 0x01)          */
#define ADC_CONTROL_SOFT_RESET_Pos            (4UL)                     /*!< ADC CONTROL: SOFT_RESET (Bit 4)                             */
#define ADC_CONTROL_SOFT_RESET_Msk            (0x10UL)                  /*!< ADC CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)               */
#define ADC_CONTROL_REPEAT_DONE_STAT_Pos      (6UL)                     /*!< ADC CONTROL: REPEAT_DONE_STAT (Bit 6)                       */
#define ADC_CONTROL_REPEAT_DONE_STAT_Msk      (0x40UL)                  /*!< ADC CONTROL: REPEAT_DONE_STAT (Bitfield-Mask: 0x01)         */
#define ADC_CONTROL_SINGLE_DONE_STAT_Pos      (7UL)                     /*!< ADC CONTROL: SINGLE_DONE_STAT (Bit 7)                       */
#define ADC_CONTROL_SINGLE_DONE_STAT_Msk      (0x80UL)                  /*!< ADC CONTROL: SINGLE_DONE_STAT (Bitfield-Mask: 0x01)         */

/* ----------------------------------  ADC_DELAY  --------------------------------- */
#define ADC_DELAY_START_Pos                   (0UL)                     /*!< ADC DELAY: START (Bit 0)                                    */
#define ADC_DELAY_START_Msk                   (0xffffUL)                /*!< ADC DELAY: START (Bitfield-Mask: 0xffff)                    */
#define ADC_DELAY_REPEAT_Pos                  (16UL)                    /*!< ADC DELAY: REPEAT (Bit 16)                                  */
#define ADC_DELAY_REPEAT_Msk                  (0xffff0000UL)            /*!< ADC DELAY: REPEAT (Bitfield-Mask: 0xffff)                   */

/* ---------------------------------  ADC_STATUS  --------------------------------- */
#define ADC_STATUS_CH0_Pos                    (0UL)                     /*!< ADC STATUS: CH0 (Bit 0)                                     */
#define ADC_STATUS_CH0_Msk                    (0x1UL)                   /*!< ADC STATUS: CH0 (Bitfield-Mask: 0x01)                       */
#define ADC_STATUS_CH1_Pos                    (1UL)                     /*!< ADC STATUS: CH1 (Bit 1)                                     */
#define ADC_STATUS_CH1_Msk                    (0x2UL)                   /*!< ADC STATUS: CH1 (Bitfield-Mask: 0x01)                       */
#define ADC_STATUS_CH2_Pos                    (2UL)                     /*!< ADC STATUS: CH2 (Bit 2)                                     */
#define ADC_STATUS_CH2_Msk                    (0x4UL)                   /*!< ADC STATUS: CH2 (Bitfield-Mask: 0x01)                       */
#define ADC_STATUS_CH3_Pos                    (3UL)                     /*!< ADC STATUS: CH3 (Bit 3)                                     */
#define ADC_STATUS_CH3_Msk                    (0x8UL)                   /*!< ADC STATUS: CH3 (Bitfield-Mask: 0x01)                       */
#define ADC_STATUS_CH4_Pos                    (4UL)                     /*!< ADC STATUS: CH4 (Bit 4)                                     */
#define ADC_STATUS_CH4_Msk                    (0x10UL)                  /*!< ADC STATUS: CH4 (Bitfield-Mask: 0x01)                       */

/* --------------------------------  ADC_SINGLE_EN  ------------------------------- */
#define ADC_SINGLE_EN_CH0_Pos                 (0UL)                     /*!< ADC SINGLE_EN: CH0 (Bit 0)                                  */
#define ADC_SINGLE_EN_CH0_Msk                 (0x1UL)                   /*!< ADC SINGLE_EN: CH0 (Bitfield-Mask: 0x01)                    */
#define ADC_SINGLE_EN_CH1_Pos                 (1UL)                     /*!< ADC SINGLE_EN: CH1 (Bit 1)                                  */
#define ADC_SINGLE_EN_CH1_Msk                 (0x2UL)                   /*!< ADC SINGLE_EN: CH1 (Bitfield-Mask: 0x01)                    */
#define ADC_SINGLE_EN_CH2_Pos                 (2UL)                     /*!< ADC SINGLE_EN: CH2 (Bit 2)                                  */
#define ADC_SINGLE_EN_CH2_Msk                 (0x4UL)                   /*!< ADC SINGLE_EN: CH2 (Bitfield-Mask: 0x01)                    */
#define ADC_SINGLE_EN_CH3_Pos                 (3UL)                     /*!< ADC SINGLE_EN: CH3 (Bit 3)                                  */
#define ADC_SINGLE_EN_CH3_Msk                 (0x8UL)                   /*!< ADC SINGLE_EN: CH3 (Bitfield-Mask: 0x01)                    */
#define ADC_SINGLE_EN_CH4_Pos                 (4UL)                     /*!< ADC SINGLE_EN: CH4 (Bit 4)                                  */
#define ADC_SINGLE_EN_CH4_Msk                 (0x10UL)                  /*!< ADC SINGLE_EN: CH4 (Bitfield-Mask: 0x01)                    */

/* ---------------------------------  ADC_REPEAT  --------------------------------- */
#define ADC_REPEAT_CH0_Pos                    (0UL)                     /*!< ADC REPEAT: CH0 (Bit 0)                                     */
#define ADC_REPEAT_CH0_Msk                    (0x1UL)                   /*!< ADC REPEAT: CH0 (Bitfield-Mask: 0x01)                       */
#define ADC_REPEAT_CH1_Pos                    (1UL)                     /*!< ADC REPEAT: CH1 (Bit 1)                                     */
#define ADC_REPEAT_CH1_Msk                    (0x2UL)                   /*!< ADC REPEAT: CH1 (Bitfield-Mask: 0x01)                       */
#define ADC_REPEAT_CH2_Pos                    (2UL)                     /*!< ADC REPEAT: CH2 (Bit 2)                                     */
#define ADC_REPEAT_CH2_Msk                    (0x4UL)                   /*!< ADC REPEAT: CH2 (Bitfield-Mask: 0x01)                       */
#define ADC_REPEAT_CH3_Pos                    (3UL)                     /*!< ADC REPEAT: CH3 (Bit 3)                                     */
#define ADC_REPEAT_CH3_Msk                    (0x8UL)                   /*!< ADC REPEAT: CH3 (Bitfield-Mask: 0x01)                       */
#define ADC_REPEAT_CH4_Pos                    (4UL)                     /*!< ADC REPEAT: CH4 (Bit 4)                                     */
#define ADC_REPEAT_CH4_Msk                    (0x10UL)                  /*!< ADC REPEAT: CH4 (Bitfield-Mask: 0x01)                       */



/* ================================================================================ */
/* ================              Peripheral memory map             ================ */
/* ================================================================================ */

#define PCR_BASE                        0x40080100UL
#define VBAT_BASE                       0x4000A400UL
#define LPC_BASE                        0x400F3000UL
#define LPC_CONFIG_BASE                 0x400F3300UL
#define GCR_BASE                        0x400FFF00UL
#define EMI_BASE                        0x400F0000UL
#define ACPI_EC0_BASE                   0x400F0C00UL
#define ACPI_EC1_BASE                   0x400F1000UL
#define KBC_BASE                        0x400F0400UL
#define PORT92_BASE                     0x400F1800UL
#define MBX_BASE                        0x400F2400UL
#define PM1_BASE                        0x400F1400UL
#define UART_BASE                       0x400F1C00UL
#define INTR_BASE                       0x4000C000UL
#define WDT_BASE                        0x40000400UL
#define TIMER_16_0_BASE                 0x40000C00UL
#define TIMER_16_1_BASE                 0x40000C20UL
#define TIMER_16_2_BASE                 0x40000C40UL
#define TIMER_16_3_BASE                 0x40000C60UL
#define TIMER_32_0_BASE                 0x40000C80UL
#define TIMER_32_1_BASE                 0x40000CA0UL
#define HTM_BASE                        0x40009800UL
#define RTC_BASE                        0x400F2C00UL
#define GPIO_BASE                       0x40081000UL
#define DMA_BASE                        0x40002400UL
#define SMB0_BASE                       0x40001800UL
#define SMB1_BASE                       0x4000AC00UL
#define SMB2_BASE                       0x4000B000UL
#define SMB3_BASE                       0x4000B400UL
#define PECI_BASE                       0x40006400UL
#define TACH_0_BASE                     0x40006000UL
#define TACH_1_BASE                     0x40006100UL
#define PWM_0_BASE                      0x40005800UL
#define PWM_1_BASE                      0x40005810UL
#define PWM_2_BASE                      0x40005820UL
#define PWM_3_BASE                      0x40005830UL
#define RPM_FAN_BASE                    0x4000A000UL
#define SPI_0_BASE                      0x40009400UL
#define SPI_1_BASE                      0x40009480UL
#define LED_0_BASE                      0x4000B800UL
#define LED_1_BASE                      0x4000B900UL
#define LED_2_BASE                      0x4000BA00UL
#define LED_3_BASE                      0x4000BB00UL
#define PS2_0_BASE                      0x40009000UL
#define PS2_1_BASE                      0x40009040UL
#define PS2_2_BASE                      0x40009080UL
#define PS2_3_BASE                      0x400090C0UL
#define KEYSCAN_BASE                    0x40009C00UL
#define BC_LINK_BASE                    0x4000BC00UL
#define TFDP_BASE                       0x40008C00UL
#define ADC_BASE                        0x40007C00UL
#define EC_REG_BANK_BASE                0x4000FC00UL
#define JTAG_BASE                       0x40080000UL
#define PKE_BASE                        0x4000BD00UL
#define TRNG_BASE                       0x4000BE00UL
#define HASH_BASE                       0x4000D000UL
#define AES_BASE                        0x4000D200UL


/* ================================================================================ */
/* ================             Peripheral declaration             ================ */
/* ================================================================================ */

#define CEC1302_PCR                             ((PCR_Type                *) PCR_BASE)
#define CEC1302_VBAT                            ((VBAT_Type               *) VBAT_BASE)
#define CEC1302_LPC                             ((LPC_Type                *) LPC_BASE)
#define CEC1302_LPC_CONFIG                      ((LPC_CONFIG_Type         *) LPC_CONFIG_BASE)
#define CEC1302_GCR                             ((GCR_Type                *) GCR_BASE)
#define CEC1302_EMI                             ((EMI_Type                *) EMI_BASE)
#define CEC1302_ACPI_EC0                        ((ACPI_EC0_Type           *) ACPI_EC0_BASE)
#define CEC1302_ACPI_EC1                        ((ACPI_EC0_Type           *) ACPI_EC1_BASE)
#define CEC1302_KBC                             ((KBC_Type                *) KBC_BASE)
#define CEC1302_PORT92                          ((PORT92_Type             *) PORT92_BASE)
#define CEC1302_MBX                             ((MBX_Type                *) MBX_BASE)
#define CEC1302_PM1                             ((PM1_Type                *) PM1_BASE)
#define CEC1302_UART                            ((UART_Type               *) UART_BASE)
#define CEC1302_INTR                            ((INTR_Type               *) INTR_BASE)
#define CEC1302_WDT                             ((WDT_Type                *) WDT_BASE)
#define CEC1302_TIMER_16_0                      ((TIMER_16_0_Type         *) TIMER_16_0_BASE)
#define CEC1302_TIMER_16_1                      ((TIMER_16_0_Type         *) TIMER_16_1_BASE)
#define CEC1302_TIMER_16_2                      ((TIMER_16_0_Type         *) TIMER_16_2_BASE)
#define CEC1302_TIMER_16_3                      ((TIMER_16_0_Type         *) TIMER_16_3_BASE)
#define CEC1302_TIMER_32_0                      ((TIMER_16_0_Type         *) TIMER_32_0_BASE)
#define CEC1302_TIMER_32_1                      ((TIMER_16_0_Type         *) TIMER_32_1_BASE)
#define CEC1302_HTM                             ((HTM_Type                *) HTM_BASE)
#define CEC1302_RTC                             ((RTC_Type                *) RTC_BASE)
#define CEC1302_GPIO                            ((GPIO_Type               *) GPIO_BASE)
#define CEC1302_DMA                             ((DMA_Type                *) DMA_BASE)
#define CEC1302_SMB0                            ((SMB0_Type               *) SMB0_BASE)
#define CEC1302_SMB1                            ((SMB0_Type               *) SMB1_BASE)
#define CEC1302_SMB2                            ((SMB0_Type               *) SMB2_BASE)
#define CEC1302_SMB3                            ((SMB0_Type               *) SMB3_BASE)
#define CEC1302_PECI                            ((PECI_Type               *) PECI_BASE)
#define CEC1302_TACH_0                          ((TACH_0_Type             *) TACH_0_BASE)
#define CEC1302_TACH_1                          ((TACH_0_Type             *) TACH_1_BASE)
#define CEC1302_PWM_0                           ((PWM_0_Type              *) PWM_0_BASE)
#define CEC1302_PWM_1                           ((PWM_0_Type              *) PWM_1_BASE)
#define CEC1302_PWM_2                           ((PWM_0_Type              *) PWM_2_BASE)
#define CEC1302_PWM_3                           ((PWM_0_Type              *) PWM_3_BASE)
#define CEC1302_RPM_FAN                         ((RPM_FAN_Type            *) RPM_FAN_BASE)
#define CEC1302_SPI_0                           ((SPI_0_Type              *) SPI_0_BASE)
#define CEC1302_SPI_1                           ((SPI_0_Type              *) SPI_1_BASE)
#define CEC1302_LED_0                           ((LED_0_Type              *) LED_0_BASE)
#define CEC1302_LED_1                           ((LED_0_Type              *) LED_1_BASE)
#define CEC1302_LED_2                           ((LED_0_Type              *) LED_2_BASE)
#define CEC1302_LED_3                           ((LED_0_Type              *) LED_3_BASE)
#define CEC1302_PS2_0                           ((PS2_0_Type              *) PS2_0_BASE)
#define CEC1302_PS2_1                           ((PS2_0_Type              *) PS2_1_BASE)
#define CEC1302_PS2_2                           ((PS2_0_Type              *) PS2_2_BASE)
#define CEC1302_PS2_3                           ((PS2_0_Type              *) PS2_3_BASE)
#define CEC1302_KEYSCAN                         ((KEYSCAN_Type            *) KEYSCAN_BASE)
#define CEC1302_BC_LINK                         ((BC_LINK_Type            *) BC_LINK_BASE)
#define CEC1302_TFDP                            ((TFDP_Type               *) TFDP_BASE)
#define CEC1302_ADC                             ((ADC_Type                *) ADC_BASE)
#define CEC1302_EC_REG_BANK                     ((EC_REG_BANK_Type        *) EC_REG_BANK_BASE)
#define CEC1302_JTAG                            ((JTAG_Type               *) JTAG_BASE)
#define CEC1302_PKE                             ((PKE_TypeDef             *) PKE_BASE)
#define CEC1302_TRNG                            ((TRNG_TypeDef            *) TRNG_BASE)
#define CEC1302_HASH                            ((HASH_TypeDef            *) HASH_BASE)
#define CEC1302_AES                             ((AES_TypeDef             *) AES_BASE)

        
/** @} */ /* End of group Device_Peripheral_Registers */
/** @} */ /* End of group MCHP_CEC1302 */
/** @} */ /* End of group Microchip Technology Inc. */

#ifdef __cplusplus
}
#endif


#endif  /* MCHP_CEC1302_H */


