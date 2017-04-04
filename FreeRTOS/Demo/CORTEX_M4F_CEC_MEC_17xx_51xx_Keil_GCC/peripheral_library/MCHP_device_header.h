
/****************************************************************************************************//**
 * @file     MCHP_device_header.h
 *
 * @brief    CMSIS Cortex-M4 Peripheral Access Layer Header File for
 *           MCHP_device_header from Microchip Technology Inc..
 *
 * @version  V1.0
 * @date     5. November 2015
 *
 * @note     Generated with SVDConv V2.87e 
 *           from CMSIS SVD File 'MCHP_device_header.svd' Version 1.0,
 *
 * @par      ARM Limited (ARM) is supplying this software for use with Cortex-M
 *           processor based microcontroller, but can be equally used for other
 *           suitable processor architectures. This file can be freely distributed.
 *           Modifications to this file shall be clearly marked.
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

/** @addtogroup MCHP_device_header
  * @{
  */

#ifndef MCHP_DEVICE_HEADER_H
#define MCHP_DEVICE_HEADER_H

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
/* ----------------Device Specific Interrupt Numbers---------------- */
  GPIO_140_176_IRQn             =   0,              /*!<   0  GPIO[140:176], GIRQ08                                            */
  GPIO_100_137_IRQn             =   1,              /*!<   1  GPIO[100:137], GIRQ09                                            */
  GPIO_040_076_IRQn             =   2,              /*!<   2  GPIO[040:076], GIRQ10                                            */
  GPIO_000_036_IRQn             =   3,              /*!<   3  GPIO[000:036], GIRQ11                                            */
  GPIO_200_236_IRQn             =   4,              /*!<   4  GPIO[200:236], GIRQ12                                            */
  MSVW00_06_IRQn                =  15,              /*!<  15  MSVW[00:06]_SRC[0:3], GIRQ 24                                    */
  MSVW07_10_IRQn                =  16,              /*!<  16  MSVW[07:10]_SRC[0:3], GIRQ 25                                    */
  GPIO_240_257_IRQn             =  17,              /*!<  17  GPIO[240:257], GIRQ26                                            */
  SMB0_IRQn                     =  20,              /*!<  20  SMB0, GIRQ 13.0                                                  */
  SMB1_IRQn                     =  21,              /*!<  21  SMB1                                                             */
  SMB2_IRQn                     =  22,              /*!<  22  SMB2                                                             */
  SMB3_IRQn                     =  23,              /*!<  23  SMB3                                                             */
  DMA0_IRQn                     =  24,              /*!<  24  DMA0, GIRQ14.0                                                   */
  DMA1_IRQn                     =  25,              /*!<  25  DMA1                                                             */
  DMA2_IRQn                     =  26,              /*!<  26  DMA2                                                             */
  DMA3_IRQn                     =  27,              /*!<  27  DMA3                                                             */
  DMA4_IRQn                     =  28,              /*!<  28  DMA4                                                             */
  DMA5_IRQn                     =  29,              /*!<  29  DMA5                                                             */
  DMA6_IRQn                     =  30,              /*!<  30  DMA6                                                             */
  DMA7_IRQn                     =  31,              /*!<  31  DMA7                                                             */
  DMA8_IRQn                     =  32,              /*!<  32  DMA8                                                             */
  DMA9_IRQn                     =  33,              /*!<  33  DMA9                                                             */
  DMA10_IRQn                    =  34,              /*!<  34  DMA10                                                            */
  DMA11_IRQn                    =  35,              /*!<  35  DMA11                                                            */
  DMA12_IRQn                    =  36,              /*!<  36  DMA12                                                            */
  DMA13_IRQn                    =  37,              /*!<  37  DMA13                                                            */
  UART_0_IRQn                   =  40,              /*!<  40  UART 0, GIRQ 15.0                                                */
  UART_1_IRQn                   =  41,              /*!<  41  UART 1, GIRQ 15.1                                                */
  EMI_0_IRQn                    =  42,              /*!<  42  EMI_0, GIRQ 15.2                                                 */
  EMI_1_IRQn                    =  43,              /*!<  43  EMI_1, GIRQ 15.3                                                 */
  EMI_2_IRQn                    =  44,              /*!<  44  EMI_2, GIRQ 15.4                                                 */
  ACPIEC0_IBF_IRQn              =  45,              /*!<  45  ACPIEC[0] IBF, GIRQ 15.5                                         */
  ACPIEC0_OBF_IRQn              =  46,              /*!<  46  ACPIEC[0] OBF, GIRQ 15.6                                         */
  ACPIEC1_IBF_IRQn              =  47,              /*!<  47  ACPIEC[1] IBF, GIRQ 15.7                                         */
  ACPIEC1_OBF_IRQn              =  48,              /*!<  48  ACPIEC[1] OBF, GIRQ 15.8                                         */
  ACPIEC2_IBF_IRQn              =  49,              /*!<  49  ACPIEC[2] IBF, GIRQ 15.9                                         */
  ACPIEC2_OBF_IRQn              =  50,              /*!<  50  ACPIEC[2] OBF, GIRQ 15.10                                        */
  ACPIEC3_IBF_IRQn              =  51,              /*!<  51  ACPIEC[3] IBF, GIRQ 15.11                                        */
  ACPIEC3_OBF_IRQn              =  52,              /*!<  52  ACPIEC[3] OBF, GIRQ 15.12                                        */
  ACPIEC4_IBF_IRQn              =  53,              /*!<  53  ACPIEC[4] IBF, GIRQ 15.13                                        */
  ACPIEC4_OBF_IRQn              =  54,              /*!<  54  ACPIEC[4] OBF, GIRQ 15.14                                        */
  ACPIPM1_CTL_IRQn              =  55,              /*!<  55  ACPIPM1_CTL, GIRQ 15.10                                          */
  ACPIPM1_EN_IRQn               =  56,              /*!<  56  ACPIPM1_EN, GIRQ 15.11                                           */
  ACPIPM1_STS_IRQn              =  57,              /*!<  57  ACPIPM1_STS, GIRQ 15.12                                          */
  KBC8042_OBF_IRQn              =  58,              /*!<  58  8042EM OBF, GIRQ 15.18                                           */
  KBC8042_IBF_IRQn              =  59,              /*!<  59  8042EM IBF, GIRQ 15.19                                           */
  MAILBOX_IRQn                  =  60,              /*!<  60  MAILBOX, GIRQ 15.20                                              */
  MAILBOX_DATA_IRQn             =  61,              /*!<  61  MAILBOX DATA, GIRQ 15.21                                         */
  PORT80_DEBUG_0_IRQn           =  62,              /*!<  62  PORT80_DEBUG_0, GIRQ 15.22                                       */
  PORT80_DEBUG_1_IRQn           =  63,              /*!<  63  PORT80_DEBUG_1, GIRQ 15.23                                       */
  ASIF_INT_IRQn                 =  64,              /*!<  64  ASIF_INT, GIRQ 15.24                                             */
  PECIHOST_IRQn                 =  70,              /*!<  70  PECIHOST, GIRQ 17.0                                              */
  TACH_0_IRQn                   =  71,              /*!<  71  TACH_0, GIRQ 17.1                                                */
  TACH_1_IRQn                   =  72,              /*!<  72  TACH_1, GIRQ 17.2                                                */
  TACH_2_IRQn                   =  73,              /*!<  73  TACH_2, GIRQ 17.3                                                */
  RPM2PWM_0_FAIL_IRQn           =  74,              /*!<  74  RPM2PWM_0 Fail, GIRQ 17.4                                        */
  RPM2PWM_0_STALL_IRQn          =  75,              /*!<  75  RPM2PWM_0 Stall, GIRQ 17.5                                       */
  RPM2PWM_1_FAIL_IRQn           =  76,              /*!<  76  RPM2PWM_1 Fail, GIRQ 17.6                                        */
  RPM2PWM_1_STALL_IRQn          =  77,              /*!<  77  RPM2PWM_1 Stall, GIRQ 17.7                                       */
  ADC_SNGL_IRQn                 =  78,              /*!<  78  ADC_SNGL, GIRQ 17.8                                              */
  ADC_RPT_IRQn                  =  79,              /*!<  79  ADC_RPT, GIRQ 17.9                                               */
  RC_ID_0_IRQn                  =  80,              /*!<  80  RC_ID_0, GIRQ 17.10                                              */
  RC_ID_1_IRQn                  =  81,              /*!<  81  RC_ID_1, GIRQ 17.11                                              */
  RC_ID_2_IRQn                  =  82,              /*!<  82  RC_ID_2, GIRQ 17.12                                              */
  LED_0_IRQn                    =  83,              /*!<  83  Breathing LED 0, GIRQ 17.13                                      */
  LED_1_IRQn                    =  84,              /*!<  84  Breathing LED 1, GIRQ 17.14                                      */
  LED_2_IRQn                    =  85,              /*!<  85  Breathing LED 2, GIRQ 17.15                                      */
  LED_3_IRQn                    =  86,              /*!<  86  Breathing LED 3, GIRQ 17.16                                      */
  PROCHOT_MON_IRQn              =  87,              /*!<  87  PROCHOT_MON, GIRQ 17.17                                          */
  POWERGUARD_0_IRQn             =  88,              /*!<  88  POWERGUARD_0, GIRQ 17.18                                         */
  POWERGUARD_1_IRQn             =  89,              /*!<  89  POWERGUARD_1, GIRQ 17.19                                         */
  LPC_IRQn                      =  90,              /*!<  90  LPC (GIRQ 18.0)                                                  */
  QMSPI_IRQn                    =  91,              /*!<  91  QMSPI, GIRQ 18.1                                                 */
  SPI0_TX_IRQn                  =  92,              /*!<  92  SPI0 TX, GIRQ 18.2                                               */
  SPI0_RX_IRQn                  =  93,              /*!<  93  SPI0 RX, GIRQ 18.3                                               */
  SPI1_TX_IRQn                  =  94,              /*!<  94  SPI1 TX, GIRQ 18.4                                               */
  SPI1_RX_IRQn                  =  95,              /*!<  95  SPI1 RX, GIRQ 18.5                                               */
  BCM_BUSY_CLR_0_IRQn           =  96,              /*!<  96  BCM_BUSY_CLR_0, GIRQ 18.6                                        */
  BCM_ERR_0_IRQn                =  97,              /*!<  97  BCM_ERR_0, GIRQ 18.7                                             */
  BCM_BUSY_CLR_1_IRQn           =  98,              /*!<  98  BCM_BUSY_CLR_1, GIRQ 18.8                                        */
  BCM_ERR_1_IRQn                =  99,              /*!<  99  BCM_ERR_1, GIRQ 18.9                                             */
  PS2_0_ACT_IRQn                = 100,              /*!< 100  PS2 Controller 0 Activity, GIRQ 17.14                            */
  PS2_1_ACT_IRQn                = 101,              /*!< 101  PS2 Controller 1 Activity, GIRQ 17.15                            */
  PS2_2_ACT_IRQn                = 102,              /*!< 102  PS2 Controller 2 Activity, GIRQ 17.16                            */
  INTR_PC_IRQn                  = 103,              /*!< 103  PC, GIRQ 19.0                                                    */
  INTR_BM1_IRQn                 = 104,              /*!< 104  BM1, GIRQ 19.1                                                   */
  INTR_BM2_IRQn                 = 105,              /*!< 105  BM2, GIRQ 19.2                                                   */
  INTR_LTR_IRQn                 = 106,              /*!< 106  LTR, GIRQ 19.3                                                   */
  INTR_OOB_UP_IRQn              = 107,              /*!< 107  OOB_UP, GIRQ 19.4                                                */
  INTR_OOB_DOWN_IRQn            = 108,              /*!< 108  OOB_DOWN, GIRQ 19.5                                              */
  INTR_FLASH_IRQn               = 109,              /*!< 109  FLASH, GIRQ 19.6                                                 */
  ESPI_RESET_IRQn               = 110,              /*!< 110  ESPI_RESET, GIRQ 19.7                                            */
  RTOS_TIMER_IRQn               = 111,              /*!< 111  RTOS_TIMER, GIRQ 21.0                                            */
  HTIMER0_IRQn                  = 112,              /*!< 112  HTIMER0, GIRQ 21.1                                               */
  HTIMER1_IRQn                  = 113,              /*!< 113  HTIMER1, GIRQ 21.2                                               */
  WEEK_ALARM_IRQn               = 114,              /*!< 114  WEEK_ALARM_INT, GIRQ 21.3                                        */
  SUB_WEEK_ALARM_IRQn           = 115,              /*!< 115  SUB_WEEK_ALARM_INT, GIRQ 21.4                                    */
  ONE_SECOND_IRQn               = 116,              /*!< 116  ONE_SECOND, GIRQ 21.5                                            */
  SUB_SECOND_IRQn               = 117,              /*!< 117  SUB_SECOND, GIRQ 21.6                                            */
  SYSPWR_PRES_IRQn              = 118,              /*!< 118  SYSPWR_PRES, GIRQ 21.7                                           */
  RTC_IRQn                      = 119,              /*!< 119  RTC, GIRQ 21.8                                                   */
  RTC_ALARM_IRQn                = 120,              /*!< 120  RTC ALARM, GIRQ 21.9                                             */
  VCI_OVRD_IN_IRQn              = 121,              /*!< 121  VCI_OVRD_IN, GIRQ 21.10                                          */
  VCI_IN0_IRQn                  = 122,              /*!< 122  VCI_IN0, GIRQ 21.11                                              */
  VCI_IN1_IRQn                  = 123,              /*!< 123  VCI_IN1, GIRQ 21.12                                              */
  VCI_IN2_IRQn                  = 124,              /*!< 124  VCI_IN2, GIRQ 21.13                                              */
  VCI_IN3_IRQn                  = 125,              /*!< 125  VCI_IN3, GIRQ 21.14                                              */
  VCI_IN4_IRQn                  = 126,              /*!< 126  VCI_IN4, GIRQ 21.15                                              */
  VCI_IN5_IRQn                  = 127,              /*!< 127  VCI_IN5, GIRQ 21.16                                              */
  VCI_IN6_IRQn                  = 128,              /*!< 128  VCI_IN6, GIRQ 21.17                                              */
  PS2_0A_WK_IRQn                = 129,              /*!< 129  PS2 Controller 0 Port A Wake, GIRQ 21.18                         */
  PS2_0B_WK_IRQn                = 130,              /*!< 130  PS2 Controller 0 Port B Wake, GIRQ 21.19                         */
  PS2_1A_WK_IRQn                = 131,              /*!< 131  PS2 Controller 1 Port A Wake, GIRQ 21.20                         */
  PS2_1B_WK_IRQn                = 132,              /*!< 132  PS2 Controller 1 Port B Wake, GIRQ 21.21                         */
  PS2_2_WK_IRQn                 = 133,              /*!< 133  PS2 Controller 2 Wake, GIRQ 21.22                                */
  KSC_INT_IRQn                  = 135,              /*!< 135  KSC, GIRQ 21.25                                                  */
  TIMER0_IRQn                   = 136,              /*!< 136  TIMER_16_0, GIRQ 23.0                                            */
  TIMER1_IRQn                   = 137,              /*!< 137  TIMER_16_1, GIRQ 23.1                                            */
  TIMER2_IRQn                   = 138,              /*!< 138  TIMER_16_2, GIRQ 23.2                                            */
  TIMER3_IRQn                   = 139,              /*!< 139  TIMER_16_3, GIRQ 23.3                                            */
  TIMER4_IRQn                   = 140,              /*!< 140  TIMER_32_0, GIRQ 23.4                                            */
  TIMER5_IRQn                   = 141,              /*!< 141  TIMER_32_1, GIRQ 23.5                                            */
  COUNTER_TIMER_0_IRQn          = 142,              /*!< 142  COUNTER_TIMER_0, GIRQ 23.6                                       */
  COUNTER_TIMER_1_IRQn          = 143,              /*!< 143  COUNTER_TIMER_1, GIRQ 23.7                                       */
  COUNTER_TIMER_2_IRQn          = 144,              /*!< 144  COUNTER_TIMER_2, GIRQ 23.8                                       */
  COUNTER_TIMER_3_IRQn          = 145,              /*!< 145  COUNTER_TIMER_3, GIRQ 23.9                                       */
  CAPTURE_TIMER_IRQn            = 146,              /*!< 146  CAPTURE_TIMER, GIRQ 23.10                                        */
  CAPTURE_0_IRQn                = 147,              /*!< 147  CAPTURE_0, GIRQ 23.11                                            */
  CAPTURE_1_IRQn                = 148,              /*!< 148  CAPTURE_1, GIRQ 23.12                                            */
  CAPTURE_2_IRQn                = 149,              /*!< 149  CAPTURE_2, GIRQ 23.13                                            */
  CAPTURE_3_IRQn                = 150,              /*!< 150  CAPTURE_3, GIRQ 23.14                                            */
  CAPTURE_4_IRQn                = 151,              /*!< 151  CAPTURE_4, GIRQ 23.15                                            */
  CAPTURE_5_IRQn                = 152,              /*!< 152  CAPTURE_5, GIRQ 23.16                                            */
  COMPARE_0_IRQn                = 153,              /*!< 153  COMPARE_0, GIRQ 23.17                                            */
  COMPARE_1_IRQn                = 154,              /*!< 154  COMPARE_1, GIRQ 23.18                                            */
  EEPROM_IRQn                   = 155,              /*!< 155  EEPROM, GIRQ 18.13                                               */
  VWIRE_ENABLE_IRQn             = 156,              /*!< 156  VWIRE_ENABLE, GIRQ 19.8                                          */
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
#define __MPU_PRESENT                  1            /*!< MPU present or not                                                    */
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



/* ================================================================================ */
/* ================                       PCR                      ================ */
/* ================================================================================ */


/**
  * @brief The Power, Clocks, and Resets (PCR) Section identifies all the power supplies,
 clock sources, and reset inputs to the chip and defines all the derived power, clock, and reset signals.  (PCR)
  */

typedef struct {                                    /*!< (@ 0x40080100) PCR Structure                                          */
  
  union {
    __IO uint32_t  SYS_SLP_CNTRL;                   /*!< (@ 0x40080100) System Sleep Control                                   */
    
    struct {
      __IO uint32_t  SLEEP_MODE :  1;               /*!< [0..0] Selects the System Sleep mode                                  */
           uint32_t             :  1;
      __IO uint32_t  TEST       :  1;               /*!< [2..2] Test bit                                                       */
      __IO uint32_t  SLEEP_ALL  :  1;               /*!< [3..3] Initiates the System Sleep mode                                */
    } SYS_SLP_CNTRL_b;                              /*!< [4] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  PROC_CLK_CNTRL;                  /*!< (@ 0x40080104) Processor Clock Control Register [7:0] Processor
                                                         Clock Divide Value (PROC_DIV)
                                                          1: divide 48 MHz Ring Oscillator by 1.
                                                          2: divide 48 MHz Ring Oscillator by 2.
                                                          3: divide 48 MHz Ring Oscillator by 3.
                                                          4: divide 48 MHz Ring Oscillator by 4.
                                                          16: divide 48 MHz Ring Oscillator by 16.
                                                          48: divide 48 MHz Ring Oscillator by 48.
                                                          No other values are supported.                                       */
    
    struct {
      __IO uint32_t  PROCESSOR_CLOCK_DIVIDE:  8;    /*!< [0..7] Selects the EC clock rate                                      */
    } PROC_CLK_CNTRL_b;                             /*!< [8] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  SLOW_CLK_CNTRL;                  /*!< (@ 0x40080108) Configures the EC_CLK clock domain                     */
    
    struct {
      __IO uint32_t  SLOW_CLOCK_DIVIDE: 10;         /*!< [0..9] SLOW_CLOCK_DIVIDE. n=Divide by n; 0=Clock off                  */
    } SLOW_CLK_CNTRL_b;                             /*!< [10] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  OSC_ID;                          /*!< (@ 0x4008010C) Oscillator ID Register                                 */
    
    struct {
      __IO uint32_t  TEST       :  8;               /*!< [0..7] Test bits                                                      */
      __IO uint32_t  PLL_LOCK   :  1;               /*!< [8..8] PLL Lock Status                                                */
    } OSC_ID_b;                                     /*!< [9] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  PCR_PWR_RST_STS;                 /*!< (@ 0x40080110) PCR Power Reset Status Register                        */
    
    struct {
           uint32_t             :  2;
      __I  uint32_t  VCC_PWRGD_STATUS:  1;          /*!< [2..2] Indicates the status of VCC_PWRGD. 0 = PWRGD not asserted.
                                                         1 = PWRGD asserte.                                                    */
      __I  uint32_t  RESET_HOST_STATUS:  1;         /*!< [3..3] Indicates the status of RESET_VCC. 0 = reset active.
                                                         1 = reset not active.                                                 */
           uint32_t             :  1;
      __IO uint32_t  VBAT_RESET_STATUS:  1;         /*!< [5..5] VBAT reset status 0 = No reset occurred while VTR was
                                                         off or since the last time this bit was cleared. 1 = A reset
                                                          occurred.(R/WC)                                                      */
      __IO uint32_t  VTR_RESET_STATUS:  1;          /*!< [6..6] Indicates the status of VTR_RESET.(R/WC)
                                                          0 = No reset occurred since the last time this bit was cleared.
                                                          1 = A reset occurred.                                                */
      __IO uint32_t  JTAG_RESET_STATUS:  1;         /*!< [7..7] Indicates s RESET_SYS was triggered by a JTAG action.(R/WC)
                                                          0 = No JTAG reset occurred since the last time this bit was
                                                         cleared.
                                                          1 = A reset occurred because of a JATAG command.                     */
           uint32_t             :  2;
      __I  uint32_t  _32K_ACTIVE:  1;               /*!< [10..10] 32K_ACTIVE (32K_ACTIVE)                                      */
      __I  uint32_t  PCICLK_ACTIVE:  1;             /*!< [11..11] PCICLK_ACTIVE (PCICLK_ACTIVE)                                */
      __I  uint32_t  ESPI_CLK_ACTIVE:  1;           /*!< [12..12] ESPI_CLK_ACTIVE                                              */
    } PCR_PWR_RST_STS_b;                            /*!< [13] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  PWR_RST_CNTRL;                   /*!< (@ 0x40080114) Power Reset Control Register                           */
    
    struct {
      __IO uint32_t  PWR_INV    :  1;               /*!< [0..0] Used by FW to control internal RESET_VCC signal function
                                                         and external PWROK pin. This bit is read-only when VCC_PWRGD
                                                          is de-asserted low.                                                  */
           uint32_t             :  7;
      __IO uint32_t  HOST_RESET_SELECT:  1;         /*!< [8..8] Determines what generates the internal platform reset
                                                         signal. 1=LRESET# pin; 0=eSPI PLTRST# VWire                           */
    } PWR_RST_CNTRL_b;                              /*!< [9] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  SYS_RST;                         /*!< (@ 0x40080118) System Reset Register                                  */
    
    struct {
           uint32_t             :  8;
      __IO uint32_t  SOFT_SYS_RESET:  1;            /*!< [8..8] A write of a 1 forces an assertion of the RESET_SYS reset
                                                         signal, resetting the device. A write of 0 has no effect.             */
    } SYS_RST_b;                                    /*!< [9] BitSize                                                           */
  };
  __I  uint32_t  RESERVED[5];
  
  union {
    __IO uint32_t  SLP_EN_0;                        /*!< (@ 0x40080130) Sleep Enable 0 Register                                */
    
    struct {
      __IO uint32_t  JTAG_STAP_SLP_EN:  1;          /*!< [0..0] JTAG STAP Enable                                               */
      __IO uint32_t  EFUSE_SLP_EN:  1;              /*!< [1..1] eFuse Enable                                                   */
      __IO uint32_t  ISPI_SLP_EN:  1;               /*!< [2..2] ISPI Enable                                                    */
    } SLP_EN_0_b;                                   /*!< [3] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  SLP_EN_1;                        /*!< (@ 0x40080134) Sleep Enable 1 Register                                */
    
    struct {
      __IO uint32_t  INT_SLP_EN :  1;               /*!< [0..0] Interrupt Sleep Enable                                         */
      __IO uint32_t  PECI_SLP_EN:  1;               /*!< [1..1] PECI Sleep Enable                                              */
      __IO uint32_t  TACH0_SLP_EN:  1;              /*!< [2..2] TACH0 Sleep Enable (TACH0_SLP_EN)                              */
           uint32_t             :  1;
      __IO uint32_t  PWM0_SLP_EN:  1;               /*!< [4..4] PWM0 Sleep Enable (PWM0_SLP_EN)                                */
      __IO uint32_t  PMC_SLP_EN :  1;               /*!< [5..5] PMC Sleep Enable (PMC_SLP_EN)                                  */
      __IO uint32_t  DMA_SLP_EN :  1;               /*!< [6..6] DMA Sleep Enable (DMA_SLP_EN)                                  */
      __IO uint32_t  TFDP_SLP_EN:  1;               /*!< [7..7] TFDP Sleep Enable (TFDP_SLP_EN)                                */
      __IO uint32_t  PROCESSOR_SLP_EN:  1;          /*!< [8..8] PROCESSOR Sleep Enable (PROCESSOR_SLP_EN)                      */
      __IO uint32_t  WDT_SLP_EN :  1;               /*!< [9..9] WDT Sleep Enable (WDT_SLP_EN)                                  */
      __IO uint32_t  SMB0_SLP_EN:  1;               /*!< [10..10] SMB0 Sleep Enable (SMB0_SLP_EN)                              */
      __IO uint32_t  TACH1_SLP_EN:  1;              /*!< [11..11] TACH1 Sleep Enable (TACH1_SLP_EN)                            */
      __IO uint32_t  TACH2_SLP_EN:  1;              /*!< [12..12] TACH2 Sleep Enable (TACH2_SLP_EN)                            */
           uint32_t             :  7;
      __IO uint32_t  PWM1_SLP_EN:  1;               /*!< [20..20] PWM1 Sleep Enable (PWM1_SLP_EN)                              */
      __IO uint32_t  PWM2_SLP_EN:  1;               /*!< [21..21] PWM2 Sleep Enable (PWM2_SLP_EN)                              */
      __IO uint32_t  PWM3_SLP_EN:  1;               /*!< [22..22] PWM3 Sleep Enable (PWM3_SLP_EN)                              */
      __IO uint32_t  PWM4_SLP_EN:  1;               /*!< [23..23] PWM4 Sleep Enable (PWM4_SLP_EN)                              */
      __IO uint32_t  PWM5_SLP_EN:  1;               /*!< [24..24] PWM3 Sleep Enable (PWM5_SLP_EN)                              */
      __IO uint32_t  PWM6_SLP_EN:  1;               /*!< [25..25] PWM3 Sleep Enable (PWM6_SLP_EN)                              */
      __IO uint32_t  PWM7_SLP_EN:  1;               /*!< [26..26] PWM3 Sleep Enable (PWM7_SLP_EN)                              */
      __IO uint32_t  PWM8_SLP_EN:  1;               /*!< [27..27] PWM3 Sleep Enable (PWM8_SLP_EN)                              */
           uint32_t             :  1;
      __IO uint32_t  EC_REG_BANK_SLP_EN:  1;        /*!< [29..29] EC_REG_BANK Sleep Enable (EC_REG_BANK_SLP_EN)                */
      __IO uint32_t  TIMER16_0_SLP_EN:  1;          /*!< [30..30] TIMER16_0 Sleep Enable (TIMER16_0_SLP_EN)                    */
      __IO uint32_t  TIMER16_1_SLP_EN:  1;          /*!< [31..31] TIMER16_1 Sleep Enable (TIMER16_1_SLP_EN)                    */
    } SLP_EN_1_b;                                   /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  SLP_EN_2;                        /*!< (@ 0x40080138) Sleep Enable 2 Register                                */
    
    struct {
      __IO uint32_t  LPC_SLP_EN :  1;               /*!< [0..0] LPC Sleep Enable (LPC_SLP_EN)                                  */
      __IO uint32_t  UART_0_SLP_EN:  1;             /*!< [1..1] UART 0 Sleep Enable                                            */
      __IO uint32_t  UART_1_SLP_EN:  1;             /*!< [2..2] UART 1 Sleep Enable                                            */
           uint32_t             :  9;
      __IO uint32_t  GLBL_CFG_SLP_EN:  1;           /*!< [12..12] GLBL_CFG (GLBL_CFG_SLP_EN)                                   */
      __IO uint32_t  ACPI_EC_0_SLP_EN:  1;          /*!< [13..13] ACPI EC 0 Sleep Enable (ACPI_EC_0_SLP_EN)                    */
      __IO uint32_t  ACPI_EC_1_SLP_EN:  1;          /*!< [14..14] ACPI EC 1 Sleep Enable (ACPI_EC_1_SLP_EN)                    */
      __IO uint32_t  ACPI_PM1_SLP_EN:  1;           /*!< [15..15] ACPI PM1 Sleep Enable (ACPI_PM1_SLP_EN)                      */
      __IO uint32_t  KBCEM_SLP_EN:  1;              /*!< [16..16] 8042EM Sleep Enable (8042EM_SLP_EN)                          */
      __IO uint32_t  MBX_SLP_EN :  1;               /*!< [17..17] Mailbox Sleep Enable (8042EM_SLP_EN)                         */
      __IO uint32_t  RTC_SLP_EN :  1;               /*!< [18..18] RTC Sleep Enable (RTC_SLP_EN)                                */
      __IO uint32_t  ESPI_SLP_EN:  1;               /*!< [19..19] eSPI Sleep Enable                                            */
           uint32_t             :  1;
      __IO uint32_t  ACPI_EC_2_SLP_EN:  1;          /*!< [21..21] ACPI EC 2 Sleep Enable (ACPI_EC_2_SLP_EN)                    */
      __IO uint32_t  ACPI_EC_3_SLP_EN:  1;          /*!< [22..22] ACPI EC 3 Sleep Enable (ACPI_EC_3_SLP_EN)                    */
      __IO uint32_t  ACPI_EC_4_SLP_EN:  1;          /*!< [23..23] ACPI EC 4 Sleep Enable (ACPI_EC_4_SLP_EN)                    */
      __IO uint32_t  ASIF_SLP_EN:  1;               /*!< [24..24] ASIF Sleep Enable                                            */
      __IO uint32_t  PORT80_0_SLP_EN:  1;           /*!< [25..25] Port 80 0 Sleep Enable                                       */
      __IO uint32_t  PORT80_1_SLP_EN:  1;           /*!< [26..26] Port 80 1 Sleep Enable                                       */
    } SLP_EN_2_b;                                   /*!< [27] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  SLP_EN_3;                        /*!< (@ 0x4008013C) Sleep Enable 3 Register                                */
    
    struct {
           uint32_t             :  3;
      __IO uint32_t  ADC_SLP_EN :  1;               /*!< [3..3] ADC Sleep Enable (ADC_SLP_EN)                                  */
           uint32_t             :  1;
      __IO uint32_t  PS2_0_SLP_EN:  1;              /*!< [5..5] PS2_0 Sleep Enable (PS2_0_SLP_EN)                              */
      __IO uint32_t  PS2_1_SLP_EN:  1;              /*!< [6..6] PS2_1 Sleep Enable (PS2_1_SLP_EN)                              */
      __IO uint32_t  PS2_2_SLP_EN:  1;              /*!< [7..7] PS2_2 Sleep Enable (PS2_2_SLP_EN)                              */
           uint32_t             :  1;
      __IO uint32_t  GP_SPI0_SLP_EN:  1;            /*!< [9..9] GP SPI0 Sleep Enable (GP_SPI0_SLP_EN)                          */
      __IO uint32_t  HTIMER_0_SLP_EN:  1;           /*!< [10..10] HTIMER 0 Sleep Enable (HTIMER_0_SLP_EN)                      */
      __IO uint32_t  KEYSCAN_SLP_EN:  1;            /*!< [11..11] KEYSCAN Sleep Enable (KEYSCAN_SLP_EN)                        */
      __IO uint32_t  RPMPWM_SLP_EN:  1;             /*!< [12..12] RPM-PWM Sleep Enable (RPMPWM_SLP_EN)                         */
      __IO uint32_t  SMB1_SLP_EN:  1;               /*!< [13..13] SMB1 Sleep Enable (SMB1_SLP_EN)                              */
      __IO uint32_t  SMB2_SLP_EN:  1;               /*!< [14..14] SMB2 Sleep Enable (SMB2_SLP_EN)                              */
      __IO uint32_t  SMB3_SLP_EN:  1;               /*!< [15..15] SMB3 Sleep Enable (SMB3_SLP_EN)                              */
      __IO uint32_t  LED0_SLP_EN:  1;               /*!< [16..16] LED0 Sleep Enable (LED0_SLP_EN)                              */
      __IO uint32_t  LED1_SLP_EN:  1;               /*!< [17..17] LED1 Sleep Enable (LED1_SLP_EN)                              */
      __IO uint32_t  LED2_SLP_EN:  1;               /*!< [18..18] LED2 Sleep Enable (LED2_SLP_EN)                              */
      __IO uint32_t  BCM0_SLP_EN:  1;               /*!< [19..19] BCM 0 Sleep Enable (BCM0_SLP_EN)                             */
      __IO uint32_t  GP_SPI1_SLP_EN:  1;            /*!< [20..20] GP SPI1 Sleep Enable (GP_SPI1_SLP_EN)                        */
      __IO uint32_t  TIMER16_2_SLP_EN:  1;          /*!< [21..21] TIMER16_2_Sleep Enable (TIMER16_2_SLP_EN)                    */
      __IO uint32_t  TIMER16_3_SLP_EN:  1;          /*!< [22..22] TIMER16_3 Sleep Enable (TIMER16_3_SLP_EN)                    */
      __IO uint32_t  TIMER32_0_SLP_EN:  1;          /*!< [23..23] TIMER32_0 Sleep Enable (TIMER32_0_SLP_EN)                    */
      __IO uint32_t  TIMER32_1_SLP_EN:  1;          /*!< [24..24] TIMER32_1 Sleep Enable (TIMER32_1_SLP_EN)                    */
      __IO uint32_t  LED3_SLP_EN:  1;               /*!< [25..25] LED3 Sleep Enable (LED3_SLP_EN)                              */
      __IO uint32_t  PKE_SLP_EN :  1;               /*!< [26..26] PKE Sleep Enable                                             */
      __IO uint32_t  RNG_SLP_EN :  1;               /*!< [27..27] RNG Sleep Enable                                             */
      __IO uint32_t  AES_HASH_SLP_EN:  1;           /*!< [28..28] AES_HASH Sleep Enable                                        */
      __IO uint32_t  HTIMER_1_SLP_EN:  1;           /*!< [29..29] HTIMER 1 Sleep Enable (HTIMER_1_SLP_EN)                      */
      __IO uint32_t  CCTIMER_SLP_EN:  1;            /*!< [30..30] Capture Compare Timer Sleep Enable (CCTIMER_SLP_EN)
                                                                                                                               */
      __IO uint32_t  PWM9_SLP_EN:  1;               /*!< [31..31] PWM9 Sleep Enable (PWM9_SLP_EN)                              */
    } SLP_EN_3_b;                                   /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  SLP_EN_4;                        /*!< (@ 0x40080140) Sleep Enable 4 Register                                */
    
    struct {
      __IO uint32_t  PWM10_SLP_EN:  1;              /*!< [0..0] PWM10 Sleep Enable (PWM10_SLP_EN)                              */
      __IO uint32_t  PWM11_SLP_EN:  1;              /*!< [1..1] PWM11 Sleep Enable (PWM11_SLP_EN)                              */
      __IO uint32_t  CNT_TMER0_SLP_EN:  1;          /*!< [2..2] CNT_TMER0 Sleep Enable (CNT_TMER0_SLP_EN)                      */
      __IO uint32_t  CNT_TMER1_SLP_EN:  1;          /*!< [3..3] CNT_TMER1 Sleep Enable (CNT_TMER1_SLP_EN)                      */
      __IO uint32_t  CNT_TMER2_SLP_EN:  1;          /*!< [4..4] CNT_TMER2 Sleep Enable (CNT_TMER2_SLP_EN)                      */
      __IO uint32_t  CNT_TMER3_SLP_EN:  1;          /*!< [5..5] CNT_TMER3 Sleep Enable (CNT_TMER3_SLP_EN)                      */
      __IO uint32_t  RTOS_SLP_EN:  1;               /*!< [6..6] PWM6 Sleep Enable (RTOS_SLP_EN)                                */
      __IO uint32_t  RPMPWM1_SLP_EN:  1;            /*!< [7..7] RPMPWM 1 Sleep Enable (RPMPWM1_SLP_EN)                         */
      __IO uint32_t  QSPI_SLP_EN:  1;               /*!< [8..8] Quad SPI Sleep Enable                                          */
      __IO uint32_t  BCM1_SLP_EN:  1;               /*!< [9..9] BCM 1 Sleep Enable (BCM1_SLP_EN)                               */
      __IO uint32_t  RC_ID0_SLP_EN:  1;             /*!< [10..10] RC_ID0 Sleep Enable (RC_ID0_SLP_EN)                          */
      __IO uint32_t  RC_ID1_SLP_EN:  1;             /*!< [11..11] RC_ID1 Sleep Enable (RC_ID1_SLP_EN)                          */
      __IO uint32_t  RC_ID2_SLP_EN:  1;             /*!< [12..12] RC_ID2 Sleep Enable (RC_ID2_SLP_EN)                          */
           uint32_t             :  2;
      __IO uint32_t  FCL_SLP_EN :  1;               /*!< [15..15] FCL Sleep Enable (FCL_SLP_EN)                                */
    } SLP_EN_4_b;                                   /*!< [16] BitSize                                                          */
  };
  __I  uint32_t  RESERVED1[3];
  
  union {
    __IO uint32_t  CLK_REQ_0;                       /*!< (@ 0x40080150) Clock Required 0 Register                              */
    
    struct {
      __IO uint32_t  JTAG_STAP_CLK_REQ:  1;         /*!< [0..0] JTAG STAP Enable                                               */
      __IO uint32_t  EFUSE_CLK_REQ:  1;             /*!< [1..1] eFuse Enable                                                   */
      __IO uint32_t  ISPI_CLK_REQ:  1;              /*!< [2..2] ISPI Clock Required                                            */
    } CLK_REQ_0_b;                                  /*!< [3] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  CLK_REQ_1;                       /*!< (@ 0x40080154) Clock Required 1 Register                              */
    
    struct {
      __IO uint32_t  INT_CLK_REQ:  1;               /*!< [0..0] Interrupt Clock Required                                       */
      __IO uint32_t  PECI_CLK_REQ:  1;              /*!< [1..1] PECI Clock Required                                            */
      __IO uint32_t  TACH0_CLK_REQ:  1;             /*!< [2..2] TACH0 Clock Required (TACH0_CLK_REQ)                           */
           uint32_t             :  1;
      __IO uint32_t  PWM0_CLK_REQ:  1;              /*!< [4..4] PWM0 Clock Required (PWM0_CLK_REQ)                             */
      __IO uint32_t  PMC_CLK_REQ:  1;               /*!< [5..5] PMC Clock Required (PMC_CLK_REQ)                               */
      __IO uint32_t  DMA_CLK_REQ:  1;               /*!< [6..6] DMA Clock Required (DMA_CLK_REQ)                               */
      __IO uint32_t  TFDP_CLK_REQ:  1;              /*!< [7..7] TFDP Clock Required (TFDP_CLK_REQ)                             */
      __IO uint32_t  PROCESSOR_CLK_REQ:  1;         /*!< [8..8] PROCESSOR Clock Required (PROCESSOR_CLK_REQ)                   */
      __IO uint32_t  WDT_CLK_REQ:  1;               /*!< [9..9] WDT Clock Required (WDT_CLK_REQ)                               */
      __IO uint32_t  SMB0_CLK_REQ:  1;              /*!< [10..10] SMB0 Clock Required (SMB0_CLK_REQ)                           */
      __IO uint32_t  TACH1_CLK_REQ:  1;             /*!< [11..11] TACH1 Clock Required (TACH1_CLK_REQ)                         */
      __IO uint32_t  TACH2_CLK_REQ:  1;             /*!< [12..12] TACH2 Clock Required (TACH2_CLK_REQ)                         */
           uint32_t             :  7;
      __IO uint32_t  PWM1_CLK_REQ:  1;              /*!< [20..20] PWM1 Clock Required (PWM1_CLK_REQ)                           */
      __IO uint32_t  PWM2_CLK_REQ:  1;              /*!< [21..21] PWM2 Clock Required (PWM2_CLK_REQ)                           */
      __IO uint32_t  PWM3_CLK_REQ:  1;              /*!< [22..22] PWM3 Clock Required (PWM3_CLK_REQ)                           */
      __IO uint32_t  PWM4_CLK_REQ:  1;              /*!< [23..23] PWM4 Clock Required (PWM4_CLK_REQ)                           */
      __IO uint32_t  PWM5_CLK_REQ:  1;              /*!< [24..24] PWM3 Clock Required (PWM5_CLK_REQ)                           */
      __IO uint32_t  PWM6_CLK_REQ:  1;              /*!< [25..25] PWM3 Clock Required (PWM6_CLK_REQ)                           */
      __IO uint32_t  PWM7_CLK_REQ:  1;              /*!< [26..26] PWM3 Clock Required (PWM7_CLK_REQ)                           */
      __IO uint32_t  PWM8_CLK_REQ:  1;              /*!< [27..27] PWM3 Clock Required (PWM8_CLK_REQ)                           */
           uint32_t             :  1;
      __IO uint32_t  EC_REG_BANK_CLK_REQ:  1;       /*!< [29..29] EC_REG_BANK Clock Required (EC_REG_BANK_CLK_REQ)             */
      __IO uint32_t  TIMER16_0_CLK_REQ:  1;         /*!< [30..30] TIMER16_0 Clock Required (TIMER16_0_CLK_REQ)                 */
      __IO uint32_t  TIMER16_1_CLK_REQ:  1;         /*!< [31..31] TIMER16_1 Clock Required (TIMER16_1_CLK_REQ)                 */
    } CLK_REQ_1_b;                                  /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  CLK_REQ_2;                       /*!< (@ 0x40080158) Clock Required 2 Register                              */
    
    struct {
      __IO uint32_t  LPC_CLK_REQ:  1;               /*!< [0..0] LPC Clock Required (LPC_CLK_REQ)                               */
      __IO uint32_t  UART_0_CLK_REQ:  1;            /*!< [1..1] UART 0 Clock Required                                          */
      __IO uint32_t  UART_1_CLK_REQ:  1;            /*!< [2..2] UART 1 Clock Required                                          */
           uint32_t             :  9;
      __IO uint32_t  GLBL_CFG_CLK_REQ:  1;          /*!< [12..12] GLBL_CFG (GLBL_CFG_CLK_REQ)                                  */
      __IO uint32_t  ACPI_EC_0_CLK_REQ:  1;         /*!< [13..13] ACPI EC 0 Clock Required (ACPI_EC_0_CLK_REQ)                 */
      __IO uint32_t  ACPI_EC_1_CLK_REQ:  1;         /*!< [14..14] ACPI EC 1 Clock Required (ACPI_EC_1_CLK_REQ)                 */
      __IO uint32_t  ACPI_PM1_CLK_REQ:  1;          /*!< [15..15] ACPI PM1 Clock Required (ACPI_PM1_CLK_REQ)                   */
      __IO uint32_t  KBCEM_CLK_REQ:  1;             /*!< [16..16] 8042EM Clock Required (8042EM_CLK_REQ)                       */
      __IO uint32_t  MBX_CLK_REQ:  1;               /*!< [17..17] Mailbox Clock Required (8042EM_CLK_REQ)                      */
      __IO uint32_t  RTC_CLK_REQ:  1;               /*!< [18..18] RTC Clock Required (RTC_CLK_REQ)                             */
      __IO uint32_t  ESPI_CLK_REQ:  1;              /*!< [19..19] eSPI Clock Required                                          */
           uint32_t             :  1;
      __IO uint32_t  ACPI_EC_2_CLK_REQ:  1;         /*!< [21..21] ACPI EC 2 Clock Required (ACPI_EC_2_CLK_REQ)                 */
      __IO uint32_t  ACPI_EC_3_CLK_REQ:  1;         /*!< [22..22] ACPI EC 3 Clock Required (ACPI_EC_3_CLK_REQ)                 */
      __IO uint32_t  ACPI_EC_4_CLK_REQ:  1;         /*!< [23..23] ACPI EC 4 Clock Required (ACPI_EC_4_CLK_REQ)                 */
      __IO uint32_t  ASIF_CLK_REQ:  1;              /*!< [24..24] ASIF Clock Required                                          */
      __IO uint32_t  PORT80_0_CLK_REQ:  1;          /*!< [25..25] Port 80 0 Clock Required                                     */
      __IO uint32_t  PORT80_1_CLK_REQ:  1;          /*!< [26..26] Port 80 1 Clock Required                                     */
    } CLK_REQ_2_b;                                  /*!< [27] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  CLK_REQ_3;                       /*!< (@ 0x4008015C) Clock Required 3 Register                              */
    
    struct {
           uint32_t             :  3;
      __IO uint32_t  ADC_CLK_REQ:  1;               /*!< [3..3] ADC Clock Required (ADC_CLK_REQ)                               */
           uint32_t             :  1;
      __IO uint32_t  PS2_0_CLK_REQ:  1;             /*!< [5..5] PS2_0 Clock Required (PS2_0_CLK_REQ)                           */
      __IO uint32_t  PS2_1_CLK_REQ:  1;             /*!< [6..6] PS2_1 Clock Required (PS2_1_CLK_REQ)                           */
      __IO uint32_t  PS2_2_CLK_REQ:  1;             /*!< [7..7] PS2_2 Clock Required (PS2_2_CLK_REQ)                           */
           uint32_t             :  1;
      __IO uint32_t  GP_SPI0_CLK_REQ:  1;           /*!< [9..9] GP SPI0 Clock Required (GP_SPI0_CLK_REQ)                       */
      __IO uint32_t  HTIMER_0_CLK_REQ:  1;          /*!< [10..10] HTIMER 0 Clock Required (HTIMER_0_CLK_REQ)                   */
      __IO uint32_t  KEYSCAN_CLK_REQ:  1;           /*!< [11..11] KEYSCAN Clock Required (KEYSCAN_CLK_REQ)                     */
      __IO uint32_t  RPMPWM0_CLK_REQ:  1;           /*!< [12..12] RPM-PWM 0 Clock Required (RPMPWM0_CLK_REQ)                   */
      __IO uint32_t  SMB1_CLK_REQ:  1;              /*!< [13..13] SMB1 Clock Required (SMB1_CLK_REQ)                           */
      __IO uint32_t  SMB2_CLK_REQ:  1;              /*!< [14..14] SMB2 Clock Required (SMB2_CLK_REQ)                           */
      __IO uint32_t  SMB3_CLK_REQ:  1;              /*!< [15..15] SMB3 Clock Required (SMB3_CLK_REQ)                           */
      __IO uint32_t  LED0_CLK_REQ:  1;              /*!< [16..16] LED0 Clock Required (LED0_CLK_REQ)                           */
      __IO uint32_t  LED1_CLK_REQ:  1;              /*!< [17..17] LED1 Clock Required (LED1_CLK_REQ)                           */
      __IO uint32_t  LED2_CLK_REQ:  1;              /*!< [18..18] LED2 Clock Required (LED2_CLK_REQ)                           */
      __IO uint32_t  BCM0_CLK_REQ:  1;              /*!< [19..19] BCM 0 Clock Required (BCM0_CLK_REQ)                          */
      __IO uint32_t  GP_SPI1_CLK_REQ:  1;           /*!< [20..20] GP SPI1 Clock Required (GP_SPI1_CLK_REQ)                     */
      __IO uint32_t  TIMER16_2_CLK_REQ:  1;         /*!< [21..21] TIMER16_2_Clock Required (TIMER16_2_CLK_REQ)                 */
      __IO uint32_t  TIMER16_3_CLK_REQ:  1;         /*!< [22..22] TIMER16_3 Clock Required (TIMER16_3_CLK_REQ)                 */
      __IO uint32_t  TIMER32_0_CLK_REQ:  1;         /*!< [23..23] TIMER32_0 Clock Required (TIMER32_0_CLK_REQ)                 */
      __IO uint32_t  TIMER32_1_CLK_REQ:  1;         /*!< [24..24] TIMER32_1 Clock Required (TIMER32_1_CLK_REQ)                 */
      __IO uint32_t  LED3_CLK_REQ:  1;              /*!< [25..25] LED3 Clock Required (LED3_CLK_REQ)                           */
      __IO uint32_t  PKE_CLK_REQ:  1;               /*!< [26..26] PKE Clock Required                                           */
      __IO uint32_t  RNG_CLK_REQ:  1;               /*!< [27..27] RNG Clock Required                                           */
      __IO uint32_t  AES_HASH_CLK_REQ:  1;          /*!< [28..28] AES_HASH Clock Required                                      */
      __IO uint32_t  HTIMER_1_CLK_REQ:  1;          /*!< [29..29] HTIMER 1 Clock Required (HTIMER_1_CLK_REQ)                   */
      __IO uint32_t  CCTIMER_CLK_REQ:  1;           /*!< [30..30] Capture Compare Timer Clock Required (CCTIMER_CLK_REQ)
                                                                                                                               */
      __IO uint32_t  PWM9_CLK_REQ:  1;              /*!< [31..31] PWM9 Clock Required (PWM9_CLK_REQ)                           */
    } CLK_REQ_3_b;                                  /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  CLK_REQ_4;                       /*!< (@ 0x40080160) Clock Required 4 Register                              */
    
    struct {
      __IO uint32_t  PWM10_CLK_REQ:  1;             /*!< [0..0] PWM10 Clock Required (PWM10_CLK_REQ)                           */
      __IO uint32_t  PWM11_CLK_REQ:  1;             /*!< [1..1] PWM11 Clock Required (PWM11_CLK_REQ)                           */
      __IO uint32_t  CNT_TMER0_CLK_REQ:  1;         /*!< [2..2] CNT_TMER0 Clock Required (CNT_TMER0_CLK_REQ)                   */
      __IO uint32_t  CNT_TMER1_CLK_REQ:  1;         /*!< [3..3] CNT_TMER1 Clock Required (CNT_TMER1_CLK_REQ)                   */
      __IO uint32_t  CNT_TMER2_CLK_REQ:  1;         /*!< [4..4] CNT_TMER2 Clock Required (CNT_TMER2_CLK_REQ)                   */
      __IO uint32_t  CNT_TMER3_CLK_REQ:  1;         /*!< [5..5] CNT_TMER3 Clock Required (CNT_TMER3_CLK_REQ)                   */
      __IO uint32_t  RTOS_CLK_REQ:  1;              /*!< [6..6] RTOS Clock Required (RTOS_CLK_REQ)                             */
      __IO uint32_t  RPMPWM1_CLK_REQ:  1;           /*!< [7..7] RPM-PWM1 Clock Required (RPMPWM1_CLK_REQ)                      */
      __IO uint32_t  QSPI_CLK_REQ:  1;              /*!< [8..8] Quad SPI Clock Required                                        */
      __IO uint32_t  BCM1_CLK_REQ:  1;              /*!< [9..9] BCM 1 Clock Required (BCM1_CLK_REQ)                            */
      __IO uint32_t  RC_ID0_CLK_REQ:  1;            /*!< [10..10] RC_ID0 Clock Required (RC_ID0_CLK_REQ)                       */
      __IO uint32_t  RC_ID1_CLK_REQ:  1;            /*!< [11..11] RC_ID1 Clock Required (RC_ID1_CLK_REQ)                       */
      __IO uint32_t  RC_ID2_CLK_REQ:  1;            /*!< [12..12] RC_ID2 Clock Required (RC_ID2_CLK_REQ)                       */
           uint32_t             :  2;
      __IO uint32_t  FCL_CLK_REQ:  1;               /*!< [15..15] FCL Clock Required (FCL_CLK_REQ)                             */
    } CLK_REQ_4_b;                                  /*!< [16] BitSize                                                          */
  };
  __I  uint32_t  RESERVED2[3];
  
  union {
    __IO uint32_t  RST_EN_0;                        /*!< (@ 0x40080170) Reset Enable 0 Register                                */
    
    struct {
      __IO uint32_t  JTAG_STAP_RST_EN:  1;          /*!< [0..0] JTAG STAP Reset Enable                                         */
      __IO uint32_t  EFUSE_RST_EN:  1;              /*!< [1..1] eFuse Reset Enable                                             */
      __IO uint32_t  ISPI_RST_EN:  1;               /*!< [2..2] ISPI Reset Enable                                              */
    } RST_EN_0_b;                                   /*!< [3] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  RST_EN_1;                        /*!< (@ 0x40080174) Reset Enable 1 Register                                */
    
    struct {
      __IO uint32_t  INT_RST_EN :  1;               /*!< [0..0] Interrupt Reset Enable                                         */
      __IO uint32_t  PECI_RST_EN:  1;               /*!< [1..1] PECI Reset Enable                                              */
      __IO uint32_t  TACH0_RST_EN:  1;              /*!< [2..2] TACH0 Reset Enable (TACH0_RST_EN)                              */
           uint32_t             :  1;
      __IO uint32_t  PWM0_RST_EN:  1;               /*!< [4..4] PWM0 Reset Enable (PWM0_RST_EN)                                */
      __IO uint32_t  PMC_RST_EN :  1;               /*!< [5..5] PMC Reset Enable (PMC_RST_EN)                                  */
      __IO uint32_t  DMA_RST_EN :  1;               /*!< [6..6] DMA Reset Enable (DMA_RST_EN)                                  */
      __IO uint32_t  TFDP_RST_EN:  1;               /*!< [7..7] TFDP Reset Enable (TFDP_RST_EN)                                */
      __IO uint32_t  PROCESSOR_RST_EN:  1;          /*!< [8..8] PROCESSOR Reset Enable (PROCESSOR_RST_EN)                      */
      __IO uint32_t  WDT_RST_EN :  1;               /*!< [9..9] WDT Reset Enable (WDT_RST_EN)                                  */
      __IO uint32_t  SMB0_RST_EN:  1;               /*!< [10..10] SMB0 Reset Enable (SMB0_RST_EN)                              */
      __IO uint32_t  TACH1_RST_EN:  1;              /*!< [11..11] TACH1 Reset Enable (TACH1_RST_EN)                            */
      __IO uint32_t  TACH2_RST_EN:  1;              /*!< [12..12] TACH2 Reset Enable (TACH2_RST_EN)                            */
           uint32_t             :  7;
      __IO uint32_t  PWM1_RST_EN:  1;               /*!< [20..20] PWM1 Reset Enable (PWM1_RST_EN)                              */
      __IO uint32_t  PWM2_RST_EN:  1;               /*!< [21..21] PWM2 Reset Enable (PWM2_RST_EN)                              */
      __IO uint32_t  PWM3_RST_EN:  1;               /*!< [22..22] PWM3 Reset Enable (PWM3_RST_EN)                              */
      __IO uint32_t  PWM4_RST_EN:  1;               /*!< [23..23] PWM4 Reset Enable (PWM4_RST_EN)                              */
      __IO uint32_t  PWM5_RST_EN:  1;               /*!< [24..24] PWM3 Reset Enable (PWM5_RST_EN)                              */
      __IO uint32_t  PWM6_RST_EN:  1;               /*!< [25..25] PWM3 Reset Enable (PWM6_RST_EN)                              */
      __IO uint32_t  PWM7_RST_EN:  1;               /*!< [26..26] PWM3 Reset Enable (PWM7_RST_EN)                              */
      __IO uint32_t  PWM8_RST_EN:  1;               /*!< [27..27] PWM3 Reset Enable (PWM8_RST_EN)                              */
           uint32_t             :  1;
      __IO uint32_t  EC_REG_BANK_RST_EN:  1;        /*!< [29..29] EC_REG_BANK Reset Enable (EC_REG_BANK_RST_EN)                */
      __IO uint32_t  TIMER16_0_RST_EN:  1;          /*!< [30..30] TIMER16_0 Reset Enable (TIMER16_0_RST_EN)                    */
      __IO uint32_t  TIMER16_1_RST_EN:  1;          /*!< [31..31] TIMER16_1 Reset Enable (TIMER16_1_RST_EN)                    */
    } RST_EN_1_b;                                   /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  RST_EN_2;                        /*!< (@ 0x40080178) Reset Enable 2 Register                                */
    
    struct {
      __IO uint32_t  LPC_RST_EN :  1;               /*!< [0..0] LPC Reset Enable (LPC_RST_EN)                                  */
      __IO uint32_t  UART_0_RST_EN:  1;             /*!< [1..1] UART 0 Reset Enable                                            */
      __IO uint32_t  UART_1_RST_EN:  1;             /*!< [2..2] UART 1 Reset Enable                                            */
           uint32_t             :  9;
      __IO uint32_t  GLBL_CFG_RST_EN:  1;           /*!< [12..12] GLBL_CFG (GLBL_CFG_RST_EN)                                   */
      __IO uint32_t  ACPI_EC_0_RST_EN:  1;          /*!< [13..13] ACPI EC 0 Reset Enable (ACPI_EC_0_RST_EN)                    */
      __IO uint32_t  ACPI_EC_1_RST_EN:  1;          /*!< [14..14] ACPI EC 1 Reset Enable (ACPI_EC_1_RST_EN)                    */
      __IO uint32_t  ACPI_PM1_RST_EN:  1;           /*!< [15..15] ACPI PM1 Reset Enable (ACPI_PM1_RST_EN)                      */
      __IO uint32_t  KBCEM_RST_EN:  1;              /*!< [16..16] 8042EM Reset Enable (8042EM_RST_EN)                          */
      __IO uint32_t  MBX_RST_EN :  1;               /*!< [17..17] Mailbox Reset Enable (8042EM_RST_EN)                         */
      __IO uint32_t  RTC_RST_EN :  1;               /*!< [18..18] RTC Reset Enable (RTC_RST_EN)                                */
      __IO uint32_t  ESPI_RST_EN:  1;               /*!< [19..19] eSPI Reset Enable                                            */
           uint32_t             :  1;
      __IO uint32_t  ACPI_EC_2_RST_EN:  1;          /*!< [21..21] ACPI EC 2 Reset Enable (ACPI_EC_2_RST_EN)                    */
      __IO uint32_t  ACPI_EC_3_RST_EN:  1;          /*!< [22..22] ACPI EC 3 Reset Enable (ACPI_EC_3_RST_EN)                    */
      __IO uint32_t  ACPI_EC_4_RST_EN:  1;          /*!< [23..23] ACPI EC 4 Reset Enable (ACPI_EC_4_RST_EN)                    */
      __IO uint32_t  ASIF_RST_EN:  1;               /*!< [24..24] ASIF Reset Enable                                            */
      __IO uint32_t  PORT80_0_RST_EN:  1;           /*!< [25..25] Port 80 0 Reset Enable                                       */
      __IO uint32_t  PORT80_1_RST_EN:  1;           /*!< [26..26] Port 80 1 Reset Enable                                       */
    } RST_EN_2_b;                                   /*!< [27] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  RST_EN_3;                        /*!< (@ 0x4008017C) Reset Enable 3 Register                                */
    
    struct {
           uint32_t             :  3;
      __IO uint32_t  ADC_RST_EN :  1;               /*!< [3..3] ADC Reset Enable (ADC_RST_EN)                                  */
           uint32_t             :  1;
      __IO uint32_t  PS2_0_RST_EN:  1;              /*!< [5..5] PS2_0 Reset Enable (PS2_0_RST_EN)                              */
      __IO uint32_t  PS2_1_RST_EN:  1;              /*!< [6..6] PS2_1 Reset Enable (PS2_1_RST_EN)                              */
      __IO uint32_t  PS2_2_RST_EN:  1;              /*!< [7..7] PS2_2 Reset Enable (PS2_2_RST_EN)                              */
           uint32_t             :  1;
      __IO uint32_t  GP_SPI0_RST_EN:  1;            /*!< [9..9] GP SPI0 Reset Enable (GP_SPI0_RST_EN)                          */
      __IO uint32_t  HTIMER_0_RST_EN:  1;           /*!< [10..10] HTIMER 0 Reset Enable (HTIMER_0_RST_EN)                      */
      __IO uint32_t  KEYSCAN_RST_EN:  1;            /*!< [11..11] KEYSCAN Reset Enable (KEYSCAN_RST_EN)                        */
      __IO uint32_t  RPMPWM0_RST_EN:  1;            /*!< [12..12] RPM-PWM 0 Reset Enable (RPMPWM0_RST_EN)                      */
      __IO uint32_t  SMB1_RST_EN:  1;               /*!< [13..13] SMB1 Reset Enable (SMB1_RST_EN)                              */
      __IO uint32_t  SMB2_RST_EN:  1;               /*!< [14..14] SMB2 Reset Enable (SMB2_RST_EN)                              */
      __IO uint32_t  SMB3_RST_EN:  1;               /*!< [15..15] SMB3 Reset Enable (SMB3_RST_EN)                              */
      __IO uint32_t  LED0_RST_EN:  1;               /*!< [16..16] LED0 Reset Enable (LED0_RST_EN)                              */
      __IO uint32_t  LED1_RST_EN:  1;               /*!< [17..17] LED1 Reset Enable (LED1_RST_EN)                              */
      __IO uint32_t  LED2_RST_EN:  1;               /*!< [18..18] LED2 Reset Enable (LED2_RST_EN)                              */
      __IO uint32_t  BCM0_RST_EN:  1;               /*!< [19..19] BCM 0 Reset Enable (BCM0_RST_EN)                             */
      __IO uint32_t  GP_SPI1_RST_EN:  1;            /*!< [20..20] GP SPI1 Reset Enable (GP_SPI1_RST_EN)                        */
      __IO uint32_t  TIMER16_2_RST_EN:  1;          /*!< [21..21] TIMER16_2_Reset Enable (TIMER16_2_RST_EN)                    */
      __IO uint32_t  TIMER16_3_RST_EN:  1;          /*!< [22..22] TIMER16_3 Reset Enable (TIMER16_3_RST_EN)                    */
      __IO uint32_t  TIMER32_0_RST_EN:  1;          /*!< [23..23] TIMER32_0 Reset Enable (TIMER32_0_RST_EN)                    */
      __IO uint32_t  TIMER32_1_RST_EN:  1;          /*!< [24..24] TIMER32_1 Reset Enable (TIMER32_1_RST_EN)                    */
      __IO uint32_t  LED3_RST_EN:  1;               /*!< [25..25] LED3 Reset Enable (LED3_RST_EN)                              */
      __IO uint32_t  PKE_RST_EN :  1;               /*!< [26..26] PKE Reset Enable                                             */
      __IO uint32_t  RNG_RST_EN :  1;               /*!< [27..27] RNG Reset Enable                                             */
      __IO uint32_t  AES_HASH_RST_EN:  1;           /*!< [28..28] AES_HASH Reset Enable                                        */
      __IO uint32_t  HTIMER_1_RST_EN:  1;           /*!< [29..29] HTIMER 1 Reset Enable (HTIMER_1_RST_EN)                      */
      __IO uint32_t  CCTIMER_RST_EN:  1;            /*!< [30..30] Capture Compare Timer Reset Enable (CCTIMER_RST_EN)
                                                                                                                               */
      __IO uint32_t  PWM9_RST_EN:  1;               /*!< [31..31] PWM9 Reset Enable (PWM9_RST_EN)                              */
    } RST_EN_3_b;                                   /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  RST_EN_4;                        /*!< (@ 0x40080180) Reset Enable 4 Register                                */
    
    struct {
      __IO uint32_t  PWM10_RST_EN:  1;              /*!< [0..0] PWM10 Reset Enable (PWM10_RST_EN)                              */
      __IO uint32_t  PWM11_RST_EN:  1;              /*!< [1..1] PWM11 Reset Enable (PWM11_RST_EN)                              */
      __IO uint32_t  CNT_TMER0_RST_EN:  1;          /*!< [2..2] CNT_TMER0 Reset Enable (CNT_TMER0_RST_EN)                      */
      __IO uint32_t  CNT_TMER1_RST_EN:  1;          /*!< [3..3] CNT_TMER1 Reset Enable (CNT_TMER1_RST_EN)                      */
      __IO uint32_t  CNT_TMER2_RST_EN:  1;          /*!< [4..4] CNT_TMER2 Reset Enable (CNT_TMER2_RST_EN)                      */
      __IO uint32_t  CNT_TMER3_RST_EN:  1;          /*!< [5..5] CNT_TMER3 Reset Enable (CNT_TMER3_RST_EN)                      */
      __IO uint32_t  RTOS_RST_EN:  1;               /*!< [6..6] RTOS Reset Enable (RTOS_RST_EN)                                */
      __IO uint32_t  RPMPWM1_RST_EN:  1;            /*!< [7..7] RPM-PWM1 Reset Enable (RPMPWM1_RST_EN)                         */
      __IO uint32_t  QSPI_RST_EN:  1;               /*!< [8..8] Quad SPI Reset Enable                                          */
      __IO uint32_t  BCM1_RST_EN:  1;               /*!< [9..9] BCM 1 Reset Enable (BCM1_RST_EN)                               */
      __IO uint32_t  RC_ID0_RST_EN:  1;             /*!< [10..10] RC_ID0 Reset Enable (RC_ID0_RST_EN)                          */
      __IO uint32_t  RC_ID1_RST_EN:  1;             /*!< [11..11] RC_ID1 Reset Enable (RC_ID1_RST_EN)                          */
      __IO uint32_t  RC_ID2_RST_EN:  1;             /*!< [12..12] RC_ID2 Reset Enable (RC_ID2_RST_EN)                          */
           uint32_t             :  2;
      __IO uint32_t  FCL_RST_EN :  1;               /*!< [15..15] FCL Reset Enable (FCL_RST_EN)                                */
    } RST_EN_4_b;                                   /*!< [16] BitSize                                                          */
  };
} PCR_Type;


/* ================================================================================ */
/* ================                      INTS                      ================ */
/* ================================================================================ */


/**
  * @brief The interrupt generation logic is made of 16 groups of signals, each of which
 consist of a Status register, a Enable register and a Result register. The Status and Enable are
 latched registers. The Result register is a bit by bit AND function of the Source and Enable registers.
 All the bits of the Result register are OR'ed together and AND'ed with the corresponding bit in the Block
 Select register to form the interrupt signal that is routed to the ARM interrupt controller.  (INTS)
  */

typedef struct {                                    /*!< (@ 0x4000E000) INTS Structure                                         */
  __IO uint32_t  GIRQ08_SRC;                        /*!< (@ 0x4000E000) Status R/W1C                                           */
  __IO uint32_t  GIRQ08_EN_SET;                     /*!< (@ 0x4000E004) Write to set source enables                            */
  __I  uint32_t  GIRQ08_RESULT;                     /*!< (@ 0x4000E008) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ08_EN_CLR;                     /*!< (@ 0x4000E00C) Write to clear source enables                          */
  __I  uint32_t  RESERVED;
  __IO uint32_t  GIRQ09_SRC;                        /*!< (@ 0x4000E014) Status R/W1C                                           */
  __IO uint32_t  GIRQ09_EN_SET;                     /*!< (@ 0x4000E018) Write to set source enables                            */
  __I  uint32_t  GIRQ09_RESULT;                     /*!< (@ 0x4000E01C) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ09_EN_CLR;                     /*!< (@ 0x4000E020) Write to clear source enables                          */
  __I  uint32_t  RESERVED1;
  __IO uint32_t  GIRQ10_SRC;                        /*!< (@ 0x4000E028) Status R/W1C                                           */
  __IO uint32_t  GIRQ10_EN_SET;                     /*!< (@ 0x4000E02C) Write to set source enables                            */
  __I  uint32_t  GIRQ10_RESULT;                     /*!< (@ 0x4000E030) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ10_EN_CLR;                     /*!< (@ 0x4000E034) Write to clear source enables                          */
  __I  uint32_t  RESERVED2;
  __IO uint32_t  GIRQ11_SRC;                        /*!< (@ 0x4000E03C) Status R/W1C                                           */
  __IO uint32_t  GIRQ11_EN_SET;                     /*!< (@ 0x4000E040) Write to set source enables                            */
  __I  uint32_t  GIRQ11_RESULT;                     /*!< (@ 0x4000E044) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ11_EN_CLR;                     /*!< (@ 0x4000E048) Write to clear source enables                          */
  __I  uint32_t  RESERVED3;
  __IO uint32_t  GIRQ12_SRC;                        /*!< (@ 0x4000E050) Status R/W1C                                           */
  __IO uint32_t  GIRQ12_EN_SET;                     /*!< (@ 0x4000E054) Write to set source enables                            */
  __I  uint32_t  GIRQ12_RESULT;                     /*!< (@ 0x4000E058) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ12_EN_CLR;                     /*!< (@ 0x4000E05C) Write to clear source enables                          */
  __I  uint32_t  RESERVED4;
  __IO uint32_t  GIRQ13_SRC;                        /*!< (@ 0x4000E064) Status R/W1C                                           */
  __IO uint32_t  GIRQ13_EN_SET;                     /*!< (@ 0x4000E068) Write to set source enables                            */
  __I  uint32_t  GIRQ13_RESULT;                     /*!< (@ 0x4000E06C) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ13_EN_CLR;                     /*!< (@ 0x4000E070) Write to clear source enables                          */
  __I  uint32_t  RESERVED5;
  __IO uint32_t  GIRQ14_SRC;                        /*!< (@ 0x4000E078) Status R/W1C                                           */
  __IO uint32_t  GIRQ14_EN_SET;                     /*!< (@ 0x4000E07C) Write to set source enables                            */
  __I  uint32_t  GIRQ14_RESULT;                     /*!< (@ 0x4000E080) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ14_EN_CLR;                     /*!< (@ 0x4000E084) Write to clear source enables                          */
  __I  uint32_t  RESERVED6;
  __IO uint32_t  GIRQ15_SRC;                        /*!< (@ 0x4000E08C) Status R/W1C                                           */
  __IO uint32_t  GIRQ15_EN_SET;                     /*!< (@ 0x4000E090) Write to set source enables                            */
  __I  uint32_t  GIRQ15_RESULT;                     /*!< (@ 0x4000E094) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ15_EN_CLR;                     /*!< (@ 0x4000E098) Write to clear source enables                          */
  __I  uint32_t  RESERVED7;
  __IO uint32_t  GIRQ16_SRC;                        /*!< (@ 0x4000E0A0) Status R/W1C                                           */
  __IO uint32_t  GIRQ16_EN_SET;                     /*!< (@ 0x4000E0A4) Write to set source enables                            */
  __I  uint32_t  GIRQ16_RESULT;                     /*!< (@ 0x4000E0A8) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ16_EN_CLR;                     /*!< (@ 0x4000E0AC) Write to clear source enables                          */
  __I  uint32_t  RESERVED8;
  __IO uint32_t  GIRQ17_SRC;                        /*!< (@ 0x4000E0B4) Status R/W1C                                           */
  __IO uint32_t  GIRQ17_EN_SET;                     /*!< (@ 0x4000E0B8) Write to set source enables                            */
  __I  uint32_t  GIRQ17_RESULT;                     /*!< (@ 0x4000E0BC) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ17_EN_CLR;                     /*!< (@ 0x4000E0C0) Write to clear source enables                          */
  __I  uint32_t  RESERVED9;
  __IO uint32_t  GIRQ18_SRC;                        /*!< (@ 0x4000E0C8) Status R/W1C                                           */
  __IO uint32_t  GIRQ18_EN_SET;                     /*!< (@ 0x4000E0CC) Write to set source enables                            */
  __I  uint32_t  GIRQ18_RESULT;                     /*!< (@ 0x4000E0D0) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ18_EN_CLR;                     /*!< (@ 0x4000E0D4) Write to clear source enables                          */
  __I  uint32_t  RESERVED10;
  __IO uint32_t  GIRQ19_SRC;                        /*!< (@ 0x4000E0DC) Status R/W1C                                           */
  __IO uint32_t  GIRQ19_EN_SET;                     /*!< (@ 0x4000E0E0) Write to set source enables                            */
  __I  uint32_t  GIRQ19_RESULT;                     /*!< (@ 0x4000E0E4) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ19_EN_CLR;                     /*!< (@ 0x4000E0E8) Write to clear source enables                          */
  __I  uint32_t  RESERVED11;
  __IO uint32_t  GIRQ20_SRC;                        /*!< (@ 0x4000E0F0) Status R/W1C                                           */
  __IO uint32_t  GIRQ20_EN_SET;                     /*!< (@ 0x4000E0F4) Write to set source enables                            */
  __I  uint32_t  GIRQ20_RESULT;                     /*!< (@ 0x4000E0F8) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ20_EN_CLR;                     /*!< (@ 0x4000E0FC) Write to clear source enables                          */
  __I  uint32_t  RESERVED12;
  __IO uint32_t  GIRQ21_SRC;                        /*!< (@ 0x4000E104) Status R/W1C                                           */
  __IO uint32_t  GIRQ21_EN_SET;                     /*!< (@ 0x4000E108) Write to set source enables                            */
  __I  uint32_t  GIRQ21_RESULT;                     /*!< (@ 0x4000E10C) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ21_EN_CLR;                     /*!< (@ 0x4000E110) Write to clear source enables                          */
  __I  uint32_t  RESERVED13;
  __IO uint32_t  GIRQ22_SRC;                        /*!< (@ 0x4000E118) Status R/W1C                                           */
  __IO uint32_t  GIRQ22_EN_SET;                     /*!< (@ 0x4000E11C) Write to set source enables                            */
  __I  uint32_t  GIRQ22_RESULT;                     /*!< (@ 0x4000E120) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ22_EN_CLR;                     /*!< (@ 0x4000E124) Write to clear source enables                          */
  __I  uint32_t  RESERVED14;
  __IO uint32_t  GIRQ23_SRC;                        /*!< (@ 0x4000E12C) Status R/W1C                                           */
  __IO uint32_t  GIRQ23_EN_SET;                     /*!< (@ 0x4000E130) Write to set source enables                            */
  __I  uint32_t  GIRQ23_RESULT;                     /*!< (@ 0x4000E134) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ23_EN_CLR;                     /*!< (@ 0x4000E138) Write to clear source enables                          */
  __I  uint32_t  RESERVED15;
  __IO uint32_t  GIRQ24_SRC;                        /*!< (@ 0x4000E140) Status R/W1C                                           */
  __IO uint32_t  GIRQ24_EN_SET;                     /*!< (@ 0x4000E144) Write to set source enables                            */
  __I  uint32_t  GIRQ24_RESULT;                     /*!< (@ 0x4000E148) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ24_EN_CLR;                     /*!< (@ 0x4000E14C) Write to clear source enables                          */
  __I  uint32_t  RESERVED16;
  __IO uint32_t  GIRQ25_SRC;                        /*!< (@ 0x4000E154) Status R/W1C                                           */
  __IO uint32_t  GIRQ25_EN_SET;                     /*!< (@ 0x4000E158) Write to set source enables                            */
  __I  uint32_t  GIRQ25_RESULT;                     /*!< (@ 0x4000E15C) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ25_EN_CLR;                     /*!< (@ 0x4000E160) Write to clear source enables                          */
  __I  uint32_t  RESERVED17;
  __IO uint32_t  GIRQ26_SRC;                        /*!< (@ 0x4000E168) Status R/W1C                                           */
  __IO uint32_t  GIRQ26_EN_SET;                     /*!< (@ 0x4000E16C) Write to set source enables                            */
  __I  uint32_t  GIRQ26_RESULT;                     /*!< (@ 0x4000E170) Read-only bitwise OR of Source and Enable              */
  __IO uint32_t  GIRQ26_EN_CLR;                     /*!< (@ 0x4000E174) Write to clear source enables                          */
  __I  uint32_t  RESERVED18[34];
  
  union {
    __IO uint32_t  BLOCK_ENABLE_SET;                /*!< (@ 0x4000E200) Block Enable Set Register                              */
    
    struct {
      __IO uint32_t  IRQ_VECTOR_ENABLE_SET: 31;     /*!< [0..30] Each GIRQx bit can be individually enabled to assert
                                                         an interrupt event.
                                                          Reads always return the current value of the internal GIRQX_ENABLE
                                                          bit. The state of the GIRQX_ENABLE bit is determined by
                                                          the corresponding GIRQX_ENABLE_SET bit and the GIRQX_ENABLE_
                                                          CLEAR bit. (0=disabled, 1=enabled) (R/WS)
                                                          1=Interrupts in the GIRQx Source Register may be enabled
                                                          0=No effect.                                                         */
    } BLOCK_ENABLE_SET_b;                           /*!< [31] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  BLOCK_ENABLE_CLEAR;              /*!< (@ 0x4000E204) Block Enable Clear Register.                           */
    
    struct {
      __IO uint32_t  IRQ_VECTOR_ENABLE_CLEAR: 31;   /*!< [0..30] Each GIRQx bit can be individually disabled to inhibit
                                                         an interrupt event.
                                                          Reads always return the current value of the internal GIRQX_ENABLE
                                                          bit. The state of the GIRQX_ENABLE bit is determined by
                                                          the corresponding GIRQX_ENABLE_SET bit and the GIRQX_ENABLE_
                                                          CLEAR bit. (0=disabled, 1=enabled) (R/WC)
                                                          1=All interrupts in the GIRQx Source Register are disabled
                                                          0=No effect.                                                         */
    } BLOCK_ENABLE_CLEAR_b;                         /*!< [31] BitSize                                                          */
  };
  
  union {
    __I  uint32_t  BLOCK_IRQ_VECTOR;                /*!< (@ 0x4000E208) Block IRQ Vector Register                              */
    
    struct {
      __I  uint32_t  IRQ_VECTOR : 25;               /*!< [0..24] Each bit in this field reports the status of the group
                                                         GIRQ interrupt assertion to the NVIC. If the GIRQx interrupt
                                                          is disabled as a group, by the Block Enable Clear Register,
                                                          then the corresponding bit will be '0'b and no interrupt will
                                                          be asserted.                                                         */
    } BLOCK_IRQ_VECTOR_b;                           /*!< [25] BitSize                                                          */
  };
} INTS_Type;


/* ================================================================================ */
/* ================                     TIMER0                     ================ */
/* ================================================================================ */


/**
  * @brief This timer block offers a simple mechanism for firmware to maintain a time base. This timer may be instantiated as 16 bits or
 32 bits. The name of the timer instance indicates the size of the timer.  (TIMER0)
  */

typedef struct {                                    /*!< (@ 0x40000C00) TIMER0 Structure                                       */
  __IO uint32_t  COUNT;                             /*!< (@ 0x40000C00) This is the value of the Timer counter. This
                                                         is updated by Hardware but may be set by Firmware.                    */
  __IO uint32_t  PRE_LOAD;                          /*!< (@ 0x40000C04) This is the value of the Timer pre-load for the
                                                         counter. This is used by H/W when the counter is to be restarted
                                                         automatically; this will become the new value of the counter
                                                          upon restart.                                                        */
  
  union {
    __IO uint32_t  STATUS;                          /*!< (@ 0x40000C08) This is the interrupt status that fires when
                                                         the timer reaches its limit                                           */
    
    struct {
      __IO uint32_t  EVENT_INTERRUPT:  1;           /*!< [0..0] This is the interrupt status that fires when the timer
                                                         reaches its limit. This is the interrupt status that fires when
                                                          the timer reaches its limit. This may be level or a self clearing
                                                          signal cycle pulse, based on the AUTO_RESTART bit in the Timer
                                                          Control Register. If the timer is set to automatically restart,
                                                          it will provide a pulse, otherwise a level is provided.(R/WC)
                                                                                                                               */
    } STATUS_b;                                     /*!< [1] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  INT_EN;                          /*!< (@ 0x40000C0C) This is the interrupt enable for the status EVENT_INTERRUPT
                                                         bit in the Timer Status Register                                      */
    
    struct {
      __IO uint32_t  ENABLE     :  1;               /*!< [0..0] This is the interrupt enable for the status EVENT_INTERRUPT
                                                         bit in the Timer Status Register.                                     */
    } INT_EN_b;                                     /*!< [1] BitSize                                                           */
  };
  
  union {
    __IO REG32_U  CONTROL;                         /*!< (@ 0x40000C10) Timer Control Register                                 */
    
    struct {
      __IO uint32_t  ENABLE     :  1;               /*!< [0..0] This enables the block for operation. 1=This block will
                                                         function normally;
                                                         0=This block will gate its clock and go into its lowest power
                                                          state                                                                */
           uint32_t             :  1;
      __IO uint32_t  COUNT_UP   :  1;               /*!< [2..2] This selects the counter direction. When the counter
                                                         in incrementing the counter will saturate and trigger the event
                                                         when it reaches all F's. When the counter is decrementing the
                                                          counter will saturate when it reaches 0h. 1=The counter will
                                                          increment;
                                                         0=The counter will decrement                                          */
      __IO uint32_t  AUTO_RESTART:  1;              /*!< [3..3] This will select the action taken upon completing a count.
                                                         1=The counter will automatically restart the count, using the
                                                         contents of the Timer Preload Register to load the Timer Count
                                                          Register.
                                                         The interrupt will be set in edge mode
                                                         0=The counter will simply enter a done state and wait for further
                                                          control inputs. The interrupt will be set in level mode.             */
      __IO uint32_t  SOFT_RESET :  1;               /*!< [4..4] This is a soft reset. This is self clearing 1 cycle after
                                                         it is written.                                                        */
      __IO uint32_t  START      :  1;               /*!< [5..5] This bit triggers the timer counter. The counter will
                                                         operate until it hits its terminating condition. This will
                                                         clear this bit. It should be noted that when operating in restart
                                                          mode, there is no terminating condition for the counter, so
                                                         this bit will never clear. Clearing this bit will halt the timer
                                                          counter.                                                             */
      __IO uint32_t  RELOAD     :  1;               /*!< [6..6] This bit reloads the counter without interrupting it
                                                         operation. This will not function if the timer has already
                                                         completed (when the START bit in this register is '0'). This
                                                          is used to periodically prevent the timer from firing when an
                                                         event occurs. Usage while the timer is off may result in erroneous
                                                          behaviour.                                                           */
      __IO uint32_t  HALT       :  1;               /*!< [7..7] This is a halt bit. This will halt the timer as long
                                                         as it is active. Once the halt is inactive, the timer will
                                                         start from where it left off. 1=Timer is halted. It stops counting.
                                                          The clock divider will also be reset. 0=Timer runs normally.
                                                                                                                               */
           uint32_t             :  8;
      __IO uint32_t  PRE_SCALE  : 16;               /*!< [16..31] This is used to divide down the system clock through
                                                         clock enables to lower the power consumption of the block and
                                                          allow
                                                         slow timers. Updating this value during operation may result
                                                          in erroneous clock enable pulses until the clock divider restarts.
                                                         The number of clocks per clock enable pulse is (Value + 1);
                                                          a setting of 0 runs at the full clock speed, while a setting
                                                          of 1
                                                         runs at half speed.                                                   */
    } CONTROL_b;                                    /*!< [32] BitSize                                                          */
  };
} TIMER0_Type;


/* ================================================================================ */
/* ================                   EC_REG_BANK                  ================ */
/* ================================================================================ */


/**
  * @brief This block is designed to be accessed internally by the EC via the register interface.  (EC_REG_BANK)
  */

typedef struct {                                    /*!< (@ 0x4000FC00) EC_REG_BANK Structure                                  */
  __I  uint32_t  RESERVED;
  __IO uint32_t  AHB_ERROR_ADDRESS;                 /*!< (@ 0x4000FC04) AHB Error Address [0:0] AHB_ERR_ADDR, In priority
                                                         order:
                                                          1. AHB address is registered when an AHB error occurs on the
                                                          processor's AHB master port and the register value was
                                                          already 0. This way only the first address to generate an exception
                                                          is captured.
                                                          2. The processor can clear this register by writing any 32-bit
                                                          value to this register.                                              */
  __I  uint32_t  RESERVED1[3];
  __IO uint8_t   AHB_ERROR_CONTROL;                 /*!< (@ 0x4000FC14) AHB Error Control [0:0] AHB_ERROR_DISABLE, 0:
                                                         EC memory exceptions are enabled. 1: EC memory exceptions are
                                                          disabled.                                                            */
  __I  uint8_t   RESERVED2[3];
  __IO uint32_t  INTERRUPT_CONTROL;                 /*!< (@ 0x4000FC18) Interrupt Control [0:0] NVIC_EN (NVIC_EN) This
                                                         bit enables Alternate NVIC IRQ's Vectors. The Alternate NVIC
                                                          Vectors provides each interrupt event with a dedicated (direct)
                                                          NVIC vector.
                                                          0 = Alternate NVIC vectors disabled, 1= Alternate NVIC vectors
                                                          enabled                                                              */
  __IO uint32_t  ETM_TRACE_ENABLE;                  /*!< (@ 0x4000FC1C) ETM TRACE Enable [0:0] TRACE_EN (TRACE_EN) This
                                                         bit enables the ARM TRACE debug port (ETM/ITM). The Trace Debug
                                                          Interface pins are forced to the TRACE functions. 0 = ARM TRACE
                                                          port disabled, 1= ARM TRACE port enabled                             */
  
  union {
    __IO uint32_t  DEBUG_Enable;                    /*!< (@ 0x4000FC20) Debug Enable Register                                  */
    
    struct {
      __IO uint32_t  DEBUG_EN   :  1;               /*!< [0..0] DEBUG_EN (JTAG_EN) This bit enables the JTAG/SWD debug
                                                         port.
                                                          0= JTAG/SWD port disabled. JTAG/SWD cannot be enabled (i.e.,
                                                          the TRST# pin is ignored and the JTAG signals remain in their
                                                          non-JTAG state)
                                                          1= JTAG/SWD port enabled. A high on TRST# enables JTAG or SWD,
                                                          as determined by SWD_EN.                                             */
      __IO uint32_t  DEBUG_PIN_CFG:  2;             /*!< [1..2] This field determines which pins are affected by the
                                                         TRST# debug enable pin.
                                                          3=Reserved
                                                          2=The pins associated with the JTAG TCK and TMS switch to the
                                                          debug interface when TRST# is de-asserted high. The pins
                                                          associated with TDI and TDO remain controlled by the associated
                                                          GPIO. This setting should be used when the ARM Serial
                                                          Wire Debug (SWD) is required for debugging and the Serial Wire
                                                          Viewer is not required
                                                          1=The pins associated with the JTAG TCK, TMS and TDO switch
                                                          to the debug interface when TRST# i                                  */
      __IO uint32_t  DEBUG_PU_EN:  1;               /*!< [3..3] If this bit is set to '1b' internal pull-up resistors
                                                         are automatically enabled on the appropriate debugging port
                                                          wires whenever the debug port is enabled (the DEBUG_EN bit
                                                          in this register is '1b' and the JTAG_RST# pin is high). The
                                                          setting
                                                          of DEBUG_PIN_CFG determines which pins have pull-ups enabled
                                                          when the debug port is enabled.                                      */
    } DEBUG_Enable_b;                               /*!< [4] BitSize                                                           */
  };
  __I  uint32_t  RESERVED3;
  __IO uint32_t  WDT_EVENT_COUNT;                   /*!< (@ 0x4000FC28) WDT Event Count [3:0] WDT_COUNT (WDT_COUNT) These
                                                         EC R/W bits are cleared to 0 on VCC1 POR, but not on a WDT.
                                                          Note: This field is written by Boot ROM firmware to indicate
                                                          the number of times a WDT fired before loading a good EC code
                                                          image.                                                               */
  
  union {
    __IO uint32_t  AES_HASH_BYTE_SWAP_CONTROL;      /*!< (@ 0x4000FC2C) AES HASH Byte Swap Control Register.                   */
    
    struct {
      __I  uint32_t  INPUT_BYTE_SWAP_ENABLE:  1;    /*!< [0..0] Used to enable byte swap on a DWORD during AHB read from
                                                         AES / HASH block: 1=Enable; 0=Disable.                                */
      __IO uint32_t  OUTPUT_BYTE_SWAP_ENABLE:  1;   /*!< [1..1] Used to enable byte swap on a DWORD during AHB write
                                                         from AES / HASH block: 1=Enable; 0=Disable.                           */
      __IO uint32_t  INPUT_BLOCK_SWAP_ENABLE:  3;   /*!< [2..4] Used to enable word swap on a DWORD during AHB read from
                                                         AES / HASH block
                                                          4=Swap 32-bit doublewords in 128-byte blocks
                                                          3=Swap doublewords in 64-byte blocks. Useful for SHA-256. Bus
                                                          references issued in the order 0x3C, 0x38, 0x34, 0x30, 0x2C,
                                                          0x28, 0x24, 0x20, 0x1C, 0x18, 0x14, 0x10, 0xC, 0x8, 0x4, 0x0,...
                                                          2=Swap doublewords in 16-byte blocks. Useful for AES. Bus references
                                                          issued in the order 0xC, 0x8, 0x4, 0x0, 0x1C, 0x18,...
                                                          1=Swap doublewords in 8-byte blocks. Useful for SHA-512, which
                                                          works on 64-                                                         */
      __IO uint32_t  OUTPUT_BLOCK_SWAP_ENABLE:  3;  /*!< [5..7] Used to enable word swap on a DWORD during AHB write
                                                         from AES / HASH block
                                                          4=Swap 32-bit doublewords in 128-byte blocks
                                                          3=Swap doublewords in 64-byte blocks. Useful for SHA-256. Bus
                                                          references issued in the order 0x3C, 0x38, 0x34, 0x30, 0x2C,
                                                          0x28, 0x24, 0x20, 0x1C, 0x18, 0x14, 0x10, 0xC, 0x8, 0x4, 0x0,...
                                                          2=Swap doublewords in 16-byte blocks. Useful for AES. Bus references
                                                          issued in the order 0xC, 0x8, 0x4, 0x0, 0x1C, 0x18,...
                                                          1=Swap doublewords in 8-byte blocks. Useful for SHA-512, which
                                                          works on 64                                                          */
    } AES_HASH_BYTE_SWAP_CONTROL_b;                 /*!< [8] BitSize                                                           */
  };
  __I  uint32_t  RESERVED4[2];
  
  union {
    __IO uint32_t  SYSTEM_SHUTDOWN_RESET;           /*!< (@ 0x4000FC38) System Shutdown Reset                                  */
    
    struct {
      __O  uint32_t  SYS_SHDN_RST:  1;              /*!< [0..0] When this bit is asserted ('1'), the SYS_SHDN# output
                                                         is deasserted.                                                        */
    } SYSTEM_SHUTDOWN_RESET_b;                      /*!< [1] BitSize                                                           */
  };
  __I  uint32_t  RESERVED5;
  
  union {
    __IO uint32_t  MISC_TRIM;                       /*!< (@ 0x4000FC40) Misc Trim                                              */
    
    struct {
      __O  uint32_t  PECI_DISABLE:  1;              /*!< [0..0] When this bit is asserted ('1'), it disables the PECI
                                                         pads to reduce leakage.                                               */
    } MISC_TRIM_b;                                  /*!< [1] BitSize                                                           */
  };
  __I  uint32_t  RESERVED6[6];
  
  union {
    __IO uint32_t  CRYPTO_SOFT_RESET;               /*!< (@ 0x4000FC5C) System Shutdown Reset                                  */
    
    struct {
      __O  uint32_t  RNG_SOFT_RESET:  1;            /*!< [0..0] When this bit is asserted ('1'), the Random Number Generator
                                                         block is reset.                                                       */
      __O  uint32_t  PUBLIC_KEY_SOFT_RESET:  1;     /*!< [1..1] When this bit is asserted ('1'), the Public Key block
                                                         is reset.                                                             */
      __O  uint32_t  AES_HASH_SOFT_RESET:  1;       /*!< [2..2] When this bit is asserted ('1'), the AES and Hash blocks
                                                         are reset.                                                            */
    } CRYPTO_SOFT_RESET_b;                          /*!< [3] BitSize                                                           */
  };
  __I  uint32_t  RESERVED7;
  
  union {
    __IO uint32_t  GPIO_BANK_POWER;                 /*!< (@ 0x4000FC64) GPIO Bank Power Register                               */
    
    struct {
      __O  uint32_t  VTR_LEVEL1 :  1;               /*!< [0..0] Voltage value on VTR1. This bit is set by hardware after
                                                         a VTR Power On Reset, but may be overridden by software.
                                                          It must be set by software if the VTR power rail is not active
                                                          when RESET_SYS is de-asserted.
                                                          1=VTR1 is powered by 3.3V
                                                          0=VTR1 is powered by 1.8V.                                           */
      __O  uint32_t  VTR_LEVEL2 :  1;               /*!< [1..1] Voltage value on VTR2. This bit is set by hardware after
                                                         a VTR Power On Reset, but may be overridden by software.
                                                          It must be set by software if the VTR power rail is not active
                                                          when RESET_SYS is de-asserted.
                                                          1=VTR2 is powered by 3.3V
                                                          0=VTR2 is powered by 1.8V.                                           */
      __O  uint32_t  VTR_LEVEL3 :  1;               /*!< [2..2] Voltage value on VTR3. This bit is set by hardware after
                                                         a VTR Power On Reset, but may be overridden by software.
                                                          It must be set by software if the VTR power rail is not active
                                                          when RESET_SYS is de-asserted.
                                                          1=VTR3 is powered by 3.3V
                                                          0=VTR3 is powered by 1.8V.                                           */
    } GPIO_BANK_POWER_b;                            /*!< [3] BitSize                                                           */
  };
  __I  uint32_t  RESERVED8[2];
  
  union {
    __IO uint32_t  JTAG_MASTER_CFG;                 /*!< (@ 0x4000FC70) JTAG Master Configuration Register                     */
    
    struct {
      __IO uint32_t  JTM_CLK    :  3;               /*!< [0..2] This field determines the JTAG Master clock rate, derived
                                                         from the 48MHz master clock.
                                                          7=375KHz; 6=750KHz; 5=1.5Mhz; 4=3Mhz; 3=6Mhz; 2=12Mhz; 1=24MHz;
                                                          0=Reserved.                                                          */
      __IO uint32_t  MASTER_SLAVE:  1;              /*!< [3..3] This bit controls the direction of the JTAG port. 1=The
                                                         JTAG Port is configured as a Master
                                                          0=The JTAG Port is configures as a Slave.                            */
    } JTAG_MASTER_CFG_b;                            /*!< [4] BitSize                                                           */
  };
  
  union {
    __I  uint32_t  JTAG_MASTER_STS;                 /*!< (@ 0x4000FC74) JTAG Master Status Register                            */
    
    struct {
      __I  uint32_t  JTM_DONE   :  1;               /*!< [0..0] This bit is set to '1b' when the JTAG Master Command
                                                         Register is written. It becomes '0b' when shifting has completed.
                                                          Software can poll this bit to determine when a command has
                                                          completed and it is therefore safe to remove the data in the
                                                          JTAG Master TDO
                                                          Register and load new data into the JTAG Master TMS Register
                                                          and the JTAG Master TDI Register.                                    */
    } JTAG_MASTER_STS_b;                            /*!< [1] BitSize                                                           */
  };
  
  union {
    __IO uint32_t  JTAG_MASTER_TDO;                 /*!< (@ 0x4000FC78) JTAG Master TDO Register                               */
    
    struct {
      __IO uint32_t  JTM_TDO    : 32;               /*!< [0..31] When the JTAG Master Command Register is written, from
                                                         1 to 32 bits are shifted into this register, starting with bit
                                                          0,
                                                          from the JTAG_TDO pin. Shifting is at the rate determined by
                                                          the JTM_CLK field in the JTAG Master Configuration Register.
                                                                                                                               */
    } JTAG_MASTER_TDO_b;                            /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  JTAG_MASTER_TDI;                 /*!< (@ 0x4000FC7C) JTAG Master TDI Register                               */
    
    struct {
      __IO uint32_t  JTM_TDI    : 32;               /*!< [0..31] When the JTAG Master Command Register is written, from
                                                         1 to 32 bits are shifted out of this register, starting with
                                                          bit 0,
                                                          onto the JTAG_TDI pin. Shifting is at the rate determined by
                                                          the JTM_CLK field in the JTAG Master Configuration Register.
                                                                                                                               */
    } JTAG_MASTER_TDI_b;                            /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  JTAG_MASTER_TMS;                 /*!< (@ 0x4000FC80) JTAG Master TMS Register                               */
    
    struct {
      __IO uint32_t  JTM_TMS    : 32;               /*!< [0..31] When the JTAG Master Command Register is written, from
                                                         1 to 32 bits are shifted out of this register, starting with
                                                          bit 0,
                                                          onto the JTAG_TMS pin. Shifting is at the rate determined by
                                                          the JTM_CLK field in the JTAG Master Configuration Register.
                                                                                                                               */
    } JTAG_MASTER_TMS_b;                            /*!< [32] BitSize                                                          */
  };
  
  union {
    __IO uint32_t  JTAG_MASTER_CMD;                 /*!< (@ 0x4000FC84) JTAG Master Command Register                           */
    
    struct {
      __IO uint32_t  JTM_COUNT  :  5;               /*!< [0..4] If the JTAG Port is configured as a Master, writing this
                                                         register starts clocking and shifting on the JTAG port. The
                                                          JTAG
                                                          Master port will shift JTM_COUNT+1 times, so writing a '0h'
                                                          will shift 1 bit, and writing '31h' will shift 32 bits. The
                                                          signal JTAG_CLK
                                                          will cycle JTM_COUNT+1 times. The contents of the JTAG Master
                                                          TMS Register and the JTAG Master TDI Register will be shifted
                                                          out on
                                                          the falling edge of JTAG_CLK and the.JTAG Master TDO Register
                                                          will get shifted in on the rising edge of JTAG_CLK.
                                                          If t                                                                 */
    } JTAG_MASTER_CMD_b;                            /*!< [5] BitSize                                                           */
  };
} EC_REG_BANK_Type;


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


/* ------------------------------  PCR_SYS_SLP_CNTRL  ----------------------------- */
#define PCR_SYS_SLP_CNTRL_SLEEP_MODE_Pos      (0UL)                     /*!< PCR SYS_SLP_CNTRL: SLEEP_MODE (Bit 0)                       */
#define PCR_SYS_SLP_CNTRL_SLEEP_MODE_Msk      (0x1UL)                   /*!< PCR SYS_SLP_CNTRL: SLEEP_MODE (Bitfield-Mask: 0x01)         */
#define PCR_SYS_SLP_CNTRL_TEST_Pos            (2UL)                     /*!< PCR SYS_SLP_CNTRL: TEST (Bit 2)                             */
#define PCR_SYS_SLP_CNTRL_TEST_Msk            (0x4UL)                   /*!< PCR SYS_SLP_CNTRL: TEST (Bitfield-Mask: 0x01)               */
#define PCR_SYS_SLP_CNTRL_SLEEP_ALL_Pos       (3UL)                     /*!< PCR SYS_SLP_CNTRL: SLEEP_ALL (Bit 3)                        */
#define PCR_SYS_SLP_CNTRL_SLEEP_ALL_Msk       (0x8UL)                   /*!< PCR SYS_SLP_CNTRL: SLEEP_ALL (Bitfield-Mask: 0x01)          */

/* -----------------------------  PCR_PROC_CLK_CNTRL  ----------------------------- */
#define PCR_PROC_CLK_CNTRL_PROCESSOR_CLOCK_DIVIDE_Pos (0UL)             /*!< PCR PROC_CLK_CNTRL: PROCESSOR_CLOCK_DIVIDE (Bit 0)          */
#define PCR_PROC_CLK_CNTRL_PROCESSOR_CLOCK_DIVIDE_Msk (0xffUL)          /*!< PCR PROC_CLK_CNTRL: PROCESSOR_CLOCK_DIVIDE (Bitfield-Mask: 0xff) */

/* -----------------------------  PCR_SLOW_CLK_CNTRL  ----------------------------- */
#define PCR_SLOW_CLK_CNTRL_SLOW_CLOCK_DIVIDE_Pos (0UL)                  /*!< PCR SLOW_CLK_CNTRL: SLOW_CLOCK_DIVIDE (Bit 0)               */
#define PCR_SLOW_CLK_CNTRL_SLOW_CLOCK_DIVIDE_Msk (0x3ffUL)              /*!< PCR SLOW_CLK_CNTRL: SLOW_CLOCK_DIVIDE (Bitfield-Mask: 0x3ff) */

/* ---------------------------------  PCR_OSC_ID  --------------------------------- */
#define PCR_OSC_ID_TEST_Pos                   (0UL)                     /*!< PCR OSC_ID: TEST (Bit 0)                                    */
#define PCR_OSC_ID_TEST_Msk                   (0xffUL)                  /*!< PCR OSC_ID: TEST (Bitfield-Mask: 0xff)                      */
#define PCR_OSC_ID_PLL_LOCK_Pos               (8UL)                     /*!< PCR OSC_ID: PLL_LOCK (Bit 8)                                */
#define PCR_OSC_ID_PLL_LOCK_Msk               (0x100UL)                 /*!< PCR OSC_ID: PLL_LOCK (Bitfield-Mask: 0x01)                  */

/* -----------------------------  PCR_PCR_PWR_RST_STS  ---------------------------- */
#define PCR_PCR_PWR_RST_STS_VCC_PWRGD_STATUS_Pos (2UL)                  /*!< PCR PCR_PWR_RST_STS: VCC_PWRGD_STATUS (Bit 2)               */
#define PCR_PCR_PWR_RST_STS_VCC_PWRGD_STATUS_Msk (0x4UL)                /*!< PCR PCR_PWR_RST_STS: VCC_PWRGD_STATUS (Bitfield-Mask: 0x01) */
#define PCR_PCR_PWR_RST_STS_RESET_HOST_STATUS_Pos (3UL)                 /*!< PCR PCR_PWR_RST_STS: RESET_HOST_STATUS (Bit 3)              */
#define PCR_PCR_PWR_RST_STS_RESET_HOST_STATUS_Msk (0x8UL)               /*!< PCR PCR_PWR_RST_STS: RESET_HOST_STATUS (Bitfield-Mask: 0x01) */
#define PCR_PCR_PWR_RST_STS_VBAT_RESET_STATUS_Pos (5UL)                 /*!< PCR PCR_PWR_RST_STS: VBAT_RESET_STATUS (Bit 5)              */
#define PCR_PCR_PWR_RST_STS_VBAT_RESET_STATUS_Msk (0x20UL)              /*!< PCR PCR_PWR_RST_STS: VBAT_RESET_STATUS (Bitfield-Mask: 0x01) */
#define PCR_PCR_PWR_RST_STS_VTR_RESET_STATUS_Pos (6UL)                  /*!< PCR PCR_PWR_RST_STS: VTR_RESET_STATUS (Bit 6)               */
#define PCR_PCR_PWR_RST_STS_VTR_RESET_STATUS_Msk (0x40UL)               /*!< PCR PCR_PWR_RST_STS: VTR_RESET_STATUS (Bitfield-Mask: 0x01) */
#define PCR_PCR_PWR_RST_STS_JTAG_RESET_STATUS_Pos (7UL)                 /*!< PCR PCR_PWR_RST_STS: JTAG_RESET_STATUS (Bit 7)              */
#define PCR_PCR_PWR_RST_STS_JTAG_RESET_STATUS_Msk (0x80UL)              /*!< PCR PCR_PWR_RST_STS: JTAG_RESET_STATUS (Bitfield-Mask: 0x01) */
#define PCR_PCR_PWR_RST_STS__32K_ACTIVE_Pos   (10UL)                    /*!< PCR PCR_PWR_RST_STS: _32K_ACTIVE (Bit 10)                   */
#define PCR_PCR_PWR_RST_STS__32K_ACTIVE_Msk   (0x400UL)                 /*!< PCR PCR_PWR_RST_STS: _32K_ACTIVE (Bitfield-Mask: 0x01)      */
#define PCR_PCR_PWR_RST_STS_PCICLK_ACTIVE_Pos (11UL)                    /*!< PCR PCR_PWR_RST_STS: PCICLK_ACTIVE (Bit 11)                 */
#define PCR_PCR_PWR_RST_STS_PCICLK_ACTIVE_Msk (0x800UL)                 /*!< PCR PCR_PWR_RST_STS: PCICLK_ACTIVE (Bitfield-Mask: 0x01)    */
#define PCR_PCR_PWR_RST_STS_ESPI_CLK_ACTIVE_Pos (12UL)                  /*!< PCR PCR_PWR_RST_STS: ESPI_CLK_ACTIVE (Bit 12)               */
#define PCR_PCR_PWR_RST_STS_ESPI_CLK_ACTIVE_Msk (0x1000UL)              /*!< PCR PCR_PWR_RST_STS: ESPI_CLK_ACTIVE (Bitfield-Mask: 0x01)  */

/* ------------------------------  PCR_PWR_RST_CNTRL  ----------------------------- */
#define PCR_PWR_RST_CNTRL_PWR_INV_Pos         (0UL)                     /*!< PCR PWR_RST_CNTRL: PWR_INV (Bit 0)                          */
#define PCR_PWR_RST_CNTRL_PWR_INV_Msk         (0x1UL)                   /*!< PCR PWR_RST_CNTRL: PWR_INV (Bitfield-Mask: 0x01)            */
#define PCR_PWR_RST_CNTRL_HOST_RESET_SELECT_Pos (8UL)                   /*!< PCR PWR_RST_CNTRL: HOST_RESET_SELECT (Bit 8)                */
#define PCR_PWR_RST_CNTRL_HOST_RESET_SELECT_Msk (0x100UL)               /*!< PCR PWR_RST_CNTRL: HOST_RESET_SELECT (Bitfield-Mask: 0x01)  */

/* ---------------------------------  PCR_SYS_RST  -------------------------------- */
#define PCR_SYS_RST_SOFT_SYS_RESET_Pos        (8UL)                     /*!< PCR SYS_RST: SOFT_SYS_RESET (Bit 8)                         */
#define PCR_SYS_RST_SOFT_SYS_RESET_Msk        (0x100UL)                 /*!< PCR SYS_RST: SOFT_SYS_RESET (Bitfield-Mask: 0x01)           */

/* --------------------------------  PCR_SLP_EN_0  -------------------------------- */
#define PCR_SLP_EN_0_JTAG_STAP_SLP_EN_Pos     (0UL)                     /*!< PCR SLP_EN_0: JTAG_STAP_SLP_EN (Bit 0)                      */
#define PCR_SLP_EN_0_JTAG_STAP_SLP_EN_Msk     (0x1UL)                   /*!< PCR SLP_EN_0: JTAG_STAP_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_0_EFUSE_SLP_EN_Pos         (1UL)                     /*!< PCR SLP_EN_0: EFUSE_SLP_EN (Bit 1)                          */
#define PCR_SLP_EN_0_EFUSE_SLP_EN_Msk         (0x2UL)                   /*!< PCR SLP_EN_0: EFUSE_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_0_ISPI_SLP_EN_Pos          (2UL)                     /*!< PCR SLP_EN_0: ISPI_SLP_EN (Bit 2)                           */
#define PCR_SLP_EN_0_ISPI_SLP_EN_Msk          (0x4UL)                   /*!< PCR SLP_EN_0: ISPI_SLP_EN (Bitfield-Mask: 0x01)             */

/* --------------------------------  PCR_SLP_EN_1  -------------------------------- */
#define PCR_SLP_EN_1_INT_SLP_EN_Pos           (0UL)                     /*!< PCR SLP_EN_1: INT_SLP_EN (Bit 0)                            */
#define PCR_SLP_EN_1_INT_SLP_EN_Msk           (0x1UL)                   /*!< PCR SLP_EN_1: INT_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_1_PECI_SLP_EN_Pos          (1UL)                     /*!< PCR SLP_EN_1: PECI_SLP_EN (Bit 1)                           */
#define PCR_SLP_EN_1_PECI_SLP_EN_Msk          (0x2UL)                   /*!< PCR SLP_EN_1: PECI_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_TACH0_SLP_EN_Pos         (2UL)                     /*!< PCR SLP_EN_1: TACH0_SLP_EN (Bit 2)                          */
#define PCR_SLP_EN_1_TACH0_SLP_EN_Msk         (0x4UL)                   /*!< PCR SLP_EN_1: TACH0_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_1_PWM0_SLP_EN_Pos          (4UL)                     /*!< PCR SLP_EN_1: PWM0_SLP_EN (Bit 4)                           */
#define PCR_SLP_EN_1_PWM0_SLP_EN_Msk          (0x10UL)                  /*!< PCR SLP_EN_1: PWM0_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PMC_SLP_EN_Pos           (5UL)                     /*!< PCR SLP_EN_1: PMC_SLP_EN (Bit 5)                            */
#define PCR_SLP_EN_1_PMC_SLP_EN_Msk           (0x20UL)                  /*!< PCR SLP_EN_1: PMC_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_1_DMA_SLP_EN_Pos           (6UL)                     /*!< PCR SLP_EN_1: DMA_SLP_EN (Bit 6)                            */
#define PCR_SLP_EN_1_DMA_SLP_EN_Msk           (0x40UL)                  /*!< PCR SLP_EN_1: DMA_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_1_TFDP_SLP_EN_Pos          (7UL)                     /*!< PCR SLP_EN_1: TFDP_SLP_EN (Bit 7)                           */
#define PCR_SLP_EN_1_TFDP_SLP_EN_Msk          (0x80UL)                  /*!< PCR SLP_EN_1: TFDP_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PROCESSOR_SLP_EN_Pos     (8UL)                     /*!< PCR SLP_EN_1: PROCESSOR_SLP_EN (Bit 8)                      */
#define PCR_SLP_EN_1_PROCESSOR_SLP_EN_Msk     (0x100UL)                 /*!< PCR SLP_EN_1: PROCESSOR_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_1_WDT_SLP_EN_Pos           (9UL)                     /*!< PCR SLP_EN_1: WDT_SLP_EN (Bit 9)                            */
#define PCR_SLP_EN_1_WDT_SLP_EN_Msk           (0x200UL)                 /*!< PCR SLP_EN_1: WDT_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_1_SMB0_SLP_EN_Pos          (10UL)                    /*!< PCR SLP_EN_1: SMB0_SLP_EN (Bit 10)                          */
#define PCR_SLP_EN_1_SMB0_SLP_EN_Msk          (0x400UL)                 /*!< PCR SLP_EN_1: SMB0_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_TACH1_SLP_EN_Pos         (11UL)                    /*!< PCR SLP_EN_1: TACH1_SLP_EN (Bit 11)                         */
#define PCR_SLP_EN_1_TACH1_SLP_EN_Msk         (0x800UL)                 /*!< PCR SLP_EN_1: TACH1_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_1_TACH2_SLP_EN_Pos         (12UL)                    /*!< PCR SLP_EN_1: TACH2_SLP_EN (Bit 12)                         */
#define PCR_SLP_EN_1_TACH2_SLP_EN_Msk         (0x1000UL)                /*!< PCR SLP_EN_1: TACH2_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_1_PWM1_SLP_EN_Pos          (20UL)                    /*!< PCR SLP_EN_1: PWM1_SLP_EN (Bit 20)                          */
#define PCR_SLP_EN_1_PWM1_SLP_EN_Msk          (0x100000UL)              /*!< PCR SLP_EN_1: PWM1_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM2_SLP_EN_Pos          (21UL)                    /*!< PCR SLP_EN_1: PWM2_SLP_EN (Bit 21)                          */
#define PCR_SLP_EN_1_PWM2_SLP_EN_Msk          (0x200000UL)              /*!< PCR SLP_EN_1: PWM2_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM3_SLP_EN_Pos          (22UL)                    /*!< PCR SLP_EN_1: PWM3_SLP_EN (Bit 22)                          */
#define PCR_SLP_EN_1_PWM3_SLP_EN_Msk          (0x400000UL)              /*!< PCR SLP_EN_1: PWM3_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM4_SLP_EN_Pos          (23UL)                    /*!< PCR SLP_EN_1: PWM4_SLP_EN (Bit 23)                          */
#define PCR_SLP_EN_1_PWM4_SLP_EN_Msk          (0x800000UL)              /*!< PCR SLP_EN_1: PWM4_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM5_SLP_EN_Pos          (24UL)                    /*!< PCR SLP_EN_1: PWM5_SLP_EN (Bit 24)                          */
#define PCR_SLP_EN_1_PWM5_SLP_EN_Msk          (0x1000000UL)             /*!< PCR SLP_EN_1: PWM5_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM6_SLP_EN_Pos          (25UL)                    /*!< PCR SLP_EN_1: PWM6_SLP_EN (Bit 25)                          */
#define PCR_SLP_EN_1_PWM6_SLP_EN_Msk          (0x2000000UL)             /*!< PCR SLP_EN_1: PWM6_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM7_SLP_EN_Pos          (26UL)                    /*!< PCR SLP_EN_1: PWM7_SLP_EN (Bit 26)                          */
#define PCR_SLP_EN_1_PWM7_SLP_EN_Msk          (0x4000000UL)             /*!< PCR SLP_EN_1: PWM7_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_PWM8_SLP_EN_Pos          (27UL)                    /*!< PCR SLP_EN_1: PWM8_SLP_EN (Bit 27)                          */
#define PCR_SLP_EN_1_PWM8_SLP_EN_Msk          (0x8000000UL)             /*!< PCR SLP_EN_1: PWM8_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_1_EC_REG_BANK_SLP_EN_Pos   (29UL)                    /*!< PCR SLP_EN_1: EC_REG_BANK_SLP_EN (Bit 29)                   */
#define PCR_SLP_EN_1_EC_REG_BANK_SLP_EN_Msk   (0x20000000UL)            /*!< PCR SLP_EN_1: EC_REG_BANK_SLP_EN (Bitfield-Mask: 0x01)      */
#define PCR_SLP_EN_1_TIMER16_0_SLP_EN_Pos     (30UL)                    /*!< PCR SLP_EN_1: TIMER16_0_SLP_EN (Bit 30)                     */
#define PCR_SLP_EN_1_TIMER16_0_SLP_EN_Msk     (0x40000000UL)            /*!< PCR SLP_EN_1: TIMER16_0_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_1_TIMER16_1_SLP_EN_Pos     (31UL)                    /*!< PCR SLP_EN_1: TIMER16_1_SLP_EN (Bit 31)                     */
#define PCR_SLP_EN_1_TIMER16_1_SLP_EN_Msk     (0x80000000UL)            /*!< PCR SLP_EN_1: TIMER16_1_SLP_EN (Bitfield-Mask: 0x01)        */

/* --------------------------------  PCR_SLP_EN_2  -------------------------------- */
#define PCR_SLP_EN_2_LPC_SLP_EN_Pos           (0UL)                     /*!< PCR SLP_EN_2: LPC_SLP_EN (Bit 0)                            */
#define PCR_SLP_EN_2_LPC_SLP_EN_Msk           (0x1UL)                   /*!< PCR SLP_EN_2: LPC_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_2_UART_0_SLP_EN_Pos        (1UL)                     /*!< PCR SLP_EN_2: UART_0_SLP_EN (Bit 1)                         */
#define PCR_SLP_EN_2_UART_0_SLP_EN_Msk        (0x2UL)                   /*!< PCR SLP_EN_2: UART_0_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_SLP_EN_2_UART_1_SLP_EN_Pos        (2UL)                     /*!< PCR SLP_EN_2: UART_1_SLP_EN (Bit 2)                         */
#define PCR_SLP_EN_2_UART_1_SLP_EN_Msk        (0x4UL)                   /*!< PCR SLP_EN_2: UART_1_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_SLP_EN_2_GLBL_CFG_SLP_EN_Pos      (12UL)                    /*!< PCR SLP_EN_2: GLBL_CFG_SLP_EN (Bit 12)                      */
#define PCR_SLP_EN_2_GLBL_CFG_SLP_EN_Msk      (0x1000UL)                /*!< PCR SLP_EN_2: GLBL_CFG_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_SLP_EN_2_ACPI_EC_0_SLP_EN_Pos     (13UL)                    /*!< PCR SLP_EN_2: ACPI_EC_0_SLP_EN (Bit 13)                     */
#define PCR_SLP_EN_2_ACPI_EC_0_SLP_EN_Msk     (0x2000UL)                /*!< PCR SLP_EN_2: ACPI_EC_0_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_2_ACPI_EC_1_SLP_EN_Pos     (14UL)                    /*!< PCR SLP_EN_2: ACPI_EC_1_SLP_EN (Bit 14)                     */
#define PCR_SLP_EN_2_ACPI_EC_1_SLP_EN_Msk     (0x4000UL)                /*!< PCR SLP_EN_2: ACPI_EC_1_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_2_ACPI_PM1_SLP_EN_Pos      (15UL)                    /*!< PCR SLP_EN_2: ACPI_PM1_SLP_EN (Bit 15)                      */
#define PCR_SLP_EN_2_ACPI_PM1_SLP_EN_Msk      (0x8000UL)                /*!< PCR SLP_EN_2: ACPI_PM1_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_SLP_EN_2_KBCEM_SLP_EN_Pos         (16UL)                    /*!< PCR SLP_EN_2: KBCEM_SLP_EN (Bit 16)                         */
#define PCR_SLP_EN_2_KBCEM_SLP_EN_Msk         (0x10000UL)               /*!< PCR SLP_EN_2: KBCEM_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_2_MBX_SLP_EN_Pos           (17UL)                    /*!< PCR SLP_EN_2: MBX_SLP_EN (Bit 17)                           */
#define PCR_SLP_EN_2_MBX_SLP_EN_Msk           (0x20000UL)               /*!< PCR SLP_EN_2: MBX_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_2_RTC_SLP_EN_Pos           (18UL)                    /*!< PCR SLP_EN_2: RTC_SLP_EN (Bit 18)                           */
#define PCR_SLP_EN_2_RTC_SLP_EN_Msk           (0x40000UL)               /*!< PCR SLP_EN_2: RTC_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_2_ESPI_SLP_EN_Pos          (19UL)                    /*!< PCR SLP_EN_2: ESPI_SLP_EN (Bit 19)                          */
#define PCR_SLP_EN_2_ESPI_SLP_EN_Msk          (0x80000UL)               /*!< PCR SLP_EN_2: ESPI_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_2_ACPI_EC_2_SLP_EN_Pos     (21UL)                    /*!< PCR SLP_EN_2: ACPI_EC_2_SLP_EN (Bit 21)                     */
#define PCR_SLP_EN_2_ACPI_EC_2_SLP_EN_Msk     (0x200000UL)              /*!< PCR SLP_EN_2: ACPI_EC_2_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_2_ACPI_EC_3_SLP_EN_Pos     (22UL)                    /*!< PCR SLP_EN_2: ACPI_EC_3_SLP_EN (Bit 22)                     */
#define PCR_SLP_EN_2_ACPI_EC_3_SLP_EN_Msk     (0x400000UL)              /*!< PCR SLP_EN_2: ACPI_EC_3_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_2_ACPI_EC_4_SLP_EN_Pos     (23UL)                    /*!< PCR SLP_EN_2: ACPI_EC_4_SLP_EN (Bit 23)                     */
#define PCR_SLP_EN_2_ACPI_EC_4_SLP_EN_Msk     (0x800000UL)              /*!< PCR SLP_EN_2: ACPI_EC_4_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_2_ASIF_SLP_EN_Pos          (24UL)                    /*!< PCR SLP_EN_2: ASIF_SLP_EN (Bit 24)                          */
#define PCR_SLP_EN_2_ASIF_SLP_EN_Msk          (0x1000000UL)             /*!< PCR SLP_EN_2: ASIF_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_2_PORT80_0_SLP_EN_Pos      (25UL)                    /*!< PCR SLP_EN_2: PORT80_0_SLP_EN (Bit 25)                      */
#define PCR_SLP_EN_2_PORT80_0_SLP_EN_Msk      (0x2000000UL)             /*!< PCR SLP_EN_2: PORT80_0_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_SLP_EN_2_PORT80_1_SLP_EN_Pos      (26UL)                    /*!< PCR SLP_EN_2: PORT80_1_SLP_EN (Bit 26)                      */
#define PCR_SLP_EN_2_PORT80_1_SLP_EN_Msk      (0x4000000UL)             /*!< PCR SLP_EN_2: PORT80_1_SLP_EN (Bitfield-Mask: 0x01)         */

/* --------------------------------  PCR_SLP_EN_3  -------------------------------- */
#define PCR_SLP_EN_3_ADC_SLP_EN_Pos           (3UL)                     /*!< PCR SLP_EN_3: ADC_SLP_EN (Bit 3)                            */
#define PCR_SLP_EN_3_ADC_SLP_EN_Msk           (0x8UL)                   /*!< PCR SLP_EN_3: ADC_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_3_PS2_0_SLP_EN_Pos         (5UL)                     /*!< PCR SLP_EN_3: PS2_0_SLP_EN (Bit 5)                          */
#define PCR_SLP_EN_3_PS2_0_SLP_EN_Msk         (0x20UL)                  /*!< PCR SLP_EN_3: PS2_0_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_3_PS2_1_SLP_EN_Pos         (6UL)                     /*!< PCR SLP_EN_3: PS2_1_SLP_EN (Bit 6)                          */
#define PCR_SLP_EN_3_PS2_1_SLP_EN_Msk         (0x40UL)                  /*!< PCR SLP_EN_3: PS2_1_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_3_PS2_2_SLP_EN_Pos         (7UL)                     /*!< PCR SLP_EN_3: PS2_2_SLP_EN (Bit 7)                          */
#define PCR_SLP_EN_3_PS2_2_SLP_EN_Msk         (0x80UL)                  /*!< PCR SLP_EN_3: PS2_2_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_3_GP_SPI0_SLP_EN_Pos       (9UL)                     /*!< PCR SLP_EN_3: GP_SPI0_SLP_EN (Bit 9)                        */
#define PCR_SLP_EN_3_GP_SPI0_SLP_EN_Msk       (0x200UL)                 /*!< PCR SLP_EN_3: GP_SPI0_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_SLP_EN_3_HTIMER_0_SLP_EN_Pos      (10UL)                    /*!< PCR SLP_EN_3: HTIMER_0_SLP_EN (Bit 10)                      */
#define PCR_SLP_EN_3_HTIMER_0_SLP_EN_Msk      (0x400UL)                 /*!< PCR SLP_EN_3: HTIMER_0_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_SLP_EN_3_KEYSCAN_SLP_EN_Pos       (11UL)                    /*!< PCR SLP_EN_3: KEYSCAN_SLP_EN (Bit 11)                       */
#define PCR_SLP_EN_3_KEYSCAN_SLP_EN_Msk       (0x800UL)                 /*!< PCR SLP_EN_3: KEYSCAN_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_SLP_EN_3_RPMPWM_SLP_EN_Pos        (12UL)                    /*!< PCR SLP_EN_3: RPMPWM_SLP_EN (Bit 12)                        */
#define PCR_SLP_EN_3_RPMPWM_SLP_EN_Msk        (0x1000UL)                /*!< PCR SLP_EN_3: RPMPWM_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_SLP_EN_3_SMB1_SLP_EN_Pos          (13UL)                    /*!< PCR SLP_EN_3: SMB1_SLP_EN (Bit 13)                          */
#define PCR_SLP_EN_3_SMB1_SLP_EN_Msk          (0x2000UL)                /*!< PCR SLP_EN_3: SMB1_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_SMB2_SLP_EN_Pos          (14UL)                    /*!< PCR SLP_EN_3: SMB2_SLP_EN (Bit 14)                          */
#define PCR_SLP_EN_3_SMB2_SLP_EN_Msk          (0x4000UL)                /*!< PCR SLP_EN_3: SMB2_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_SMB3_SLP_EN_Pos          (15UL)                    /*!< PCR SLP_EN_3: SMB3_SLP_EN (Bit 15)                          */
#define PCR_SLP_EN_3_SMB3_SLP_EN_Msk          (0x8000UL)                /*!< PCR SLP_EN_3: SMB3_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_LED0_SLP_EN_Pos          (16UL)                    /*!< PCR SLP_EN_3: LED0_SLP_EN (Bit 16)                          */
#define PCR_SLP_EN_3_LED0_SLP_EN_Msk          (0x10000UL)               /*!< PCR SLP_EN_3: LED0_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_LED1_SLP_EN_Pos          (17UL)                    /*!< PCR SLP_EN_3: LED1_SLP_EN (Bit 17)                          */
#define PCR_SLP_EN_3_LED1_SLP_EN_Msk          (0x20000UL)               /*!< PCR SLP_EN_3: LED1_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_LED2_SLP_EN_Pos          (18UL)                    /*!< PCR SLP_EN_3: LED2_SLP_EN (Bit 18)                          */
#define PCR_SLP_EN_3_LED2_SLP_EN_Msk          (0x40000UL)               /*!< PCR SLP_EN_3: LED2_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_BCM0_SLP_EN_Pos          (19UL)                    /*!< PCR SLP_EN_3: BCM0_SLP_EN (Bit 19)                          */
#define PCR_SLP_EN_3_BCM0_SLP_EN_Msk          (0x80000UL)               /*!< PCR SLP_EN_3: BCM0_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_GP_SPI1_SLP_EN_Pos       (20UL)                    /*!< PCR SLP_EN_3: GP_SPI1_SLP_EN (Bit 20)                       */
#define PCR_SLP_EN_3_GP_SPI1_SLP_EN_Msk       (0x100000UL)              /*!< PCR SLP_EN_3: GP_SPI1_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_SLP_EN_3_TIMER16_2_SLP_EN_Pos     (21UL)                    /*!< PCR SLP_EN_3: TIMER16_2_SLP_EN (Bit 21)                     */
#define PCR_SLP_EN_3_TIMER16_2_SLP_EN_Msk     (0x200000UL)              /*!< PCR SLP_EN_3: TIMER16_2_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_3_TIMER16_3_SLP_EN_Pos     (22UL)                    /*!< PCR SLP_EN_3: TIMER16_3_SLP_EN (Bit 22)                     */
#define PCR_SLP_EN_3_TIMER16_3_SLP_EN_Msk     (0x400000UL)              /*!< PCR SLP_EN_3: TIMER16_3_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_3_TIMER32_0_SLP_EN_Pos     (23UL)                    /*!< PCR SLP_EN_3: TIMER32_0_SLP_EN (Bit 23)                     */
#define PCR_SLP_EN_3_TIMER32_0_SLP_EN_Msk     (0x800000UL)              /*!< PCR SLP_EN_3: TIMER32_0_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_3_TIMER32_1_SLP_EN_Pos     (24UL)                    /*!< PCR SLP_EN_3: TIMER32_1_SLP_EN (Bit 24)                     */
#define PCR_SLP_EN_3_TIMER32_1_SLP_EN_Msk     (0x1000000UL)             /*!< PCR SLP_EN_3: TIMER32_1_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_3_LED3_SLP_EN_Pos          (25UL)                    /*!< PCR SLP_EN_3: LED3_SLP_EN (Bit 25)                          */
#define PCR_SLP_EN_3_LED3_SLP_EN_Msk          (0x2000000UL)             /*!< PCR SLP_EN_3: LED3_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_3_PKE_SLP_EN_Pos           (26UL)                    /*!< PCR SLP_EN_3: PKE_SLP_EN (Bit 26)                           */
#define PCR_SLP_EN_3_PKE_SLP_EN_Msk           (0x4000000UL)             /*!< PCR SLP_EN_3: PKE_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_3_RNG_SLP_EN_Pos           (27UL)                    /*!< PCR SLP_EN_3: RNG_SLP_EN (Bit 27)                           */
#define PCR_SLP_EN_3_RNG_SLP_EN_Msk           (0x8000000UL)             /*!< PCR SLP_EN_3: RNG_SLP_EN (Bitfield-Mask: 0x01)              */
#define PCR_SLP_EN_3_AES_HASH_SLP_EN_Pos      (28UL)                    /*!< PCR SLP_EN_3: AES_HASH_SLP_EN (Bit 28)                      */
#define PCR_SLP_EN_3_AES_HASH_SLP_EN_Msk      (0x10000000UL)            /*!< PCR SLP_EN_3: AES_HASH_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_SLP_EN_3_HTIMER_1_SLP_EN_Pos      (29UL)                    /*!< PCR SLP_EN_3: HTIMER_1_SLP_EN (Bit 29)                      */
#define PCR_SLP_EN_3_HTIMER_1_SLP_EN_Msk      (0x20000000UL)            /*!< PCR SLP_EN_3: HTIMER_1_SLP_EN (Bitfield-Mask: 0x01)         */
#define PCR_SLP_EN_3_CCTIMER_SLP_EN_Pos       (30UL)                    /*!< PCR SLP_EN_3: CCTIMER_SLP_EN (Bit 30)                       */
#define PCR_SLP_EN_3_CCTIMER_SLP_EN_Msk       (0x40000000UL)            /*!< PCR SLP_EN_3: CCTIMER_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_SLP_EN_3_PWM9_SLP_EN_Pos          (31UL)                    /*!< PCR SLP_EN_3: PWM9_SLP_EN (Bit 31)                          */
#define PCR_SLP_EN_3_PWM9_SLP_EN_Msk          (0x80000000UL)            /*!< PCR SLP_EN_3: PWM9_SLP_EN (Bitfield-Mask: 0x01)             */

/* --------------------------------  PCR_SLP_EN_4  -------------------------------- */
#define PCR_SLP_EN_4_PWM10_SLP_EN_Pos         (0UL)                     /*!< PCR SLP_EN_4: PWM10_SLP_EN (Bit 0)                          */
#define PCR_SLP_EN_4_PWM10_SLP_EN_Msk         (0x1UL)                   /*!< PCR SLP_EN_4: PWM10_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_4_PWM11_SLP_EN_Pos         (1UL)                     /*!< PCR SLP_EN_4: PWM11_SLP_EN (Bit 1)                          */
#define PCR_SLP_EN_4_PWM11_SLP_EN_Msk         (0x2UL)                   /*!< PCR SLP_EN_4: PWM11_SLP_EN (Bitfield-Mask: 0x01)            */
#define PCR_SLP_EN_4_CNT_TMER0_SLP_EN_Pos     (2UL)                     /*!< PCR SLP_EN_4: CNT_TMER0_SLP_EN (Bit 2)                      */
#define PCR_SLP_EN_4_CNT_TMER0_SLP_EN_Msk     (0x4UL)                   /*!< PCR SLP_EN_4: CNT_TMER0_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_4_CNT_TMER1_SLP_EN_Pos     (3UL)                     /*!< PCR SLP_EN_4: CNT_TMER1_SLP_EN (Bit 3)                      */
#define PCR_SLP_EN_4_CNT_TMER1_SLP_EN_Msk     (0x8UL)                   /*!< PCR SLP_EN_4: CNT_TMER1_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_4_CNT_TMER2_SLP_EN_Pos     (4UL)                     /*!< PCR SLP_EN_4: CNT_TMER2_SLP_EN (Bit 4)                      */
#define PCR_SLP_EN_4_CNT_TMER2_SLP_EN_Msk     (0x10UL)                  /*!< PCR SLP_EN_4: CNT_TMER2_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_4_CNT_TMER3_SLP_EN_Pos     (5UL)                     /*!< PCR SLP_EN_4: CNT_TMER3_SLP_EN (Bit 5)                      */
#define PCR_SLP_EN_4_CNT_TMER3_SLP_EN_Msk     (0x20UL)                  /*!< PCR SLP_EN_4: CNT_TMER3_SLP_EN (Bitfield-Mask: 0x01)        */
#define PCR_SLP_EN_4_RTOS_SLP_EN_Pos          (6UL)                     /*!< PCR SLP_EN_4: RTOS_SLP_EN (Bit 6)                           */
#define PCR_SLP_EN_4_RTOS_SLP_EN_Msk          (0x40UL)                  /*!< PCR SLP_EN_4: RTOS_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_4_RPMPWM1_SLP_EN_Pos       (7UL)                     /*!< PCR SLP_EN_4: RPMPWM1_SLP_EN (Bit 7)                        */
#define PCR_SLP_EN_4_RPMPWM1_SLP_EN_Msk       (0x80UL)                  /*!< PCR SLP_EN_4: RPMPWM1_SLP_EN (Bitfield-Mask: 0x01)          */
#define PCR_SLP_EN_4_QSPI_SLP_EN_Pos          (8UL)                     /*!< PCR SLP_EN_4: QSPI_SLP_EN (Bit 8)                           */
#define PCR_SLP_EN_4_QSPI_SLP_EN_Msk          (0x100UL)                 /*!< PCR SLP_EN_4: QSPI_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_4_BCM1_SLP_EN_Pos          (9UL)                     /*!< PCR SLP_EN_4: BCM1_SLP_EN (Bit 9)                           */
#define PCR_SLP_EN_4_BCM1_SLP_EN_Msk          (0x200UL)                 /*!< PCR SLP_EN_4: BCM1_SLP_EN (Bitfield-Mask: 0x01)             */
#define PCR_SLP_EN_4_RC_ID0_SLP_EN_Pos        (10UL)                    /*!< PCR SLP_EN_4: RC_ID0_SLP_EN (Bit 10)                        */
#define PCR_SLP_EN_4_RC_ID0_SLP_EN_Msk        (0x400UL)                 /*!< PCR SLP_EN_4: RC_ID0_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_SLP_EN_4_RC_ID1_SLP_EN_Pos        (11UL)                    /*!< PCR SLP_EN_4: RC_ID1_SLP_EN (Bit 11)                        */
#define PCR_SLP_EN_4_RC_ID1_SLP_EN_Msk        (0x800UL)                 /*!< PCR SLP_EN_4: RC_ID1_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_SLP_EN_4_RC_ID2_SLP_EN_Pos        (12UL)                    /*!< PCR SLP_EN_4: RC_ID2_SLP_EN (Bit 12)                        */
#define PCR_SLP_EN_4_RC_ID2_SLP_EN_Msk        (0x1000UL)                /*!< PCR SLP_EN_4: RC_ID2_SLP_EN (Bitfield-Mask: 0x01)           */
#define PCR_SLP_EN_4_FCL_SLP_EN_Pos           (15UL)                    /*!< PCR SLP_EN_4: FCL_SLP_EN (Bit 15)                           */
#define PCR_SLP_EN_4_FCL_SLP_EN_Msk           (0x8000UL)                /*!< PCR SLP_EN_4: FCL_SLP_EN (Bitfield-Mask: 0x01)              */

/* --------------------------------  PCR_CLK_REQ_0  ------------------------------- */
#define PCR_CLK_REQ_0_JTAG_STAP_CLK_REQ_Pos   (0UL)                     /*!< PCR CLK_REQ_0: JTAG_STAP_CLK_REQ (Bit 0)                    */
#define PCR_CLK_REQ_0_JTAG_STAP_CLK_REQ_Msk   (0x1UL)                   /*!< PCR CLK_REQ_0: JTAG_STAP_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_0_EFUSE_CLK_REQ_Pos       (1UL)                     /*!< PCR CLK_REQ_0: EFUSE_CLK_REQ (Bit 1)                        */
#define PCR_CLK_REQ_0_EFUSE_CLK_REQ_Msk       (0x2UL)                   /*!< PCR CLK_REQ_0: EFUSE_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_0_ISPI_CLK_REQ_Pos        (2UL)                     /*!< PCR CLK_REQ_0: ISPI_CLK_REQ (Bit 2)                         */
#define PCR_CLK_REQ_0_ISPI_CLK_REQ_Msk        (0x4UL)                   /*!< PCR CLK_REQ_0: ISPI_CLK_REQ (Bitfield-Mask: 0x01)           */

/* --------------------------------  PCR_CLK_REQ_1  ------------------------------- */
#define PCR_CLK_REQ_1_INT_CLK_REQ_Pos         (0UL)                     /*!< PCR CLK_REQ_1: INT_CLK_REQ (Bit 0)                          */
#define PCR_CLK_REQ_1_INT_CLK_REQ_Msk         (0x1UL)                   /*!< PCR CLK_REQ_1: INT_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_1_PECI_CLK_REQ_Pos        (1UL)                     /*!< PCR CLK_REQ_1: PECI_CLK_REQ (Bit 1)                         */
#define PCR_CLK_REQ_1_PECI_CLK_REQ_Msk        (0x2UL)                   /*!< PCR CLK_REQ_1: PECI_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_TACH0_CLK_REQ_Pos       (2UL)                     /*!< PCR CLK_REQ_1: TACH0_CLK_REQ (Bit 2)                        */
#define PCR_CLK_REQ_1_TACH0_CLK_REQ_Msk       (0x4UL)                   /*!< PCR CLK_REQ_1: TACH0_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_1_PWM0_CLK_REQ_Pos        (4UL)                     /*!< PCR CLK_REQ_1: PWM0_CLK_REQ (Bit 4)                         */
#define PCR_CLK_REQ_1_PWM0_CLK_REQ_Msk        (0x10UL)                  /*!< PCR CLK_REQ_1: PWM0_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PMC_CLK_REQ_Pos         (5UL)                     /*!< PCR CLK_REQ_1: PMC_CLK_REQ (Bit 5)                          */
#define PCR_CLK_REQ_1_PMC_CLK_REQ_Msk         (0x20UL)                  /*!< PCR CLK_REQ_1: PMC_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_1_DMA_CLK_REQ_Pos         (6UL)                     /*!< PCR CLK_REQ_1: DMA_CLK_REQ (Bit 6)                          */
#define PCR_CLK_REQ_1_DMA_CLK_REQ_Msk         (0x40UL)                  /*!< PCR CLK_REQ_1: DMA_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_1_TFDP_CLK_REQ_Pos        (7UL)                     /*!< PCR CLK_REQ_1: TFDP_CLK_REQ (Bit 7)                         */
#define PCR_CLK_REQ_1_TFDP_CLK_REQ_Msk        (0x80UL)                  /*!< PCR CLK_REQ_1: TFDP_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PROCESSOR_CLK_REQ_Pos   (8UL)                     /*!< PCR CLK_REQ_1: PROCESSOR_CLK_REQ (Bit 8)                    */
#define PCR_CLK_REQ_1_PROCESSOR_CLK_REQ_Msk   (0x100UL)                 /*!< PCR CLK_REQ_1: PROCESSOR_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_1_WDT_CLK_REQ_Pos         (9UL)                     /*!< PCR CLK_REQ_1: WDT_CLK_REQ (Bit 9)                          */
#define PCR_CLK_REQ_1_WDT_CLK_REQ_Msk         (0x200UL)                 /*!< PCR CLK_REQ_1: WDT_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_1_SMB0_CLK_REQ_Pos        (10UL)                    /*!< PCR CLK_REQ_1: SMB0_CLK_REQ (Bit 10)                        */
#define PCR_CLK_REQ_1_SMB0_CLK_REQ_Msk        (0x400UL)                 /*!< PCR CLK_REQ_1: SMB0_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_TACH1_CLK_REQ_Pos       (11UL)                    /*!< PCR CLK_REQ_1: TACH1_CLK_REQ (Bit 11)                       */
#define PCR_CLK_REQ_1_TACH1_CLK_REQ_Msk       (0x800UL)                 /*!< PCR CLK_REQ_1: TACH1_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_1_TACH2_CLK_REQ_Pos       (12UL)                    /*!< PCR CLK_REQ_1: TACH2_CLK_REQ (Bit 12)                       */
#define PCR_CLK_REQ_1_TACH2_CLK_REQ_Msk       (0x1000UL)                /*!< PCR CLK_REQ_1: TACH2_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_1_PWM1_CLK_REQ_Pos        (20UL)                    /*!< PCR CLK_REQ_1: PWM1_CLK_REQ (Bit 20)                        */
#define PCR_CLK_REQ_1_PWM1_CLK_REQ_Msk        (0x100000UL)              /*!< PCR CLK_REQ_1: PWM1_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM2_CLK_REQ_Pos        (21UL)                    /*!< PCR CLK_REQ_1: PWM2_CLK_REQ (Bit 21)                        */
#define PCR_CLK_REQ_1_PWM2_CLK_REQ_Msk        (0x200000UL)              /*!< PCR CLK_REQ_1: PWM2_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM3_CLK_REQ_Pos        (22UL)                    /*!< PCR CLK_REQ_1: PWM3_CLK_REQ (Bit 22)                        */
#define PCR_CLK_REQ_1_PWM3_CLK_REQ_Msk        (0x400000UL)              /*!< PCR CLK_REQ_1: PWM3_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM4_CLK_REQ_Pos        (23UL)                    /*!< PCR CLK_REQ_1: PWM4_CLK_REQ (Bit 23)                        */
#define PCR_CLK_REQ_1_PWM4_CLK_REQ_Msk        (0x800000UL)              /*!< PCR CLK_REQ_1: PWM4_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM5_CLK_REQ_Pos        (24UL)                    /*!< PCR CLK_REQ_1: PWM5_CLK_REQ (Bit 24)                        */
#define PCR_CLK_REQ_1_PWM5_CLK_REQ_Msk        (0x1000000UL)             /*!< PCR CLK_REQ_1: PWM5_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM6_CLK_REQ_Pos        (25UL)                    /*!< PCR CLK_REQ_1: PWM6_CLK_REQ (Bit 25)                        */
#define PCR_CLK_REQ_1_PWM6_CLK_REQ_Msk        (0x2000000UL)             /*!< PCR CLK_REQ_1: PWM6_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM7_CLK_REQ_Pos        (26UL)                    /*!< PCR CLK_REQ_1: PWM7_CLK_REQ (Bit 26)                        */
#define PCR_CLK_REQ_1_PWM7_CLK_REQ_Msk        (0x4000000UL)             /*!< PCR CLK_REQ_1: PWM7_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_PWM8_CLK_REQ_Pos        (27UL)                    /*!< PCR CLK_REQ_1: PWM8_CLK_REQ (Bit 27)                        */
#define PCR_CLK_REQ_1_PWM8_CLK_REQ_Msk        (0x8000000UL)             /*!< PCR CLK_REQ_1: PWM8_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_1_EC_REG_BANK_CLK_REQ_Pos (29UL)                    /*!< PCR CLK_REQ_1: EC_REG_BANK_CLK_REQ (Bit 29)                 */
#define PCR_CLK_REQ_1_EC_REG_BANK_CLK_REQ_Msk (0x20000000UL)            /*!< PCR CLK_REQ_1: EC_REG_BANK_CLK_REQ (Bitfield-Mask: 0x01)    */
#define PCR_CLK_REQ_1_TIMER16_0_CLK_REQ_Pos   (30UL)                    /*!< PCR CLK_REQ_1: TIMER16_0_CLK_REQ (Bit 30)                   */
#define PCR_CLK_REQ_1_TIMER16_0_CLK_REQ_Msk   (0x40000000UL)            /*!< PCR CLK_REQ_1: TIMER16_0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_1_TIMER16_1_CLK_REQ_Pos   (31UL)                    /*!< PCR CLK_REQ_1: TIMER16_1_CLK_REQ (Bit 31)                   */
#define PCR_CLK_REQ_1_TIMER16_1_CLK_REQ_Msk   (0x80000000UL)            /*!< PCR CLK_REQ_1: TIMER16_1_CLK_REQ (Bitfield-Mask: 0x01)      */

/* --------------------------------  PCR_CLK_REQ_2  ------------------------------- */
#define PCR_CLK_REQ_2_LPC_CLK_REQ_Pos         (0UL)                     /*!< PCR CLK_REQ_2: LPC_CLK_REQ (Bit 0)                          */
#define PCR_CLK_REQ_2_LPC_CLK_REQ_Msk         (0x1UL)                   /*!< PCR CLK_REQ_2: LPC_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_2_UART_0_CLK_REQ_Pos      (1UL)                     /*!< PCR CLK_REQ_2: UART_0_CLK_REQ (Bit 1)                       */
#define PCR_CLK_REQ_2_UART_0_CLK_REQ_Msk      (0x2UL)                   /*!< PCR CLK_REQ_2: UART_0_CLK_REQ (Bitfield-Mask: 0x01)         */
#define PCR_CLK_REQ_2_UART_1_CLK_REQ_Pos      (2UL)                     /*!< PCR CLK_REQ_2: UART_1_CLK_REQ (Bit 2)                       */
#define PCR_CLK_REQ_2_UART_1_CLK_REQ_Msk      (0x4UL)                   /*!< PCR CLK_REQ_2: UART_1_CLK_REQ (Bitfield-Mask: 0x01)         */
#define PCR_CLK_REQ_2_GLBL_CFG_CLK_REQ_Pos    (12UL)                    /*!< PCR CLK_REQ_2: GLBL_CFG_CLK_REQ (Bit 12)                    */
#define PCR_CLK_REQ_2_GLBL_CFG_CLK_REQ_Msk    (0x1000UL)                /*!< PCR CLK_REQ_2: GLBL_CFG_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_CLK_REQ_2_ACPI_EC_0_CLK_REQ_Pos   (13UL)                    /*!< PCR CLK_REQ_2: ACPI_EC_0_CLK_REQ (Bit 13)                   */
#define PCR_CLK_REQ_2_ACPI_EC_0_CLK_REQ_Msk   (0x2000UL)                /*!< PCR CLK_REQ_2: ACPI_EC_0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_2_ACPI_EC_1_CLK_REQ_Pos   (14UL)                    /*!< PCR CLK_REQ_2: ACPI_EC_1_CLK_REQ (Bit 14)                   */
#define PCR_CLK_REQ_2_ACPI_EC_1_CLK_REQ_Msk   (0x4000UL)                /*!< PCR CLK_REQ_2: ACPI_EC_1_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_2_ACPI_PM1_CLK_REQ_Pos    (15UL)                    /*!< PCR CLK_REQ_2: ACPI_PM1_CLK_REQ (Bit 15)                    */
#define PCR_CLK_REQ_2_ACPI_PM1_CLK_REQ_Msk    (0x8000UL)                /*!< PCR CLK_REQ_2: ACPI_PM1_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_CLK_REQ_2_KBCEM_CLK_REQ_Pos       (16UL)                    /*!< PCR CLK_REQ_2: KBCEM_CLK_REQ (Bit 16)                       */
#define PCR_CLK_REQ_2_KBCEM_CLK_REQ_Msk       (0x10000UL)               /*!< PCR CLK_REQ_2: KBCEM_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_2_MBX_CLK_REQ_Pos         (17UL)                    /*!< PCR CLK_REQ_2: MBX_CLK_REQ (Bit 17)                         */
#define PCR_CLK_REQ_2_MBX_CLK_REQ_Msk         (0x20000UL)               /*!< PCR CLK_REQ_2: MBX_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_2_RTC_CLK_REQ_Pos         (18UL)                    /*!< PCR CLK_REQ_2: RTC_CLK_REQ (Bit 18)                         */
#define PCR_CLK_REQ_2_RTC_CLK_REQ_Msk         (0x40000UL)               /*!< PCR CLK_REQ_2: RTC_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_2_ESPI_CLK_REQ_Pos        (19UL)                    /*!< PCR CLK_REQ_2: ESPI_CLK_REQ (Bit 19)                        */
#define PCR_CLK_REQ_2_ESPI_CLK_REQ_Msk        (0x80000UL)               /*!< PCR CLK_REQ_2: ESPI_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_2_ACPI_EC_2_CLK_REQ_Pos   (21UL)                    /*!< PCR CLK_REQ_2: ACPI_EC_2_CLK_REQ (Bit 21)                   */
#define PCR_CLK_REQ_2_ACPI_EC_2_CLK_REQ_Msk   (0x200000UL)              /*!< PCR CLK_REQ_2: ACPI_EC_2_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_2_ACPI_EC_3_CLK_REQ_Pos   (22UL)                    /*!< PCR CLK_REQ_2: ACPI_EC_3_CLK_REQ (Bit 22)                   */
#define PCR_CLK_REQ_2_ACPI_EC_3_CLK_REQ_Msk   (0x400000UL)              /*!< PCR CLK_REQ_2: ACPI_EC_3_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_2_ACPI_EC_4_CLK_REQ_Pos   (23UL)                    /*!< PCR CLK_REQ_2: ACPI_EC_4_CLK_REQ (Bit 23)                   */
#define PCR_CLK_REQ_2_ACPI_EC_4_CLK_REQ_Msk   (0x800000UL)              /*!< PCR CLK_REQ_2: ACPI_EC_4_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_2_ASIF_CLK_REQ_Pos        (24UL)                    /*!< PCR CLK_REQ_2: ASIF_CLK_REQ (Bit 24)                        */
#define PCR_CLK_REQ_2_ASIF_CLK_REQ_Msk        (0x1000000UL)             /*!< PCR CLK_REQ_2: ASIF_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_2_PORT80_0_CLK_REQ_Pos    (25UL)                    /*!< PCR CLK_REQ_2: PORT80_0_CLK_REQ (Bit 25)                    */
#define PCR_CLK_REQ_2_PORT80_0_CLK_REQ_Msk    (0x2000000UL)             /*!< PCR CLK_REQ_2: PORT80_0_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_CLK_REQ_2_PORT80_1_CLK_REQ_Pos    (26UL)                    /*!< PCR CLK_REQ_2: PORT80_1_CLK_REQ (Bit 26)                    */
#define PCR_CLK_REQ_2_PORT80_1_CLK_REQ_Msk    (0x4000000UL)             /*!< PCR CLK_REQ_2: PORT80_1_CLK_REQ (Bitfield-Mask: 0x01)       */

/* --------------------------------  PCR_CLK_REQ_3  ------------------------------- */
#define PCR_CLK_REQ_3_ADC_CLK_REQ_Pos         (3UL)                     /*!< PCR CLK_REQ_3: ADC_CLK_REQ (Bit 3)                          */
#define PCR_CLK_REQ_3_ADC_CLK_REQ_Msk         (0x8UL)                   /*!< PCR CLK_REQ_3: ADC_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_3_PS2_0_CLK_REQ_Pos       (5UL)                     /*!< PCR CLK_REQ_3: PS2_0_CLK_REQ (Bit 5)                        */
#define PCR_CLK_REQ_3_PS2_0_CLK_REQ_Msk       (0x20UL)                  /*!< PCR CLK_REQ_3: PS2_0_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_3_PS2_1_CLK_REQ_Pos       (6UL)                     /*!< PCR CLK_REQ_3: PS2_1_CLK_REQ (Bit 6)                        */
#define PCR_CLK_REQ_3_PS2_1_CLK_REQ_Msk       (0x40UL)                  /*!< PCR CLK_REQ_3: PS2_1_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_3_PS2_2_CLK_REQ_Pos       (7UL)                     /*!< PCR CLK_REQ_3: PS2_2_CLK_REQ (Bit 7)                        */
#define PCR_CLK_REQ_3_PS2_2_CLK_REQ_Msk       (0x80UL)                  /*!< PCR CLK_REQ_3: PS2_2_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_3_GP_SPI0_CLK_REQ_Pos     (9UL)                     /*!< PCR CLK_REQ_3: GP_SPI0_CLK_REQ (Bit 9)                      */
#define PCR_CLK_REQ_3_GP_SPI0_CLK_REQ_Msk     (0x200UL)                 /*!< PCR CLK_REQ_3: GP_SPI0_CLK_REQ (Bitfield-Mask: 0x01)        */
#define PCR_CLK_REQ_3_HTIMER_0_CLK_REQ_Pos    (10UL)                    /*!< PCR CLK_REQ_3: HTIMER_0_CLK_REQ (Bit 10)                    */
#define PCR_CLK_REQ_3_HTIMER_0_CLK_REQ_Msk    (0x400UL)                 /*!< PCR CLK_REQ_3: HTIMER_0_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_CLK_REQ_3_KEYSCAN_CLK_REQ_Pos     (11UL)                    /*!< PCR CLK_REQ_3: KEYSCAN_CLK_REQ (Bit 11)                     */
#define PCR_CLK_REQ_3_KEYSCAN_CLK_REQ_Msk     (0x800UL)                 /*!< PCR CLK_REQ_3: KEYSCAN_CLK_REQ (Bitfield-Mask: 0x01)        */
#define PCR_CLK_REQ_3_RPMPWM0_CLK_REQ_Pos     (12UL)                    /*!< PCR CLK_REQ_3: RPMPWM0_CLK_REQ (Bit 12)                     */
#define PCR_CLK_REQ_3_RPMPWM0_CLK_REQ_Msk     (0x1000UL)                /*!< PCR CLK_REQ_3: RPMPWM0_CLK_REQ (Bitfield-Mask: 0x01)        */
#define PCR_CLK_REQ_3_SMB1_CLK_REQ_Pos        (13UL)                    /*!< PCR CLK_REQ_3: SMB1_CLK_REQ (Bit 13)                        */
#define PCR_CLK_REQ_3_SMB1_CLK_REQ_Msk        (0x2000UL)                /*!< PCR CLK_REQ_3: SMB1_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_SMB2_CLK_REQ_Pos        (14UL)                    /*!< PCR CLK_REQ_3: SMB2_CLK_REQ (Bit 14)                        */
#define PCR_CLK_REQ_3_SMB2_CLK_REQ_Msk        (0x4000UL)                /*!< PCR CLK_REQ_3: SMB2_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_SMB3_CLK_REQ_Pos        (15UL)                    /*!< PCR CLK_REQ_3: SMB3_CLK_REQ (Bit 15)                        */
#define PCR_CLK_REQ_3_SMB3_CLK_REQ_Msk        (0x8000UL)                /*!< PCR CLK_REQ_3: SMB3_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_LED0_CLK_REQ_Pos        (16UL)                    /*!< PCR CLK_REQ_3: LED0_CLK_REQ (Bit 16)                        */
#define PCR_CLK_REQ_3_LED0_CLK_REQ_Msk        (0x10000UL)               /*!< PCR CLK_REQ_3: LED0_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_LED1_CLK_REQ_Pos        (17UL)                    /*!< PCR CLK_REQ_3: LED1_CLK_REQ (Bit 17)                        */
#define PCR_CLK_REQ_3_LED1_CLK_REQ_Msk        (0x20000UL)               /*!< PCR CLK_REQ_3: LED1_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_LED2_CLK_REQ_Pos        (18UL)                    /*!< PCR CLK_REQ_3: LED2_CLK_REQ (Bit 18)                        */
#define PCR_CLK_REQ_3_LED2_CLK_REQ_Msk        (0x40000UL)               /*!< PCR CLK_REQ_3: LED2_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_BCM0_CLK_REQ_Pos        (19UL)                    /*!< PCR CLK_REQ_3: BCM0_CLK_REQ (Bit 19)                        */
#define PCR_CLK_REQ_3_BCM0_CLK_REQ_Msk        (0x80000UL)               /*!< PCR CLK_REQ_3: BCM0_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_GP_SPI1_CLK_REQ_Pos     (20UL)                    /*!< PCR CLK_REQ_3: GP_SPI1_CLK_REQ (Bit 20)                     */
#define PCR_CLK_REQ_3_GP_SPI1_CLK_REQ_Msk     (0x100000UL)              /*!< PCR CLK_REQ_3: GP_SPI1_CLK_REQ (Bitfield-Mask: 0x01)        */
#define PCR_CLK_REQ_3_TIMER16_2_CLK_REQ_Pos   (21UL)                    /*!< PCR CLK_REQ_3: TIMER16_2_CLK_REQ (Bit 21)                   */
#define PCR_CLK_REQ_3_TIMER16_2_CLK_REQ_Msk   (0x200000UL)              /*!< PCR CLK_REQ_3: TIMER16_2_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_3_TIMER16_3_CLK_REQ_Pos   (22UL)                    /*!< PCR CLK_REQ_3: TIMER16_3_CLK_REQ (Bit 22)                   */
#define PCR_CLK_REQ_3_TIMER16_3_CLK_REQ_Msk   (0x400000UL)              /*!< PCR CLK_REQ_3: TIMER16_3_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_3_TIMER32_0_CLK_REQ_Pos   (23UL)                    /*!< PCR CLK_REQ_3: TIMER32_0_CLK_REQ (Bit 23)                   */
#define PCR_CLK_REQ_3_TIMER32_0_CLK_REQ_Msk   (0x800000UL)              /*!< PCR CLK_REQ_3: TIMER32_0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_3_TIMER32_1_CLK_REQ_Pos   (24UL)                    /*!< PCR CLK_REQ_3: TIMER32_1_CLK_REQ (Bit 24)                   */
#define PCR_CLK_REQ_3_TIMER32_1_CLK_REQ_Msk   (0x1000000UL)             /*!< PCR CLK_REQ_3: TIMER32_1_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_3_LED3_CLK_REQ_Pos        (25UL)                    /*!< PCR CLK_REQ_3: LED3_CLK_REQ (Bit 25)                        */
#define PCR_CLK_REQ_3_LED3_CLK_REQ_Msk        (0x2000000UL)             /*!< PCR CLK_REQ_3: LED3_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_3_PKE_CLK_REQ_Pos         (26UL)                    /*!< PCR CLK_REQ_3: PKE_CLK_REQ (Bit 26)                         */
#define PCR_CLK_REQ_3_PKE_CLK_REQ_Msk         (0x4000000UL)             /*!< PCR CLK_REQ_3: PKE_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_3_RNG_CLK_REQ_Pos         (27UL)                    /*!< PCR CLK_REQ_3: RNG_CLK_REQ (Bit 27)                         */
#define PCR_CLK_REQ_3_RNG_CLK_REQ_Msk         (0x8000000UL)             /*!< PCR CLK_REQ_3: RNG_CLK_REQ (Bitfield-Mask: 0x01)            */
#define PCR_CLK_REQ_3_AES_HASH_CLK_REQ_Pos    (28UL)                    /*!< PCR CLK_REQ_3: AES_HASH_CLK_REQ (Bit 28)                    */
#define PCR_CLK_REQ_3_AES_HASH_CLK_REQ_Msk    (0x10000000UL)            /*!< PCR CLK_REQ_3: AES_HASH_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_CLK_REQ_3_HTIMER_1_CLK_REQ_Pos    (29UL)                    /*!< PCR CLK_REQ_3: HTIMER_1_CLK_REQ (Bit 29)                    */
#define PCR_CLK_REQ_3_HTIMER_1_CLK_REQ_Msk    (0x20000000UL)            /*!< PCR CLK_REQ_3: HTIMER_1_CLK_REQ (Bitfield-Mask: 0x01)       */
#define PCR_CLK_REQ_3_CCTIMER_CLK_REQ_Pos     (30UL)                    /*!< PCR CLK_REQ_3: CCTIMER_CLK_REQ (Bit 30)                     */
#define PCR_CLK_REQ_3_CCTIMER_CLK_REQ_Msk     (0x40000000UL)            /*!< PCR CLK_REQ_3: CCTIMER_CLK_REQ (Bitfield-Mask: 0x01)        */
#define PCR_CLK_REQ_3_PWM9_CLK_REQ_Pos        (31UL)                    /*!< PCR CLK_REQ_3: PWM9_CLK_REQ (Bit 31)                        */
#define PCR_CLK_REQ_3_PWM9_CLK_REQ_Msk        (0x80000000UL)            /*!< PCR CLK_REQ_3: PWM9_CLK_REQ (Bitfield-Mask: 0x01)           */

/* --------------------------------  PCR_CLK_REQ_4  ------------------------------- */
#define PCR_CLK_REQ_4_PWM10_CLK_REQ_Pos       (0UL)                     /*!< PCR CLK_REQ_4: PWM10_CLK_REQ (Bit 0)                        */
#define PCR_CLK_REQ_4_PWM10_CLK_REQ_Msk       (0x1UL)                   /*!< PCR CLK_REQ_4: PWM10_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_4_PWM11_CLK_REQ_Pos       (1UL)                     /*!< PCR CLK_REQ_4: PWM11_CLK_REQ (Bit 1)                        */
#define PCR_CLK_REQ_4_PWM11_CLK_REQ_Msk       (0x2UL)                   /*!< PCR CLK_REQ_4: PWM11_CLK_REQ (Bitfield-Mask: 0x01)          */
#define PCR_CLK_REQ_4_CNT_TMER0_CLK_REQ_Pos   (2UL)                     /*!< PCR CLK_REQ_4: CNT_TMER0_CLK_REQ (Bit 2)                    */
#define PCR_CLK_REQ_4_CNT_TMER0_CLK_REQ_Msk   (0x4UL)                   /*!< PCR CLK_REQ_4: CNT_TMER0_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_4_CNT_TMER1_CLK_REQ_Pos   (3UL)                     /*!< PCR CLK_REQ_4: CNT_TMER1_CLK_REQ (Bit 3)                    */
#define PCR_CLK_REQ_4_CNT_TMER1_CLK_REQ_Msk   (0x8UL)                   /*!< PCR CLK_REQ_4: CNT_TMER1_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_4_CNT_TMER2_CLK_REQ_Pos   (4UL)                     /*!< PCR CLK_REQ_4: CNT_TMER2_CLK_REQ (Bit 4)                    */
#define PCR_CLK_REQ_4_CNT_TMER2_CLK_REQ_Msk   (0x10UL)                  /*!< PCR CLK_REQ_4: CNT_TMER2_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_4_CNT_TMER3_CLK_REQ_Pos   (5UL)                     /*!< PCR CLK_REQ_4: CNT_TMER3_CLK_REQ (Bit 5)                    */
#define PCR_CLK_REQ_4_CNT_TMER3_CLK_REQ_Msk   (0x20UL)                  /*!< PCR CLK_REQ_4: CNT_TMER3_CLK_REQ (Bitfield-Mask: 0x01)      */
#define PCR_CLK_REQ_4_RTOS_CLK_REQ_Pos        (6UL)                     /*!< PCR CLK_REQ_4: RTOS_CLK_REQ (Bit 6)                         */
#define PCR_CLK_REQ_4_RTOS_CLK_REQ_Msk        (0x40UL)                  /*!< PCR CLK_REQ_4: RTOS_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_4_RPMPWM1_CLK_REQ_Pos     (7UL)                     /*!< PCR CLK_REQ_4: RPMPWM1_CLK_REQ (Bit 7)                      */
#define PCR_CLK_REQ_4_RPMPWM1_CLK_REQ_Msk     (0x80UL)                  /*!< PCR CLK_REQ_4: RPMPWM1_CLK_REQ (Bitfield-Mask: 0x01)        */
#define PCR_CLK_REQ_4_QSPI_CLK_REQ_Pos        (8UL)                     /*!< PCR CLK_REQ_4: QSPI_CLK_REQ (Bit 8)                         */
#define PCR_CLK_REQ_4_QSPI_CLK_REQ_Msk        (0x100UL)                 /*!< PCR CLK_REQ_4: QSPI_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_4_BCM1_CLK_REQ_Pos        (9UL)                     /*!< PCR CLK_REQ_4: BCM1_CLK_REQ (Bit 9)                         */
#define PCR_CLK_REQ_4_BCM1_CLK_REQ_Msk        (0x200UL)                 /*!< PCR CLK_REQ_4: BCM1_CLK_REQ (Bitfield-Mask: 0x01)           */
#define PCR_CLK_REQ_4_RC_ID0_CLK_REQ_Pos      (10UL)                    /*!< PCR CLK_REQ_4: RC_ID0_CLK_REQ (Bit 10)                      */
#define PCR_CLK_REQ_4_RC_ID0_CLK_REQ_Msk      (0x400UL)                 /*!< PCR CLK_REQ_4: RC_ID0_CLK_REQ (Bitfield-Mask: 0x01)         */
#define PCR_CLK_REQ_4_RC_ID1_CLK_REQ_Pos      (11UL)                    /*!< PCR CLK_REQ_4: RC_ID1_CLK_REQ (Bit 11)                      */
#define PCR_CLK_REQ_4_RC_ID1_CLK_REQ_Msk      (0x800UL)                 /*!< PCR CLK_REQ_4: RC_ID1_CLK_REQ (Bitfield-Mask: 0x01)         */
#define PCR_CLK_REQ_4_RC_ID2_CLK_REQ_Pos      (12UL)                    /*!< PCR CLK_REQ_4: RC_ID2_CLK_REQ (Bit 12)                      */
#define PCR_CLK_REQ_4_RC_ID2_CLK_REQ_Msk      (0x1000UL)                /*!< PCR CLK_REQ_4: RC_ID2_CLK_REQ (Bitfield-Mask: 0x01)         */
#define PCR_CLK_REQ_4_FCL_CLK_REQ_Pos         (15UL)                    /*!< PCR CLK_REQ_4: FCL_CLK_REQ (Bit 15)                         */
#define PCR_CLK_REQ_4_FCL_CLK_REQ_Msk         (0x8000UL)                /*!< PCR CLK_REQ_4: FCL_CLK_REQ (Bitfield-Mask: 0x01)            */

/* --------------------------------  PCR_RST_EN_0  -------------------------------- */
#define PCR_RST_EN_0_JTAG_STAP_RST_EN_Pos     (0UL)                     /*!< PCR RST_EN_0: JTAG_STAP_RST_EN (Bit 0)                      */
#define PCR_RST_EN_0_JTAG_STAP_RST_EN_Msk     (0x1UL)                   /*!< PCR RST_EN_0: JTAG_STAP_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_0_EFUSE_RST_EN_Pos         (1UL)                     /*!< PCR RST_EN_0: EFUSE_RST_EN (Bit 1)                          */
#define PCR_RST_EN_0_EFUSE_RST_EN_Msk         (0x2UL)                   /*!< PCR RST_EN_0: EFUSE_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_0_ISPI_RST_EN_Pos          (2UL)                     /*!< PCR RST_EN_0: ISPI_RST_EN (Bit 2)                           */
#define PCR_RST_EN_0_ISPI_RST_EN_Msk          (0x4UL)                   /*!< PCR RST_EN_0: ISPI_RST_EN (Bitfield-Mask: 0x01)             */

/* --------------------------------  PCR_RST_EN_1  -------------------------------- */
#define PCR_RST_EN_1_INT_RST_EN_Pos           (0UL)                     /*!< PCR RST_EN_1: INT_RST_EN (Bit 0)                            */
#define PCR_RST_EN_1_INT_RST_EN_Msk           (0x1UL)                   /*!< PCR RST_EN_1: INT_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_1_PECI_RST_EN_Pos          (1UL)                     /*!< PCR RST_EN_1: PECI_RST_EN (Bit 1)                           */
#define PCR_RST_EN_1_PECI_RST_EN_Msk          (0x2UL)                   /*!< PCR RST_EN_1: PECI_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_TACH0_RST_EN_Pos         (2UL)                     /*!< PCR RST_EN_1: TACH0_RST_EN (Bit 2)                          */
#define PCR_RST_EN_1_TACH0_RST_EN_Msk         (0x4UL)                   /*!< PCR RST_EN_1: TACH0_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_1_PWM0_RST_EN_Pos          (4UL)                     /*!< PCR RST_EN_1: PWM0_RST_EN (Bit 4)                           */
#define PCR_RST_EN_1_PWM0_RST_EN_Msk          (0x10UL)                  /*!< PCR RST_EN_1: PWM0_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PMC_RST_EN_Pos           (5UL)                     /*!< PCR RST_EN_1: PMC_RST_EN (Bit 5)                            */
#define PCR_RST_EN_1_PMC_RST_EN_Msk           (0x20UL)                  /*!< PCR RST_EN_1: PMC_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_1_DMA_RST_EN_Pos           (6UL)                     /*!< PCR RST_EN_1: DMA_RST_EN (Bit 6)                            */
#define PCR_RST_EN_1_DMA_RST_EN_Msk           (0x40UL)                  /*!< PCR RST_EN_1: DMA_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_1_TFDP_RST_EN_Pos          (7UL)                     /*!< PCR RST_EN_1: TFDP_RST_EN (Bit 7)                           */
#define PCR_RST_EN_1_TFDP_RST_EN_Msk          (0x80UL)                  /*!< PCR RST_EN_1: TFDP_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PROCESSOR_RST_EN_Pos     (8UL)                     /*!< PCR RST_EN_1: PROCESSOR_RST_EN (Bit 8)                      */
#define PCR_RST_EN_1_PROCESSOR_RST_EN_Msk     (0x100UL)                 /*!< PCR RST_EN_1: PROCESSOR_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_1_WDT_RST_EN_Pos           (9UL)                     /*!< PCR RST_EN_1: WDT_RST_EN (Bit 9)                            */
#define PCR_RST_EN_1_WDT_RST_EN_Msk           (0x200UL)                 /*!< PCR RST_EN_1: WDT_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_1_SMB0_RST_EN_Pos          (10UL)                    /*!< PCR RST_EN_1: SMB0_RST_EN (Bit 10)                          */
#define PCR_RST_EN_1_SMB0_RST_EN_Msk          (0x400UL)                 /*!< PCR RST_EN_1: SMB0_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_TACH1_RST_EN_Pos         (11UL)                    /*!< PCR RST_EN_1: TACH1_RST_EN (Bit 11)                         */
#define PCR_RST_EN_1_TACH1_RST_EN_Msk         (0x800UL)                 /*!< PCR RST_EN_1: TACH1_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_1_TACH2_RST_EN_Pos         (12UL)                    /*!< PCR RST_EN_1: TACH2_RST_EN (Bit 12)                         */
#define PCR_RST_EN_1_TACH2_RST_EN_Msk         (0x1000UL)                /*!< PCR RST_EN_1: TACH2_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_1_PWM1_RST_EN_Pos          (20UL)                    /*!< PCR RST_EN_1: PWM1_RST_EN (Bit 20)                          */
#define PCR_RST_EN_1_PWM1_RST_EN_Msk          (0x100000UL)              /*!< PCR RST_EN_1: PWM1_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM2_RST_EN_Pos          (21UL)                    /*!< PCR RST_EN_1: PWM2_RST_EN (Bit 21)                          */
#define PCR_RST_EN_1_PWM2_RST_EN_Msk          (0x200000UL)              /*!< PCR RST_EN_1: PWM2_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM3_RST_EN_Pos          (22UL)                    /*!< PCR RST_EN_1: PWM3_RST_EN (Bit 22)                          */
#define PCR_RST_EN_1_PWM3_RST_EN_Msk          (0x400000UL)              /*!< PCR RST_EN_1: PWM3_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM4_RST_EN_Pos          (23UL)                    /*!< PCR RST_EN_1: PWM4_RST_EN (Bit 23)                          */
#define PCR_RST_EN_1_PWM4_RST_EN_Msk          (0x800000UL)              /*!< PCR RST_EN_1: PWM4_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM5_RST_EN_Pos          (24UL)                    /*!< PCR RST_EN_1: PWM5_RST_EN (Bit 24)                          */
#define PCR_RST_EN_1_PWM5_RST_EN_Msk          (0x1000000UL)             /*!< PCR RST_EN_1: PWM5_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM6_RST_EN_Pos          (25UL)                    /*!< PCR RST_EN_1: PWM6_RST_EN (Bit 25)                          */
#define PCR_RST_EN_1_PWM6_RST_EN_Msk          (0x2000000UL)             /*!< PCR RST_EN_1: PWM6_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM7_RST_EN_Pos          (26UL)                    /*!< PCR RST_EN_1: PWM7_RST_EN (Bit 26)                          */
#define PCR_RST_EN_1_PWM7_RST_EN_Msk          (0x4000000UL)             /*!< PCR RST_EN_1: PWM7_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_PWM8_RST_EN_Pos          (27UL)                    /*!< PCR RST_EN_1: PWM8_RST_EN (Bit 27)                          */
#define PCR_RST_EN_1_PWM8_RST_EN_Msk          (0x8000000UL)             /*!< PCR RST_EN_1: PWM8_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_1_EC_REG_BANK_RST_EN_Pos   (29UL)                    /*!< PCR RST_EN_1: EC_REG_BANK_RST_EN (Bit 29)                   */
#define PCR_RST_EN_1_EC_REG_BANK_RST_EN_Msk   (0x20000000UL)            /*!< PCR RST_EN_1: EC_REG_BANK_RST_EN (Bitfield-Mask: 0x01)      */
#define PCR_RST_EN_1_TIMER16_0_RST_EN_Pos     (30UL)                    /*!< PCR RST_EN_1: TIMER16_0_RST_EN (Bit 30)                     */
#define PCR_RST_EN_1_TIMER16_0_RST_EN_Msk     (0x40000000UL)            /*!< PCR RST_EN_1: TIMER16_0_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_1_TIMER16_1_RST_EN_Pos     (31UL)                    /*!< PCR RST_EN_1: TIMER16_1_RST_EN (Bit 31)                     */
#define PCR_RST_EN_1_TIMER16_1_RST_EN_Msk     (0x80000000UL)            /*!< PCR RST_EN_1: TIMER16_1_RST_EN (Bitfield-Mask: 0x01)        */

/* --------------------------------  PCR_RST_EN_2  -------------------------------- */
#define PCR_RST_EN_2_LPC_RST_EN_Pos           (0UL)                     /*!< PCR RST_EN_2: LPC_RST_EN (Bit 0)                            */
#define PCR_RST_EN_2_LPC_RST_EN_Msk           (0x1UL)                   /*!< PCR RST_EN_2: LPC_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_2_UART_0_RST_EN_Pos        (1UL)                     /*!< PCR RST_EN_2: UART_0_RST_EN (Bit 1)                         */
#define PCR_RST_EN_2_UART_0_RST_EN_Msk        (0x2UL)                   /*!< PCR RST_EN_2: UART_0_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_RST_EN_2_UART_1_RST_EN_Pos        (2UL)                     /*!< PCR RST_EN_2: UART_1_RST_EN (Bit 2)                         */
#define PCR_RST_EN_2_UART_1_RST_EN_Msk        (0x4UL)                   /*!< PCR RST_EN_2: UART_1_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_RST_EN_2_GLBL_CFG_RST_EN_Pos      (12UL)                    /*!< PCR RST_EN_2: GLBL_CFG_RST_EN (Bit 12)                      */
#define PCR_RST_EN_2_GLBL_CFG_RST_EN_Msk      (0x1000UL)                /*!< PCR RST_EN_2: GLBL_CFG_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_RST_EN_2_ACPI_EC_0_RST_EN_Pos     (13UL)                    /*!< PCR RST_EN_2: ACPI_EC_0_RST_EN (Bit 13)                     */
#define PCR_RST_EN_2_ACPI_EC_0_RST_EN_Msk     (0x2000UL)                /*!< PCR RST_EN_2: ACPI_EC_0_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_2_ACPI_EC_1_RST_EN_Pos     (14UL)                    /*!< PCR RST_EN_2: ACPI_EC_1_RST_EN (Bit 14)                     */
#define PCR_RST_EN_2_ACPI_EC_1_RST_EN_Msk     (0x4000UL)                /*!< PCR RST_EN_2: ACPI_EC_1_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_2_ACPI_PM1_RST_EN_Pos      (15UL)                    /*!< PCR RST_EN_2: ACPI_PM1_RST_EN (Bit 15)                      */
#define PCR_RST_EN_2_ACPI_PM1_RST_EN_Msk      (0x8000UL)                /*!< PCR RST_EN_2: ACPI_PM1_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_RST_EN_2_KBCEM_RST_EN_Pos         (16UL)                    /*!< PCR RST_EN_2: KBCEM_RST_EN (Bit 16)                         */
#define PCR_RST_EN_2_KBCEM_RST_EN_Msk         (0x10000UL)               /*!< PCR RST_EN_2: KBCEM_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_2_MBX_RST_EN_Pos           (17UL)                    /*!< PCR RST_EN_2: MBX_RST_EN (Bit 17)                           */
#define PCR_RST_EN_2_MBX_RST_EN_Msk           (0x20000UL)               /*!< PCR RST_EN_2: MBX_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_2_RTC_RST_EN_Pos           (18UL)                    /*!< PCR RST_EN_2: RTC_RST_EN (Bit 18)                           */
#define PCR_RST_EN_2_RTC_RST_EN_Msk           (0x40000UL)               /*!< PCR RST_EN_2: RTC_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_2_ESPI_RST_EN_Pos          (19UL)                    /*!< PCR RST_EN_2: ESPI_RST_EN (Bit 19)                          */
#define PCR_RST_EN_2_ESPI_RST_EN_Msk          (0x80000UL)               /*!< PCR RST_EN_2: ESPI_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_2_ACPI_EC_2_RST_EN_Pos     (21UL)                    /*!< PCR RST_EN_2: ACPI_EC_2_RST_EN (Bit 21)                     */
#define PCR_RST_EN_2_ACPI_EC_2_RST_EN_Msk     (0x200000UL)              /*!< PCR RST_EN_2: ACPI_EC_2_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_2_ACPI_EC_3_RST_EN_Pos     (22UL)                    /*!< PCR RST_EN_2: ACPI_EC_3_RST_EN (Bit 22)                     */
#define PCR_RST_EN_2_ACPI_EC_3_RST_EN_Msk     (0x400000UL)              /*!< PCR RST_EN_2: ACPI_EC_3_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_2_ACPI_EC_4_RST_EN_Pos     (23UL)                    /*!< PCR RST_EN_2: ACPI_EC_4_RST_EN (Bit 23)                     */
#define PCR_RST_EN_2_ACPI_EC_4_RST_EN_Msk     (0x800000UL)              /*!< PCR RST_EN_2: ACPI_EC_4_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_2_ASIF_RST_EN_Pos          (24UL)                    /*!< PCR RST_EN_2: ASIF_RST_EN (Bit 24)                          */
#define PCR_RST_EN_2_ASIF_RST_EN_Msk          (0x1000000UL)             /*!< PCR RST_EN_2: ASIF_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_2_PORT80_0_RST_EN_Pos      (25UL)                    /*!< PCR RST_EN_2: PORT80_0_RST_EN (Bit 25)                      */
#define PCR_RST_EN_2_PORT80_0_RST_EN_Msk      (0x2000000UL)             /*!< PCR RST_EN_2: PORT80_0_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_RST_EN_2_PORT80_1_RST_EN_Pos      (26UL)                    /*!< PCR RST_EN_2: PORT80_1_RST_EN (Bit 26)                      */
#define PCR_RST_EN_2_PORT80_1_RST_EN_Msk      (0x4000000UL)             /*!< PCR RST_EN_2: PORT80_1_RST_EN (Bitfield-Mask: 0x01)         */

/* --------------------------------  PCR_RST_EN_3  -------------------------------- */
#define PCR_RST_EN_3_ADC_RST_EN_Pos           (3UL)                     /*!< PCR RST_EN_3: ADC_RST_EN (Bit 3)                            */
#define PCR_RST_EN_3_ADC_RST_EN_Msk           (0x8UL)                   /*!< PCR RST_EN_3: ADC_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_3_PS2_0_RST_EN_Pos         (5UL)                     /*!< PCR RST_EN_3: PS2_0_RST_EN (Bit 5)                          */
#define PCR_RST_EN_3_PS2_0_RST_EN_Msk         (0x20UL)                  /*!< PCR RST_EN_3: PS2_0_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_3_PS2_1_RST_EN_Pos         (6UL)                     /*!< PCR RST_EN_3: PS2_1_RST_EN (Bit 6)                          */
#define PCR_RST_EN_3_PS2_1_RST_EN_Msk         (0x40UL)                  /*!< PCR RST_EN_3: PS2_1_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_3_PS2_2_RST_EN_Pos         (7UL)                     /*!< PCR RST_EN_3: PS2_2_RST_EN (Bit 7)                          */
#define PCR_RST_EN_3_PS2_2_RST_EN_Msk         (0x80UL)                  /*!< PCR RST_EN_3: PS2_2_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_3_GP_SPI0_RST_EN_Pos       (9UL)                     /*!< PCR RST_EN_3: GP_SPI0_RST_EN (Bit 9)                        */
#define PCR_RST_EN_3_GP_SPI0_RST_EN_Msk       (0x200UL)                 /*!< PCR RST_EN_3: GP_SPI0_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_RST_EN_3_HTIMER_0_RST_EN_Pos      (10UL)                    /*!< PCR RST_EN_3: HTIMER_0_RST_EN (Bit 10)                      */
#define PCR_RST_EN_3_HTIMER_0_RST_EN_Msk      (0x400UL)                 /*!< PCR RST_EN_3: HTIMER_0_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_RST_EN_3_KEYSCAN_RST_EN_Pos       (11UL)                    /*!< PCR RST_EN_3: KEYSCAN_RST_EN (Bit 11)                       */
#define PCR_RST_EN_3_KEYSCAN_RST_EN_Msk       (0x800UL)                 /*!< PCR RST_EN_3: KEYSCAN_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_RST_EN_3_RPMPWM0_RST_EN_Pos       (12UL)                    /*!< PCR RST_EN_3: RPMPWM0_RST_EN (Bit 12)                       */
#define PCR_RST_EN_3_RPMPWM0_RST_EN_Msk       (0x1000UL)                /*!< PCR RST_EN_3: RPMPWM0_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_RST_EN_3_SMB1_RST_EN_Pos          (13UL)                    /*!< PCR RST_EN_3: SMB1_RST_EN (Bit 13)                          */
#define PCR_RST_EN_3_SMB1_RST_EN_Msk          (0x2000UL)                /*!< PCR RST_EN_3: SMB1_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_SMB2_RST_EN_Pos          (14UL)                    /*!< PCR RST_EN_3: SMB2_RST_EN (Bit 14)                          */
#define PCR_RST_EN_3_SMB2_RST_EN_Msk          (0x4000UL)                /*!< PCR RST_EN_3: SMB2_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_SMB3_RST_EN_Pos          (15UL)                    /*!< PCR RST_EN_3: SMB3_RST_EN (Bit 15)                          */
#define PCR_RST_EN_3_SMB3_RST_EN_Msk          (0x8000UL)                /*!< PCR RST_EN_3: SMB3_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_LED0_RST_EN_Pos          (16UL)                    /*!< PCR RST_EN_3: LED0_RST_EN (Bit 16)                          */
#define PCR_RST_EN_3_LED0_RST_EN_Msk          (0x10000UL)               /*!< PCR RST_EN_3: LED0_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_LED1_RST_EN_Pos          (17UL)                    /*!< PCR RST_EN_3: LED1_RST_EN (Bit 17)                          */
#define PCR_RST_EN_3_LED1_RST_EN_Msk          (0x20000UL)               /*!< PCR RST_EN_3: LED1_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_LED2_RST_EN_Pos          (18UL)                    /*!< PCR RST_EN_3: LED2_RST_EN (Bit 18)                          */
#define PCR_RST_EN_3_LED2_RST_EN_Msk          (0x40000UL)               /*!< PCR RST_EN_3: LED2_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_BCM0_RST_EN_Pos          (19UL)                    /*!< PCR RST_EN_3: BCM0_RST_EN (Bit 19)                          */
#define PCR_RST_EN_3_BCM0_RST_EN_Msk          (0x80000UL)               /*!< PCR RST_EN_3: BCM0_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_GP_SPI1_RST_EN_Pos       (20UL)                    /*!< PCR RST_EN_3: GP_SPI1_RST_EN (Bit 20)                       */
#define PCR_RST_EN_3_GP_SPI1_RST_EN_Msk       (0x100000UL)              /*!< PCR RST_EN_3: GP_SPI1_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_RST_EN_3_TIMER16_2_RST_EN_Pos     (21UL)                    /*!< PCR RST_EN_3: TIMER16_2_RST_EN (Bit 21)                     */
#define PCR_RST_EN_3_TIMER16_2_RST_EN_Msk     (0x200000UL)              /*!< PCR RST_EN_3: TIMER16_2_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_3_TIMER16_3_RST_EN_Pos     (22UL)                    /*!< PCR RST_EN_3: TIMER16_3_RST_EN (Bit 22)                     */
#define PCR_RST_EN_3_TIMER16_3_RST_EN_Msk     (0x400000UL)              /*!< PCR RST_EN_3: TIMER16_3_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_3_TIMER32_0_RST_EN_Pos     (23UL)                    /*!< PCR RST_EN_3: TIMER32_0_RST_EN (Bit 23)                     */
#define PCR_RST_EN_3_TIMER32_0_RST_EN_Msk     (0x800000UL)              /*!< PCR RST_EN_3: TIMER32_0_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_3_TIMER32_1_RST_EN_Pos     (24UL)                    /*!< PCR RST_EN_3: TIMER32_1_RST_EN (Bit 24)                     */
#define PCR_RST_EN_3_TIMER32_1_RST_EN_Msk     (0x1000000UL)             /*!< PCR RST_EN_3: TIMER32_1_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_3_LED3_RST_EN_Pos          (25UL)                    /*!< PCR RST_EN_3: LED3_RST_EN (Bit 25)                          */
#define PCR_RST_EN_3_LED3_RST_EN_Msk          (0x2000000UL)             /*!< PCR RST_EN_3: LED3_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_3_PKE_RST_EN_Pos           (26UL)                    /*!< PCR RST_EN_3: PKE_RST_EN (Bit 26)                           */
#define PCR_RST_EN_3_PKE_RST_EN_Msk           (0x4000000UL)             /*!< PCR RST_EN_3: PKE_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_3_RNG_RST_EN_Pos           (27UL)                    /*!< PCR RST_EN_3: RNG_RST_EN (Bit 27)                           */
#define PCR_RST_EN_3_RNG_RST_EN_Msk           (0x8000000UL)             /*!< PCR RST_EN_3: RNG_RST_EN (Bitfield-Mask: 0x01)              */
#define PCR_RST_EN_3_AES_HASH_RST_EN_Pos      (28UL)                    /*!< PCR RST_EN_3: AES_HASH_RST_EN (Bit 28)                      */
#define PCR_RST_EN_3_AES_HASH_RST_EN_Msk      (0x10000000UL)            /*!< PCR RST_EN_3: AES_HASH_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_RST_EN_3_HTIMER_1_RST_EN_Pos      (29UL)                    /*!< PCR RST_EN_3: HTIMER_1_RST_EN (Bit 29)                      */
#define PCR_RST_EN_3_HTIMER_1_RST_EN_Msk      (0x20000000UL)            /*!< PCR RST_EN_3: HTIMER_1_RST_EN (Bitfield-Mask: 0x01)         */
#define PCR_RST_EN_3_CCTIMER_RST_EN_Pos       (30UL)                    /*!< PCR RST_EN_3: CCTIMER_RST_EN (Bit 30)                       */
#define PCR_RST_EN_3_CCTIMER_RST_EN_Msk       (0x40000000UL)            /*!< PCR RST_EN_3: CCTIMER_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_RST_EN_3_PWM9_RST_EN_Pos          (31UL)                    /*!< PCR RST_EN_3: PWM9_RST_EN (Bit 31)                          */
#define PCR_RST_EN_3_PWM9_RST_EN_Msk          (0x80000000UL)            /*!< PCR RST_EN_3: PWM9_RST_EN (Bitfield-Mask: 0x01)             */

/* --------------------------------  PCR_RST_EN_4  -------------------------------- */
#define PCR_RST_EN_4_PWM10_RST_EN_Pos         (0UL)                     /*!< PCR RST_EN_4: PWM10_RST_EN (Bit 0)                          */
#define PCR_RST_EN_4_PWM10_RST_EN_Msk         (0x1UL)                   /*!< PCR RST_EN_4: PWM10_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_4_PWM11_RST_EN_Pos         (1UL)                     /*!< PCR RST_EN_4: PWM11_RST_EN (Bit 1)                          */
#define PCR_RST_EN_4_PWM11_RST_EN_Msk         (0x2UL)                   /*!< PCR RST_EN_4: PWM11_RST_EN (Bitfield-Mask: 0x01)            */
#define PCR_RST_EN_4_CNT_TMER0_RST_EN_Pos     (2UL)                     /*!< PCR RST_EN_4: CNT_TMER0_RST_EN (Bit 2)                      */
#define PCR_RST_EN_4_CNT_TMER0_RST_EN_Msk     (0x4UL)                   /*!< PCR RST_EN_4: CNT_TMER0_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_4_CNT_TMER1_RST_EN_Pos     (3UL)                     /*!< PCR RST_EN_4: CNT_TMER1_RST_EN (Bit 3)                      */
#define PCR_RST_EN_4_CNT_TMER1_RST_EN_Msk     (0x8UL)                   /*!< PCR RST_EN_4: CNT_TMER1_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_4_CNT_TMER2_RST_EN_Pos     (4UL)                     /*!< PCR RST_EN_4: CNT_TMER2_RST_EN (Bit 4)                      */
#define PCR_RST_EN_4_CNT_TMER2_RST_EN_Msk     (0x10UL)                  /*!< PCR RST_EN_4: CNT_TMER2_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_4_CNT_TMER3_RST_EN_Pos     (5UL)                     /*!< PCR RST_EN_4: CNT_TMER3_RST_EN (Bit 5)                      */
#define PCR_RST_EN_4_CNT_TMER3_RST_EN_Msk     (0x20UL)                  /*!< PCR RST_EN_4: CNT_TMER3_RST_EN (Bitfield-Mask: 0x01)        */
#define PCR_RST_EN_4_RTOS_RST_EN_Pos          (6UL)                     /*!< PCR RST_EN_4: RTOS_RST_EN (Bit 6)                           */
#define PCR_RST_EN_4_RTOS_RST_EN_Msk          (0x40UL)                  /*!< PCR RST_EN_4: RTOS_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_4_RPMPWM1_RST_EN_Pos       (7UL)                     /*!< PCR RST_EN_4: RPMPWM1_RST_EN (Bit 7)                        */
#define PCR_RST_EN_4_RPMPWM1_RST_EN_Msk       (0x80UL)                  /*!< PCR RST_EN_4: RPMPWM1_RST_EN (Bitfield-Mask: 0x01)          */
#define PCR_RST_EN_4_QSPI_RST_EN_Pos          (8UL)                     /*!< PCR RST_EN_4: QSPI_RST_EN (Bit 8)                           */
#define PCR_RST_EN_4_QSPI_RST_EN_Msk          (0x100UL)                 /*!< PCR RST_EN_4: QSPI_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_4_BCM1_RST_EN_Pos          (9UL)                     /*!< PCR RST_EN_4: BCM1_RST_EN (Bit 9)                           */
#define PCR_RST_EN_4_BCM1_RST_EN_Msk          (0x200UL)                 /*!< PCR RST_EN_4: BCM1_RST_EN (Bitfield-Mask: 0x01)             */
#define PCR_RST_EN_4_RC_ID0_RST_EN_Pos        (10UL)                    /*!< PCR RST_EN_4: RC_ID0_RST_EN (Bit 10)                        */
#define PCR_RST_EN_4_RC_ID0_RST_EN_Msk        (0x400UL)                 /*!< PCR RST_EN_4: RC_ID0_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_RST_EN_4_RC_ID1_RST_EN_Pos        (11UL)                    /*!< PCR RST_EN_4: RC_ID1_RST_EN (Bit 11)                        */
#define PCR_RST_EN_4_RC_ID1_RST_EN_Msk        (0x800UL)                 /*!< PCR RST_EN_4: RC_ID1_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_RST_EN_4_RC_ID2_RST_EN_Pos        (12UL)                    /*!< PCR RST_EN_4: RC_ID2_RST_EN (Bit 12)                        */
#define PCR_RST_EN_4_RC_ID2_RST_EN_Msk        (0x1000UL)                /*!< PCR RST_EN_4: RC_ID2_RST_EN (Bitfield-Mask: 0x01)           */
#define PCR_RST_EN_4_FCL_RST_EN_Pos           (15UL)                    /*!< PCR RST_EN_4: FCL_RST_EN (Bit 15)                           */
#define PCR_RST_EN_4_FCL_RST_EN_Msk           (0x8000UL)                /*!< PCR RST_EN_4: FCL_RST_EN (Bitfield-Mask: 0x01)              */


/* ================================================================================ */
/* ================          struct 'INTS' Position & Mask         ================ */
/* ================================================================================ */


/* ----------------------------  INTS_BLOCK_ENABLE_SET  --------------------------- */
#define INTS_BLOCK_ENABLE_SET_IRQ_VECTOR_ENABLE_SET_Pos (0UL)           /*!< INTS BLOCK_ENABLE_SET: IRQ_VECTOR_ENABLE_SET (Bit 0)        */
#define INTS_BLOCK_ENABLE_SET_IRQ_VECTOR_ENABLE_SET_Msk (0x7fffffffUL)  /*!< INTS BLOCK_ENABLE_SET: IRQ_VECTOR_ENABLE_SET (Bitfield-Mask: 0x7fffffff) */

/* ---------------------------  INTS_BLOCK_ENABLE_CLEAR  -------------------------- */
#define INTS_BLOCK_ENABLE_CLEAR_IRQ_VECTOR_ENABLE_CLEAR_Pos (0UL)       /*!< INTS BLOCK_ENABLE_CLEAR: IRQ_VECTOR_ENABLE_CLEAR (Bit 0)    */
#define INTS_BLOCK_ENABLE_CLEAR_IRQ_VECTOR_ENABLE_CLEAR_Msk (0x7fffffffUL) /*!< INTS BLOCK_ENABLE_CLEAR: IRQ_VECTOR_ENABLE_CLEAR (Bitfield-Mask: 0x7fffffff) */

/* ----------------------------  INTS_BLOCK_IRQ_VECTOR  --------------------------- */
#define INTS_BLOCK_IRQ_VECTOR_IRQ_VECTOR_Pos  (0UL)                     /*!< INTS BLOCK_IRQ_VECTOR: IRQ_VECTOR (Bit 0)                   */
#define INTS_BLOCK_IRQ_VECTOR_IRQ_VECTOR_Msk  (0x1ffffffUL)             /*!< INTS BLOCK_IRQ_VECTOR: IRQ_VECTOR (Bitfield-Mask: 0x1ffffff) */


/* ================================================================================ */
/* ================          struct 'WDT' Position & Mask          ================ */
/* ================================================================================ */


/* -------------------------------  WDT_WDT_CONTROL  ------------------------------ */
#define WDT_WDT_CONTROL_WDT_ENABLE_Pos        (0UL)                     /*!< WDT WDT_CONTROL: WDT_ENABLE (Bit 0)                         */
#define WDT_WDT_CONTROL_WDT_ENABLE_Msk        (0x1UL)                   /*!< WDT WDT_CONTROL: WDT_ENABLE (Bitfield-Mask: 0x01)           */
#define WDT_WDT_CONTROL_WDT_STATUS_Pos        (1UL)                     /*!< WDT WDT_CONTROL: WDT_STATUS (Bit 1)                         */
#define WDT_WDT_CONTROL_WDT_STATUS_Msk        (0x2UL)                   /*!< WDT WDT_CONTROL: WDT_STATUS (Bitfield-Mask: 0x01)           */
#define WDT_WDT_CONTROL_HIBERNATION_TIMER0_STALL_Pos (2UL)              /*!< WDT WDT_CONTROL: HIBERNATION_TIMER0_STALL (Bit 2)           */
#define WDT_WDT_CONTROL_HIBERNATION_TIMER0_STALL_Msk (0x4UL)            /*!< WDT WDT_CONTROL: HIBERNATION_TIMER0_STALL (Bitfield-Mask: 0x01) */
#define WDT_WDT_CONTROL_WEEK_TIMER_STALL_Pos  (3UL)                     /*!< WDT WDT_CONTROL: WEEK_TIMER_STALL (Bit 3)                   */
#define WDT_WDT_CONTROL_WEEK_TIMER_STALL_Msk  (0x8UL)                   /*!< WDT WDT_CONTROL: WEEK_TIMER_STALL (Bitfield-Mask: 0x01)     */
#define WDT_WDT_CONTROL_JTAG_STALL_Pos        (4UL)                     /*!< WDT WDT_CONTROL: JTAG_STALL (Bit 4)                         */
#define WDT_WDT_CONTROL_JTAG_STALL_Msk        (0x10UL)                  /*!< WDT WDT_CONTROL: JTAG_STALL (Bitfield-Mask: 0x01)           */


/* ================================================================================ */
/* ================         struct 'TIMER0' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  TIMER0_STATUS  ------------------------------- */
#define TIMER0_STATUS_EVENT_INTERRUPT_Pos     (0UL)                     /*!< TIMER0 STATUS: EVENT_INTERRUPT (Bit 0)                      */
#define TIMER0_STATUS_EVENT_INTERRUPT_Msk     (0x1UL)                   /*!< TIMER0 STATUS: EVENT_INTERRUPT (Bitfield-Mask: 0x01)        */

/* --------------------------------  TIMER0_INT_EN  ------------------------------- */
#define TIMER0_INT_EN_ENABLE_Pos              (0UL)                     /*!< TIMER0 INT_EN: ENABLE (Bit 0)                               */
#define TIMER0_INT_EN_ENABLE_Msk              (0x1UL)                   /*!< TIMER0 INT_EN: ENABLE (Bitfield-Mask: 0x01)                 */

/* -------------------------------  TIMER0_CONTROL  ------------------------------- */
#define TIMER0_CONTROL_ENABLE_Pos             (0UL)                     /*!< TIMER0 CONTROL: ENABLE (Bit 0)                              */
#define TIMER0_CONTROL_ENABLE_Msk             (0x1UL)                   /*!< TIMER0 CONTROL: ENABLE (Bitfield-Mask: 0x01)                */
#define TIMER0_CONTROL_COUNT_UP_Pos           (2UL)                     /*!< TIMER0 CONTROL: COUNT_UP (Bit 2)                            */
#define TIMER0_CONTROL_COUNT_UP_Msk           (0x4UL)                   /*!< TIMER0 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)              */
#define TIMER0_CONTROL_AUTO_RESTART_Pos       (3UL)                     /*!< TIMER0 CONTROL: AUTO_RESTART (Bit 3)                        */
#define TIMER0_CONTROL_AUTO_RESTART_Msk       (0x8UL)                   /*!< TIMER0 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)          */
#define TIMER0_CONTROL_SOFT_RESET_Pos         (4UL)                     /*!< TIMER0 CONTROL: SOFT_RESET (Bit 4)                          */
#define TIMER0_CONTROL_SOFT_RESET_Msk         (0x10UL)                  /*!< TIMER0 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)            */
#define TIMER0_CONTROL_START_Pos              (5UL)                     /*!< TIMER0 CONTROL: START (Bit 5)                               */
#define TIMER0_CONTROL_START_Msk              (0x20UL)                  /*!< TIMER0 CONTROL: START (Bitfield-Mask: 0x01)                 */
#define TIMER0_CONTROL_RELOAD_Pos             (6UL)                     /*!< TIMER0 CONTROL: RELOAD (Bit 6)                              */
#define TIMER0_CONTROL_RELOAD_Msk             (0x40UL)                  /*!< TIMER0 CONTROL: RELOAD (Bitfield-Mask: 0x01)                */
#define TIMER0_CONTROL_HALT_Pos               (7UL)                     /*!< TIMER0 CONTROL: HALT (Bit 7)                                */
#define TIMER0_CONTROL_HALT_Msk               (0x80UL)                  /*!< TIMER0 CONTROL: HALT (Bitfield-Mask: 0x01)                  */
#define TIMER0_CONTROL_PRE_SCALE_Pos          (16UL)                    /*!< TIMER0 CONTROL: PRE_SCALE (Bit 16)                          */
#define TIMER0_CONTROL_PRE_SCALE_Msk          (0xffff0000UL)            /*!< TIMER0 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)           */


/* ================================================================================ */
/* ================         struct 'TIMER1' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  TIMER1_STATUS  ------------------------------- */
#define TIMER1_STATUS_EVENT_INTERRUPT_Pos     (0UL)                     /*!< TIMER1 STATUS: EVENT_INTERRUPT (Bit 0)                      */
#define TIMER1_STATUS_EVENT_INTERRUPT_Msk     (0x1UL)                   /*!< TIMER1 STATUS: EVENT_INTERRUPT (Bitfield-Mask: 0x01)        */

/* --------------------------------  TIMER1_INT_EN  ------------------------------- */
#define TIMER1_INT_EN_ENABLE_Pos              (0UL)                     /*!< TIMER1 INT_EN: ENABLE (Bit 0)                               */
#define TIMER1_INT_EN_ENABLE_Msk              (0x1UL)                   /*!< TIMER1 INT_EN: ENABLE (Bitfield-Mask: 0x01)                 */

/* -------------------------------  TIMER1_CONTROL  ------------------------------- */
#define TIMER1_CONTROL_ENABLE_Pos             (0UL)                     /*!< TIMER1 CONTROL: ENABLE (Bit 0)                              */
#define TIMER1_CONTROL_ENABLE_Msk             (0x1UL)                   /*!< TIMER1 CONTROL: ENABLE (Bitfield-Mask: 0x01)                */
#define TIMER1_CONTROL_COUNT_UP_Pos           (2UL)                     /*!< TIMER1 CONTROL: COUNT_UP (Bit 2)                            */
#define TIMER1_CONTROL_COUNT_UP_Msk           (0x4UL)                   /*!< TIMER1 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)              */
#define TIMER1_CONTROL_AUTO_RESTART_Pos       (3UL)                     /*!< TIMER1 CONTROL: AUTO_RESTART (Bit 3)                        */
#define TIMER1_CONTROL_AUTO_RESTART_Msk       (0x8UL)                   /*!< TIMER1 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)          */
#define TIMER1_CONTROL_SOFT_RESET_Pos         (4UL)                     /*!< TIMER1 CONTROL: SOFT_RESET (Bit 4)                          */
#define TIMER1_CONTROL_SOFT_RESET_Msk         (0x10UL)                  /*!< TIMER1 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)            */
#define TIMER1_CONTROL_START_Pos              (5UL)                     /*!< TIMER1 CONTROL: START (Bit 5)                               */
#define TIMER1_CONTROL_START_Msk              (0x20UL)                  /*!< TIMER1 CONTROL: START (Bitfield-Mask: 0x01)                 */
#define TIMER1_CONTROL_RELOAD_Pos             (6UL)                     /*!< TIMER1 CONTROL: RELOAD (Bit 6)                              */
#define TIMER1_CONTROL_RELOAD_Msk             (0x40UL)                  /*!< TIMER1 CONTROL: RELOAD (Bitfield-Mask: 0x01)                */
#define TIMER1_CONTROL_HALT_Pos               (7UL)                     /*!< TIMER1 CONTROL: HALT (Bit 7)                                */
#define TIMER1_CONTROL_HALT_Msk               (0x80UL)                  /*!< TIMER1 CONTROL: HALT (Bitfield-Mask: 0x01)                  */
#define TIMER1_CONTROL_PRE_SCALE_Pos          (16UL)                    /*!< TIMER1 CONTROL: PRE_SCALE (Bit 16)                          */
#define TIMER1_CONTROL_PRE_SCALE_Msk          (0xffff0000UL)            /*!< TIMER1 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)           */


/* ================================================================================ */
/* ================         struct 'TIMER2' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  TIMER2_STATUS  ------------------------------- */
#define TIMER2_STATUS_EVENT_INTERRUPT_Pos     (0UL)                     /*!< TIMER2 STATUS: EVENT_INTERRUPT (Bit 0)                      */
#define TIMER2_STATUS_EVENT_INTERRUPT_Msk     (0x1UL)                   /*!< TIMER2 STATUS: EVENT_INTERRUPT (Bitfield-Mask: 0x01)        */

/* --------------------------------  TIMER2_INT_EN  ------------------------------- */
#define TIMER2_INT_EN_ENABLE_Pos              (0UL)                     /*!< TIMER2 INT_EN: ENABLE (Bit 0)                               */
#define TIMER2_INT_EN_ENABLE_Msk              (0x1UL)                   /*!< TIMER2 INT_EN: ENABLE (Bitfield-Mask: 0x01)                 */

/* -------------------------------  TIMER2_CONTROL  ------------------------------- */
#define TIMER2_CONTROL_ENABLE_Pos             (0UL)                     /*!< TIMER2 CONTROL: ENABLE (Bit 0)                              */
#define TIMER2_CONTROL_ENABLE_Msk             (0x1UL)                   /*!< TIMER2 CONTROL: ENABLE (Bitfield-Mask: 0x01)                */
#define TIMER2_CONTROL_COUNT_UP_Pos           (2UL)                     /*!< TIMER2 CONTROL: COUNT_UP (Bit 2)                            */
#define TIMER2_CONTROL_COUNT_UP_Msk           (0x4UL)                   /*!< TIMER2 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)              */
#define TIMER2_CONTROL_AUTO_RESTART_Pos       (3UL)                     /*!< TIMER2 CONTROL: AUTO_RESTART (Bit 3)                        */
#define TIMER2_CONTROL_AUTO_RESTART_Msk       (0x8UL)                   /*!< TIMER2 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)          */
#define TIMER2_CONTROL_SOFT_RESET_Pos         (4UL)                     /*!< TIMER2 CONTROL: SOFT_RESET (Bit 4)                          */
#define TIMER2_CONTROL_SOFT_RESET_Msk         (0x10UL)                  /*!< TIMER2 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)            */
#define TIMER2_CONTROL_START_Pos              (5UL)                     /*!< TIMER2 CONTROL: START (Bit 5)                               */
#define TIMER2_CONTROL_START_Msk              (0x20UL)                  /*!< TIMER2 CONTROL: START (Bitfield-Mask: 0x01)                 */
#define TIMER2_CONTROL_RELOAD_Pos             (6UL)                     /*!< TIMER2 CONTROL: RELOAD (Bit 6)                              */
#define TIMER2_CONTROL_RELOAD_Msk             (0x40UL)                  /*!< TIMER2 CONTROL: RELOAD (Bitfield-Mask: 0x01)                */
#define TIMER2_CONTROL_HALT_Pos               (7UL)                     /*!< TIMER2 CONTROL: HALT (Bit 7)                                */
#define TIMER2_CONTROL_HALT_Msk               (0x80UL)                  /*!< TIMER2 CONTROL: HALT (Bitfield-Mask: 0x01)                  */
#define TIMER2_CONTROL_PRE_SCALE_Pos          (16UL)                    /*!< TIMER2 CONTROL: PRE_SCALE (Bit 16)                          */
#define TIMER2_CONTROL_PRE_SCALE_Msk          (0xffff0000UL)            /*!< TIMER2 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)           */


/* ================================================================================ */
/* ================         struct 'TIMER3' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  TIMER3_STATUS  ------------------------------- */
#define TIMER3_STATUS_EVENT_INTERRUPT_Pos     (0UL)                     /*!< TIMER3 STATUS: EVENT_INTERRUPT (Bit 0)                      */
#define TIMER3_STATUS_EVENT_INTERRUPT_Msk     (0x1UL)                   /*!< TIMER3 STATUS: EVENT_INTERRUPT (Bitfield-Mask: 0x01)        */

/* --------------------------------  TIMER3_INT_EN  ------------------------------- */
#define TIMER3_INT_EN_ENABLE_Pos              (0UL)                     /*!< TIMER3 INT_EN: ENABLE (Bit 0)                               */
#define TIMER3_INT_EN_ENABLE_Msk              (0x1UL)                   /*!< TIMER3 INT_EN: ENABLE (Bitfield-Mask: 0x01)                 */

/* -------------------------------  TIMER3_CONTROL  ------------------------------- */
#define TIMER3_CONTROL_ENABLE_Pos             (0UL)                     /*!< TIMER3 CONTROL: ENABLE (Bit 0)                              */
#define TIMER3_CONTROL_ENABLE_Msk             (0x1UL)                   /*!< TIMER3 CONTROL: ENABLE (Bitfield-Mask: 0x01)                */
#define TIMER3_CONTROL_COUNT_UP_Pos           (2UL)                     /*!< TIMER3 CONTROL: COUNT_UP (Bit 2)                            */
#define TIMER3_CONTROL_COUNT_UP_Msk           (0x4UL)                   /*!< TIMER3 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)              */
#define TIMER3_CONTROL_AUTO_RESTART_Pos       (3UL)                     /*!< TIMER3 CONTROL: AUTO_RESTART (Bit 3)                        */
#define TIMER3_CONTROL_AUTO_RESTART_Msk       (0x8UL)                   /*!< TIMER3 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)          */
#define TIMER3_CONTROL_SOFT_RESET_Pos         (4UL)                     /*!< TIMER3 CONTROL: SOFT_RESET (Bit 4)                          */
#define TIMER3_CONTROL_SOFT_RESET_Msk         (0x10UL)                  /*!< TIMER3 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)            */
#define TIMER3_CONTROL_START_Pos              (5UL)                     /*!< TIMER3 CONTROL: START (Bit 5)                               */
#define TIMER3_CONTROL_START_Msk              (0x20UL)                  /*!< TIMER3 CONTROL: START (Bitfield-Mask: 0x01)                 */
#define TIMER3_CONTROL_RELOAD_Pos             (6UL)                     /*!< TIMER3 CONTROL: RELOAD (Bit 6)                              */
#define TIMER3_CONTROL_RELOAD_Msk             (0x40UL)                  /*!< TIMER3 CONTROL: RELOAD (Bitfield-Mask: 0x01)                */
#define TIMER3_CONTROL_HALT_Pos               (7UL)                     /*!< TIMER3 CONTROL: HALT (Bit 7)                                */
#define TIMER3_CONTROL_HALT_Msk               (0x80UL)                  /*!< TIMER3 CONTROL: HALT (Bitfield-Mask: 0x01)                  */
#define TIMER3_CONTROL_PRE_SCALE_Pos          (16UL)                    /*!< TIMER3 CONTROL: PRE_SCALE (Bit 16)                          */
#define TIMER3_CONTROL_PRE_SCALE_Msk          (0xffff0000UL)            /*!< TIMER3 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)           */


/* ================================================================================ */
/* ================         struct 'TIMER4' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  TIMER4_STATUS  ------------------------------- */
#define TIMER4_STATUS_EVENT_INTERRUPT_Pos     (0UL)                     /*!< TIMER4 STATUS: EVENT_INTERRUPT (Bit 0)                      */
#define TIMER4_STATUS_EVENT_INTERRUPT_Msk     (0x1UL)                   /*!< TIMER4 STATUS: EVENT_INTERRUPT (Bitfield-Mask: 0x01)        */

/* --------------------------------  TIMER4_INT_EN  ------------------------------- */
#define TIMER4_INT_EN_ENABLE_Pos              (0UL)                     /*!< TIMER4 INT_EN: ENABLE (Bit 0)                               */
#define TIMER4_INT_EN_ENABLE_Msk              (0x1UL)                   /*!< TIMER4 INT_EN: ENABLE (Bitfield-Mask: 0x01)                 */

/* -------------------------------  TIMER4_CONTROL  ------------------------------- */
#define TIMER4_CONTROL_ENABLE_Pos             (0UL)                     /*!< TIMER4 CONTROL: ENABLE (Bit 0)                              */
#define TIMER4_CONTROL_ENABLE_Msk             (0x1UL)                   /*!< TIMER4 CONTROL: ENABLE (Bitfield-Mask: 0x01)                */
#define TIMER4_CONTROL_COUNT_UP_Pos           (2UL)                     /*!< TIMER4 CONTROL: COUNT_UP (Bit 2)                            */
#define TIMER4_CONTROL_COUNT_UP_Msk           (0x4UL)                   /*!< TIMER4 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)              */
#define TIMER4_CONTROL_AUTO_RESTART_Pos       (3UL)                     /*!< TIMER4 CONTROL: AUTO_RESTART (Bit 3)                        */
#define TIMER4_CONTROL_AUTO_RESTART_Msk       (0x8UL)                   /*!< TIMER4 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)          */
#define TIMER4_CONTROL_SOFT_RESET_Pos         (4UL)                     /*!< TIMER4 CONTROL: SOFT_RESET (Bit 4)                          */
#define TIMER4_CONTROL_SOFT_RESET_Msk         (0x10UL)                  /*!< TIMER4 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)            */
#define TIMER4_CONTROL_START_Pos              (5UL)                     /*!< TIMER4 CONTROL: START (Bit 5)                               */
#define TIMER4_CONTROL_START_Msk              (0x20UL)                  /*!< TIMER4 CONTROL: START (Bitfield-Mask: 0x01)                 */
#define TIMER4_CONTROL_RELOAD_Pos             (6UL)                     /*!< TIMER4 CONTROL: RELOAD (Bit 6)                              */
#define TIMER4_CONTROL_RELOAD_Msk             (0x40UL)                  /*!< TIMER4 CONTROL: RELOAD (Bitfield-Mask: 0x01)                */
#define TIMER4_CONTROL_HALT_Pos               (7UL)                     /*!< TIMER4 CONTROL: HALT (Bit 7)                                */
#define TIMER4_CONTROL_HALT_Msk               (0x80UL)                  /*!< TIMER4 CONTROL: HALT (Bitfield-Mask: 0x01)                  */
#define TIMER4_CONTROL_PRE_SCALE_Pos          (16UL)                    /*!< TIMER4 CONTROL: PRE_SCALE (Bit 16)                          */
#define TIMER4_CONTROL_PRE_SCALE_Msk          (0xffff0000UL)            /*!< TIMER4 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)           */


/* ================================================================================ */
/* ================         struct 'TIMER5' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  TIMER5_STATUS  ------------------------------- */
#define TIMER5_STATUS_EVENT_INTERRUPT_Pos     (0UL)                     /*!< TIMER5 STATUS: EVENT_INTERRUPT (Bit 0)                      */
#define TIMER5_STATUS_EVENT_INTERRUPT_Msk     (0x1UL)                   /*!< TIMER5 STATUS: EVENT_INTERRUPT (Bitfield-Mask: 0x01)        */

/* --------------------------------  TIMER5_INT_EN  ------------------------------- */
#define TIMER5_INT_EN_ENABLE_Pos              (0UL)                     /*!< TIMER5 INT_EN: ENABLE (Bit 0)                               */
#define TIMER5_INT_EN_ENABLE_Msk              (0x1UL)                   /*!< TIMER5 INT_EN: ENABLE (Bitfield-Mask: 0x01)                 */

/* -------------------------------  TIMER5_CONTROL  ------------------------------- */
#define TIMER5_CONTROL_ENABLE_Pos             (0UL)                     /*!< TIMER5 CONTROL: ENABLE (Bit 0)                              */
#define TIMER5_CONTROL_ENABLE_Msk             (0x1UL)                   /*!< TIMER5 CONTROL: ENABLE (Bitfield-Mask: 0x01)                */
#define TIMER5_CONTROL_COUNT_UP_Pos           (2UL)                     /*!< TIMER5 CONTROL: COUNT_UP (Bit 2)                            */
#define TIMER5_CONTROL_COUNT_UP_Msk           (0x4UL)                   /*!< TIMER5 CONTROL: COUNT_UP (Bitfield-Mask: 0x01)              */
#define TIMER5_CONTROL_AUTO_RESTART_Pos       (3UL)                     /*!< TIMER5 CONTROL: AUTO_RESTART (Bit 3)                        */
#define TIMER5_CONTROL_AUTO_RESTART_Msk       (0x8UL)                   /*!< TIMER5 CONTROL: AUTO_RESTART (Bitfield-Mask: 0x01)          */
#define TIMER5_CONTROL_SOFT_RESET_Pos         (4UL)                     /*!< TIMER5 CONTROL: SOFT_RESET (Bit 4)                          */
#define TIMER5_CONTROL_SOFT_RESET_Msk         (0x10UL)                  /*!< TIMER5 CONTROL: SOFT_RESET (Bitfield-Mask: 0x01)            */
#define TIMER5_CONTROL_START_Pos              (5UL)                     /*!< TIMER5 CONTROL: START (Bit 5)                               */
#define TIMER5_CONTROL_START_Msk              (0x20UL)                  /*!< TIMER5 CONTROL: START (Bitfield-Mask: 0x01)                 */
#define TIMER5_CONTROL_RELOAD_Pos             (6UL)                     /*!< TIMER5 CONTROL: RELOAD (Bit 6)                              */
#define TIMER5_CONTROL_RELOAD_Msk             (0x40UL)                  /*!< TIMER5 CONTROL: RELOAD (Bitfield-Mask: 0x01)                */
#define TIMER5_CONTROL_HALT_Pos               (7UL)                     /*!< TIMER5 CONTROL: HALT (Bit 7)                                */
#define TIMER5_CONTROL_HALT_Msk               (0x80UL)                  /*!< TIMER5 CONTROL: HALT (Bitfield-Mask: 0x01)                  */
#define TIMER5_CONTROL_PRE_SCALE_Pos          (16UL)                    /*!< TIMER5 CONTROL: PRE_SCALE (Bit 16)                          */
#define TIMER5_CONTROL_PRE_SCALE_Msk          (0xffff0000UL)            /*!< TIMER5 CONTROL: PRE_SCALE (Bitfield-Mask: 0xffff)           */


/* ================================================================================ */
/* ================      struct 'EC_REG_BANK' Position & Mask      ================ */
/* ================================================================================ */


/* --------------------------  EC_REG_BANK_DEBUG_Enable  -------------------------- */
#define EC_REG_BANK_DEBUG_Enable_DEBUG_EN_Pos (0UL)                     /*!< EC_REG_BANK DEBUG_Enable: DEBUG_EN (Bit 0)                  */
#define EC_REG_BANK_DEBUG_Enable_DEBUG_EN_Msk (0x1UL)                   /*!< EC_REG_BANK DEBUG_Enable: DEBUG_EN (Bitfield-Mask: 0x01)    */
#define EC_REG_BANK_DEBUG_Enable_DEBUG_PIN_CFG_Pos (1UL)                /*!< EC_REG_BANK DEBUG_Enable: DEBUG_PIN_CFG (Bit 1)             */
#define EC_REG_BANK_DEBUG_Enable_DEBUG_PIN_CFG_Msk (0x6UL)              /*!< EC_REG_BANK DEBUG_Enable: DEBUG_PIN_CFG (Bitfield-Mask: 0x03) */
#define EC_REG_BANK_DEBUG_Enable_DEBUG_PU_EN_Pos (3UL)                  /*!< EC_REG_BANK DEBUG_Enable: DEBUG_PU_EN (Bit 3)               */
#define EC_REG_BANK_DEBUG_Enable_DEBUG_PU_EN_Msk (0x8UL)                /*!< EC_REG_BANK DEBUG_Enable: DEBUG_PU_EN (Bitfield-Mask: 0x01) */

/* -------------------  EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL  ------------------- */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_INPUT_BYTE_SWAP_ENABLE_Pos (0UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: INPUT_BYTE_SWAP_ENABLE (Bit 0) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_INPUT_BYTE_SWAP_ENABLE_Msk (0x1UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: INPUT_BYTE_SWAP_ENABLE (Bitfield-Mask: 0x01) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_OUTPUT_BYTE_SWAP_ENABLE_Pos (1UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: OUTPUT_BYTE_SWAP_ENABLE (Bit 1) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_OUTPUT_BYTE_SWAP_ENABLE_Msk (0x2UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: OUTPUT_BYTE_SWAP_ENABLE (Bitfield-Mask: 0x01) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_INPUT_BLOCK_SWAP_ENABLE_Pos (2UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: INPUT_BLOCK_SWAP_ENABLE (Bit 2) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_INPUT_BLOCK_SWAP_ENABLE_Msk (0x1cUL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: INPUT_BLOCK_SWAP_ENABLE (Bitfield-Mask: 0x07) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_OUTPUT_BLOCK_SWAP_ENABLE_Pos (5UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: OUTPUT_BLOCK_SWAP_ENABLE (Bit 5) */
#define EC_REG_BANK_AES_HASH_BYTE_SWAP_CONTROL_OUTPUT_BLOCK_SWAP_ENABLE_Msk (0xe0UL) /*!< EC_REG_BANK AES_HASH_BYTE_SWAP_CONTROL: OUTPUT_BLOCK_SWAP_ENABLE (Bitfield-Mask: 0x07) */

/* ----------------------  EC_REG_BANK_SYSTEM_SHUTDOWN_RESET  --------------------- */
#define EC_REG_BANK_SYSTEM_SHUTDOWN_RESET_SYS_SHDN_RST_Pos (0UL)        /*!< EC_REG_BANK SYSTEM_SHUTDOWN_RESET: SYS_SHDN_RST (Bit 0)     */
#define EC_REG_BANK_SYSTEM_SHUTDOWN_RESET_SYS_SHDN_RST_Msk (0x1UL)      /*!< EC_REG_BANK SYSTEM_SHUTDOWN_RESET: SYS_SHDN_RST (Bitfield-Mask: 0x01) */

/* ----------------------------  EC_REG_BANK_MISC_TRIM  --------------------------- */
#define EC_REG_BANK_MISC_TRIM_PECI_DISABLE_Pos (0UL)                    /*!< EC_REG_BANK MISC_TRIM: PECI_DISABLE (Bit 0)                 */
#define EC_REG_BANK_MISC_TRIM_PECI_DISABLE_Msk (0x1UL)                  /*!< EC_REG_BANK MISC_TRIM: PECI_DISABLE (Bitfield-Mask: 0x01)   */

/* ------------------------  EC_REG_BANK_CRYPTO_SOFT_RESET  ----------------------- */
#define EC_REG_BANK_CRYPTO_SOFT_RESET_RNG_SOFT_RESET_Pos (0UL)          /*!< EC_REG_BANK CRYPTO_SOFT_RESET: RNG_SOFT_RESET (Bit 0)       */
#define EC_REG_BANK_CRYPTO_SOFT_RESET_RNG_SOFT_RESET_Msk (0x1UL)        /*!< EC_REG_BANK CRYPTO_SOFT_RESET: RNG_SOFT_RESET (Bitfield-Mask: 0x01) */
#define EC_REG_BANK_CRYPTO_SOFT_RESET_PUBLIC_KEY_SOFT_RESET_Pos (1UL)   /*!< EC_REG_BANK CRYPTO_SOFT_RESET: PUBLIC_KEY_SOFT_RESET (Bit 1) */
#define EC_REG_BANK_CRYPTO_SOFT_RESET_PUBLIC_KEY_SOFT_RESET_Msk (0x2UL) /*!< EC_REG_BANK CRYPTO_SOFT_RESET: PUBLIC_KEY_SOFT_RESET (Bitfield-Mask: 0x01) */
#define EC_REG_BANK_CRYPTO_SOFT_RESET_AES_HASH_SOFT_RESET_Pos (2UL)     /*!< EC_REG_BANK CRYPTO_SOFT_RESET: AES_HASH_SOFT_RESET (Bit 2)  */
#define EC_REG_BANK_CRYPTO_SOFT_RESET_AES_HASH_SOFT_RESET_Msk (0x4UL)   /*!< EC_REG_BANK CRYPTO_SOFT_RESET: AES_HASH_SOFT_RESET (Bitfield-Mask: 0x01) */

/* -------------------------  EC_REG_BANK_GPIO_BANK_POWER  ------------------------ */
#define EC_REG_BANK_GPIO_BANK_POWER_VTR_LEVEL1_Pos (0UL)                /*!< EC_REG_BANK GPIO_BANK_POWER: VTR_LEVEL1 (Bit 0)             */
#define EC_REG_BANK_GPIO_BANK_POWER_VTR_LEVEL1_Msk (0x1UL)              /*!< EC_REG_BANK GPIO_BANK_POWER: VTR_LEVEL1 (Bitfield-Mask: 0x01) */
#define EC_REG_BANK_GPIO_BANK_POWER_VTR_LEVEL2_Pos (1UL)                /*!< EC_REG_BANK GPIO_BANK_POWER: VTR_LEVEL2 (Bit 1)             */
#define EC_REG_BANK_GPIO_BANK_POWER_VTR_LEVEL2_Msk (0x2UL)              /*!< EC_REG_BANK GPIO_BANK_POWER: VTR_LEVEL2 (Bitfield-Mask: 0x01) */
#define EC_REG_BANK_GPIO_BANK_POWER_VTR_LEVEL3_Pos (2UL)                /*!< EC_REG_BANK GPIO_BANK_POWER: VTR_LEVEL3 (Bit 2)             */
#define EC_REG_BANK_GPIO_BANK_POWER_VTR_LEVEL3_Msk (0x4UL)              /*!< EC_REG_BANK GPIO_BANK_POWER: VTR_LEVEL3 (Bitfield-Mask: 0x01) */

/* -------------------------  EC_REG_BANK_JTAG_MASTER_CFG  ------------------------ */
#define EC_REG_BANK_JTAG_MASTER_CFG_JTM_CLK_Pos (0UL)                   /*!< EC_REG_BANK JTAG_MASTER_CFG: JTM_CLK (Bit 0)                */
#define EC_REG_BANK_JTAG_MASTER_CFG_JTM_CLK_Msk (0x7UL)                 /*!< EC_REG_BANK JTAG_MASTER_CFG: JTM_CLK (Bitfield-Mask: 0x07)  */
#define EC_REG_BANK_JTAG_MASTER_CFG_MASTER_SLAVE_Pos (3UL)              /*!< EC_REG_BANK JTAG_MASTER_CFG: MASTER_SLAVE (Bit 3)           */
#define EC_REG_BANK_JTAG_MASTER_CFG_MASTER_SLAVE_Msk (0x8UL)            /*!< EC_REG_BANK JTAG_MASTER_CFG: MASTER_SLAVE (Bitfield-Mask: 0x01) */

/* -------------------------  EC_REG_BANK_JTAG_MASTER_STS  ------------------------ */
#define EC_REG_BANK_JTAG_MASTER_STS_JTM_DONE_Pos (0UL)                  /*!< EC_REG_BANK JTAG_MASTER_STS: JTM_DONE (Bit 0)               */
#define EC_REG_BANK_JTAG_MASTER_STS_JTM_DONE_Msk (0x1UL)                /*!< EC_REG_BANK JTAG_MASTER_STS: JTM_DONE (Bitfield-Mask: 0x01) */

/* -------------------------  EC_REG_BANK_JTAG_MASTER_TDO  ------------------------ */
#define EC_REG_BANK_JTAG_MASTER_TDO_JTM_TDO_Pos (0UL)                   /*!< EC_REG_BANK JTAG_MASTER_TDO: JTM_TDO (Bit 0)                */
#define EC_REG_BANK_JTAG_MASTER_TDO_JTM_TDO_Msk (0xffffffffUL)          /*!< EC_REG_BANK JTAG_MASTER_TDO: JTM_TDO (Bitfield-Mask: 0xffffffff) */

/* -------------------------  EC_REG_BANK_JTAG_MASTER_TDI  ------------------------ */
#define EC_REG_BANK_JTAG_MASTER_TDI_JTM_TDI_Pos (0UL)                   /*!< EC_REG_BANK JTAG_MASTER_TDI: JTM_TDI (Bit 0)                */
#define EC_REG_BANK_JTAG_MASTER_TDI_JTM_TDI_Msk (0xffffffffUL)          /*!< EC_REG_BANK JTAG_MASTER_TDI: JTM_TDI (Bitfield-Mask: 0xffffffff) */

/* -------------------------  EC_REG_BANK_JTAG_MASTER_TMS  ------------------------ */
#define EC_REG_BANK_JTAG_MASTER_TMS_JTM_TMS_Pos (0UL)                   /*!< EC_REG_BANK JTAG_MASTER_TMS: JTM_TMS (Bit 0)                */
#define EC_REG_BANK_JTAG_MASTER_TMS_JTM_TMS_Msk (0xffffffffUL)          /*!< EC_REG_BANK JTAG_MASTER_TMS: JTM_TMS (Bitfield-Mask: 0xffffffff) */

/* -------------------------  EC_REG_BANK_JTAG_MASTER_CMD  ------------------------ */
#define EC_REG_BANK_JTAG_MASTER_CMD_JTM_COUNT_Pos (0UL)                 /*!< EC_REG_BANK JTAG_MASTER_CMD: JTM_COUNT (Bit 0)              */
#define EC_REG_BANK_JTAG_MASTER_CMD_JTM_COUNT_Msk (0x1fUL)              /*!< EC_REG_BANK JTAG_MASTER_CMD: JTM_COUNT (Bitfield-Mask: 0x1f) */


/* ================================================================================ */
/* ================              Peripheral memory map             ================ */
/* ================================================================================ */

#define PCR_BASE                        0x40080100UL
#define INTS_BASE                       0x4000E000UL
#define TIMER0_BASE                     0x40000C00UL
#define TIMER1_BASE                     0x40000C20UL
#define TIMER2_BASE                     0x40000C40UL
#define TIMER3_BASE                     0x40000C60UL
#define TIMER4_BASE                     0x40000C80UL
#define TIMER5_BASE                     0x40000CA0UL
#define EC_REG_BANK_BASE                0x4000FC00UL


/* ================================================================================ */
/* ================             Peripheral declaration             ================ */
/* ================================================================================ */

#define MEC2016_PCR                             ((PCR_Type                *) PCR_BASE)
#define MEC2016_INTS                            ((INTS_Type               *) INTS_BASE)
#define MEC2016_TIMER0                          ((TIMER0_Type             *) TIMER0_BASE)
#define MEC2016_TIMER1                          ((TIMER0_Type             *) TIMER1_BASE)
#define MEC2016_TIMER2                          ((TIMER0_Type             *) TIMER2_BASE)
#define MEC2016_TIMER3                          ((TIMER0_Type             *) TIMER3_BASE)
#define MEC2016_TIMER4                          ((TIMER0_Type             *) TIMER4_BASE)
#define MEC2016_TIMER5                          ((TIMER0_Type             *) TIMER5_BASE)
#define MEC2016_EC_REG_BANK                     ((EC_REG_BANK_Type        *) EC_REG_BANK_BASE)

/** @} */ /* End of group Device_Peripheral_Registers */
/** @} */ /* End of group MCHP_device_internal */
/** @} */ /* End of group Microchip Technology Inc. */

#ifdef __cplusplus
}
#endif


#endif  /* MCHP_device_internal_H */

