 
/****************************************************************************************************//**
 * @file     LPC43xx.h
 *
 * @status   EXPERIMENTAL
 *
 * @brief    CMSIS Cortex-M4 Core Peripheral Access Layer Header File for
 *           default LPC43xx Device Series
 *
 * @version  V0.10
 * @date     10. June 2011
 *
 * @note     Generated with SFDGen V2.6 Build 4f  on Friday, 10.06.2011 14:32:01
 *
 *
 *******************************************************************************************************/



/** @addtogroup (null)
  * @{
  */

/** @addtogroup LPC43xx
  * @{
  */

#ifndef __LPC43XX_H__
#define __LPC43XX_H__

#ifdef __cplusplus
extern "C" {
#endif 


#if defined ( __CC_ARM   )
  #pragma anon_unions
#endif

 /* Interrupt Number Definition */

#if defined CORE_M4

typedef enum {
// -------------------------  Cortex-M4 Processor Exceptions Numbers  -----------------------------
  Reset_IRQn                        = -15,  /*!<   1  Reset Vector, invoked on Power up and warm reset */
  NonMaskableInt_IRQn               = -14,  /*!<   2  Non maskable Interrupt, cannot be stopped or preempted */
  HardFault_IRQn                    = -13,  /*!<   3  Hard Fault, all classes of Fault */
  MemoryManagement_IRQn             = -12,  /*!<   4  Memory Management, MPU mismatch, including Access Violation and No Match */
  BusFault_IRQn                     = -11,  /*!<   5  Bus Fault, Pre-Fetch-, Memory Access Fault, other address/memory related Fault */
  UsageFault_IRQn                   = -10,  /*!<   6  Usage Fault, i.e. Undef Instruction, Illegal State Transition */
  SVCall_IRQn                       = -5,   /*!<  11  System Service Call via SVC instruction */
  DebugMonitor_IRQn                 = -4,   /*!<  12  Debug Monitor                    */
  PendSV_IRQn                       = -2,   /*!<  14  Pendable request for system service */
  SysTick_IRQn                      = -1,   /*!<  15  System Tick Timer                */
// ---------------------------  LPC43xx Specific Interrupt Numbers  -------------------------------
  DAC_IRQn                          = 0,    /*!<   0  DAC                              */
  M0_IRQn                           = 1,    /*!<   1  M0                               */
  DMA_IRQn                          = 2,    /*!<   2  DMA                              */
  RESERVED0_IRQn                    = 3,    
  RESERVED1_IRQn                    = 4,
  ETH_IRQn                          = 5,    /*!<   5  ETHERNET                         */
  SDIO_IRQn                         = 6,    /*!<   6  SDIO                             */
  LCD_IRQn                          = 7,    /*!<   7  LCD                              */
  USB0_IRQn                         = 8,    /*!<   8  USB0                             */
  USB1_IRQn                         = 9,    /*!<   9  USB1                             */
  SCT_IRQn                          = 10,   /*!<  10  SCT                              */
  RITIMER_IRQn                      = 11,   /*!<  11  RITIMER                          */
  TIMER0_IRQn                       = 12,   /*!<  12  TIMER0                           */
  TIMER1_IRQn                       = 13,   /*!<  13  TIMER1_INT                       */
  TIMER2_IRQn                       = 14,   /*!<  14  TIMER2_INT                       */
  TIMER3_IRQn                       = 15,   /*!<  15  TIMER3_INT                       */
  MCPWM_IRQn                        = 16,   /*!<  16  MCPWM                            */
  ADC0_IRQn                         = 17,   /*!<  17  ADC0                             */
  I2C0_IRQn                         = 18,   /*!<  18  I2C0                             */
  I2C1_IRQn                         = 19,   /*!<  19  I2C1                             */
  SPI_IRQn                          = 20,   /*!<  20  SPI                              */
  ADC1_IRQn                         = 21,   /*!<  21  ADC1                             */
  SSP0_IRQn                         = 22,   /*!<  22  SSP0                             */
  SSP1_IRQn                         = 23,   /*!<  23  SSP1                             */
  USART0_IRQn                       = 24,   /*!<  24  USART0                           */
  UART1_IRQn                        = 25,   /*!<  25  UART1                            */
  USART2_IRQn                       = 26,   /*!<  26  USART2                           */
  USART3_IRQn                       = 27,   /*!<  27  USART3                           */
  I2S0_IRQn                         = 28,   /*!<  28  I2S0                             */
  I2S1_IRQn                         = 29,   /*!<  29  I2S1                             */
  SPIFI_IRQn                        = 30,   /*!<  30  SPIFI                            */
  SGPIO_IRQn                        = 31,   /*!<  31  SGPIO                            */
  PIN_INT0_IRQn                     = 32,   /*!<  32  PIN_INT0                         */
  PIN_INT1_IRQn                     = 33,   /*!<  33  PIN_INT1                         */
  PIN_INT2_IRQn                     = 34,   /*!<  34  PIN_INT2                         */
  PIN_INT3_IRQn                     = 35,   /*!<  35  PIN_INT3                         */
  PIN_INT4_IRQn                     = 36,   /*!<  36  PIN_INT4                         */
  PIN_INT5_IRQn                     = 37,   /*!<  37  PIN_INT5                         */
  PIN_INT6_IRQn                     = 38,   /*!<  38  PIN_INT6                         */
  PIN_INT7_IRQn                     = 39,   /*!<  39  PIN_INT7                         */
  GINT0_IRQn                        = 40,   /*!<  40  GINT0                            */
  GINT1_IRQn                        = 41,   /*!<  41  GINT1                            */
  EVENTROUTER_INT_IRQn              = 42,   /*!<  42  EVENTROUTER_INT                  */
  C_CAN1_IRQn                       = 43,   /*!<  43  C_CAN1                           */
  RESERVED3_IRQn                    = 44,
  VADC_IRQn                         = 45,   /*!<  45  VADC                             */
  ATIMER_IRQn                       = 46,   /*!<  46  ATIMER                           */
  RTC_IRQn                          = 47,   /*!<  47  RTC                              */
  RESERVED4_IRQn                    = 48,
  WWDT_IRQn                         = 49,   /*!<  49  WDT                              */
  RESERVED5_IRQn                    = 50,   
  C_CAN0_IRQn                       = 51,   /*!<  51  C_CAN0                           */
  QEI_IRQn                          = 52,   /*!<  52  QEI                              */
} IRQn_Type;

#endif

#if defined CORE_M0
#include "LPC43xx_M0.h"
#endif

 /* Event Router Input (ERI) Number Definitions */
typedef enum {
  WAKEUP0_ERIn                      = 0,
  WAKEUP1_ERIn                      = 1,
  WAKEUP2_ERIn                      = 2,
  WAKEUP3_ERIn                      = 3,
  ATIMER_ERIn                       = 4,
  RTC_ERIn                          = 5,
  BOD1_ERIn                         = 6,  /* Bod trip 1 */
  WWDT_ERIn                         = 7,
  ETH_ERIn                          = 8,
  USB0_ERIn                         = 9,
  USB1_ERIn                         = 10,
  SDIO_ERIn                         = 11,
  CAN_ERIn                          = 12, /* CAN0/1 or'ed */
  TIM2_ERIn                         = 13,
  TIM6_ERIn                         = 14,
  QEI_ERIn                          = 15,
  TIM14_ERIn                        = 16,
  RESERVED1_ERI                     = 17, 
  M4_ERIn                           = 18, /* M4 */ 
  RESET_ERIn                        = 19,
  BOD2_ERIn                         = 20, /* Bod trip 2 */
  PMC_ERIn                          = 21, /* Vd1_rst_req */
  REG_VD1_OK_ERIn                   = 22,
  REG_VD2_OK_ERIn                   = 23,
  REG_VD3_OK_ERIn                   = 24,
  REG_VD8_OK_ERIn                   = 25
}ERIn_Type;


/** @addtogroup Configuration_of_CMSIS
  * @{
  */

/* Processor and Core Peripheral Section */ 
/* Configuration of the Cortex-M4 Processor and Core Peripherals */

#if defined CORE_M0
#define __CM0_REV              0x0101       /*!< Cortex-M0 Core Revision               */
#define __MPU_PRESENT             0         /*!< MPU present or not                    */
#define __NVIC_PRIO_BITS          2         /*!< Number of Bits used for Priority Levels */
#define __Vendor_SysTickConfig    0         /*!< Set to 1 if different SysTick Config is used */
#endif

#ifdef CORE_M4
#define __CM4_REV              0x0001       /*!< Cortex-M4 Core Revision               */
#define __MPU_PRESENT             0         /*!< MPU present or not                    */
#define __NVIC_PRIO_BITS          3         /*!< Number of Bits used for Priority Levels */
#define __Vendor_SysTickConfig    0         /*!< Set to 1 if different SysTick Config is used */
#endif

/** @} */ /* End of group Configuration_of_CMSIS */

#ifdef CORE_M0
#include "core_cm0.h"                       /*!< Cortex-M0 processor and core peripherals */
#include "system_LPC43xx_M0.h"             /*!< LPC43xx System                           */
#endif

#ifdef CORE_M4
#include "core_cm4.h"                       /*!< Cortex-M4 processor and core peripherals */
#include "system_LPC43xx.h"                 /*!< LPC43xx System                        */
#endif

/** @addtogroup Device_Peripheral_Registers
  * @{
  */


// ------------------------------------------------------------------------------------------------
// -----                                          SCT                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx State Configurable Timer (SCT) Modification date=1/18/2011 Major revision=0 Minor revision=7  (SCT)
  */

#define CONFIG_SCT_nEV   (16)            /* Number of events */
#define CONFIG_SCT_nRG   (16)            /* Number of match/compare registers */
#define CONFIG_SCT_nOU   (16)            /* Number of outputs */

typedef struct
{
    __IO  uint32_t CONFIG;              /* 0x000 Configuration Register */
    union {
        __IO uint32_t CTRL_U;           /* 0x004 Control Register */
        struct {
            __IO uint16_t CTRL_L;       /* 0x004 low control register */
            __IO uint16_t CTRL_H;       /* 0x006 high control register */
        };
    };
    __IO uint16_t LIMIT_L;              /* 0x008 limit register for counter L */
    __IO uint16_t LIMIT_H;              /* 0x00A limit register for counter H */
    __IO uint16_t HALT_L;               /* 0x00C halt register for counter L */
    __IO uint16_t HALT_H;               /* 0x00E halt register for counter H */
    __IO uint16_t STOP_L;               /* 0x010 stop register for counter L */
    __IO uint16_t STOP_H;               /* 0x012 stop register for counter H */
    __IO uint16_t START_L;              /* 0x014 start register for counter L */
    __IO uint16_t START_H;              /* 0x016 start register for counter H */
         uint32_t RESERVED1[10];        /* 0x018-0x03C reserved */
    union {
        __IO uint32_t COUNT_U;          /* 0x040 counter register */
        struct {
            __IO uint16_t COUNT_L;      /* 0x040 counter register for counter L */
            __IO uint16_t COUNT_H;      /* 0x042 counter register for counter H */
        };
    };
    __IO uint16_t STATE_L;              /* 0x044 state register for counter L */
    __IO uint16_t STATE_H;              /* 0x046 state register for counter H */
    __I  uint32_t INPUT;                /* 0x048 input register */
    __IO uint16_t REGMODE_L;            /* 0x04C match - capture registers mode register L */
    __IO uint16_t REGMODE_H;            /* 0x04E match - capture registers mode register H */
    __IO uint32_t OUTPUT;               /* 0x050 output register */
    __IO uint32_t OUTPUTDIRCTRL;        /* 0x054 Output counter direction Control Register */
    __IO uint32_t RES;                  /* 0x058 conflict resolution register */
    __IO uint32_t DMA0REQUEST;          /* 0x05C DMA0 Request Register */
    __IO uint32_t DMA1REQUEST;          /* 0x060 DMA1 Request Register */
         uint32_t RESERVED2[35];        /* 0x064-0x0EC reserved */
    __IO uint32_t EVEN;                 /* 0x0F0 event enable register */
    __IO uint32_t EVFLAG;               /* 0x0F4 event flag register */
    __IO uint32_t CONEN;                /* 0x0F8 conflict enable register */
    __IO uint32_t CONFLAG;              /* 0x0FC conflict flag register */

    union {
        __IO union {                    /* 0x100-... Match / Capture value */
            uint32_t U;                 /*       SCTMATCH[i].U  Unified 32-bit register */
            struct {
                uint16_t L;             /*       SCTMATCH[i].L  Access to L value */
                uint16_t H;             /*       SCTMATCH[i].H  Access to H value */
            };
        } MATCH[CONFIG_SCT_nRG];
        __I union {
            uint32_t U;                 /*       SCTCAP[i].U  Unified 32-bit register */
            struct {
                uint16_t L;             /*       SCTCAP[i].L  Access to H value */
                uint16_t H;             /*       SCTCAP[i].H  Access to H value */
            };
        } CAP[CONFIG_SCT_nRG];
    };

         uint32_t RESERVED3[32-CONFIG_SCT_nRG];      /* ...-0x17C reserved */

    union {
        __IO uint16_t MATCH_L[CONFIG_SCT_nRG];       /* 0x180-... Match Value L counter */
        __I  uint16_t CAP_L[CONFIG_SCT_nRG];         /* 0x180-... Capture Value L counter */
    };
         uint16_t RESERVED4[32-CONFIG_SCT_nRG];      /* ...-0x1BE reserved */
    union {
        __IO uint16_t MATCH_H[CONFIG_SCT_nRG];       /* 0x1C0-... Match Value H counter */
        __I  uint16_t CAP_H[CONFIG_SCT_nRG];         /* 0x1C0-... Capture Value H counter */
    };
         uint16_t RESERVED5[32-CONFIG_SCT_nRG];      /* ...-0x1FE reserved */

    union {
        __IO union {                    /* 0x200-... Match Reload / Capture Control value */
            uint32_t U;                 /*       SCTMATCHREL[i].U  Unified 32-bit register */
            struct {
                uint16_t L;             /*       SCTMATCHREL[i].L  Access to L value */
                uint16_t H;             /*       SCTMATCHREL[i].H  Access to H value */
            };
        } MATCHREL[CONFIG_SCT_nRG];
        __IO union {
            uint32_t U;                 /*       SCTCAPCTRL[i].U  Unified 32-bit register */
            struct {
                uint16_t L;             /*       SCTCAPCTRL[i].L  Access to H value */
                uint16_t H;             /*       SCTCAPCTRL[i].H  Access to H value */
            };
        } CAPCTRL[CONFIG_SCT_nRG];
    };

         uint32_t RESERVED6[32-CONFIG_SCT_nRG];      /* ...-0x27C reserved */

    union {
        __IO uint16_t MATCHREL_L[CONFIG_SCT_nRG];    /* 0x280-... Match Reload value L counter */
        __IO uint16_t CAPCTRL_L[CONFIG_SCT_nRG];     /* 0x280-... Capture Control value L counter */
    };
         uint16_t RESERVED7[32-CONFIG_SCT_nRG];      /* ...-0x2BE reserved */
    union {
        __IO uint16_t MATCHREL_H[CONFIG_SCT_nRG];    /* 0x2C0-... Match Reload value H counter */
        __IO uint16_t CAPCTRL_H[CONFIG_SCT_nRG];     /* 0x2C0-... Capture Control value H counter */
    };
         uint16_t RESERVED8[32-CONFIG_SCT_nRG];      /* ...-0x2FE reserved */

    __IO struct {                       /* 0x300-0x3FC  SCTEVENT[i].STATE / SCTEVENT[i].CTRL*/
        uint32_t STATE;                 /* Event State Register */
        uint32_t CTRL;                  /* Event Control Register */
    } EVENT[CONFIG_SCT_nEV];

         uint32_t RESERVED9[128-2*CONFIG_SCT_nEV];   /* ...-0x4FC reserved */

    __IO struct {                       /* 0x500-0x57C  SCTOUT[i].SET / SCTOUT[i].CLR */
        uint32_t SET;                   /* Output n Set Register */
        uint32_t CLR;                   /* Output n Clear Register */
    } OUT[CONFIG_SCT_nOU];

         uint32_t RESERVED10[191-2*CONFIG_SCT_nOU];  /* ...-0x7F8 reserved */

    __I  uint32_t MODULECONTENT;        /* 0x7FC Module Content */

} LPC_SCT_Type;

// ------------------------------------------------------------------------------------------------
// -----                                         GPDMA                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx General Purpose DMA (GPDMA) controller Modification date=1/19/2011 Major revision=0 Minor revision=7  (GPDMA)
  */

typedef struct {                            /*!< (@ 0x40002000) GPDMA Structure        */
  __I  uint32_t INTSTAT;                    /*!< (@ 0x40002000) DMA Interrupt Status Register */
  __I  uint32_t INTTCSTAT;                  /*!< (@ 0x40002004) DMA Interrupt Terminal Count Request Status Register */
  __O  uint32_t INTTCCLEAR;                 /*!< (@ 0x40002008) DMA Interrupt Terminal Count Request Clear Register */
  __I  uint32_t INTERRSTAT;                 /*!< (@ 0x4000200C) DMA Interrupt Error Status Register */
  __O  uint32_t INTERRCLR;                  /*!< (@ 0x40002010) DMA Interrupt Error Clear Register */
  __I  uint32_t RAWINTTCSTAT;               /*!< (@ 0x40002014) DMA Raw Interrupt Terminal Count Status Register */
  __I  uint32_t RAWINTERRSTAT;              /*!< (@ 0x40002018) DMA Raw Error Interrupt Status Register */
  __I  uint32_t ENBLDCHNS;                  /*!< (@ 0x4000201C) DMA Enabled Channel Register */
  __IO uint32_t SOFTBREQ;                   /*!< (@ 0x40002020) DMA Software Burst Request Register */
  __IO uint32_t SOFTSREQ;                   /*!< (@ 0x40002024) DMA Software Single Request Register */
  __IO uint32_t SOFTLBREQ;                  /*!< (@ 0x40002028) DMA Software Last Burst Request Register */
  __IO uint32_t SOFTLSREQ;                  /*!< (@ 0x4000202C) DMA Software Last Single Request Register */
  __IO uint32_t CONFIG;                     /*!< (@ 0x40002030) DMA Configuration Register */
  __IO uint32_t SYNC;                       /*!< (@ 0x40002034) DMA Synchronization Register */
  __I  uint32_t RESERVED0[50];
  __IO uint32_t C0SRCADDR;                  /*!< (@ 0x40002100) DMA Channel Source Address Register */
  __IO uint32_t C0DESTADDR;                 /*!< (@ 0x40002104) DMA Channel Destination Address Register */
  __IO uint32_t C0LLI;                      /*!< (@ 0x40002108) DMA Channel Linked List Item Register */
  __IO uint32_t C0CONTROL;                  /*!< (@ 0x4000210C) DMA Channel Control Register */
  __IO uint32_t C0CONFIG;                   /*!< (@ 0x40002110) DMA Channel Configuration Register */
  __I  uint32_t RESERVED1[3];
  __IO uint32_t C1SRCADDR;                  /*!< (@ 0x40002120) DMA Channel Source Address Register */
  __IO uint32_t C1DESTADDR;                 /*!< (@ 0x40002124) DMA Channel Destination Address Register */
  __IO uint32_t C1LLI;                      /*!< (@ 0x40002128) DMA Channel Linked List Item Register */
  __IO uint32_t C1CONTROL;                  /*!< (@ 0x4000212C) DMA Channel Control Register */
  __IO uint32_t C1CONFIG;                   /*!< (@ 0x40002130) DMA Channel Configuration Register */
  __I  uint32_t RESERVED2[3];
  __IO uint32_t C2SRCADDR;                  /*!< (@ 0x40002140) DMA Channel Source Address Register */
  __IO uint32_t C2DESTADDR;                 /*!< (@ 0x40002144) DMA Channel Destination Address Register */
  __IO uint32_t C2LLI;                      /*!< (@ 0x40002148) DMA Channel Linked List Item Register */
  __IO uint32_t C2CONTROL;                  /*!< (@ 0x4000214C) DMA Channel Control Register */
  __IO uint32_t C2CONFIG;                   /*!< (@ 0x40002150) DMA Channel Configuration Register */
  __I  uint32_t RESERVED3[3];
  __IO uint32_t C3SRCADDR;                  /*!< (@ 0x40002160) DMA Channel Source Address Register */
  __IO uint32_t C3DESTADDR;                 /*!< (@ 0x40002164) DMA Channel Destination Address Register */
  __IO uint32_t C3LLI;                      /*!< (@ 0x40002168) DMA Channel Linked List Item Register */
  __IO uint32_t C3CONTROL;                  /*!< (@ 0x4000216C) DMA Channel Control Register */
  __IO uint32_t C3CONFIG;                   /*!< (@ 0x40002170) DMA Channel Configuration Register */
  __I  uint32_t RESERVED4[3];
  __IO uint32_t C4SRCADDR;                  /*!< (@ 0x40002180) DMA Channel Source Address Register */
  __IO uint32_t C4DESTADDR;                 /*!< (@ 0x40002184) DMA Channel Destination Address Register */
  __IO uint32_t C4LLI;                      /*!< (@ 0x40002188) DMA Channel Linked List Item Register */
  __IO uint32_t C4CONTROL;                  /*!< (@ 0x4000218C) DMA Channel Control Register */
  __IO uint32_t C4CONFIG;                   /*!< (@ 0x40002190) DMA Channel Configuration Register */
  __I  uint32_t RESERVED5[3];
  __IO uint32_t C5SRCADDR;                  /*!< (@ 0x400021A0) DMA Channel Source Address Register */
  __IO uint32_t C5DESTADDR;                 /*!< (@ 0x400021A4) DMA Channel Destination Address Register */
  __IO uint32_t C5LLI;                      /*!< (@ 0x400021A8) DMA Channel Linked List Item Register */
  __IO uint32_t C5CONTROL;                  /*!< (@ 0x400021AC) DMA Channel Control Register */
  __IO uint32_t C5CONFIG;                   /*!< (@ 0x400021B0) DMA Channel Configuration Register */
  __I  uint32_t RESERVED6[3];
  __IO uint32_t C6SRCADDR;                  /*!< (@ 0x400021C0) DMA Channel Source Address Register */
  __IO uint32_t C6DESTADDR;                 /*!< (@ 0x400021C4) DMA Channel Destination Address Register */
  __IO uint32_t C6LLI;                      /*!< (@ 0x400021C8) DMA Channel Linked List Item Register */
  __IO uint32_t C6CONTROL;                  /*!< (@ 0x400021CC) DMA Channel Control Register */
  __IO uint32_t C6CONFIG;                   /*!< (@ 0x400021D0) DMA Channel Configuration Register */
  __I  uint32_t RESERVED7[3];
  __IO uint32_t C7SRCADDR;                  /*!< (@ 0x400021E0) DMA Channel Source Address Register */
  __IO uint32_t C7DESTADDR;                 /*!< (@ 0x400021E4) DMA Channel Destination Address Register */
  __IO uint32_t C7LLI;                      /*!< (@ 0x400021E8) DMA Channel Linked List Item Register */
  __IO uint32_t C7CONTROL;                  /*!< (@ 0x400021EC) DMA Channel Control Register */
  __IO uint32_t C7CONFIG;                   /*!< (@ 0x400021F0) DMA Channel Configuration Register */
} LPC_GPDMA_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         SPIFI                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx SPI Flash Interface (SPIFI) Modification date=1/19/2011 Major revision=0 Minor revision=7  (SPIFI)
  */

typedef struct {                            /*!< (@ 0x40003000) SPIFI Structure        */
  __IO uint32_t CTRL;                       /*!< (@ 0x40003000) SPIFI control register */
  __IO uint32_t CMD;                        /*!< (@ 0x40003004) SPIFI command register */
  __IO uint32_t ADDR;                       /*!< (@ 0x40003008) SPIFI address register */
  __IO uint32_t DATINTM;                    /*!< (@ 0x4000300C) SPIFI intermediate data register */
  __IO uint32_t ADDRINTM;                   /*!< (@ 0x40003010) SPIFI address and intermediate data register */
  __IO uint32_t DAT;                        /*!< (@ 0x40003014) SPIFI data register    */
  __IO uint32_t MEMCMD;                     /*!< (@ 0x40003018) SPIFI memory command register */
  __I  uint32_t STAT;                       /*!< (@ 0x4000301C) SPIFI status register  */
} LPC_SPIFI_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         SDMMC                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10462 Chapter title=LPC43xx SD/MMC Modification date=n/a Major revision=n/a Minor revision=n/a  (SDMMC)
  */

typedef struct {                            /*!< (@ 0x40004000) SDMMC Structure        */
  __IO uint32_t CTRL;                       /*!< (@ 0x40004000) Control Register       */
  __IO uint32_t PWREN;                      /*!< (@ 0x40004004) Power Enable Register  */
  __IO uint32_t CLKDIV;                     /*!< (@ 0x40004008) Clock Divider Register */
  __IO uint32_t CLKSRC;                     /*!< (@ 0x4000400C) SD Clock Source Register */
  __IO uint32_t CLKENA;                     /*!< (@ 0x40004010) Clock Enable Register  */
  __IO uint32_t TMOUT;                      /*!< (@ 0x40004014) Timeout Register       */
  __IO uint32_t CTYPE;                      /*!< (@ 0x40004018) Card Type Register     */
  __IO uint32_t BLKSIZ;                     /*!< (@ 0x4000401C) Block Size Register    */
  __IO uint32_t BYTCNT;                     /*!< (@ 0x40004020) Byte Count Register    */
  __IO uint32_t INTMASK;                    /*!< (@ 0x40004024) Interrupt Mask Register */
  __IO uint32_t CMDARG;                     /*!< (@ 0x40004028) Command Argument Register */
  __IO uint32_t CMD;                        /*!< (@ 0x4000402C) Command Register       */
  __I  uint32_t RESP0;                      /*!< (@ 0x40004030) Response Register 0    */
  __I  uint32_t RESP1;                      /*!< (@ 0x40004034) Response Register 1    */
  __I  uint32_t RESP2;                      /*!< (@ 0x40004038) Response Register 2    */
  __I  uint32_t RESP3;                      /*!< (@ 0x4000403C) Response Register 3    */
  __I  uint32_t MINTSTS;                    /*!< (@ 0x40004040) Masked Interrupt Status Register */
  __IO uint32_t RINTSTS;                    /*!< (@ 0x40004044) Raw Interrupt Status Register */
  __I  uint32_t STATUS;                     /*!< (@ 0x40004048) Status Register        */
  __IO uint32_t FIFOTH;                     /*!< (@ 0x4000404C) FIFO Threshold Watermark Register */
  __I  uint32_t CDETECT;                    /*!< (@ 0x40004050) Card Detect Register   */
  __I  uint32_t WRTPRT;                     /*!< (@ 0x40004054) Write Protect Register */
  __IO uint32_t GPIO;                       /*!< (@ 0x40004058) General Purpose Input/Output Register */
  __I  uint32_t TCBCNT;                     /*!< (@ 0x4000405C) Transferred CIU Card Byte Count Register */
  __I  uint32_t TBBCNT;                     /*!< (@ 0x40004060) Transferred Host to BIU-FIFO Byte Count Register */
  __IO uint32_t DEBNCE;                     /*!< (@ 0x40004064) Debounce Count Register */
  __IO uint32_t USRID;                      /*!< (@ 0x40004068) User ID Register       */
  __I  uint32_t VERID;                      /*!< (@ 0x4000406C) Version ID Register    */
  __I  uint32_t RESERVED0;
  __IO uint32_t UHS_REG;                    /*!< (@ 0x40004074) UHS-1 Register         */
  __IO uint32_t RST_N;                      /*!< (@ 0x40004078) Hardware Reset         */
  __I  uint32_t RESERVED1;
  __IO uint32_t BMOD;                       /*!< (@ 0x40004080) Bus Mode Register      */
  __O  uint32_t PLDMND;                     /*!< (@ 0x40004084) Poll Demand Register   */
  __IO uint32_t DBADDR;                     /*!< (@ 0x40004088) Descriptor List Base Address Register */
  __IO uint32_t IDSTS;                      /*!< (@ 0x4000408C) Internal DMAC Status Register */
  __IO uint32_t IDINTEN;                    /*!< (@ 0x40004090) Internal DMAC Interrupt Enable Register */
  __I  uint32_t DSCADDR;                    /*!< (@ 0x40004094) Current Host Descriptor Address Register */
  __I  uint32_t BUFADDR;                    /*!< (@ 0x40004098) Current Buffer Descriptor Address Register */
} LPC_SDMMC_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          EMC                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx External Memory Controller (EMC) Modification date=1/19/2011 Major revision=0 Minor revision=7  (EMC)
  */

typedef struct {                            /*!< (@ 0x40005000) EMC Structure          */
  __IO uint32_t CONTROL;                    /*!< (@ 0x40005000) Controls operation of the memory controller. */
  __I  uint32_t STATUS;                     /*!< (@ 0x40005004) Provides EMC status information. */
  __IO uint32_t CONFIG;                     /*!< (@ 0x40005008) Configures operation of the memory controller. */
  __I  uint32_t RESERVED0[5];
  __IO uint32_t DYNAMICCONTROL;             /*!< (@ 0x40005020) Controls dynamic memory operation. */
  __IO uint32_t DYNAMICREFRESH;             /*!< (@ 0x40005024) Configures dynamic memory refresh operation. */
  __IO uint32_t DYNAMICREADCONFIG;          /*!< (@ 0x40005028) Configures the dynamic memory read strategy. */
  __I  uint32_t RESERVED1;
  __IO uint32_t DYNAMICRP;                  /*!< (@ 0x40005030) Selects the precharge command period. */
  __IO uint32_t DYNAMICRAS;                 /*!< (@ 0x40005034) Selects the active to precharge command period. */
  __IO uint32_t DYNAMICSREX;                /*!< (@ 0x40005038) Selects the self-refresh exit time. */
  __IO uint32_t DYNAMICAPR;                 /*!< (@ 0x4000503C) Selects the last-data-out to active command time. */
  __IO uint32_t DYNAMICDAL;                 /*!< (@ 0x40005040) Selects the data-in to active command time. */
  __IO uint32_t DYNAMICWR;                  /*!< (@ 0x40005044) Selects the write recovery time. */
  __IO uint32_t DYNAMICRC;                  /*!< (@ 0x40005048) Selects the active to active command period. */
  __IO uint32_t DYNAMICRFC;                 /*!< (@ 0x4000504C) Selects the auto-refresh period. */
  __IO uint32_t DYNAMICXSR;                 /*!< (@ 0x40005050) Selects the exit self-refresh to active command time. */
  __IO uint32_t DYNAMICRRD;                 /*!< (@ 0x40005054) Selects the active bank A to active bank B latency. */
  __IO uint32_t DYNAMICMRD;                 /*!< (@ 0x40005058) Selects the load mode register to active command time. */
  __I  uint32_t RESERVED2[9];
  __IO uint32_t STATICEXTENDEDWAIT;         /*!< (@ 0x40005080) Selects time for long static memory read and write transfers. */
  __I  uint32_t RESERVED3[31];
  __IO uint32_t DYNAMICCONFIG0;             /*!< (@ 0x40005100) Selects the configuration information for dynamic memory chip select n. */
  __IO uint32_t DYNAMICRASCAS0;             /*!< (@ 0x40005104) Selects the RAS and CAS latencies for dynamic memory chip select n. */
  __I  uint32_t RESERVED4[6];
  __IO uint32_t DYNAMICCONFIG1;             /*!< (@ 0x40005120) Selects the configuration information for dynamic memory chip select n. */
  __IO uint32_t DYNAMICRASCAS1;             /*!< (@ 0x40005124) Selects the RAS and CAS latencies for dynamic memory chip select n. */
  __I  uint32_t RESERVED5[6];
  __IO uint32_t DYNAMICCONFIG2;             /*!< (@ 0x40005140) Selects the configuration information for dynamic memory chip select n. */
  __IO uint32_t DYNAMICRASCAS2;             /*!< (@ 0x40005144) Selects the RAS and CAS latencies for dynamic memory chip select n. */
  __I  uint32_t RESERVED6[6];
  __IO uint32_t DYNAMICCONFIG3;             /*!< (@ 0x40005160) Selects the configuration information for dynamic memory chip select n. */
  __IO uint32_t DYNAMICRASCAS3;             /*!< (@ 0x40005164) Selects the RAS and CAS latencies for dynamic memory chip select n. */
  __I  uint32_t RESERVED7[38];
  __IO uint32_t STATICCONFIG0;              /*!< (@ 0x40005200) Selects the memory configuration for static chip select n. */
  __IO uint32_t STATICWAITWEN0;             /*!< (@ 0x40005204) Selects the delay from chip select n to write enable. */
  __IO uint32_t STATICWAITOEN0;             /*!< (@ 0x40005208) Selects the delay from chip select n or address change, whichever is later, to output enable. */
  __IO uint32_t STATICWAITRD0;              /*!< (@ 0x4000520C) Selects the delay from chip select n to a read access. */
  __IO uint32_t STATICWAITPAG0;             /*!< (@ 0x40005210) Selects the delay for asynchronous page mode sequential accesses for chip select n. */
  __IO uint32_t STATICWAITWR0;              /*!< (@ 0x40005214) Selects the delay from chip select n to a write access. */
  __IO uint32_t STATICWAITTURN0;            /*!< (@ 0x40005218) Selects bus turnaround cycles */
  __I  uint32_t RESERVED8[1];
  __IO uint32_t STATICCONFIG1;              /*!< (@ 0x40005220) Selects the memory configuration for static chip select n. */
  __IO uint32_t STATICWAITWEN1;             /*!< (@ 0x40005224) Selects the delay from chip select n to write enable. */
  __IO uint32_t STATICWAITOEN1;             /*!< (@ 0x40005228) Selects the delay from chip select n or address change, whichever is later, to output enable. */
  __IO uint32_t STATICWAITRD1;              /*!< (@ 0x4000522C) Selects the delay from chip select n to a read access. */
  __IO uint32_t STATICWAITPAG1;             /*!< (@ 0x40005230) Selects the delay for asynchronous page mode sequential accesses for chip select n. */
  __IO uint32_t STATICWAITWR1;              /*!< (@ 0x40005234) Selects the delay from chip select n to a write access. */
  __I  uint32_t STATICWAITTURN1;            /*!< (@ 0x40005238) read-write             */
  __I  uint32_t RESERVED9[1];
  __IO uint32_t STATICCONFIG2;              /*!< (@ 0x40005240) Selects the memory configuration for static chip select n. */
  __IO uint32_t STATICWAITWEN2;             /*!< (@ 0x40005244) Selects the delay from chip select n to write enable. */
  __IO uint32_t STATICWAITOEN2;             /*!< (@ 0x40005248) Selects the delay from chip select n or address change, whichever is later, to output enable. */
  __IO uint32_t STATICWAITRD2;              /*!< (@ 0x4000524C) Selects the delay from chip select n to a read access. */
  __IO uint32_t STATICWAITPAG2;             /*!< (@ 0x40005250) Selects the delay for asynchronous page mode sequential accesses for chip select n. */
  __IO uint32_t STATICWAITWR2;              /*!< (@ 0x40005254) Selects the delay from chip select n to a write access. */
  __I  uint32_t STATICWAITTURN2;            /*!< (@ 0x40005258) read-write             */
  __I  uint32_t RESERVED10[1];
  __IO uint32_t STATICCONFIG3;              /*!< (@ 0x40005260) Selects the memory configuration for static chip select n. */
  __IO uint32_t STATICWAITWEN3;             /*!< (@ 0x40005264) Selects the delay from chip select n to write enable. */
  __IO uint32_t STATICWAITOEN3;             /*!< (@ 0x40005268) Selects the delay from chip select n or address change, whichever is later, to output enable. */
  __IO uint32_t STATICWAITRD3;              /*!< (@ 0x4000526C) Selects the delay from chip select n to a read access. */
  __IO uint32_t STATICWAITPAG3;             /*!< (@ 0x40005270) Selects the delay for asynchronous page mode sequential accesses for chip select n. */
  __IO uint32_t STATICWAITWR3;              /*!< (@ 0x40005274) Selects the delay from chip select n to a write access. */
  __I  uint32_t STATICWAITTURN3;            /*!< (@ 0x40005278) read-write             */
} LPC_EMC_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         USB0                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx USB0 Host/Device/OTG controller Modification date=1/19/2011 Major revision=0 Minor revision=7  (USB0)
  */

typedef struct {                            /*!< (@ 0x40006000) USB0 Structure         */
  __I  uint32_t RESERVED0[64];
  __I  uint32_t CAPLENGTH;                  /*!< (@ 0x40006100) Capability register length */
  __I  uint32_t HCSPARAMS;                  /*!< (@ 0x40006104) Host controller structural parameters */
  __I  uint32_t HCCPARAMS;                  /*!< (@ 0x40006108) Host controller capability parameters */
  __I  uint32_t RESERVED1[5];
  __I  uint32_t DCIVERSION;                 /*!< (@ 0x40006120) Device interface version number */
  __I  uint32_t RESERVED2[7];
  
  union {
    __IO uint32_t USBCMD_H;                 /*!< (@ 0x40006140) USB command (host mode) */
    __IO uint32_t USBCMD_D;                 /*!< (@ 0x40006140) USB command (device mode) */
  };
  
  union {
    __IO uint32_t USBSTS_H;                 /*!< (@ 0x40006144) USB status (host mode) */
    __IO uint32_t USBSTS_D;                 /*!< (@ 0x40006144) USB status (device mode) */
  };
  
  union {
    __IO uint32_t USBINTR_H;                /*!< (@ 0x40006148) USB interrupt enable (host mode) */
    __IO uint32_t USBINTR_D;                /*!< (@ 0x40006148) USB interrupt enable (device mode) */
  };
  
  union {
    __IO uint32_t FRINDEX_H;                /*!< (@ 0x4000614C) USB frame index (host mode) */
    __IO uint32_t FRINDEX_D;                /*!< (@ 0x4000614C) USB frame index (device mode) */
  };
  __I  uint32_t RESERVED3;
  
  union {
    __IO uint32_t PERIODICLISTBASE;         /*!< (@ 0x40006154) Frame list base address (host mode) */
    __IO uint32_t DEVICEADDR;               /*!< (@ 0x40006154) USB device address (device mode) */
  };
  
  union {
    __IO uint32_t ASYNCLISTADDR;            /*!< (@ 0x40006158) Address of endpoint list in memory */
    __IO uint32_t ENDPOINTLISTADDR;         /*!< (@ 0x40006158) Address of endpoint list in memory */
  };
  __IO uint32_t TTCTRL;                     /*!< (@ 0x4000615C) Asynchronous buffer status for embedded TT (host mode) */
  __IO uint32_t BURSTSIZE;                  /*!< (@ 0x40006160) Programmable burst size */
  __IO uint32_t TXFILLTUNING;               /*!< (@ 0x40006164) Host transmit pre-buffer packet tuning (host mode) */
  __I  uint32_t RESERVED4[3];
  __IO uint32_t BINTERVAL;                  /*!< (@ 0x40006174) Length of virtual frame */
  __IO uint32_t ENDPTNAK;                   /*!< (@ 0x40006178) Endpoint NAK (device mode) */
  __IO uint32_t ENDPTNAKEN;                 /*!< (@ 0x4000617C) Endpoint NAK Enable (device mode) */
  __I  uint32_t RESERVED5;
  
  union {
    __IO uint32_t PORTSC1_H;                /*!< (@ 0x40006184) Port 1 status/control (host mode) */
    __IO uint32_t PORTSC1_D;                /*!< (@ 0x40006184) Port 1 status/control (device mode) */
  };
  __I  uint32_t RESERVED6[7];
  __IO uint32_t OTGSC;                      /*!< (@ 0x400061A4) OTG status and control */
  
  union {
    __IO uint32_t USBMODE_H;                /*!< (@ 0x400061A8) USB mode (host mode)   */
    __IO uint32_t USBMODE_D;                /*!< (@ 0x400061A8) USB device mode (device mode) */
  };
  __IO uint32_t ENDPTSETUPSTAT;             /*!< (@ 0x400061AC) Endpoint setup status  */
  __IO uint32_t ENDPTPRIME;                 /*!< (@ 0x400061B0) Endpoint initialization */
  __IO uint32_t ENDPTFLUSH;                 /*!< (@ 0x400061B4) Endpoint de-initialization */
  __I  uint32_t ENDPTSTAT;                  /*!< (@ 0x400061B8) Endpoint status        */
  __IO uint32_t ENDPTCOMPLETE;              /*!< (@ 0x400061BC) Endpoint complete      */
  __IO uint32_t ENDPTCTRL0;                 /*!< (@ 0x400061C0) Endpoint control 0     */
  __IO uint32_t ENDPTCTRL[5];               /*!< (@ 0x400061C4) Endpoint control       */
} LPC_USB0_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         USB1                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx USB1 Host/Device controller Modification date=1/19/2011 Major revision=0 Minor revision=7  (USB1)
  */

typedef struct {                            /*!< (@ 0x40007000) USB1 Structure         */
  __I  uint32_t RESERVED0[64];
  __I  uint32_t CAPLENGTH;                  /*!< (@ 0x40007100) Capability register length */
  __I  uint32_t HCSPARAMS;                  /*!< (@ 0x40007104) Host controller structural parameters */
  __I  uint32_t HCCPARAMS;                  /*!< (@ 0x40007108) Host controller capability parameters */
  __I  uint32_t RESERVED1[5];
  __I  uint32_t DCIVERSION;                 /*!< (@ 0x40007120) Device interface version number */
  __I  uint32_t RESERVED2[7];
  
  union {
    __IO uint32_t USBCMD_H;                 /*!< (@ 0x40007140) USB command (host mode) */
    __IO uint32_t USBCMD_D;                 /*!< (@ 0x40007140) USB command (device mode) */
  };
  
  union {
    __IO uint32_t USBSTS_H;                 /*!< (@ 0x40007144) USB status (host mode) */
    __IO uint32_t USBSTS_D;                 /*!< (@ 0x40007144) USB status (device mode) */
  };
  
  union {
    __IO uint32_t USBINTR_H;                /*!< (@ 0x40007148) USB interrupt enable (host mode) */
    __IO uint32_t USBINTR_D;                /*!< (@ 0x40007148) USB interrupt enable (device mode) */
  };
  
  union {
    __IO uint32_t FRINDEX_H;                /*!< (@ 0x4000714C) USB frame index (host mode) */
    __I  uint32_t FRINDEX_D;                /*!< (@ 0x4000714C) USB frame index (device mode) */
  };
  __I  uint32_t RESERVED3;
  
  union {
    __IO uint32_t PERIODICLISTBASE;         /*!< (@ 0x40007154) Frame list base address */
    __IO uint32_t DEVICEADDR;               /*!< (@ 0x40007154) USB device address     */
  };
  
  union {
    __IO uint32_t ASYNCLISTADDR;            /*!< (@ 0x40007158) Address of endpoint list in memory (host mode) */
    __IO uint32_t ENDPOINTLISTADDR;         /*!< (@ 0x40007158) Address of endpoint list in memory (device mode) */
  };
  __IO uint32_t TTCTRL;                     /*!< (@ 0x4000715C) Asynchronous buffer status for embedded TT (host mode) */
  __IO uint32_t BURSTSIZE;                  /*!< (@ 0x40007160) Programmable burst size */
  __IO uint32_t TXFILLTUNING;               /*!< (@ 0x40007164) Host transmit pre-buffer packet tuning (host mode) */
  __I  uint32_t RESERVED4[2];
  __IO uint32_t ULPIVIEWPORT;               /*!< (@ 0x40007170) ULPI viewport          */
  __IO uint32_t BINTERVAL;                  /*!< (@ 0x40007174) Length of virtual frame */
  __IO uint32_t ENDPTNAK;                   /*!< (@ 0x40007178) Endpoint NAK (device mode) */
  __IO uint32_t ENDPTNAKEN;                 /*!< (@ 0x4000717C) Endpoint NAK Enable (device mode) */
  __I  uint32_t RESERVED5;
  
  union {
    __IO uint32_t PORTSC1_H;                /*!< (@ 0x40007184) Port 1 status/control (host mode) */
    __IO uint32_t PORTSC1_D;                /*!< (@ 0x40007184) Port 1 status/control (device mode) */
  };
  __I  uint32_t RESERVED6[8];
  
  union {
    __IO uint32_t USBMODE_H;                /*!< (@ 0x400071A8) USB mode (host mode)   */
    __IO uint32_t USBMODE_D;                /*!< (@ 0x400071A8) USB mode (device mode) */
  };
  __IO uint32_t ENDPTSETUPSTAT;             /*!< (@ 0x400071AC) Endpoint setup status  */
  __IO uint32_t ENDPTPRIME;                 /*!< (@ 0x400071B0) Endpoint initialization */
  __IO uint32_t ENDPTFLUSH;                 /*!< (@ 0x400071B4) Endpoint de-initialization */
  __I  uint32_t ENDPTSTAT;                  /*!< (@ 0x400071B8) Endpoint status        */
  __IO uint32_t ENDPTCOMPLETE;              /*!< (@ 0x400071BC) Endpoint complete      */
  __IO uint32_t ENDPTCTRL0;                 /*!< (@ 0x400071C0) Endpoint control 0     */
  __IO uint32_t ENDPTCTRL[3];               /*!< (@ 0x400071C4) Endpoint control       */
} LPC_USB1_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          LCD                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx LCD Modification date=1/19/2011 Major revision=0 Minor revision=7  (LCD)
  */

typedef struct {                            /*!< (@ 0x40008000) LCD Structure          */
  __IO uint32_t TIMH;                       /*!< (@ 0x40008000) Horizontal Timing Control register */
  __IO uint32_t TIMV;                       /*!< (@ 0x40008004) Vertical Timing Control register */
  __IO uint32_t POL;                        /*!< (@ 0x40008008) Clock and Signal Polarity Control register */
  __IO uint32_t LE;                         /*!< (@ 0x4000800C) Line End Control register */
  __IO uint32_t UPBASE;                     /*!< (@ 0x40008010) Upper Panel Frame Base Address register */
  __IO uint32_t LPBASE;                     /*!< (@ 0x40008014) Lower Panel Frame Base Address register */
  __IO uint32_t CTRL;                       /*!< (@ 0x40008018) LCD Control register   */
  __IO uint32_t INTMSK;                     /*!< (@ 0x4000801C) Interrupt Mask register */
  __I  uint32_t INTRAW;                     /*!< (@ 0x40008020) Raw Interrupt Status register */
  __I  uint32_t INTSTAT;                    /*!< (@ 0x40008024) Masked Interrupt Status register */
  __O  uint32_t INTCLR;                     /*!< (@ 0x40008028) Interrupt Clear register */
  __I  uint32_t UPCURR;                     /*!< (@ 0x4000802C) Upper Panel Current Address Value register */
  __I  uint32_t LPCURR;                     /*!< (@ 0x40008030) Lower Panel Current Address Value register */
  __I  uint32_t RESERVED0[115];
  __IO uint32_t PAL[256];                   /*!< (@ 0x40008200) 256x16-bit Color Palette registers */
  __I  uint32_t RESERVED1[128];
  __IO uint32_t CRSR_IMG[256];              /*!< (@ 0x40008800) Cursor Image registers */
  __IO uint32_t CRSR_CTRL;                  /*!< (@ 0x40008C00) Cursor Control register */
  __IO uint32_t CRSR_CFG;                   /*!< (@ 0x40008C04) Cursor Configuration register */
  __IO uint32_t CRSR_PAL0;                  /*!< (@ 0x40008C08) Cursor Palette register 0 */
  __IO uint32_t CRSR_PAL1;                  /*!< (@ 0x40008C0C) Cursor Palette register 1 */
  __IO uint32_t CRSR_XY;                    /*!< (@ 0x40008C10) Cursor XY Position register */
  __IO uint32_t CRSR_CLIP;                  /*!< (@ 0x40008C14) Cursor Clip Position register */
  __I  uint32_t RESERVED2[2];
  __IO uint32_t CRSR_INTMSK;                /*!< (@ 0x40008C20) Cursor Interrupt Mask register */
  __O  uint32_t CRSR_INTCLR;                /*!< (@ 0x40008C24) Cursor Interrupt Clear register */
  __I  uint32_t CRSR_INTRAW;                /*!< (@ 0x40008C28) Cursor Raw Interrupt Status register */
  __I  uint32_t CRSR_INTSTAT;               /*!< (@ 0x40008C2C) Cursor Masked Interrupt Status register */
} LPC_LCD_Type;


// ------------------------------------------------------------------------------------------------
// -----                                       ETHERNET                                       -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Ethernet Modification date=1/20/2011 Major revision=0 Minor revision=7  (ETHERNET)
  */

typedef struct {                            /*!< (@ 0x40010000) ETHERNET Structure     */
  __IO uint32_t MAC_CONFIG;                 /*!< (@ 0x40010000) MAC configuration register */
  __IO uint32_t MAC_FRAME_FILTER;           /*!< (@ 0x40010004) MAC frame filter       */
  __IO uint32_t MAC_HASHTABLE_HIGH;         /*!< (@ 0x40010008) Hash table high register */
  __IO uint32_t MAC_HASHTABLE_LOW;          /*!< (@ 0x4001000C) Hash table low register */
  __IO uint32_t MAC_MII_ADDR;               /*!< (@ 0x40010010) MII address register   */
  __IO uint32_t MAC_MII_DATA;               /*!< (@ 0x40010014) MII data register      */
  __IO uint32_t MAC_FLOW_CTRL;              /*!< (@ 0x40010018) Flow control register  */
  __IO uint32_t MAC_VLAN_TAG;               /*!< (@ 0x4001001C) VLAN tag register      */
  __I  uint32_t RESERVED0;
  __IO uint32_t MAC_DEBUG;                  /*!< (@ 0x40010024) Debug register         */
  __IO uint32_t MAC_RWAKE_FRFLT;            /*!< (@ 0x40010028) Remote wake-up frame filter */
  __IO uint32_t MAC_PMT_CTRL_STAT;          /*!< (@ 0x4001002C) PMT control and status */
  __I  uint32_t RESERVED1[2];
  __IO uint32_t MAC_INTR;                   /*!< (@ 0x40010038) Interrupt status register */
  __IO uint32_t MAC_INTR_MASK;              /*!< (@ 0x4001003C) Interrupt mask register */
  __IO uint32_t MAC_ADDR0_HIGH;             /*!< (@ 0x40010040) MAC address 0 high register */
  __IO uint32_t MAC_ADDR0_LOW;              /*!< (@ 0x40010044) MAC address 0 low register */
  __I  uint32_t RESERVED2[430];
  __IO uint32_t MAC_TIMESTP_CTRL;           /*!< (@ 0x40010700) Time stamp control register */
  __I  uint32_t RESERVED3[575];
  __IO uint32_t DMA_BUS_MODE;               /*!< (@ 0x40011000) Bus Mode Register      */
  __IO uint32_t DMA_TRANS_POLL_DEMAND;      /*!< (@ 0x40011004) Transmit poll demand register */
  __IO uint32_t DMA_REC_POLL_DEMAND;        /*!< (@ 0x40011008) Receive poll demand register */
  __IO uint32_t DMA_REC_DES_ADDR;           /*!< (@ 0x4001100C) Receive descriptor list address register */
  __IO uint32_t DMA_TRANS_DES_ADDR;         /*!< (@ 0x40011010) Transmit descriptor list address register */
  __IO uint32_t DMA_STAT;                   /*!< (@ 0x40011014) Status register        */
  __IO uint32_t DMA_OP_MODE;                /*!< (@ 0x40011018) Operation mode register */
  __IO uint32_t DMA_INT_EN;                 /*!< (@ 0x4001101C) Interrupt enable register */
  __IO uint32_t DMA_MFRM_BUFOF;             /*!< (@ 0x40011020) Missed frame and buffer overflow register */
  __IO uint32_t DMA_REC_INT_WDT;            /*!< (@ 0x40011024) Receive interrupt watchdog timer register */
  __I  uint32_t RESERVED4[8];
  __IO uint32_t DMA_CURHOST_TRANS_DES;      /*!< (@ 0x40011048) Current host transmit descriptor register */
  __IO uint32_t DMA_CURHOST_REC_DES;        /*!< (@ 0x4001104C) Current host receive descriptor register */
  __IO uint32_t DMA_CURHOST_TRANS_BUF;      /*!< (@ 0x40011050) Current host transmit buffer address register */
  __IO uint32_t DMA_CURHOST_REC_BUF;        /*!< (@ 0x40011054) Current host receive buffer address register */
} LPC_ETHERNET_Type;


// ------------------------------------------------------------------------------------------------
// -----                                        ATIMER                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Alarm timer Modification date=1/7/2011 Major revision=0 Minor revision=6  (ATIMER)
  */

typedef struct {                            /*!< (@ 0x40040000) ATIMER Structure       */
  __IO uint32_t DOWNCOUNTER;                /*!< (@ 0x40040000) Downcounter register   */
  __IO uint32_t PRESET;                     /*!< (@ 0x40040004) Preset value register  */
  __I  uint32_t RESERVED0[1012];
  __O  uint32_t CLR_EN;                     /*!< (@ 0x40040FD8) Interrupt clear enable register */
  __O  uint32_t SET_EN;                     /*!< (@ 0x40040FDC) Interrupt set enable register */
  __I  uint32_t STATUS;                     /*!< (@ 0x40040FE0) Status register        */
  __I  uint32_t ENABLE;                     /*!< (@ 0x40040FE4) Enable register        */
  __O  uint32_t CLR_STAT;                   /*!< (@ 0x40040FE8) Clear register         */
  __O  uint32_t SET_STAT;                   /*!< (@ 0x40040FEC) Set register           */
} LPC_ATIMER_Type;


// ------------------------------------------------------------------------------------------------
// -----                                        REGFILE                                       -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx rtc/REGFILE date=1/20/2011 Major revision=0 Minor revision=7  (REGFILE)
  */

typedef struct {                            /*!< (@ 0x40041000) REGFILE Structure      */
  __IO uint32_t REGFILE[64];                /*!< (@ 0x40041000) General purpose storage register */
} LPC_REGFILE_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          PMC                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Power Management Controller (PMC) Modification date=1/20/2011 Major revision=0 Minor revision=7  (PMC)
  */

typedef struct {                            /*!< (@ 0x40042000) PMC Structure          */
  __IO uint32_t PD0_SLEEP0_HW_ENA;          /*!< (@ 0x40042000) Hardware sleep event enable register */
       uint32_t RESERVED0;
  __IO uint32_t PD0_SLEEP0_HW_EDG_LVL;      /* 0x008 */
       uint32_t RESERVED1[3];
  __IO uint32_t PD0_SLEEP0_CONFIG;          /* 0x018 */
  __IO uint32_t PD0_SLEEP0_MODE;            /*!< (@ 0x4004201C) Sleep power mode register */
       uint32_t RESERVED2[24];
  __IO uint32_t PD0_WAKE0_HW_ENA;           /* 0x080 */
       uint32_t RESERVED3;
  __IO uint32_t PD0_WAKE0_HW_EDG_LVL;       /* 0x088 */
       uint32_t RESERVED4[67];
  __IO uint32_t PD0_PSU_OPT;                /* 0x198 */
       uint32_t RESERVED5[2];
  __IO uint32_t PD0_PSU_DELAY;              /* 0x1A4 */
       uint32_t RESERVED6;
  __IO uint32_t PD0_POST_PSU_DELAY;			/* 0x1AC */
} LPC_PMC_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         CREG                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Configuration Registers (CREG) Modification date=1/20/2011 Major revision=0 Minor revision=7  (CREG)
  */

typedef struct {                            /*!< (@ 0x40043000) CREG Structure         */
  __IO uint32_t IRCTRM;                     /*!< (@ 0x40043000) IRC trim register      */
  __IO uint32_t CREG0;                      /*!< (@ 0x40043004) Chip configuration register 32 kHz oscillator output and BOD control register. */
  __IO uint32_t PMUCON;                     /*!< (@ 0x40043008) Power mode control register. */
  __I  uint32_t RESERVED0[61];
  __IO uint32_t M4MEMMAP;                   /*!< (@ 0x40043100) ARM Cortex-M4 memory mapping */
  __I  uint32_t RESERVED1[5];
  __IO uint32_t CREG5;                      /*!< (@ 0x40043118) Chip configuration register 5. Controls JTAG access. */
  __IO uint32_t DMAMUX;                     /*!< (@ 0x4004311C) DMA muxing control     */
  __I  uint32_t RESERVED2[2];
  __IO uint32_t ETBCFG;                     /*!< (@ 0x40043128) ETB RAM configuration  */
  __IO uint32_t CREG6;                      /*!< (@ 0x4004312C) tbd.                   */
  __I  uint32_t RESERVED3[52];
  __I  uint32_t CHIPID;                     /*!< (@ 0x40043200) Part ID                */
} LPC_CREG_Type;


// ------------------------------------------------------------------------------------------------
// -----                                      EVENTROUTER                                     -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Event router Modification date=1/20/2011 Major revision=0 Minor revision=7  (EVENTROUTER)
  */

typedef struct {                            /*!< (@ 0x40044000) EVENTROUTER Structure  */
  __IO uint32_t HILO;                       /*!< (@ 0x40044000) Level configuration register */
  __IO uint32_t EDGE;                       /*!< (@ 0x40044004) Edge configuration     */
  __I  uint32_t RESERVED0[1012];
  __O  uint32_t CLR_EN;                     /*!< (@ 0x40044FD8) Event clear enable register */
  __O  uint32_t SET_EN;                     /*!< (@ 0x40044FDC) Event set enable register */
  __I  uint32_t STATUS;                     /*!< (@ 0x40044FE0) Status register        */
  __I  uint32_t ENABLE;                     /*!< (@ 0x40044FE4) Enable register        */
  __O  uint32_t CLR_STAT;                   /*!< (@ 0x40044FE8) Clear register         */
  __O  uint32_t SET_STAT;                   /*!< (@ 0x40044FEC) Set register           */
} LPC_EVENTROUTER_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          RTC                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Real-Time Clock (RTC) Modification date=1/20/2011 Major revision=0 Minor revision=7  (RTC)
  */

typedef struct {                            /*!< (@ 0x40046000) RTC Structure          */
  __O  uint32_t ILR;                        /*!< (@ 0x40046000) Interrupt Location Register */
  __I  uint32_t RESERVED0;
  __IO uint32_t CCR;                        /*!< (@ 0x40046008) Clock Control Register */
  __IO uint32_t CIIR;                       /*!< (@ 0x4004600C) Counter Increment Interrupt Register */
  __IO uint32_t AMR;                        /*!< (@ 0x40046010) Alarm Mask Register    */
  __I  uint32_t CTIME0;                     /*!< (@ 0x40046014) Consolidated Time Register 0 */
  __I  uint32_t CTIME1;                     /*!< (@ 0x40046018) Consolidated Time Register 1 */
  __I  uint32_t CTIME2;                     /*!< (@ 0x4004601C) Consolidated Time Register 2 */
  __IO uint32_t SEC;                        /*!< (@ 0x40046020) Seconds Register       */
  __IO uint32_t MIN;                        /*!< (@ 0x40046024) Minutes Register       */
  __IO uint32_t HRS;                        /*!< (@ 0x40046028) Hours Register         */
  __IO uint32_t DOM;                        /*!< (@ 0x4004602C) Day of Month Register  */
  __IO uint32_t DOW;                        /*!< (@ 0x40046030) Day of Week Register   */
  __IO uint32_t DOY;                        /*!< (@ 0x40046034) Day of Year Register   */
  __IO uint32_t MONTH;                      /*!< (@ 0x40046038) Months Register        */
  __IO uint32_t YEAR;                       /*!< (@ 0x4004603C) Years Register         */
  __IO uint32_t CALIBRATION;                /*!< (@ 0x40046040) Calibration Value Register */
  __I  uint32_t RESERVED1[7];
  __IO uint32_t ASEC;                       /*!< (@ 0x40046060) Alarm value for Seconds */
  __IO uint32_t AMIN;                       /*!< (@ 0x40046064) Alarm value for Minutes */
  __IO uint32_t AHRS;                       /*!< (@ 0x40046068) Alarm value for Hours  */
  __IO uint32_t ADOM;                       /*!< (@ 0x4004606C) Alarm value for Day of Month */
  __IO uint32_t ADOW;                       /*!< (@ 0x40046070) Alarm value for Day of Week */
  __IO uint32_t ADOY;                       /*!< (@ 0x40046074) Alarm value for Day of Year */
  __IO uint32_t AMON;                       /*!< (@ 0x40046078) Alarm value for Months */
  __IO uint32_t AYRS;                       /*!< (@ 0x4004607C) Alarm value for Year   */
} LPC_RTC_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          CGU                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10462 Chapter title=LPC43xx Clock Generation Unit (CGU) Modification date=6/1/2011 Major revision=0 Minor revision=1  (CGU)
  */

typedef struct {                            /*!< (@ 0x40050000) CGU Structure          */
  __I  uint32_t RESERVED0[5];
  __IO uint32_t FREQ_MON;                   /*!< (@ 0x40050014) Frequency monitor register */
  __IO uint32_t XTAL_OSC_CTRL;              /*!< (@ 0x40050018) Crystal oscillator control register */
  __I  uint32_t PLL0USB_STAT;               /*!< (@ 0x4005001C) PLL0 (USB) status register */
  __IO uint32_t PLL0USB_CTRL;               /*!< (@ 0x40050020) PLL0 (USB) control register */
  __IO uint32_t PLL0USB_MDIV;               /*!< (@ 0x40050024) PLL0 (USB) M-divider register */
  __IO uint32_t PLL0USB_NP_DIV;             /*!< (@ 0x40050028) PLL0 (USB) N/P-divider register */
  __I  uint32_t PLL0AUDIO_STAT;             /*!< (@ 0x4005002C) PLL0 (audio) status register */
  __IO uint32_t PLL0AUDIO_CTRL;             /*!< (@ 0x40050030) PLL0 (audio) control register */
  __IO uint32_t PLL0AUDIO_MDIV;             /*!< (@ 0x40050034) PLL0 (audio) M-divider register */
  __IO uint32_t PLL0AUDIO_NP_DIV;           /*!< (@ 0x40050038) PLL0 (audio) N/P-divider register */
  __IO uint32_t PLL0AUDIO_FRAC;             /*!< (@ 0x4005003C) PLL0 (audio)           */
  __I  uint32_t PLL1_STAT;                  /*!< (@ 0x40050040) PLL1 status register   */
  __IO uint32_t PLL1_CTRL;                  /*!< (@ 0x40050044) PLL1 control register  */
  __IO uint32_t IDIVA_CTRL;                 /*!< (@ 0x40050048) Integer divider A control register */
  __IO uint32_t IDIVB_CTRL;                 /*!< (@ 0x4005004C) Integer divider B control register */
  __IO uint32_t IDIVC_CTRL;                 /*!< (@ 0x40050050) Integer divider C control register */
  __IO uint32_t IDIVD_CTRL;                 /*!< (@ 0x40050054) Integer divider D control register */
  __IO uint32_t IDIVE_CTRL;                 /*!< (@ 0x40050058) Integer divider E control register */
  __IO uint32_t BASE_SAFE_CLK;              /*!< (@ 0x4005005C) Output stage 0 control register for base clock BASE_SAFE_CLK */
  __IO uint32_t BASE_USB0_CLK;              /*!< (@ 0x40050060) Output stage 1 control register for base clock BASE_USB0_CLK */
  __IO uint32_t BASE_M0_CLK;                /*!< (@ 0x40050064) */
  __IO uint32_t BASE_USB1_CLK;              /*!< (@ 0x40050068) Output stage 3 control register for base clock BASE_USB1_CLK */
  __IO uint32_t BASE_M4_CLK;                /*!< (@ 0x4005006C) Output stage control register  */
  __IO uint32_t BASE_SPIFI0_CLK;            /*!< (@ 0x40050070) Output stage control register  */
  __IO uint32_t BASE_SPI_CLK;               /*!< (@ 0x40050074) Output stage control register  */
  __IO uint32_t BASE_PHY_RX_CLK;            /*!< (@ 0x40050078) Output stage control register  */
  __IO uint32_t BASE_PHY_TX_CLK;            /*!< (@ 0x4005007C) Output stage control register  */
  __IO uint32_t BASE_APB1_CLK;              /*!< (@ 0x40050080) Output stage control register  */
  __IO uint32_t BASE_APB3_CLK;              /*!< (@ 0x40050084) Output stage control register  */
  __IO uint32_t BASE_LCD_CLK;               /*!< (@ 0x40050088) Output stage control register  */
  __IO uint32_t BASE_VADC_CLK;         		/*!< (@ 0x4005008C) Output stage control register  */
  __IO uint32_t BASE_SDIO_CLK;              /*!< (@ 0x40050090) Output stage control register  */
  __IO uint32_t BASE_SSP0_CLK;              /*!< (@ 0x40050094) Output stage control register  */
  __IO uint32_t BASE_SSP1_CLK;              /*!< (@ 0x40050098) Output stage control register  */
  __IO uint32_t BASE_UART0_CLK;             /*!< (@ 0x4005009C) Output stage control register  */
  __IO uint32_t BASE_UART1_CLK;             /*!< (@ 0x400500A0) Output stage control register  */
  __IO uint32_t BASE_UART2_CLK;             /*!< (@ 0x400500A4) Output stage control register  */
  __IO uint32_t BASE_UART3_CLK;             /*!< (@ 0x400500A8) Output stage control register  */
  __IO uint32_t BASE_OUT_CLK;               /*!< (@ 0x400500AC) Output stage 20 control register for base clock BASE_OUT_CLK */
  __IO uint32_t BASE_AOTEST_CLK;            /*!< (@ 0x400500B0) */
  __IO uint32_t BASE_ISO_TCK;               /*!< (@ 0x400500B4) */
  __IO uint32_t BASE_BSR_TCK;               /*!< (@ 0x400500B8) */
  __IO uint32_t BASE_CLK_TESTSHELL;         /*!< (@ 0x400500BC) */
  __IO uint32_t BASE_APLL_CLK;              /*!< (@ 0x400500C0) Output stage 25 control register for base clock BASE_APLL_CLK */
  __IO uint32_t BASE_CGU_OUT0_CLK;          /*!< (@ 0x400500C4) Output stage 26 control register for base clock BASE_CGU_OUT0_CLK */
  __IO uint32_t BASE_CGU_OUT1_CLK;          /*!< (@ 0x400500C8) Output stage 27 control register for base clock BASE_CGU_OUT1_CLK */
} LPC_CGU_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         CCU1                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Clock Control Unit (CCU) Modification date=1/21/2011 Major revision=0 Minor revision=7  (CCU1)
  */

typedef struct {                            /*!< (@ 0x40051000) CCU1 Structure         */
  __IO uint32_t PM;                         /*!< (@ 0x40051000) CCU1 power mode register */
  __I  uint32_t BASE_STAT;                  /*!< (@ 0x40051004) CCU1 base clocks status register */
  __I  uint32_t RESERVED0[62];
  __IO uint32_t CLK_APB3_BUS_CFG;           /*!< (@ 0x40051100) CLK_APB3_BUS clock configuration register */
  __I  uint32_t CLK_APB3_BUS_STAT;          /*!< (@ 0x40051104) CLK_APB3_BUS clock status register */
  __IO uint32_t CLK_APB3_I2C1_CFG;          /*!< (@ 0x40051108) CLK_APB3_I2C1 clock configuration register */
  __I  uint32_t CLK_APB3_I2C1_STAT;         /*!< (@ 0x4005110C) CLK_APB3_I2C1 clock status register */
  __IO uint32_t CLK_APB3_DAC_CFG;           /*!< (@ 0x40051110) CLK_APB3_DAC clock configuration register */
  __I  uint32_t CLK_APB3_DAC_STAT;          /*!< (@ 0x40051114) CLK_APB3_DAC clock status register */
  __IO uint32_t CLK_APB3_ADC0_CFG;          /*!< (@ 0x40051118) CLK_APB3_ADC0 clock configuration register */
  __I  uint32_t CLK_APB3_ADC0_STAT;         /*!< (@ 0x4005111C) CLK_APB3_ADC0 clock status register */
  __IO uint32_t CLK_APB3_ADC1_CFG;          /*!< (@ 0x40051120) CLK_APB3_ADC1 clock configuration register */
  __I  uint32_t CLK_APB3_ADC1_STAT;         /*!< (@ 0x40051124) CLK_APB3_ADC1 clock status register */
  __IO uint32_t CLK_APB3_CAN0_CFG;          /*!< (@ 0x40051128) CLK_APB3_CAN0 clock configuration register */
  __I  uint32_t CLK_APB3_CAN0_STAT;         /*!< (@ 0x4005112C) CLK_APB3_CAN0 clock status register */
  __IO uint32_t CLK_APB3_SPARE0_CFG;        /*!< (@ 0x40051130) */
  __I  uint32_t CLK_APB3_SPARE0_STAT;       /*!< (@ 0x40051134) */
  __I  uint32_t RESERVED1[52-2];
  __IO uint32_t CLK_APB1_BUS_CFG;           /*!< (@ 0x40051200) CLK_APB1_BUS clock configuration register */
  __I  uint32_t CLK_APB1_BUS_STAT;          /*!< (@ 0x40051204) CLK_APB1_BUS clock status register */
  __IO uint32_t CLK_APB1_MOTOCONPWM_CFG;    /*!< (@ 0x40051208) CLK_APB1_MOTOCONPWM clock configuration register */
  __I  uint32_t CLK_APB1_MOTOCONPWM_STAT;   /*!< (@ 0x4005120C) CLK_APB1_MOTOCONPWM clock status register */
  __IO uint32_t CLK_ABP1_I2C0_CFG;          /*!< (@ 0x40051210) CLK_ABP1_I2C0 clock configuration register */
  __I  uint32_t CLK_APB1_I2C0_STAT;         /*!< (@ 0x40051214) CLK_APB1_I2C0 clock status register */
  __IO uint32_t CLK_APB1_I2S_CFG;           /*!< (@ 0x40051218) CLK_APB1_I2S clock configuration register */
  __I  uint32_t CLK_APB1_I2S_STAT;          /*!< (@ 0x4005121C) CLK_APB1_I2S clock status register */
  __IO uint32_t CLK_APB1_CAN1_CFG;          /*!< (@ 0x40051220) CLK_APB1_CAN1 clock configuration register */
  __I  uint32_t CLK_APB1_CAN1_STAT;         /*!< (@ 0x40051224) CLK_APB1_CAN1 clock status register */
  __IO uint32_t CLK_APB1_SPARE0_CFG;        /*!< (@ 0x40051228) */
  __I  uint32_t CLK_APB1_SPARE0_STAT;       /*!< (@ 0x4005122C) */
  __I  uint32_t RESERVED2[54-2];
  __IO uint32_t CLK_SPIFI_CFG;              /*!< (@ 0x40051300) CLK_SPIFI clock configuration register */
  __I  uint32_t CLK_SPIFI_STAT;             /*!< (@ 0x40051304) CLK_APB1_SPIFI clock status register */
  __I  uint32_t RESERVED3[62];
  __IO uint32_t CLK_M4_BUS_CFG;             /*!< (@ 0x40051400) CLK_M4_BUS clock configuration register */
  __I  uint32_t CLK_M4_BUS_STAT;            /*!< (@ 0x40051404) CLK_M4_BUSclock status register */
  __IO uint32_t CLK_M4_SPIFI_CFG;           /*!< (@ 0x40051408) CLK_M4_SPIFI clock configuration register */
  __I  uint32_t CLK_M4_SPIFI_STAT;          /*!< (@ 0x4005140C) CLK_M4_SPIFI clock status register */
  __IO uint32_t CLK_M4_GPIO_CFG;            /*!< (@ 0x40051410) CLK_M4_GPIO clock configuration register */
  __I  uint32_t CLK_M4_GPIO_STAT;           /*!< (@ 0x40051414) CLK_M4_GPIO clock status register */
  __IO uint32_t CLK_M4_LCD_CFG;             /*!< (@ 0x40051418) CLK_M4_LCD clock configuration register */
  __I  uint32_t CLK_M4_LCD_STAT;            /*!< (@ 0x4005141C) CLK_M4_LCD clock status register */
  __IO uint32_t CLK_M4_ETHERNET_CFG;        /*!< (@ 0x40051420) CLK_M4_ETHERNET clock configuration register */
  __I  uint32_t CLK_M4_ETHERNET_STAT;       /*!< (@ 0x40051424) CLK_M4_ETHERNET clock status register */
  __IO uint32_t CLK_M4_USB0_CFG;            /*!< (@ 0x40051428) CLK_M4_USB0 clock configuration register */
  __I  uint32_t CLK_M4_USB0_STAT;           /*!< (@ 0x4005142C) CLK_M4_USB0 clock status register */
  __IO uint32_t CLK_M4_EMC_CFG;             /*!< (@ 0x40051430) CLK_M4_EMC clock configuration register */
  __I  uint32_t CLK_M4_EMC_STAT;            /*!< (@ 0x40051434) CLK_M4_EMC clock status register */
  __IO uint32_t CLK_M4_SDIO_CFG;            /*!< (@ 0x40051438) CLK_M4_SDIO clock configuration register */
  __I  uint32_t CLK_M4_SDIO_STAT;           /*!< (@ 0x4005143C) CLK_M4_SDIO clock status register */
  __IO uint32_t CLK_M4_DMA_CFG;             /*!< (@ 0x40051440) CLK_M4_DMA clock configuration register */
  __I  uint32_t CLK_M4_DMA_STAT;            /*!< (@ 0x40051444) CLK_M4_DMA clock status register */
  __IO uint32_t CLK_M4_M4CORE_CFG;          /*!< (@ 0x40051448) CLK_M4_M4CORE clock configuration register */
  __I  uint32_t CLK_M4_M4CORE_STAT;         /*!< (@ 0x4005144C) CLK_M4_M4CORE clock status register */
  __IO uint32_t CLK_M4_USART_CFG;           /*!< (@ 0x40051450) Reserved for Eagle */
  __I  uint32_t CLK_M4_USART_STAT;          /*!< (@ 0x40051454) Reserved for Eagle */
  __IO uint32_t CLK_M4_EVENTHANDLER_CFG;    /*!< (@ 0x40051458) Reserved for Eagle */
  __I  uint32_t CLK_M4_EVENTHANDLER_STAT;   /*!< (@ 0x4005145C) Reserved for Eagle */
//  __I  uint32_t RESERVED4[4];
  __IO uint32_t CLK_M4_AES_CFG;             /*!< (@ 0x40051460) CLK_M4_AES clock configuration register */
  __I  uint32_t CLK_M4_AES_STAT;            /*!< (@ 0x40051464) CLK_M4_AES clock status register */
  __IO uint32_t CLK_M4_SCT_CFG;             /*!< (@ 0x40051468) CLK_M4_SCT clock configuration register */
  __I  uint32_t CLK_M4_SCT_STAT;            /*!< (@ 0x4005146C) CLK_M4_SCT clock status register */
  __IO uint32_t CLK_M4_USB1_CFG;            /*!< (@ 0x40051470) CLK_M4_USB1 clock configuration register */
  __I  uint32_t CLK_M4_USB1_STAT;           /*!< (@ 0x40051474) CLK_M4_USB1 clock status register */
  __IO uint32_t CLK_M4_EMCDIV_CFG;          /*!< (@ 0x40051478) CLK_M4_EMCDIV clock configuration register */
  __I  uint32_t CLK_M4_EMCDIV_STAT;         /*!< (@ 0x4005147C) CLK_M4_EMCDIV clock status register */
  __IO uint32_t CLK_M4_FLASH0_CFG;          /*!< (@ 0x40051480)  */
  __I  uint32_t CLK_M4_FLASH0_STAT;         /*!< (@ 0x40051484)  */
  __IO uint32_t CLK_M4_FLASH1_CFG;          /*!< (@ 0x40051488)  */
  __I  uint32_t CLK_M4_FLASH1_STAT;         /*!< (@ 0x4005148C)  */
  __IO uint32_t CLK_M4_M0ACORE_CFG;	        /*!< (@ 0x40051490)  */
  __I  uint32_t CLK_M4_M0ACORE_STAT;		/*!< (@ 0x40051494)  */
  __IO uint32_t CLK_M4_VADC_CFG;			/*!< (@ 0x40051498)  */
  __I  uint32_t CLK_M4_VADC_STAT;			/*!< (@ 0x4005149C)  */
  __IO uint32_t CLK_M4_EEPROM_CFG;          /*!< (@ 0x400514A0)  */
  __I  uint32_t CLK_M4_EEPROM_STAT;         /*!< (@ 0x400514A4)  */
  __IO uint32_t CLK_M4_SPARE0_CFG;          /*!< (@ 0x400514A8)  */
  __I  uint32_t CLK_M4_SPARE0_STAT;         /*!< (@ 0x400514AC)  */
  __IO uint32_t CLK_M4_SPARE1_CFG;          /*!< (@ 0x400514B0)  */
  __I  uint32_t CLK_M4_SPARE1_STAT;         /*!< (@ 0x400514B4)  */
  __I  uint32_t RESERVED5[32-14];
  __IO uint32_t CLK_M4_WWDT_CFG;            /*!< (@ 0x40051500) CLK_M4_WWDT clock configuration register */
  __I  uint32_t CLK_M4_WWDT_STAT;           /*!< (@ 0x40051504) CLK_M4_WWDT clock status register */
  __IO uint32_t CLK_M4_USART0_CFG;          /*!< (@ 0x40051508) CLK_M4_USART0 clock configuration register */
  __I  uint32_t CLK_M4_USART0_STAT;         /*!< (@ 0x4005150C) CLK_M4_USART0 clock status register */
  __IO uint32_t CLK_M4_UART1_CFG;           /*!< (@ 0x40051510) CLK_M4_UART1 clock configuration register */
  __I  uint32_t CLK_M4_UART1_STAT;          /*!< (@ 0x40051514) CLK_M4_UART1 clock status register */
  __IO uint32_t CLK_M4_SSP0_CFG;            /*!< (@ 0x40051518) CLK_M4_SSP0 clock configuration register */
  __I  uint32_t CLK_M4_SSP0_STAT;           /*!< (@ 0x4005151C) CLK_M4_SSP0 clock status register */
  __IO uint32_t CLK_M4_TIMER0_CFG;          /*!< (@ 0x40051520) CLK_M4_TIMER0 clock configuration register */
  __I  uint32_t CLK_M4_TIMER0_STAT;         /*!< (@ 0x40051524) CLK_M4_TIMER0 clock status register */
  __IO uint32_t CLK_M4_TIMER1_CFG;          /*!< (@ 0x40051528) CLK_M4_TIMER1clock configuration register */
  __I  uint32_t CLK_M4_TIMER1_STAT;         /*!< (@ 0x4005152C) CLK_M4_TIMER1 clock status register */
  __IO uint32_t CLK_M4_SCU_CFG;             /*!< (@ 0x40051530) CLK_M4_SCU clock configuration register */
  __I  uint32_t CLK_M4_SCU_STAT;            /*!< (@ 0x40051534) CLK_SCU_XXX clock status register */
  __IO uint32_t CLK_M4_CREG_CFG;            /*!< (@ 0x40051538) CLK_M4_CREGclock configuration register */
  __I  uint32_t CLK_M4_CREG_STAT;           /*!< (@ 0x4005153C) CLK_M4_CREG clock status register */
  __IO uint32_t CLK_APB0_SPARE1_CFG;        /*!< (@ 0x40051540)  */
  __I  uint32_t CLK_APB0_SPARE1_STAT;       /*!< (@ 0x40051544)  */
  __I  uint32_t RESERVED6[48-2];
  __IO uint32_t CLK_M4_RITIMER_CFG;         /*!< (@ 0x40051600) CLK_M4_RITIMER clock configuration register */
  __I  uint32_t CLK_M4_RITIMER_STAT;        /*!< (@ 0x40051604) CLK_M4_RITIMER clock status register */
  __IO uint32_t CLK_M4_USART2_CFG;          /*!< (@ 0x40051608) CLK_M4_USART2 clock configuration register */
  __I  uint32_t CLK_M4_USART2_STAT;         /*!< (@ 0x4005160C) CLK_M4_USART2 clock status register */
  __IO uint32_t CLK_M4_USART3_CFG;          /*!< (@ 0x40051610) CLK_M4_USART3 clock configuration register */
  __I  uint32_t CLK_M4_USART3_STAT;         /*!< (@ 0x40051614) CLK_M4_USART3 clock status register */
  __IO uint32_t CLK_M4_TIMER2_CFG;          /*!< (@ 0x40051618) CLK_M4_TIMER2 clock configuration register */
  __I  uint32_t CLK_M4_TIMER2_STAT;         /*!< (@ 0x4005161C) CLK_M4_TIMER2 clock status register */
  __IO uint32_t CLK_M4_TIMER3_CFG;          /*!< (@ 0x40051620) CLK_M4_TIMER3 clock configuration register */
  __I  uint32_t CLK_M4_TIMER3_STAT;         /*!< (@ 0x40051624) CLK_M4_TIMER3 clock status register */
  __IO uint32_t CLK_M4_SSP1_CFG;            /*!< (@ 0x40051628) CLK_M4_SSP1 clock configuration register */
  __I  uint32_t CLK_M4_SSP1_STAT;           /*!< (@ 0x4005162C) CLK_M4_SSP1 clock status register */
  __IO uint32_t CLK_M4_QEI_CFG;             /*!< (@ 0x40051630) CLK_M4_QEIclock configuration register */
  __I  uint32_t CLK_M4_QEI_STAT;            /*!< (@ 0x40051634) CLK_M4_QEI clock status register */
  __IO uint32_t CLK_APB2_SPARE1_CFG;        /*!< (@ 0x40051638)  */
  __I  uint32_t CLK_APB2_SPARE1_STAT;       /*!< (@ 0x4005163C)  */
  __I  uint32_t RESERVED7[48];
  __IO uint32_t CLK_M0_BUS_CFG;             /*!< (@ 0x40051700)  */
  __I  uint32_t CLK_M0_BUS_STAT;            /*!< (@ 0x40051704)  */
  __IO uint32_t CLK_M0_GPIO_CFG;            /*!< (@ 0x40051708)  */
  __I  uint32_t CLK_M0_GPIO_STAT;           /*!< (@ 0x4005170C)  */
  __IO uint32_t CLK_M0_M0SCORE_CFG;         /*!< (@ 0x40051710)  */
  __I  uint32_t CLK_M0_M0SCORE_STAT;        /*!< (@ 0x40051714)  */
  __IO uint32_t CLK_M0_SGPIO_CFG;           /*!< (@ 0x40051718)  */
  __I  uint32_t CLK_M0_SGPIO_STAT;          /*!< (@ 0x4005171C)  */
  __IO uint32_t CLK_M0_EDM_CFG;             /*!< (@ 0x40051720)  */
  __I  uint32_t CLK_M0_EDM_STAT;            /*!< (@ 0x40051724)  */
  __I  uint32_t RESERVED72[54];
  __IO uint32_t CLK_USB0_CFG;               /*!< (@ 0x40051800) CLK_M4_USB0 clock configuration register */
  __I  uint32_t CLK_USB0_STAT;              /*!< (@ 0x40051804) CLK_USB0 clock status register */
  __I  uint32_t RESERVED8[62];
  __IO uint32_t CLK_USB1_CFG;               /*!< (@ 0x40051900) CLK_USB1 clock configuration register */
  __I  uint32_t CLK_USB1_STAT;              /*!< (@ 0x40051904) CLK_USB1 clock status register */
  __I  uint32_t RESERVED9[126];
  __IO uint32_t CLK_VADC_CFG;               /*!< (@ 0x40051B00) CLK_VADC clock configuration register */
  __I  uint32_t CLK_VADC_STAT;              /*!< (@ 0x40051B04) CLK_VADC clock status register */
} LPC_CCU1_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         CCU2                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Clock Control Unit (CCU) Modification date=1/21/2011 Major revision=0 Minor revision=7  (CCU2)
  */

typedef struct {                            /*!< (@ 0x40052000) CCU2 Structure         */
  __IO uint32_t PM;                         /*!< (@ 0x40052000) Power mode register    */
  __I  uint32_t BASE_STAT;                  /*!< (@ 0x40052004) CCU base clocks status register */
  __I  uint32_t RESERVED0[62];
  __IO uint32_t CLK_APLL_CFG;               /*!< (@ 0x40052100) CLK_APLL clock configuration register */
  __I  uint32_t CLK_APLL_STAT;              /*!< (@ 0x40052104) CLK_APLL clock status register */
  __I  uint32_t RESERVED1[62];
  __IO uint32_t CLK_APB2_USART3_CFG;        /*!< (@ 0x40052200) CLK_APB2_USART3 clock configuration register */
  __I  uint32_t CLK_APB2_USART3_STAT;       /*!< (@ 0x40052204) CLK_APB2_USART3 clock status register */
  __I  uint32_t RESERVED2[62];
  __IO uint32_t CLK_APB2_USART2_CFG;        /*!< (@ 0x40052300) CLK_APB2_USART2 clock configuration register */
  __I  uint32_t CLK_APB2_USART2_STAT;       /*!< (@ 0x40052304) CLK_APB2_USART clock status register */
  __I  uint32_t RESERVED3[62];
  __IO uint32_t CLK_APB0_UART1_CFG;     /*!< (@ 0x40052400) CLK_APB2_UART1 clock configuration register */
  __I  uint32_t CLK_APB0_UART1_STAT;        /*!< (@ 0x40052404) CLK_APB0_UART1 clock status register */
  __I  uint32_t RESERVED4[62];
  __IO uint32_t CLK_APB0_USART0_CFG;        /*!< (@ 0x40052500) CLK_APB2_USART0 clock configuration register */
  __I  uint32_t CLK_APB0_USART0_STAT;       /*!< (@ 0x40052504) CLK_APB0_USART0 clock status register */
  __I  uint32_t RESERVED5[62];
  __IO uint32_t CLK_APB2_SSP1_CFG;          /*!< (@ 0x40052600) CLK_APB2_SSP1 clock configuration register */
  __I  uint32_t CLK_APB2_SSP1_STAT;         /*!< (@ 0x40052604) CLK_APB2_SSP1 clock status register */
  __I  uint32_t RESERVED6[62];
  __IO uint32_t CLK_APB0_SSP0_CFG;          /*!< (@ 0x40052700) CLK_APB0_SSP0 clock configuration register */
  __I  uint32_t CLK_APB0_SSP0_STAT;         /*!< (@ 0x40052704) CLK_APB0_SSP0 clock status register */
  __I  uint32_t RESERVED7[62];
  __IO uint32_t CLK_SDIO_CFG;               /*!< (@ 0x40052800) CLK_SDIO clock configuration register */
  __I  uint32_t CLK_SDIO_STAT;              /*!< (@ 0x40052804) CLK_SDIO clock status register */
} LPC_CCU2_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          RGU                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Reset Generation Unit (RGU) Modification date=1/21/2011 Major revision=0 Minor revision=7  (RGU)
  */

typedef struct {                            /*!< (@ 0x40053000) RGU Structure          */
  __I  uint32_t RESERVED0[64];
  __O  uint32_t RESET_CTRL0;                /*!< (@ 0x40053100) Reset control register 0 */
  __O  uint32_t RESET_CTRL1;                /*!< (@ 0x40053104) Reset control register 1 */
  __I  uint32_t RESERVED1[2];
  __IO uint32_t RESET_STATUS0;              /*!< (@ 0x40053110) Reset status register 0 */
  __IO uint32_t RESET_STATUS1;              /*!< (@ 0x40053114) Reset status register 1 */
  __IO uint32_t RESET_STATUS2;              /*!< (@ 0x40053118) Reset status register 2 */
  __IO uint32_t RESET_STATUS3;              /*!< (@ 0x4005311C) Reset status register 3 */
  __I  uint32_t RESERVED2[12];
  __I  uint32_t RESET_ACTIVE_STATUS0;       /*!< (@ 0x40053150) Reset active status register 0 */
  __I  uint32_t RESET_ACTIVE_STATUS1;       /*!< (@ 0x40053154) Reset active status register 1 */
  __I  uint32_t RESERVED3[170];
  __IO uint32_t RESET_EXT_STAT0;            /*!< (@ 0x40053400) Reset external status register 0 for CORE_RST */
  __IO uint32_t RESET_EXT_STAT1;            /*!< (@ 0x40053404) Reset external status register 1 for PERIPH_RST */
  __IO uint32_t RESET_EXT_STAT2;            /*!< (@ 0x40053408) Reset external status register 2 for MASTER_RST */
  __I  uint32_t RESERVED4;
  __IO uint32_t RESET_EXT_STAT4;            /*!< (@ 0x40053410) Reset external status register 4 for WWDT_RST */
  __IO uint32_t RESET_EXT_STAT5;            /*!< (@ 0x40053414) Reset external status register 5 for CREG_RST */
  __I  uint32_t RESERVED5[2];
  __IO uint32_t RESET_EXT_STAT8;            /*!< (@ 0x40053420) Reset external status register */
  __IO uint32_t RESET_EXT_STAT9;            /*!< (@ 0x40053424) Reset external status register */
  __I  uint32_t RESERVED6[3];
  __IO uint32_t RESET_EXT_STAT13;           /*!< (@ 0x40053434) Reset external status register */
  __I  uint32_t RESERVED7[2];
  __IO uint32_t RESET_EXT_STAT16;           /*!< (@ 0x40053440) Reset external status register */
  __IO uint32_t RESET_EXT_STAT17;           /*!< (@ 0x40053444) Reset external status register */
  __IO uint32_t RESET_EXT_STAT18;           /*!< (@ 0x40053448) Reset external status register */
  __IO uint32_t RESET_EXT_STAT19;           /*!< (@ 0x4005344C) Reset external status register */
  __IO uint32_t RESET_EXT_STAT20;           /*!< (@ 0x40053450) Reset external status register */
  __IO uint32_t RESET_EXT_STAT21;           /*!< (@ 0x40053454) Reset external status register */
  __IO uint32_t RESET_EXT_STAT22;           /*!< (@ 0x40053458) Reset external status register */
  __IO uint32_t RESET_EXT_STAT23;           /*!< (@ 0x4005345C) Reset external status register */
  __I  uint32_t RESERVED8[4];
  __IO uint32_t RESET_EXT_STAT28;           /*!< (@ 0x40053470) Reset external status register */
  __I  uint32_t RESERVED9[3];
  __IO uint32_t RESET_EXT_STAT32;           /*!< (@ 0x40053480) Reset external status register */
  __IO uint32_t RESET_EXT_STAT33;           /*!< (@ 0x40053484) Reset external status register */
  __IO uint32_t RESET_EXT_STAT34;           /*!< (@ 0x40053488) Reset external status register */
  __IO uint32_t RESET_EXT_STAT35;           /*!< (@ 0x4005348C) Reset external status register */
  __IO uint32_t RESET_EXT_STAT36;           /*!< (@ 0x40053490) Reset external status register */
  __IO uint32_t RESET_EXT_STAT37;           /*!< (@ 0x40053494) Reset external status register */
  __IO uint32_t RESET_EXT_STAT38;           /*!< (@ 0x40053498) Reset external status register */
  __IO uint32_t RESET_EXT_STAT39;           /*!< (@ 0x4005349C) Reset external status register */
  __IO uint32_t RESET_EXT_STAT40;           /*!< (@ 0x400534A0) Reset external status register */
  __IO uint32_t RESET_EXT_STAT41;           /*!< (@ 0x400534A4) Reset external status register */
  __IO uint32_t RESET_EXT_STAT42;           /*!< (@ 0x400534A8) Reset external status register */
  __I  uint32_t RESERVED10;
  __IO uint32_t RESET_EXT_STAT44;           /*!< (@ 0x400534B0) Reset external status register */
  __IO uint32_t RESET_EXT_STAT45;           /*!< (@ 0x400534B4) Reset external status register */
  __IO uint32_t RESET_EXT_STAT46;           /*!< (@ 0x400534B8) Reset external status register */
  __IO uint32_t RESET_EXT_STAT47;           /*!< (@ 0x400534BC) Reset external status register */
  __IO uint32_t RESET_EXT_STAT48;           /*!< (@ 0x400534C0) Reset external status register */
  __IO uint32_t RESET_EXT_STAT49;           /*!< (@ 0x400534C4) Reset external status register */
  __IO uint32_t RESET_EXT_STAT50;           /*!< (@ 0x400534C8) Reset external status register */
  __IO uint32_t RESET_EXT_STAT51;           /*!< (@ 0x400534CC) Reset external status register */
  __IO uint32_t RESET_EXT_STAT52;           /*!< (@ 0x400534D0) Reset external status register */
  __IO uint32_t RESET_EXT_STAT53;           /*!< (@ 0x400534D4) Reset external status register */
  __I  uint32_t RESERVED11;
  __IO uint32_t RESET_EXT_STAT55;           /*!< (@ 0x400534DC) Reset external status register */
  __IO uint32_t RESET_EXT_STAT56;           /*!< (@ 0x400534E0) Reset external status register */
} LPC_RGU_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         WWDT                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Windowed Watchdog timer (WWDT) Modification date=1/14/2011 Major revision=0 Minor revision=7  (WWDT)
  */

typedef struct {                            /*!< (@ 0x40080000) WWDT Structure         */
  __IO uint32_t MOD;                        /*!< (@ 0x40080000) Watchdog mode register. This register contains the basic mode and status of the Watchdog Timer. */
  __IO uint32_t TC;                         /*!< (@ 0x40080004) Watchdog timer constant register. This register determines the time-out value. */
  __O  uint32_t FEED;                       /*!< (@ 0x40080008) Watchdog feed sequence register. Writing 0xAA followed by 0x55 to this register reloads the Watchdog timer with the value contained in WDTC. */
  __I  uint32_t TV;                         /*!< (@ 0x4008000C) Watchdog timer value register. This register reads out the current value of the Watchdog timer. */
  __I  uint32_t RESERVED0;
  __IO uint32_t WARNINT;                    /*!< (@ 0x40080014) Watchdog warning interrupt register. This register contains the Watchdog warning interrupt compare value. */
  __IO uint32_t WINDOW;                     /*!< (@ 0x40080018) Watchdog timer window register. This register contains the Watchdog window value. */
} LPC_WWDT_Type;


// ------------------------------------------------------------------------------------------------
// -----                                        USARTn                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx USART0_2_3 Modification date=1/14/2011 Major revision=0 Minor revision=7  (USARTn)
  */

typedef struct {                            /*!< (@ 0x400xx000) USARTn Structure       */

  union {
    __IO uint32_t DLL;                      /*!< (@ 0x400xx000) Divisor Latch LSB. Least significant byte of the baud rate divisor value. The full divisor is used to generate a baud rate from the fractional rate divider (DLAB = 1). */
    __O  uint32_t THR;                      /*!< (@ 0x400xx000) Transmit Holding Register. The next character to be transmitted is written here (DLAB = 0). */
    __I  uint32_t RBR;                      /*!< (@ 0x400xx000) Receiver Buffer Register. Contains the next received character to be read (DLAB = 0). */
  };

  union {
    __IO uint32_t IER;                      /*!< (@ 0x400xx004) Interrupt Enable Register. Contains individual interrupt enable bits for the 7 potential UART interrupts (DLAB = 0). */
    __IO uint32_t DLM;                      /*!< (@ 0x400xx004) Divisor Latch MSB. Most significant byte of the baud rate divisor value. The full divisor is used to generate a baud rate from the fractional rate divider (DLAB = 1). */
  };

  union {
    __O  uint32_t FCR;                      /*!< (@ 0x400xx008) FIFO Control Register. Controls UART FIFO usage and modes. */
    __I  uint32_t IIR;                      /*!< (@ 0x400xx008) Interrupt ID Register. Identifies which interrupt(s) are pending. */
  };
  __IO uint32_t LCR;                        /*!< (@ 0x400xx00C) Line Control Register. Contains controls for frame formatting and break generation. */
  __I  uint32_t RESERVED0[1];
  __I  uint32_t LSR;                        /*!< (@ 0x400xx014) Line Status Register. Contains flags for transmit and receive status, including line errors. */
  __I  uint32_t RESERVED1[1];
  __IO uint32_t SCR;                        /*!< (@ 0x400xx01C) Scratch Pad Register. Eight-bit temporary storage for software. */
  __IO uint32_t ACR;                        /*!< (@ 0x400xx020) Auto-baud Control Register. Contains controls for the auto-baud feature. */
  __IO uint32_t ICR;                        /*!< (@ 0x400xx024) IrDA control register (UART3 only) */
  __IO uint32_t FDR;                        /*!< (@ 0x400xx028) Fractional Divider Register. Generates a clock input for the baud rate divider. */
  __I  uint32_t RESERVED2[4];
  __IO uint32_t HDEN;                       /*!< (@ 0x400xx03C) Half-duplex enable Register */
  __I  uint32_t RESERVED3[2];
  __IO uint32_t SCICTRL;                    /*!< (@ 0x400xx048) Smart card interface control register */
  __IO uint32_t RS485CTRL;                  /*!< (@ 0x400xx04C) RS-485/EIA-485 Control. Contains controls to configure various aspects of RS-485/EIA-485 modes. */
  __IO uint32_t RS485ADRMATCH;              /*!< (@ 0x400xx050) RS-485/EIA-485 address match. Contains the address match value for RS-485/EIA-485 mode. */
  __IO uint32_t RS485DLY;                   /*!< (@ 0x400xx054) RS-485/EIA-485 direction control delay. */
  __IO uint32_t SYNCCTRL;                   /*!< (@ 0x400xx058) Synchronous mode control register. */
  __IO uint32_t TER;                        /*!< (@ 0x400xx05C) Transmit Enable Register. Turns off UART transmitter for use with software flow control. */
} LPC_USARTn_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         UART1                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx UART1 Modification date=1/14/2011 Major revision=0 Minor revision=7  (UART1)
  */

typedef struct {                            /*!< (@ 0x40082000) UART1 Structure        */

  union {
    __IO uint32_t DLL;                      /*!< (@ 0x40082000) Divisor Latch LSB. Least significant byte of the baud rate divisor value. The full divisor is used to generate a baud rate from the fractional rate divider. (DLAB=1) */
    __O  uint32_t THR;                      /*!< (@ 0x40082000) Transmit Holding Register. The next character to be transmitted is written here. (DLAB=0) */
    __I  uint32_t RBR;                      /*!< (@ 0x40082000) Receiver Buffer Register. Contains the next received character to be read. (DLAB=0) */
  };

  union {
    __IO uint32_t IER;                      /*!< (@ 0x40082004) Interrupt Enable Register. Contains individual interrupt enable bits for the 7 potential UART1 interrupts. (DLAB=0) */
    __IO uint32_t DLM;                      /*!< (@ 0x40082004) Divisor Latch MSB. Most significant byte of the baud rate divisor value. The full divisor is used to generate a baud rate from the fractional rate divider.(DLAB=1) */
  };

  union {
    __O  uint32_t FCR;                      /*!< (@ 0x40082008) FIFO Control Register. Controls UART1 FIFO usage and modes. */
    __I  uint32_t IIR;                      /*!< (@ 0x40082008) Interrupt ID Register. Identifies which interrupt(s) are pending. */
  };
  __IO uint32_t LCR;                        /*!< (@ 0x4008200C) Line Control Register. Contains controls for frame formatting and break generation. */
  __IO uint32_t MCR;                        /*!< (@ 0x40082010) Modem Control Register. Contains controls for flow control handshaking and loopback mode. */
  __I  uint32_t LSR;                        /*!< (@ 0x40082014) Line Status Register. Contains flags for transmit and receive status, including line errors. */
  __I  uint32_t MSR;                        /*!< (@ 0x40082018) Modem Status Register. Contains handshake signal status flags. */
  __IO uint32_t SCR;                        /*!< (@ 0x4008201C) Scratch Pad Register. 8-bit temporary storage for software. */
  __IO uint32_t ACR;                        /*!< (@ 0x40082020) Auto-baud Control Register. Contains controls for the auto-baud feature. */
  __I  uint32_t RESERVED0[1];
  __IO uint32_t FDR;                        /*!< (@ 0x40082028) Fractional Divider Register. Generates a clock input for the baud rate divider. */
  __I  uint32_t RESERVED1[1];
  __IO uint32_t TER;                        /*!< (@ 0x40082030) Transmit Enable Register. Turns off UART transmitter for use with software flow control. */
  __I  uint32_t RESERVED2[6];
  __IO uint32_t RS485CTRL;                  /*!< (@ 0x4008204C) RS-485/EIA-485 Control. Contains controls to configure various aspects of RS-485/EIA-485 modes. */
  __IO uint32_t RS485ADRMATCH;              /*!< (@ 0x40082050) RS-485/EIA-485 address match. Contains the address match value for RS-485/EIA-485 mode. */
  __IO uint32_t RS485DLY;                   /*!< (@ 0x40082054) RS-485/EIA-485 direction control delay. */
  __I  uint32_t FIFOLVL;                    /*!< (@ 0x40082058) FIFO Level register. Provides the current fill levels of the transmit and receive FIFOs.  */
} LPC_UART1_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         SSPn                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx SSP0/1 Modification date=1/14/2011 Major revision=0 Minor revision=7  (SSP0)
  */

typedef struct {                            /*!< (@ 0x400xx000) SSPn Structure         */
  __IO uint32_t CR0;                        /*!< (@ 0x400xx000) Control Register 0. Selects the serial clock rate, bus type, and data size. */
  __IO uint32_t CR1;                        /*!< (@ 0x400xx004) Control Register 1. Selects master/slave and other modes. */
  __IO uint32_t DR;                         /*!< (@ 0x400xx008) Data Register. Writes fill the transmit FIFO, and reads empty the receive FIFO. */
  __I  uint32_t SR;                         /*!< (@ 0x400xx00C) Status Register        */
  __IO uint32_t CPSR;                       /*!< (@ 0x400xx010) Clock Prescale Register */
  __IO uint32_t IMSC;                       /*!< (@ 0x400xx014) Interrupt Mask Set and Clear Register */
  __I  uint32_t RIS;                        /*!< (@ 0x400xx018) Raw Interrupt Status Register */
  __I  uint32_t MIS;                        /*!< (@ 0x400xx01C) Masked Interrupt Status Register */
  __O  uint32_t ICR;                        /*!< (@ 0x400xx020) SSPICR Interrupt Clear Register */
  __IO uint32_t DMACR;                      /*!< (@ 0x400xx024) SSPn DMA control register */
} LPC_SSPn_Type;


// ------------------------------------------------------------------------------------------------
// -----                                        TIMERn                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Timer0/1/2/3 Modification date=1/14/2011 Major revision=0 Minor revision=7  (TIMERn)
  */

typedef struct {                            /*!< (@ 0x400xx000) TIMERn Structure       */
  __IO uint32_t IR;                         /*!< (@ 0x400xx000) Interrupt Register. The IR can be written to clear interrupts. The IR can be read to identify which of eight possible interrupt sources are pending. */
  __IO uint32_t TCR;                        /*!< (@ 0x400xx004) Timer Control Register. The TCR is used to control the Timer Counter functions. The Timer Counter can be disabled or reset through the TCR. */
  __IO uint32_t TC;                         /*!< (@ 0x400xx008) Timer Counter. The 32 bit TC is incremented every PR+1 cycles of PCLK. The TC is controlled through the TCR. */
  __IO uint32_t PR;                         /*!< (@ 0x400xx00C) Prescale Register. The Prescale Counter (below) is equal to this value, the next clock increments the TC and clears the PC. */
  __IO uint32_t PC;                         /*!< (@ 0x400xx010) Prescale Counter. The 32 bit PC is a counter which is incremented to the value stored in PR. When the value in PR is reached, the TC is incremented and the PC is cleared. The PC is observable and controllable through the bus interface. */
  __IO uint32_t MCR;                        /*!< (@ 0x400xx014) Match Control Register. The MCR is used to control if an interrupt is generated and if the TC is reset when a Match occurs. */
  __IO uint32_t MR[4];                      /*!< (@ 0x400xx018) Match Register. MR can be enabled through the MCR to reset the TC, stop both the TC and PC, and/or generate an interrupt every time MR matches the TC. */
  __IO uint32_t CCR;                        /*!< (@ 0x400xx028) Capture Control Register. The CCR controls which edges of the capture inputs are used to load the Capture Registers and whether or not an interrupt is generated when a capture takes place. */
  __IO uint32_t CR[4];                      /*!< (@ 0x400xx02C) Capture Register. CR is loaded with the value of TC when there is an event on the CAPn.0 input. */
  __IO uint32_t EMR;                        /*!< (@ 0x400xx03C) External Match Register. The EMR controls the external match pins MATn.0-3 (MAT0.0-3 and MAT1.0-3 respectively). */
  __I  uint32_t RESERVED0[12];
  __IO uint32_t CTCR;                       /*!< (@ 0x400xx070) Count Control Register. The CTCR selects between Timer and Counter mode, and in Counter mode selects the signal and edge(s) for counting. */
} LPC_TIMERn_Type;




// ------------------------------------------------------------------------------------------------
// -----                                          SCU                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx System Control Unit (SCU) Modification date=6/8/2011 Major revision=0 Minor revision=10  (SCU)
  */

typedef struct {                            /*!< (@ 0x40086000) SCU Structure          */
  __IO uint32_t SFSP0_0;                   /*!< (@ 0x40086000) Pin configuration register for pins P0 */
  __IO uint32_t SFSP0_1;                   /*!< (@ 0x40086004) Pin configuration register for pins P0 */
  __I  uint32_t RESERVED0[30];
  __IO uint32_t SFSP1_0;                    /*!< (@ 0x40086080) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_1;                    /*!< (@ 0x40086084) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_2;                    /*!< (@ 0x40086088) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_3;                    /*!< (@ 0x4008608C) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_4;                    /*!< (@ 0x40086090) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_5;                    /*!< (@ 0x40086094) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_6;                    /*!< (@ 0x40086098) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_7;                    /*!< (@ 0x4008609C) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_8;                    /*!< (@ 0x400860A0) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_9;                    /*!< (@ 0x400860A4) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_10;                   /*!< (@ 0x400860A8) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_11;                   /*!< (@ 0x400860AC) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_12;                   /*!< (@ 0x400860B0) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_13;                   /*!< (@ 0x400860B4) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_14;                   /*!< (@ 0x400860B8) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_15;                   /*!< (@ 0x400860BC) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_16;                   /*!< (@ 0x400860C0) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_17;                   /*!< (@ 0x400860C4) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_18;                   /*!< (@ 0x400860C8) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_19;                   /*!< (@ 0x400860CC) Pin configuration register for pins P1 */
  __IO uint32_t SFSP1_20;                   /*!< (@ 0x400860D0) Pin configuration register for pins P1 */
  __I  uint32_t RESERVED1[11];
  __IO uint32_t SFSP2_0;                    /*!< (@ 0x40086100) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_1;                    /*!< (@ 0x40086104) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_2;                    /*!< (@ 0x40086108) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_3;                    /*!< (@ 0x4008610C) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_4;                    /*!< (@ 0x40086110) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_5;                    /*!< (@ 0x40086114) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_6;                    /*!< (@ 0x40086118) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_7;                    /*!< (@ 0x4008611C) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_8;                    /*!< (@ 0x40086120) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_9;                    /*!< (@ 0x40086124) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_10;                   /*!< (@ 0x40086128) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_11;                   /*!< (@ 0x4008612C) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_12;                   /*!< (@ 0x40086130) Pin configuration register for pins P2 */
  __IO uint32_t SFSP2_13;                   /*!< (@ 0x40086134) Pin configuration register for pins P2 */
  __I  uint32_t RESERVED2[18];
  __IO uint32_t SFSP3_0;                  	/*!< (@ 0x40086180) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_1;                  	/*!< (@ 0x40086184) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_2;                  	/*!< (@ 0x40086188) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_3;                  	/*!< (@ 0x4008618C) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_4;                  	/*!< (@ 0x40086190) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_5;                  	/*!< (@ 0x40086194) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_6;                  	/*!< (@ 0x40086198) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_7;                  	/*!< (@ 0x4008619C) Pin configuration register for pins P3 */
  __IO uint32_t SFSP3_8;                  	/*!< (@ 0x400861A0) Pin configuration register for pins P3 */
  __I  uint32_t RESERVED3[23];
  __IO uint32_t SFSP4_0;                    /*!< (@ 0x40086200) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_1;                    /*!< (@ 0x40086204) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_2;                    /*!< (@ 0x40086208) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_3;                    /*!< (@ 0x4008620C) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_4;                    /*!< (@ 0x40086210) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_5;                    /*!< (@ 0x40086214) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_6;                    /*!< (@ 0x40086218) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_7;                    /*!< (@ 0x4008621C) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_8;                    /*!< (@ 0x40086220) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_9;                    /*!< (@ 0x40086224) Pin configuration register for pins P4 */
  __IO uint32_t SFSP4_10;                   /*!< (@ 0x40086228) Pin configuration register for pins P4 */
  __I  uint32_t RESERVED4[21];
  __IO uint32_t SFSP5_0;                  	/*!< (@ 0x40086280) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_1;                  	/*!< (@ 0x40086284) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_2;                  	/*!< (@ 0x40086288) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_3;                  	/*!< (@ 0x4008628C) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_4;                  	/*!< (@ 0x40086290) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_5;                  	/*!< (@ 0x40086294) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_6;                  	/*!< (@ 0x40086298) Pin configuration register for pins P5 */
  __IO uint32_t SFSP5_7;                  	/*!< (@ 0x4008629C) Pin configuration register for pins P5 */
  __I  uint32_t RESERVED5[24];
  __IO uint32_t SFSP6_0;                    /*!< (@ 0x40086300) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_1;                    /*!< (@ 0x40086304) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_2;                    /*!< (@ 0x40086308) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_3;                    /*!< (@ 0x4008630C) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_4;                    /*!< (@ 0x40086310) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_5;                    /*!< (@ 0x40086314) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_6;                    /*!< (@ 0x40086318) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_7;                    /*!< (@ 0x4008631C) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_8;                    /*!< (@ 0x40086320) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_9;                    /*!< (@ 0x40086324) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_10;                   /*!< (@ 0x40086328) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_11;                   /*!< (@ 0x4008632C) Pin configuration register for pins P6 */
  __IO uint32_t SFSP6_12;                   /*!< (@ 0x40086330) Pin configuration register for pins P6 */
  __I  uint32_t RESERVED6[19];
  __IO uint32_t SFSP7_0;                  	/*!< (@ 0x40086380) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_1;                  	/*!< (@ 0x40086384) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_2;                  	/*!< (@ 0x40086388) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_3;                  	/*!< (@ 0x4008638C) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_4;                  	/*!< (@ 0x40086390) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_5;                  	/*!< (@ 0x40086394) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_6;                  	/*!< (@ 0x40086398) Pin configuration register for pins P7 */
  __IO uint32_t SFSP7_7;                  	/*!< (@ 0x4008639C) Pin configuration register for pins P7 */
  __I  uint32_t RESERVED7[24];
  __IO uint32_t SFSP8_0;                  	/*!< (@ 0x40086400) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_1;                  	/*!< (@ 0x40086404) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_2;                  	/*!< (@ 0x40086408) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_3;                  	/*!< (@ 0x4008640C) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_4;                  	/*!< (@ 0x40086410) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_5;                  	/*!< (@ 0x40086414) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_6;                  	/*!< (@ 0x40086418) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_7;                  	/*!< (@ 0x4008641C) Pin configuration register for pins P8 */
  __IO uint32_t SFSP8_8;                  	/*!< (@ 0x40086420) Pin configuration register for pins P8 */
  __I  uint32_t RESERVED8[23];
  __IO uint32_t SFSP9_0;                  	/*!< (@ 0x40086480) Pin configuration register for pins P9 */
  __IO uint32_t SFSP9_1;                  	/*!< (@ 0x40086484) Pin configuration register for pins P9 */
  __IO uint32_t SFSP9_2;                  	/*!< (@ 0x40086488) Pin configuration register for pins P9 */
  __IO uint32_t SFSP9_3;                  	/*!< (@ 0x4008648C) Pin configuration register for pins P9 */
  __IO uint32_t SFSP9_4;                  	/*!< (@ 0x40086490) Pin configuration register for pins P9 */
  __IO uint32_t SFSP9_5;                  	/*!< (@ 0x40086494) Pin configuration register for pins P9 */
  __IO uint32_t SFSP9_6;                  	/*!< (@ 0x40086498) Pin configuration register for pins P9 */
  __I  uint32_t RESERVED9[25];
  __IO uint32_t SFSPA_0;                  	/*!< (@ 0x40086500) Pin configuration register for pins PA */
  __IO uint32_t SFSPA_1;                  	/*!< (@ 0x40086504) Pin configuration register for pins PA */
  __IO uint32_t SFSPA_2;                  	/*!< (@ 0x40086508) Pin configuration register for pins PA */
  __IO uint32_t SFSPA_3;                  	/*!< (@ 0x4008650C) Pin configuration register for pins PA */
  __IO uint32_t SFSPA_4;                  	/*!< (@ 0x40086510) Pin configuration register for pins PA */
  __I  uint32_t RESERVED10[27];
  __IO uint32_t SFSPB_0;                  	/*!< (@ 0x40086580) Pin configuration register for pins PB */
  __IO uint32_t SFSPB_1;                  	/*!< (@ 0x40086584) Pin configuration register for pins PB */
  __IO uint32_t SFSPB_2;                  	/*!< (@ 0x40086588) Pin configuration register for pins PB */
  __IO uint32_t SFSPB_3;                  	/*!< (@ 0x4008658C) Pin configuration register for pins PB */
  __IO uint32_t SFSPB_4;                  	/*!< (@ 0x40086590) Pin configuration register for pins PB */
  __IO uint32_t SFSPB_5;                  	/*!< (@ 0x40086594) Pin configuration register for pins PB */
  __IO uint32_t SFSPB_6;                  	/*!< (@ 0x40086598) Pin configuration register for pins PB */
  __I  uint32_t RESERVED11[25];
  __IO uint32_t SFSPC_0;                    /*!< (@ 0x40086600) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_1;                    /*!< (@ 0x40086604) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_2;                    /*!< (@ 0x40086608) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_3;                    /*!< (@ 0x4008660C) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_4;                    /*!< (@ 0x40086610) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_5;                    /*!< (@ 0x40086614) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_6;                    /*!< (@ 0x40086618) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_7;                    /*!< (@ 0x4008661C) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_8;                    /*!< (@ 0x40086620) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_9;                    /*!< (@ 0x40086624) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_10;                   /*!< (@ 0x40086628) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_11;                   /*!< (@ 0x4008662C) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_12;                   /*!< (@ 0x40086630) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_13;                   /*!< (@ 0x40086634) Pin configuration register for pins PC */
  __IO uint32_t SFSPC_14;                   /*!< (@ 0x40086638) Pin configuration register for pins PC */
  __I  uint32_t RESERVED12[17];
  __IO uint32_t SFSPD_0;                    /*!< (@ 0x40086680) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_1;                    /*!< (@ 0x40086684) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_2;                    /*!< (@ 0x40086688) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_3;                    /*!< (@ 0x4008668C) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_4;                    /*!< (@ 0x40086690) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_5;                    /*!< (@ 0x40086694) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_6;                    /*!< (@ 0x40086698) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_7;                    /*!< (@ 0x4008669C) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_8;                    /*!< (@ 0x400866A0) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_9;                    /*!< (@ 0x400866A4) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_10;                   /*!< (@ 0x400866A8) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_11;                   /*!< (@ 0x400866AC) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_12;                   /*!< (@ 0x400866B0) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_13;                   /*!< (@ 0x400866B4) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_14;                   /*!< (@ 0x400866B8) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_15;                   /*!< (@ 0x400866BC) Pin configuration register for pins PD */
  __IO uint32_t SFSPD_16;                   /*!< (@ 0x400866C0) Pin configuration register for pins PD */
  __I  uint32_t RESERVED13[15];
  __IO uint32_t SFSPE_0;                    /*!< (@ 0x40086700) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_1;                    /*!< (@ 0x40086704) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_2;                    /*!< (@ 0x40086708) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_3;                    /*!< (@ 0x4008670C) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_4;                    /*!< (@ 0x40086710) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_5;                    /*!< (@ 0x40086714) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_6;                    /*!< (@ 0x40086718) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_7;                    /*!< (@ 0x4008671C) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_8;                    /*!< (@ 0x40086720) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_9;                    /*!< (@ 0x40086724) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_10;                   /*!< (@ 0x40086728) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_11;                   /*!< (@ 0x4008672C) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_12;                   /*!< (@ 0x40086730) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_13;                   /*!< (@ 0x40086734) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_14;                   /*!< (@ 0x40086738) Pin configuration register for pins PE */
  __IO uint32_t SFSPE_15;                   /*!< (@ 0x4008673C) Pin configuration register for pins PE */
  __I  uint32_t RESERVED14[16];
  __IO uint32_t SFSPF_0;                    /*!< (@ 0x40086780) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_1;                    /*!< (@ 0x40086784) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_2;                    /*!< (@ 0x40086788) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_3;                    /*!< (@ 0x4008678C) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_4;                    /*!< (@ 0x40086790) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_5;                    /*!< (@ 0x40086794) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_6;                    /*!< (@ 0x40086798) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_7;                    /*!< (@ 0x4008679C) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_8;                    /*!< (@ 0x400867A0) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_9;                    /*!< (@ 0x400867A4) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_10;                   /*!< (@ 0x400867A8) Pin configuration register for pins PF */
  __IO uint32_t SFSPF_11;                   /*!< (@ 0x400867AC) Pin configuration register for pins PF */
  __I  uint32_t RESERVED15[276];
  __IO uint32_t SFSCLK_0;                   /*!< (@ 0x40086C00) Pin configuration register for pin CLK0 */
  __IO uint32_t SFSCLK_1;                   /*!< (@ 0x40086C04) Pin configuration register for pin CLK1 */
  __IO uint32_t SFSCLK_2;                   /*!< (@ 0x40086C08) Pin configuration register for pin CLK2 */
  __IO uint32_t SFSCLK_3;                   /*!< (@ 0x40086C0C) Pin configuration register for pin CLK3 */
  __I  uint32_t RESERVED16[28];
  __IO uint32_t SFSUSB;                     /*!< (@ 0x40086C80) Pin configuration register for */
  __IO uint32_t SFSI2C0;                    /*!< (@ 0x40086C84) Pin configuration register for I 2C0-bus pins */
  __IO uint32_t ENAIO0;                     /*!< (@ 0x40086C88) ADC0 function select register */
  __IO uint32_t ENAIO1;                     /*!< (@ 0x40086C8C) ADC1 function select register */
  __IO uint32_t ENAIO2;                     /*!< (@ 0x40086C90) Analog function select register */
  __I  uint32_t RESERVED17[27];
  __IO uint32_t EMCCLKDELAY;                /*!< (@ 0x40086D00) EMC clock delay register */
  __IO uint32_t EMCCTRLDELAY;               /*!< (@ 0x40086D04) EMC control delay register */
  __IO uint32_t EMCCSDELAY;                 /*!< (@ 0x40086D08) EMC chip select delay register */
  __IO uint32_t EMCDOUTDELAY;               /*!< (@ 0x40086D0C) EMC data out delay register */
  __IO uint32_t EMCFBCLKDELAY;              /*!< (@ 0x40086D10) EMC FBCLK delay register */
  __IO uint32_t EMCADDRDELAY0;              /*!< (@ 0x40086D14) EMC address line delay register 0 */
  __IO uint32_t EMCADDRDELAY1;              /*!< (@ 0x40086D18) EMC address line delay register 1 */
  __IO uint32_t EMCADDRDELAY2;              /*!< (@ 0x40086D1C) EMC address line delay register 2 */
  __I  uint32_t RESERVED18;
  __IO uint32_t EMCDINDELAY;                /*!< (@ 0x40086D24) EMC data delay register */
  __I  uint32_t RESERVED19[54];
  __IO uint32_t PINTSEL0;                   /*!< (@ 0x40086E00) Pin interrupt select register for pin interrupts 0 to 3. */
  __IO uint32_t PINTSEL1;                   /*!< (@ 0x40086E04) Pin interrupt select register for pin interrupts 4 to 7. */
} LPC_SCU_Type;

// ------------------------------------------------------------------------------------------------
// -----                                         MCPWM                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Motor Control PWM (MOTOCONPWM) Modification date=1/14/2011 Major revision=0 Minor revision=7  (MCPWM)
  */

typedef struct {                            /*!< (@ 0x400A0000) MCPWM Structure        */
  __I  uint32_t CON;                        /*!< (@ 0x400A0000) PWM Control read address */
  __O  uint32_t CON_SET;                    /*!< (@ 0x400A0004) PWM Control set address */
  __O  uint32_t CON_CLR;                    /*!< (@ 0x400A0008) PWM Control clear address */
  __I  uint32_t CAPCON;                     /*!< (@ 0x400A000C) Capture Control read address */
  __O  uint32_t CAPCON_SET;                 /*!< (@ 0x400A0010) Capture Control set address */
  __O  uint32_t CAPCON_CLR;                 /*!< (@ 0x400A0014) Event Control clear address */
  __IO uint32_t TC[3];                      /*!< (@ 0x400A0018) Timer Counter register */
  __IO uint32_t LIM[3];                     /*!< (@ 0x400A0024) Limit register         */
  __IO uint32_t MAT[3];                     /*!< (@ 0x400A0030) Match register         */
  __IO uint32_t DT;                         /*!< (@ 0x400A003C) Dead time register     */
  __IO uint32_t CCP;                        /*!< (@ 0x400A0040) Communication Pattern register */
  __I  uint32_t CAP[3];                     /*!< (@ 0x400A0044) Capture register       */
  __I  uint32_t INTEN;                      /*!< (@ 0x400A0050) Interrupt Enable read address */
  __O  uint32_t INTEN_SET;                  /*!< (@ 0x400A0054) Interrupt Enable set address */
  __O  uint32_t INTEN_CLR;                  /*!< (@ 0x400A0058) Interrupt Enable clear address */
  __I  uint32_t CNTCON;                     /*!< (@ 0x400A005C) Count Control read address */
  __O  uint32_t CNTCON_SET;                 /*!< (@ 0x400A0060) Count Control set address */
  __O  uint32_t CNTCON_CLR;                 /*!< (@ 0x400A0064) Count Control clear address */
  __I  uint32_t INTF;                       /*!< (@ 0x400A0068) Interrupt flags read address */
  __O  uint32_t INTF_SET;                   /*!< (@ 0x400A006C) Interrupt flags set address */
  __O  uint32_t INTF_CLR;                   /*!< (@ 0x400A0070) Interrupt flags clear address */
  __O  uint32_t CAP_CLR;                    /*!< (@ 0x400A0074) Capture clear address  */
} LPC_MCPWM_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         I2Cn                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx I2C0/1-bus interface Modification date=1/14/2011 Major revision=0 Minor revision=7  (I2Cn)
  */

typedef struct {                            /*!< (@ 0x400xx000) I2C0 Structure         */
  __IO uint32_t CONSET;                     /*!< (@ 0x400xx000) I2C Control Set Register. When a one is written to a bit of this register, the corresponding bit in the I2C control register is set. Writing a zero has no effect on the corresponding bit in the I2C control register. */
  __I  uint32_t STAT;                       /*!< (@ 0x400xx004) I2C Status Register. During I2C operation, this register provides detailed status codes that allow software to determine the next action needed. */
  __IO uint32_t DAT;                        /*!< (@ 0x400xx008) I2C Data Register. During master or slave transmit mode, data to be transmitted is written to this register. During master or slave receive mode, data that has been received may be read from this register. */
  __IO uint32_t ADR0;                       /*!< (@ 0x400xx00C) I2C Slave Address Register 0. Contains the 7-bit slave address for operation of the I2C interface in slave mode, and is not used in master mode. The least significant bit determines whether a slave responds to the General Call address. */
  __IO uint32_t SCLH;                       /*!< (@ 0x400xx010) SCH Duty Cycle Register High Half Word. Determines the high time of the I2C clock. */
  __IO uint32_t SCLL;                       /*!< (@ 0x400xx014) SCL Duty Cycle Register Low Half Word. Determines the low time of the I2C clock. SCLL and SCLH together determine the clock frequency generated by an I2C master and certain times used in slave mode. */
  __O  uint32_t CONCLR;                     /*!< (@ 0x400xx018) I2C Control Clear Register. When a one is written to a bit of this register, the corresponding bit in the I2C control register is cleared. Writing a zero has no effect on the corresponding bit in the I2C control register. */
  __IO uint32_t MMCTRL;                     /*!< (@ 0x400xx01C) Monitor mode control register. */
  __IO uint32_t ADR1;                       /*!< (@ 0x400xx020) I2C Slave Address Register. Contains the 7-bit slave address for operation of the I2C interface in slave mode, and is not used in master mode. The least significant bit determines whether a slave responds to the General Call address. */
  __IO uint32_t ADR2;                       /*!< (@ 0x400xx024) I2C Slave Address Register. Contains the 7-bit slave address for operation of the I2C interface in slave mode, and is not used in master mode. The least significant bit determines whether a slave responds to the General Call address. */
  __IO uint32_t ADR3;                       /*!< (@ 0x400xx028) I2C Slave Address Register. Contains the 7-bit slave address for operation of the I2C interface in slave mode, and is not used in master mode. The least significant bit determines whether a slave responds to the General Call address. */
  __I  uint32_t DATA_BUFFER;                /*!< (@ 0x400xx02C) Data buffer register. The contents of the 8 MSBs of the DAT shift register will be transferred to the DATA_BUFFER automatically after every nine bits (8 bits of data plus ACK or NACK) has been received on the bus. */
  __IO uint32_t MASK[4];                    /*!< (@ 0x400xx030) I2C Slave address mask register */
} LPC_I2Cn_Type;

// ------------------------------------------------------------------------------------------------
// -----                                         I2Sn                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx I2S interface Modification date=1/14/2011 Major revision=0 Minor revision=7  (I2Sn)
    0x400A2000 / 0x400A3000
  */

typedef struct {                            /*!< (@ 0x400Ax000) I2S Structure         */
  __IO uint32_t DAO;                        /*!< (@ 0x400Ax000) I2S Digital Audio Output Register. Contains control bits for the I2S transmit channel. */
  __IO uint32_t DAI;                        /*!< (@ 0x400Ax004) I2S Digital Audio Input Register. Contains control bits for the I2S receive channel. */
  __O  uint32_t TXFIFO;                     /*!< (@ 0x400Ax008) I2S Transmit FIFO. Access register for the 8 x 32-bit transmitter FIFO. */
  __I  uint32_t RXFIFO;                     /*!< (@ 0x400Ax00C) I2S Receive FIFO. Access register for the 8 x 32-bit receiver FIFO. */
  __I  uint32_t STATE;                      /*!< (@ 0x400Ax010) I2S Status Feedback Register. Contains status information about the I2S interface. */
  __IO uint32_t DMA1;                       /*!< (@ 0x400Ax014) I2S DMA Configuration Register 1. Contains control information for DMA request 1. */
  __IO uint32_t DMA2;                       /*!< (@ 0x400Ax018) I2S DMA Configuration Register 2. Contains control information for DMA request 2. */
  __IO uint32_t IRQ;                        /*!< (@ 0x400Ax01C) I2S Interrupt Request Control Register. Contains bits that control how the I2S interrupt request is generated. */
  __IO uint32_t TXRATE;                     /*!< (@ 0x400Ax020) I2S Transmit MCLK divider. This register determines the I2S TX MCLK rate by specifying the value to divide PCLK by in order to produce MCLK. */
  __IO uint32_t RXRATE;                     /*!< (@ 0x400Ax024) I2S Receive MCLK divider. This register determines the I2S RX MCLK rate by specifying the value to divide PCLK by in order to produce MCLK. */
  __IO uint32_t TXBITRATE;                  /*!< (@ 0x400Ax028) I2S Transmit bit rate divider. This register determines the I2S transmit bit rate by specifying the value to divide TX_MCLK by in order to produce the transmit bit clock. */
  __IO uint32_t RXBITRATE;                  /*!< (@ 0x400Ax02C) I2S Receive bit rate divider. This register determines the I2S receive bit rate by specifying the value to divide RX_MCLK by in order to produce the receive bit clock. */
  __IO uint32_t TXMODE;                     /*!< (@ 0x400Ax030) I2S Transmit mode control. */
  __IO uint32_t RXMODE;                     /*!< (@ 0x400Ax034) I2S Receive mode control. */
} LPC_I2Sn_Type;


// ------------------------------------------------------------------------------------------------
// -----                                        RITIMER                                       -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Repetitive Interrupt Timer (RIT) Modification date=1/14/2011 Major revision=0 Minor revision=7  (RITIMER)
  */

typedef struct {                            /*!< (@ 0x400C0000) RITIMER Structure      */
  __IO uint32_t COMPVAL;                    /*!< (@ 0x400C0000) Compare register       */
  __IO uint32_t MASK;                       /*!< (@ 0x400C0004) Mask register. This register holds the 32-bit mask value. A 1 written to any bit will force a compare on the corresponding bit of the counter and compare register. */
  __IO uint32_t CTRL;                       /*!< (@ 0x400C0008) Control register.      */
  __IO uint32_t COUNTER;                    /*!< (@ 0x400C000C) 32-bit counter         */
} LPC_RITIMER_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          QEI                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx Quadrature Encoder Interface (QEI) Modification date=1/18/2011 Major revision=0 Minor revision=7  (QEI)
  */

typedef struct {                            /*!< (@ 0x400C6000) QEI Structure          */
  __O  uint32_t CON;                        /*!< (@ 0x400C6000) Control register       */
  __I  uint32_t STAT;                       /*!< (@ 0x400C6004) Encoder status register */
  __IO uint32_t CONF;                       /*!< (@ 0x400C6008) Configuration register */
  __I  uint32_t POS;                        /*!< (@ 0x400C600C) Position register      */
  __IO uint32_t MAXPOS;                     /*!< (@ 0x400C6010) Maximum position register */
  __IO uint32_t CMPOS0;                     /*!< (@ 0x400C6014) position compare register 0 */
  __IO uint32_t CMPOS1;                     /*!< (@ 0x400C6018) position compare register 1 */
  __IO uint32_t CMPOS2;                     /*!< (@ 0x400C601C) position compare register 2 */
  __I  uint32_t INXCNT;                     /*!< (@ 0x400C6020) Index count register   */
  __IO uint32_t INXCMP0;                    /*!< (@ 0x400C6024) Index compare register 0 */
  __IO uint32_t LOAD;                       /*!< (@ 0x400C6028) Velocity timer reload register */
  __I  uint32_t TIME;                       /*!< (@ 0x400C602C) Velocity timer register */
  __I  uint32_t VEL;                        /*!< (@ 0x400C6030) Velocity counter register */
  __I  uint32_t CAP;                        /*!< (@ 0x400C6034) Velocity capture register */
  __IO uint32_t VELCOMP;                    /*!< (@ 0x400C6038) Velocity compare register */
  __IO uint32_t FILTERPHA;                  /*!< (@ 0x400C603C) Digital filter register on input phase A (QEI_A) */
  __IO uint32_t FILTERPHB;                  /*!< (@ 0x400C6040) Digital filter register on input phase B (QEI_B) */
  __IO uint32_t FILTERINX;                  /*!< (@ 0x400C6044) Digital filter register on input index (QEI_IDX) */
  __IO uint32_t WINDOW;                     /*!< (@ 0x400C6048) Index acceptance window register */
  __IO uint32_t INXCMP1;                    /*!< (@ 0x400C604C) Index compare register 1 */
  __IO uint32_t INXCMP2;                    /*!< (@ 0x400C6050) Index compare register 2 */
  __I  uint32_t RESERVED0[993];
  __O  uint32_t IEC;                        /*!< (@ 0x400C6FD8) Interrupt enable clear register */
  __O  uint32_t IES;                        /*!< (@ 0x400C6FDC) Interrupt enable set register */
  __I  uint32_t INTSTAT;                    /*!< (@ 0x400C6FE0) Interrupt status register */
  __I  uint32_t IE;                         /*!< (@ 0x400C6FE4) Interrupt enable register */
  __O  uint32_t CLR;                        /*!< (@ 0x400C6FE8) Interrupt status clear register */
  __O  uint32_t SET;                        /*!< (@ 0x400C6FEC) Interrupt status set register */
} LPC_QEI_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         GIMA                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=Falcon Chapter title=Global Input Multiplexer Array (GIMA) Modification date=3/25/2011 Major revision=0 Minor revision=4  (GIMA)
  */

typedef struct {                            /*!< (@ 0x400C7000) GIMA Structure         */
  __IO uint32_t CAP0_0_IN;                  /*!< (@ 0x400C7000) Timer 0 CAP0_0 capture input multiplexer */
  __IO uint32_t CAP0_1_IN;                  /*!< (@ 0x400C7004) Timer 0 CAP0_1 capture input multiplexer */
  __IO uint32_t CAP0_2_IN;                  /*!< (@ 0x400C7008) Timer 0 CAP0_2 capture input multiplexer */
  __IO uint32_t CAP0_3_IN;                  /*!< (@ 0x400C700C) Timer 0 CAP0_3 capture input multiplexer */
  __IO uint32_t CAP1_0_IN;                  /*!< (@ 0x400C7010) Timer 1 CAP1_0 capture input multiplexer */
  __IO uint32_t CAP1_1_IN;                  /*!< (@ 0x400C7014) Timer 1 CAP1_1 capture input multiplexer */
  __IO uint32_t CAP1_2_IN;                  /*!< (@ 0x400C7018) Timer 1 CAP1_2 capture input multiplexer */
  __IO uint32_t CAP1_3_IN;                  /*!< (@ 0x400C701C) Timer 1 CAP1_3 capture input multiplexer */
  __IO uint32_t CAP2_0_IN;                  /*!< (@ 0x400C7020) Timer 2 CAP2_0 capture input multiplexer */
  __IO uint32_t CAP2_1_IN;                  /*!< (@ 0x400C7024) Timer 2 CAP2_1 capture input multiplexer */
  __IO uint32_t CAP2_2_IN;                  /*!< (@ 0x400C7028) Timer 2 CAP2_2 capture input multiplexer */
  __IO uint32_t CAP2_3_IN;                  /*!< (@ 0x400C702C) Timer 2 CAP2_3 capture input multiplexer */
  __IO uint32_t CAP3_0_IN;                  /*!< (@ 0x400C7030) Timer 3 CAP3_0 capture input multiplexer */
  __IO uint32_t CAP3_1_IN;                  /*!< (@ 0x400C7034) Timer 3 CAP3_1 capture input multiplexer */
  __IO uint32_t CAP3_2_IN;                  /*!< (@ 0x400C7038) Timer 3 CAP3_2 capture input multiplexer */
  __IO uint32_t CAP3_3_IN;                  /*!< (@ 0x400C703C) Timer 3 CAP3_3 capture input multiplexer */
  __IO uint32_t CTIN_0_IN;                  /*!< (@ 0x400C7040) SCT CTIN_0 capture input multiplexer */
  __IO uint32_t CTIN_1_IN;                  /*!< (@ 0x400C7044) SCT CTIN_1 capture input multiplexer */
  __IO uint32_t CTIN_2_IN;                  /*!< (@ 0x400C7048) SCT CTIN_2 capture input multiplexer */
  __IO uint32_t CTIN_3_IN;                  /*!< (@ 0x400C704C) SCT CTIN_3 capture input multiplexer */
  __IO uint32_t CTIN_4_IN;                  /*!< (@ 0x400C7050) SCT CTIN_4 capture input multiplexer */
  __IO uint32_t CTIN_5_IN;                  /*!< (@ 0x400C7054) SCT CTIN_5 capture input multiplexer */
  __IO uint32_t CTIN_6_IN;                  /*!< (@ 0x400C7058) SCT CTIN_6 capture input multiplexer */
  __IO uint32_t CTIN_7_IN;                  /*!< (@ 0x400C705C) SCT CTIN_7 capture input multiplexer */
  __IO uint32_t VADC_TRIGGER_IN;            /*!< (@ 0x400C7060) ADC trigger input multiplexer */
  __IO uint32_t EVENTROUTER_13_IN;          /*!< (@ 0x400C7064) Event router input 13 multiplexer */
  __IO uint32_t EVENTROUTER_14_IN;          /*!< (@ 0x400C7068) Event router input 14 multiplexer */
  __IO uint32_t EVENTROUTER_16_IN;          /*!< (@ 0x400C706C) Event router input 16 multiplexer */
  __IO uint32_t ADCSTART0_IN;               /*!< (@ 0x400C7070) ADC start0 input multiplexer */
  __IO uint32_t ADCSTART1_IN;               /*!< (@ 0x400C7074) ADC start1 input multiplexer */
} LPC_GIMA_Type;


// ------------------------------------------------------------------------------------------------
// -----                                          DAC                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx DAC Modification date=1/18/2011 Major revision=0 Minor revision=7  (DAC)
  */

typedef struct {                            /*!< (@ 0x400E1000) DAC Structure          */
  __IO uint32_t CR;                         /*!< (@ 0x400E1000) DAC register. Holds the conversion data. */
  __IO uint32_t CTRL;                       /*!< (@ 0x400E1004) DAC control register.  */
  __IO uint32_t CNTVAL;                     /*!< (@ 0x400E1008) DAC counter value register. */
} LPC_DAC_Type;


// ------------------------------------------------------------------------------------------------
// -----                                        C_CANn                                        -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx C_CAN Modification date=1/18/2011 Major revision=0 Minor revision=7  (C_CANn)
    0x400A4000 / 0x400E2000
  */

typedef struct {                            /*!< (@ 0x400E2000) C_CAN Structure       */
  __IO uint32_t CNTL;                       /*!< (@ 0x400E2000) CAN control            */
  __IO uint32_t STAT;                       /*!< (@ 0x400E2004) Status register        */
  __I  uint32_t EC;                         /*!< (@ 0x400E2008) Error counter          */
  __IO uint32_t BT;                         /*!< (@ 0x400E200C) Bit timing register    */
  __I  uint32_t INT;                        /*!< (@ 0x400E2010) Interrupt register     */
  __IO uint32_t TEST;                       /*!< (@ 0x400E2014) Test register          */
  __IO uint32_t BRPE;                       /*!< (@ 0x400E2018) Baud rate prescaler extension register */
  __I  uint32_t RESERVED0;
  __IO uint32_t IF1_CMDREQ;                 /*!< (@ 0x400E2020) Message interface command request  */
  
  union {
    __IO uint32_t IF1_CMDMSK_R;             /*!< (@ 0x400E2024) Message interface command mask (read direction) */
    __IO uint32_t IF1_CMDMSK_W;             /*!< (@ 0x400E2024) Message interface command mask (write direction) */
  };
  __IO uint32_t IF1_MSK1;                   /*!< (@ 0x400E2028) Message interface mask 1 */
  __IO uint32_t IF1_MSK2;                   /*!< (@ 0x400E202C) Message interface 1 mask 2 */
  __IO uint32_t IF1_ARB1;                   /*!< (@ 0x400E2030) Message interface 1 arbitration 1 */
  __IO uint32_t IF1_ARB2;                   /*!< (@ 0x400E2034) Message interface 1 arbitration 2 */
  __IO uint32_t IF1_MCTRL;                  /*!< (@ 0x400E2038) Message interface 1 message control */
  __IO uint32_t IF1_DA1;                    /*!< (@ 0x400E203C) Message interface data A1 */
  __IO uint32_t IF1_DA2;                    /*!< (@ 0x400E2040) Message interface 1 data A2 */
  __IO uint32_t IF1_DB1;                    /*!< (@ 0x400E2044) Message interface 1 data B1 */
  __IO uint32_t IF1_DB2;                    /*!< (@ 0x400E2048) Message interface 1 data B2 */
  __I  uint32_t RESERVED1[13];
  __IO uint32_t IF2_CMDREQ;                 /*!< (@ 0x400E2080) Message interface command request  */

  union {
    __IO uint32_t IF2_CMDMSK_R;             /*!< (@ 0x400E2084) Message interface command mask (read direction) */
    __IO uint32_t IF2_CMDMSK_W;             /*!< (@ 0x400E2084) Message interface command mask (write direction) */
  };
  __IO uint32_t IF2_MSK1;                   /*!< (@ 0x400E2088) Message interface mask 1 */
  __IO uint32_t IF2_MSK2;                   /*!< (@ 0x400E208C) Message interface 1 mask 2 */
  __IO uint32_t IF2_ARB1;                   /*!< (@ 0x400E2090) Message interface 1 arbitration 1 */
  __IO uint32_t IF2_ARB2;                   /*!< (@ 0x400E2094) Message interface 1 arbitration 2 */
  __IO uint32_t IF2_MCTRL;                  /*!< (@ 0x400E2098) Message interface 1 message control */
  __IO uint32_t IF2_DA1;                    /*!< (@ 0x400E209C) Message interface data A1 */
  __IO uint32_t IF2_DA2;                    /*!< (@ 0x400E20A0) Message interface 1 data A2 */
  __IO uint32_t IF2_DB1;                    /*!< (@ 0x400E20A4) Message interface 1 data B1 */
  __IO uint32_t IF2_DB2;                    /*!< (@ 0x400E20A8) Message interface 1 data B2 */
  __I  uint32_t RESERVED6[21];
  __I  uint32_t TXREQ1;                     /*!< (@ 0x400E2100) Transmission request 1 */
  __I  uint32_t TXREQ2;                     /*!< (@ 0x400E2104) Transmission request 2 */
  __I  uint32_t RESERVED2[6];
  __I  uint32_t ND1;                        /*!< (@ 0x400E2120) New data 1             */
  __I  uint32_t ND2;                        /*!< (@ 0x400E2124) New data 2             */
  __I  uint32_t RESERVED3[6];
  __I  uint32_t IR1;                        /*!< (@ 0x400E2140) Interrupt pending 1    */
  __I  uint32_t IR2;                        /*!< (@ 0x400E2144) Interrupt pending 2    */
  __I  uint32_t RESERVED4[6];
  __I  uint32_t MSGV1;                      /*!< (@ 0x400E2160) Message valid 1        */
  __I  uint32_t MSGV2;                      /*!< (@ 0x400E2164) Message valid 2        */
  __I  uint32_t RESERVED5[6];
  __IO uint32_t CLKDIV;                     /*!< (@ 0x400E2180) CAN clock divider register */
} LPC_C_CANn_Type;


// ------------------------------------------------------------------------------------------------
// -----                                         ADCn                                         -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief Product name title=UM10430 Chapter title=LPC43xx 10-bit ADC0/1 Modification date=1/18/2011 Major revision=0 Minor revision=7  (ADCn)
    0x400E3000 / 0x400E4000
  */

typedef struct {                            /*!< (@ 0x400Ex000) ADCn Structure         */
  __IO uint32_t CR;                         /*!< (@ 0x400Ex000) A/D Control Register. The AD0CR register must be written to select the operating mode before A/D conversion can occur. */
  __I  uint32_t GDR;                        /*!< (@ 0x400Ex004) A/D Global Data Register. Contains the result of the most recent A/D conversion. */
  __I  uint32_t RESERVED0;
  __IO uint32_t INTEN;                      /*!< (@ 0x400Ex00C) A/D Interrupt Enable Register. This register contains enable bits that allow the DONE flag of each A/D channel to be included or excluded from contributing to the generation of an A/D interrupt. */
  __I  uint32_t DR[8];                      /*!< (@ 0x400Ex010) A/D Channel Data Register. This register contains the result of the most recent conversion completed on channel n. */
  __I  uint32_t STAT;                       /*!< (@ 0x400Ex030) A/D Status Register. This register contains DONE and OVERRUN flags for all of the A/D channels, as well as the A/D interrupt flag. */
} LPC_ADCn_Type;



// ------------------------------------------------------------------------------------------------
// -----                                         Video ADC                                    -----
// ------------------------------------------------------------------------------------------------
/**
  * 
    0x400F0000
  */

typedef struct {                            
  __O  uint32_t FLUSH;                      /*!< (@ 0x400F0000) A/D Flush FIFO         */
  __IO uint32_t DMA_REQ;                    /*!< (@ 0x400F0004) A/D DMA request a DMA write to load a descriptor table from memory */
  __I  uint32_t FIFO_STS;                   /*!< (@ 0x400F0008) A/D Full / count / empty status */
  __IO uint32_t FIFO_CFG;                   /*!< (@ 0x400F000C) A/D FIFO configuration - regular or packed samples */
  __O  uint32_t TRIGGER;                    /*!< (@ 0x400F0010) A/D Trigger to initiate timer and descriptor table processing */
  __IO uint32_t DSCR_STS;                   /*!< (@ 0x400F0014) A/D Descriptor processing status register */
  __IO uint32_t POWER_DOWN;                 /*!< (@ 0x400F0018) A/D ADC power down control */
  __IO uint32_t CONFIG;                     /*!< (@ 0x400F001C) A/D ADC configuration register */
  __IO uint32_t THR_A;                      /*!< (@ 0x400F0020) A/D Threshold register A */
  __IO uint32_t THR_B;                      /*!< (@ 0x400F0024) A/D Threshold register B */
  __I  uint32_t LAST_SAMPLE[6];             /*!< (@ 0x400F0028 to 0x400F003C) A/D Last sample registers - sample data and results of window comparator */
  __I  uint32_t RESERVED0[48];				
  __IO uint32_t ADC_DEBUG;                  /*!< (@ 0x400F0100) A/D Debug Register*/
  __IO uint32_t ADC_SPEED;                  /*!< (@ 0x400F0104) A/D Speed setting register */
  __IO uint32_t POWER_CONTROL;              /*!< (@ 0x400F0108) A/D Power control register*/
  __I  uint32_t RESERVED1[61];
  __I  uint32_t FIFO_OUTPUT[16];            /*!< (@ 0x400F0200) A/D FIFO output results */
  __I  uint32_t RESERVED2[48];
  __IO uint32_t DESCRIPTOR_0[8];            /*!< (@ 0x400F0300) A/D Descriptor entries table 0 */
  __IO uint32_t DESCRIPTOR_1[8];            /*!< (@ 0x400F0320) A/D Descriptor entries table 1 */
  __I  uint32_t RESERVED3[752];
  __O  uint32_t CLR_EN0;                    /*!< (@ 0x400F0F00) A/D Interupt 0 bit mask fields Clear enable */
  __O  uint32_t SET_EN0;                    /*!< (@ 0x400F0F04) A/D Interrupt 0 bit mask fields Set enable */
  __I  uint32_t MASK0;                      /*!< (@ 0x400F0F08) A/D Interrupt 0 enable register */
  __I  uint32_t STATUS0;                    /*!< (@ 0x400F0F0C) A/D Interrtpt 0 status register */
  __O  uint32_t CLR_STAT0;                  /*!< (@ 0x400F0F10) A/D Interrupt 0 Clear Status */
  __O  uint32_t SET_STAT0;                  /*!< (@ 0x400F0F14) A/D Interrupt 0 set status */
  __I  uint32_t RESERVED4[2];
  __O  uint32_t CLR_EN1;                    /*!< (@ 0x400F0F20) A/D Interrupt 1 clear mask */
  __O  uint32_t SET_EN1;                    /*!< (@ 0x400F0F24) A/D Interrupt 1 bit mask fields Set enable */
  __I  uint32_t MASK1;                      /*!< (@ 0x400F0F28) A/D Interrupt 1 enable register */
  __I  uint32_t STATUS1;                    /*!< (@ 0x400F0F2C) A/D Interrtpt 1 status register */
  __O  uint32_t CLR_STAT1;                  /*!< (@ 0x400F0F30) A/D Interrupt 1 Clear Status */
  __O  uint32_t SET_STAT1;                  /*!< (@ 0x400F0F34) A/D Interrupt 1 set status */
} LPC_VADC_Type;

// ------------------------------------------------------------------------------------------------
// -----                                       GPIO_PORT                                      -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief GPIO port  (GPIO_PORT)
    Note: it is not a generic gpio but a high speed gpio (hs gpio)!
  */

typedef struct {                            /*!< (@ 0x400F4000) GPIO_PORT Structure    */
  __IO uint8_t B[256];                      /*!< (@ 0x400F4000) Byte pin registers port 0 to 5; pins PIOn_0 to PIOn_31 */
  __I  uint32_t RESERVED0[960];
  __IO uint32_t W[256];                     /*!< (@ 0x400F5000) Word pin registers port 0 to 5 */
  __I  uint32_t RESERVED1[768];
  __IO uint32_t DIR[8];                     /*!< (@ 0x400F6000) Direction registers port n */
  __I  uint32_t RESERVED2[24];
  __IO uint32_t MASK[8];                    /*!< (@ 0x400F6080) Mask register port n   */
  __I  uint32_t RESERVED3[24];
  __IO uint32_t PIN[8];                     /*!< (@ 0x400F6100) Portpin register port n */
  __I  uint32_t RESERVED4[24];
  __IO uint32_t MPIN[8];                    /*!< (@ 0x400F6180) Masked port register port n */
  __I  uint32_t RESERVED5[24];
  __IO uint32_t SET[8];                     /*!< (@ 0x400F6200) Write: Set register for port n Read: output bits for port n */
  __I  uint32_t RESERVED6[24];
  __O  uint32_t CLR[8];                     /*!< (@ 0x400F6280) Clear port n           */
  __I  uint32_t RESERVED7[24];
  __O  uint32_t NOT[8];                     /*!< (@ 0x400F6300) Toggle port n          */
} LPC_GPIO_PORT_Type;

// ------------------------------------------------------------------------------------------------
// -----                                         GPIOn (same as GPIO_PORT, backward compatibility)                                        -----
// ------------------------------------------------------------------------------------------------

// Is a backward compatibility for struct members important: DIR/MASK/PIN/SET/CLR??? NOT is new.

typedef struct {
  __IO  uint32_t RESERVED1[2048];         //reserved for Byte pin (PB) and Word pin (PW) registers
  __IO uint32_t DIR;                       /*!< (@ 0x400F6000) Direction registers port n */
  __IO  uint32_t RESERVED2[31];            //reserved for port 1 ..7 (tricky)
  __IO uint32_t MASK;                      /*!< (@ 0x400F6080) Mask register port n */
  __IO  uint32_t RESERVED3[31];            //reserved for port 1 ..7 (tricky)
  __IO  uint32_t RESERVED4[32];            //Do not use GPIO port register due to non-masking
  __IO uint32_t PIN;                       /*!< (@ 0x400F6180) Masked port register port n */
  __IO  uint32_t RESERVED5[31];            //reserved for port 1 ..7 (tricky)
  __IO uint32_t SET;                       /*!< (@ 0x400F6200) Write: Set register for port n Read: output bits for port n */
  __IO  uint32_t RESERVED6[31];            //reserved for port 1 ..7 (tricky)
  __O  uint32_t CLR;                       /*!< (@ 0x400F6280) Clear port n */
  __IO  uint32_t RESERVED7[31];            //reserved for port 1 ..7 (tricky)
  __O  uint32_t NOT;                       /*!< (@ 0x400F6300) Toggle port n */
  __IO  uint32_t RESERVED8[31];            //reserved for port 1 ..7 (tricky)
  //to be expanded
} LPC_GPIOn_Type;

// ------------------------------------------------------------------------------------------------
// -----                                     GPIO_PIN_INT                                     -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief GPIO pin interrupt (GPIO_PIN_INT)
  */

typedef struct {                            /*!< (@ 0x40087000) GPIO_PIN_INT Structure */
  __IO uint32_t ISEL;                       /*!< (@ 0x40087000) Pin Interrupt Mode register */
  __IO uint32_t IENR;                       /*!< (@ 0x40087004) Pin Interrupt Enable (Rising) register */
  __O  uint32_t SIENR;                      /*!< (@ 0x40087008) Set Pin Interrupt Enable (Rising) register */
  __O  uint32_t CIENR;                      /*!< (@ 0x4008700C) Clear Pin Interrupt Enable (Rising) register */
  __IO uint32_t IENF;                       /*!< (@ 0x40087010) Pin Interrupt Enable Falling Edge / Active Level register */
  __O  uint32_t SIENF;                      /*!< (@ 0x40087014) Set Pin Interrupt Enable Falling Edge / Active Level register */
  __O  uint32_t CIENF;                      /*!< (@ 0x40087018) Clear Pin Interrupt Enable Falling Edge / Active Level address */
  __IO uint32_t RISE;                       /*!< (@ 0x4008701C) Pin Interrupt Rising Edge register */
  __IO uint32_t FALL;                       /*!< (@ 0x40087020) Pin Interrupt Falling Edge register */
  __IO uint32_t IST;                        /*!< (@ 0x40087024) Pin Interrupt Status register */
} LPC_GPIO_PIN_INT_Type;


// ------------------------------------------------------------------------------------------------
// -----                                    GPIO_GROUP_INTn                                   -----
// ------------------------------------------------------------------------------------------------


/**
  * @brief GPIO group interrupt 0/1 (GPIO_GROUP_INTn) 
    0x40088000/0x40089000
  */

typedef struct {                            /*!< (@ 0x4008x000) GPIO_GROUP_INT0 Structure */
  __IO uint32_t CTRL;                       /*!< (@ 0x4008x000) GPIO grouped interrupt control register */
  __I  uint32_t RESERVED0[7];
  __IO uint32_t PORT_POL[8];                /*!< (@ 0x4008x020) GPIO grouped interrupt port polarity register */
  __IO uint32_t PORT_ENA[8];                /*!< (@ 0x4008x040) GPIO grouped interrupt port 0/1 enable register */
} LPC_GPIO_GROUP_INTn_Type;


// ------------------------------------------------------------------------------------------------
// -----                                  Random number generation (RNG)                      -----
// ------------------------------------------------------------------------------------------------

typedef struct
{
  __I	uint32_t RANDOM_NUMBER;     /*!< (@ 0x40054000) Random number */
  __I	uint32_t STATISTIC;         /*!< (@ 0x40054004) Statistic */
  __IO	uint32_t COUNTER_SEL_RNG;   /*!< (@ 0x40054008) Select for statistics */
  __I   uint32_t RESERVED0[(0xFF4-0x008-0x04)/4];
  __IO	uint32_t POWERDOWN;         /*!< (@ 0x40054FF4) Powerdown mode */
} LPC_RNG_Type;


// ------------------------------------------------------------------------------------------------
// -----                                  Serial GPIO (SGPIO)                                 -----
// ------------------------------------------------------------------------------------------------

typedef struct
{
  __IO	uint32_t OUT_MUX_CFG[16];   /*!< (@ 0x40101000) Pin output multiplexer configuration */
  __IO	uint32_t SGPIO_MUX_CFG[16]; /*!< (@ 0x40101040) SGPIO input multiplexer configuration */
  __IO	uint32_t SLICE_MUX_CFG[16]; /*!< (@ 0x40101080) Slice multiplexer configuration */
  __IO	uint32_t REG[16];           /*!< (@ 0x401010C0) Register */
  __IO	uint32_t REG_SS[16];        /*!< (@ 0x40101100) Shadow register */
  __IO	uint32_t PRESET[16];        /*!< (@ 0x40101140) Reload value of  COUNT0, loaded when COUNT0 reaches 0x0 */
  __IO	uint32_t COUNT[16];         /*!< (@ 0x40101180) Down counter, counts down each clock cycle */
  __IO	uint32_t POS[16];           /*!< (@ 0x401011C0) Each time COUNT0 reaches 0x0 POS counts down */
  __IO	uint32_t MASK_A;            /*!< (@ 0x40101200) Mask for pattern match function of slice A */
  __IO	uint32_t MASK_H;            /*!< (@ 0x40101204) Mask for pattern match function of slice H */
  __IO	uint32_t MASK_I;            /*!< (@ 0x40101208) Mask for pattern match function of slice I */
  __IO	uint32_t MASK_P;            /*!< (@ 0x4010120C) Mask for pattern match function of slice P */
  __I	uint32_t GPIO_INREG;        /*!< (@ 0x40101210) GPIO input status register */
  __IO	uint32_t GPIO_OUTREG;       /*!< (@ 0x40101214) GPIO output control register */
  __IO	uint32_t GPIO_OEREG;        /*!< (@ 0x40101218) GPIO OE control register */
  __IO	uint32_t CTRL_ENABLE;       /*!< (@ 0x4010121C) Enables the slice COUNT counter */
  __IO	uint32_t CTRL_DISABLE;      /*!< (@ 0x40101220) Disables the slice COUNT counter */
  __I   uint32_t RESERVED0[(0xF00-0x220-0x04)/4];
  __IO	uint32_t CLR_EN0;           /*!< (@ 0x40101F00) Shift clock interrupt clear mask */
  __IO	uint32_t SET_EN0;           /*!< (@ 0x40101F04) Shift clock interrupt set mask */
  __I	uint32_t ENABLE0;           /*!< (@ 0x40101F08) Shift clock interrupt enable */
  __I	uint32_t STATUS0;           /*!< (@ 0x40101F0C) Shift clock interrupt status */
  __IO	uint32_t CTR_STAT0;         /*!< (@ 0x40101F10) Shift clock interrupt clear status */
  __IO	uint32_t SET_STAT0;         /*!< (@ 0x40101F14) Shift clock interrupt set status */
  __I   uint32_t RESERVED1[2];
  __IO	uint32_t CLR_EN1;           /*!< (@ 0x40101F20) Capture clock interrupt clear mask */
  __IO	uint32_t SET_EN1;           /*!< (@ 0x40101F24) Capture clock interrupt set mask */
  __I	uint32_t ENABLE1;           /*!< (@ 0x40101F28) Capture clock interrupt enable */
  __I	uint32_t STATUS1;           /*!< (@ 0x40101F2C) Capture clock interrupt status */
  __IO	uint32_t CTR_STAT1;         /*!< (@ 0x40101F30) Capture clock interrupt clear status */
  __IO	uint32_t SET_STAT1;         /*!< (@ 0x40101F34) Capture clock interrupt set status */
  __I   uint32_t RESERVED2[2];
  __IO	uint32_t CLR_EN2;           /*!< (@ 0x40101F40) Pattern match interrupt clear mask */
  __IO	uint32_t SET_EN2;           /*!< (@ 0x40101F44) Pattern match interrupt set mask */
  __I	uint32_t ENABLE2;           /*!< (@ 0x40101F48) Pattern match interrupt enable */
  __I	uint32_t STATUS2;           /*!< (@ 0x40101F4C) Pattern match interrupt status */
  __IO	uint32_t CTR_STAT2;         /*!< (@ 0x40101F50) Pattern match interrupt clear status */
  __IO	uint32_t SET_STAT2;         /*!< (@ 0x40101F54) Pattern match interrupt set status */
  __I   uint32_t RESERVED3[2];
  __IO	uint32_t CLR_EN3;           /*!< (@ 0x40101F60) Input interrupt clear mask */
  __IO	uint32_t SET_EN3;           /*!< (@ 0x40101F64) Input bit match interrupt set mask */
  __I	uint32_t ENABLE3;           /*!< (@ 0x40101F68) Input bit match interrupt enable */
  __I	uint32_t STATUS3;           /*!< (@ 0x40101F6C) Input bit match interrupt status */
  __IO	uint32_t CTR_STAT3;         /*!< (@ 0x40101F70) Input bit match interrupt clear status */
  __IO	uint32_t SET_STAT3;         /*!< (@ 0x40101F74) Input bit match interrupt set status */
} LPC_SGPIO_Type;

#if defined ( __CC_ARM   )
  #pragma no_anon_unions
#endif


// ------------------------------------------------------------------------------------------------
// -----                                 Peripheral memory map                                -----
// ------------------------------------------------------------------------------------------------

#define LPC_SCT_BASE              (0x40000000)
#define LPC_GPDMA_BASE            (0x40002000)
#define LPC_SPIFI_BASE            (0x40003000)
#define LPC_SDMMC_BASE            (0x40004000)
#define LPC_EMC_BASE              (0x40005000)
#define LPC_USB0_BASE             (0x40006000)
#define LPC_USB1_BASE             (0x40007000)
#define LPC_LCD_BASE              (0x40008000)
#define LPC_ETHERNET_BASE         (0x40010000)
#define LPC_ATIMER_BASE           (0x40040000)
#define LPC_REGFILE_BASE          (0x40041000)
#define LPC_PMC_BASE              (0x40042000)
#define LPC_CREG_BASE             (0x40043000)
#define LPC_EVENTROUTER_BASE      (0x40044000)
#define LPC_RTC_BASE              (0x40046000)
#define LPC_CGU_BASE              (0x40050000)
#define LPC_CCU1_BASE             (0x40051000)
#define LPC_CCU2_BASE             (0x40052000)
#define LPC_RGU_BASE              (0x40053000)
#define LPC_WWDT_BASE             (0x40080000)
#define LPC_USART0_BASE           (0x40081000)
#define LPC_USART2_BASE           (0x400C1000)
#define LPC_USART3_BASE           (0x400C2000)
#define LPC_UART1_BASE            (0x40082000)
#define LPC_SSP0_BASE             (0x40083000)
#define LPC_SSP1_BASE             (0x400C5000)
#define LPC_TIMER0_BASE           (0x40084000)
#define LPC_TIMER1_BASE           (0x40085000)
#define LPC_TIMER2_BASE           (0x400C3000)
#define LPC_TIMER3_BASE           (0x400C4000)
#define LPC_SCU_BASE              (0x40086000)
#define LPC_GPIO_PIN_INT_BASE     (0x40087000)
#define LPC_GPIO_GROUP_INT0_BASE  (0x40088000)
#define LPC_GPIO_GROUP_INT1_BASE  (0x40089000)
#define LPC_MCPWM_BASE            (0x400A0000)
#define LPC_I2C0_BASE             (0x400A1000)
#define LPC_I2C1_BASE             (0x400E0000)
#define LPC_I2S0_BASE             (0x400A2000)
#define LPC_I2S1_BASE             (0x400A3000)
#define LPC_C_CAN1_BASE           (0x400A4000)
#define LPC_RITIMER_BASE          (0x400C0000)
#define LPC_QEI_BASE              (0x400C6000)
#define LPC_GIMA_BASE             (0x400C7000)
#define LPC_DAC_BASE              (0x400E1000)
#define LPC_C_CAN0_BASE           (0x400E2000)
#define LPC_ADC0_BASE             (0x400E3000)
#define LPC_ADC1_BASE             (0x400E4000)
#define LPC_GPIO_PORT_BASE        (0x400F4000)
//The following are applied to have a backward compitability with existing Eagle/Raptor GPIOs
#define LPC_GPIO0_BASE            (0x400F4000)
#define LPC_GPIO1_BASE            (0x400F4004)
#define LPC_GPIO2_BASE            (0x400F4008)
#define LPC_GPIO3_BASE            (0x400F400C)
#define LPC_GPIO4_BASE            (0x400F4010)
#define LPC_GPIO5_BASE            (0x400F4014)
#define LPC_GPIO6_BASE            (0x400F4018)
#define LPC_GPIO7_BASE            (0x400F401C)
#define LPC_RNG_BASE              (0x40054000)
#define LPC_SGPIO_BASE            (0x40101000)
#define LPC_VADC_BASE             (0x400F0000)


// ------------------------------------------------------------------------------------------------
// -----                                Peripheral declaration                                -----
// ------------------------------------------------------------------------------------------------

#define LPC_SCT                   ((LPC_SCT_Type            *) LPC_SCT_BASE)
#define LPC_GPDMA                 ((LPC_GPDMA_Type          *) LPC_GPDMA_BASE)
#define LPC_SPIFI                 ((LPC_SPIFI_Type          *) LPC_SPIFI_BASE)
#define LPC_SDMMC                 ((LPC_SDMMC_Type          *) LPC_SDMMC_BASE)
#define LPC_EMC                   ((LPC_EMC_Type            *) LPC_EMC_BASE)
#define LPC_USB0                  ((LPC_USB0_Type           *) LPC_USB0_BASE)
#define LPC_USB1                  ((LPC_USB1_Type           *) LPC_USB1_BASE)
#define LPC_LCD                   ((LPC_LCD_Type            *) LPC_LCD_BASE)
#define LPC_ETHERNET              ((LPC_ETHERNET_Type       *) LPC_ETHERNET_BASE)
#define LPC_ATIMER                ((LPC_ATIMER_Type         *) LPC_ATIMER_BASE)
#define LPC_REGFILE               ((LPC_REGFILE_Type        *) LPC_REGFILE_BASE)
#define LPC_PMC                   ((LPC_PMC_Type            *) LPC_PMC_BASE)
#define LPC_CREG                  ((LPC_CREG_Type           *) LPC_CREG_BASE)
#define LPC_EVENTROUTER           ((LPC_EVENTROUTER_Type    *) LPC_EVENTROUTER_BASE)
#define LPC_RTC                   ((LPC_RTC_Type            *) LPC_RTC_BASE)
#define LPC_CGU                   ((LPC_CGU_Type            *) LPC_CGU_BASE)
#define LPC_CCU1                  ((LPC_CCU1_Type           *) LPC_CCU1_BASE)
#define LPC_CCU2                  ((LPC_CCU2_Type           *) LPC_CCU2_BASE)
#define LPC_RGU                   ((LPC_RGU_Type            *) LPC_RGU_BASE)
#define LPC_WWDT                  ((LPC_WWDT_Type           *) LPC_WWDT_BASE)
#define LPC_USART0                ((LPC_USARTn_Type         *) LPC_USART0_BASE)
#define LPC_USART2                ((LPC_USARTn_Type         *) LPC_USART2_BASE)
#define LPC_USART3                ((LPC_USARTn_Type         *) LPC_USART3_BASE)
#define LPC_UART1                 ((LPC_UART1_Type          *) LPC_UART1_BASE)
#define LPC_SSP0                  ((LPC_SSPn_Type           *) LPC_SSP0_BASE)
#define LPC_SSP1                  ((LPC_SSPn_Type           *) LPC_SSP1_BASE)
#define LPC_TIMER0                ((LPC_TIMERn_Type         *) LPC_TIMER0_BASE)
#define LPC_TIMER1                ((LPC_TIMERn_Type         *) LPC_TIMER1_BASE)
#define LPC_TIMER2                ((LPC_TIMERn_Type         *) LPC_TIMER2_BASE)
#define LPC_TIMER3                ((LPC_TIMERn_Type         *) LPC_TIMER3_BASE)
#define LPC_SCU                   ((LPC_SCU_Type            *) LPC_SCU_BASE)
#define LPC_GPIO_PIN_INT          ((LPC_GPIO_PIN_INT_Type   *) LPC_GPIO_PIN_INT_BASE)
#define LPC_GPIO_GROUP_INT0       ((LPC_GPIO_GROUP_INT0_Type*) LPC_GPIO_GROUP_INT0_BASE)
#define LPC_GPIO_GROUP_INT1       ((LPC_GPIO_GROUP_INT1_Type*) LPC_GPIO_GROUP_INT1_BASE)
#define LPC_MCPWM                 ((LPC_MCPWM_Type          *) LPC_MCPWM_BASE)
#define LPC_I2C0                  ((LPC_I2Cn_Type           *) LPC_I2C0_BASE)
#define LPC_I2C1                  ((LPC_I2Cn_Type           *) LPC_I2C1_BASE)
#define LPC_I2S0                  ((LPC_I2Sn_Type           *) LPC_I2S0_BASE)
#define LPC_I2S1                  ((LPC_I2Sn_Type           *) LPC_I2S1_BASE)
#define LPC_C_CAN1                ((LPC_C_CANn_Type         *) LPC_C_CAN1_BASE)
#define LPC_RITIMER               ((LPC_RITIMER_Type        *) LPC_RITIMER_BASE)
#define LPC_QEI                   ((LPC_QEI_Type            *) LPC_QEI_BASE)
#define LPC_GIMA                  ((LPC_GIMA_Type           *) LPC_GIMA_BASE)
#define LPC_DAC                   ((LPC_DAC_Type            *) LPC_DAC_BASE)
#define LPC_C_CAN0                ((LPC_C_CANn_Type         *) LPC_C_CAN0_BASE)
#define LPC_ADC0                  ((LPC_ADCn_Type           *) LPC_ADC0_BASE)
#define LPC_ADC1                  ((LPC_ADCn_Type           *) LPC_ADC1_BASE)
#define LPC_GPIO_PORT             ((LPC_GPIO_PORT_Type      *) LPC_GPIO_PORT_BASE) //Short name: HSGPIO???
#define LPC_GPIO0                 ((LPC_GPIOn_Type          *) LPC_GPIO0_BASE)     //Backward compitable for all GPIOs
#define LPC_GPIO1                 ((LPC_GPIOn_Type          *) LPC_GPIO1_BASE)
#define LPC_GPIO2                 ((LPC_GPIOn_Type          *) LPC_GPIO2_BASE)
#define LPC_GPIO3                 ((LPC_GPIOn_Type          *) LPC_GPIO3_BASE)
#define LPC_GPIO4                 ((LPC_GPIOn_Type          *) LPC_GPIO4_BASE)
#define LPC_GPIO5                 ((LPC_GPIOn_Type          *) LPC_GPIO5_BASE)
#define LPC_GPIO6                 ((LPC_GPIOn_Type          *) LPC_GPIO6_BASE)
#define LPC_GPIO7                 ((LPC_GPIOn_Type          *) LPC_GPIO7_BASE)
#define LPC_SGPIO                 ((LPC_SGPIO_Type          *) LPC_SGPIO_BASE)
#define LPC_RNG                   ((LPC_RNG_Type            *) LPC_RNG_BASE)
#define LPC_VADC                  ((LPC_VADC_Type           *) LPC_VADC_BASE)

/** @} */ /* End of group Device_Peripheral_Registers */
/** @} */ /* End of group (null) */
/** @} */ /* End of group LPC43xx */

#ifdef __cplusplus
}
#endif 


#endif  // __LPC43XX_A_H__
