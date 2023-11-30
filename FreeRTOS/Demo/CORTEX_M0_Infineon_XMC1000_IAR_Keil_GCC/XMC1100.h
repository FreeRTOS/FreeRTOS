
/****************************************************************************************************//**
 * @file     XMC1100.h
 *
 * @brief    CMSIS Cortex-M0 Peripheral Access Layer Header File for
 *           XMC1100 from Infineon.
 *
 * @version  V1.0.6 (Reference Manual v1.0)
 * @date     26. March 2013
 *
 * @note     Generated with SVDConv V2.78b 
 *           from CMSIS SVD File 'XMC1100_Processed_SVD.xml' Version 1.0.6 (Reference Manual v1.0),
 *******************************************************************************************************/



/** @addtogroup Infineon
  * @{
  */

/** @addtogroup XMC1100
  * @{
  */

#ifndef XMC1100_H
#define XMC1100_H

#ifdef __cplusplus
extern "C" {
#endif


/* -------------------------  Interrupt Number Definition  ------------------------ */

typedef enum {
/* -------------------  Cortex-M0 Processor Exceptions Numbers  ------------------- */
  Reset_IRQn                    = -15,              /*!<   1  Reset Vector, invoked on Power up and warm reset                 */
  NonMaskableInt_IRQn           = -14,              /*!<   2  Non maskable Interrupt, cannot be stopped or preempted           */
  HardFault_IRQn                = -13,              /*!<   3  Hard Fault, all classes of Fault                                 */
  SVCall_IRQn                   =  -5,              /*!<  11  System Service Call via SVC instruction                          */
  DebugMonitor_IRQn             =  -4,              /*!<  12  Debug Monitor                                                    */
  PendSV_IRQn                   =  -2,              /*!<  14  Pendable request for system service                              */
  SysTick_IRQn                  =  -1,              /*!<  15  System Tick Timer                                                */
/* ---------------------  XMC1100 Specific Interrupt Numbers  --------------------- */
  SCU_0_IRQn          =   0,   /*!< SCU SR0 Interrupt                        */
  SCU_1_IRQn          =   1,   /*!< SCU SR1 Interrupt                        */
  SCU_2_IRQn          =   2,   /*!< SCU SR2 Interrupt                        */
  ERU0_0_IRQn         =   3,   /*!< ERU0 SR0 Interrupt                       */
  ERU0_1_IRQn         =   4,   /*!< ERU0 SR1 Interrupt                       */
  ERU0_2_IRQn         =   5,   /*!< ERU0 SR2 Interrupt                       */
  ERU0_3_IRQn         =   6,   /*!< ERU0 SR3 Interrupt                       */
  
  USIC0_0_IRQn        =   9,   /*!< USIC SR0 Interrupt                       */
  USIC0_1_IRQn        =  10,   /*!< USIC SR1 Interrupt                       */
  USIC0_2_IRQn        =  11,   /*!< USIC SR2 Interrupt                       */
  USIC0_3_IRQn        =  12,   /*!< USIC SR3 Interrupt                       */
  USIC0_4_IRQn        =  13,   /*!< USIC SR4 Interrupt                       */
  USIC0_5_IRQn        =  14,   /*!< USIC SR5 Interrupt                       */
  
  VADC0_C0_0_IRQn     =  15,   /*!< VADC SR0 Interrupt                       */
  VADC0_C0_1_IRQn     =  16,   /*!< VADC SR1 Interrupt                       */
  
  CCU40_0_IRQn        =  21,   /*!< CCU40 SR0 Interrupt                      */
  CCU40_1_IRQn        =  22,   /*!< CCU40 SR1 Interrupt                      */
  CCU40_2_IRQn        =  23,   /*!< CCU40 SR2 Interrupt                      */
  CCU40_3_IRQn        =  24,   /*!< CCU40 SR3 Interrupt                      */

} IRQn_Type;


/** @addtogroup Configuration_of_CMSIS
  * @{
  */


/* ================================================================================ */
/* ================      Processor and Core Peripheral Section     ================ */
/* ================================================================================ */

/* ----------------Configuration of the Cortex-M0 Processor and Core Peripherals---------------- */
#define __CM0_REV                 0x0000            /*!< Cortex-M0 Core Revision                                               */
#define __MPU_PRESENT                  0            /*!< MPU present or not                                                    */
#define __NVIC_PRIO_BITS               2            /*!< Number of Bits used for Priority Levels                               */
#define __Vendor_SysTickConfig         0            /*!< Set to 1 if different SysTick Config is used                          */
/** @} */ /* End of group Configuration_of_CMSIS */

#include <core_cm0.h>                               /*!< Cortex-M0 processor and core peripherals                              */
#include "system_XMC1100.h"                         /*!< XMC1100 System                                                        */


/* ================================================================================ */
/* ================       Device Specific Peripheral Section       ================ */
/* ================================================================================ */
/* Macro to modify desired bitfields of a register */
#define WR_REG(reg, mask, pos, val) reg = (((uint32_t)val << pos) & \
		                                         ((uint32_t)mask)) | \
                                          (reg & ((uint32_t)~((uint32_t)mask)))

/* Macro to modify desired bitfields of a register */
#define WR_REG_SIZE(reg, mask, pos, val, size) {  \
uint##size##_t VAL1 = (uint##size##_t)((uint##size##_t)val << pos); \
uint##size##_t VAL2 = (uint##size##_t) (VAL1 & (uint##size##_t)mask); \
uint##size##_t VAL3 = (uint##size##_t)~((uint##size##_t)mask); \
uint##size##_t VAL4 = (uint##size##_t) ((uint##size##_t)reg & VAL3); \
reg = (uint##size##_t) (VAL2 | VAL4);\
}

/** Macro to read bitfields from a register */
#define RD_REG(reg, mask, pos) (((uint32_t)reg & (uint32_t)mask) >> pos)

/** Macro to read bitfields from a register */
#define RD_REG_SIZE(reg, mask, pos,size) ((uint##size##_t)(((uint32_t)reg & \
                                                      (uint32_t)mask) >> pos) )

/** Macro to set a bit in register */
#define SET_BIT(reg, pos)     (reg |= ((uint32_t)1<<pos))

/** Macro to clear a bit in register */
#define CLR_BIT(reg, pos)     (reg = reg & (uint32_t)(~((uint32_t)1<<pos)) )
/*
* ==========================================================================
* ---------- Interrupt Handler Definition ----------------------------------
* ==========================================================================
*/
#define IRQ_Hdlr_0   SCU_0_IRQHandler
#define IRQ_Hdlr_1   SCU_1_IRQHandler
#define IRQ_Hdlr_2   SCU_2_IRQHandler
#define IRQ_Hdlr_3   ERU0_0_IRQHandler
#define IRQ_Hdlr_4   ERU0_1_IRQHandler
#define IRQ_Hdlr_5   ERU0_2_IRQHandler
#define IRQ_Hdlr_6   ERU0_3_IRQHandler

#define IRQ_Hdlr_9   USIC0_0_IRQHandler
#define IRQ_Hdlr_10  USIC0_1_IRQHandler
#define IRQ_Hdlr_11  USIC0_2_IRQHandler
#define IRQ_Hdlr_12  USIC0_3_IRQHandler
#define IRQ_Hdlr_13  USIC0_4_IRQHandler
#define IRQ_Hdlr_14  USIC0_5_IRQHandler
#define IRQ_Hdlr_15  VADC0_C0_0_IRQHandler
#define IRQ_Hdlr_16  VADC0_C0_1_IRQHandler
#define IRQ_Hdlr_21  CCU40_0_IRQHandler
#define IRQ_Hdlr_22  CCU40_1_IRQHandler
#define IRQ_Hdlr_23  CCU40_2_IRQHandler
#define IRQ_Hdlr_24  CCU40_3_IRQHandler

/*
* ==========================================================================
* ---------- Interrupt Handler retrieval macro -----------------------------
* ==========================================================================
*/
#define GET_IRQ_HANDLER(N) IRQ_Hdlr_##N


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
/* ================                       PPB                      ================ */
/* ================================================================================ */


/**
  * @brief Cortex-M0 Private Peripheral Block (PPB)
  */

typedef struct {                                    /*!< (@ 0xE000E000) PPB Structure                                          */
  __I  uint32_t  RESERVED0[4];
  __IO uint32_t  SYST_CSR;                          /*!< (@ 0xE000E010) SysTick Control and Status Register                    */
  __IO uint32_t  SYST_RVR;                          /*!< (@ 0xE000E014) SysTick Reload Value Register                          */
  __IO uint32_t  SYST_CVR;                          /*!< (@ 0xE000E018) SysTick Current Value Register                         */
  __I  uint32_t  SYST_CALIB;                        /*!< (@ 0xE000E01C) SysTick Calibration Value Register                     */
  __I  uint32_t  RESERVED1[56];
  __IO uint32_t  NVIC_ISER;                         /*!< (@ 0xE000E100) Interrupt Set-enable Register                          */
  __I  uint32_t  RESERVED2[31];
  __IO uint32_t  NVIC_ICER;                         /*!< (@ 0xE000E180) IInterrupt Clear-enable Register                       */
  __I  uint32_t  RESERVED3[31];
  __IO uint32_t  NVIC_ISPR;                         /*!< (@ 0xE000E200) Interrupt Set-pending Register                         */
  __I  uint32_t  RESERVED4[31];
  __IO uint32_t  NVIC_ICPR;                         /*!< (@ 0xE000E280) Interrupt Clear-pending Register                       */
  __I  uint32_t  RESERVED5[95];
  __IO uint32_t  NVIC_IPR0;                         /*!< (@ 0xE000E400) Interrupt Priority Register 0                          */
  __IO uint32_t  NVIC_IPR1;                         /*!< (@ 0xE000E404) Interrupt Priority Register 1                          */
  __IO uint32_t  NVIC_IPR2;                         /*!< (@ 0xE000E408) Interrupt Priority Register 2                          */
  __IO uint32_t  NVIC_IPR3;                         /*!< (@ 0xE000E40C) Interrupt Priority Register 3                          */
  __IO uint32_t  NVIC_IPR4;                         /*!< (@ 0xE000E410) Interrupt Priority Register 4                          */
  __IO uint32_t  NVIC_IPR5;                         /*!< (@ 0xE000E414) Interrupt Priority Register 5                          */
  __IO uint32_t  NVIC_IPR6;                         /*!< (@ 0xE000E418) Interrupt Priority Register 6                          */
  __IO uint32_t  NVIC_IPR7;                         /*!< (@ 0xE000E41C) Interrupt Priority Register 7                          */
  __I  uint32_t  RESERVED6[568];
  __I  uint32_t  CPUID;                             /*!< (@ 0xE000ED00) CPUID Base Register                                    */
  __IO uint32_t  ICSR;                              /*!< (@ 0xE000ED04) Interrupt Control and State Register                   */
  __I  uint32_t  RESERVED7;
  __IO uint32_t  AIRCR;                             /*!< (@ 0xE000ED0C) Application Interrupt and Reset Control Register       */
  __IO uint32_t  SCR;                               /*!< (@ 0xE000ED10) System Control Register                                */
  __I  uint32_t  CCR;                               /*!< (@ 0xE000ED14) Configuration and Control Register                     */
  __I  uint32_t  RESERVED8;
  __IO uint32_t  SHPR2;                             /*!< (@ 0xE000ED1C) System Handler Priority Register 2                     */
  __IO uint32_t  SHPR3;                             /*!< (@ 0xE000ED20) System Handler Priority Register 3                     */
  __IO uint32_t  SHCSR;                             /*!< (@ 0xE000ED24) System Handler Control and State Register              */
} PPB_Type;


/* ================================================================================ */
/* ================                   ERU [ERU0]                   ================ */
/* ================================================================================ */


/**
  * @brief Event Request Unit 0 (ERU)
  */

typedef struct {                                    /*!< (@ 0x40010600) ERU Structure                                          */
  __IO uint32_t  EXISEL;                            /*!< (@ 0x40010600) Event Input Select                                     */
  __I  uint32_t  RESERVED0[3];
  __IO uint32_t  EXICON[4];                         /*!< (@ 0x40010610) Event Input Control                                    */
  __IO uint32_t  EXOCON[4];                         /*!< (@ 0x40010620) Event Output Trigger Control                           */
} ERU_GLOBAL_TypeDef;


/* ================================================================================ */
/* ================                       PAU                      ================ */
/* ================================================================================ */


/**
  * @brief PAU Unit (PAU)
  */

typedef struct {                                    /*!< (@ 0x40000000) PAU Structure                                          */
  __I  uint32_t  RESERVED0[16];
  __I  uint32_t  AVAIL0;                            /*!< (@ 0x40000040) Peripheral Availability Register 0                     */
  __I  uint32_t  AVAIL1;                            /*!< (@ 0x40000044) Peripheral Availability Register 1                     */
  __I  uint32_t  AVAIL2;                            /*!< (@ 0x40000048) Peripheral Availability Register 2                     */
  __I  uint32_t  RESERVED1[13];
  __IO uint32_t  PRIVDIS0;                          /*!< (@ 0x40000080) Peripheral Privilege Access Register 0                 */
  __IO uint32_t  PRIVDIS1;                          /*!< (@ 0x40000084) Peripheral Privilege Access Register 1                 */
  __I  uint32_t  RESERVED2[222];
  __I  uint32_t  ROMSIZE;                           /*!< (@ 0x40000400) ROM Size Register                                      */
  __I  uint32_t  FLSIZE;                            /*!< (@ 0x40000404) Flash Size Register                                    */
  __I  uint32_t  RESERVED3[2];
  __I  uint32_t  RAM0SIZE;                          /*!< (@ 0x40000410) RAM0 Size Register                                     */
} PAU_Type;


/* ================================================================================ */
/* ================                       NVM                      ================ */
/* ================================================================================ */


/**
  * @brief NVM Unit (NVM)
  */

typedef struct {                                    /*!< (@ 0x40050000) NVM Structure                                          */
  __I  uint16_t  NVMSTATUS;                         /*!< (@ 0x40050000) NVM Status Register                                    */
  __I  uint16_t  RESERVED0;
  __IO uint16_t  NVMPROG;                           /*!< (@ 0x40050004) NVM Programming Control Register                       */
  __I  uint16_t  RESERVED1;
  __IO uint16_t  NVMCONF;                           /*!< (@ 0x40050008) NVM Configuration Register                             */
} NVM_Type;


/* ================================================================================ */
/* ================                       WDT                      ================ */
/* ================================================================================ */


/**
  * @brief Watch Dog Timer (WDT)
  */

typedef struct {                                    /*!< (@ 0x40020000) WDT Structure                                          */
  __I  uint32_t  ID;                                /*!< (@ 0x40020000) WDT Module ID Register                                 */
  __IO uint32_t  CTR;                               /*!< (@ 0x40020004) WDT Control Register                                   */
  __O  uint32_t  SRV;                               /*!< (@ 0x40020008) WDT Service Register                                   */
  __I  uint32_t  TIM;                               /*!< (@ 0x4002000C) WDT Timer Register                                     */
  __IO uint32_t  WLB;                               /*!< (@ 0x40020010) WDT Window Lower Bound Register                        */
  __IO uint32_t  WUB;                               /*!< (@ 0x40020014) WDT Window Upper Bound Register                        */
  __I  uint32_t  WDTSTS;                            /*!< (@ 0x40020018) WDT Status Register                                    */
  __O  uint32_t  WDTCLR;                            /*!< (@ 0x4002001C) WDT Clear Register                                     */
} WDT_GLOBAL_TypeDef;


/* ================================================================================ */
/* ================                       RTC                      ================ */
/* ================================================================================ */


/**
  * @brief Real Time Clock (RTC)
  */

typedef struct {                                    /*!< (@ 0x40010A00) RTC Structure                                          */
  __I  uint32_t  ID;                                /*!< (@ 0x40010A00) RTC Module ID Register                                 */
  __IO uint32_t  CTR;                               /*!< (@ 0x40010A04) RTC Control Register                                   */
  __I  uint32_t  RAWSTAT;                           /*!< (@ 0x40010A08) RTC Raw Service Request Register                       */
  __I  uint32_t  STSSR;                             /*!< (@ 0x40010A0C) RTC Service Request Status Register                    */
  __IO uint32_t  MSKSR;                             /*!< (@ 0x40010A10) RTC Service Request Mask Register                      */
  __O  uint32_t  CLRSR;                             /*!< (@ 0x40010A14) RTC Clear Service Request Register                     */
  __IO uint32_t  ATIM0;                             /*!< (@ 0x40010A18) RTC Alarm Time Register 0                              */
  __IO uint32_t  ATIM1;                             /*!< (@ 0x40010A1C) RTC Alarm Time Register 1                              */
  __IO uint32_t  TIM0;                              /*!< (@ 0x40010A20) RTC Time Register 0                                    */
  __IO uint32_t  TIM1;                              /*!< (@ 0x40010A24) RTC Time Register 1                                    */
} RTC_GLOBAL_TypeDef;


/* ================================================================================ */
/* ================                      PRNG                      ================ */
/* ================================================================================ */


/**
  * @brief PRNG Unit (PRNG)
  */

typedef struct {                                    /*!< (@ 0x48020000) PRNG Structure                                         */
  __IO uint16_t  WORD;                              /*!< (@ 0x48020000) Pseudo RNG Word Register                               */
  __I  uint16_t  RESERVED0;
  __I  uint16_t  CHK;                               /*!< (@ 0x48020004) Pseudo RNG Status Check Register                       */
  __I  uint16_t  RESERVED1[3];
  __IO uint16_t  CTRL;                              /*!< (@ 0x4802000C) Pseudo RNG Control Register                            */
} PRNG_Type;


/* ================================================================================ */
/* ================                  USIC [USIC0]                  ================ */
/* ================================================================================ */


/**
  * @brief Universal Serial Interface Controller 0 (USIC)
  */

typedef struct {                                    /*!< (@ 0x48000008) USIC Structure                                         */
  __I  uint32_t  ID;                                /*!< (@ 0x48000008) Module Identification Register                         */
} USIC_GLOBAL_TypeDef;


/* ================================================================================ */
/* ================               USIC_CH [USIC0_CH0]              ================ */
/* ================================================================================ */


/**
  * @brief Universal Serial Interface Controller 0 (USIC_CH)
  */

typedef struct {                                    /*!< (@ 0x48000000) USIC_CH Structure                                      */
  __I  uint32_t  RESERVED0;
  __I  uint32_t  CCFG;                              /*!< (@ 0x48000004) Channel Configuration Register                         */
  __I  uint32_t  RESERVED1;
  __IO uint32_t  KSCFG;                             /*!< (@ 0x4800000C) Kernel State Configuration Register                    */
  __IO uint32_t  FDR;                               /*!< (@ 0x48000010) Fractional Divider Register                            */
  __IO uint32_t  BRG;                               /*!< (@ 0x48000014) Baud Rate Generator Register                           */
  __IO uint32_t  INPR;                              /*!< (@ 0x48000018) Interrupt Node Pointer Register                        */
  __IO uint32_t  DX0CR;                             /*!< (@ 0x4800001C) Input Control Register 0                               */
  __IO uint32_t  DX1CR;                             /*!< (@ 0x48000020) Input Control Register 1                               */
  __IO uint32_t  DX2CR;                             /*!< (@ 0x48000024) Input Control Register 2                               */
  __IO uint32_t  DX3CR;                             /*!< (@ 0x48000028) Input Control Register 3                               */
  __IO uint32_t  DX4CR;                             /*!< (@ 0x4800002C) Input Control Register 4                               */
  __IO uint32_t  DX5CR;                             /*!< (@ 0x48000030) Input Control Register 5                               */
  __IO uint32_t  SCTR;                              /*!< (@ 0x48000034) Shift Control Register                                 */
  __IO uint32_t  TCSR;                              /*!< (@ 0x48000038) Transmit Control/Status Register                       */
  
  union {
    __IO uint32_t  PCR_IICMode;                     /*!< (@ 0x4800003C) Protocol Control Register [IIC Mode]                   */
    __IO uint32_t  PCR_IISMode;                     /*!< (@ 0x4800003C) Protocol Control Register [IIS Mode]                   */
    __IO uint32_t  PCR_SSCMode;                     /*!< (@ 0x4800003C) Protocol Control Register [SSC Mode]                   */
    __IO uint32_t  PCR;                             /*!< (@ 0x4800003C) Protocol Control Register                              */
    __IO uint32_t  PCR_ASCMode;                     /*!< (@ 0x4800003C) Protocol Control Register [ASC Mode]                   */
  };
  __IO uint32_t  CCR;                               /*!< (@ 0x48000040) Channel Control Register                               */
  __IO uint32_t  CMTR;                              /*!< (@ 0x48000044) Capture Mode Timer Register                            */
  
  union {
    __IO uint32_t  PSR_IICMode;                     /*!< (@ 0x48000048) Protocol Status Register [IIC Mode]                    */
    __IO uint32_t  PSR_IISMode;                     /*!< (@ 0x48000048) Protocol Status Register [IIS Mode]                    */
    __IO uint32_t  PSR_SSCMode;                     /*!< (@ 0x48000048) Protocol Status Register [SSC Mode]                    */
    __IO uint32_t  PSR;                             /*!< (@ 0x48000048) Protocol Status Register                               */
    __IO uint32_t  PSR_ASCMode;                     /*!< (@ 0x48000048) Protocol Status Register [ASC Mode]                    */
  };
  __O  uint32_t  PSCR;                              /*!< (@ 0x4800004C) Protocol Status Clear Register                         */
  __I  uint32_t  RBUFSR;                            /*!< (@ 0x48000050) Receiver Buffer Status Register                        */
  __I  uint32_t  RBUF;                              /*!< (@ 0x48000054) Receiver Buffer Register                               */
  __I  uint32_t  RBUFD;                             /*!< (@ 0x48000058) Receiver Buffer Register for Debugger                  */
  __I  uint32_t  RBUF0;                             /*!< (@ 0x4800005C) Receiver Buffer Register 0                             */
  __I  uint32_t  RBUF1;                             /*!< (@ 0x48000060) Receiver Buffer Register 1                             */
  __I  uint32_t  RBUF01SR;                          /*!< (@ 0x48000064) Receiver Buffer 01 Status Register                     */
  __O  uint32_t  FMR;                               /*!< (@ 0x48000068) Flag Modification Register                             */
  __I  uint32_t  RESERVED2[5];
  __IO uint32_t  TBUF[32];                          /*!< (@ 0x48000080) Transmit Buffer                                        */
  __IO uint32_t  BYP;                               /*!< (@ 0x48000100) Bypass Data Register                                   */
  __IO uint32_t  BYPCR;                             /*!< (@ 0x48000104) Bypass Control Register                                */
  __IO uint32_t  TBCTR;                             /*!< (@ 0x48000108) Transmitter Buffer Control Register                    */
  __IO uint32_t  RBCTR;                             /*!< (@ 0x4800010C) Receiver Buffer Control Register                       */
  __I  uint32_t  TRBPTR;                            /*!< (@ 0x48000110) Transmit/Receive Buffer Pointer Register               */
  __IO uint32_t  TRBSR;                             /*!< (@ 0x48000114) Transmit/Receive Buffer Status Register                */
  __O  uint32_t  TRBSCR;                            /*!< (@ 0x48000118) Transmit/Receive Buffer Status Clear Register          */
  __I  uint32_t  OUTR;                              /*!< (@ 0x4800011C) Receiver Buffer Output Register                        */
  __I  uint32_t  OUTDR;                             /*!< (@ 0x48000120) Receiver Buffer Output Register L for Debugger         */
  __I  uint32_t  RESERVED3[23];
  __O  uint32_t  IN[32];                            /*!< (@ 0x48000180) Transmit FIFO Buffer                                   */
} USIC_CH_TypeDef;


/* ================================================================================ */
/* ================                   SCU_GENERAL                  ================ */
/* ================================================================================ */


/**
  * @brief System Control Unit (SCU_GENERAL)
  */

typedef struct {                                    /*!< (@ 0x40010000) SCU_GENERAL Structure                                  */
  __I  uint32_t  DBGROMID;                          /*!< (@ 0x40010000) Debug System ROM ID Register                           */
  __I  uint32_t  IDCHIP;                            /*!< (@ 0x40010004) Chip ID Register                                       */
  __I  uint32_t  ID;                                /*!< (@ 0x40010008) SCU Module ID Register                                 */
  __I  uint32_t  RESERVED0[2];
  __IO uint32_t  SSW0;                              /*!< (@ 0x40010014) SSW Register 0                                         */
  __I  uint32_t  RESERVED1[3];
  __IO uint32_t  PASSWD;                            /*!< (@ 0x40010024) Password Register                                      */
  __I  uint32_t  RESERVED2[2];
  __IO uint32_t  CCUCON;                            /*!< (@ 0x40010030) CCU Control Register                                   */
  __I  uint32_t  RESERVED3[5];
  __I  uint32_t  MIRRSTS;                           /*!< (@ 0x40010048) Mirror Update Status Register                          */
  __I  uint32_t  RESERVED4[2];
  __IO uint32_t  PMTSR;                             /*!< (@ 0x40010054) Parity Memory Test Select Register                     */
} SCU_GENERAL_Type;


/* ================================================================================ */
/* ================                  SCU_INTERRUPT                 ================ */
/* ================================================================================ */


/**
  * @brief System Control Unit (SCU_INTERRUPT)
  */

typedef struct {                                    /*!< (@ 0x40010038) SCU_INTERRUPT Structure                                */
  __I  uint32_t  SRRAW;                             /*!< (@ 0x40010038) SCU Raw Service Request Status                         */
  __IO uint32_t  SRMSK;                             /*!< (@ 0x4001003C) SCU Service Request Mask                               */
  __O  uint32_t  SRCLR;                             /*!< (@ 0x40010040) SCU Service Request Clear                              */
  __O  uint32_t  SRSET;                             /*!< (@ 0x40010044) SCU Service Request Set                                */
} SCU_INTERRUPT_TypeDef;


/* ================================================================================ */
/* ================                    SCU_POWER                   ================ */
/* ================================================================================ */


/**
  * @brief System Control Unit (SCU_POWER)
  */

typedef struct {                                    /*!< (@ 0x40010200) SCU_POWER Structure                                    */
  __I  uint32_t  VDESR;                             /*!< (@ 0x40010200) Voltage Detector Status Register                       */
} SCU_POWER_Type;


/* ================================================================================ */
/* ================                     SCU_CLK                    ================ */
/* ================================================================================ */


/**
  * @brief System Control Unit (SCU_CLK)
  */

typedef struct {                                    /*!< (@ 0x40010300) SCU_CLK Structure                                      */
  __IO uint32_t  CLKCR;                             /*!< (@ 0x40010300) Clock Control Register                                 */
  __IO uint32_t  PWRSVCR;                           /*!< (@ 0x40010304) Power Save Control Register                            */
  __I  uint32_t  CGATSTAT0;                         /*!< (@ 0x40010308) Peripheral 0 Clock Gating Status                       */
  __O  uint32_t  CGATSET0;                          /*!< (@ 0x4001030C) Peripheral 0 Clock Gating Set                          */
  __O  uint32_t  CGATCLR0;                          /*!< (@ 0x40010310) Peripheral 0 Clock Gating Clear                        */
  __IO uint32_t  OSCCSR;                            /*!< (@ 0x40010314) Oscillator Control and Status Register                 */
} SCU_CLK_TypeDef;


/* ================================================================================ */
/* ================                    SCU_RESET                   ================ */
/* ================================================================================ */


/**
  * @brief System Control Unit (SCU_RESET)
  */

typedef struct {                                    /*!< (@ 0x40010400) SCU_RESET Structure                                    */
  __I  uint32_t  RSTSTAT;                           /*!< (@ 0x40010400) RCU Reset Status                                       */
  __O  uint32_t  RSTSET;                            /*!< (@ 0x40010404) RCU Reset Set Register                                 */
  __O  uint32_t  RSTCLR;                            /*!< (@ 0x40010408) RCU Reset Clear Register                               */
  __IO uint32_t  RSTCON;                            /*!< (@ 0x4001040C) RCU Reset Control Register                             */
} SCU_RESET_Type;


/* ================================================================================ */
/* ================                   SCU_ANALOG                   ================ */
/* ================================================================================ */


/**
  * @brief System Control Unit (SCU_ANALOG)
  */

typedef struct {                                    /*!< (@ 0x40011000) SCU_ANALOG Structure                                   */
  __I  uint32_t  RESERVED0[20];
  __IO uint16_t  ANAVDEL;                           /*!< (@ 0x40011050) Voltage Detector Control Register                      */
} SCU_ANALOG_Type;


/* ================================================================================ */
/* ================                  CCU4 [CCU40]                  ================ */
/* ================================================================================ */


/**
  * @brief Capture Compare Unit 4 - Unit 0 (CCU4)
  */

typedef struct {                                    /*!< (@ 0x48040000) CCU4 Structure                                         */
  __IO uint32_t  GCTRL;                             /*!< (@ 0x48040000) Global Control Register                                */
  __I  uint32_t  GSTAT;                             /*!< (@ 0x48040004) Global Status Register                                 */
  __O  uint32_t  GIDLS;                             /*!< (@ 0x48040008) Global Idle Set                                        */
  __O  uint32_t  GIDLC;                             /*!< (@ 0x4804000C) Global Idle Clear                                      */
  __O  uint32_t  GCSS;                              /*!< (@ 0x48040010) Global Channel Set                                     */
  __O  uint32_t  GCSC;                              /*!< (@ 0x48040014) Global Channel Clear                                   */
  __I  uint32_t  GCST;                              /*!< (@ 0x48040018) Global Channel Status                                  */
  __I  uint32_t  RESERVED0[25];
  __I  uint32_t  MIDR;                              /*!< (@ 0x48040080) Module Identification                                  */
} CCU4_GLOBAL_TypeDef;


/* ================================================================================ */
/* ================              CCU4_CC4 [CCU40_CC40]             ================ */
/* ================================================================================ */


/**
  * @brief Capture Compare Unit 4 - Unit 0 (CCU4_CC4)
  */

typedef struct {                                    /*!< (@ 0x48040100) CCU4_CC4 Structure                                     */
  __IO uint32_t  INS;                               /*!< (@ 0x48040100) Input Selector Configuration                           */
  __IO uint32_t  CMC;                               /*!< (@ 0x48040104) Connection Matrix Control                              */
  __I  uint32_t  TCST;                              /*!< (@ 0x48040108) Slice Timer Status                                     */
  __O  uint32_t  TCSET;                             /*!< (@ 0x4804010C) Slice Timer Run Set                                    */
  __O  uint32_t  TCCLR;                             /*!< (@ 0x48040110) Slice Timer Clear                                      */
  __IO uint32_t  TC;                                /*!< (@ 0x48040114) Slice Timer Control                                    */
  __IO uint32_t  PSL;                               /*!< (@ 0x48040118) Passive Level Config                                   */
  __I  uint32_t  DIT;                               /*!< (@ 0x4804011C) Dither Config                                          */
  __IO uint32_t  DITS;                              /*!< (@ 0x48040120) Dither Shadow Register                                 */
  __IO uint32_t  PSC;                               /*!< (@ 0x48040124) Prescaler Control                                      */
  __IO uint32_t  FPC;                               /*!< (@ 0x48040128) Floating Prescaler Control                             */
  __IO uint32_t  FPCS;                              /*!< (@ 0x4804012C) Floating Prescaler Shadow                              */
  __I  uint32_t  PR;                                /*!< (@ 0x48040130) Timer Period Value                                     */
  __IO uint32_t  PRS;                               /*!< (@ 0x48040134) Timer Shadow Period Value                              */
  __I  uint32_t  CR;                                /*!< (@ 0x48040138) Timer Compare Value                                    */
  __IO uint32_t  CRS;                               /*!< (@ 0x4804013C) Timer Shadow Compare Value                             */
  __I  uint32_t  RESERVED0[12];
  __IO uint32_t  TIMER;                             /*!< (@ 0x48040170) Timer Value                                            */
  __I  uint32_t  CV[4];                             /*!< (@ 0x48040174) Capture Register 0                                     */
  __I  uint32_t  RESERVED1[7];
  __I  uint32_t  INTS;                              /*!< (@ 0x480401A0) Interrupt Status                                       */
  __IO uint32_t  INTE;                              /*!< (@ 0x480401A4) Interrupt Enable Control                               */
  __IO uint32_t  SRS;                               /*!< (@ 0x480401A8) Service Request Selector                               */
  __O  uint32_t  SWS;                               /*!< (@ 0x480401AC) Interrupt Status Set                                   */
  __O  uint32_t  SWR;                               /*!< (@ 0x480401B0) Interrupt Status Clear                                 */
  __I  uint32_t  RESERVED2;
  __I  uint32_t  ECRD0;                             /*!< (@ 0x480401B8) Extended Read Back 0                                   */
  __I  uint32_t  ECRD1;                             /*!< (@ 0x480401BC) Extended Read Back 1                                   */
} CCU4_CC4_TypeDef;


/* ================================================================================ */
/* ================                   VADC [VADC]                  ================ */
/* ================================================================================ */


/**
  * @brief Analog to Digital Converter (VADC)
  */

typedef struct {                                    /*!< (@ 0x48030000) VADC Structure                                         */
  __IO uint32_t  CLC;                               /*!< (@ 0x48030000) Clock Control Register                                 */
  __I  uint32_t  RESERVED0;
  __I  uint32_t  ID;                                /*!< (@ 0x48030008) Module Identification Register                         */
  __I  uint32_t  RESERVED1[7];
  __IO uint32_t  OCS;                               /*!< (@ 0x48030028) OCDS Control and Status Register                       */
  __I  uint32_t  RESERVED2[21];
  __IO uint32_t  GLOBCFG;                           /*!< (@ 0x48030080) Global Configuration Register                          */
  __I  uint32_t  RESERVED3[7];
  __IO uint32_t  GLOBICLASS[2];                     /*!< (@ 0x480300A0) Input Class Register, Global                           */
  __I  uint32_t  RESERVED4[14];
  __IO uint32_t  GLOBEFLAG;                         /*!< (@ 0x480300E0) Global Event Flag Register                             */
  __I  uint32_t  RESERVED5[23];
  __IO uint32_t  GLOBEVNP;                          /*!< (@ 0x48030140) Global Event Node Pointer Register                     */
  __I  uint32_t  RESERVED6[15];
  __IO uint32_t  BRSSEL[2];                         /*!< (@ 0x48030180) Background Request Source Channel Select Register      */
  __I  uint32_t  RESERVED7[14];
  __IO uint32_t  BRSPND[2];                         /*!< (@ 0x480301C0) Background Request Source Pending Register             */
  __I  uint32_t  RESERVED8[14];
  __IO uint32_t  BRSCTRL;                           /*!< (@ 0x48030200) Background Request Source Control Register             */
  __IO uint32_t  BRSMR;                             /*!< (@ 0x48030204) Background Request Source Mode Register                */
  __I  uint32_t  RESERVED9[30];
  __IO uint32_t  GLOBRCR;                           /*!< (@ 0x48030280) Global Result Control Register                         */
  __I  uint32_t  RESERVED10[31];
  __IO uint32_t  GLOBRES;                           /*!< (@ 0x48030300) Global Result Register                                 */
  __I  uint32_t  RESERVED11[31];
  __IO uint32_t  GLOBRESD;                          /*!< (@ 0x48030380) Global Result Register, Debug                          */
} VADC_GLOBAL_TypeDef;


/* ================================================================================ */
/* ================                   SHS [SHS0]                   ================ */
/* ================================================================================ */


/**
  * @brief Sample and Hold ADC Sequencer (SHS)
  */

typedef struct {                                    /*!< (@ 0x48034000) SHS Structure                                          */
  __I  uint32_t  RESERVED0[2];
  __I  uint32_t  ID;                                /*!< (@ 0x48034008) Module Identification Register                         */
  __I  uint32_t  RESERVED1[13];
  __IO uint32_t  SHSCFG;                            /*!< (@ 0x48034040) SHS Configuration Register                             */
  __IO uint32_t  STEPCFG;                           /*!< (@ 0x48034044) Stepper Configuration Register                         */
  __I  uint32_t  RESERVED2[2];
  __IO uint32_t  LOOP;                              /*!< (@ 0x48034050) Loop Control Register                                  */
  __I  uint32_t  RESERVED3[11];
  __IO uint32_t  TIMCFG0;                           /*!< (@ 0x48034080) Timing Configuration Register 0                        */
  __IO uint32_t  TIMCFG1;                           /*!< (@ 0x48034084) Timing Configuration Register 1                        */
  __I  uint32_t  RESERVED4[13];
  __IO uint32_t  CALCTR;                            /*!< (@ 0x480340BC) Calibration Control Register                           */
  __IO uint32_t  CALGC0;                            /*!< (@ 0x480340C0) Gain Calibration Control Register 0                    */
  __IO uint32_t  CALGC1;                            /*!< (@ 0x480340C4) Gain Calibration Control Register 1                    */
  __I  uint32_t  RESERVED5[46];
  __IO uint32_t  GNCTR00;                           /*!< (@ 0x48034180) Gain Control Register 00                               */
  __I  uint32_t  RESERVED6[3];
  __IO uint32_t  GNCTR10;                           /*!< (@ 0x48034190) Gain Control Register 10                               */
} SHS_Type;


/* ================================================================================ */
/* ================                      PORT0                     ================ */
/* ================================================================================ */


/**
  * @brief Port 0 (PORT0)
  */

typedef struct {                                    /*!< (@ 0x40040000) PORT0 Structure                                        */
  __IO uint32_t  OUT;                               /*!< (@ 0x40040000) Port 0 Output Register                                 */
  __O  uint32_t  OMR;                               /*!< (@ 0x40040004) Port 0 Output Modification Register                    */
  __I  uint32_t  RESERVED0[2];
  __IO uint32_t  IOCR0;                             /*!< (@ 0x40040010) Port 0 Input/Output Control Register 0                 */
  __IO uint32_t  IOCR4;                             /*!< (@ 0x40040014) Port 0 Input/Output Control Register 4                 */
  __IO uint32_t  IOCR8;                             /*!< (@ 0x40040018) Port 0 Input/Output Control Register 8                 */
  __IO uint32_t  IOCR12;                            /*!< (@ 0x4004001C) Port 0 Input/Output Control Register 12                */
  __I  uint32_t  RESERVED1;
  __I  uint32_t  IN;                                /*!< (@ 0x40040024) Port 0 Input Register                                  */
  __I  uint32_t  RESERVED2[6];
  __IO uint32_t  PHCR0;                             /*!< (@ 0x40040040) Port 0 Pad Hysteresis Control Register 0               */
  __IO uint32_t  PHCR1;                             /*!< (@ 0x40040044) Port 0 Pad Hysteresis Control Register 1               */
  __I  uint32_t  RESERVED3[6];
  __I  uint32_t  PDISC;                             /*!< (@ 0x40040060) Port 0 Pin Function Decision Control Register          */
  __I  uint32_t  RESERVED4[3];
  __IO uint32_t  PPS;                               /*!< (@ 0x40040070) Port 0 Pin Power Save Register                         */
  __IO uint32_t  HWSEL;                             /*!< (@ 0x40040074) Port 0 Pin Hardware Select Register                    */
} PORT0_Type;


/* ================================================================================ */
/* ================                      PORT1                     ================ */
/* ================================================================================ */


/**
  * @brief Port 1 (PORT1)
  */

typedef struct {                                    /*!< (@ 0x40040100) PORT1 Structure                                        */
  __IO uint32_t  OUT;                               /*!< (@ 0x40040100) Port 1 Output Register                                 */
  __O  uint32_t  OMR;                               /*!< (@ 0x40040104) Port 1 Output Modification Register                    */
  __I  uint32_t  RESERVED0[2];
  __IO uint32_t  IOCR0;                             /*!< (@ 0x40040110) Port 1 Input/Output Control Register 0                 */
  __IO uint32_t  IOCR4;                             /*!< (@ 0x40040114) Port 1 Input/Output Control Register 4                 */
  __I  uint32_t  RESERVED1[3];
  __I  uint32_t  IN;                                /*!< (@ 0x40040124) Port 1 Input Register                                  */
  __I  uint32_t  RESERVED2[6];
  __IO uint32_t  PHCR0;                             /*!< (@ 0x40040140) Port 1 Pad Hysteresis Control Register 0               */
  __I  uint32_t  RESERVED3[7];
  __I  uint32_t  PDISC;                             /*!< (@ 0x40040160) Port 1 Pin Function Decision Control Register          */
  __I  uint32_t  RESERVED4[3];
  __IO uint32_t  PPS;                               /*!< (@ 0x40040170) Port 1 Pin Power Save Register                         */
  __IO uint32_t  HWSEL;                             /*!< (@ 0x40040174) Port 1 Pin Hardware Select Register                    */
} PORT1_Type;


/* ================================================================================ */
/* ================                      PORT2                     ================ */
/* ================================================================================ */


/**
  * @brief Port 2 (PORT2)
  */

typedef struct {                                    /*!< (@ 0x40040200) PORT2 Structure                                        */
  __IO uint32_t  OUT;                               /*!< (@ 0x40040200) Port 2 Output Register                                 */
  __O  uint32_t  OMR;                               /*!< (@ 0x40040204) Port 2 Output Modification Register                    */
  __I  uint32_t  RESERVED0[2];
  __IO uint32_t  IOCR0;                             /*!< (@ 0x40040210) Port 2 Input/Output Control Register 0                 */
  __IO uint32_t  IOCR4;                             /*!< (@ 0x40040214) Port 2 Input/Output Control Register 4                 */
  __IO uint32_t  IOCR8;                             /*!< (@ 0x40040218) Port 2 Input/Output Control Register 8                 */
  __I  uint32_t  RESERVED1[2];
  __I  uint32_t  IN;                                /*!< (@ 0x40040224) Port 2 Input Register                                  */
  __I  uint32_t  RESERVED2[6];
  __IO uint32_t  PHCR0;                             /*!< (@ 0x40040240) Port 2 Pad Hysteresis Control Register 0               */
  __IO uint32_t  PHCR1;                             /*!< (@ 0x40040244) Port 2 Pad Hysteresis Control Register 1               */
  __I  uint32_t  RESERVED3[6];
  __IO uint32_t  PDISC;                             /*!< (@ 0x40040260) Port 2 Pin Function Decision Control Register          */
  __I  uint32_t  RESERVED4[3];
  __IO uint32_t  PPS;                               /*!< (@ 0x40040270) Port 2 Pin Power Save Register                         */
  __IO uint32_t  HWSEL;                             /*!< (@ 0x40040274) Port 2 Pin Hardware Select Register                    */
} PORT2_Type;


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
/* ================          struct 'PPB' Position & Mask          ================ */
/* ================================================================================ */


/* --------------------------------  PPB_SYST_CSR  -------------------------------- */
#define PPB_SYST_CSR_ENABLE_Pos               0                                                       /*!< PPB SYST_CSR: ENABLE Position           */
#define PPB_SYST_CSR_ENABLE_Msk               (0x01UL << PPB_SYST_CSR_ENABLE_Pos)                     /*!< PPB SYST_CSR: ENABLE Mask               */
#define PPB_SYST_CSR_TICKINT_Pos              1                                                       /*!< PPB SYST_CSR: TICKINT Position          */
#define PPB_SYST_CSR_TICKINT_Msk              (0x01UL << PPB_SYST_CSR_TICKINT_Pos)                    /*!< PPB SYST_CSR: TICKINT Mask              */
#define PPB_SYST_CSR_CLKSOURCE_Pos            2                                                       /*!< PPB SYST_CSR: CLKSOURCE Position        */
#define PPB_SYST_CSR_CLKSOURCE_Msk            (0x01UL << PPB_SYST_CSR_CLKSOURCE_Pos)                  /*!< PPB SYST_CSR: CLKSOURCE Mask            */
#define PPB_SYST_CSR_COUNTFLAG_Pos            16                                                      /*!< PPB SYST_CSR: COUNTFLAG Position        */
#define PPB_SYST_CSR_COUNTFLAG_Msk            (0x01UL << PPB_SYST_CSR_COUNTFLAG_Pos)                  /*!< PPB SYST_CSR: COUNTFLAG Mask            */

/* --------------------------------  PPB_SYST_RVR  -------------------------------- */
#define PPB_SYST_RVR_RELOAD_Pos               0                                                       /*!< PPB SYST_RVR: RELOAD Position           */
#define PPB_SYST_RVR_RELOAD_Msk               (0x00ffffffUL << PPB_SYST_RVR_RELOAD_Pos)               /*!< PPB SYST_RVR: RELOAD Mask               */

/* --------------------------------  PPB_SYST_CVR  -------------------------------- */
#define PPB_SYST_CVR_CURRENT_Pos              0                                                       /*!< PPB SYST_CVR: CURRENT Position          */
#define PPB_SYST_CVR_CURRENT_Msk              (0x00ffffffUL << PPB_SYST_CVR_CURRENT_Pos)              /*!< PPB SYST_CVR: CURRENT Mask              */

/* -------------------------------  PPB_SYST_CALIB  ------------------------------- */
#define PPB_SYST_CALIB_TENMS_Pos              0                                                       /*!< PPB SYST_CALIB: TENMS Position          */
#define PPB_SYST_CALIB_TENMS_Msk              (0x00ffffffUL << PPB_SYST_CALIB_TENMS_Pos)              /*!< PPB SYST_CALIB: TENMS Mask              */
#define PPB_SYST_CALIB_SKEW_Pos               30                                                      /*!< PPB SYST_CALIB: SKEW Position           */
#define PPB_SYST_CALIB_SKEW_Msk               (0x01UL << PPB_SYST_CALIB_SKEW_Pos)                     /*!< PPB SYST_CALIB: SKEW Mask               */
#define PPB_SYST_CALIB_NOREF_Pos              31                                                      /*!< PPB SYST_CALIB: NOREF Position          */
#define PPB_SYST_CALIB_NOREF_Msk              (0x01UL << PPB_SYST_CALIB_NOREF_Pos)                    /*!< PPB SYST_CALIB: NOREF Mask              */

/* --------------------------------  PPB_NVIC_ISER  ------------------------------- */
#define PPB_NVIC_ISER_SETENA_Pos              0                                                       /*!< PPB NVIC_ISER: SETENA Position          */
#define PPB_NVIC_ISER_SETENA_Msk              (0xffffffffUL << PPB_NVIC_ISER_SETENA_Pos)              /*!< PPB NVIC_ISER: SETENA Mask              */

/* --------------------------------  PPB_NVIC_ICER  ------------------------------- */
#define PPB_NVIC_ICER_CLRENA_Pos              0                                                       /*!< PPB NVIC_ICER: CLRENA Position          */
#define PPB_NVIC_ICER_CLRENA_Msk              (0xffffffffUL << PPB_NVIC_ICER_CLRENA_Pos)              /*!< PPB NVIC_ICER: CLRENA Mask              */

/* --------------------------------  PPB_NVIC_ISPR  ------------------------------- */
#define PPB_NVIC_ISPR_SETPEND_Pos             0                                                       /*!< PPB NVIC_ISPR: SETPEND Position         */
#define PPB_NVIC_ISPR_SETPEND_Msk             (0xffffffffUL << PPB_NVIC_ISPR_SETPEND_Pos)             /*!< PPB NVIC_ISPR: SETPEND Mask             */

/* --------------------------------  PPB_NVIC_ICPR  ------------------------------- */
#define PPB_NVIC_ICPR_CLRPEND_Pos             0                                                       /*!< PPB NVIC_ICPR: CLRPEND Position         */
#define PPB_NVIC_ICPR_CLRPEND_Msk             (0xffffffffUL << PPB_NVIC_ICPR_CLRPEND_Pos)             /*!< PPB NVIC_ICPR: CLRPEND Mask             */

/* --------------------------------  PPB_NVIC_IPR0  ------------------------------- */
#define PPB_NVIC_IPR0_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR0: PRI_0 Position           */
#define PPB_NVIC_IPR0_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR0_PRI_0_Pos)               /*!< PPB NVIC_IPR0: PRI_0 Mask               */
#define PPB_NVIC_IPR0_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR0: PRI_1 Position           */
#define PPB_NVIC_IPR0_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR0_PRI_1_Pos)               /*!< PPB NVIC_IPR0: PRI_1 Mask               */
#define PPB_NVIC_IPR0_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR0: PRI_2 Position           */
#define PPB_NVIC_IPR0_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR0_PRI_2_Pos)               /*!< PPB NVIC_IPR0: PRI_2 Mask               */
#define PPB_NVIC_IPR0_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR0: PRI_3 Position           */
#define PPB_NVIC_IPR0_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR0_PRI_3_Pos)               /*!< PPB NVIC_IPR0: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR1  ------------------------------- */
#define PPB_NVIC_IPR1_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR1: PRI_0 Position           */
#define PPB_NVIC_IPR1_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR1_PRI_0_Pos)               /*!< PPB NVIC_IPR1: PRI_0 Mask               */
#define PPB_NVIC_IPR1_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR1: PRI_1 Position           */
#define PPB_NVIC_IPR1_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR1_PRI_1_Pos)               /*!< PPB NVIC_IPR1: PRI_1 Mask               */
#define PPB_NVIC_IPR1_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR1: PRI_2 Position           */
#define PPB_NVIC_IPR1_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR1_PRI_2_Pos)               /*!< PPB NVIC_IPR1: PRI_2 Mask               */
#define PPB_NVIC_IPR1_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR1: PRI_3 Position           */
#define PPB_NVIC_IPR1_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR1_PRI_3_Pos)               /*!< PPB NVIC_IPR1: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR2  ------------------------------- */
#define PPB_NVIC_IPR2_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR2: PRI_0 Position           */
#define PPB_NVIC_IPR2_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR2_PRI_0_Pos)               /*!< PPB NVIC_IPR2: PRI_0 Mask               */
#define PPB_NVIC_IPR2_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR2: PRI_1 Position           */
#define PPB_NVIC_IPR2_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR2_PRI_1_Pos)               /*!< PPB NVIC_IPR2: PRI_1 Mask               */
#define PPB_NVIC_IPR2_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR2: PRI_2 Position           */
#define PPB_NVIC_IPR2_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR2_PRI_2_Pos)               /*!< PPB NVIC_IPR2: PRI_2 Mask               */
#define PPB_NVIC_IPR2_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR2: PRI_3 Position           */
#define PPB_NVIC_IPR2_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR2_PRI_3_Pos)               /*!< PPB NVIC_IPR2: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR3  ------------------------------- */
#define PPB_NVIC_IPR3_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR3: PRI_0 Position           */
#define PPB_NVIC_IPR3_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR3_PRI_0_Pos)               /*!< PPB NVIC_IPR3: PRI_0 Mask               */
#define PPB_NVIC_IPR3_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR3: PRI_1 Position           */
#define PPB_NVIC_IPR3_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR3_PRI_1_Pos)               /*!< PPB NVIC_IPR3: PRI_1 Mask               */
#define PPB_NVIC_IPR3_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR3: PRI_2 Position           */
#define PPB_NVIC_IPR3_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR3_PRI_2_Pos)               /*!< PPB NVIC_IPR3: PRI_2 Mask               */
#define PPB_NVIC_IPR3_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR3: PRI_3 Position           */
#define PPB_NVIC_IPR3_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR3_PRI_3_Pos)               /*!< PPB NVIC_IPR3: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR4  ------------------------------- */
#define PPB_NVIC_IPR4_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR4: PRI_0 Position           */
#define PPB_NVIC_IPR4_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR4_PRI_0_Pos)               /*!< PPB NVIC_IPR4: PRI_0 Mask               */
#define PPB_NVIC_IPR4_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR4: PRI_1 Position           */
#define PPB_NVIC_IPR4_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR4_PRI_1_Pos)               /*!< PPB NVIC_IPR4: PRI_1 Mask               */
#define PPB_NVIC_IPR4_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR4: PRI_2 Position           */
#define PPB_NVIC_IPR4_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR4_PRI_2_Pos)               /*!< PPB NVIC_IPR4: PRI_2 Mask               */
#define PPB_NVIC_IPR4_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR4: PRI_3 Position           */
#define PPB_NVIC_IPR4_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR4_PRI_3_Pos)               /*!< PPB NVIC_IPR4: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR5  ------------------------------- */
#define PPB_NVIC_IPR5_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR5: PRI_0 Position           */
#define PPB_NVIC_IPR5_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR5_PRI_0_Pos)               /*!< PPB NVIC_IPR5: PRI_0 Mask               */
#define PPB_NVIC_IPR5_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR5: PRI_1 Position           */
#define PPB_NVIC_IPR5_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR5_PRI_1_Pos)               /*!< PPB NVIC_IPR5: PRI_1 Mask               */
#define PPB_NVIC_IPR5_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR5: PRI_2 Position           */
#define PPB_NVIC_IPR5_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR5_PRI_2_Pos)               /*!< PPB NVIC_IPR5: PRI_2 Mask               */
#define PPB_NVIC_IPR5_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR5: PRI_3 Position           */
#define PPB_NVIC_IPR5_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR5_PRI_3_Pos)               /*!< PPB NVIC_IPR5: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR6  ------------------------------- */
#define PPB_NVIC_IPR6_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR6: PRI_0 Position           */
#define PPB_NVIC_IPR6_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR6_PRI_0_Pos)               /*!< PPB NVIC_IPR6: PRI_0 Mask               */
#define PPB_NVIC_IPR6_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR6: PRI_1 Position           */
#define PPB_NVIC_IPR6_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR6_PRI_1_Pos)               /*!< PPB NVIC_IPR6: PRI_1 Mask               */
#define PPB_NVIC_IPR6_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR6: PRI_2 Position           */
#define PPB_NVIC_IPR6_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR6_PRI_2_Pos)               /*!< PPB NVIC_IPR6: PRI_2 Mask               */
#define PPB_NVIC_IPR6_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR6: PRI_3 Position           */
#define PPB_NVIC_IPR6_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR6_PRI_3_Pos)               /*!< PPB NVIC_IPR6: PRI_3 Mask               */

/* --------------------------------  PPB_NVIC_IPR7  ------------------------------- */
#define PPB_NVIC_IPR7_PRI_0_Pos               0                                                       /*!< PPB NVIC_IPR7: PRI_0 Position           */
#define PPB_NVIC_IPR7_PRI_0_Msk               (0x000000ffUL << PPB_NVIC_IPR7_PRI_0_Pos)               /*!< PPB NVIC_IPR7: PRI_0 Mask               */
#define PPB_NVIC_IPR7_PRI_1_Pos               8                                                       /*!< PPB NVIC_IPR7: PRI_1 Position           */
#define PPB_NVIC_IPR7_PRI_1_Msk               (0x000000ffUL << PPB_NVIC_IPR7_PRI_1_Pos)               /*!< PPB NVIC_IPR7: PRI_1 Mask               */
#define PPB_NVIC_IPR7_PRI_2_Pos               16                                                      /*!< PPB NVIC_IPR7: PRI_2 Position           */
#define PPB_NVIC_IPR7_PRI_2_Msk               (0x000000ffUL << PPB_NVIC_IPR7_PRI_2_Pos)               /*!< PPB NVIC_IPR7: PRI_2 Mask               */
#define PPB_NVIC_IPR7_PRI_3_Pos               24                                                      /*!< PPB NVIC_IPR7: PRI_3 Position           */
#define PPB_NVIC_IPR7_PRI_3_Msk               (0x000000ffUL << PPB_NVIC_IPR7_PRI_3_Pos)               /*!< PPB NVIC_IPR7: PRI_3 Mask               */

/* ----------------------------------  PPB_CPUID  --------------------------------- */
#define PPB_CPUID_Revision_Pos                0                                                       /*!< PPB CPUID: Revision Position            */
#define PPB_CPUID_Revision_Msk                (0x0fUL << PPB_CPUID_Revision_Pos)                      /*!< PPB CPUID: Revision Mask                */
#define PPB_CPUID_PartNo_Pos                  4                                                       /*!< PPB CPUID: PartNo Position              */
#define PPB_CPUID_PartNo_Msk                  (0x00000fffUL << PPB_CPUID_PartNo_Pos)                  /*!< PPB CPUID: PartNo Mask                  */
#define PPB_CPUID_Architecture_Pos            16                                                      /*!< PPB CPUID: Architecture Position        */
#define PPB_CPUID_Architecture_Msk            (0x0fUL << PPB_CPUID_Architecture_Pos)                  /*!< PPB CPUID: Architecture Mask            */
#define PPB_CPUID_Variant_Pos                 20                                                      /*!< PPB CPUID: Variant Position             */
#define PPB_CPUID_Variant_Msk                 (0x0fUL << PPB_CPUID_Variant_Pos)                       /*!< PPB CPUID: Variant Mask                 */
#define PPB_CPUID_Implementer_Pos             24                                                      /*!< PPB CPUID: Implementer Position         */
#define PPB_CPUID_Implementer_Msk             (0x000000ffUL << PPB_CPUID_Implementer_Pos)             /*!< PPB CPUID: Implementer Mask             */

/* ----------------------------------  PPB_ICSR  ---------------------------------- */
#define PPB_ICSR_VECTACTIVE_Pos               0                                                       /*!< PPB ICSR: VECTACTIVE Position           */
#define PPB_ICSR_VECTACTIVE_Msk               (0x3fUL << PPB_ICSR_VECTACTIVE_Pos)                     /*!< PPB ICSR: VECTACTIVE Mask               */
#define PPB_ICSR_VECTPENDING_Pos              12                                                      /*!< PPB ICSR: VECTPENDING Position          */
#define PPB_ICSR_VECTPENDING_Msk              (0x3fUL << PPB_ICSR_VECTPENDING_Pos)                    /*!< PPB ICSR: VECTPENDING Mask              */
#define PPB_ICSR_ISRPENDING_Pos               22                                                      /*!< PPB ICSR: ISRPENDING Position           */
#define PPB_ICSR_ISRPENDING_Msk               (0x01UL << PPB_ICSR_ISRPENDING_Pos)                     /*!< PPB ICSR: ISRPENDING Mask               */
#define PPB_ICSR_PENDSTCLR_Pos                25                                                      /*!< PPB ICSR: PENDSTCLR Position            */
#define PPB_ICSR_PENDSTCLR_Msk                (0x01UL << PPB_ICSR_PENDSTCLR_Pos)                      /*!< PPB ICSR: PENDSTCLR Mask                */
#define PPB_ICSR_PENDSTSET_Pos                26                                                      /*!< PPB ICSR: PENDSTSET Position            */
#define PPB_ICSR_PENDSTSET_Msk                (0x01UL << PPB_ICSR_PENDSTSET_Pos)                      /*!< PPB ICSR: PENDSTSET Mask                */
#define PPB_ICSR_PENDSVCLR_Pos                27                                                      /*!< PPB ICSR: PENDSVCLR Position            */
#define PPB_ICSR_PENDSVCLR_Msk                (0x01UL << PPB_ICSR_PENDSVCLR_Pos)                      /*!< PPB ICSR: PENDSVCLR Mask                */
#define PPB_ICSR_PENDSVSET_Pos                28                                                      /*!< PPB ICSR: PENDSVSET Position            */
#define PPB_ICSR_PENDSVSET_Msk                (0x01UL << PPB_ICSR_PENDSVSET_Pos)                      /*!< PPB ICSR: PENDSVSET Mask                */

/* ----------------------------------  PPB_AIRCR  --------------------------------- */
#define PPB_AIRCR_SYSRESETREQ_Pos             2                                                       /*!< PPB AIRCR: SYSRESETREQ Position         */
#define PPB_AIRCR_SYSRESETREQ_Msk             (0x01UL << PPB_AIRCR_SYSRESETREQ_Pos)                   /*!< PPB AIRCR: SYSRESETREQ Mask             */
#define PPB_AIRCR_ENDIANNESS_Pos              15                                                      /*!< PPB AIRCR: ENDIANNESS Position          */
#define PPB_AIRCR_ENDIANNESS_Msk              (0x01UL << PPB_AIRCR_ENDIANNESS_Pos)                    /*!< PPB AIRCR: ENDIANNESS Mask              */
#define PPB_AIRCR_VECTKEY_Pos                 16                                                      /*!< PPB AIRCR: VECTKEY Position             */
#define PPB_AIRCR_VECTKEY_Msk                 (0x0000ffffUL << PPB_AIRCR_VECTKEY_Pos)                 /*!< PPB AIRCR: VECTKEY Mask                 */

/* -----------------------------------  PPB_SCR  ---------------------------------- */
#define PPB_SCR_SLEEPONEXIT_Pos               1                                                       /*!< PPB SCR: SLEEPONEXIT Position           */
#define PPB_SCR_SLEEPONEXIT_Msk               (0x01UL << PPB_SCR_SLEEPONEXIT_Pos)                     /*!< PPB SCR: SLEEPONEXIT Mask               */
#define PPB_SCR_SLEEPDEEP_Pos                 2                                                       /*!< PPB SCR: SLEEPDEEP Position             */
#define PPB_SCR_SLEEPDEEP_Msk                 (0x01UL << PPB_SCR_SLEEPDEEP_Pos)                       /*!< PPB SCR: SLEEPDEEP Mask                 */
#define PPB_SCR_SEVONPEND_Pos                 4                                                       /*!< PPB SCR: SEVONPEND Position             */
#define PPB_SCR_SEVONPEND_Msk                 (0x01UL << PPB_SCR_SEVONPEND_Pos)                       /*!< PPB SCR: SEVONPEND Mask                 */

/* -----------------------------------  PPB_CCR  ---------------------------------- */
#define PPB_CCR_UNALIGN_TRP_Pos               3                                                       /*!< PPB CCR: UNALIGN_TRP Position           */
#define PPB_CCR_UNALIGN_TRP_Msk               (0x01UL << PPB_CCR_UNALIGN_TRP_Pos)                     /*!< PPB CCR: UNALIGN_TRP Mask               */
#define PPB_CCR_STKALIGN_Pos                  9                                                       /*!< PPB CCR: STKALIGN Position              */
#define PPB_CCR_STKALIGN_Msk                  (0x01UL << PPB_CCR_STKALIGN_Pos)                        /*!< PPB CCR: STKALIGN Mask                  */

/* ----------------------------------  PPB_SHPR2  --------------------------------- */
#define PPB_SHPR2_PRI_11_Pos                  24                                                      /*!< PPB SHPR2: PRI_11 Position              */
#define PPB_SHPR2_PRI_11_Msk                  (0x000000ffUL << PPB_SHPR2_PRI_11_Pos)                  /*!< PPB SHPR2: PRI_11 Mask                  */

/* ----------------------------------  PPB_SHPR3  --------------------------------- */
#define PPB_SHPR3_PRI_14_Pos                  16                                                      /*!< PPB SHPR3: PRI_14 Position              */
#define PPB_SHPR3_PRI_14_Msk                  (0x000000ffUL << PPB_SHPR3_PRI_14_Pos)                  /*!< PPB SHPR3: PRI_14 Mask                  */
#define PPB_SHPR3_PRI_15_Pos                  24                                                      /*!< PPB SHPR3: PRI_15 Position              */
#define PPB_SHPR3_PRI_15_Msk                  (0x000000ffUL << PPB_SHPR3_PRI_15_Pos)                  /*!< PPB SHPR3: PRI_15 Mask                  */

/* ----------------------------------  PPB_SHCSR  --------------------------------- */
#define PPB_SHCSR_SVCALLPENDED_Pos            15                                                      /*!< PPB SHCSR: SVCALLPENDED Position        */
#define PPB_SHCSR_SVCALLPENDED_Msk            (0x01UL << PPB_SHCSR_SVCALLPENDED_Pos)                  /*!< PPB SHCSR: SVCALLPENDED Mask            */


/* ================================================================================ */
/* ================           Group 'ERU' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  ERU_EXISEL  --------------------------------- */
#define ERU_EXISEL_EXS0A_Pos                  0                                                       /*!< ERU EXISEL: EXS0A Position              */
#define ERU_EXISEL_EXS0A_Msk                  (0x03UL << ERU_EXISEL_EXS0A_Pos)                        /*!< ERU EXISEL: EXS0A Mask                  */
#define ERU_EXISEL_EXS0B_Pos                  2                                                       /*!< ERU EXISEL: EXS0B Position              */
#define ERU_EXISEL_EXS0B_Msk                  (0x03UL << ERU_EXISEL_EXS0B_Pos)                        /*!< ERU EXISEL: EXS0B Mask                  */
#define ERU_EXISEL_EXS1A_Pos                  4                                                       /*!< ERU EXISEL: EXS1A Position              */
#define ERU_EXISEL_EXS1A_Msk                  (0x03UL << ERU_EXISEL_EXS1A_Pos)                        /*!< ERU EXISEL: EXS1A Mask                  */
#define ERU_EXISEL_EXS1B_Pos                  6                                                       /*!< ERU EXISEL: EXS1B Position              */
#define ERU_EXISEL_EXS1B_Msk                  (0x03UL << ERU_EXISEL_EXS1B_Pos)                        /*!< ERU EXISEL: EXS1B Mask                  */
#define ERU_EXISEL_EXS2A_Pos                  8                                                       /*!< ERU EXISEL: EXS2A Position              */
#define ERU_EXISEL_EXS2A_Msk                  (0x03UL << ERU_EXISEL_EXS2A_Pos)                        /*!< ERU EXISEL: EXS2A Mask                  */
#define ERU_EXISEL_EXS2B_Pos                  10                                                      /*!< ERU EXISEL: EXS2B Position              */
#define ERU_EXISEL_EXS2B_Msk                  (0x03UL << ERU_EXISEL_EXS2B_Pos)                        /*!< ERU EXISEL: EXS2B Mask                  */
#define ERU_EXISEL_EXS3A_Pos                  12                                                      /*!< ERU EXISEL: EXS3A Position              */
#define ERU_EXISEL_EXS3A_Msk                  (0x03UL << ERU_EXISEL_EXS3A_Pos)                        /*!< ERU EXISEL: EXS3A Mask                  */
#define ERU_EXISEL_EXS3B_Pos                  14                                                      /*!< ERU EXISEL: EXS3B Position              */
#define ERU_EXISEL_EXS3B_Msk                  (0x03UL << ERU_EXISEL_EXS3B_Pos)                        /*!< ERU EXISEL: EXS3B Mask                  */

/* ---------------------------------  ERU_EXICON  --------------------------------- */
#define ERU_EXICON_PE_Pos                     0                                                       /*!< ERU EXICON: PE Position                 */
#define ERU_EXICON_PE_Msk                     (0x01UL << ERU_EXICON_PE_Pos)                           /*!< ERU EXICON: PE Mask                     */
#define ERU_EXICON_LD_Pos                     1                                                       /*!< ERU EXICON: LD Position                 */
#define ERU_EXICON_LD_Msk                     (0x01UL << ERU_EXICON_LD_Pos)                           /*!< ERU EXICON: LD Mask                     */
#define ERU_EXICON_RE_Pos                     2                                                       /*!< ERU EXICON: RE Position                 */
#define ERU_EXICON_RE_Msk                     (0x01UL << ERU_EXICON_RE_Pos)                           /*!< ERU EXICON: RE Mask                     */
#define ERU_EXICON_FE_Pos                     3                                                       /*!< ERU EXICON: FE Position                 */
#define ERU_EXICON_FE_Msk                     (0x01UL << ERU_EXICON_FE_Pos)                           /*!< ERU EXICON: FE Mask                     */
#define ERU_EXICON_OCS_Pos                    4                                                       /*!< ERU EXICON: OCS Position                */
#define ERU_EXICON_OCS_Msk                    (0x07UL << ERU_EXICON_OCS_Pos)                          /*!< ERU EXICON: OCS Mask                    */
#define ERU_EXICON_FL_Pos                     7                                                       /*!< ERU EXICON: FL Position                 */
#define ERU_EXICON_FL_Msk                     (0x01UL << ERU_EXICON_FL_Pos)                           /*!< ERU EXICON: FL Mask                     */
#define ERU_EXICON_SS_Pos                     8                                                       /*!< ERU EXICON: SS Position                 */
#define ERU_EXICON_SS_Msk                     (0x03UL << ERU_EXICON_SS_Pos)                           /*!< ERU EXICON: SS Mask                     */
#define ERU_EXICON_NA_Pos                     10                                                      /*!< ERU EXICON: NA Position                 */
#define ERU_EXICON_NA_Msk                     (0x01UL << ERU_EXICON_NA_Pos)                           /*!< ERU EXICON: NA Mask                     */
#define ERU_EXICON_NB_Pos                     11                                                      /*!< ERU EXICON: NB Position                 */
#define ERU_EXICON_NB_Msk                     (0x01UL << ERU_EXICON_NB_Pos)                           /*!< ERU EXICON: NB Mask                     */

/* ---------------------------------  ERU_EXOCON  --------------------------------- */
#define ERU_EXOCON_ISS_Pos                    0                                                       /*!< ERU EXOCON: ISS Position                */
#define ERU_EXOCON_ISS_Msk                    (0x03UL << ERU_EXOCON_ISS_Pos)                          /*!< ERU EXOCON: ISS Mask                    */
#define ERU_EXOCON_GEEN_Pos                   2                                                       /*!< ERU EXOCON: GEEN Position               */
#define ERU_EXOCON_GEEN_Msk                   (0x01UL << ERU_EXOCON_GEEN_Pos)                         /*!< ERU EXOCON: GEEN Mask                   */
#define ERU_EXOCON_PDR_Pos                    3                                                       /*!< ERU EXOCON: PDR Position                */
#define ERU_EXOCON_PDR_Msk                    (0x01UL << ERU_EXOCON_PDR_Pos)                          /*!< ERU EXOCON: PDR Mask                    */
#define ERU_EXOCON_GP_Pos                     4                                                       /*!< ERU EXOCON: GP Position                 */
#define ERU_EXOCON_GP_Msk                     (0x03UL << ERU_EXOCON_GP_Pos)                           /*!< ERU EXOCON: GP Mask                     */
#define ERU_EXOCON_IPEN0_Pos                  12                                                      /*!< ERU EXOCON: IPEN0 Position              */
#define ERU_EXOCON_IPEN0_Msk                  (0x01UL << ERU_EXOCON_IPEN0_Pos)                        /*!< ERU EXOCON: IPEN0 Mask                  */
#define ERU_EXOCON_IPEN1_Pos                  13                                                      /*!< ERU EXOCON: IPEN1 Position              */
#define ERU_EXOCON_IPEN1_Msk                  (0x01UL << ERU_EXOCON_IPEN1_Pos)                        /*!< ERU EXOCON: IPEN1 Mask                  */
#define ERU_EXOCON_IPEN2_Pos                  14                                                      /*!< ERU EXOCON: IPEN2 Position              */
#define ERU_EXOCON_IPEN2_Msk                  (0x01UL << ERU_EXOCON_IPEN2_Pos)                        /*!< ERU EXOCON: IPEN2 Mask                  */
#define ERU_EXOCON_IPEN3_Pos                  15                                                      /*!< ERU EXOCON: IPEN3 Position              */
#define ERU_EXOCON_IPEN3_Msk                  (0x01UL << ERU_EXOCON_IPEN3_Pos)                        /*!< ERU EXOCON: IPEN3 Mask                  */


/* ================================================================================ */
/* ================          struct 'PAU' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  PAU_AVAIL0  --------------------------------- */
#define PAU_AVAIL0_AVAIL22_Pos                22                                                      /*!< PAU AVAIL0: AVAIL22 Position            */
#define PAU_AVAIL0_AVAIL22_Msk                (0x01UL << PAU_AVAIL0_AVAIL22_Pos)                      /*!< PAU AVAIL0: AVAIL22 Mask                */
#define PAU_AVAIL0_AVAIL23_Pos                23                                                      /*!< PAU AVAIL0: AVAIL23 Position            */
#define PAU_AVAIL0_AVAIL23_Msk                (0x01UL << PAU_AVAIL0_AVAIL23_Pos)                      /*!< PAU AVAIL0: AVAIL23 Mask                */
#define PAU_AVAIL0_AVAIL24_Pos                24                                                      /*!< PAU AVAIL0: AVAIL24 Position            */
#define PAU_AVAIL0_AVAIL24_Msk                (0x01UL << PAU_AVAIL0_AVAIL24_Pos)                      /*!< PAU AVAIL0: AVAIL24 Mask                */

/* ---------------------------------  PAU_AVAIL1  --------------------------------- */
#define PAU_AVAIL1_AVAIL0_Pos                 0                                                       /*!< PAU AVAIL1: AVAIL0 Position             */
#define PAU_AVAIL1_AVAIL0_Msk                 (0x01UL << PAU_AVAIL1_AVAIL0_Pos)                       /*!< PAU AVAIL1: AVAIL0 Mask                 */
#define PAU_AVAIL1_AVAIL1_Pos                 1                                                       /*!< PAU AVAIL1: AVAIL1 Position             */
#define PAU_AVAIL1_AVAIL1_Msk                 (0x01UL << PAU_AVAIL1_AVAIL1_Pos)                       /*!< PAU AVAIL1: AVAIL1 Mask                 */
#define PAU_AVAIL1_AVAIL4_Pos                 4                                                       /*!< PAU AVAIL1: AVAIL4 Position             */
#define PAU_AVAIL1_AVAIL4_Msk                 (0x01UL << PAU_AVAIL1_AVAIL4_Pos)                       /*!< PAU AVAIL1: AVAIL4 Mask                 */
#define PAU_AVAIL1_AVAIL5_Pos                 5                                                       /*!< PAU AVAIL1: AVAIL5 Position             */
#define PAU_AVAIL1_AVAIL5_Msk                 (0x01UL << PAU_AVAIL1_AVAIL5_Pos)                       /*!< PAU AVAIL1: AVAIL5 Mask                 */
#define PAU_AVAIL1_AVAIL8_Pos                 8                                                       /*!< PAU AVAIL1: AVAIL8 Position             */
#define PAU_AVAIL1_AVAIL8_Msk                 (0x01UL << PAU_AVAIL1_AVAIL8_Pos)                       /*!< PAU AVAIL1: AVAIL8 Mask                 */
#define PAU_AVAIL1_AVAIL9_Pos                 9                                                       /*!< PAU AVAIL1: AVAIL9 Position             */
#define PAU_AVAIL1_AVAIL9_Msk                 (0x01UL << PAU_AVAIL1_AVAIL9_Pos)                       /*!< PAU AVAIL1: AVAIL9 Mask                 */
#define PAU_AVAIL1_AVAIL10_Pos                10                                                      /*!< PAU AVAIL1: AVAIL10 Position            */
#define PAU_AVAIL1_AVAIL10_Msk                (0x01UL << PAU_AVAIL1_AVAIL10_Pos)                      /*!< PAU AVAIL1: AVAIL10 Mask                */
#define PAU_AVAIL1_AVAIL11_Pos                11                                                      /*!< PAU AVAIL1: AVAIL11 Position            */
#define PAU_AVAIL1_AVAIL11_Msk                (0x01UL << PAU_AVAIL1_AVAIL11_Pos)                      /*!< PAU AVAIL1: AVAIL11 Mask                */
#define PAU_AVAIL1_AVAIL12_Pos                12                                                      /*!< PAU AVAIL1: AVAIL12 Position            */
#define PAU_AVAIL1_AVAIL12_Msk                (0x01UL << PAU_AVAIL1_AVAIL12_Pos)                      /*!< PAU AVAIL1: AVAIL12 Mask                */

/* --------------------------------  PAU_PRIVDIS0  -------------------------------- */
#define PAU_PRIVDIS0_PDIS2_Pos                2                                                       /*!< PAU PRIVDIS0: PDIS2 Position            */
#define PAU_PRIVDIS0_PDIS2_Msk                (0x01UL << PAU_PRIVDIS0_PDIS2_Pos)                      /*!< PAU PRIVDIS0: PDIS2 Mask                */
#define PAU_PRIVDIS0_PDIS5_Pos                5                                                       /*!< PAU PRIVDIS0: PDIS5 Position            */
#define PAU_PRIVDIS0_PDIS5_Msk                (0x01UL << PAU_PRIVDIS0_PDIS5_Pos)                      /*!< PAU PRIVDIS0: PDIS5 Mask                */
#define PAU_PRIVDIS0_PDIS6_Pos                6                                                       /*!< PAU PRIVDIS0: PDIS6 Position            */
#define PAU_PRIVDIS0_PDIS6_Msk                (0x01UL << PAU_PRIVDIS0_PDIS6_Pos)                      /*!< PAU PRIVDIS0: PDIS6 Mask                */
#define PAU_PRIVDIS0_PDIS7_Pos                7                                                       /*!< PAU PRIVDIS0: PDIS7 Position            */
#define PAU_PRIVDIS0_PDIS7_Msk                (0x01UL << PAU_PRIVDIS0_PDIS7_Pos)                      /*!< PAU PRIVDIS0: PDIS7 Mask                */
#define PAU_PRIVDIS0_PDIS19_Pos               19                                                      /*!< PAU PRIVDIS0: PDIS19 Position           */
#define PAU_PRIVDIS0_PDIS19_Msk               (0x01UL << PAU_PRIVDIS0_PDIS19_Pos)                     /*!< PAU PRIVDIS0: PDIS19 Mask               */
#define PAU_PRIVDIS0_PDIS22_Pos               22                                                      /*!< PAU PRIVDIS0: PDIS22 Position           */
#define PAU_PRIVDIS0_PDIS22_Msk               (0x01UL << PAU_PRIVDIS0_PDIS22_Pos)                     /*!< PAU PRIVDIS0: PDIS22 Mask               */
#define PAU_PRIVDIS0_PDIS23_Pos               23                                                      /*!< PAU PRIVDIS0: PDIS23 Position           */
#define PAU_PRIVDIS0_PDIS23_Msk               (0x01UL << PAU_PRIVDIS0_PDIS23_Pos)                     /*!< PAU PRIVDIS0: PDIS23 Mask               */
#define PAU_PRIVDIS0_PDIS24_Pos               24                                                      /*!< PAU PRIVDIS0: PDIS24 Position           */
#define PAU_PRIVDIS0_PDIS24_Msk               (0x01UL << PAU_PRIVDIS0_PDIS24_Pos)                     /*!< PAU PRIVDIS0: PDIS24 Mask               */

/* --------------------------------  PAU_PRIVDIS1  -------------------------------- */
#define PAU_PRIVDIS1_PDIS0_Pos                0                                                       /*!< PAU PRIVDIS1: PDIS0 Position            */
#define PAU_PRIVDIS1_PDIS0_Msk                (0x01UL << PAU_PRIVDIS1_PDIS0_Pos)                      /*!< PAU PRIVDIS1: PDIS0 Mask                */
#define PAU_PRIVDIS1_PDIS1_Pos                1                                                       /*!< PAU PRIVDIS1: PDIS1 Position            */
#define PAU_PRIVDIS1_PDIS1_Msk                (0x01UL << PAU_PRIVDIS1_PDIS1_Pos)                      /*!< PAU PRIVDIS1: PDIS1 Mask                */
#define PAU_PRIVDIS1_PDIS5_Pos                5                                                       /*!< PAU PRIVDIS1: PDIS5 Position            */
#define PAU_PRIVDIS1_PDIS5_Msk                (0x01UL << PAU_PRIVDIS1_PDIS5_Pos)                      /*!< PAU PRIVDIS1: PDIS5 Mask                */
#define PAU_PRIVDIS1_PDIS8_Pos                8                                                       /*!< PAU PRIVDIS1: PDIS8 Position            */
#define PAU_PRIVDIS1_PDIS8_Msk                (0x01UL << PAU_PRIVDIS1_PDIS8_Pos)                      /*!< PAU PRIVDIS1: PDIS8 Mask                */
#define PAU_PRIVDIS1_PDIS9_Pos                9                                                       /*!< PAU PRIVDIS1: PDIS9 Position            */
#define PAU_PRIVDIS1_PDIS9_Msk                (0x01UL << PAU_PRIVDIS1_PDIS9_Pos)                      /*!< PAU PRIVDIS1: PDIS9 Mask                */
#define PAU_PRIVDIS1_PDIS10_Pos               10                                                      /*!< PAU PRIVDIS1: PDIS10 Position           */
#define PAU_PRIVDIS1_PDIS10_Msk               (0x01UL << PAU_PRIVDIS1_PDIS10_Pos)                     /*!< PAU PRIVDIS1: PDIS10 Mask               */
#define PAU_PRIVDIS1_PDIS11_Pos               11                                                      /*!< PAU PRIVDIS1: PDIS11 Position           */
#define PAU_PRIVDIS1_PDIS11_Msk               (0x01UL << PAU_PRIVDIS1_PDIS11_Pos)                     /*!< PAU PRIVDIS1: PDIS11 Mask               */
#define PAU_PRIVDIS1_PDIS12_Pos               12                                                      /*!< PAU PRIVDIS1: PDIS12 Position           */
#define PAU_PRIVDIS1_PDIS12_Msk               (0x01UL << PAU_PRIVDIS1_PDIS12_Pos)                     /*!< PAU PRIVDIS1: PDIS12 Mask               */

/* ---------------------------------  PAU_ROMSIZE  -------------------------------- */
#define PAU_ROMSIZE_ADDR_Pos                  8                                                       /*!< PAU ROMSIZE: ADDR Position              */
#define PAU_ROMSIZE_ADDR_Msk                  (0x3fUL << PAU_ROMSIZE_ADDR_Pos)                        /*!< PAU ROMSIZE: ADDR Mask                  */

/* ---------------------------------  PAU_FLSIZE  --------------------------------- */
#define PAU_FLSIZE_ADDR_Pos                   12                                                      /*!< PAU FLSIZE: ADDR Position               */
#define PAU_FLSIZE_ADDR_Msk                   (0x3fUL << PAU_FLSIZE_ADDR_Pos)                         /*!< PAU FLSIZE: ADDR Mask                   */

/* --------------------------------  PAU_RAM0SIZE  -------------------------------- */
#define PAU_RAM0SIZE_ADDR_Pos                 8                                                       /*!< PAU RAM0SIZE: ADDR Position             */
#define PAU_RAM0SIZE_ADDR_Msk                 (0x1fUL << PAU_RAM0SIZE_ADDR_Pos)                       /*!< PAU RAM0SIZE: ADDR Mask                 */


/* ================================================================================ */
/* ================          struct 'NVM' Position & Mask          ================ */
/* ================================================================================ */


/* --------------------------------  NVM_NVMSTATUS  ------------------------------- */
#define NVM_NVMSTATUS_BUSY_Pos                0                                                       /*!< NVM NVMSTATUS: BUSY Position            */
#define NVM_NVMSTATUS_BUSY_Msk                (0x01UL << NVM_NVMSTATUS_BUSY_Pos)                      /*!< NVM NVMSTATUS: BUSY Mask                */
#define NVM_NVMSTATUS_SLEEP_Pos               1                                                       /*!< NVM NVMSTATUS: SLEEP Position           */
#define NVM_NVMSTATUS_SLEEP_Msk               (0x01UL << NVM_NVMSTATUS_SLEEP_Pos)                     /*!< NVM NVMSTATUS: SLEEP Mask               */
#define NVM_NVMSTATUS_VERR_Pos                2                                                       /*!< NVM NVMSTATUS: VERR Position            */
#define NVM_NVMSTATUS_VERR_Msk                (0x03UL << NVM_NVMSTATUS_VERR_Pos)                      /*!< NVM NVMSTATUS: VERR Mask                */
#define NVM_NVMSTATUS_ECC1READ_Pos            4                                                       /*!< NVM NVMSTATUS: ECC1READ Position        */
#define NVM_NVMSTATUS_ECC1READ_Msk            (0x01UL << NVM_NVMSTATUS_ECC1READ_Pos)                  /*!< NVM NVMSTATUS: ECC1READ Mask            */
#define NVM_NVMSTATUS_ECC2READ_Pos            5                                                       /*!< NVM NVMSTATUS: ECC2READ Position        */
#define NVM_NVMSTATUS_ECC2READ_Msk            (0x01UL << NVM_NVMSTATUS_ECC2READ_Pos)                  /*!< NVM NVMSTATUS: ECC2READ Mask            */
#define NVM_NVMSTATUS_WRPERR_Pos              6                                                       /*!< NVM NVMSTATUS: WRPERR Position          */
#define NVM_NVMSTATUS_WRPERR_Msk              (0x01UL << NVM_NVMSTATUS_WRPERR_Pos)                    /*!< NVM NVMSTATUS: WRPERR Mask              */

/* ---------------------------------  NVM_NVMPROG  -------------------------------- */
#define NVM_NVMPROG_ACTION_Pos                0                                                       /*!< NVM NVMPROG: ACTION Position            */
#define NVM_NVMPROG_ACTION_Msk                (0x000000ffUL << NVM_NVMPROG_ACTION_Pos)                /*!< NVM NVMPROG: ACTION Mask                */
#define NVM_NVMPROG_RSTVERR_Pos               12                                                      /*!< NVM NVMPROG: RSTVERR Position           */
#define NVM_NVMPROG_RSTVERR_Msk               (0x01UL << NVM_NVMPROG_RSTVERR_Pos)                     /*!< NVM NVMPROG: RSTVERR Mask               */
#define NVM_NVMPROG_RSTECC_Pos                13                                                      /*!< NVM NVMPROG: RSTECC Position            */
#define NVM_NVMPROG_RSTECC_Msk                (0x01UL << NVM_NVMPROG_RSTECC_Pos)                      /*!< NVM NVMPROG: RSTECC Mask                */

/* ---------------------------------  NVM_NVMCONF  -------------------------------- */
#define NVM_NVMCONF_HRLEV_Pos                 1                                                       /*!< NVM NVMCONF: HRLEV Position             */
#define NVM_NVMCONF_HRLEV_Msk                 (0x03UL << NVM_NVMCONF_HRLEV_Pos)                       /*!< NVM NVMCONF: HRLEV Mask                 */
#define NVM_NVMCONF_SECPROT_Pos               4                                                       /*!< NVM NVMCONF: SECPROT Position           */
#define NVM_NVMCONF_SECPROT_Msk               (0x000000ffUL << NVM_NVMCONF_SECPROT_Pos)               /*!< NVM NVMCONF: SECPROT Mask               */
#define NVM_NVMCONF_INT_ON_Pos                14                                                      /*!< NVM NVMCONF: INT_ON Position            */
#define NVM_NVMCONF_INT_ON_Msk                (0x01UL << NVM_NVMCONF_INT_ON_Pos)                      /*!< NVM NVMCONF: INT_ON Mask                */
#define NVM_NVMCONF_NVM_ON_Pos                15                                                      /*!< NVM NVMCONF: NVM_ON Position            */
#define NVM_NVMCONF_NVM_ON_Msk                (0x01UL << NVM_NVMCONF_NVM_ON_Pos)                      /*!< NVM NVMCONF: NVM_ON Mask                */


/* ================================================================================ */
/* ================          struct 'WDT' Position & Mask          ================ */
/* ================================================================================ */


/* -----------------------------------  WDT_ID  ----------------------------------- */
#define WDT_ID_MOD_REV_Pos                    0                                                       /*!< WDT ID: MOD_REV Position                */
#define WDT_ID_MOD_REV_Msk                    (0x000000ffUL << WDT_ID_MOD_REV_Pos)                    /*!< WDT ID: MOD_REV Mask                    */
#define WDT_ID_MOD_TYPE_Pos                   8                                                       /*!< WDT ID: MOD_TYPE Position               */
#define WDT_ID_MOD_TYPE_Msk                   (0x000000ffUL << WDT_ID_MOD_TYPE_Pos)                   /*!< WDT ID: MOD_TYPE Mask                   */
#define WDT_ID_MOD_NUMBER_Pos                 16                                                      /*!< WDT ID: MOD_NUMBER Position             */
#define WDT_ID_MOD_NUMBER_Msk                 (0x0000ffffUL << WDT_ID_MOD_NUMBER_Pos)                 /*!< WDT ID: MOD_NUMBER Mask                 */

/* -----------------------------------  WDT_CTR  ---------------------------------- */
#define WDT_CTR_ENB_Pos                       0                                                       /*!< WDT CTR: ENB Position                   */
#define WDT_CTR_ENB_Msk                       (0x01UL << WDT_CTR_ENB_Pos)                             /*!< WDT CTR: ENB Mask                       */
#define WDT_CTR_PRE_Pos                       1                                                       /*!< WDT CTR: PRE Position                   */
#define WDT_CTR_PRE_Msk                       (0x01UL << WDT_CTR_PRE_Pos)                             /*!< WDT CTR: PRE Mask                       */
#define WDT_CTR_DSP_Pos                       4                                                       /*!< WDT CTR: DSP Position                   */
#define WDT_CTR_DSP_Msk                       (0x01UL << WDT_CTR_DSP_Pos)                             /*!< WDT CTR: DSP Mask                       */
#define WDT_CTR_SPW_Pos                       8                                                       /*!< WDT CTR: SPW Position                   */
#define WDT_CTR_SPW_Msk                       (0x000000ffUL << WDT_CTR_SPW_Pos)                       /*!< WDT CTR: SPW Mask                       */

/* -----------------------------------  WDT_SRV  ---------------------------------- */
#define WDT_SRV_SRV_Pos                       0                                                       /*!< WDT SRV: SRV Position                   */
#define WDT_SRV_SRV_Msk                       (0xffffffffUL << WDT_SRV_SRV_Pos)                       /*!< WDT SRV: SRV Mask                       */

/* -----------------------------------  WDT_TIM  ---------------------------------- */
#define WDT_TIM_TIM_Pos                       0                                                       /*!< WDT TIM: TIM Position                   */
#define WDT_TIM_TIM_Msk                       (0xffffffffUL << WDT_TIM_TIM_Pos)                       /*!< WDT TIM: TIM Mask                       */

/* -----------------------------------  WDT_WLB  ---------------------------------- */
#define WDT_WLB_WLB_Pos                       0                                                       /*!< WDT WLB: WLB Position                   */
#define WDT_WLB_WLB_Msk                       (0xffffffffUL << WDT_WLB_WLB_Pos)                       /*!< WDT WLB: WLB Mask                       */

/* -----------------------------------  WDT_WUB  ---------------------------------- */
#define WDT_WUB_WUB_Pos                       0                                                       /*!< WDT WUB: WUB Position                   */
#define WDT_WUB_WUB_Msk                       (0xffffffffUL << WDT_WUB_WUB_Pos)                       /*!< WDT WUB: WUB Mask                       */

/* ---------------------------------  WDT_WDTSTS  --------------------------------- */
#define WDT_WDTSTS_ALMS_Pos                   0                                                       /*!< WDT WDTSTS: ALMS Position               */
#define WDT_WDTSTS_ALMS_Msk                   (0x01UL << WDT_WDTSTS_ALMS_Pos)                         /*!< WDT WDTSTS: ALMS Mask                   */

/* ---------------------------------  WDT_WDTCLR  --------------------------------- */
#define WDT_WDTCLR_ALMC_Pos                   0                                                       /*!< WDT WDTCLR: ALMC Position               */
#define WDT_WDTCLR_ALMC_Msk                   (0x01UL << WDT_WDTCLR_ALMC_Pos)                         /*!< WDT WDTCLR: ALMC Mask                   */


/* ================================================================================ */
/* ================          struct 'RTC' Position & Mask          ================ */
/* ================================================================================ */


/* -----------------------------------  RTC_ID  ----------------------------------- */
#define RTC_ID_MOD_REV_Pos                    0                                                       /*!< RTC ID: MOD_REV Position                */
#define RTC_ID_MOD_REV_Msk                    (0x000000ffUL << RTC_ID_MOD_REV_Pos)                    /*!< RTC ID: MOD_REV Mask                    */
#define RTC_ID_MOD_TYPE_Pos                   8                                                       /*!< RTC ID: MOD_TYPE Position               */
#define RTC_ID_MOD_TYPE_Msk                   (0x000000ffUL << RTC_ID_MOD_TYPE_Pos)                   /*!< RTC ID: MOD_TYPE Mask                   */
#define RTC_ID_MOD_NUMBER_Pos                 16                                                      /*!< RTC ID: MOD_NUMBER Position             */
#define RTC_ID_MOD_NUMBER_Msk                 (0x0000ffffUL << RTC_ID_MOD_NUMBER_Pos)                 /*!< RTC ID: MOD_NUMBER Mask                 */

/* -----------------------------------  RTC_CTR  ---------------------------------- */
#define RTC_CTR_ENB_Pos                       0                                                       /*!< RTC CTR: ENB Position                   */
#define RTC_CTR_ENB_Msk                       (0x01UL << RTC_CTR_ENB_Pos)                             /*!< RTC CTR: ENB Mask                       */
#define RTC_CTR_SUS_Pos                       1                                                       /*!< RTC CTR: SUS Position                   */
#define RTC_CTR_SUS_Msk                       (0x01UL << RTC_CTR_SUS_Pos)                             /*!< RTC CTR: SUS Mask                       */
#define RTC_CTR_DIV_Pos                       16                                                      /*!< RTC CTR: DIV Position                   */
#define RTC_CTR_DIV_Msk                       (0x0000ffffUL << RTC_CTR_DIV_Pos)                       /*!< RTC CTR: DIV Mask                       */

/* ---------------------------------  RTC_RAWSTAT  -------------------------------- */
#define RTC_RAWSTAT_RPSE_Pos                  0                                                       /*!< RTC RAWSTAT: RPSE Position              */
#define RTC_RAWSTAT_RPSE_Msk                  (0x01UL << RTC_RAWSTAT_RPSE_Pos)                        /*!< RTC RAWSTAT: RPSE Mask                  */
#define RTC_RAWSTAT_RPMI_Pos                  1                                                       /*!< RTC RAWSTAT: RPMI Position              */
#define RTC_RAWSTAT_RPMI_Msk                  (0x01UL << RTC_RAWSTAT_RPMI_Pos)                        /*!< RTC RAWSTAT: RPMI Mask                  */
#define RTC_RAWSTAT_RPHO_Pos                  2                                                       /*!< RTC RAWSTAT: RPHO Position              */
#define RTC_RAWSTAT_RPHO_Msk                  (0x01UL << RTC_RAWSTAT_RPHO_Pos)                        /*!< RTC RAWSTAT: RPHO Mask                  */
#define RTC_RAWSTAT_RPDA_Pos                  3                                                       /*!< RTC RAWSTAT: RPDA Position              */
#define RTC_RAWSTAT_RPDA_Msk                  (0x01UL << RTC_RAWSTAT_RPDA_Pos)                        /*!< RTC RAWSTAT: RPDA Mask                  */
#define RTC_RAWSTAT_RPMO_Pos                  5                                                       /*!< RTC RAWSTAT: RPMO Position              */
#define RTC_RAWSTAT_RPMO_Msk                  (0x01UL << RTC_RAWSTAT_RPMO_Pos)                        /*!< RTC RAWSTAT: RPMO Mask                  */
#define RTC_RAWSTAT_RPYE_Pos                  6                                                       /*!< RTC RAWSTAT: RPYE Position              */
#define RTC_RAWSTAT_RPYE_Msk                  (0x01UL << RTC_RAWSTAT_RPYE_Pos)                        /*!< RTC RAWSTAT: RPYE Mask                  */
#define RTC_RAWSTAT_RAI_Pos                   8                                                       /*!< RTC RAWSTAT: RAI Position               */
#define RTC_RAWSTAT_RAI_Msk                   (0x01UL << RTC_RAWSTAT_RAI_Pos)                         /*!< RTC RAWSTAT: RAI Mask                   */

/* ----------------------------------  RTC_STSSR  --------------------------------- */
#define RTC_STSSR_SPSE_Pos                    0                                                       /*!< RTC STSSR: SPSE Position                */
#define RTC_STSSR_SPSE_Msk                    (0x01UL << RTC_STSSR_SPSE_Pos)                          /*!< RTC STSSR: SPSE Mask                    */
#define RTC_STSSR_SPMI_Pos                    1                                                       /*!< RTC STSSR: SPMI Position                */
#define RTC_STSSR_SPMI_Msk                    (0x01UL << RTC_STSSR_SPMI_Pos)                          /*!< RTC STSSR: SPMI Mask                    */
#define RTC_STSSR_SPHO_Pos                    2                                                       /*!< RTC STSSR: SPHO Position                */
#define RTC_STSSR_SPHO_Msk                    (0x01UL << RTC_STSSR_SPHO_Pos)                          /*!< RTC STSSR: SPHO Mask                    */
#define RTC_STSSR_SPDA_Pos                    3                                                       /*!< RTC STSSR: SPDA Position                */
#define RTC_STSSR_SPDA_Msk                    (0x01UL << RTC_STSSR_SPDA_Pos)                          /*!< RTC STSSR: SPDA Mask                    */
#define RTC_STSSR_SPMO_Pos                    5                                                       /*!< RTC STSSR: SPMO Position                */
#define RTC_STSSR_SPMO_Msk                    (0x01UL << RTC_STSSR_SPMO_Pos)                          /*!< RTC STSSR: SPMO Mask                    */
#define RTC_STSSR_SPYE_Pos                    6                                                       /*!< RTC STSSR: SPYE Position                */
#define RTC_STSSR_SPYE_Msk                    (0x01UL << RTC_STSSR_SPYE_Pos)                          /*!< RTC STSSR: SPYE Mask                    */
#define RTC_STSSR_SAI_Pos                     8                                                       /*!< RTC STSSR: SAI Position                 */
#define RTC_STSSR_SAI_Msk                     (0x01UL << RTC_STSSR_SAI_Pos)                           /*!< RTC STSSR: SAI Mask                     */

/* ----------------------------------  RTC_MSKSR  --------------------------------- */
#define RTC_MSKSR_MPSE_Pos                    0                                                       /*!< RTC MSKSR: MPSE Position                */
#define RTC_MSKSR_MPSE_Msk                    (0x01UL << RTC_MSKSR_MPSE_Pos)                          /*!< RTC MSKSR: MPSE Mask                    */
#define RTC_MSKSR_MPMI_Pos                    1                                                       /*!< RTC MSKSR: MPMI Position                */
#define RTC_MSKSR_MPMI_Msk                    (0x01UL << RTC_MSKSR_MPMI_Pos)                          /*!< RTC MSKSR: MPMI Mask                    */
#define RTC_MSKSR_MPHO_Pos                    2                                                       /*!< RTC MSKSR: MPHO Position                */
#define RTC_MSKSR_MPHO_Msk                    (0x01UL << RTC_MSKSR_MPHO_Pos)                          /*!< RTC MSKSR: MPHO Mask                    */
#define RTC_MSKSR_MPDA_Pos                    3                                                       /*!< RTC MSKSR: MPDA Position                */
#define RTC_MSKSR_MPDA_Msk                    (0x01UL << RTC_MSKSR_MPDA_Pos)                          /*!< RTC MSKSR: MPDA Mask                    */
#define RTC_MSKSR_MPMO_Pos                    5                                                       /*!< RTC MSKSR: MPMO Position                */
#define RTC_MSKSR_MPMO_Msk                    (0x01UL << RTC_MSKSR_MPMO_Pos)                          /*!< RTC MSKSR: MPMO Mask                    */
#define RTC_MSKSR_MPYE_Pos                    6                                                       /*!< RTC MSKSR: MPYE Position                */
#define RTC_MSKSR_MPYE_Msk                    (0x01UL << RTC_MSKSR_MPYE_Pos)                          /*!< RTC MSKSR: MPYE Mask                    */
#define RTC_MSKSR_MAI_Pos                     8                                                       /*!< RTC MSKSR: MAI Position                 */
#define RTC_MSKSR_MAI_Msk                     (0x01UL << RTC_MSKSR_MAI_Pos)                           /*!< RTC MSKSR: MAI Mask                     */

/* ----------------------------------  RTC_CLRSR  --------------------------------- */
#define RTC_CLRSR_RPSE_Pos                    0                                                       /*!< RTC CLRSR: RPSE Position                */
#define RTC_CLRSR_RPSE_Msk                    (0x01UL << RTC_CLRSR_RPSE_Pos)                          /*!< RTC CLRSR: RPSE Mask                    */
#define RTC_CLRSR_RPMI_Pos                    1                                                       /*!< RTC CLRSR: RPMI Position                */
#define RTC_CLRSR_RPMI_Msk                    (0x01UL << RTC_CLRSR_RPMI_Pos)                          /*!< RTC CLRSR: RPMI Mask                    */
#define RTC_CLRSR_RPHO_Pos                    2                                                       /*!< RTC CLRSR: RPHO Position                */
#define RTC_CLRSR_RPHO_Msk                    (0x01UL << RTC_CLRSR_RPHO_Pos)                          /*!< RTC CLRSR: RPHO Mask                    */
#define RTC_CLRSR_RPDA_Pos                    3                                                       /*!< RTC CLRSR: RPDA Position                */
#define RTC_CLRSR_RPDA_Msk                    (0x01UL << RTC_CLRSR_RPDA_Pos)                          /*!< RTC CLRSR: RPDA Mask                    */
#define RTC_CLRSR_RPMO_Pos                    5                                                       /*!< RTC CLRSR: RPMO Position                */
#define RTC_CLRSR_RPMO_Msk                    (0x01UL << RTC_CLRSR_RPMO_Pos)                          /*!< RTC CLRSR: RPMO Mask                    */
#define RTC_CLRSR_RPYE_Pos                    6                                                       /*!< RTC CLRSR: RPYE Position                */
#define RTC_CLRSR_RPYE_Msk                    (0x01UL << RTC_CLRSR_RPYE_Pos)                          /*!< RTC CLRSR: RPYE Mask                    */
#define RTC_CLRSR_RAI_Pos                     8                                                       /*!< RTC CLRSR: RAI Position                 */
#define RTC_CLRSR_RAI_Msk                     (0x01UL << RTC_CLRSR_RAI_Pos)                           /*!< RTC CLRSR: RAI Mask                     */

/* ----------------------------------  RTC_ATIM0  --------------------------------- */
#define RTC_ATIM0_ASE_Pos                     0                                                       /*!< RTC ATIM0: ASE Position                 */
#define RTC_ATIM0_ASE_Msk                     (0x3fUL << RTC_ATIM0_ASE_Pos)                           /*!< RTC ATIM0: ASE Mask                     */
#define RTC_ATIM0_AMI_Pos                     8                                                       /*!< RTC ATIM0: AMI Position                 */
#define RTC_ATIM0_AMI_Msk                     (0x3fUL << RTC_ATIM0_AMI_Pos)                           /*!< RTC ATIM0: AMI Mask                     */
#define RTC_ATIM0_AHO_Pos                     16                                                      /*!< RTC ATIM0: AHO Position                 */
#define RTC_ATIM0_AHO_Msk                     (0x1fUL << RTC_ATIM0_AHO_Pos)                           /*!< RTC ATIM0: AHO Mask                     */
#define RTC_ATIM0_ADA_Pos                     24                                                      /*!< RTC ATIM0: ADA Position                 */
#define RTC_ATIM0_ADA_Msk                     (0x1fUL << RTC_ATIM0_ADA_Pos)                           /*!< RTC ATIM0: ADA Mask                     */

/* ----------------------------------  RTC_ATIM1  --------------------------------- */
#define RTC_ATIM1_AMO_Pos                     8                                                       /*!< RTC ATIM1: AMO Position                 */
#define RTC_ATIM1_AMO_Msk                     (0x0fUL << RTC_ATIM1_AMO_Pos)                           /*!< RTC ATIM1: AMO Mask                     */
#define RTC_ATIM1_AYE_Pos                     16                                                      /*!< RTC ATIM1: AYE Position                 */
#define RTC_ATIM1_AYE_Msk                     (0x0000ffffUL << RTC_ATIM1_AYE_Pos)                     /*!< RTC ATIM1: AYE Mask                     */

/* ----------------------------------  RTC_TIM0  ---------------------------------- */
#define RTC_TIM0_SE_Pos                       0                                                       /*!< RTC TIM0: SE Position                   */
#define RTC_TIM0_SE_Msk                       (0x3fUL << RTC_TIM0_SE_Pos)                             /*!< RTC TIM0: SE Mask                       */
#define RTC_TIM0_MI_Pos                       8                                                       /*!< RTC TIM0: MI Position                   */
#define RTC_TIM0_MI_Msk                       (0x3fUL << RTC_TIM0_MI_Pos)                             /*!< RTC TIM0: MI Mask                       */
#define RTC_TIM0_HO_Pos                       16                                                      /*!< RTC TIM0: HO Position                   */
#define RTC_TIM0_HO_Msk                       (0x1fUL << RTC_TIM0_HO_Pos)                             /*!< RTC TIM0: HO Mask                       */
#define RTC_TIM0_DA_Pos                       24                                                      /*!< RTC TIM0: DA Position                   */
#define RTC_TIM0_DA_Msk                       (0x1fUL << RTC_TIM0_DA_Pos)                             /*!< RTC TIM0: DA Mask                       */

/* ----------------------------------  RTC_TIM1  ---------------------------------- */
#define RTC_TIM1_DAWE_Pos                     0                                                       /*!< RTC TIM1: DAWE Position                 */
#define RTC_TIM1_DAWE_Msk                     (0x07UL << RTC_TIM1_DAWE_Pos)                           /*!< RTC TIM1: DAWE Mask                     */
#define RTC_TIM1_MO_Pos                       8                                                       /*!< RTC TIM1: MO Position                   */
#define RTC_TIM1_MO_Msk                       (0x0fUL << RTC_TIM1_MO_Pos)                             /*!< RTC TIM1: MO Mask                       */
#define RTC_TIM1_YE_Pos                       16                                                      /*!< RTC TIM1: YE Position                   */
#define RTC_TIM1_YE_Msk                       (0x0000ffffUL << RTC_TIM1_YE_Pos)                       /*!< RTC TIM1: YE Mask                       */


/* ================================================================================ */
/* ================          struct 'PRNG' Position & Mask         ================ */
/* ================================================================================ */


/* ----------------------------------  PRNG_WORD  --------------------------------- */
#define PRNG_WORD_RDATA_Pos                   0                                                       /*!< PRNG WORD: RDATA Position               */
#define PRNG_WORD_RDATA_Msk                   (0x0000ffffUL << PRNG_WORD_RDATA_Pos)                   /*!< PRNG WORD: RDATA Mask                   */

/* ----------------------------------  PRNG_CHK  ---------------------------------- */
#define PRNG_CHK_RDV_Pos                      0                                                       /*!< PRNG CHK: RDV Position                  */
#define PRNG_CHK_RDV_Msk                      (0x01UL << PRNG_CHK_RDV_Pos)                            /*!< PRNG CHK: RDV Mask                      */

/* ----------------------------------  PRNG_CTRL  --------------------------------- */
#define PRNG_CTRL_RDBS_Pos                    1                                                       /*!< PRNG CTRL: RDBS Position                */
#define PRNG_CTRL_RDBS_Msk                    (0x03UL << PRNG_CTRL_RDBS_Pos)                          /*!< PRNG CTRL: RDBS Mask                    */
#define PRNG_CTRL_KLD_Pos                     3                                                       /*!< PRNG CTRL: KLD Position                 */
#define PRNG_CTRL_KLD_Msk                     (0x01UL << PRNG_CTRL_KLD_Pos)                           /*!< PRNG CTRL: KLD Mask                     */


/* ================================================================================ */
/* ================          Group 'USIC' Position & Mask          ================ */
/* ================================================================================ */


/* -----------------------------------  USIC_ID  ---------------------------------- */
#define USIC_ID_MOD_REV_Pos                   0                                                       /*!< USIC ID: MOD_REV Position               */
#define USIC_ID_MOD_REV_Msk                   (0x000000ffUL << USIC_ID_MOD_REV_Pos)                   /*!< USIC ID: MOD_REV Mask                   */
#define USIC_ID_MOD_TYPE_Pos                  8                                                       /*!< USIC ID: MOD_TYPE Position              */
#define USIC_ID_MOD_TYPE_Msk                  (0x000000ffUL << USIC_ID_MOD_TYPE_Pos)                  /*!< USIC ID: MOD_TYPE Mask                  */
#define USIC_ID_MOD_NUMBER_Pos                16                                                      /*!< USIC ID: MOD_NUMBER Position            */
#define USIC_ID_MOD_NUMBER_Msk                (0x0000ffffUL << USIC_ID_MOD_NUMBER_Pos)                /*!< USIC ID: MOD_NUMBER Mask                */


/* ================================================================================ */
/* ================         Group 'USIC_CH' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  USIC_CH_CCFG  -------------------------------- */
#define USIC_CH_CCFG_SSC_Pos                  0                                                       /*!< USIC_CH CCFG: SSC Position              */
#define USIC_CH_CCFG_SSC_Msk                  (0x01UL << USIC_CH_CCFG_SSC_Pos)                        /*!< USIC_CH CCFG: SSC Mask                  */
#define USIC_CH_CCFG_ASC_Pos                  1                                                       /*!< USIC_CH CCFG: ASC Position              */
#define USIC_CH_CCFG_ASC_Msk                  (0x01UL << USIC_CH_CCFG_ASC_Pos)                        /*!< USIC_CH CCFG: ASC Mask                  */
#define USIC_CH_CCFG_IIC_Pos                  2                                                       /*!< USIC_CH CCFG: IIC Position              */
#define USIC_CH_CCFG_IIC_Msk                  (0x01UL << USIC_CH_CCFG_IIC_Pos)                        /*!< USIC_CH CCFG: IIC Mask                  */
#define USIC_CH_CCFG_IIS_Pos                  3                                                       /*!< USIC_CH CCFG: IIS Position              */
#define USIC_CH_CCFG_IIS_Msk                  (0x01UL << USIC_CH_CCFG_IIS_Pos)                        /*!< USIC_CH CCFG: IIS Mask                  */
#define USIC_CH_CCFG_RB_Pos                   6                                                       /*!< USIC_CH CCFG: RB Position               */
#define USIC_CH_CCFG_RB_Msk                   (0x01UL << USIC_CH_CCFG_RB_Pos)                         /*!< USIC_CH CCFG: RB Mask                   */
#define USIC_CH_CCFG_TB_Pos                   7                                                       /*!< USIC_CH CCFG: TB Position               */
#define USIC_CH_CCFG_TB_Msk                   (0x01UL << USIC_CH_CCFG_TB_Pos)                         /*!< USIC_CH CCFG: TB Mask                   */

/* --------------------------------  USIC_CH_KSCFG  ------------------------------- */
#define USIC_CH_KSCFG_MODEN_Pos               0                                                       /*!< USIC_CH KSCFG: MODEN Position           */
#define USIC_CH_KSCFG_MODEN_Msk               (0x01UL << USIC_CH_KSCFG_MODEN_Pos)                     /*!< USIC_CH KSCFG: MODEN Mask               */
#define USIC_CH_KSCFG_BPMODEN_Pos             1                                                       /*!< USIC_CH KSCFG: BPMODEN Position         */
#define USIC_CH_KSCFG_BPMODEN_Msk             (0x01UL << USIC_CH_KSCFG_BPMODEN_Pos)                   /*!< USIC_CH KSCFG: BPMODEN Mask             */
#define USIC_CH_KSCFG_NOMCFG_Pos              4                                                       /*!< USIC_CH KSCFG: NOMCFG Position          */
#define USIC_CH_KSCFG_NOMCFG_Msk              (0x03UL << USIC_CH_KSCFG_NOMCFG_Pos)                    /*!< USIC_CH KSCFG: NOMCFG Mask              */
#define USIC_CH_KSCFG_BPNOM_Pos               7                                                       /*!< USIC_CH KSCFG: BPNOM Position           */
#define USIC_CH_KSCFG_BPNOM_Msk               (0x01UL << USIC_CH_KSCFG_BPNOM_Pos)                     /*!< USIC_CH KSCFG: BPNOM Mask               */
#define USIC_CH_KSCFG_SUMCFG_Pos              8                                                       /*!< USIC_CH KSCFG: SUMCFG Position          */
#define USIC_CH_KSCFG_SUMCFG_Msk              (0x03UL << USIC_CH_KSCFG_SUMCFG_Pos)                    /*!< USIC_CH KSCFG: SUMCFG Mask              */
#define USIC_CH_KSCFG_BPSUM_Pos               11                                                      /*!< USIC_CH KSCFG: BPSUM Position           */
#define USIC_CH_KSCFG_BPSUM_Msk               (0x01UL << USIC_CH_KSCFG_BPSUM_Pos)                     /*!< USIC_CH KSCFG: BPSUM Mask               */

/* ---------------------------------  USIC_CH_FDR  -------------------------------- */
#define USIC_CH_FDR_STEP_Pos                  0                                                       /*!< USIC_CH FDR: STEP Position              */
#define USIC_CH_FDR_STEP_Msk                  (0x000003ffUL << USIC_CH_FDR_STEP_Pos)                  /*!< USIC_CH FDR: STEP Mask                  */
#define USIC_CH_FDR_DM_Pos                    14                                                      /*!< USIC_CH FDR: DM Position                */
#define USIC_CH_FDR_DM_Msk                    (0x03UL << USIC_CH_FDR_DM_Pos)                          /*!< USIC_CH FDR: DM Mask                    */
#define USIC_CH_FDR_RESULT_Pos                16                                                      /*!< USIC_CH FDR: RESULT Position            */
#define USIC_CH_FDR_RESULT_Msk                (0x000003ffUL << USIC_CH_FDR_RESULT_Pos)                /*!< USIC_CH FDR: RESULT Mask                */

/* ---------------------------------  USIC_CH_BRG  -------------------------------- */
#define USIC_CH_BRG_CLKSEL_Pos                0                                                       /*!< USIC_CH BRG: CLKSEL Position            */
#define USIC_CH_BRG_CLKSEL_Msk                (0x03UL << USIC_CH_BRG_CLKSEL_Pos)                      /*!< USIC_CH BRG: CLKSEL Mask                */
#define USIC_CH_BRG_TMEN_Pos                  3                                                       /*!< USIC_CH BRG: TMEN Position              */
#define USIC_CH_BRG_TMEN_Msk                  (0x01UL << USIC_CH_BRG_TMEN_Pos)                        /*!< USIC_CH BRG: TMEN Mask                  */
#define USIC_CH_BRG_PPPEN_Pos                 4                                                       /*!< USIC_CH BRG: PPPEN Position             */
#define USIC_CH_BRG_PPPEN_Msk                 (0x01UL << USIC_CH_BRG_PPPEN_Pos)                       /*!< USIC_CH BRG: PPPEN Mask                 */
#define USIC_CH_BRG_CTQSEL_Pos                6                                                       /*!< USIC_CH BRG: CTQSEL Position            */
#define USIC_CH_BRG_CTQSEL_Msk                (0x03UL << USIC_CH_BRG_CTQSEL_Pos)                      /*!< USIC_CH BRG: CTQSEL Mask                */
#define USIC_CH_BRG_PCTQ_Pos                  8                                                       /*!< USIC_CH BRG: PCTQ Position              */
#define USIC_CH_BRG_PCTQ_Msk                  (0x03UL << USIC_CH_BRG_PCTQ_Pos)                        /*!< USIC_CH BRG: PCTQ Mask                  */
#define USIC_CH_BRG_DCTQ_Pos                  10                                                      /*!< USIC_CH BRG: DCTQ Position              */
#define USIC_CH_BRG_DCTQ_Msk                  (0x1fUL << USIC_CH_BRG_DCTQ_Pos)                        /*!< USIC_CH BRG: DCTQ Mask                  */
#define USIC_CH_BRG_PDIV_Pos                  16                                                      /*!< USIC_CH BRG: PDIV Position              */
#define USIC_CH_BRG_PDIV_Msk                  (0x000003ffUL << USIC_CH_BRG_PDIV_Pos)                  /*!< USIC_CH BRG: PDIV Mask                  */
#define USIC_CH_BRG_SCLKOSEL_Pos              28                                                      /*!< USIC_CH BRG: SCLKOSEL Position          */
#define USIC_CH_BRG_SCLKOSEL_Msk              (0x01UL << USIC_CH_BRG_SCLKOSEL_Pos)                    /*!< USIC_CH BRG: SCLKOSEL Mask              */
#define USIC_CH_BRG_MCLKCFG_Pos               29                                                      /*!< USIC_CH BRG: MCLKCFG Position           */
#define USIC_CH_BRG_MCLKCFG_Msk               (0x01UL << USIC_CH_BRG_MCLKCFG_Pos)                     /*!< USIC_CH BRG: MCLKCFG Mask               */
#define USIC_CH_BRG_SCLKCFG_Pos               30                                                      /*!< USIC_CH BRG: SCLKCFG Position           */
#define USIC_CH_BRG_SCLKCFG_Msk               (0x03UL << USIC_CH_BRG_SCLKCFG_Pos)                     /*!< USIC_CH BRG: SCLKCFG Mask               */

/* --------------------------------  USIC_CH_INPR  -------------------------------- */
#define USIC_CH_INPR_TSINP_Pos                0                                                       /*!< USIC_CH INPR: TSINP Position            */
#define USIC_CH_INPR_TSINP_Msk                (0x07UL << USIC_CH_INPR_TSINP_Pos)                      /*!< USIC_CH INPR: TSINP Mask                */
#define USIC_CH_INPR_TBINP_Pos                4                                                       /*!< USIC_CH INPR: TBINP Position            */
#define USIC_CH_INPR_TBINP_Msk                (0x07UL << USIC_CH_INPR_TBINP_Pos)                      /*!< USIC_CH INPR: TBINP Mask                */
#define USIC_CH_INPR_RINP_Pos                 8                                                       /*!< USIC_CH INPR: RINP Position             */
#define USIC_CH_INPR_RINP_Msk                 (0x07UL << USIC_CH_INPR_RINP_Pos)                       /*!< USIC_CH INPR: RINP Mask                 */
#define USIC_CH_INPR_AINP_Pos                 12                                                      /*!< USIC_CH INPR: AINP Position             */
#define USIC_CH_INPR_AINP_Msk                 (0x07UL << USIC_CH_INPR_AINP_Pos)                       /*!< USIC_CH INPR: AINP Mask                 */
#define USIC_CH_INPR_PINP_Pos                 16                                                      /*!< USIC_CH INPR: PINP Position             */
#define USIC_CH_INPR_PINP_Msk                 (0x07UL << USIC_CH_INPR_PINP_Pos)                       /*!< USIC_CH INPR: PINP Mask                 */

/* --------------------------------  USIC_CH_DX0CR  ------------------------------- */
#define USIC_CH_DX0CR_DSEL_Pos                0                                                       /*!< USIC_CH DX0CR: DSEL Position            */
#define USIC_CH_DX0CR_DSEL_Msk                (0x07UL << USIC_CH_DX0CR_DSEL_Pos)                      /*!< USIC_CH DX0CR: DSEL Mask                */
#define USIC_CH_DX0CR_INSW_Pos                4                                                       /*!< USIC_CH DX0CR: INSW Position            */
#define USIC_CH_DX0CR_INSW_Msk                (0x01UL << USIC_CH_DX0CR_INSW_Pos)                      /*!< USIC_CH DX0CR: INSW Mask                */
#define USIC_CH_DX0CR_DFEN_Pos                5                                                       /*!< USIC_CH DX0CR: DFEN Position            */
#define USIC_CH_DX0CR_DFEN_Msk                (0x01UL << USIC_CH_DX0CR_DFEN_Pos)                      /*!< USIC_CH DX0CR: DFEN Mask                */
#define USIC_CH_DX0CR_DSEN_Pos                6                                                       /*!< USIC_CH DX0CR: DSEN Position            */
#define USIC_CH_DX0CR_DSEN_Msk                (0x01UL << USIC_CH_DX0CR_DSEN_Pos)                      /*!< USIC_CH DX0CR: DSEN Mask                */
#define USIC_CH_DX0CR_DPOL_Pos                8                                                       /*!< USIC_CH DX0CR: DPOL Position            */
#define USIC_CH_DX0CR_DPOL_Msk                (0x01UL << USIC_CH_DX0CR_DPOL_Pos)                      /*!< USIC_CH DX0CR: DPOL Mask                */
#define USIC_CH_DX0CR_SFSEL_Pos               9                                                       /*!< USIC_CH DX0CR: SFSEL Position           */
#define USIC_CH_DX0CR_SFSEL_Msk               (0x01UL << USIC_CH_DX0CR_SFSEL_Pos)                     /*!< USIC_CH DX0CR: SFSEL Mask               */
#define USIC_CH_DX0CR_CM_Pos                  10                                                      /*!< USIC_CH DX0CR: CM Position              */
#define USIC_CH_DX0CR_CM_Msk                  (0x03UL << USIC_CH_DX0CR_CM_Pos)                        /*!< USIC_CH DX0CR: CM Mask                  */
#define USIC_CH_DX0CR_DXS_Pos                 15                                                      /*!< USIC_CH DX0CR: DXS Position             */
#define USIC_CH_DX0CR_DXS_Msk                 (0x01UL << USIC_CH_DX0CR_DXS_Pos)                       /*!< USIC_CH DX0CR: DXS Mask                 */

/* --------------------------------  USIC_CH_DX1CR  ------------------------------- */
#define USIC_CH_DX1CR_DSEL_Pos                0                                                       /*!< USIC_CH DX1CR: DSEL Position            */
#define USIC_CH_DX1CR_DSEL_Msk                (0x07UL << USIC_CH_DX1CR_DSEL_Pos)                      /*!< USIC_CH DX1CR: DSEL Mask                */
#define USIC_CH_DX1CR_DCEN_Pos                3                                                       /*!< USIC_CH DX1CR: DCEN Position            */
#define USIC_CH_DX1CR_DCEN_Msk                (0x01UL << USIC_CH_DX1CR_DCEN_Pos)                      /*!< USIC_CH DX1CR: DCEN Mask                */
#define USIC_CH_DX1CR_INSW_Pos                4                                                       /*!< USIC_CH DX1CR: INSW Position            */
#define USIC_CH_DX1CR_INSW_Msk                (0x01UL << USIC_CH_DX1CR_INSW_Pos)                      /*!< USIC_CH DX1CR: INSW Mask                */
#define USIC_CH_DX1CR_DFEN_Pos                5                                                       /*!< USIC_CH DX1CR: DFEN Position            */
#define USIC_CH_DX1CR_DFEN_Msk                (0x01UL << USIC_CH_DX1CR_DFEN_Pos)                      /*!< USIC_CH DX1CR: DFEN Mask                */
#define USIC_CH_DX1CR_DSEN_Pos                6                                                       /*!< USIC_CH DX1CR: DSEN Position            */
#define USIC_CH_DX1CR_DSEN_Msk                (0x01UL << USIC_CH_DX1CR_DSEN_Pos)                      /*!< USIC_CH DX1CR: DSEN Mask                */
#define USIC_CH_DX1CR_DPOL_Pos                8                                                       /*!< USIC_CH DX1CR: DPOL Position            */
#define USIC_CH_DX1CR_DPOL_Msk                (0x01UL << USIC_CH_DX1CR_DPOL_Pos)                      /*!< USIC_CH DX1CR: DPOL Mask                */
#define USIC_CH_DX1CR_SFSEL_Pos               9                                                       /*!< USIC_CH DX1CR: SFSEL Position           */
#define USIC_CH_DX1CR_SFSEL_Msk               (0x01UL << USIC_CH_DX1CR_SFSEL_Pos)                     /*!< USIC_CH DX1CR: SFSEL Mask               */
#define USIC_CH_DX1CR_CM_Pos                  10                                                      /*!< USIC_CH DX1CR: CM Position              */
#define USIC_CH_DX1CR_CM_Msk                  (0x03UL << USIC_CH_DX1CR_CM_Pos)                        /*!< USIC_CH DX1CR: CM Mask                  */
#define USIC_CH_DX1CR_DXS_Pos                 15                                                      /*!< USIC_CH DX1CR: DXS Position             */
#define USIC_CH_DX1CR_DXS_Msk                 (0x01UL << USIC_CH_DX1CR_DXS_Pos)                       /*!< USIC_CH DX1CR: DXS Mask                 */

/* --------------------------------  USIC_CH_DX2CR  ------------------------------- */
#define USIC_CH_DX2CR_DSEL_Pos                0                                                       /*!< USIC_CH DX2CR: DSEL Position            */
#define USIC_CH_DX2CR_DSEL_Msk                (0x07UL << USIC_CH_DX2CR_DSEL_Pos)                      /*!< USIC_CH DX2CR: DSEL Mask                */
#define USIC_CH_DX2CR_INSW_Pos                4                                                       /*!< USIC_CH DX2CR: INSW Position            */
#define USIC_CH_DX2CR_INSW_Msk                (0x01UL << USIC_CH_DX2CR_INSW_Pos)                      /*!< USIC_CH DX2CR: INSW Mask                */
#define USIC_CH_DX2CR_DFEN_Pos                5                                                       /*!< USIC_CH DX2CR: DFEN Position            */
#define USIC_CH_DX2CR_DFEN_Msk                (0x01UL << USIC_CH_DX2CR_DFEN_Pos)                      /*!< USIC_CH DX2CR: DFEN Mask                */
#define USIC_CH_DX2CR_DSEN_Pos                6                                                       /*!< USIC_CH DX2CR: DSEN Position            */
#define USIC_CH_DX2CR_DSEN_Msk                (0x01UL << USIC_CH_DX2CR_DSEN_Pos)                      /*!< USIC_CH DX2CR: DSEN Mask                */
#define USIC_CH_DX2CR_DPOL_Pos                8                                                       /*!< USIC_CH DX2CR: DPOL Position            */
#define USIC_CH_DX2CR_DPOL_Msk                (0x01UL << USIC_CH_DX2CR_DPOL_Pos)                      /*!< USIC_CH DX2CR: DPOL Mask                */
#define USIC_CH_DX2CR_SFSEL_Pos               9                                                       /*!< USIC_CH DX2CR: SFSEL Position           */
#define USIC_CH_DX2CR_SFSEL_Msk               (0x01UL << USIC_CH_DX2CR_SFSEL_Pos)                     /*!< USIC_CH DX2CR: SFSEL Mask               */
#define USIC_CH_DX2CR_CM_Pos                  10                                                      /*!< USIC_CH DX2CR: CM Position              */
#define USIC_CH_DX2CR_CM_Msk                  (0x03UL << USIC_CH_DX2CR_CM_Pos)                        /*!< USIC_CH DX2CR: CM Mask                  */
#define USIC_CH_DX2CR_DXS_Pos                 15                                                      /*!< USIC_CH DX2CR: DXS Position             */
#define USIC_CH_DX2CR_DXS_Msk                 (0x01UL << USIC_CH_DX2CR_DXS_Pos)                       /*!< USIC_CH DX2CR: DXS Mask                 */

/* --------------------------------  USIC_CH_DX3CR  ------------------------------- */
#define USIC_CH_DX3CR_DSEL_Pos                0                                                       /*!< USIC_CH DX3CR: DSEL Position            */
#define USIC_CH_DX3CR_DSEL_Msk                (0x07UL << USIC_CH_DX3CR_DSEL_Pos)                      /*!< USIC_CH DX3CR: DSEL Mask                */
#define USIC_CH_DX3CR_INSW_Pos                4                                                       /*!< USIC_CH DX3CR: INSW Position            */
#define USIC_CH_DX3CR_INSW_Msk                (0x01UL << USIC_CH_DX3CR_INSW_Pos)                      /*!< USIC_CH DX3CR: INSW Mask                */
#define USIC_CH_DX3CR_DFEN_Pos                5                                                       /*!< USIC_CH DX3CR: DFEN Position            */
#define USIC_CH_DX3CR_DFEN_Msk                (0x01UL << USIC_CH_DX3CR_DFEN_Pos)                      /*!< USIC_CH DX3CR: DFEN Mask                */
#define USIC_CH_DX3CR_DSEN_Pos                6                                                       /*!< USIC_CH DX3CR: DSEN Position            */
#define USIC_CH_DX3CR_DSEN_Msk                (0x01UL << USIC_CH_DX3CR_DSEN_Pos)                      /*!< USIC_CH DX3CR: DSEN Mask                */
#define USIC_CH_DX3CR_DPOL_Pos                8                                                       /*!< USIC_CH DX3CR: DPOL Position            */
#define USIC_CH_DX3CR_DPOL_Msk                (0x01UL << USIC_CH_DX3CR_DPOL_Pos)                      /*!< USIC_CH DX3CR: DPOL Mask                */
#define USIC_CH_DX3CR_SFSEL_Pos               9                                                       /*!< USIC_CH DX3CR: SFSEL Position           */
#define USIC_CH_DX3CR_SFSEL_Msk               (0x01UL << USIC_CH_DX3CR_SFSEL_Pos)                     /*!< USIC_CH DX3CR: SFSEL Mask               */
#define USIC_CH_DX3CR_CM_Pos                  10                                                      /*!< USIC_CH DX3CR: CM Position              */
#define USIC_CH_DX3CR_CM_Msk                  (0x03UL << USIC_CH_DX3CR_CM_Pos)                        /*!< USIC_CH DX3CR: CM Mask                  */
#define USIC_CH_DX3CR_DXS_Pos                 15                                                      /*!< USIC_CH DX3CR: DXS Position             */
#define USIC_CH_DX3CR_DXS_Msk                 (0x01UL << USIC_CH_DX3CR_DXS_Pos)                       /*!< USIC_CH DX3CR: DXS Mask                 */

/* --------------------------------  USIC_CH_DX4CR  ------------------------------- */
#define USIC_CH_DX4CR_DSEL_Pos                0                                                       /*!< USIC_CH DX4CR: DSEL Position            */
#define USIC_CH_DX4CR_DSEL_Msk                (0x07UL << USIC_CH_DX4CR_DSEL_Pos)                      /*!< USIC_CH DX4CR: DSEL Mask                */
#define USIC_CH_DX4CR_INSW_Pos                4                                                       /*!< USIC_CH DX4CR: INSW Position            */
#define USIC_CH_DX4CR_INSW_Msk                (0x01UL << USIC_CH_DX4CR_INSW_Pos)                      /*!< USIC_CH DX4CR: INSW Mask                */
#define USIC_CH_DX4CR_DFEN_Pos                5                                                       /*!< USIC_CH DX4CR: DFEN Position            */
#define USIC_CH_DX4CR_DFEN_Msk                (0x01UL << USIC_CH_DX4CR_DFEN_Pos)                      /*!< USIC_CH DX4CR: DFEN Mask                */
#define USIC_CH_DX4CR_DSEN_Pos                6                                                       /*!< USIC_CH DX4CR: DSEN Position            */
#define USIC_CH_DX4CR_DSEN_Msk                (0x01UL << USIC_CH_DX4CR_DSEN_Pos)                      /*!< USIC_CH DX4CR: DSEN Mask                */
#define USIC_CH_DX4CR_DPOL_Pos                8                                                       /*!< USIC_CH DX4CR: DPOL Position            */
#define USIC_CH_DX4CR_DPOL_Msk                (0x01UL << USIC_CH_DX4CR_DPOL_Pos)                      /*!< USIC_CH DX4CR: DPOL Mask                */
#define USIC_CH_DX4CR_SFSEL_Pos               9                                                       /*!< USIC_CH DX4CR: SFSEL Position           */
#define USIC_CH_DX4CR_SFSEL_Msk               (0x01UL << USIC_CH_DX4CR_SFSEL_Pos)                     /*!< USIC_CH DX4CR: SFSEL Mask               */
#define USIC_CH_DX4CR_CM_Pos                  10                                                      /*!< USIC_CH DX4CR: CM Position              */
#define USIC_CH_DX4CR_CM_Msk                  (0x03UL << USIC_CH_DX4CR_CM_Pos)                        /*!< USIC_CH DX4CR: CM Mask                  */
#define USIC_CH_DX4CR_DXS_Pos                 15                                                      /*!< USIC_CH DX4CR: DXS Position             */
#define USIC_CH_DX4CR_DXS_Msk                 (0x01UL << USIC_CH_DX4CR_DXS_Pos)                       /*!< USIC_CH DX4CR: DXS Mask                 */

/* --------------------------------  USIC_CH_DX5CR  ------------------------------- */
#define USIC_CH_DX5CR_DSEL_Pos                0                                                       /*!< USIC_CH DX5CR: DSEL Position            */
#define USIC_CH_DX5CR_DSEL_Msk                (0x07UL << USIC_CH_DX5CR_DSEL_Pos)                      /*!< USIC_CH DX5CR: DSEL Mask                */
#define USIC_CH_DX5CR_INSW_Pos                4                                                       /*!< USIC_CH DX5CR: INSW Position            */
#define USIC_CH_DX5CR_INSW_Msk                (0x01UL << USIC_CH_DX5CR_INSW_Pos)                      /*!< USIC_CH DX5CR: INSW Mask                */
#define USIC_CH_DX5CR_DFEN_Pos                5                                                       /*!< USIC_CH DX5CR: DFEN Position            */
#define USIC_CH_DX5CR_DFEN_Msk                (0x01UL << USIC_CH_DX5CR_DFEN_Pos)                      /*!< USIC_CH DX5CR: DFEN Mask                */
#define USIC_CH_DX5CR_DSEN_Pos                6                                                       /*!< USIC_CH DX5CR: DSEN Position            */
#define USIC_CH_DX5CR_DSEN_Msk                (0x01UL << USIC_CH_DX5CR_DSEN_Pos)                      /*!< USIC_CH DX5CR: DSEN Mask                */
#define USIC_CH_DX5CR_DPOL_Pos                8                                                       /*!< USIC_CH DX5CR: DPOL Position            */
#define USIC_CH_DX5CR_DPOL_Msk                (0x01UL << USIC_CH_DX5CR_DPOL_Pos)                      /*!< USIC_CH DX5CR: DPOL Mask                */
#define USIC_CH_DX5CR_SFSEL_Pos               9                                                       /*!< USIC_CH DX5CR: SFSEL Position           */
#define USIC_CH_DX5CR_SFSEL_Msk               (0x01UL << USIC_CH_DX5CR_SFSEL_Pos)                     /*!< USIC_CH DX5CR: SFSEL Mask               */
#define USIC_CH_DX5CR_CM_Pos                  10                                                      /*!< USIC_CH DX5CR: CM Position              */
#define USIC_CH_DX5CR_CM_Msk                  (0x03UL << USIC_CH_DX5CR_CM_Pos)                        /*!< USIC_CH DX5CR: CM Mask                  */
#define USIC_CH_DX5CR_DXS_Pos                 15                                                      /*!< USIC_CH DX5CR: DXS Position             */
#define USIC_CH_DX5CR_DXS_Msk                 (0x01UL << USIC_CH_DX5CR_DXS_Pos)                       /*!< USIC_CH DX5CR: DXS Mask                 */

/* --------------------------------  USIC_CH_SCTR  -------------------------------- */
#define USIC_CH_SCTR_SDIR_Pos                 0                                                       /*!< USIC_CH SCTR: SDIR Position             */
#define USIC_CH_SCTR_SDIR_Msk                 (0x01UL << USIC_CH_SCTR_SDIR_Pos)                       /*!< USIC_CH SCTR: SDIR Mask                 */
#define USIC_CH_SCTR_PDL_Pos                  1                                                       /*!< USIC_CH SCTR: PDL Position              */
#define USIC_CH_SCTR_PDL_Msk                  (0x01UL << USIC_CH_SCTR_PDL_Pos)                        /*!< USIC_CH SCTR: PDL Mask                  */
#define USIC_CH_SCTR_DSM_Pos                  2                                                       /*!< USIC_CH SCTR: DSM Position              */
#define USIC_CH_SCTR_DSM_Msk                  (0x03UL << USIC_CH_SCTR_DSM_Pos)                        /*!< USIC_CH SCTR: DSM Mask                  */
#define USIC_CH_SCTR_HPCDIR_Pos               4                                                       /*!< USIC_CH SCTR: HPCDIR Position           */
#define USIC_CH_SCTR_HPCDIR_Msk               (0x01UL << USIC_CH_SCTR_HPCDIR_Pos)                     /*!< USIC_CH SCTR: HPCDIR Mask               */
#define USIC_CH_SCTR_DOCFG_Pos                6                                                       /*!< USIC_CH SCTR: DOCFG Position            */
#define USIC_CH_SCTR_DOCFG_Msk                (0x03UL << USIC_CH_SCTR_DOCFG_Pos)                      /*!< USIC_CH SCTR: DOCFG Mask                */
#define USIC_CH_SCTR_TRM_Pos                  8                                                       /*!< USIC_CH SCTR: TRM Position              */
#define USIC_CH_SCTR_TRM_Msk                  (0x03UL << USIC_CH_SCTR_TRM_Pos)                        /*!< USIC_CH SCTR: TRM Mask                  */
#define USIC_CH_SCTR_FLE_Pos                  16                                                      /*!< USIC_CH SCTR: FLE Position              */
#define USIC_CH_SCTR_FLE_Msk                  (0x3fUL << USIC_CH_SCTR_FLE_Pos)                        /*!< USIC_CH SCTR: FLE Mask                  */
#define USIC_CH_SCTR_WLE_Pos                  24                                                      /*!< USIC_CH SCTR: WLE Position              */
#define USIC_CH_SCTR_WLE_Msk                  (0x0fUL << USIC_CH_SCTR_WLE_Pos)                        /*!< USIC_CH SCTR: WLE Mask                  */

/* --------------------------------  USIC_CH_TCSR  -------------------------------- */
#define USIC_CH_TCSR_WLEMD_Pos                0                                                       /*!< USIC_CH TCSR: WLEMD Position            */
#define USIC_CH_TCSR_WLEMD_Msk                (0x01UL << USIC_CH_TCSR_WLEMD_Pos)                      /*!< USIC_CH TCSR: WLEMD Mask                */
#define USIC_CH_TCSR_SELMD_Pos                1                                                       /*!< USIC_CH TCSR: SELMD Position            */
#define USIC_CH_TCSR_SELMD_Msk                (0x01UL << USIC_CH_TCSR_SELMD_Pos)                      /*!< USIC_CH TCSR: SELMD Mask                */
#define USIC_CH_TCSR_FLEMD_Pos                2                                                       /*!< USIC_CH TCSR: FLEMD Position            */
#define USIC_CH_TCSR_FLEMD_Msk                (0x01UL << USIC_CH_TCSR_FLEMD_Pos)                      /*!< USIC_CH TCSR: FLEMD Mask                */
#define USIC_CH_TCSR_WAMD_Pos                 3                                                       /*!< USIC_CH TCSR: WAMD Position             */
#define USIC_CH_TCSR_WAMD_Msk                 (0x01UL << USIC_CH_TCSR_WAMD_Pos)                       /*!< USIC_CH TCSR: WAMD Mask                 */
#define USIC_CH_TCSR_HPCMD_Pos                4                                                       /*!< USIC_CH TCSR: HPCMD Position            */
#define USIC_CH_TCSR_HPCMD_Msk                (0x01UL << USIC_CH_TCSR_HPCMD_Pos)                      /*!< USIC_CH TCSR: HPCMD Mask                */
#define USIC_CH_TCSR_SOF_Pos                  5                                                       /*!< USIC_CH TCSR: SOF Position              */
#define USIC_CH_TCSR_SOF_Msk                  (0x01UL << USIC_CH_TCSR_SOF_Pos)                        /*!< USIC_CH TCSR: SOF Mask                  */
#define USIC_CH_TCSR_EOF_Pos                  6                                                       /*!< USIC_CH TCSR: EOF Position              */
#define USIC_CH_TCSR_EOF_Msk                  (0x01UL << USIC_CH_TCSR_EOF_Pos)                        /*!< USIC_CH TCSR: EOF Mask                  */
#define USIC_CH_TCSR_TDV_Pos                  7                                                       /*!< USIC_CH TCSR: TDV Position              */
#define USIC_CH_TCSR_TDV_Msk                  (0x01UL << USIC_CH_TCSR_TDV_Pos)                        /*!< USIC_CH TCSR: TDV Mask                  */
#define USIC_CH_TCSR_TDSSM_Pos                8                                                       /*!< USIC_CH TCSR: TDSSM Position            */
#define USIC_CH_TCSR_TDSSM_Msk                (0x01UL << USIC_CH_TCSR_TDSSM_Pos)                      /*!< USIC_CH TCSR: TDSSM Mask                */
#define USIC_CH_TCSR_TDEN_Pos                 10                                                      /*!< USIC_CH TCSR: TDEN Position             */
#define USIC_CH_TCSR_TDEN_Msk                 (0x03UL << USIC_CH_TCSR_TDEN_Pos)                       /*!< USIC_CH TCSR: TDEN Mask                 */
#define USIC_CH_TCSR_TDVTR_Pos                12                                                      /*!< USIC_CH TCSR: TDVTR Position            */
#define USIC_CH_TCSR_TDVTR_Msk                (0x01UL << USIC_CH_TCSR_TDVTR_Pos)                      /*!< USIC_CH TCSR: TDVTR Mask                */
#define USIC_CH_TCSR_WA_Pos                   13                                                      /*!< USIC_CH TCSR: WA Position               */
#define USIC_CH_TCSR_WA_Msk                   (0x01UL << USIC_CH_TCSR_WA_Pos)                         /*!< USIC_CH TCSR: WA Mask                   */
#define USIC_CH_TCSR_TSOF_Pos                 24                                                      /*!< USIC_CH TCSR: TSOF Position             */
#define USIC_CH_TCSR_TSOF_Msk                 (0x01UL << USIC_CH_TCSR_TSOF_Pos)                       /*!< USIC_CH TCSR: TSOF Mask                 */
#define USIC_CH_TCSR_TV_Pos                   26                                                      /*!< USIC_CH TCSR: TV Position               */
#define USIC_CH_TCSR_TV_Msk                   (0x01UL << USIC_CH_TCSR_TV_Pos)                         /*!< USIC_CH TCSR: TV Mask                   */
#define USIC_CH_TCSR_TVC_Pos                  27                                                      /*!< USIC_CH TCSR: TVC Position              */
#define USIC_CH_TCSR_TVC_Msk                  (0x01UL << USIC_CH_TCSR_TVC_Pos)                        /*!< USIC_CH TCSR: TVC Mask                  */
#define USIC_CH_TCSR_TE_Pos                   28                                                      /*!< USIC_CH TCSR: TE Position               */
#define USIC_CH_TCSR_TE_Msk                   (0x01UL << USIC_CH_TCSR_TE_Pos)                         /*!< USIC_CH TCSR: TE Mask                   */

/* ---------------------------------  USIC_CH_PCR  -------------------------------- */
#define USIC_CH_PCR_CTR0_Pos                  0                                                       /*!< USIC_CH PCR: CTR0 Position              */
#define USIC_CH_PCR_CTR0_Msk                  (0x01UL << USIC_CH_PCR_CTR0_Pos)                        /*!< USIC_CH PCR: CTR0 Mask                  */
#define USIC_CH_PCR_CTR1_Pos                  1                                                       /*!< USIC_CH PCR: CTR1 Position              */
#define USIC_CH_PCR_CTR1_Msk                  (0x01UL << USIC_CH_PCR_CTR1_Pos)                        /*!< USIC_CH PCR: CTR1 Mask                  */
#define USIC_CH_PCR_CTR2_Pos                  2                                                       /*!< USIC_CH PCR: CTR2 Position              */
#define USIC_CH_PCR_CTR2_Msk                  (0x01UL << USIC_CH_PCR_CTR2_Pos)                        /*!< USIC_CH PCR: CTR2 Mask                  */
#define USIC_CH_PCR_CTR3_Pos                  3                                                       /*!< USIC_CH PCR: CTR3 Position              */
#define USIC_CH_PCR_CTR3_Msk                  (0x01UL << USIC_CH_PCR_CTR3_Pos)                        /*!< USIC_CH PCR: CTR3 Mask                  */
#define USIC_CH_PCR_CTR4_Pos                  4                                                       /*!< USIC_CH PCR: CTR4 Position              */
#define USIC_CH_PCR_CTR4_Msk                  (0x01UL << USIC_CH_PCR_CTR4_Pos)                        /*!< USIC_CH PCR: CTR4 Mask                  */
#define USIC_CH_PCR_CTR5_Pos                  5                                                       /*!< USIC_CH PCR: CTR5 Position              */
#define USIC_CH_PCR_CTR5_Msk                  (0x01UL << USIC_CH_PCR_CTR5_Pos)                        /*!< USIC_CH PCR: CTR5 Mask                  */
#define USIC_CH_PCR_CTR6_Pos                  6                                                       /*!< USIC_CH PCR: CTR6 Position              */
#define USIC_CH_PCR_CTR6_Msk                  (0x01UL << USIC_CH_PCR_CTR6_Pos)                        /*!< USIC_CH PCR: CTR6 Mask                  */
#define USIC_CH_PCR_CTR7_Pos                  7                                                       /*!< USIC_CH PCR: CTR7 Position              */
#define USIC_CH_PCR_CTR7_Msk                  (0x01UL << USIC_CH_PCR_CTR7_Pos)                        /*!< USIC_CH PCR: CTR7 Mask                  */
#define USIC_CH_PCR_CTR8_Pos                  8                                                       /*!< USIC_CH PCR: CTR8 Position              */
#define USIC_CH_PCR_CTR8_Msk                  (0x01UL << USIC_CH_PCR_CTR8_Pos)                        /*!< USIC_CH PCR: CTR8 Mask                  */
#define USIC_CH_PCR_CTR9_Pos                  9                                                       /*!< USIC_CH PCR: CTR9 Position              */
#define USIC_CH_PCR_CTR9_Msk                  (0x01UL << USIC_CH_PCR_CTR9_Pos)                        /*!< USIC_CH PCR: CTR9 Mask                  */
#define USIC_CH_PCR_CTR10_Pos                 10                                                      /*!< USIC_CH PCR: CTR10 Position             */
#define USIC_CH_PCR_CTR10_Msk                 (0x01UL << USIC_CH_PCR_CTR10_Pos)                       /*!< USIC_CH PCR: CTR10 Mask                 */
#define USIC_CH_PCR_CTR11_Pos                 11                                                      /*!< USIC_CH PCR: CTR11 Position             */
#define USIC_CH_PCR_CTR11_Msk                 (0x01UL << USIC_CH_PCR_CTR11_Pos)                       /*!< USIC_CH PCR: CTR11 Mask                 */
#define USIC_CH_PCR_CTR12_Pos                 12                                                      /*!< USIC_CH PCR: CTR12 Position             */
#define USIC_CH_PCR_CTR12_Msk                 (0x01UL << USIC_CH_PCR_CTR12_Pos)                       /*!< USIC_CH PCR: CTR12 Mask                 */
#define USIC_CH_PCR_CTR13_Pos                 13                                                      /*!< USIC_CH PCR: CTR13 Position             */
#define USIC_CH_PCR_CTR13_Msk                 (0x01UL << USIC_CH_PCR_CTR13_Pos)                       /*!< USIC_CH PCR: CTR13 Mask                 */
#define USIC_CH_PCR_CTR14_Pos                 14                                                      /*!< USIC_CH PCR: CTR14 Position             */
#define USIC_CH_PCR_CTR14_Msk                 (0x01UL << USIC_CH_PCR_CTR14_Pos)                       /*!< USIC_CH PCR: CTR14 Mask                 */
#define USIC_CH_PCR_CTR15_Pos                 15                                                      /*!< USIC_CH PCR: CTR15 Position             */
#define USIC_CH_PCR_CTR15_Msk                 (0x01UL << USIC_CH_PCR_CTR15_Pos)                       /*!< USIC_CH PCR: CTR15 Mask                 */
#define USIC_CH_PCR_CTR16_Pos                 16                                                      /*!< USIC_CH PCR: CTR16 Position             */
#define USIC_CH_PCR_CTR16_Msk                 (0x01UL << USIC_CH_PCR_CTR16_Pos)                       /*!< USIC_CH PCR: CTR16 Mask                 */
#define USIC_CH_PCR_CTR17_Pos                 17                                                      /*!< USIC_CH PCR: CTR17 Position             */
#define USIC_CH_PCR_CTR17_Msk                 (0x01UL << USIC_CH_PCR_CTR17_Pos)                       /*!< USIC_CH PCR: CTR17 Mask                 */
#define USIC_CH_PCR_CTR18_Pos                 18                                                      /*!< USIC_CH PCR: CTR18 Position             */
#define USIC_CH_PCR_CTR18_Msk                 (0x01UL << USIC_CH_PCR_CTR18_Pos)                       /*!< USIC_CH PCR: CTR18 Mask                 */
#define USIC_CH_PCR_CTR19_Pos                 19                                                      /*!< USIC_CH PCR: CTR19 Position             */
#define USIC_CH_PCR_CTR19_Msk                 (0x01UL << USIC_CH_PCR_CTR19_Pos)                       /*!< USIC_CH PCR: CTR19 Mask                 */
#define USIC_CH_PCR_CTR20_Pos                 20                                                      /*!< USIC_CH PCR: CTR20 Position             */
#define USIC_CH_PCR_CTR20_Msk                 (0x01UL << USIC_CH_PCR_CTR20_Pos)                       /*!< USIC_CH PCR: CTR20 Mask                 */
#define USIC_CH_PCR_CTR21_Pos                 21                                                      /*!< USIC_CH PCR: CTR21 Position             */
#define USIC_CH_PCR_CTR21_Msk                 (0x01UL << USIC_CH_PCR_CTR21_Pos)                       /*!< USIC_CH PCR: CTR21 Mask                 */
#define USIC_CH_PCR_CTR22_Pos                 22                                                      /*!< USIC_CH PCR: CTR22 Position             */
#define USIC_CH_PCR_CTR22_Msk                 (0x01UL << USIC_CH_PCR_CTR22_Pos)                       /*!< USIC_CH PCR: CTR22 Mask                 */
#define USIC_CH_PCR_CTR23_Pos                 23                                                      /*!< USIC_CH PCR: CTR23 Position             */
#define USIC_CH_PCR_CTR23_Msk                 (0x01UL << USIC_CH_PCR_CTR23_Pos)                       /*!< USIC_CH PCR: CTR23 Mask                 */
#define USIC_CH_PCR_CTR24_Pos                 24                                                      /*!< USIC_CH PCR: CTR24 Position             */
#define USIC_CH_PCR_CTR24_Msk                 (0x01UL << USIC_CH_PCR_CTR24_Pos)                       /*!< USIC_CH PCR: CTR24 Mask                 */
#define USIC_CH_PCR_CTR25_Pos                 25                                                      /*!< USIC_CH PCR: CTR25 Position             */
#define USIC_CH_PCR_CTR25_Msk                 (0x01UL << USIC_CH_PCR_CTR25_Pos)                       /*!< USIC_CH PCR: CTR25 Mask                 */
#define USIC_CH_PCR_CTR26_Pos                 26                                                      /*!< USIC_CH PCR: CTR26 Position             */
#define USIC_CH_PCR_CTR26_Msk                 (0x01UL << USIC_CH_PCR_CTR26_Pos)                       /*!< USIC_CH PCR: CTR26 Mask                 */
#define USIC_CH_PCR_CTR27_Pos                 27                                                      /*!< USIC_CH PCR: CTR27 Position             */
#define USIC_CH_PCR_CTR27_Msk                 (0x01UL << USIC_CH_PCR_CTR27_Pos)                       /*!< USIC_CH PCR: CTR27 Mask                 */
#define USIC_CH_PCR_CTR28_Pos                 28                                                      /*!< USIC_CH PCR: CTR28 Position             */
#define USIC_CH_PCR_CTR28_Msk                 (0x01UL << USIC_CH_PCR_CTR28_Pos)                       /*!< USIC_CH PCR: CTR28 Mask                 */
#define USIC_CH_PCR_CTR29_Pos                 29                                                      /*!< USIC_CH PCR: CTR29 Position             */
#define USIC_CH_PCR_CTR29_Msk                 (0x01UL << USIC_CH_PCR_CTR29_Pos)                       /*!< USIC_CH PCR: CTR29 Mask                 */
#define USIC_CH_PCR_CTR30_Pos                 30                                                      /*!< USIC_CH PCR: CTR30 Position             */
#define USIC_CH_PCR_CTR30_Msk                 (0x01UL << USIC_CH_PCR_CTR30_Pos)                       /*!< USIC_CH PCR: CTR30 Mask                 */
#define USIC_CH_PCR_CTR31_Pos                 31                                                      /*!< USIC_CH PCR: CTR31 Position             */
#define USIC_CH_PCR_CTR31_Msk                 (0x01UL << USIC_CH_PCR_CTR31_Pos)                       /*!< USIC_CH PCR: CTR31 Mask                 */

/* -----------------------------  USIC_CH_PCR_ASCMode  ---------------------------- */
#define USIC_CH_PCR_ASCMode_SMD_Pos           0                                                       /*!< USIC_CH PCR_ASCMode: SMD Position       */
#define USIC_CH_PCR_ASCMode_SMD_Msk           (0x01UL << USIC_CH_PCR_ASCMode_SMD_Pos)                 /*!< USIC_CH PCR_ASCMode: SMD Mask           */
#define USIC_CH_PCR_ASCMode_STPB_Pos          1                                                       /*!< USIC_CH PCR_ASCMode: STPB Position      */
#define USIC_CH_PCR_ASCMode_STPB_Msk          (0x01UL << USIC_CH_PCR_ASCMode_STPB_Pos)                /*!< USIC_CH PCR_ASCMode: STPB Mask          */
#define USIC_CH_PCR_ASCMode_IDM_Pos           2                                                       /*!< USIC_CH PCR_ASCMode: IDM Position       */
#define USIC_CH_PCR_ASCMode_IDM_Msk           (0x01UL << USIC_CH_PCR_ASCMode_IDM_Pos)                 /*!< USIC_CH PCR_ASCMode: IDM Mask           */
#define USIC_CH_PCR_ASCMode_SBIEN_Pos         3                                                       /*!< USIC_CH PCR_ASCMode: SBIEN Position     */
#define USIC_CH_PCR_ASCMode_SBIEN_Msk         (0x01UL << USIC_CH_PCR_ASCMode_SBIEN_Pos)               /*!< USIC_CH PCR_ASCMode: SBIEN Mask         */
#define USIC_CH_PCR_ASCMode_CDEN_Pos          4                                                       /*!< USIC_CH PCR_ASCMode: CDEN Position      */
#define USIC_CH_PCR_ASCMode_CDEN_Msk          (0x01UL << USIC_CH_PCR_ASCMode_CDEN_Pos)                /*!< USIC_CH PCR_ASCMode: CDEN Mask          */
#define USIC_CH_PCR_ASCMode_RNIEN_Pos         5                                                       /*!< USIC_CH PCR_ASCMode: RNIEN Position     */
#define USIC_CH_PCR_ASCMode_RNIEN_Msk         (0x01UL << USIC_CH_PCR_ASCMode_RNIEN_Pos)               /*!< USIC_CH PCR_ASCMode: RNIEN Mask         */
#define USIC_CH_PCR_ASCMode_FEIEN_Pos         6                                                       /*!< USIC_CH PCR_ASCMode: FEIEN Position     */
#define USIC_CH_PCR_ASCMode_FEIEN_Msk         (0x01UL << USIC_CH_PCR_ASCMode_FEIEN_Pos)               /*!< USIC_CH PCR_ASCMode: FEIEN Mask         */
#define USIC_CH_PCR_ASCMode_FFIEN_Pos         7                                                       /*!< USIC_CH PCR_ASCMode: FFIEN Position     */
#define USIC_CH_PCR_ASCMode_FFIEN_Msk         (0x01UL << USIC_CH_PCR_ASCMode_FFIEN_Pos)               /*!< USIC_CH PCR_ASCMode: FFIEN Mask         */
#define USIC_CH_PCR_ASCMode_SP_Pos            8                                                       /*!< USIC_CH PCR_ASCMode: SP Position        */
#define USIC_CH_PCR_ASCMode_SP_Msk            (0x1fUL << USIC_CH_PCR_ASCMode_SP_Pos)                  /*!< USIC_CH PCR_ASCMode: SP Mask            */
#define USIC_CH_PCR_ASCMode_PL_Pos            13                                                      /*!< USIC_CH PCR_ASCMode: PL Position        */
#define USIC_CH_PCR_ASCMode_PL_Msk            (0x07UL << USIC_CH_PCR_ASCMode_PL_Pos)                  /*!< USIC_CH PCR_ASCMode: PL Mask            */
#define USIC_CH_PCR_ASCMode_RSTEN_Pos         16                                                      /*!< USIC_CH PCR_ASCMode: RSTEN Position     */
#define USIC_CH_PCR_ASCMode_RSTEN_Msk         (0x01UL << USIC_CH_PCR_ASCMode_RSTEN_Pos)               /*!< USIC_CH PCR_ASCMode: RSTEN Mask         */
#define USIC_CH_PCR_ASCMode_TSTEN_Pos         17                                                      /*!< USIC_CH PCR_ASCMode: TSTEN Position     */
#define USIC_CH_PCR_ASCMode_TSTEN_Msk         (0x01UL << USIC_CH_PCR_ASCMode_TSTEN_Pos)               /*!< USIC_CH PCR_ASCMode: TSTEN Mask         */
#define USIC_CH_PCR_ASCMode_MCLK_Pos          31                                                      /*!< USIC_CH PCR_ASCMode: MCLK Position      */
#define USIC_CH_PCR_ASCMode_MCLK_Msk          (0x01UL << USIC_CH_PCR_ASCMode_MCLK_Pos)                /*!< USIC_CH PCR_ASCMode: MCLK Mask          */

/* -----------------------------  USIC_CH_PCR_SSCMode  ---------------------------- */
#define USIC_CH_PCR_SSCMode_MSLSEN_Pos        0                                                       /*!< USIC_CH PCR_SSCMode: MSLSEN Position    */
#define USIC_CH_PCR_SSCMode_MSLSEN_Msk        (0x01UL << USIC_CH_PCR_SSCMode_MSLSEN_Pos)              /*!< USIC_CH PCR_SSCMode: MSLSEN Mask        */
#define USIC_CH_PCR_SSCMode_SELCTR_Pos        1                                                       /*!< USIC_CH PCR_SSCMode: SELCTR Position    */
#define USIC_CH_PCR_SSCMode_SELCTR_Msk        (0x01UL << USIC_CH_PCR_SSCMode_SELCTR_Pos)              /*!< USIC_CH PCR_SSCMode: SELCTR Mask        */
#define USIC_CH_PCR_SSCMode_SELINV_Pos        2                                                       /*!< USIC_CH PCR_SSCMode: SELINV Position    */
#define USIC_CH_PCR_SSCMode_SELINV_Msk        (0x01UL << USIC_CH_PCR_SSCMode_SELINV_Pos)              /*!< USIC_CH PCR_SSCMode: SELINV Mask        */
#define USIC_CH_PCR_SSCMode_FEM_Pos           3                                                       /*!< USIC_CH PCR_SSCMode: FEM Position       */
#define USIC_CH_PCR_SSCMode_FEM_Msk           (0x01UL << USIC_CH_PCR_SSCMode_FEM_Pos)                 /*!< USIC_CH PCR_SSCMode: FEM Mask           */
#define USIC_CH_PCR_SSCMode_CTQSEL1_Pos       4                                                       /*!< USIC_CH PCR_SSCMode: CTQSEL1 Position   */
#define USIC_CH_PCR_SSCMode_CTQSEL1_Msk       (0x03UL << USIC_CH_PCR_SSCMode_CTQSEL1_Pos)             /*!< USIC_CH PCR_SSCMode: CTQSEL1 Mask       */
#define USIC_CH_PCR_SSCMode_PCTQ1_Pos         6                                                       /*!< USIC_CH PCR_SSCMode: PCTQ1 Position     */
#define USIC_CH_PCR_SSCMode_PCTQ1_Msk         (0x03UL << USIC_CH_PCR_SSCMode_PCTQ1_Pos)               /*!< USIC_CH PCR_SSCMode: PCTQ1 Mask         */
#define USIC_CH_PCR_SSCMode_DCTQ1_Pos         8                                                       /*!< USIC_CH PCR_SSCMode: DCTQ1 Position     */
#define USIC_CH_PCR_SSCMode_DCTQ1_Msk         (0x1fUL << USIC_CH_PCR_SSCMode_DCTQ1_Pos)               /*!< USIC_CH PCR_SSCMode: DCTQ1 Mask         */
#define USIC_CH_PCR_SSCMode_PARIEN_Pos        13                                                      /*!< USIC_CH PCR_SSCMode: PARIEN Position    */
#define USIC_CH_PCR_SSCMode_PARIEN_Msk        (0x01UL << USIC_CH_PCR_SSCMode_PARIEN_Pos)              /*!< USIC_CH PCR_SSCMode: PARIEN Mask        */
#define USIC_CH_PCR_SSCMode_MSLSIEN_Pos       14                                                      /*!< USIC_CH PCR_SSCMode: MSLSIEN Position   */
#define USIC_CH_PCR_SSCMode_MSLSIEN_Msk       (0x01UL << USIC_CH_PCR_SSCMode_MSLSIEN_Pos)             /*!< USIC_CH PCR_SSCMode: MSLSIEN Mask       */
#define USIC_CH_PCR_SSCMode_DX2TIEN_Pos       15                                                      /*!< USIC_CH PCR_SSCMode: DX2TIEN Position   */
#define USIC_CH_PCR_SSCMode_DX2TIEN_Msk       (0x01UL << USIC_CH_PCR_SSCMode_DX2TIEN_Pos)             /*!< USIC_CH PCR_SSCMode: DX2TIEN Mask       */
#define USIC_CH_PCR_SSCMode_SELO_Pos          16                                                      /*!< USIC_CH PCR_SSCMode: SELO Position      */
#define USIC_CH_PCR_SSCMode_SELO_Msk          (0x000000ffUL << USIC_CH_PCR_SSCMode_SELO_Pos)          /*!< USIC_CH PCR_SSCMode: SELO Mask          */
#define USIC_CH_PCR_SSCMode_TIWEN_Pos         24                                                      /*!< USIC_CH PCR_SSCMode: TIWEN Position     */
#define USIC_CH_PCR_SSCMode_TIWEN_Msk         (0x01UL << USIC_CH_PCR_SSCMode_TIWEN_Pos)               /*!< USIC_CH PCR_SSCMode: TIWEN Mask         */
#define USIC_CH_PCR_SSCMode_MCLK_Pos          31                                                      /*!< USIC_CH PCR_SSCMode: MCLK Position      */
#define USIC_CH_PCR_SSCMode_MCLK_Msk          (0x01UL << USIC_CH_PCR_SSCMode_MCLK_Pos)                /*!< USIC_CH PCR_SSCMode: MCLK Mask          */

/* -----------------------------  USIC_CH_PCR_IICMode  ---------------------------- */
#define USIC_CH_PCR_IICMode_SLAD_Pos          0                                                       /*!< USIC_CH PCR_IICMode: SLAD Position      */
#define USIC_CH_PCR_IICMode_SLAD_Msk          (0x0000ffffUL << USIC_CH_PCR_IICMode_SLAD_Pos)          /*!< USIC_CH PCR_IICMode: SLAD Mask          */
#define USIC_CH_PCR_IICMode_ACK00_Pos         16                                                      /*!< USIC_CH PCR_IICMode: ACK00 Position     */
#define USIC_CH_PCR_IICMode_ACK00_Msk         (0x01UL << USIC_CH_PCR_IICMode_ACK00_Pos)               /*!< USIC_CH PCR_IICMode: ACK00 Mask         */
#define USIC_CH_PCR_IICMode_STIM_Pos          17                                                      /*!< USIC_CH PCR_IICMode: STIM Position      */
#define USIC_CH_PCR_IICMode_STIM_Msk          (0x01UL << USIC_CH_PCR_IICMode_STIM_Pos)                /*!< USIC_CH PCR_IICMode: STIM Mask          */
#define USIC_CH_PCR_IICMode_SCRIEN_Pos        18                                                      /*!< USIC_CH PCR_IICMode: SCRIEN Position    */
#define USIC_CH_PCR_IICMode_SCRIEN_Msk        (0x01UL << USIC_CH_PCR_IICMode_SCRIEN_Pos)              /*!< USIC_CH PCR_IICMode: SCRIEN Mask        */
#define USIC_CH_PCR_IICMode_RSCRIEN_Pos       19                                                      /*!< USIC_CH PCR_IICMode: RSCRIEN Position   */
#define USIC_CH_PCR_IICMode_RSCRIEN_Msk       (0x01UL << USIC_CH_PCR_IICMode_RSCRIEN_Pos)             /*!< USIC_CH PCR_IICMode: RSCRIEN Mask       */
#define USIC_CH_PCR_IICMode_PCRIEN_Pos        20                                                      /*!< USIC_CH PCR_IICMode: PCRIEN Position    */
#define USIC_CH_PCR_IICMode_PCRIEN_Msk        (0x01UL << USIC_CH_PCR_IICMode_PCRIEN_Pos)              /*!< USIC_CH PCR_IICMode: PCRIEN Mask        */
#define USIC_CH_PCR_IICMode_NACKIEN_Pos       21                                                      /*!< USIC_CH PCR_IICMode: NACKIEN Position   */
#define USIC_CH_PCR_IICMode_NACKIEN_Msk       (0x01UL << USIC_CH_PCR_IICMode_NACKIEN_Pos)             /*!< USIC_CH PCR_IICMode: NACKIEN Mask       */
#define USIC_CH_PCR_IICMode_ARLIEN_Pos        22                                                      /*!< USIC_CH PCR_IICMode: ARLIEN Position    */
#define USIC_CH_PCR_IICMode_ARLIEN_Msk        (0x01UL << USIC_CH_PCR_IICMode_ARLIEN_Pos)              /*!< USIC_CH PCR_IICMode: ARLIEN Mask        */
#define USIC_CH_PCR_IICMode_SRRIEN_Pos        23                                                      /*!< USIC_CH PCR_IICMode: SRRIEN Position    */
#define USIC_CH_PCR_IICMode_SRRIEN_Msk        (0x01UL << USIC_CH_PCR_IICMode_SRRIEN_Pos)              /*!< USIC_CH PCR_IICMode: SRRIEN Mask        */
#define USIC_CH_PCR_IICMode_ERRIEN_Pos        24                                                      /*!< USIC_CH PCR_IICMode: ERRIEN Position    */
#define USIC_CH_PCR_IICMode_ERRIEN_Msk        (0x01UL << USIC_CH_PCR_IICMode_ERRIEN_Pos)              /*!< USIC_CH PCR_IICMode: ERRIEN Mask        */
#define USIC_CH_PCR_IICMode_SACKDIS_Pos       25                                                      /*!< USIC_CH PCR_IICMode: SACKDIS Position   */
#define USIC_CH_PCR_IICMode_SACKDIS_Msk       (0x01UL << USIC_CH_PCR_IICMode_SACKDIS_Pos)             /*!< USIC_CH PCR_IICMode: SACKDIS Mask       */
#define USIC_CH_PCR_IICMode_HDEL_Pos          26                                                      /*!< USIC_CH PCR_IICMode: HDEL Position      */
#define USIC_CH_PCR_IICMode_HDEL_Msk          (0x0fUL << USIC_CH_PCR_IICMode_HDEL_Pos)                /*!< USIC_CH PCR_IICMode: HDEL Mask          */
#define USIC_CH_PCR_IICMode_ACKIEN_Pos        30                                                      /*!< USIC_CH PCR_IICMode: ACKIEN Position    */
#define USIC_CH_PCR_IICMode_ACKIEN_Msk        (0x01UL << USIC_CH_PCR_IICMode_ACKIEN_Pos)              /*!< USIC_CH PCR_IICMode: ACKIEN Mask        */
#define USIC_CH_PCR_IICMode_MCLK_Pos          31                                                      /*!< USIC_CH PCR_IICMode: MCLK Position      */
#define USIC_CH_PCR_IICMode_MCLK_Msk          (0x01UL << USIC_CH_PCR_IICMode_MCLK_Pos)                /*!< USIC_CH PCR_IICMode: MCLK Mask          */

/* -----------------------------  USIC_CH_PCR_IISMode  ---------------------------- */
#define USIC_CH_PCR_IISMode_WAGEN_Pos         0                                                       /*!< USIC_CH PCR_IISMode: WAGEN Position     */
#define USIC_CH_PCR_IISMode_WAGEN_Msk         (0x01UL << USIC_CH_PCR_IISMode_WAGEN_Pos)               /*!< USIC_CH PCR_IISMode: WAGEN Mask         */
#define USIC_CH_PCR_IISMode_DTEN_Pos          1                                                       /*!< USIC_CH PCR_IISMode: DTEN Position      */
#define USIC_CH_PCR_IISMode_DTEN_Msk          (0x01UL << USIC_CH_PCR_IISMode_DTEN_Pos)                /*!< USIC_CH PCR_IISMode: DTEN Mask          */
#define USIC_CH_PCR_IISMode_SELINV_Pos        2                                                       /*!< USIC_CH PCR_IISMode: SELINV Position    */
#define USIC_CH_PCR_IISMode_SELINV_Msk        (0x01UL << USIC_CH_PCR_IISMode_SELINV_Pos)              /*!< USIC_CH PCR_IISMode: SELINV Mask        */
#define USIC_CH_PCR_IISMode_WAFEIEN_Pos       4                                                       /*!< USIC_CH PCR_IISMode: WAFEIEN Position   */
#define USIC_CH_PCR_IISMode_WAFEIEN_Msk       (0x01UL << USIC_CH_PCR_IISMode_WAFEIEN_Pos)             /*!< USIC_CH PCR_IISMode: WAFEIEN Mask       */
#define USIC_CH_PCR_IISMode_WAREIEN_Pos       5                                                       /*!< USIC_CH PCR_IISMode: WAREIEN Position   */
#define USIC_CH_PCR_IISMode_WAREIEN_Msk       (0x01UL << USIC_CH_PCR_IISMode_WAREIEN_Pos)             /*!< USIC_CH PCR_IISMode: WAREIEN Mask       */
#define USIC_CH_PCR_IISMode_ENDIEN_Pos        6                                                       /*!< USIC_CH PCR_IISMode: ENDIEN Position    */
#define USIC_CH_PCR_IISMode_ENDIEN_Msk        (0x01UL << USIC_CH_PCR_IISMode_ENDIEN_Pos)              /*!< USIC_CH PCR_IISMode: ENDIEN Mask        */
#define USIC_CH_PCR_IISMode_DX2TIEN_Pos       15                                                      /*!< USIC_CH PCR_IISMode: DX2TIEN Position   */
#define USIC_CH_PCR_IISMode_DX2TIEN_Msk       (0x01UL << USIC_CH_PCR_IISMode_DX2TIEN_Pos)             /*!< USIC_CH PCR_IISMode: DX2TIEN Mask       */
#define USIC_CH_PCR_IISMode_TDEL_Pos          16                                                      /*!< USIC_CH PCR_IISMode: TDEL Position      */
#define USIC_CH_PCR_IISMode_TDEL_Msk          (0x3fUL << USIC_CH_PCR_IISMode_TDEL_Pos)                /*!< USIC_CH PCR_IISMode: TDEL Mask          */
#define USIC_CH_PCR_IISMode_MCLK_Pos          31                                                      /*!< USIC_CH PCR_IISMode: MCLK Position      */
#define USIC_CH_PCR_IISMode_MCLK_Msk          (0x01UL << USIC_CH_PCR_IISMode_MCLK_Pos)                /*!< USIC_CH PCR_IISMode: MCLK Mask          */

/* ---------------------------------  USIC_CH_CCR  -------------------------------- */
#define USIC_CH_CCR_MODE_Pos                  0                                                       /*!< USIC_CH CCR: MODE Position              */
#define USIC_CH_CCR_MODE_Msk                  (0x0fUL << USIC_CH_CCR_MODE_Pos)                        /*!< USIC_CH CCR: MODE Mask                  */
#define USIC_CH_CCR_HPCEN_Pos                 6                                                       /*!< USIC_CH CCR: HPCEN Position             */
#define USIC_CH_CCR_HPCEN_Msk                 (0x03UL << USIC_CH_CCR_HPCEN_Pos)                       /*!< USIC_CH CCR: HPCEN Mask                 */
#define USIC_CH_CCR_PM_Pos                    8                                                       /*!< USIC_CH CCR: PM Position                */
#define USIC_CH_CCR_PM_Msk                    (0x03UL << USIC_CH_CCR_PM_Pos)                          /*!< USIC_CH CCR: PM Mask                    */
#define USIC_CH_CCR_RSIEN_Pos                 10                                                      /*!< USIC_CH CCR: RSIEN Position             */
#define USIC_CH_CCR_RSIEN_Msk                 (0x01UL << USIC_CH_CCR_RSIEN_Pos)                       /*!< USIC_CH CCR: RSIEN Mask                 */
#define USIC_CH_CCR_DLIEN_Pos                 11                                                      /*!< USIC_CH CCR: DLIEN Position             */
#define USIC_CH_CCR_DLIEN_Msk                 (0x01UL << USIC_CH_CCR_DLIEN_Pos)                       /*!< USIC_CH CCR: DLIEN Mask                 */
#define USIC_CH_CCR_TSIEN_Pos                 12                                                      /*!< USIC_CH CCR: TSIEN Position             */
#define USIC_CH_CCR_TSIEN_Msk                 (0x01UL << USIC_CH_CCR_TSIEN_Pos)                       /*!< USIC_CH CCR: TSIEN Mask                 */
#define USIC_CH_CCR_TBIEN_Pos                 13                                                      /*!< USIC_CH CCR: TBIEN Position             */
#define USIC_CH_CCR_TBIEN_Msk                 (0x01UL << USIC_CH_CCR_TBIEN_Pos)                       /*!< USIC_CH CCR: TBIEN Mask                 */
#define USIC_CH_CCR_RIEN_Pos                  14                                                      /*!< USIC_CH CCR: RIEN Position              */
#define USIC_CH_CCR_RIEN_Msk                  (0x01UL << USIC_CH_CCR_RIEN_Pos)                        /*!< USIC_CH CCR: RIEN Mask                  */
#define USIC_CH_CCR_AIEN_Pos                  15                                                      /*!< USIC_CH CCR: AIEN Position              */
#define USIC_CH_CCR_AIEN_Msk                  (0x01UL << USIC_CH_CCR_AIEN_Pos)                        /*!< USIC_CH CCR: AIEN Mask                  */
#define USIC_CH_CCR_BRGIEN_Pos                16                                                      /*!< USIC_CH CCR: BRGIEN Position            */
#define USIC_CH_CCR_BRGIEN_Msk                (0x01UL << USIC_CH_CCR_BRGIEN_Pos)                      /*!< USIC_CH CCR: BRGIEN Mask                */

/* --------------------------------  USIC_CH_CMTR  -------------------------------- */
#define USIC_CH_CMTR_CTV_Pos                  0                                                       /*!< USIC_CH CMTR: CTV Position              */
#define USIC_CH_CMTR_CTV_Msk                  (0x000003ffUL << USIC_CH_CMTR_CTV_Pos)                  /*!< USIC_CH CMTR: CTV Mask                  */

/* ---------------------------------  USIC_CH_PSR  -------------------------------- */
#define USIC_CH_PSR_ST0_Pos                   0                                                       /*!< USIC_CH PSR: ST0 Position               */
#define USIC_CH_PSR_ST0_Msk                   (0x01UL << USIC_CH_PSR_ST0_Pos)                         /*!< USIC_CH PSR: ST0 Mask                   */
#define USIC_CH_PSR_ST1_Pos                   1                                                       /*!< USIC_CH PSR: ST1 Position               */
#define USIC_CH_PSR_ST1_Msk                   (0x01UL << USIC_CH_PSR_ST1_Pos)                         /*!< USIC_CH PSR: ST1 Mask                   */
#define USIC_CH_PSR_ST2_Pos                   2                                                       /*!< USIC_CH PSR: ST2 Position               */
#define USIC_CH_PSR_ST2_Msk                   (0x01UL << USIC_CH_PSR_ST2_Pos)                         /*!< USIC_CH PSR: ST2 Mask                   */
#define USIC_CH_PSR_ST3_Pos                   3                                                       /*!< USIC_CH PSR: ST3 Position               */
#define USIC_CH_PSR_ST3_Msk                   (0x01UL << USIC_CH_PSR_ST3_Pos)                         /*!< USIC_CH PSR: ST3 Mask                   */
#define USIC_CH_PSR_ST4_Pos                   4                                                       /*!< USIC_CH PSR: ST4 Position               */
#define USIC_CH_PSR_ST4_Msk                   (0x01UL << USIC_CH_PSR_ST4_Pos)                         /*!< USIC_CH PSR: ST4 Mask                   */
#define USIC_CH_PSR_ST5_Pos                   5                                                       /*!< USIC_CH PSR: ST5 Position               */
#define USIC_CH_PSR_ST5_Msk                   (0x01UL << USIC_CH_PSR_ST5_Pos)                         /*!< USIC_CH PSR: ST5 Mask                   */
#define USIC_CH_PSR_ST6_Pos                   6                                                       /*!< USIC_CH PSR: ST6 Position               */
#define USIC_CH_PSR_ST6_Msk                   (0x01UL << USIC_CH_PSR_ST6_Pos)                         /*!< USIC_CH PSR: ST6 Mask                   */
#define USIC_CH_PSR_ST7_Pos                   7                                                       /*!< USIC_CH PSR: ST7 Position               */
#define USIC_CH_PSR_ST7_Msk                   (0x01UL << USIC_CH_PSR_ST7_Pos)                         /*!< USIC_CH PSR: ST7 Mask                   */
#define USIC_CH_PSR_ST8_Pos                   8                                                       /*!< USIC_CH PSR: ST8 Position               */
#define USIC_CH_PSR_ST8_Msk                   (0x01UL << USIC_CH_PSR_ST8_Pos)                         /*!< USIC_CH PSR: ST8 Mask                   */
#define USIC_CH_PSR_ST9_Pos                   9                                                       /*!< USIC_CH PSR: ST9 Position               */
#define USIC_CH_PSR_ST9_Msk                   (0x01UL << USIC_CH_PSR_ST9_Pos)                         /*!< USIC_CH PSR: ST9 Mask                   */
#define USIC_CH_PSR_RSIF_Pos                  10                                                      /*!< USIC_CH PSR: RSIF Position              */
#define USIC_CH_PSR_RSIF_Msk                  (0x01UL << USIC_CH_PSR_RSIF_Pos)                        /*!< USIC_CH PSR: RSIF Mask                  */
#define USIC_CH_PSR_DLIF_Pos                  11                                                      /*!< USIC_CH PSR: DLIF Position              */
#define USIC_CH_PSR_DLIF_Msk                  (0x01UL << USIC_CH_PSR_DLIF_Pos)                        /*!< USIC_CH PSR: DLIF Mask                  */
#define USIC_CH_PSR_TSIF_Pos                  12                                                      /*!< USIC_CH PSR: TSIF Position              */
#define USIC_CH_PSR_TSIF_Msk                  (0x01UL << USIC_CH_PSR_TSIF_Pos)                        /*!< USIC_CH PSR: TSIF Mask                  */
#define USIC_CH_PSR_TBIF_Pos                  13                                                      /*!< USIC_CH PSR: TBIF Position              */
#define USIC_CH_PSR_TBIF_Msk                  (0x01UL << USIC_CH_PSR_TBIF_Pos)                        /*!< USIC_CH PSR: TBIF Mask                  */
#define USIC_CH_PSR_RIF_Pos                   14                                                      /*!< USIC_CH PSR: RIF Position               */
#define USIC_CH_PSR_RIF_Msk                   (0x01UL << USIC_CH_PSR_RIF_Pos)                         /*!< USIC_CH PSR: RIF Mask                   */
#define USIC_CH_PSR_AIF_Pos                   15                                                      /*!< USIC_CH PSR: AIF Position               */
#define USIC_CH_PSR_AIF_Msk                   (0x01UL << USIC_CH_PSR_AIF_Pos)                         /*!< USIC_CH PSR: AIF Mask                   */
#define USIC_CH_PSR_BRGIF_Pos                 16                                                      /*!< USIC_CH PSR: BRGIF Position             */
#define USIC_CH_PSR_BRGIF_Msk                 (0x01UL << USIC_CH_PSR_BRGIF_Pos)                       /*!< USIC_CH PSR: BRGIF Mask                 */

/* -----------------------------  USIC_CH_PSR_ASCMode  ---------------------------- */
#define USIC_CH_PSR_ASCMode_TXIDLE_Pos        0                                                       /*!< USIC_CH PSR_ASCMode: TXIDLE Position    */
#define USIC_CH_PSR_ASCMode_TXIDLE_Msk        (0x01UL << USIC_CH_PSR_ASCMode_TXIDLE_Pos)              /*!< USIC_CH PSR_ASCMode: TXIDLE Mask        */
#define USIC_CH_PSR_ASCMode_RXIDLE_Pos        1                                                       /*!< USIC_CH PSR_ASCMode: RXIDLE Position    */
#define USIC_CH_PSR_ASCMode_RXIDLE_Msk        (0x01UL << USIC_CH_PSR_ASCMode_RXIDLE_Pos)              /*!< USIC_CH PSR_ASCMode: RXIDLE Mask        */
#define USIC_CH_PSR_ASCMode_SBD_Pos           2                                                       /*!< USIC_CH PSR_ASCMode: SBD Position       */
#define USIC_CH_PSR_ASCMode_SBD_Msk           (0x01UL << USIC_CH_PSR_ASCMode_SBD_Pos)                 /*!< USIC_CH PSR_ASCMode: SBD Mask           */
#define USIC_CH_PSR_ASCMode_COL_Pos           3                                                       /*!< USIC_CH PSR_ASCMode: COL Position       */
#define USIC_CH_PSR_ASCMode_COL_Msk           (0x01UL << USIC_CH_PSR_ASCMode_COL_Pos)                 /*!< USIC_CH PSR_ASCMode: COL Mask           */
#define USIC_CH_PSR_ASCMode_RNS_Pos           4                                                       /*!< USIC_CH PSR_ASCMode: RNS Position       */
#define USIC_CH_PSR_ASCMode_RNS_Msk           (0x01UL << USIC_CH_PSR_ASCMode_RNS_Pos)                 /*!< USIC_CH PSR_ASCMode: RNS Mask           */
#define USIC_CH_PSR_ASCMode_FER0_Pos          5                                                       /*!< USIC_CH PSR_ASCMode: FER0 Position      */
#define USIC_CH_PSR_ASCMode_FER0_Msk          (0x01UL << USIC_CH_PSR_ASCMode_FER0_Pos)                /*!< USIC_CH PSR_ASCMode: FER0 Mask          */
#define USIC_CH_PSR_ASCMode_FER1_Pos          6                                                       /*!< USIC_CH PSR_ASCMode: FER1 Position      */
#define USIC_CH_PSR_ASCMode_FER1_Msk          (0x01UL << USIC_CH_PSR_ASCMode_FER1_Pos)                /*!< USIC_CH PSR_ASCMode: FER1 Mask          */
#define USIC_CH_PSR_ASCMode_RFF_Pos           7                                                       /*!< USIC_CH PSR_ASCMode: RFF Position       */
#define USIC_CH_PSR_ASCMode_RFF_Msk           (0x01UL << USIC_CH_PSR_ASCMode_RFF_Pos)                 /*!< USIC_CH PSR_ASCMode: RFF Mask           */
#define USIC_CH_PSR_ASCMode_TFF_Pos           8                                                       /*!< USIC_CH PSR_ASCMode: TFF Position       */
#define USIC_CH_PSR_ASCMode_TFF_Msk           (0x01UL << USIC_CH_PSR_ASCMode_TFF_Pos)                 /*!< USIC_CH PSR_ASCMode: TFF Mask           */
#define USIC_CH_PSR_ASCMode_BUSY_Pos          9                                                       /*!< USIC_CH PSR_ASCMode: BUSY Position      */
#define USIC_CH_PSR_ASCMode_BUSY_Msk          (0x01UL << USIC_CH_PSR_ASCMode_BUSY_Pos)                /*!< USIC_CH PSR_ASCMode: BUSY Mask          */
#define USIC_CH_PSR_ASCMode_RSIF_Pos          10                                                      /*!< USIC_CH PSR_ASCMode: RSIF Position      */
#define USIC_CH_PSR_ASCMode_RSIF_Msk          (0x01UL << USIC_CH_PSR_ASCMode_RSIF_Pos)                /*!< USIC_CH PSR_ASCMode: RSIF Mask          */
#define USIC_CH_PSR_ASCMode_DLIF_Pos          11                                                      /*!< USIC_CH PSR_ASCMode: DLIF Position      */
#define USIC_CH_PSR_ASCMode_DLIF_Msk          (0x01UL << USIC_CH_PSR_ASCMode_DLIF_Pos)                /*!< USIC_CH PSR_ASCMode: DLIF Mask          */
#define USIC_CH_PSR_ASCMode_TSIF_Pos          12                                                      /*!< USIC_CH PSR_ASCMode: TSIF Position      */
#define USIC_CH_PSR_ASCMode_TSIF_Msk          (0x01UL << USIC_CH_PSR_ASCMode_TSIF_Pos)                /*!< USIC_CH PSR_ASCMode: TSIF Mask          */
#define USIC_CH_PSR_ASCMode_TBIF_Pos          13                                                      /*!< USIC_CH PSR_ASCMode: TBIF Position      */
#define USIC_CH_PSR_ASCMode_TBIF_Msk          (0x01UL << USIC_CH_PSR_ASCMode_TBIF_Pos)                /*!< USIC_CH PSR_ASCMode: TBIF Mask          */
#define USIC_CH_PSR_ASCMode_RIF_Pos           14                                                      /*!< USIC_CH PSR_ASCMode: RIF Position       */
#define USIC_CH_PSR_ASCMode_RIF_Msk           (0x01UL << USIC_CH_PSR_ASCMode_RIF_Pos)                 /*!< USIC_CH PSR_ASCMode: RIF Mask           */
#define USIC_CH_PSR_ASCMode_AIF_Pos           15                                                      /*!< USIC_CH PSR_ASCMode: AIF Position       */
#define USIC_CH_PSR_ASCMode_AIF_Msk           (0x01UL << USIC_CH_PSR_ASCMode_AIF_Pos)                 /*!< USIC_CH PSR_ASCMode: AIF Mask           */
#define USIC_CH_PSR_ASCMode_BRGIF_Pos         16                                                      /*!< USIC_CH PSR_ASCMode: BRGIF Position     */
#define USIC_CH_PSR_ASCMode_BRGIF_Msk         (0x01UL << USIC_CH_PSR_ASCMode_BRGIF_Pos)               /*!< USIC_CH PSR_ASCMode: BRGIF Mask         */

/* -----------------------------  USIC_CH_PSR_SSCMode  ---------------------------- */
#define USIC_CH_PSR_SSCMode_MSLS_Pos          0                                                       /*!< USIC_CH PSR_SSCMode: MSLS Position      */
#define USIC_CH_PSR_SSCMode_MSLS_Msk          (0x01UL << USIC_CH_PSR_SSCMode_MSLS_Pos)                /*!< USIC_CH PSR_SSCMode: MSLS Mask          */
#define USIC_CH_PSR_SSCMode_DX2S_Pos          1                                                       /*!< USIC_CH PSR_SSCMode: DX2S Position      */
#define USIC_CH_PSR_SSCMode_DX2S_Msk          (0x01UL << USIC_CH_PSR_SSCMode_DX2S_Pos)                /*!< USIC_CH PSR_SSCMode: DX2S Mask          */
#define USIC_CH_PSR_SSCMode_MSLSEV_Pos        2                                                       /*!< USIC_CH PSR_SSCMode: MSLSEV Position    */
#define USIC_CH_PSR_SSCMode_MSLSEV_Msk        (0x01UL << USIC_CH_PSR_SSCMode_MSLSEV_Pos)              /*!< USIC_CH PSR_SSCMode: MSLSEV Mask        */
#define USIC_CH_PSR_SSCMode_DX2TEV_Pos        3                                                       /*!< USIC_CH PSR_SSCMode: DX2TEV Position    */
#define USIC_CH_PSR_SSCMode_DX2TEV_Msk        (0x01UL << USIC_CH_PSR_SSCMode_DX2TEV_Pos)              /*!< USIC_CH PSR_SSCMode: DX2TEV Mask        */
#define USIC_CH_PSR_SSCMode_PARERR_Pos        4                                                       /*!< USIC_CH PSR_SSCMode: PARERR Position    */
#define USIC_CH_PSR_SSCMode_PARERR_Msk        (0x01UL << USIC_CH_PSR_SSCMode_PARERR_Pos)              /*!< USIC_CH PSR_SSCMode: PARERR Mask        */
#define USIC_CH_PSR_SSCMode_RSIF_Pos          10                                                      /*!< USIC_CH PSR_SSCMode: RSIF Position      */
#define USIC_CH_PSR_SSCMode_RSIF_Msk          (0x01UL << USIC_CH_PSR_SSCMode_RSIF_Pos)                /*!< USIC_CH PSR_SSCMode: RSIF Mask          */
#define USIC_CH_PSR_SSCMode_DLIF_Pos          11                                                      /*!< USIC_CH PSR_SSCMode: DLIF Position      */
#define USIC_CH_PSR_SSCMode_DLIF_Msk          (0x01UL << USIC_CH_PSR_SSCMode_DLIF_Pos)                /*!< USIC_CH PSR_SSCMode: DLIF Mask          */
#define USIC_CH_PSR_SSCMode_TSIF_Pos          12                                                      /*!< USIC_CH PSR_SSCMode: TSIF Position      */
#define USIC_CH_PSR_SSCMode_TSIF_Msk          (0x01UL << USIC_CH_PSR_SSCMode_TSIF_Pos)                /*!< USIC_CH PSR_SSCMode: TSIF Mask          */
#define USIC_CH_PSR_SSCMode_TBIF_Pos          13                                                      /*!< USIC_CH PSR_SSCMode: TBIF Position      */
#define USIC_CH_PSR_SSCMode_TBIF_Msk          (0x01UL << USIC_CH_PSR_SSCMode_TBIF_Pos)                /*!< USIC_CH PSR_SSCMode: TBIF Mask          */
#define USIC_CH_PSR_SSCMode_RIF_Pos           14                                                      /*!< USIC_CH PSR_SSCMode: RIF Position       */
#define USIC_CH_PSR_SSCMode_RIF_Msk           (0x01UL << USIC_CH_PSR_SSCMode_RIF_Pos)                 /*!< USIC_CH PSR_SSCMode: RIF Mask           */
#define USIC_CH_PSR_SSCMode_AIF_Pos           15                                                      /*!< USIC_CH PSR_SSCMode: AIF Position       */
#define USIC_CH_PSR_SSCMode_AIF_Msk           (0x01UL << USIC_CH_PSR_SSCMode_AIF_Pos)                 /*!< USIC_CH PSR_SSCMode: AIF Mask           */
#define USIC_CH_PSR_SSCMode_BRGIF_Pos         16                                                      /*!< USIC_CH PSR_SSCMode: BRGIF Position     */
#define USIC_CH_PSR_SSCMode_BRGIF_Msk         (0x01UL << USIC_CH_PSR_SSCMode_BRGIF_Pos)               /*!< USIC_CH PSR_SSCMode: BRGIF Mask         */

/* -----------------------------  USIC_CH_PSR_IICMode  ---------------------------- */
#define USIC_CH_PSR_IICMode_SLSEL_Pos         0                                                       /*!< USIC_CH PSR_IICMode: SLSEL Position     */
#define USIC_CH_PSR_IICMode_SLSEL_Msk         (0x01UL << USIC_CH_PSR_IICMode_SLSEL_Pos)               /*!< USIC_CH PSR_IICMode: SLSEL Mask         */
#define USIC_CH_PSR_IICMode_WTDF_Pos          1                                                       /*!< USIC_CH PSR_IICMode: WTDF Position      */
#define USIC_CH_PSR_IICMode_WTDF_Msk          (0x01UL << USIC_CH_PSR_IICMode_WTDF_Pos)                /*!< USIC_CH PSR_IICMode: WTDF Mask          */
#define USIC_CH_PSR_IICMode_SCR_Pos           2                                                       /*!< USIC_CH PSR_IICMode: SCR Position       */
#define USIC_CH_PSR_IICMode_SCR_Msk           (0x01UL << USIC_CH_PSR_IICMode_SCR_Pos)                 /*!< USIC_CH PSR_IICMode: SCR Mask           */
#define USIC_CH_PSR_IICMode_RSCR_Pos          3                                                       /*!< USIC_CH PSR_IICMode: RSCR Position      */
#define USIC_CH_PSR_IICMode_RSCR_Msk          (0x01UL << USIC_CH_PSR_IICMode_RSCR_Pos)                /*!< USIC_CH PSR_IICMode: RSCR Mask          */
#define USIC_CH_PSR_IICMode_PCR_Pos           4                                                       /*!< USIC_CH PSR_IICMode: PCR Position       */
#define USIC_CH_PSR_IICMode_PCR_Msk           (0x01UL << USIC_CH_PSR_IICMode_PCR_Pos)                 /*!< USIC_CH PSR_IICMode: PCR Mask           */
#define USIC_CH_PSR_IICMode_NACK_Pos          5                                                       /*!< USIC_CH PSR_IICMode: NACK Position      */
#define USIC_CH_PSR_IICMode_NACK_Msk          (0x01UL << USIC_CH_PSR_IICMode_NACK_Pos)                /*!< USIC_CH PSR_IICMode: NACK Mask          */
#define USIC_CH_PSR_IICMode_ARL_Pos           6                                                       /*!< USIC_CH PSR_IICMode: ARL Position       */
#define USIC_CH_PSR_IICMode_ARL_Msk           (0x01UL << USIC_CH_PSR_IICMode_ARL_Pos)                 /*!< USIC_CH PSR_IICMode: ARL Mask           */
#define USIC_CH_PSR_IICMode_SRR_Pos           7                                                       /*!< USIC_CH PSR_IICMode: SRR Position       */
#define USIC_CH_PSR_IICMode_SRR_Msk           (0x01UL << USIC_CH_PSR_IICMode_SRR_Pos)                 /*!< USIC_CH PSR_IICMode: SRR Mask           */
#define USIC_CH_PSR_IICMode_ERR_Pos           8                                                       /*!< USIC_CH PSR_IICMode: ERR Position       */
#define USIC_CH_PSR_IICMode_ERR_Msk           (0x01UL << USIC_CH_PSR_IICMode_ERR_Pos)                 /*!< USIC_CH PSR_IICMode: ERR Mask           */
#define USIC_CH_PSR_IICMode_ACK_Pos           9                                                       /*!< USIC_CH PSR_IICMode: ACK Position       */
#define USIC_CH_PSR_IICMode_ACK_Msk           (0x01UL << USIC_CH_PSR_IICMode_ACK_Pos)                 /*!< USIC_CH PSR_IICMode: ACK Mask           */
#define USIC_CH_PSR_IICMode_RSIF_Pos          10                                                      /*!< USIC_CH PSR_IICMode: RSIF Position      */
#define USIC_CH_PSR_IICMode_RSIF_Msk          (0x01UL << USIC_CH_PSR_IICMode_RSIF_Pos)                /*!< USIC_CH PSR_IICMode: RSIF Mask          */
#define USIC_CH_PSR_IICMode_DLIF_Pos          11                                                      /*!< USIC_CH PSR_IICMode: DLIF Position      */
#define USIC_CH_PSR_IICMode_DLIF_Msk          (0x01UL << USIC_CH_PSR_IICMode_DLIF_Pos)                /*!< USIC_CH PSR_IICMode: DLIF Mask          */
#define USIC_CH_PSR_IICMode_TSIF_Pos          12                                                      /*!< USIC_CH PSR_IICMode: TSIF Position      */
#define USIC_CH_PSR_IICMode_TSIF_Msk          (0x01UL << USIC_CH_PSR_IICMode_TSIF_Pos)                /*!< USIC_CH PSR_IICMode: TSIF Mask          */
#define USIC_CH_PSR_IICMode_TBIF_Pos          13                                                      /*!< USIC_CH PSR_IICMode: TBIF Position      */
#define USIC_CH_PSR_IICMode_TBIF_Msk          (0x01UL << USIC_CH_PSR_IICMode_TBIF_Pos)                /*!< USIC_CH PSR_IICMode: TBIF Mask          */
#define USIC_CH_PSR_IICMode_RIF_Pos           14                                                      /*!< USIC_CH PSR_IICMode: RIF Position       */
#define USIC_CH_PSR_IICMode_RIF_Msk           (0x01UL << USIC_CH_PSR_IICMode_RIF_Pos)                 /*!< USIC_CH PSR_IICMode: RIF Mask           */
#define USIC_CH_PSR_IICMode_AIF_Pos           15                                                      /*!< USIC_CH PSR_IICMode: AIF Position       */
#define USIC_CH_PSR_IICMode_AIF_Msk           (0x01UL << USIC_CH_PSR_IICMode_AIF_Pos)                 /*!< USIC_CH PSR_IICMode: AIF Mask           */
#define USIC_CH_PSR_IICMode_BRGIF_Pos         16                                                      /*!< USIC_CH PSR_IICMode: BRGIF Position     */
#define USIC_CH_PSR_IICMode_BRGIF_Msk         (0x01UL << USIC_CH_PSR_IICMode_BRGIF_Pos)               /*!< USIC_CH PSR_IICMode: BRGIF Mask         */

/* -----------------------------  USIC_CH_PSR_IISMode  ---------------------------- */
#define USIC_CH_PSR_IISMode_WA_Pos            0                                                       /*!< USIC_CH PSR_IISMode: WA Position        */
#define USIC_CH_PSR_IISMode_WA_Msk            (0x01UL << USIC_CH_PSR_IISMode_WA_Pos)                  /*!< USIC_CH PSR_IISMode: WA Mask            */
#define USIC_CH_PSR_IISMode_DX2S_Pos          1                                                       /*!< USIC_CH PSR_IISMode: DX2S Position      */
#define USIC_CH_PSR_IISMode_DX2S_Msk          (0x01UL << USIC_CH_PSR_IISMode_DX2S_Pos)                /*!< USIC_CH PSR_IISMode: DX2S Mask          */
#define USIC_CH_PSR_IISMode_DX2TEV_Pos        3                                                       /*!< USIC_CH PSR_IISMode: DX2TEV Position    */
#define USIC_CH_PSR_IISMode_DX2TEV_Msk        (0x01UL << USIC_CH_PSR_IISMode_DX2TEV_Pos)              /*!< USIC_CH PSR_IISMode: DX2TEV Mask        */
#define USIC_CH_PSR_IISMode_WAFE_Pos          4                                                       /*!< USIC_CH PSR_IISMode: WAFE Position      */
#define USIC_CH_PSR_IISMode_WAFE_Msk          (0x01UL << USIC_CH_PSR_IISMode_WAFE_Pos)                /*!< USIC_CH PSR_IISMode: WAFE Mask          */
#define USIC_CH_PSR_IISMode_WARE_Pos          5                                                       /*!< USIC_CH PSR_IISMode: WARE Position      */
#define USIC_CH_PSR_IISMode_WARE_Msk          (0x01UL << USIC_CH_PSR_IISMode_WARE_Pos)                /*!< USIC_CH PSR_IISMode: WARE Mask          */
#define USIC_CH_PSR_IISMode_END_Pos           6                                                       /*!< USIC_CH PSR_IISMode: END Position       */
#define USIC_CH_PSR_IISMode_END_Msk           (0x01UL << USIC_CH_PSR_IISMode_END_Pos)                 /*!< USIC_CH PSR_IISMode: END Mask           */
#define USIC_CH_PSR_IISMode_RSIF_Pos          10                                                      /*!< USIC_CH PSR_IISMode: RSIF Position      */
#define USIC_CH_PSR_IISMode_RSIF_Msk          (0x01UL << USIC_CH_PSR_IISMode_RSIF_Pos)                /*!< USIC_CH PSR_IISMode: RSIF Mask          */
#define USIC_CH_PSR_IISMode_DLIF_Pos          11                                                      /*!< USIC_CH PSR_IISMode: DLIF Position      */
#define USIC_CH_PSR_IISMode_DLIF_Msk          (0x01UL << USIC_CH_PSR_IISMode_DLIF_Pos)                /*!< USIC_CH PSR_IISMode: DLIF Mask          */
#define USIC_CH_PSR_IISMode_TSIF_Pos          12                                                      /*!< USIC_CH PSR_IISMode: TSIF Position      */
#define USIC_CH_PSR_IISMode_TSIF_Msk          (0x01UL << USIC_CH_PSR_IISMode_TSIF_Pos)                /*!< USIC_CH PSR_IISMode: TSIF Mask          */
#define USIC_CH_PSR_IISMode_TBIF_Pos          13                                                      /*!< USIC_CH PSR_IISMode: TBIF Position      */
#define USIC_CH_PSR_IISMode_TBIF_Msk          (0x01UL << USIC_CH_PSR_IISMode_TBIF_Pos)                /*!< USIC_CH PSR_IISMode: TBIF Mask          */
#define USIC_CH_PSR_IISMode_RIF_Pos           14                                                      /*!< USIC_CH PSR_IISMode: RIF Position       */
#define USIC_CH_PSR_IISMode_RIF_Msk           (0x01UL << USIC_CH_PSR_IISMode_RIF_Pos)                 /*!< USIC_CH PSR_IISMode: RIF Mask           */
#define USIC_CH_PSR_IISMode_AIF_Pos           15                                                      /*!< USIC_CH PSR_IISMode: AIF Position       */
#define USIC_CH_PSR_IISMode_AIF_Msk           (0x01UL << USIC_CH_PSR_IISMode_AIF_Pos)                 /*!< USIC_CH PSR_IISMode: AIF Mask           */
#define USIC_CH_PSR_IISMode_BRGIF_Pos         16                                                      /*!< USIC_CH PSR_IISMode: BRGIF Position     */
#define USIC_CH_PSR_IISMode_BRGIF_Msk         (0x01UL << USIC_CH_PSR_IISMode_BRGIF_Pos)               /*!< USIC_CH PSR_IISMode: BRGIF Mask         */

/* --------------------------------  USIC_CH_PSCR  -------------------------------- */
#define USIC_CH_PSCR_CST0_Pos                 0                                                       /*!< USIC_CH PSCR: CST0 Position             */
#define USIC_CH_PSCR_CST0_Msk                 (0x01UL << USIC_CH_PSCR_CST0_Pos)                       /*!< USIC_CH PSCR: CST0 Mask                 */
#define USIC_CH_PSCR_CST1_Pos                 1                                                       /*!< USIC_CH PSCR: CST1 Position             */
#define USIC_CH_PSCR_CST1_Msk                 (0x01UL << USIC_CH_PSCR_CST1_Pos)                       /*!< USIC_CH PSCR: CST1 Mask                 */
#define USIC_CH_PSCR_CST2_Pos                 2                                                       /*!< USIC_CH PSCR: CST2 Position             */
#define USIC_CH_PSCR_CST2_Msk                 (0x01UL << USIC_CH_PSCR_CST2_Pos)                       /*!< USIC_CH PSCR: CST2 Mask                 */
#define USIC_CH_PSCR_CST3_Pos                 3                                                       /*!< USIC_CH PSCR: CST3 Position             */
#define USIC_CH_PSCR_CST3_Msk                 (0x01UL << USIC_CH_PSCR_CST3_Pos)                       /*!< USIC_CH PSCR: CST3 Mask                 */
#define USIC_CH_PSCR_CST4_Pos                 4                                                       /*!< USIC_CH PSCR: CST4 Position             */
#define USIC_CH_PSCR_CST4_Msk                 (0x01UL << USIC_CH_PSCR_CST4_Pos)                       /*!< USIC_CH PSCR: CST4 Mask                 */
#define USIC_CH_PSCR_CST5_Pos                 5                                                       /*!< USIC_CH PSCR: CST5 Position             */
#define USIC_CH_PSCR_CST5_Msk                 (0x01UL << USIC_CH_PSCR_CST5_Pos)                       /*!< USIC_CH PSCR: CST5 Mask                 */
#define USIC_CH_PSCR_CST6_Pos                 6                                                       /*!< USIC_CH PSCR: CST6 Position             */
#define USIC_CH_PSCR_CST6_Msk                 (0x01UL << USIC_CH_PSCR_CST6_Pos)                       /*!< USIC_CH PSCR: CST6 Mask                 */
#define USIC_CH_PSCR_CST7_Pos                 7                                                       /*!< USIC_CH PSCR: CST7 Position             */
#define USIC_CH_PSCR_CST7_Msk                 (0x01UL << USIC_CH_PSCR_CST7_Pos)                       /*!< USIC_CH PSCR: CST7 Mask                 */
#define USIC_CH_PSCR_CST8_Pos                 8                                                       /*!< USIC_CH PSCR: CST8 Position             */
#define USIC_CH_PSCR_CST8_Msk                 (0x01UL << USIC_CH_PSCR_CST8_Pos)                       /*!< USIC_CH PSCR: CST8 Mask                 */
#define USIC_CH_PSCR_CST9_Pos                 9                                                       /*!< USIC_CH PSCR: CST9 Position             */
#define USIC_CH_PSCR_CST9_Msk                 (0x01UL << USIC_CH_PSCR_CST9_Pos)                       /*!< USIC_CH PSCR: CST9 Mask                 */
#define USIC_CH_PSCR_CRSIF_Pos                10                                                      /*!< USIC_CH PSCR: CRSIF Position            */
#define USIC_CH_PSCR_CRSIF_Msk                (0x01UL << USIC_CH_PSCR_CRSIF_Pos)                      /*!< USIC_CH PSCR: CRSIF Mask                */
#define USIC_CH_PSCR_CDLIF_Pos                11                                                      /*!< USIC_CH PSCR: CDLIF Position            */
#define USIC_CH_PSCR_CDLIF_Msk                (0x01UL << USIC_CH_PSCR_CDLIF_Pos)                      /*!< USIC_CH PSCR: CDLIF Mask                */
#define USIC_CH_PSCR_CTSIF_Pos                12                                                      /*!< USIC_CH PSCR: CTSIF Position            */
#define USIC_CH_PSCR_CTSIF_Msk                (0x01UL << USIC_CH_PSCR_CTSIF_Pos)                      /*!< USIC_CH PSCR: CTSIF Mask                */
#define USIC_CH_PSCR_CTBIF_Pos                13                                                      /*!< USIC_CH PSCR: CTBIF Position            */
#define USIC_CH_PSCR_CTBIF_Msk                (0x01UL << USIC_CH_PSCR_CTBIF_Pos)                      /*!< USIC_CH PSCR: CTBIF Mask                */
#define USIC_CH_PSCR_CRIF_Pos                 14                                                      /*!< USIC_CH PSCR: CRIF Position             */
#define USIC_CH_PSCR_CRIF_Msk                 (0x01UL << USIC_CH_PSCR_CRIF_Pos)                       /*!< USIC_CH PSCR: CRIF Mask                 */
#define USIC_CH_PSCR_CAIF_Pos                 15                                                      /*!< USIC_CH PSCR: CAIF Position             */
#define USIC_CH_PSCR_CAIF_Msk                 (0x01UL << USIC_CH_PSCR_CAIF_Pos)                       /*!< USIC_CH PSCR: CAIF Mask                 */
#define USIC_CH_PSCR_CBRGIF_Pos               16                                                      /*!< USIC_CH PSCR: CBRGIF Position           */
#define USIC_CH_PSCR_CBRGIF_Msk               (0x01UL << USIC_CH_PSCR_CBRGIF_Pos)                     /*!< USIC_CH PSCR: CBRGIF Mask               */

/* -------------------------------  USIC_CH_RBUFSR  ------------------------------- */
#define USIC_CH_RBUFSR_WLEN_Pos               0                                                       /*!< USIC_CH RBUFSR: WLEN Position           */
#define USIC_CH_RBUFSR_WLEN_Msk               (0x0fUL << USIC_CH_RBUFSR_WLEN_Pos)                     /*!< USIC_CH RBUFSR: WLEN Mask               */
#define USIC_CH_RBUFSR_SOF_Pos                6                                                       /*!< USIC_CH RBUFSR: SOF Position            */
#define USIC_CH_RBUFSR_SOF_Msk                (0x01UL << USIC_CH_RBUFSR_SOF_Pos)                      /*!< USIC_CH RBUFSR: SOF Mask                */
#define USIC_CH_RBUFSR_PAR_Pos                8                                                       /*!< USIC_CH RBUFSR: PAR Position            */
#define USIC_CH_RBUFSR_PAR_Msk                (0x01UL << USIC_CH_RBUFSR_PAR_Pos)                      /*!< USIC_CH RBUFSR: PAR Mask                */
#define USIC_CH_RBUFSR_PERR_Pos               9                                                       /*!< USIC_CH RBUFSR: PERR Position           */
#define USIC_CH_RBUFSR_PERR_Msk               (0x01UL << USIC_CH_RBUFSR_PERR_Pos)                     /*!< USIC_CH RBUFSR: PERR Mask               */
#define USIC_CH_RBUFSR_RDV0_Pos               13                                                      /*!< USIC_CH RBUFSR: RDV0 Position           */
#define USIC_CH_RBUFSR_RDV0_Msk               (0x01UL << USIC_CH_RBUFSR_RDV0_Pos)                     /*!< USIC_CH RBUFSR: RDV0 Mask               */
#define USIC_CH_RBUFSR_RDV1_Pos               14                                                      /*!< USIC_CH RBUFSR: RDV1 Position           */
#define USIC_CH_RBUFSR_RDV1_Msk               (0x01UL << USIC_CH_RBUFSR_RDV1_Pos)                     /*!< USIC_CH RBUFSR: RDV1 Mask               */
#define USIC_CH_RBUFSR_DS_Pos                 15                                                      /*!< USIC_CH RBUFSR: DS Position             */
#define USIC_CH_RBUFSR_DS_Msk                 (0x01UL << USIC_CH_RBUFSR_DS_Pos)                       /*!< USIC_CH RBUFSR: DS Mask                 */

/* --------------------------------  USIC_CH_RBUF  -------------------------------- */
#define USIC_CH_RBUF_DSR_Pos                  0                                                       /*!< USIC_CH RBUF: DSR Position              */
#define USIC_CH_RBUF_DSR_Msk                  (0x0000ffffUL << USIC_CH_RBUF_DSR_Pos)                  /*!< USIC_CH RBUF: DSR Mask                  */

/* --------------------------------  USIC_CH_RBUFD  ------------------------------- */
#define USIC_CH_RBUFD_DSR_Pos                 0                                                       /*!< USIC_CH RBUFD: DSR Position             */
#define USIC_CH_RBUFD_DSR_Msk                 (0x0000ffffUL << USIC_CH_RBUFD_DSR_Pos)                 /*!< USIC_CH RBUFD: DSR Mask                 */

/* --------------------------------  USIC_CH_RBUF0  ------------------------------- */
#define USIC_CH_RBUF0_DSR0_Pos                0                                                       /*!< USIC_CH RBUF0: DSR0 Position            */
#define USIC_CH_RBUF0_DSR0_Msk                (0x0000ffffUL << USIC_CH_RBUF0_DSR0_Pos)                /*!< USIC_CH RBUF0: DSR0 Mask                */

/* --------------------------------  USIC_CH_RBUF1  ------------------------------- */
#define USIC_CH_RBUF1_DSR1_Pos                0                                                       /*!< USIC_CH RBUF1: DSR1 Position            */
#define USIC_CH_RBUF1_DSR1_Msk                (0x0000ffffUL << USIC_CH_RBUF1_DSR1_Pos)                /*!< USIC_CH RBUF1: DSR1 Mask                */

/* ------------------------------  USIC_CH_RBUF01SR  ------------------------------ */
#define USIC_CH_RBUF01SR_WLEN0_Pos            0                                                       /*!< USIC_CH RBUF01SR: WLEN0 Position        */
#define USIC_CH_RBUF01SR_WLEN0_Msk            (0x0fUL << USIC_CH_RBUF01SR_WLEN0_Pos)                  /*!< USIC_CH RBUF01SR: WLEN0 Mask            */
#define USIC_CH_RBUF01SR_SOF0_Pos             6                                                       /*!< USIC_CH RBUF01SR: SOF0 Position         */
#define USIC_CH_RBUF01SR_SOF0_Msk             (0x01UL << USIC_CH_RBUF01SR_SOF0_Pos)                   /*!< USIC_CH RBUF01SR: SOF0 Mask             */
#define USIC_CH_RBUF01SR_PAR0_Pos             8                                                       /*!< USIC_CH RBUF01SR: PAR0 Position         */
#define USIC_CH_RBUF01SR_PAR0_Msk             (0x01UL << USIC_CH_RBUF01SR_PAR0_Pos)                   /*!< USIC_CH RBUF01SR: PAR0 Mask             */
#define USIC_CH_RBUF01SR_PERR0_Pos            9                                                       /*!< USIC_CH RBUF01SR: PERR0 Position        */
#define USIC_CH_RBUF01SR_PERR0_Msk            (0x01UL << USIC_CH_RBUF01SR_PERR0_Pos)                  /*!< USIC_CH RBUF01SR: PERR0 Mask            */
#define USIC_CH_RBUF01SR_RDV00_Pos            13                                                      /*!< USIC_CH RBUF01SR: RDV00 Position        */
#define USIC_CH_RBUF01SR_RDV00_Msk            (0x01UL << USIC_CH_RBUF01SR_RDV00_Pos)                  /*!< USIC_CH RBUF01SR: RDV00 Mask            */
#define USIC_CH_RBUF01SR_RDV01_Pos            14                                                      /*!< USIC_CH RBUF01SR: RDV01 Position        */
#define USIC_CH_RBUF01SR_RDV01_Msk            (0x01UL << USIC_CH_RBUF01SR_RDV01_Pos)                  /*!< USIC_CH RBUF01SR: RDV01 Mask            */
#define USIC_CH_RBUF01SR_DS0_Pos              15                                                      /*!< USIC_CH RBUF01SR: DS0 Position          */
#define USIC_CH_RBUF01SR_DS0_Msk              (0x01UL << USIC_CH_RBUF01SR_DS0_Pos)                    /*!< USIC_CH RBUF01SR: DS0 Mask              */
#define USIC_CH_RBUF01SR_WLEN1_Pos            16                                                      /*!< USIC_CH RBUF01SR: WLEN1 Position        */
#define USIC_CH_RBUF01SR_WLEN1_Msk            (0x0fUL << USIC_CH_RBUF01SR_WLEN1_Pos)                  /*!< USIC_CH RBUF01SR: WLEN1 Mask            */
#define USIC_CH_RBUF01SR_SOF1_Pos             22                                                      /*!< USIC_CH RBUF01SR: SOF1 Position         */
#define USIC_CH_RBUF01SR_SOF1_Msk             (0x01UL << USIC_CH_RBUF01SR_SOF1_Pos)                   /*!< USIC_CH RBUF01SR: SOF1 Mask             */
#define USIC_CH_RBUF01SR_PAR1_Pos             24                                                      /*!< USIC_CH RBUF01SR: PAR1 Position         */
#define USIC_CH_RBUF01SR_PAR1_Msk             (0x01UL << USIC_CH_RBUF01SR_PAR1_Pos)                   /*!< USIC_CH RBUF01SR: PAR1 Mask             */
#define USIC_CH_RBUF01SR_PERR1_Pos            25                                                      /*!< USIC_CH RBUF01SR: PERR1 Position        */
#define USIC_CH_RBUF01SR_PERR1_Msk            (0x01UL << USIC_CH_RBUF01SR_PERR1_Pos)                  /*!< USIC_CH RBUF01SR: PERR1 Mask            */
#define USIC_CH_RBUF01SR_RDV10_Pos            29                                                      /*!< USIC_CH RBUF01SR: RDV10 Position        */
#define USIC_CH_RBUF01SR_RDV10_Msk            (0x01UL << USIC_CH_RBUF01SR_RDV10_Pos)                  /*!< USIC_CH RBUF01SR: RDV10 Mask            */
#define USIC_CH_RBUF01SR_RDV11_Pos            30                                                      /*!< USIC_CH RBUF01SR: RDV11 Position        */
#define USIC_CH_RBUF01SR_RDV11_Msk            (0x01UL << USIC_CH_RBUF01SR_RDV11_Pos)                  /*!< USIC_CH RBUF01SR: RDV11 Mask            */
#define USIC_CH_RBUF01SR_DS1_Pos              31                                                      /*!< USIC_CH RBUF01SR: DS1 Position          */
#define USIC_CH_RBUF01SR_DS1_Msk              (0x01UL << USIC_CH_RBUF01SR_DS1_Pos)                    /*!< USIC_CH RBUF01SR: DS1 Mask              */

/* ---------------------------------  USIC_CH_FMR  -------------------------------- */
#define USIC_CH_FMR_MTDV_Pos                  0                                                       /*!< USIC_CH FMR: MTDV Position              */
#define USIC_CH_FMR_MTDV_Msk                  (0x03UL << USIC_CH_FMR_MTDV_Pos)                        /*!< USIC_CH FMR: MTDV Mask                  */
#define USIC_CH_FMR_ATVC_Pos                  4                                                       /*!< USIC_CH FMR: ATVC Position              */
#define USIC_CH_FMR_ATVC_Msk                  (0x01UL << USIC_CH_FMR_ATVC_Pos)                        /*!< USIC_CH FMR: ATVC Mask                  */
#define USIC_CH_FMR_CRDV0_Pos                 14                                                      /*!< USIC_CH FMR: CRDV0 Position             */
#define USIC_CH_FMR_CRDV0_Msk                 (0x01UL << USIC_CH_FMR_CRDV0_Pos)                       /*!< USIC_CH FMR: CRDV0 Mask                 */
#define USIC_CH_FMR_CRDV1_Pos                 15                                                      /*!< USIC_CH FMR: CRDV1 Position             */
#define USIC_CH_FMR_CRDV1_Msk                 (0x01UL << USIC_CH_FMR_CRDV1_Pos)                       /*!< USIC_CH FMR: CRDV1 Mask                 */
#define USIC_CH_FMR_SIO0_Pos                  16                                                      /*!< USIC_CH FMR: SIO0 Position              */
#define USIC_CH_FMR_SIO0_Msk                  (0x01UL << USIC_CH_FMR_SIO0_Pos)                        /*!< USIC_CH FMR: SIO0 Mask                  */
#define USIC_CH_FMR_SIO1_Pos                  17                                                      /*!< USIC_CH FMR: SIO1 Position              */
#define USIC_CH_FMR_SIO1_Msk                  (0x01UL << USIC_CH_FMR_SIO1_Pos)                        /*!< USIC_CH FMR: SIO1 Mask                  */
#define USIC_CH_FMR_SIO2_Pos                  18                                                      /*!< USIC_CH FMR: SIO2 Position              */
#define USIC_CH_FMR_SIO2_Msk                  (0x01UL << USIC_CH_FMR_SIO2_Pos)                        /*!< USIC_CH FMR: SIO2 Mask                  */
#define USIC_CH_FMR_SIO3_Pos                  19                                                      /*!< USIC_CH FMR: SIO3 Position              */
#define USIC_CH_FMR_SIO3_Msk                  (0x01UL << USIC_CH_FMR_SIO3_Pos)                        /*!< USIC_CH FMR: SIO3 Mask                  */
#define USIC_CH_FMR_SIO4_Pos                  20                                                      /*!< USIC_CH FMR: SIO4 Position              */
#define USIC_CH_FMR_SIO4_Msk                  (0x01UL << USIC_CH_FMR_SIO4_Pos)                        /*!< USIC_CH FMR: SIO4 Mask                  */
#define USIC_CH_FMR_SIO5_Pos                  21                                                      /*!< USIC_CH FMR: SIO5 Position              */
#define USIC_CH_FMR_SIO5_Msk                  (0x01UL << USIC_CH_FMR_SIO5_Pos)                        /*!< USIC_CH FMR: SIO5 Mask                  */

/* --------------------------------  USIC_CH_TBUF  -------------------------------- */
#define USIC_CH_TBUF_TDATA_Pos                0                                                       /*!< USIC_CH TBUF: TDATA Position            */
#define USIC_CH_TBUF_TDATA_Msk                (0x0000ffffUL << USIC_CH_TBUF_TDATA_Pos)                /*!< USIC_CH TBUF: TDATA Mask                */

/* ---------------------------------  USIC_CH_BYP  -------------------------------- */
#define USIC_CH_BYP_BDATA_Pos                 0                                                       /*!< USIC_CH BYP: BDATA Position             */
#define USIC_CH_BYP_BDATA_Msk                 (0x0000ffffUL << USIC_CH_BYP_BDATA_Pos)                 /*!< USIC_CH BYP: BDATA Mask                 */

/* --------------------------------  USIC_CH_BYPCR  ------------------------------- */
#define USIC_CH_BYPCR_BWLE_Pos                0                                                       /*!< USIC_CH BYPCR: BWLE Position            */
#define USIC_CH_BYPCR_BWLE_Msk                (0x0fUL << USIC_CH_BYPCR_BWLE_Pos)                      /*!< USIC_CH BYPCR: BWLE Mask                */
#define USIC_CH_BYPCR_BDSSM_Pos               8                                                       /*!< USIC_CH BYPCR: BDSSM Position           */
#define USIC_CH_BYPCR_BDSSM_Msk               (0x01UL << USIC_CH_BYPCR_BDSSM_Pos)                     /*!< USIC_CH BYPCR: BDSSM Mask               */
#define USIC_CH_BYPCR_BDEN_Pos                10                                                      /*!< USIC_CH BYPCR: BDEN Position            */
#define USIC_CH_BYPCR_BDEN_Msk                (0x03UL << USIC_CH_BYPCR_BDEN_Pos)                      /*!< USIC_CH BYPCR: BDEN Mask                */
#define USIC_CH_BYPCR_BDVTR_Pos               12                                                      /*!< USIC_CH BYPCR: BDVTR Position           */
#define USIC_CH_BYPCR_BDVTR_Msk               (0x01UL << USIC_CH_BYPCR_BDVTR_Pos)                     /*!< USIC_CH BYPCR: BDVTR Mask               */
#define USIC_CH_BYPCR_BPRIO_Pos               13                                                      /*!< USIC_CH BYPCR: BPRIO Position           */
#define USIC_CH_BYPCR_BPRIO_Msk               (0x01UL << USIC_CH_BYPCR_BPRIO_Pos)                     /*!< USIC_CH BYPCR: BPRIO Mask               */
#define USIC_CH_BYPCR_BDV_Pos                 15                                                      /*!< USIC_CH BYPCR: BDV Position             */
#define USIC_CH_BYPCR_BDV_Msk                 (0x01UL << USIC_CH_BYPCR_BDV_Pos)                       /*!< USIC_CH BYPCR: BDV Mask                 */
#define USIC_CH_BYPCR_BSELO_Pos               16                                                      /*!< USIC_CH BYPCR: BSELO Position           */
#define USIC_CH_BYPCR_BSELO_Msk               (0x1fUL << USIC_CH_BYPCR_BSELO_Pos)                     /*!< USIC_CH BYPCR: BSELO Mask               */
#define USIC_CH_BYPCR_BHPC_Pos                21                                                      /*!< USIC_CH BYPCR: BHPC Position            */
#define USIC_CH_BYPCR_BHPC_Msk                (0x07UL << USIC_CH_BYPCR_BHPC_Pos)                      /*!< USIC_CH BYPCR: BHPC Mask                */

/* --------------------------------  USIC_CH_TBCTR  ------------------------------- */
#define USIC_CH_TBCTR_DPTR_Pos                0                                                       /*!< USIC_CH TBCTR: DPTR Position            */
#define USIC_CH_TBCTR_DPTR_Msk                (0x3fUL << USIC_CH_TBCTR_DPTR_Pos)                      /*!< USIC_CH TBCTR: DPTR Mask                */
#define USIC_CH_TBCTR_LIMIT_Pos               8                                                       /*!< USIC_CH TBCTR: LIMIT Position           */
#define USIC_CH_TBCTR_LIMIT_Msk               (0x3fUL << USIC_CH_TBCTR_LIMIT_Pos)                     /*!< USIC_CH TBCTR: LIMIT Mask               */
#define USIC_CH_TBCTR_STBTM_Pos               14                                                      /*!< USIC_CH TBCTR: STBTM Position           */
#define USIC_CH_TBCTR_STBTM_Msk               (0x01UL << USIC_CH_TBCTR_STBTM_Pos)                     /*!< USIC_CH TBCTR: STBTM Mask               */
#define USIC_CH_TBCTR_STBTEN_Pos              15                                                      /*!< USIC_CH TBCTR: STBTEN Position          */
#define USIC_CH_TBCTR_STBTEN_Msk              (0x01UL << USIC_CH_TBCTR_STBTEN_Pos)                    /*!< USIC_CH TBCTR: STBTEN Mask              */
#define USIC_CH_TBCTR_STBINP_Pos              16                                                      /*!< USIC_CH TBCTR: STBINP Position          */
#define USIC_CH_TBCTR_STBINP_Msk              (0x07UL << USIC_CH_TBCTR_STBINP_Pos)                    /*!< USIC_CH TBCTR: STBINP Mask              */
#define USIC_CH_TBCTR_ATBINP_Pos              19                                                      /*!< USIC_CH TBCTR: ATBINP Position          */
#define USIC_CH_TBCTR_ATBINP_Msk              (0x07UL << USIC_CH_TBCTR_ATBINP_Pos)                    /*!< USIC_CH TBCTR: ATBINP Mask              */
#define USIC_CH_TBCTR_SIZE_Pos                24                                                      /*!< USIC_CH TBCTR: SIZE Position            */
#define USIC_CH_TBCTR_SIZE_Msk                (0x07UL << USIC_CH_TBCTR_SIZE_Pos)                      /*!< USIC_CH TBCTR: SIZE Mask                */
#define USIC_CH_TBCTR_LOF_Pos                 28                                                      /*!< USIC_CH TBCTR: LOF Position             */
#define USIC_CH_TBCTR_LOF_Msk                 (0x01UL << USIC_CH_TBCTR_LOF_Pos)                       /*!< USIC_CH TBCTR: LOF Mask                 */
#define USIC_CH_TBCTR_STBIEN_Pos              30                                                      /*!< USIC_CH TBCTR: STBIEN Position          */
#define USIC_CH_TBCTR_STBIEN_Msk              (0x01UL << USIC_CH_TBCTR_STBIEN_Pos)                    /*!< USIC_CH TBCTR: STBIEN Mask              */
#define USIC_CH_TBCTR_TBERIEN_Pos             31                                                      /*!< USIC_CH TBCTR: TBERIEN Position         */
#define USIC_CH_TBCTR_TBERIEN_Msk             (0x01UL << USIC_CH_TBCTR_TBERIEN_Pos)                   /*!< USIC_CH TBCTR: TBERIEN Mask             */

/* --------------------------------  USIC_CH_RBCTR  ------------------------------- */
#define USIC_CH_RBCTR_DPTR_Pos                0                                                       /*!< USIC_CH RBCTR: DPTR Position            */
#define USIC_CH_RBCTR_DPTR_Msk                (0x3fUL << USIC_CH_RBCTR_DPTR_Pos)                      /*!< USIC_CH RBCTR: DPTR Mask                */
#define USIC_CH_RBCTR_LIMIT_Pos               8                                                       /*!< USIC_CH RBCTR: LIMIT Position           */
#define USIC_CH_RBCTR_LIMIT_Msk               (0x3fUL << USIC_CH_RBCTR_LIMIT_Pos)                     /*!< USIC_CH RBCTR: LIMIT Mask               */
#define USIC_CH_RBCTR_SRBTM_Pos               14                                                      /*!< USIC_CH RBCTR: SRBTM Position           */
#define USIC_CH_RBCTR_SRBTM_Msk               (0x01UL << USIC_CH_RBCTR_SRBTM_Pos)                     /*!< USIC_CH RBCTR: SRBTM Mask               */
#define USIC_CH_RBCTR_SRBTEN_Pos              15                                                      /*!< USIC_CH RBCTR: SRBTEN Position          */
#define USIC_CH_RBCTR_SRBTEN_Msk              (0x01UL << USIC_CH_RBCTR_SRBTEN_Pos)                    /*!< USIC_CH RBCTR: SRBTEN Mask              */
#define USIC_CH_RBCTR_SRBINP_Pos              16                                                      /*!< USIC_CH RBCTR: SRBINP Position          */
#define USIC_CH_RBCTR_SRBINP_Msk              (0x07UL << USIC_CH_RBCTR_SRBINP_Pos)                    /*!< USIC_CH RBCTR: SRBINP Mask              */
#define USIC_CH_RBCTR_ARBINP_Pos              19                                                      /*!< USIC_CH RBCTR: ARBINP Position          */
#define USIC_CH_RBCTR_ARBINP_Msk              (0x07UL << USIC_CH_RBCTR_ARBINP_Pos)                    /*!< USIC_CH RBCTR: ARBINP Mask              */
#define USIC_CH_RBCTR_RCIM_Pos                22                                                      /*!< USIC_CH RBCTR: RCIM Position            */
#define USIC_CH_RBCTR_RCIM_Msk                (0x03UL << USIC_CH_RBCTR_RCIM_Pos)                      /*!< USIC_CH RBCTR: RCIM Mask                */
#define USIC_CH_RBCTR_SIZE_Pos                24                                                      /*!< USIC_CH RBCTR: SIZE Position            */
#define USIC_CH_RBCTR_SIZE_Msk                (0x07UL << USIC_CH_RBCTR_SIZE_Pos)                      /*!< USIC_CH RBCTR: SIZE Mask                */
#define USIC_CH_RBCTR_RNM_Pos                 27                                                      /*!< USIC_CH RBCTR: RNM Position             */
#define USIC_CH_RBCTR_RNM_Msk                 (0x01UL << USIC_CH_RBCTR_RNM_Pos)                       /*!< USIC_CH RBCTR: RNM Mask                 */
#define USIC_CH_RBCTR_LOF_Pos                 28                                                      /*!< USIC_CH RBCTR: LOF Position             */
#define USIC_CH_RBCTR_LOF_Msk                 (0x01UL << USIC_CH_RBCTR_LOF_Pos)                       /*!< USIC_CH RBCTR: LOF Mask                 */
#define USIC_CH_RBCTR_ARBIEN_Pos              29                                                      /*!< USIC_CH RBCTR: ARBIEN Position          */
#define USIC_CH_RBCTR_ARBIEN_Msk              (0x01UL << USIC_CH_RBCTR_ARBIEN_Pos)                    /*!< USIC_CH RBCTR: ARBIEN Mask              */
#define USIC_CH_RBCTR_SRBIEN_Pos              30                                                      /*!< USIC_CH RBCTR: SRBIEN Position          */
#define USIC_CH_RBCTR_SRBIEN_Msk              (0x01UL << USIC_CH_RBCTR_SRBIEN_Pos)                    /*!< USIC_CH RBCTR: SRBIEN Mask              */
#define USIC_CH_RBCTR_RBERIEN_Pos             31                                                      /*!< USIC_CH RBCTR: RBERIEN Position         */
#define USIC_CH_RBCTR_RBERIEN_Msk             (0x01UL << USIC_CH_RBCTR_RBERIEN_Pos)                   /*!< USIC_CH RBCTR: RBERIEN Mask             */

/* -------------------------------  USIC_CH_TRBPTR  ------------------------------- */
#define USIC_CH_TRBPTR_TDIPTR_Pos             0                                                       /*!< USIC_CH TRBPTR: TDIPTR Position         */
#define USIC_CH_TRBPTR_TDIPTR_Msk             (0x3fUL << USIC_CH_TRBPTR_TDIPTR_Pos)                   /*!< USIC_CH TRBPTR: TDIPTR Mask             */
#define USIC_CH_TRBPTR_TDOPTR_Pos             8                                                       /*!< USIC_CH TRBPTR: TDOPTR Position         */
#define USIC_CH_TRBPTR_TDOPTR_Msk             (0x3fUL << USIC_CH_TRBPTR_TDOPTR_Pos)                   /*!< USIC_CH TRBPTR: TDOPTR Mask             */
#define USIC_CH_TRBPTR_RDIPTR_Pos             16                                                      /*!< USIC_CH TRBPTR: RDIPTR Position         */
#define USIC_CH_TRBPTR_RDIPTR_Msk             (0x3fUL << USIC_CH_TRBPTR_RDIPTR_Pos)                   /*!< USIC_CH TRBPTR: RDIPTR Mask             */
#define USIC_CH_TRBPTR_RDOPTR_Pos             24                                                      /*!< USIC_CH TRBPTR: RDOPTR Position         */
#define USIC_CH_TRBPTR_RDOPTR_Msk             (0x3fUL << USIC_CH_TRBPTR_RDOPTR_Pos)                   /*!< USIC_CH TRBPTR: RDOPTR Mask             */

/* --------------------------------  USIC_CH_TRBSR  ------------------------------- */
#define USIC_CH_TRBSR_SRBI_Pos                0                                                       /*!< USIC_CH TRBSR: SRBI Position            */
#define USIC_CH_TRBSR_SRBI_Msk                (0x01UL << USIC_CH_TRBSR_SRBI_Pos)                      /*!< USIC_CH TRBSR: SRBI Mask                */
#define USIC_CH_TRBSR_RBERI_Pos               1                                                       /*!< USIC_CH TRBSR: RBERI Position           */
#define USIC_CH_TRBSR_RBERI_Msk               (0x01UL << USIC_CH_TRBSR_RBERI_Pos)                     /*!< USIC_CH TRBSR: RBERI Mask               */
#define USIC_CH_TRBSR_ARBI_Pos                2                                                       /*!< USIC_CH TRBSR: ARBI Position            */
#define USIC_CH_TRBSR_ARBI_Msk                (0x01UL << USIC_CH_TRBSR_ARBI_Pos)                      /*!< USIC_CH TRBSR: ARBI Mask                */
#define USIC_CH_TRBSR_REMPTY_Pos              3                                                       /*!< USIC_CH TRBSR: REMPTY Position          */
#define USIC_CH_TRBSR_REMPTY_Msk              (0x01UL << USIC_CH_TRBSR_REMPTY_Pos)                    /*!< USIC_CH TRBSR: REMPTY Mask              */
#define USIC_CH_TRBSR_RFULL_Pos               4                                                       /*!< USIC_CH TRBSR: RFULL Position           */
#define USIC_CH_TRBSR_RFULL_Msk               (0x01UL << USIC_CH_TRBSR_RFULL_Pos)                     /*!< USIC_CH TRBSR: RFULL Mask               */
#define USIC_CH_TRBSR_RBUS_Pos                5                                                       /*!< USIC_CH TRBSR: RBUS Position            */
#define USIC_CH_TRBSR_RBUS_Msk                (0x01UL << USIC_CH_TRBSR_RBUS_Pos)                      /*!< USIC_CH TRBSR: RBUS Mask                */
#define USIC_CH_TRBSR_SRBT_Pos                6                                                       /*!< USIC_CH TRBSR: SRBT Position            */
#define USIC_CH_TRBSR_SRBT_Msk                (0x01UL << USIC_CH_TRBSR_SRBT_Pos)                      /*!< USIC_CH TRBSR: SRBT Mask                */
#define USIC_CH_TRBSR_STBI_Pos                8                                                       /*!< USIC_CH TRBSR: STBI Position            */
#define USIC_CH_TRBSR_STBI_Msk                (0x01UL << USIC_CH_TRBSR_STBI_Pos)                      /*!< USIC_CH TRBSR: STBI Mask                */
#define USIC_CH_TRBSR_TBERI_Pos               9                                                       /*!< USIC_CH TRBSR: TBERI Position           */
#define USIC_CH_TRBSR_TBERI_Msk               (0x01UL << USIC_CH_TRBSR_TBERI_Pos)                     /*!< USIC_CH TRBSR: TBERI Mask               */
#define USIC_CH_TRBSR_TEMPTY_Pos              11                                                      /*!< USIC_CH TRBSR: TEMPTY Position          */
#define USIC_CH_TRBSR_TEMPTY_Msk              (0x01UL << USIC_CH_TRBSR_TEMPTY_Pos)                    /*!< USIC_CH TRBSR: TEMPTY Mask              */
#define USIC_CH_TRBSR_TFULL_Pos               12                                                      /*!< USIC_CH TRBSR: TFULL Position           */
#define USIC_CH_TRBSR_TFULL_Msk               (0x01UL << USIC_CH_TRBSR_TFULL_Pos)                     /*!< USIC_CH TRBSR: TFULL Mask               */
#define USIC_CH_TRBSR_TBUS_Pos                13                                                      /*!< USIC_CH TRBSR: TBUS Position            */
#define USIC_CH_TRBSR_TBUS_Msk                (0x01UL << USIC_CH_TRBSR_TBUS_Pos)                      /*!< USIC_CH TRBSR: TBUS Mask                */
#define USIC_CH_TRBSR_STBT_Pos                14                                                      /*!< USIC_CH TRBSR: STBT Position            */
#define USIC_CH_TRBSR_STBT_Msk                (0x01UL << USIC_CH_TRBSR_STBT_Pos)                      /*!< USIC_CH TRBSR: STBT Mask                */
#define USIC_CH_TRBSR_RBFLVL_Pos              16                                                      /*!< USIC_CH TRBSR: RBFLVL Position          */
#define USIC_CH_TRBSR_RBFLVL_Msk              (0x7fUL << USIC_CH_TRBSR_RBFLVL_Pos)                    /*!< USIC_CH TRBSR: RBFLVL Mask              */
#define USIC_CH_TRBSR_TBFLVL_Pos              24                                                      /*!< USIC_CH TRBSR: TBFLVL Position          */
#define USIC_CH_TRBSR_TBFLVL_Msk              (0x7fUL << USIC_CH_TRBSR_TBFLVL_Pos)                    /*!< USIC_CH TRBSR: TBFLVL Mask              */

/* -------------------------------  USIC_CH_TRBSCR  ------------------------------- */
#define USIC_CH_TRBSCR_CSRBI_Pos              0                                                       /*!< USIC_CH TRBSCR: CSRBI Position          */
#define USIC_CH_TRBSCR_CSRBI_Msk              (0x01UL << USIC_CH_TRBSCR_CSRBI_Pos)                    /*!< USIC_CH TRBSCR: CSRBI Mask              */
#define USIC_CH_TRBSCR_CRBERI_Pos             1                                                       /*!< USIC_CH TRBSCR: CRBERI Position         */
#define USIC_CH_TRBSCR_CRBERI_Msk             (0x01UL << USIC_CH_TRBSCR_CRBERI_Pos)                   /*!< USIC_CH TRBSCR: CRBERI Mask             */
#define USIC_CH_TRBSCR_CARBI_Pos              2                                                       /*!< USIC_CH TRBSCR: CARBI Position          */
#define USIC_CH_TRBSCR_CARBI_Msk              (0x01UL << USIC_CH_TRBSCR_CARBI_Pos)                    /*!< USIC_CH TRBSCR: CARBI Mask              */
#define USIC_CH_TRBSCR_CSTBI_Pos              8                                                       /*!< USIC_CH TRBSCR: CSTBI Position          */
#define USIC_CH_TRBSCR_CSTBI_Msk              (0x01UL << USIC_CH_TRBSCR_CSTBI_Pos)                    /*!< USIC_CH TRBSCR: CSTBI Mask              */
#define USIC_CH_TRBSCR_CTBERI_Pos             9                                                       /*!< USIC_CH TRBSCR: CTBERI Position         */
#define USIC_CH_TRBSCR_CTBERI_Msk             (0x01UL << USIC_CH_TRBSCR_CTBERI_Pos)                   /*!< USIC_CH TRBSCR: CTBERI Mask             */
#define USIC_CH_TRBSCR_CBDV_Pos               10                                                      /*!< USIC_CH TRBSCR: CBDV Position           */
#define USIC_CH_TRBSCR_CBDV_Msk               (0x01UL << USIC_CH_TRBSCR_CBDV_Pos)                     /*!< USIC_CH TRBSCR: CBDV Mask               */
#define USIC_CH_TRBSCR_FLUSHRB_Pos            14                                                      /*!< USIC_CH TRBSCR: FLUSHRB Position        */
#define USIC_CH_TRBSCR_FLUSHRB_Msk            (0x01UL << USIC_CH_TRBSCR_FLUSHRB_Pos)                  /*!< USIC_CH TRBSCR: FLUSHRB Mask            */
#define USIC_CH_TRBSCR_FLUSHTB_Pos            15                                                      /*!< USIC_CH TRBSCR: FLUSHTB Position        */
#define USIC_CH_TRBSCR_FLUSHTB_Msk            (0x01UL << USIC_CH_TRBSCR_FLUSHTB_Pos)                  /*!< USIC_CH TRBSCR: FLUSHTB Mask            */

/* --------------------------------  USIC_CH_OUTR  -------------------------------- */
#define USIC_CH_OUTR_DSR_Pos                  0                                                       /*!< USIC_CH OUTR: DSR Position              */
#define USIC_CH_OUTR_DSR_Msk                  (0x0000ffffUL << USIC_CH_OUTR_DSR_Pos)                  /*!< USIC_CH OUTR: DSR Mask                  */
#define USIC_CH_OUTR_RCI_Pos                  16                                                      /*!< USIC_CH OUTR: RCI Position              */
#define USIC_CH_OUTR_RCI_Msk                  (0x1fUL << USIC_CH_OUTR_RCI_Pos)                        /*!< USIC_CH OUTR: RCI Mask                  */

/* --------------------------------  USIC_CH_OUTDR  ------------------------------- */
#define USIC_CH_OUTDR_DSR_Pos                 0                                                       /*!< USIC_CH OUTDR: DSR Position             */
#define USIC_CH_OUTDR_DSR_Msk                 (0x0000ffffUL << USIC_CH_OUTDR_DSR_Pos)                 /*!< USIC_CH OUTDR: DSR Mask                 */
#define USIC_CH_OUTDR_RCI_Pos                 16                                                      /*!< USIC_CH OUTDR: RCI Position             */
#define USIC_CH_OUTDR_RCI_Msk                 (0x1fUL << USIC_CH_OUTDR_RCI_Pos)                       /*!< USIC_CH OUTDR: RCI Mask                 */

/* ---------------------------------  USIC_CH_IN  --------------------------------- */
#define USIC_CH_IN_TDATA_Pos                  0                                                       /*!< USIC_CH IN: TDATA Position              */
#define USIC_CH_IN_TDATA_Msk                  (0x0000ffffUL << USIC_CH_IN_TDATA_Pos)                  /*!< USIC_CH IN: TDATA Mask                  */


/* ================================================================================ */
/* ================      struct 'SCU_GENERAL' Position & Mask      ================ */
/* ================================================================================ */


/* ----------------------------  SCU_GENERAL_DBGROMID  ---------------------------- */
#define SCU_GENERAL_DBGROMID_MANUFID_Pos      1                                                       /*!< SCU_GENERAL DBGROMID: MANUFID Position  */
#define SCU_GENERAL_DBGROMID_MANUFID_Msk      (0x000007ffUL << SCU_GENERAL_DBGROMID_MANUFID_Pos)      /*!< SCU_GENERAL DBGROMID: MANUFID Mask      */
#define SCU_GENERAL_DBGROMID_PARTNO_Pos       12                                                      /*!< SCU_GENERAL DBGROMID: PARTNO Position   */
#define SCU_GENERAL_DBGROMID_PARTNO_Msk       (0x0000ffffUL << SCU_GENERAL_DBGROMID_PARTNO_Pos)       /*!< SCU_GENERAL DBGROMID: PARTNO Mask       */
#define SCU_GENERAL_DBGROMID_VERSION_Pos      28                                                      /*!< SCU_GENERAL DBGROMID: VERSION Position  */
#define SCU_GENERAL_DBGROMID_VERSION_Msk      (0x0fUL << SCU_GENERAL_DBGROMID_VERSION_Pos)            /*!< SCU_GENERAL DBGROMID: VERSION Mask      */

/* -----------------------------  SCU_GENERAL_IDCHIP  ----------------------------- */
#define SCU_GENERAL_IDCHIP_IDCHIP_Pos         0                                                       /*!< SCU_GENERAL IDCHIP: IDCHIP Position     */
#define SCU_GENERAL_IDCHIP_IDCHIP_Msk         (0xffffffffUL << SCU_GENERAL_IDCHIP_IDCHIP_Pos)         /*!< SCU_GENERAL IDCHIP: IDCHIP Mask         */

/* -------------------------------  SCU_GENERAL_ID  ------------------------------- */
#define SCU_GENERAL_ID_MOD_REV_Pos            0                                                       /*!< SCU_GENERAL ID: MOD_REV Position        */
#define SCU_GENERAL_ID_MOD_REV_Msk            (0x000000ffUL << SCU_GENERAL_ID_MOD_REV_Pos)            /*!< SCU_GENERAL ID: MOD_REV Mask            */
#define SCU_GENERAL_ID_MOD_TYPE_Pos           8                                                       /*!< SCU_GENERAL ID: MOD_TYPE Position       */
#define SCU_GENERAL_ID_MOD_TYPE_Msk           (0x000000ffUL << SCU_GENERAL_ID_MOD_TYPE_Pos)           /*!< SCU_GENERAL ID: MOD_TYPE Mask           */
#define SCU_GENERAL_ID_MOD_NUMBER_Pos         16                                                      /*!< SCU_GENERAL ID: MOD_NUMBER Position     */
#define SCU_GENERAL_ID_MOD_NUMBER_Msk         (0x0000ffffUL << SCU_GENERAL_ID_MOD_NUMBER_Pos)         /*!< SCU_GENERAL ID: MOD_NUMBER Mask         */

/* ------------------------------  SCU_GENERAL_SSW0  ------------------------------ */
#define SCU_GENERAL_SSW0_DAT_Pos              0                                                       /*!< SCU_GENERAL SSW0: DAT Position          */
#define SCU_GENERAL_SSW0_DAT_Msk              (0xffffffffUL << SCU_GENERAL_SSW0_DAT_Pos)              /*!< SCU_GENERAL SSW0: DAT Mask              */

/* -----------------------------  SCU_GENERAL_PASSWD  ----------------------------- */
#define SCU_GENERAL_PASSWD_MODE_Pos           0                                                       /*!< SCU_GENERAL PASSWD: MODE Position       */
#define SCU_GENERAL_PASSWD_MODE_Msk           (0x03UL << SCU_GENERAL_PASSWD_MODE_Pos)                 /*!< SCU_GENERAL PASSWD: MODE Mask           */
#define SCU_GENERAL_PASSWD_PROTS_Pos          2                                                       /*!< SCU_GENERAL PASSWD: PROTS Position      */
#define SCU_GENERAL_PASSWD_PROTS_Msk          (0x01UL << SCU_GENERAL_PASSWD_PROTS_Pos)                /*!< SCU_GENERAL PASSWD: PROTS Mask          */
#define SCU_GENERAL_PASSWD_PASS_Pos           3                                                       /*!< SCU_GENERAL PASSWD: PASS Position       */
#define SCU_GENERAL_PASSWD_PASS_Msk           (0x1fUL << SCU_GENERAL_PASSWD_PASS_Pos)                 /*!< SCU_GENERAL PASSWD: PASS Mask           */

/* -----------------------------  SCU_GENERAL_CCUCON  ----------------------------- */
#define SCU_GENERAL_CCUCON_GSC40_Pos          0                                                       /*!< SCU_GENERAL CCUCON: GSC40 Position      */
#define SCU_GENERAL_CCUCON_GSC40_Msk          (0x01UL << SCU_GENERAL_CCUCON_GSC40_Pos)                /*!< SCU_GENERAL CCUCON: GSC40 Mask          */

/* -----------------------------  SCU_GENERAL_MIRRSTS  ---------------------------- */
#define SCU_GENERAL_MIRRSTS_RTC_CTR_Pos       0                                                       /*!< SCU_GENERAL MIRRSTS: RTC_CTR Position   */
#define SCU_GENERAL_MIRRSTS_RTC_CTR_Msk       (0x01UL << SCU_GENERAL_MIRRSTS_RTC_CTR_Pos)             /*!< SCU_GENERAL MIRRSTS: RTC_CTR Mask       */
#define SCU_GENERAL_MIRRSTS_RTC_ATIM0_Pos     1                                                       /*!< SCU_GENERAL MIRRSTS: RTC_ATIM0 Position */
#define SCU_GENERAL_MIRRSTS_RTC_ATIM0_Msk     (0x01UL << SCU_GENERAL_MIRRSTS_RTC_ATIM0_Pos)           /*!< SCU_GENERAL MIRRSTS: RTC_ATIM0 Mask     */
#define SCU_GENERAL_MIRRSTS_RTC_ATIM1_Pos     2                                                       /*!< SCU_GENERAL MIRRSTS: RTC_ATIM1 Position */
#define SCU_GENERAL_MIRRSTS_RTC_ATIM1_Msk     (0x01UL << SCU_GENERAL_MIRRSTS_RTC_ATIM1_Pos)           /*!< SCU_GENERAL MIRRSTS: RTC_ATIM1 Mask     */
#define SCU_GENERAL_MIRRSTS_RTC_TIM0_Pos      3                                                       /*!< SCU_GENERAL MIRRSTS: RTC_TIM0 Position  */
#define SCU_GENERAL_MIRRSTS_RTC_TIM0_Msk      (0x01UL << SCU_GENERAL_MIRRSTS_RTC_TIM0_Pos)            /*!< SCU_GENERAL MIRRSTS: RTC_TIM0 Mask      */
#define SCU_GENERAL_MIRRSTS_RTC_TIM1_Pos      4                                                       /*!< SCU_GENERAL MIRRSTS: RTC_TIM1 Position  */
#define SCU_GENERAL_MIRRSTS_RTC_TIM1_Msk      (0x01UL << SCU_GENERAL_MIRRSTS_RTC_TIM1_Pos)            /*!< SCU_GENERAL MIRRSTS: RTC_TIM1 Mask      */

/* ------------------------------  SCU_GENERAL_PMTSR  ----------------------------- */
#define SCU_GENERAL_PMTSR_MTENS_Pos           0                                                       /*!< SCU_GENERAL PMTSR: MTENS Position       */
#define SCU_GENERAL_PMTSR_MTENS_Msk           (0x01UL << SCU_GENERAL_PMTSR_MTENS_Pos)                 /*!< SCU_GENERAL PMTSR: MTENS Mask           */


/* ================================================================================ */
/* ================     struct 'SCU_INTERRUPT' Position & Mask     ================ */
/* ================================================================================ */


/* -----------------------------  SCU_INTERRUPT_SRRAW  ---------------------------- */
#define SCU_INTERRUPT_SRRAW_PRWARN_Pos        0                                                       /*!< SCU_INTERRUPT SRRAW: PRWARN Position    */
#define SCU_INTERRUPT_SRRAW_PRWARN_Msk        (0x01UL << SCU_INTERRUPT_SRRAW_PRWARN_Pos)              /*!< SCU_INTERRUPT SRRAW: PRWARN Mask        */
#define SCU_INTERRUPT_SRRAW_PI_Pos            1                                                       /*!< SCU_INTERRUPT SRRAW: PI Position        */
#define SCU_INTERRUPT_SRRAW_PI_Msk            (0x01UL << SCU_INTERRUPT_SRRAW_PI_Pos)                  /*!< SCU_INTERRUPT SRRAW: PI Mask            */
#define SCU_INTERRUPT_SRRAW_AI_Pos            2                                                       /*!< SCU_INTERRUPT SRRAW: AI Position        */
#define SCU_INTERRUPT_SRRAW_AI_Msk            (0x01UL << SCU_INTERRUPT_SRRAW_AI_Pos)                  /*!< SCU_INTERRUPT SRRAW: AI Mask            */
#define SCU_INTERRUPT_SRRAW_VDDPI_Pos         3                                                       /*!< SCU_INTERRUPT SRRAW: VDDPI Position     */
#define SCU_INTERRUPT_SRRAW_VDDPI_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_VDDPI_Pos)               /*!< SCU_INTERRUPT SRRAW: VDDPI Mask         */
#define SCU_INTERRUPT_SRRAW_ACMP0I_Pos        4                                                       /*!< SCU_INTERRUPT SRRAW: ACMP0I Position    */
#define SCU_INTERRUPT_SRRAW_ACMP0I_Msk        (0x01UL << SCU_INTERRUPT_SRRAW_ACMP0I_Pos)              /*!< SCU_INTERRUPT SRRAW: ACMP0I Mask        */
#define SCU_INTERRUPT_SRRAW_ACMP1I_Pos        5                                                       /*!< SCU_INTERRUPT SRRAW: ACMP1I Position    */
#define SCU_INTERRUPT_SRRAW_ACMP1I_Msk        (0x01UL << SCU_INTERRUPT_SRRAW_ACMP1I_Pos)              /*!< SCU_INTERRUPT SRRAW: ACMP1I Mask        */
#define SCU_INTERRUPT_SRRAW_ACMP2I_Pos        6                                                       /*!< SCU_INTERRUPT SRRAW: ACMP2I Position    */
#define SCU_INTERRUPT_SRRAW_ACMP2I_Msk        (0x01UL << SCU_INTERRUPT_SRRAW_ACMP2I_Pos)              /*!< SCU_INTERRUPT SRRAW: ACMP2I Mask        */
#define SCU_INTERRUPT_SRRAW_VDROPI_Pos        7                                                       /*!< SCU_INTERRUPT SRRAW: VDROPI Position    */
#define SCU_INTERRUPT_SRRAW_VDROPI_Msk        (0x01UL << SCU_INTERRUPT_SRRAW_VDROPI_Pos)              /*!< SCU_INTERRUPT SRRAW: VDROPI Mask        */
#define SCU_INTERRUPT_SRRAW_ORC0I_Pos         8                                                       /*!< SCU_INTERRUPT SRRAW: ORC0I Position     */
#define SCU_INTERRUPT_SRRAW_ORC0I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC0I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC0I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC1I_Pos         9                                                       /*!< SCU_INTERRUPT SRRAW: ORC1I Position     */
#define SCU_INTERRUPT_SRRAW_ORC1I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC1I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC1I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC2I_Pos         10                                                      /*!< SCU_INTERRUPT SRRAW: ORC2I Position     */
#define SCU_INTERRUPT_SRRAW_ORC2I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC2I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC2I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC3I_Pos         11                                                      /*!< SCU_INTERRUPT SRRAW: ORC3I Position     */
#define SCU_INTERRUPT_SRRAW_ORC3I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC3I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC3I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC4I_Pos         12                                                      /*!< SCU_INTERRUPT SRRAW: ORC4I Position     */
#define SCU_INTERRUPT_SRRAW_ORC4I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC4I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC4I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC5I_Pos         13                                                      /*!< SCU_INTERRUPT SRRAW: ORC5I Position     */
#define SCU_INTERRUPT_SRRAW_ORC5I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC5I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC5I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC6I_Pos         14                                                      /*!< SCU_INTERRUPT SRRAW: ORC6I Position     */
#define SCU_INTERRUPT_SRRAW_ORC6I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC6I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC6I Mask         */
#define SCU_INTERRUPT_SRRAW_ORC7I_Pos         15                                                      /*!< SCU_INTERRUPT SRRAW: ORC7I Position     */
#define SCU_INTERRUPT_SRRAW_ORC7I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_ORC7I_Pos)               /*!< SCU_INTERRUPT SRRAW: ORC7I Mask         */
#define SCU_INTERRUPT_SRRAW_LOCI_Pos          16                                                      /*!< SCU_INTERRUPT SRRAW: LOCI Position      */
#define SCU_INTERRUPT_SRRAW_LOCI_Msk          (0x01UL << SCU_INTERRUPT_SRRAW_LOCI_Pos)                /*!< SCU_INTERRUPT SRRAW: LOCI Mask          */
#define SCU_INTERRUPT_SRRAW_PESRAMI_Pos       17                                                      /*!< SCU_INTERRUPT SRRAW: PESRAMI Position   */
#define SCU_INTERRUPT_SRRAW_PESRAMI_Msk       (0x01UL << SCU_INTERRUPT_SRRAW_PESRAMI_Pos)             /*!< SCU_INTERRUPT SRRAW: PESRAMI Mask       */
#define SCU_INTERRUPT_SRRAW_PEU0I_Pos         18                                                      /*!< SCU_INTERRUPT SRRAW: PEU0I Position     */
#define SCU_INTERRUPT_SRRAW_PEU0I_Msk         (0x01UL << SCU_INTERRUPT_SRRAW_PEU0I_Pos)               /*!< SCU_INTERRUPT SRRAW: PEU0I Mask         */
#define SCU_INTERRUPT_SRRAW_FLECC2I_Pos       19                                                      /*!< SCU_INTERRUPT SRRAW: FLECC2I Position   */
#define SCU_INTERRUPT_SRRAW_FLECC2I_Msk       (0x01UL << SCU_INTERRUPT_SRRAW_FLECC2I_Pos)             /*!< SCU_INTERRUPT SRRAW: FLECC2I Mask       */
#define SCU_INTERRUPT_SRRAW_FLCMPLTI_Pos      20                                                      /*!< SCU_INTERRUPT SRRAW: FLCMPLTI Position  */
#define SCU_INTERRUPT_SRRAW_FLCMPLTI_Msk      (0x01UL << SCU_INTERRUPT_SRRAW_FLCMPLTI_Pos)            /*!< SCU_INTERRUPT SRRAW: FLCMPLTI Mask      */
#define SCU_INTERRUPT_SRRAW_VCLIPI_Pos        21                                                      /*!< SCU_INTERRUPT SRRAW: VCLIPI Position    */
#define SCU_INTERRUPT_SRRAW_VCLIPI_Msk        (0x01UL << SCU_INTERRUPT_SRRAW_VCLIPI_Pos)              /*!< SCU_INTERRUPT SRRAW: VCLIPI Mask        */
#define SCU_INTERRUPT_SRRAW_SBYCLKFI_Pos      22                                                      /*!< SCU_INTERRUPT SRRAW: SBYCLKFI Position  */
#define SCU_INTERRUPT_SRRAW_SBYCLKFI_Msk      (0x01UL << SCU_INTERRUPT_SRRAW_SBYCLKFI_Pos)            /*!< SCU_INTERRUPT SRRAW: SBYCLKFI Mask      */
#define SCU_INTERRUPT_SRRAW_RTC_CTR_Pos       24                                                      /*!< SCU_INTERRUPT SRRAW: RTC_CTR Position   */
#define SCU_INTERRUPT_SRRAW_RTC_CTR_Msk       (0x01UL << SCU_INTERRUPT_SRRAW_RTC_CTR_Pos)             /*!< SCU_INTERRUPT SRRAW: RTC_CTR Mask       */
#define SCU_INTERRUPT_SRRAW_RTC_ATIM0_Pos     25                                                      /*!< SCU_INTERRUPT SRRAW: RTC_ATIM0 Position */
#define SCU_INTERRUPT_SRRAW_RTC_ATIM0_Msk     (0x01UL << SCU_INTERRUPT_SRRAW_RTC_ATIM0_Pos)           /*!< SCU_INTERRUPT SRRAW: RTC_ATIM0 Mask     */
#define SCU_INTERRUPT_SRRAW_RTC_ATIM1_Pos     26                                                      /*!< SCU_INTERRUPT SRRAW: RTC_ATIM1 Position */
#define SCU_INTERRUPT_SRRAW_RTC_ATIM1_Msk     (0x01UL << SCU_INTERRUPT_SRRAW_RTC_ATIM1_Pos)           /*!< SCU_INTERRUPT SRRAW: RTC_ATIM1 Mask     */
#define SCU_INTERRUPT_SRRAW_RTC_TIM0_Pos      27                                                      /*!< SCU_INTERRUPT SRRAW: RTC_TIM0 Position  */
#define SCU_INTERRUPT_SRRAW_RTC_TIM0_Msk      (0x01UL << SCU_INTERRUPT_SRRAW_RTC_TIM0_Pos)            /*!< SCU_INTERRUPT SRRAW: RTC_TIM0 Mask      */
#define SCU_INTERRUPT_SRRAW_RTC_TIM1_Pos      28                                                      /*!< SCU_INTERRUPT SRRAW: RTC_TIM1 Position  */
#define SCU_INTERRUPT_SRRAW_RTC_TIM1_Msk      (0x01UL << SCU_INTERRUPT_SRRAW_RTC_TIM1_Pos)            /*!< SCU_INTERRUPT SRRAW: RTC_TIM1 Mask      */
#define SCU_INTERRUPT_SRRAW_TSE_DONE_Pos      29                                                      /*!< SCU_INTERRUPT SRRAW: TSE_DONE Position  */
#define SCU_INTERRUPT_SRRAW_TSE_DONE_Msk      (0x01UL << SCU_INTERRUPT_SRRAW_TSE_DONE_Pos)            /*!< SCU_INTERRUPT SRRAW: TSE_DONE Mask      */
#define SCU_INTERRUPT_SRRAW_TSE_HIGH_Pos      30                                                      /*!< SCU_INTERRUPT SRRAW: TSE_HIGH Position  */
#define SCU_INTERRUPT_SRRAW_TSE_HIGH_Msk      (0x01UL << SCU_INTERRUPT_SRRAW_TSE_HIGH_Pos)            /*!< SCU_INTERRUPT SRRAW: TSE_HIGH Mask      */
#define SCU_INTERRUPT_SRRAW_TSE_LOW_Pos       31                                                      /*!< SCU_INTERRUPT SRRAW: TSE_LOW Position   */
#define SCU_INTERRUPT_SRRAW_TSE_LOW_Msk       (0x01UL << SCU_INTERRUPT_SRRAW_TSE_LOW_Pos)             /*!< SCU_INTERRUPT SRRAW: TSE_LOW Mask       */

/* -----------------------------  SCU_INTERRUPT_SRMSK  ---------------------------- */
#define SCU_INTERRUPT_SRMSK_PRWARN_Pos        0                                                       /*!< SCU_INTERRUPT SRMSK: PRWARN Position    */
#define SCU_INTERRUPT_SRMSK_PRWARN_Msk        (0x01UL << SCU_INTERRUPT_SRMSK_PRWARN_Pos)              /*!< SCU_INTERRUPT SRMSK: PRWARN Mask        */
#define SCU_INTERRUPT_SRMSK_VDDPI_Pos         3                                                       /*!< SCU_INTERRUPT SRMSK: VDDPI Position     */
#define SCU_INTERRUPT_SRMSK_VDDPI_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_VDDPI_Pos)               /*!< SCU_INTERRUPT SRMSK: VDDPI Mask         */
#define SCU_INTERRUPT_SRMSK_ACMP0I_Pos        4                                                       /*!< SCU_INTERRUPT SRMSK: ACMP0I Position    */
#define SCU_INTERRUPT_SRMSK_ACMP0I_Msk        (0x01UL << SCU_INTERRUPT_SRMSK_ACMP0I_Pos)              /*!< SCU_INTERRUPT SRMSK: ACMP0I Mask        */
#define SCU_INTERRUPT_SRMSK_ACMP1I_Pos        5                                                       /*!< SCU_INTERRUPT SRMSK: ACMP1I Position    */
#define SCU_INTERRUPT_SRMSK_ACMP1I_Msk        (0x01UL << SCU_INTERRUPT_SRMSK_ACMP1I_Pos)              /*!< SCU_INTERRUPT SRMSK: ACMP1I Mask        */
#define SCU_INTERRUPT_SRMSK_ACMP2I_Pos        6                                                       /*!< SCU_INTERRUPT SRMSK: ACMP2I Position    */
#define SCU_INTERRUPT_SRMSK_ACMP2I_Msk        (0x01UL << SCU_INTERRUPT_SRMSK_ACMP2I_Pos)              /*!< SCU_INTERRUPT SRMSK: ACMP2I Mask        */
#define SCU_INTERRUPT_SRMSK_VDROPI_Pos        7                                                       /*!< SCU_INTERRUPT SRMSK: VDROPI Position    */
#define SCU_INTERRUPT_SRMSK_VDROPI_Msk        (0x01UL << SCU_INTERRUPT_SRMSK_VDROPI_Pos)              /*!< SCU_INTERRUPT SRMSK: VDROPI Mask        */
#define SCU_INTERRUPT_SRMSK_ORC0I_Pos         8                                                       /*!< SCU_INTERRUPT SRMSK: ORC0I Position     */
#define SCU_INTERRUPT_SRMSK_ORC0I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC0I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC0I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC1I_Pos         9                                                       /*!< SCU_INTERRUPT SRMSK: ORC1I Position     */
#define SCU_INTERRUPT_SRMSK_ORC1I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC1I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC1I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC2I_Pos         10                                                      /*!< SCU_INTERRUPT SRMSK: ORC2I Position     */
#define SCU_INTERRUPT_SRMSK_ORC2I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC2I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC2I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC3I_Pos         11                                                      /*!< SCU_INTERRUPT SRMSK: ORC3I Position     */
#define SCU_INTERRUPT_SRMSK_ORC3I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC3I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC3I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC4I_Pos         12                                                      /*!< SCU_INTERRUPT SRMSK: ORC4I Position     */
#define SCU_INTERRUPT_SRMSK_ORC4I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC4I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC4I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC5I_Pos         13                                                      /*!< SCU_INTERRUPT SRMSK: ORC5I Position     */
#define SCU_INTERRUPT_SRMSK_ORC5I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC5I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC5I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC6I_Pos         14                                                      /*!< SCU_INTERRUPT SRMSK: ORC6I Position     */
#define SCU_INTERRUPT_SRMSK_ORC6I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC6I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC6I Mask         */
#define SCU_INTERRUPT_SRMSK_ORC7I_Pos         15                                                      /*!< SCU_INTERRUPT SRMSK: ORC7I Position     */
#define SCU_INTERRUPT_SRMSK_ORC7I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_ORC7I_Pos)               /*!< SCU_INTERRUPT SRMSK: ORC7I Mask         */
#define SCU_INTERRUPT_SRMSK_LOCI_Pos          16                                                      /*!< SCU_INTERRUPT SRMSK: LOCI Position      */
#define SCU_INTERRUPT_SRMSK_LOCI_Msk          (0x01UL << SCU_INTERRUPT_SRMSK_LOCI_Pos)                /*!< SCU_INTERRUPT SRMSK: LOCI Mask          */
#define SCU_INTERRUPT_SRMSK_PESRAMI_Pos       17                                                      /*!< SCU_INTERRUPT SRMSK: PESRAMI Position   */
#define SCU_INTERRUPT_SRMSK_PESRAMI_Msk       (0x01UL << SCU_INTERRUPT_SRMSK_PESRAMI_Pos)             /*!< SCU_INTERRUPT SRMSK: PESRAMI Mask       */
#define SCU_INTERRUPT_SRMSK_PEU0I_Pos         18                                                      /*!< SCU_INTERRUPT SRMSK: PEU0I Position     */
#define SCU_INTERRUPT_SRMSK_PEU0I_Msk         (0x01UL << SCU_INTERRUPT_SRMSK_PEU0I_Pos)               /*!< SCU_INTERRUPT SRMSK: PEU0I Mask         */
#define SCU_INTERRUPT_SRMSK_FLECC2I_Pos       19                                                      /*!< SCU_INTERRUPT SRMSK: FLECC2I Position   */
#define SCU_INTERRUPT_SRMSK_FLECC2I_Msk       (0x01UL << SCU_INTERRUPT_SRMSK_FLECC2I_Pos)             /*!< SCU_INTERRUPT SRMSK: FLECC2I Mask       */
#define SCU_INTERRUPT_SRMSK_VCLIPI_Pos        21                                                      /*!< SCU_INTERRUPT SRMSK: VCLIPI Position    */
#define SCU_INTERRUPT_SRMSK_VCLIPI_Msk        (0x01UL << SCU_INTERRUPT_SRMSK_VCLIPI_Pos)              /*!< SCU_INTERRUPT SRMSK: VCLIPI Mask        */
#define SCU_INTERRUPT_SRMSK_SBYCLKFI_Pos      22                                                      /*!< SCU_INTERRUPT SRMSK: SBYCLKFI Position  */
#define SCU_INTERRUPT_SRMSK_SBYCLKFI_Msk      (0x01UL << SCU_INTERRUPT_SRMSK_SBYCLKFI_Pos)            /*!< SCU_INTERRUPT SRMSK: SBYCLKFI Mask      */
#define SCU_INTERRUPT_SRMSK_RTC_CTR_Pos       24                                                      /*!< SCU_INTERRUPT SRMSK: RTC_CTR Position   */
#define SCU_INTERRUPT_SRMSK_RTC_CTR_Msk       (0x01UL << SCU_INTERRUPT_SRMSK_RTC_CTR_Pos)             /*!< SCU_INTERRUPT SRMSK: RTC_CTR Mask       */
#define SCU_INTERRUPT_SRMSK_RTC_ATIM0_Pos     25                                                      /*!< SCU_INTERRUPT SRMSK: RTC_ATIM0 Position */
#define SCU_INTERRUPT_SRMSK_RTC_ATIM0_Msk     (0x01UL << SCU_INTERRUPT_SRMSK_RTC_ATIM0_Pos)           /*!< SCU_INTERRUPT SRMSK: RTC_ATIM0 Mask     */
#define SCU_INTERRUPT_SRMSK_RTC_ATIM1_Pos     26                                                      /*!< SCU_INTERRUPT SRMSK: RTC_ATIM1 Position */
#define SCU_INTERRUPT_SRMSK_RTC_ATIM1_Msk     (0x01UL << SCU_INTERRUPT_SRMSK_RTC_ATIM1_Pos)           /*!< SCU_INTERRUPT SRMSK: RTC_ATIM1 Mask     */
#define SCU_INTERRUPT_SRMSK_RTC_TIM0_Pos      27                                                      /*!< SCU_INTERRUPT SRMSK: RTC_TIM0 Position  */
#define SCU_INTERRUPT_SRMSK_RTC_TIM0_Msk      (0x01UL << SCU_INTERRUPT_SRMSK_RTC_TIM0_Pos)            /*!< SCU_INTERRUPT SRMSK: RTC_TIM0 Mask      */
#define SCU_INTERRUPT_SRMSK_RTC_TIM1_Pos      28                                                      /*!< SCU_INTERRUPT SRMSK: RTC_TIM1 Position  */
#define SCU_INTERRUPT_SRMSK_RTC_TIM1_Msk      (0x01UL << SCU_INTERRUPT_SRMSK_RTC_TIM1_Pos)            /*!< SCU_INTERRUPT SRMSK: RTC_TIM1 Mask      */
#define SCU_INTERRUPT_SRMSK_TSE_DONE_Pos      29                                                      /*!< SCU_INTERRUPT SRMSK: TSE_DONE Position  */
#define SCU_INTERRUPT_SRMSK_TSE_DONE_Msk      (0x01UL << SCU_INTERRUPT_SRMSK_TSE_DONE_Pos)            /*!< SCU_INTERRUPT SRMSK: TSE_DONE Mask      */
#define SCU_INTERRUPT_SRMSK_TSE_HIGH_Pos      30                                                      /*!< SCU_INTERRUPT SRMSK: TSE_HIGH Position  */
#define SCU_INTERRUPT_SRMSK_TSE_HIGH_Msk      (0x01UL << SCU_INTERRUPT_SRMSK_TSE_HIGH_Pos)            /*!< SCU_INTERRUPT SRMSK: TSE_HIGH Mask      */
#define SCU_INTERRUPT_SRMSK_TSE_LOW_Pos       31                                                      /*!< SCU_INTERRUPT SRMSK: TSE_LOW Position   */
#define SCU_INTERRUPT_SRMSK_TSE_LOW_Msk       (0x01UL << SCU_INTERRUPT_SRMSK_TSE_LOW_Pos)             /*!< SCU_INTERRUPT SRMSK: TSE_LOW Mask       */

/* -----------------------------  SCU_INTERRUPT_SRCLR  ---------------------------- */
#define SCU_INTERRUPT_SRCLR_PRWARN_Pos        0                                                       /*!< SCU_INTERRUPT SRCLR: PRWARN Position    */
#define SCU_INTERRUPT_SRCLR_PRWARN_Msk        (0x01UL << SCU_INTERRUPT_SRCLR_PRWARN_Pos)              /*!< SCU_INTERRUPT SRCLR: PRWARN Mask        */
#define SCU_INTERRUPT_SRCLR_PI_Pos            1                                                       /*!< SCU_INTERRUPT SRCLR: PI Position        */
#define SCU_INTERRUPT_SRCLR_PI_Msk            (0x01UL << SCU_INTERRUPT_SRCLR_PI_Pos)                  /*!< SCU_INTERRUPT SRCLR: PI Mask            */
#define SCU_INTERRUPT_SRCLR_AI_Pos            2                                                       /*!< SCU_INTERRUPT SRCLR: AI Position        */
#define SCU_INTERRUPT_SRCLR_AI_Msk            (0x01UL << SCU_INTERRUPT_SRCLR_AI_Pos)                  /*!< SCU_INTERRUPT SRCLR: AI Mask            */
#define SCU_INTERRUPT_SRCLR_VDDPI_Pos         3                                                       /*!< SCU_INTERRUPT SRCLR: VDDPI Position     */
#define SCU_INTERRUPT_SRCLR_VDDPI_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_VDDPI_Pos)               /*!< SCU_INTERRUPT SRCLR: VDDPI Mask         */
#define SCU_INTERRUPT_SRCLR_ACMP0I_Pos        4                                                       /*!< SCU_INTERRUPT SRCLR: ACMP0I Position    */
#define SCU_INTERRUPT_SRCLR_ACMP0I_Msk        (0x01UL << SCU_INTERRUPT_SRCLR_ACMP0I_Pos)              /*!< SCU_INTERRUPT SRCLR: ACMP0I Mask        */
#define SCU_INTERRUPT_SRCLR_ACMP1I_Pos        5                                                       /*!< SCU_INTERRUPT SRCLR: ACMP1I Position    */
#define SCU_INTERRUPT_SRCLR_ACMP1I_Msk        (0x01UL << SCU_INTERRUPT_SRCLR_ACMP1I_Pos)              /*!< SCU_INTERRUPT SRCLR: ACMP1I Mask        */
#define SCU_INTERRUPT_SRCLR_ACMP2I_Pos        6                                                       /*!< SCU_INTERRUPT SRCLR: ACMP2I Position    */
#define SCU_INTERRUPT_SRCLR_ACMP2I_Msk        (0x01UL << SCU_INTERRUPT_SRCLR_ACMP2I_Pos)              /*!< SCU_INTERRUPT SRCLR: ACMP2I Mask        */
#define SCU_INTERRUPT_SRCLR_VDROPI_Pos        7                                                       /*!< SCU_INTERRUPT SRCLR: VDROPI Position    */
#define SCU_INTERRUPT_SRCLR_VDROPI_Msk        (0x01UL << SCU_INTERRUPT_SRCLR_VDROPI_Pos)              /*!< SCU_INTERRUPT SRCLR: VDROPI Mask        */
#define SCU_INTERRUPT_SRCLR_ORC0I_Pos         8                                                       /*!< SCU_INTERRUPT SRCLR: ORC0I Position     */
#define SCU_INTERRUPT_SRCLR_ORC0I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC0I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC0I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC1I_Pos         9                                                       /*!< SCU_INTERRUPT SRCLR: ORC1I Position     */
#define SCU_INTERRUPT_SRCLR_ORC1I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC1I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC1I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC2I_Pos         10                                                      /*!< SCU_INTERRUPT SRCLR: ORC2I Position     */
#define SCU_INTERRUPT_SRCLR_ORC2I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC2I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC2I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC3I_Pos         11                                                      /*!< SCU_INTERRUPT SRCLR: ORC3I Position     */
#define SCU_INTERRUPT_SRCLR_ORC3I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC3I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC3I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC4I_Pos         12                                                      /*!< SCU_INTERRUPT SRCLR: ORC4I Position     */
#define SCU_INTERRUPT_SRCLR_ORC4I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC4I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC4I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC5I_Pos         13                                                      /*!< SCU_INTERRUPT SRCLR: ORC5I Position     */
#define SCU_INTERRUPT_SRCLR_ORC5I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC5I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC5I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC6I_Pos         14                                                      /*!< SCU_INTERRUPT SRCLR: ORC6I Position     */
#define SCU_INTERRUPT_SRCLR_ORC6I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC6I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC6I Mask         */
#define SCU_INTERRUPT_SRCLR_ORC7I_Pos         15                                                      /*!< SCU_INTERRUPT SRCLR: ORC7I Position     */
#define SCU_INTERRUPT_SRCLR_ORC7I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_ORC7I_Pos)               /*!< SCU_INTERRUPT SRCLR: ORC7I Mask         */
#define SCU_INTERRUPT_SRCLR_LOCI_Pos          16                                                      /*!< SCU_INTERRUPT SRCLR: LOCI Position      */
#define SCU_INTERRUPT_SRCLR_LOCI_Msk          (0x01UL << SCU_INTERRUPT_SRCLR_LOCI_Pos)                /*!< SCU_INTERRUPT SRCLR: LOCI Mask          */
#define SCU_INTERRUPT_SRCLR_PESRAMI_Pos       17                                                      /*!< SCU_INTERRUPT SRCLR: PESRAMI Position   */
#define SCU_INTERRUPT_SRCLR_PESRAMI_Msk       (0x01UL << SCU_INTERRUPT_SRCLR_PESRAMI_Pos)             /*!< SCU_INTERRUPT SRCLR: PESRAMI Mask       */
#define SCU_INTERRUPT_SRCLR_PEU0I_Pos         18                                                      /*!< SCU_INTERRUPT SRCLR: PEU0I Position     */
#define SCU_INTERRUPT_SRCLR_PEU0I_Msk         (0x01UL << SCU_INTERRUPT_SRCLR_PEU0I_Pos)               /*!< SCU_INTERRUPT SRCLR: PEU0I Mask         */
#define SCU_INTERRUPT_SRCLR_FLECC2I_Pos       19                                                      /*!< SCU_INTERRUPT SRCLR: FLECC2I Position   */
#define SCU_INTERRUPT_SRCLR_FLECC2I_Msk       (0x01UL << SCU_INTERRUPT_SRCLR_FLECC2I_Pos)             /*!< SCU_INTERRUPT SRCLR: FLECC2I Mask       */
#define SCU_INTERRUPT_SRCLR_FLCMPLTI_Pos      20                                                      /*!< SCU_INTERRUPT SRCLR: FLCMPLTI Position  */
#define SCU_INTERRUPT_SRCLR_FLCMPLTI_Msk      (0x01UL << SCU_INTERRUPT_SRCLR_FLCMPLTI_Pos)            /*!< SCU_INTERRUPT SRCLR: FLCMPLTI Mask      */
#define SCU_INTERRUPT_SRCLR_VCLIPI_Pos        21                                                      /*!< SCU_INTERRUPT SRCLR: VCLIPI Position    */
#define SCU_INTERRUPT_SRCLR_VCLIPI_Msk        (0x01UL << SCU_INTERRUPT_SRCLR_VCLIPI_Pos)              /*!< SCU_INTERRUPT SRCLR: VCLIPI Mask        */
#define SCU_INTERRUPT_SRCLR_SBYCLKFI_Pos      22                                                      /*!< SCU_INTERRUPT SRCLR: SBYCLKFI Position  */
#define SCU_INTERRUPT_SRCLR_SBYCLKFI_Msk      (0x01UL << SCU_INTERRUPT_SRCLR_SBYCLKFI_Pos)            /*!< SCU_INTERRUPT SRCLR: SBYCLKFI Mask      */
#define SCU_INTERRUPT_SRCLR_RTC_CTR_Pos       24                                                      /*!< SCU_INTERRUPT SRCLR: RTC_CTR Position   */
#define SCU_INTERRUPT_SRCLR_RTC_CTR_Msk       (0x01UL << SCU_INTERRUPT_SRCLR_RTC_CTR_Pos)             /*!< SCU_INTERRUPT SRCLR: RTC_CTR Mask       */
#define SCU_INTERRUPT_SRCLR_RTC_ATIM0_Pos     25                                                      /*!< SCU_INTERRUPT SRCLR: RTC_ATIM0 Position */
#define SCU_INTERRUPT_SRCLR_RTC_ATIM0_Msk     (0x01UL << SCU_INTERRUPT_SRCLR_RTC_ATIM0_Pos)           /*!< SCU_INTERRUPT SRCLR: RTC_ATIM0 Mask     */
#define SCU_INTERRUPT_SRCLR_RTC_ATIM1_Pos     26                                                      /*!< SCU_INTERRUPT SRCLR: RTC_ATIM1 Position */
#define SCU_INTERRUPT_SRCLR_RTC_ATIM1_Msk     (0x01UL << SCU_INTERRUPT_SRCLR_RTC_ATIM1_Pos)           /*!< SCU_INTERRUPT SRCLR: RTC_ATIM1 Mask     */
#define SCU_INTERRUPT_SRCLR_RTC_TIM0_Pos      27                                                      /*!< SCU_INTERRUPT SRCLR: RTC_TIM0 Position  */
#define SCU_INTERRUPT_SRCLR_RTC_TIM0_Msk      (0x01UL << SCU_INTERRUPT_SRCLR_RTC_TIM0_Pos)            /*!< SCU_INTERRUPT SRCLR: RTC_TIM0 Mask      */
#define SCU_INTERRUPT_SRCLR_RTC_TIM1_Pos      28                                                      /*!< SCU_INTERRUPT SRCLR: RTC_TIM1 Position  */
#define SCU_INTERRUPT_SRCLR_RTC_TIM1_Msk      (0x01UL << SCU_INTERRUPT_SRCLR_RTC_TIM1_Pos)            /*!< SCU_INTERRUPT SRCLR: RTC_TIM1 Mask      */
#define SCU_INTERRUPT_SRCLR_TSE_DONE_Pos      29                                                      /*!< SCU_INTERRUPT SRCLR: TSE_DONE Position  */
#define SCU_INTERRUPT_SRCLR_TSE_DONE_Msk      (0x01UL << SCU_INTERRUPT_SRCLR_TSE_DONE_Pos)            /*!< SCU_INTERRUPT SRCLR: TSE_DONE Mask      */
#define SCU_INTERRUPT_SRCLR_TSE_HIGH_Pos      30                                                      /*!< SCU_INTERRUPT SRCLR: TSE_HIGH Position  */
#define SCU_INTERRUPT_SRCLR_TSE_HIGH_Msk      (0x01UL << SCU_INTERRUPT_SRCLR_TSE_HIGH_Pos)            /*!< SCU_INTERRUPT SRCLR: TSE_HIGH Mask      */
#define SCU_INTERRUPT_SRCLR_TSE_LOW_Pos       31                                                      /*!< SCU_INTERRUPT SRCLR: TSE_LOW Position   */
#define SCU_INTERRUPT_SRCLR_TSE_LOW_Msk       (0x01UL << SCU_INTERRUPT_SRCLR_TSE_LOW_Pos)             /*!< SCU_INTERRUPT SRCLR: TSE_LOW Mask       */

/* -----------------------------  SCU_INTERRUPT_SRSET  ---------------------------- */
#define SCU_INTERRUPT_SRSET_PRWARN_Pos        0                                                       /*!< SCU_INTERRUPT SRSET: PRWARN Position    */
#define SCU_INTERRUPT_SRSET_PRWARN_Msk        (0x01UL << SCU_INTERRUPT_SRSET_PRWARN_Pos)              /*!< SCU_INTERRUPT SRSET: PRWARN Mask        */
#define SCU_INTERRUPT_SRSET_PI_Pos            1                                                       /*!< SCU_INTERRUPT SRSET: PI Position        */
#define SCU_INTERRUPT_SRSET_PI_Msk            (0x01UL << SCU_INTERRUPT_SRSET_PI_Pos)                  /*!< SCU_INTERRUPT SRSET: PI Mask            */
#define SCU_INTERRUPT_SRSET_AI_Pos            2                                                       /*!< SCU_INTERRUPT SRSET: AI Position        */
#define SCU_INTERRUPT_SRSET_AI_Msk            (0x01UL << SCU_INTERRUPT_SRSET_AI_Pos)                  /*!< SCU_INTERRUPT SRSET: AI Mask            */
#define SCU_INTERRUPT_SRSET_VDDPI_Pos         3                                                       /*!< SCU_INTERRUPT SRSET: VDDPI Position     */
#define SCU_INTERRUPT_SRSET_VDDPI_Msk         (0x01UL << SCU_INTERRUPT_SRSET_VDDPI_Pos)               /*!< SCU_INTERRUPT SRSET: VDDPI Mask         */
#define SCU_INTERRUPT_SRSET_ACMP0I_Pos        4                                                       /*!< SCU_INTERRUPT SRSET: ACMP0I Position    */
#define SCU_INTERRUPT_SRSET_ACMP0I_Msk        (0x01UL << SCU_INTERRUPT_SRSET_ACMP0I_Pos)              /*!< SCU_INTERRUPT SRSET: ACMP0I Mask        */
#define SCU_INTERRUPT_SRSET_ACMP1I_Pos        5                                                       /*!< SCU_INTERRUPT SRSET: ACMP1I Position    */
#define SCU_INTERRUPT_SRSET_ACMP1I_Msk        (0x01UL << SCU_INTERRUPT_SRSET_ACMP1I_Pos)              /*!< SCU_INTERRUPT SRSET: ACMP1I Mask        */
#define SCU_INTERRUPT_SRSET_ACMP2I_Pos        6                                                       /*!< SCU_INTERRUPT SRSET: ACMP2I Position    */
#define SCU_INTERRUPT_SRSET_ACMP2I_Msk        (0x01UL << SCU_INTERRUPT_SRSET_ACMP2I_Pos)              /*!< SCU_INTERRUPT SRSET: ACMP2I Mask        */
#define SCU_INTERRUPT_SRSET_VDROPI_Pos        7                                                       /*!< SCU_INTERRUPT SRSET: VDROPI Position    */
#define SCU_INTERRUPT_SRSET_VDROPI_Msk        (0x01UL << SCU_INTERRUPT_SRSET_VDROPI_Pos)              /*!< SCU_INTERRUPT SRSET: VDROPI Mask        */
#define SCU_INTERRUPT_SRSET_ORC0I_Pos         8                                                       /*!< SCU_INTERRUPT SRSET: ORC0I Position     */
#define SCU_INTERRUPT_SRSET_ORC0I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC0I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC0I Mask         */
#define SCU_INTERRUPT_SRSET_ORC1I_Pos         9                                                       /*!< SCU_INTERRUPT SRSET: ORC1I Position     */
#define SCU_INTERRUPT_SRSET_ORC1I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC1I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC1I Mask         */
#define SCU_INTERRUPT_SRSET_ORC2I_Pos         10                                                      /*!< SCU_INTERRUPT SRSET: ORC2I Position     */
#define SCU_INTERRUPT_SRSET_ORC2I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC2I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC2I Mask         */
#define SCU_INTERRUPT_SRSET_ORC3I_Pos         11                                                      /*!< SCU_INTERRUPT SRSET: ORC3I Position     */
#define SCU_INTERRUPT_SRSET_ORC3I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC3I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC3I Mask         */
#define SCU_INTERRUPT_SRSET_ORC4I_Pos         12                                                      /*!< SCU_INTERRUPT SRSET: ORC4I Position     */
#define SCU_INTERRUPT_SRSET_ORC4I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC4I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC4I Mask         */
#define SCU_INTERRUPT_SRSET_ORC5I_Pos         13                                                      /*!< SCU_INTERRUPT SRSET: ORC5I Position     */
#define SCU_INTERRUPT_SRSET_ORC5I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC5I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC5I Mask         */
#define SCU_INTERRUPT_SRSET_ORC6I_Pos         14                                                      /*!< SCU_INTERRUPT SRSET: ORC6I Position     */
#define SCU_INTERRUPT_SRSET_ORC6I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC6I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC6I Mask         */
#define SCU_INTERRUPT_SRSET_ORC7I_Pos         15                                                      /*!< SCU_INTERRUPT SRSET: ORC7I Position     */
#define SCU_INTERRUPT_SRSET_ORC7I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_ORC7I_Pos)               /*!< SCU_INTERRUPT SRSET: ORC7I Mask         */
#define SCU_INTERRUPT_SRSET_LOCI_Pos          16                                                      /*!< SCU_INTERRUPT SRSET: LOCI Position      */
#define SCU_INTERRUPT_SRSET_LOCI_Msk          (0x01UL << SCU_INTERRUPT_SRSET_LOCI_Pos)                /*!< SCU_INTERRUPT SRSET: LOCI Mask          */
#define SCU_INTERRUPT_SRSET_PESRAMI_Pos       17                                                      /*!< SCU_INTERRUPT SRSET: PESRAMI Position   */
#define SCU_INTERRUPT_SRSET_PESRAMI_Msk       (0x01UL << SCU_INTERRUPT_SRSET_PESRAMI_Pos)             /*!< SCU_INTERRUPT SRSET: PESRAMI Mask       */
#define SCU_INTERRUPT_SRSET_PEU0I_Pos         18                                                      /*!< SCU_INTERRUPT SRSET: PEU0I Position     */
#define SCU_INTERRUPT_SRSET_PEU0I_Msk         (0x01UL << SCU_INTERRUPT_SRSET_PEU0I_Pos)               /*!< SCU_INTERRUPT SRSET: PEU0I Mask         */
#define SCU_INTERRUPT_SRSET_FLECC2I_Pos       19                                                      /*!< SCU_INTERRUPT SRSET: FLECC2I Position   */
#define SCU_INTERRUPT_SRSET_FLECC2I_Msk       (0x01UL << SCU_INTERRUPT_SRSET_FLECC2I_Pos)             /*!< SCU_INTERRUPT SRSET: FLECC2I Mask       */
#define SCU_INTERRUPT_SRSET_FLCMPLTI_Pos      20                                                      /*!< SCU_INTERRUPT SRSET: FLCMPLTI Position  */
#define SCU_INTERRUPT_SRSET_FLCMPLTI_Msk      (0x01UL << SCU_INTERRUPT_SRSET_FLCMPLTI_Pos)            /*!< SCU_INTERRUPT SRSET: FLCMPLTI Mask      */
#define SCU_INTERRUPT_SRSET_VCLIPI_Pos        21                                                      /*!< SCU_INTERRUPT SRSET: VCLIPI Position    */
#define SCU_INTERRUPT_SRSET_VCLIPI_Msk        (0x01UL << SCU_INTERRUPT_SRSET_VCLIPI_Pos)              /*!< SCU_INTERRUPT SRSET: VCLIPI Mask        */
#define SCU_INTERRUPT_SRSET_SBYCLKFI_Pos      22                                                      /*!< SCU_INTERRUPT SRSET: SBYCLKFI Position  */
#define SCU_INTERRUPT_SRSET_SBYCLKFI_Msk      (0x01UL << SCU_INTERRUPT_SRSET_SBYCLKFI_Pos)            /*!< SCU_INTERRUPT SRSET: SBYCLKFI Mask      */
#define SCU_INTERRUPT_SRSET_RTC_CTR_Pos       24                                                      /*!< SCU_INTERRUPT SRSET: RTC_CTR Position   */
#define SCU_INTERRUPT_SRSET_RTC_CTR_Msk       (0x01UL << SCU_INTERRUPT_SRSET_RTC_CTR_Pos)             /*!< SCU_INTERRUPT SRSET: RTC_CTR Mask       */
#define SCU_INTERRUPT_SRSET_RTC_ATIM0_Pos     25                                                      /*!< SCU_INTERRUPT SRSET: RTC_ATIM0 Position */
#define SCU_INTERRUPT_SRSET_RTC_ATIM0_Msk     (0x01UL << SCU_INTERRUPT_SRSET_RTC_ATIM0_Pos)           /*!< SCU_INTERRUPT SRSET: RTC_ATIM0 Mask     */
#define SCU_INTERRUPT_SRSET_RTC_ATIM1_Pos     26                                                      /*!< SCU_INTERRUPT SRSET: RTC_ATIM1 Position */
#define SCU_INTERRUPT_SRSET_RTC_ATIM1_Msk     (0x01UL << SCU_INTERRUPT_SRSET_RTC_ATIM1_Pos)           /*!< SCU_INTERRUPT SRSET: RTC_ATIM1 Mask     */
#define SCU_INTERRUPT_SRSET_RTC_TIM0_Pos      27                                                      /*!< SCU_INTERRUPT SRSET: RTC_TIM0 Position  */
#define SCU_INTERRUPT_SRSET_RTC_TIM0_Msk      (0x01UL << SCU_INTERRUPT_SRSET_RTC_TIM0_Pos)            /*!< SCU_INTERRUPT SRSET: RTC_TIM0 Mask      */
#define SCU_INTERRUPT_SRSET_RTC_TIM1_Pos      28                                                      /*!< SCU_INTERRUPT SRSET: RTC_TIM1 Position  */
#define SCU_INTERRUPT_SRSET_RTC_TIM1_Msk      (0x01UL << SCU_INTERRUPT_SRSET_RTC_TIM1_Pos)            /*!< SCU_INTERRUPT SRSET: RTC_TIM1 Mask      */
#define SCU_INTERRUPT_SRSET_TSE_DONE_Pos      29                                                      /*!< SCU_INTERRUPT SRSET: TSE_DONE Position  */
#define SCU_INTERRUPT_SRSET_TSE_DONE_Msk      (0x01UL << SCU_INTERRUPT_SRSET_TSE_DONE_Pos)            /*!< SCU_INTERRUPT SRSET: TSE_DONE Mask      */
#define SCU_INTERRUPT_SRSET_TSE_HIGH_Pos      30                                                      /*!< SCU_INTERRUPT SRSET: TSE_HIGH Position  */
#define SCU_INTERRUPT_SRSET_TSE_HIGH_Msk      (0x01UL << SCU_INTERRUPT_SRSET_TSE_HIGH_Pos)            /*!< SCU_INTERRUPT SRSET: TSE_HIGH Mask      */
#define SCU_INTERRUPT_SRSET_TSE_LOW_Pos       31                                                      /*!< SCU_INTERRUPT SRSET: TSE_LOW Position   */
#define SCU_INTERRUPT_SRSET_TSE_LOW_Msk       (0x01UL << SCU_INTERRUPT_SRSET_TSE_LOW_Pos)             /*!< SCU_INTERRUPT SRSET: TSE_LOW Mask       */


/* ================================================================================ */
/* ================       struct 'SCU_POWER' Position & Mask       ================ */
/* ================================================================================ */


/* -------------------------------  SCU_POWER_VDESR  ------------------------------ */
#define SCU_POWER_VDESR_VCLIP_Pos             0                                                       /*!< SCU_POWER VDESR: VCLIP Position         */
#define SCU_POWER_VDESR_VCLIP_Msk             (0x01UL << SCU_POWER_VDESR_VCLIP_Pos)                   /*!< SCU_POWER VDESR: VCLIP Mask             */
#define SCU_POWER_VDESR_VDDPPW_Pos            1                                                       /*!< SCU_POWER VDESR: VDDPPW Position        */
#define SCU_POWER_VDESR_VDDPPW_Msk            (0x01UL << SCU_POWER_VDESR_VDDPPW_Pos)                  /*!< SCU_POWER VDESR: VDDPPW Mask            */


/* ================================================================================ */
/* ================        struct 'SCU_CLK' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  SCU_CLK_CLKCR  ------------------------------- */
#define SCU_CLK_CLKCR_FDIV_Pos                0                                                       /*!< SCU_CLK CLKCR: FDIV Position            */
#define SCU_CLK_CLKCR_FDIV_Msk                (0x000000ffUL << SCU_CLK_CLKCR_FDIV_Pos)                /*!< SCU_CLK CLKCR: FDIV Mask                */
#define SCU_CLK_CLKCR_IDIV_Pos                8                                                       /*!< SCU_CLK CLKCR: IDIV Position            */
#define SCU_CLK_CLKCR_IDIV_Msk                (0x000000ffUL << SCU_CLK_CLKCR_IDIV_Pos)                /*!< SCU_CLK CLKCR: IDIV Mask                */
#define SCU_CLK_CLKCR_PCLKSEL_Pos             16                                                      /*!< SCU_CLK CLKCR: PCLKSEL Position         */
#define SCU_CLK_CLKCR_PCLKSEL_Msk             (0x01UL << SCU_CLK_CLKCR_PCLKSEL_Pos)                   /*!< SCU_CLK CLKCR: PCLKSEL Mask             */
#define SCU_CLK_CLKCR_RTCCLKSEL_Pos           17                                                      /*!< SCU_CLK CLKCR: RTCCLKSEL Position       */
#define SCU_CLK_CLKCR_RTCCLKSEL_Msk           (0x07UL << SCU_CLK_CLKCR_RTCCLKSEL_Pos)                 /*!< SCU_CLK CLKCR: RTCCLKSEL Mask           */
#define SCU_CLK_CLKCR_CNTADJ_Pos              20                                                      /*!< SCU_CLK CLKCR: CNTADJ Position          */
#define SCU_CLK_CLKCR_CNTADJ_Msk              (0x000003ffUL << SCU_CLK_CLKCR_CNTADJ_Pos)              /*!< SCU_CLK CLKCR: CNTADJ Mask              */
#define SCU_CLK_CLKCR_VDDC2LOW_Pos            30                                                      /*!< SCU_CLK CLKCR: VDDC2LOW Position        */
#define SCU_CLK_CLKCR_VDDC2LOW_Msk            (0x01UL << SCU_CLK_CLKCR_VDDC2LOW_Pos)                  /*!< SCU_CLK CLKCR: VDDC2LOW Mask            */
#define SCU_CLK_CLKCR_VDDC2HIGH_Pos           31                                                      /*!< SCU_CLK CLKCR: VDDC2HIGH Position       */
#define SCU_CLK_CLKCR_VDDC2HIGH_Msk           (0x01UL << SCU_CLK_CLKCR_VDDC2HIGH_Pos)                 /*!< SCU_CLK CLKCR: VDDC2HIGH Mask           */

/* -------------------------------  SCU_CLK_PWRSVCR  ------------------------------ */
#define SCU_CLK_PWRSVCR_FPD_Pos               0                                                       /*!< SCU_CLK PWRSVCR: FPD Position           */
#define SCU_CLK_PWRSVCR_FPD_Msk               (0x01UL << SCU_CLK_PWRSVCR_FPD_Pos)                     /*!< SCU_CLK PWRSVCR: FPD Mask               */

/* ------------------------------  SCU_CLK_CGATSTAT0  ----------------------------- */
#define SCU_CLK_CGATSTAT0_VADC_Pos            0                                                       /*!< SCU_CLK CGATSTAT0: VADC Position        */
#define SCU_CLK_CGATSTAT0_VADC_Msk            (0x01UL << SCU_CLK_CGATSTAT0_VADC_Pos)                  /*!< SCU_CLK CGATSTAT0: VADC Mask            */
#define SCU_CLK_CGATSTAT0_CCU40_Pos           2                                                       /*!< SCU_CLK CGATSTAT0: CCU40 Position       */
#define SCU_CLK_CGATSTAT0_CCU40_Msk           (0x01UL << SCU_CLK_CGATSTAT0_CCU40_Pos)                 /*!< SCU_CLK CGATSTAT0: CCU40 Mask           */
#define SCU_CLK_CGATSTAT0_USIC0_Pos           3                                                       /*!< SCU_CLK CGATSTAT0: USIC0 Position       */
#define SCU_CLK_CGATSTAT0_USIC0_Msk           (0x01UL << SCU_CLK_CGATSTAT0_USIC0_Pos)                 /*!< SCU_CLK CGATSTAT0: USIC0 Mask           */
#define SCU_CLK_CGATSTAT0_WDT_Pos             9                                                       /*!< SCU_CLK CGATSTAT0: WDT Position         */
#define SCU_CLK_CGATSTAT0_WDT_Msk             (0x01UL << SCU_CLK_CGATSTAT0_WDT_Pos)                   /*!< SCU_CLK CGATSTAT0: WDT Mask             */
#define SCU_CLK_CGATSTAT0_RTC_Pos             10                                                      /*!< SCU_CLK CGATSTAT0: RTC Position         */
#define SCU_CLK_CGATSTAT0_RTC_Msk             (0x01UL << SCU_CLK_CGATSTAT0_RTC_Pos)                   /*!< SCU_CLK CGATSTAT0: RTC Mask             */

/* ------------------------------  SCU_CLK_CGATSET0  ------------------------------ */
#define SCU_CLK_CGATSET0_VADC_Pos             0                                                       /*!< SCU_CLK CGATSET0: VADC Position         */
#define SCU_CLK_CGATSET0_VADC_Msk             (0x01UL << SCU_CLK_CGATSET0_VADC_Pos)                   /*!< SCU_CLK CGATSET0: VADC Mask             */
#define SCU_CLK_CGATSET0_CCU40_Pos            2                                                       /*!< SCU_CLK CGATSET0: CCU40 Position        */
#define SCU_CLK_CGATSET0_CCU40_Msk            (0x01UL << SCU_CLK_CGATSET0_CCU40_Pos)                  /*!< SCU_CLK CGATSET0: CCU40 Mask            */
#define SCU_CLK_CGATSET0_USIC0_Pos            3                                                       /*!< SCU_CLK CGATSET0: USIC0 Position        */
#define SCU_CLK_CGATSET0_USIC0_Msk            (0x01UL << SCU_CLK_CGATSET0_USIC0_Pos)                  /*!< SCU_CLK CGATSET0: USIC0 Mask            */
#define SCU_CLK_CGATSET0_WDT_Pos              9                                                       /*!< SCU_CLK CGATSET0: WDT Position          */
#define SCU_CLK_CGATSET0_WDT_Msk              (0x01UL << SCU_CLK_CGATSET0_WDT_Pos)                    /*!< SCU_CLK CGATSET0: WDT Mask              */
#define SCU_CLK_CGATSET0_RTC_Pos              10                                                      /*!< SCU_CLK CGATSET0: RTC Position          */
#define SCU_CLK_CGATSET0_RTC_Msk              (0x01UL << SCU_CLK_CGATSET0_RTC_Pos)                    /*!< SCU_CLK CGATSET0: RTC Mask              */

/* ------------------------------  SCU_CLK_CGATCLR0  ------------------------------ */
#define SCU_CLK_CGATCLR0_VADC_Pos             0                                                       /*!< SCU_CLK CGATCLR0: VADC Position         */
#define SCU_CLK_CGATCLR0_VADC_Msk             (0x01UL << SCU_CLK_CGATCLR0_VADC_Pos)                   /*!< SCU_CLK CGATCLR0: VADC Mask             */
#define SCU_CLK_CGATCLR0_CCU40_Pos            2                                                       /*!< SCU_CLK CGATCLR0: CCU40 Position        */
#define SCU_CLK_CGATCLR0_CCU40_Msk            (0x01UL << SCU_CLK_CGATCLR0_CCU40_Pos)                  /*!< SCU_CLK CGATCLR0: CCU40 Mask            */
#define SCU_CLK_CGATCLR0_USIC0_Pos            3                                                       /*!< SCU_CLK CGATCLR0: USIC0 Position        */
#define SCU_CLK_CGATCLR0_USIC0_Msk            (0x01UL << SCU_CLK_CGATCLR0_USIC0_Pos)                  /*!< SCU_CLK CGATCLR0: USIC0 Mask            */
#define SCU_CLK_CGATCLR0_WDT_Pos              9                                                       /*!< SCU_CLK CGATCLR0: WDT Position          */
#define SCU_CLK_CGATCLR0_WDT_Msk              (0x01UL << SCU_CLK_CGATCLR0_WDT_Pos)                    /*!< SCU_CLK CGATCLR0: WDT Mask              */
#define SCU_CLK_CGATCLR0_RTC_Pos              10                                                      /*!< SCU_CLK CGATCLR0: RTC Position          */
#define SCU_CLK_CGATCLR0_RTC_Msk              (0x01UL << SCU_CLK_CGATCLR0_RTC_Pos)                    /*!< SCU_CLK CGATCLR0: RTC Mask              */

/* -------------------------------  SCU_CLK_OSCCSR  ------------------------------- */
#define SCU_CLK_OSCCSR_OSC2L_Pos              0                                                       /*!< SCU_CLK OSCCSR: OSC2L Position          */
#define SCU_CLK_OSCCSR_OSC2L_Msk              (0x01UL << SCU_CLK_OSCCSR_OSC2L_Pos)                    /*!< SCU_CLK OSCCSR: OSC2L Mask              */
#define SCU_CLK_OSCCSR_OSC2H_Pos              1                                                       /*!< SCU_CLK OSCCSR: OSC2H Position          */
#define SCU_CLK_OSCCSR_OSC2H_Msk              (0x01UL << SCU_CLK_OSCCSR_OSC2H_Pos)                    /*!< SCU_CLK OSCCSR: OSC2H Mask              */
#define SCU_CLK_OSCCSR_OWDRES_Pos             16                                                      /*!< SCU_CLK OSCCSR: OWDRES Position         */
#define SCU_CLK_OSCCSR_OWDRES_Msk             (0x01UL << SCU_CLK_OSCCSR_OWDRES_Pos)                   /*!< SCU_CLK OSCCSR: OWDRES Mask             */
#define SCU_CLK_OSCCSR_OWDEN_Pos              17                                                      /*!< SCU_CLK OSCCSR: OWDEN Position          */
#define SCU_CLK_OSCCSR_OWDEN_Msk              (0x01UL << SCU_CLK_OSCCSR_OWDEN_Pos)                    /*!< SCU_CLK OSCCSR: OWDEN Mask              */


/* ================================================================================ */
/* ================       struct 'SCU_RESET' Position & Mask       ================ */
/* ================================================================================ */


/* ------------------------------  SCU_RESET_RSTSTAT  ----------------------------- */
#define SCU_RESET_RSTSTAT_RSTSTAT_Pos         0                                                       /*!< SCU_RESET RSTSTAT: RSTSTAT Position     */
#define SCU_RESET_RSTSTAT_RSTSTAT_Msk         (0x000003ffUL << SCU_RESET_RSTSTAT_RSTSTAT_Pos)         /*!< SCU_RESET RSTSTAT: RSTSTAT Mask         */
#define SCU_RESET_RSTSTAT_LCKEN_Pos           10                                                      /*!< SCU_RESET RSTSTAT: LCKEN Position       */
#define SCU_RESET_RSTSTAT_LCKEN_Msk           (0x01UL << SCU_RESET_RSTSTAT_LCKEN_Pos)                 /*!< SCU_RESET RSTSTAT: LCKEN Mask           */

/* ------------------------------  SCU_RESET_RSTSET  ------------------------------ */
#define SCU_RESET_RSTSET_LCKEN_Pos            10                                                      /*!< SCU_RESET RSTSET: LCKEN Position        */
#define SCU_RESET_RSTSET_LCKEN_Msk            (0x01UL << SCU_RESET_RSTSET_LCKEN_Pos)                  /*!< SCU_RESET RSTSET: LCKEN Mask            */

/* ------------------------------  SCU_RESET_RSTCLR  ------------------------------ */
#define SCU_RESET_RSTCLR_RSCLR_Pos            0                                                       /*!< SCU_RESET RSTCLR: RSCLR Position        */
#define SCU_RESET_RSTCLR_RSCLR_Msk            (0x01UL << SCU_RESET_RSTCLR_RSCLR_Pos)                  /*!< SCU_RESET RSTCLR: RSCLR Mask            */
#define SCU_RESET_RSTCLR_LCKEN_Pos            10                                                      /*!< SCU_RESET RSTCLR: LCKEN Position        */
#define SCU_RESET_RSTCLR_LCKEN_Msk            (0x01UL << SCU_RESET_RSTCLR_LCKEN_Pos)                  /*!< SCU_RESET RSTCLR: LCKEN Mask            */

/* ------------------------------  SCU_RESET_RSTCON  ------------------------------ */
#define SCU_RESET_RSTCON_ECCRSTEN_Pos         0                                                       /*!< SCU_RESET RSTCON: ECCRSTEN Position     */
#define SCU_RESET_RSTCON_ECCRSTEN_Msk         (0x01UL << SCU_RESET_RSTCON_ECCRSTEN_Pos)               /*!< SCU_RESET RSTCON: ECCRSTEN Mask         */
#define SCU_RESET_RSTCON_LOCRSTEN_Pos         1                                                       /*!< SCU_RESET RSTCON: LOCRSTEN Position     */
#define SCU_RESET_RSTCON_LOCRSTEN_Msk         (0x01UL << SCU_RESET_RSTCON_LOCRSTEN_Pos)               /*!< SCU_RESET RSTCON: LOCRSTEN Mask         */
#define SCU_RESET_RSTCON_SPERSTEN_Pos         2                                                       /*!< SCU_RESET RSTCON: SPERSTEN Position     */
#define SCU_RESET_RSTCON_SPERSTEN_Msk         (0x01UL << SCU_RESET_RSTCON_SPERSTEN_Pos)               /*!< SCU_RESET RSTCON: SPERSTEN Mask         */
#define SCU_RESET_RSTCON_U0PERSTEN_Pos        3                                                       /*!< SCU_RESET RSTCON: U0PERSTEN Position    */
#define SCU_RESET_RSTCON_U0PERSTEN_Msk        (0x01UL << SCU_RESET_RSTCON_U0PERSTEN_Pos)              /*!< SCU_RESET RSTCON: U0PERSTEN Mask        */
#define SCU_RESET_RSTCON_MRSTEN_Pos           16                                                      /*!< SCU_RESET RSTCON: MRSTEN Position       */
#define SCU_RESET_RSTCON_MRSTEN_Msk           (0x01UL << SCU_RESET_RSTCON_MRSTEN_Pos)                 /*!< SCU_RESET RSTCON: MRSTEN Mask           */


/* ================================================================================ */
/* ================       struct 'SCU_ANALOG' Position & Mask      ================ */
/* ================================================================================ */


/* -----------------------------  SCU_ANALOG_ANAVDEL  ----------------------------- */
#define SCU_ANALOG_ANAVDEL_VDEL_SELECT_Pos    0                                                       /*!< SCU_ANALOG ANAVDEL: VDEL_SELECT Position */
#define SCU_ANALOG_ANAVDEL_VDEL_SELECT_Msk    (0x03UL << SCU_ANALOG_ANAVDEL_VDEL_SELECT_Pos)          /*!< SCU_ANALOG ANAVDEL: VDEL_SELECT Mask    */
#define SCU_ANALOG_ANAVDEL_VDEL_TIM_ADJ_Pos   2                                                       /*!< SCU_ANALOG ANAVDEL: VDEL_TIM_ADJ Position */
#define SCU_ANALOG_ANAVDEL_VDEL_TIM_ADJ_Msk   (0x03UL << SCU_ANALOG_ANAVDEL_VDEL_TIM_ADJ_Pos)         /*!< SCU_ANALOG ANAVDEL: VDEL_TIM_ADJ Mask   */
#define SCU_ANALOG_ANAVDEL_VDEL_EN_Pos        4                                                       /*!< SCU_ANALOG ANAVDEL: VDEL_EN Position    */
#define SCU_ANALOG_ANAVDEL_VDEL_EN_Msk        (0x01UL << SCU_ANALOG_ANAVDEL_VDEL_EN_Pos)              /*!< SCU_ANALOG ANAVDEL: VDEL_EN Mask        */


/* ================================================================================ */
/* ================          Group 'CCU4' Position & Mask          ================ */
/* ================================================================================ */


/* ---------------------------------  CCU4_GCTRL  --------------------------------- */
#define CCU4_GCTRL_PRBC_Pos                   0                                                       /*!< CCU4 GCTRL: PRBC Position               */
#define CCU4_GCTRL_PRBC_Msk                   (0x07UL << CCU4_GCTRL_PRBC_Pos)                         /*!< CCU4 GCTRL: PRBC Mask                   */
#define CCU4_GCTRL_PCIS_Pos                   4                                                       /*!< CCU4 GCTRL: PCIS Position               */
#define CCU4_GCTRL_PCIS_Msk                   (0x03UL << CCU4_GCTRL_PCIS_Pos)                         /*!< CCU4 GCTRL: PCIS Mask                   */
#define CCU4_GCTRL_SUSCFG_Pos                 8                                                       /*!< CCU4 GCTRL: SUSCFG Position             */
#define CCU4_GCTRL_SUSCFG_Msk                 (0x03UL << CCU4_GCTRL_SUSCFG_Pos)                       /*!< CCU4 GCTRL: SUSCFG Mask                 */
#define CCU4_GCTRL_MSE0_Pos                   10                                                      /*!< CCU4 GCTRL: MSE0 Position               */
#define CCU4_GCTRL_MSE0_Msk                   (0x01UL << CCU4_GCTRL_MSE0_Pos)                         /*!< CCU4 GCTRL: MSE0 Mask                   */
#define CCU4_GCTRL_MSE1_Pos                   11                                                      /*!< CCU4 GCTRL: MSE1 Position               */
#define CCU4_GCTRL_MSE1_Msk                   (0x01UL << CCU4_GCTRL_MSE1_Pos)                         /*!< CCU4 GCTRL: MSE1 Mask                   */
#define CCU4_GCTRL_MSE2_Pos                   12                                                      /*!< CCU4 GCTRL: MSE2 Position               */
#define CCU4_GCTRL_MSE2_Msk                   (0x01UL << CCU4_GCTRL_MSE2_Pos)                         /*!< CCU4 GCTRL: MSE2 Mask                   */
#define CCU4_GCTRL_MSE3_Pos                   13                                                      /*!< CCU4 GCTRL: MSE3 Position               */
#define CCU4_GCTRL_MSE3_Msk                   (0x01UL << CCU4_GCTRL_MSE3_Pos)                         /*!< CCU4 GCTRL: MSE3 Mask                   */
#define CCU4_GCTRL_MSDE_Pos                   14                                                      /*!< CCU4 GCTRL: MSDE Position               */
#define CCU4_GCTRL_MSDE_Msk                   (0x03UL << CCU4_GCTRL_MSDE_Pos)                         /*!< CCU4 GCTRL: MSDE Mask                   */

/* ---------------------------------  CCU4_GSTAT  --------------------------------- */
#define CCU4_GSTAT_S0I_Pos                    0                                                       /*!< CCU4 GSTAT: S0I Position                */
#define CCU4_GSTAT_S0I_Msk                    (0x01UL << CCU4_GSTAT_S0I_Pos)                          /*!< CCU4 GSTAT: S0I Mask                    */
#define CCU4_GSTAT_S1I_Pos                    1                                                       /*!< CCU4 GSTAT: S1I Position                */
#define CCU4_GSTAT_S1I_Msk                    (0x01UL << CCU4_GSTAT_S1I_Pos)                          /*!< CCU4 GSTAT: S1I Mask                    */
#define CCU4_GSTAT_S2I_Pos                    2                                                       /*!< CCU4 GSTAT: S2I Position                */
#define CCU4_GSTAT_S2I_Msk                    (0x01UL << CCU4_GSTAT_S2I_Pos)                          /*!< CCU4 GSTAT: S2I Mask                    */
#define CCU4_GSTAT_S3I_Pos                    3                                                       /*!< CCU4 GSTAT: S3I Position                */
#define CCU4_GSTAT_S3I_Msk                    (0x01UL << CCU4_GSTAT_S3I_Pos)                          /*!< CCU4 GSTAT: S3I Mask                    */
#define CCU4_GSTAT_PRB_Pos                    8                                                       /*!< CCU4 GSTAT: PRB Position                */
#define CCU4_GSTAT_PRB_Msk                    (0x01UL << CCU4_GSTAT_PRB_Pos)                          /*!< CCU4 GSTAT: PRB Mask                    */

/* ---------------------------------  CCU4_GIDLS  --------------------------------- */
#define CCU4_GIDLS_SS0I_Pos                   0                                                       /*!< CCU4 GIDLS: SS0I Position               */
#define CCU4_GIDLS_SS0I_Msk                   (0x01UL << CCU4_GIDLS_SS0I_Pos)                         /*!< CCU4 GIDLS: SS0I Mask                   */
#define CCU4_GIDLS_SS1I_Pos                   1                                                       /*!< CCU4 GIDLS: SS1I Position               */
#define CCU4_GIDLS_SS1I_Msk                   (0x01UL << CCU4_GIDLS_SS1I_Pos)                         /*!< CCU4 GIDLS: SS1I Mask                   */
#define CCU4_GIDLS_SS2I_Pos                   2                                                       /*!< CCU4 GIDLS: SS2I Position               */
#define CCU4_GIDLS_SS2I_Msk                   (0x01UL << CCU4_GIDLS_SS2I_Pos)                         /*!< CCU4 GIDLS: SS2I Mask                   */
#define CCU4_GIDLS_SS3I_Pos                   3                                                       /*!< CCU4 GIDLS: SS3I Position               */
#define CCU4_GIDLS_SS3I_Msk                   (0x01UL << CCU4_GIDLS_SS3I_Pos)                         /*!< CCU4 GIDLS: SS3I Mask                   */
#define CCU4_GIDLS_CPRB_Pos                   8                                                       /*!< CCU4 GIDLS: CPRB Position               */
#define CCU4_GIDLS_CPRB_Msk                   (0x01UL << CCU4_GIDLS_CPRB_Pos)                         /*!< CCU4 GIDLS: CPRB Mask                   */
#define CCU4_GIDLS_PSIC_Pos                   9                                                       /*!< CCU4 GIDLS: PSIC Position               */
#define CCU4_GIDLS_PSIC_Msk                   (0x01UL << CCU4_GIDLS_PSIC_Pos)                         /*!< CCU4 GIDLS: PSIC Mask                   */

/* ---------------------------------  CCU4_GIDLC  --------------------------------- */
#define CCU4_GIDLC_CS0I_Pos                   0                                                       /*!< CCU4 GIDLC: CS0I Position               */
#define CCU4_GIDLC_CS0I_Msk                   (0x01UL << CCU4_GIDLC_CS0I_Pos)                         /*!< CCU4 GIDLC: CS0I Mask                   */
#define CCU4_GIDLC_CS1I_Pos                   1                                                       /*!< CCU4 GIDLC: CS1I Position               */
#define CCU4_GIDLC_CS1I_Msk                   (0x01UL << CCU4_GIDLC_CS1I_Pos)                         /*!< CCU4 GIDLC: CS1I Mask                   */
#define CCU4_GIDLC_CS2I_Pos                   2                                                       /*!< CCU4 GIDLC: CS2I Position               */
#define CCU4_GIDLC_CS2I_Msk                   (0x01UL << CCU4_GIDLC_CS2I_Pos)                         /*!< CCU4 GIDLC: CS2I Mask                   */
#define CCU4_GIDLC_CS3I_Pos                   3                                                       /*!< CCU4 GIDLC: CS3I Position               */
#define CCU4_GIDLC_CS3I_Msk                   (0x01UL << CCU4_GIDLC_CS3I_Pos)                         /*!< CCU4 GIDLC: CS3I Mask                   */
#define CCU4_GIDLC_SPRB_Pos                   8                                                       /*!< CCU4 GIDLC: SPRB Position               */
#define CCU4_GIDLC_SPRB_Msk                   (0x01UL << CCU4_GIDLC_SPRB_Pos)                         /*!< CCU4 GIDLC: SPRB Mask                   */

/* ----------------------------------  CCU4_GCSS  --------------------------------- */
#define CCU4_GCSS_S0SE_Pos                    0                                                       /*!< CCU4 GCSS: S0SE Position                */
#define CCU4_GCSS_S0SE_Msk                    (0x01UL << CCU4_GCSS_S0SE_Pos)                          /*!< CCU4 GCSS: S0SE Mask                    */
#define CCU4_GCSS_S0DSE_Pos                   1                                                       /*!< CCU4 GCSS: S0DSE Position               */
#define CCU4_GCSS_S0DSE_Msk                   (0x01UL << CCU4_GCSS_S0DSE_Pos)                         /*!< CCU4 GCSS: S0DSE Mask                   */
#define CCU4_GCSS_S0PSE_Pos                   2                                                       /*!< CCU4 GCSS: S0PSE Position               */
#define CCU4_GCSS_S0PSE_Msk                   (0x01UL << CCU4_GCSS_S0PSE_Pos)                         /*!< CCU4 GCSS: S0PSE Mask                   */
#define CCU4_GCSS_S1SE_Pos                    4                                                       /*!< CCU4 GCSS: S1SE Position                */
#define CCU4_GCSS_S1SE_Msk                    (0x01UL << CCU4_GCSS_S1SE_Pos)                          /*!< CCU4 GCSS: S1SE Mask                    */
#define CCU4_GCSS_S1DSE_Pos                   5                                                       /*!< CCU4 GCSS: S1DSE Position               */
#define CCU4_GCSS_S1DSE_Msk                   (0x01UL << CCU4_GCSS_S1DSE_Pos)                         /*!< CCU4 GCSS: S1DSE Mask                   */
#define CCU4_GCSS_S1PSE_Pos                   6                                                       /*!< CCU4 GCSS: S1PSE Position               */
#define CCU4_GCSS_S1PSE_Msk                   (0x01UL << CCU4_GCSS_S1PSE_Pos)                         /*!< CCU4 GCSS: S1PSE Mask                   */
#define CCU4_GCSS_S2SE_Pos                    8                                                       /*!< CCU4 GCSS: S2SE Position                */
#define CCU4_GCSS_S2SE_Msk                    (0x01UL << CCU4_GCSS_S2SE_Pos)                          /*!< CCU4 GCSS: S2SE Mask                    */
#define CCU4_GCSS_S2DSE_Pos                   9                                                       /*!< CCU4 GCSS: S2DSE Position               */
#define CCU4_GCSS_S2DSE_Msk                   (0x01UL << CCU4_GCSS_S2DSE_Pos)                         /*!< CCU4 GCSS: S2DSE Mask                   */
#define CCU4_GCSS_S2PSE_Pos                   10                                                      /*!< CCU4 GCSS: S2PSE Position               */
#define CCU4_GCSS_S2PSE_Msk                   (0x01UL << CCU4_GCSS_S2PSE_Pos)                         /*!< CCU4 GCSS: S2PSE Mask                   */
#define CCU4_GCSS_S3SE_Pos                    12                                                      /*!< CCU4 GCSS: S3SE Position                */
#define CCU4_GCSS_S3SE_Msk                    (0x01UL << CCU4_GCSS_S3SE_Pos)                          /*!< CCU4 GCSS: S3SE Mask                    */
#define CCU4_GCSS_S3DSE_Pos                   13                                                      /*!< CCU4 GCSS: S3DSE Position               */
#define CCU4_GCSS_S3DSE_Msk                   (0x01UL << CCU4_GCSS_S3DSE_Pos)                         /*!< CCU4 GCSS: S3DSE Mask                   */
#define CCU4_GCSS_S3PSE_Pos                   14                                                      /*!< CCU4 GCSS: S3PSE Position               */
#define CCU4_GCSS_S3PSE_Msk                   (0x01UL << CCU4_GCSS_S3PSE_Pos)                         /*!< CCU4 GCSS: S3PSE Mask                   */
#define CCU4_GCSS_S0STS_Pos                   16                                                      /*!< CCU4 GCSS: S0STS Position               */
#define CCU4_GCSS_S0STS_Msk                   (0x01UL << CCU4_GCSS_S0STS_Pos)                         /*!< CCU4 GCSS: S0STS Mask                   */
#define CCU4_GCSS_S1STS_Pos                   17                                                      /*!< CCU4 GCSS: S1STS Position               */
#define CCU4_GCSS_S1STS_Msk                   (0x01UL << CCU4_GCSS_S1STS_Pos)                         /*!< CCU4 GCSS: S1STS Mask                   */
#define CCU4_GCSS_S2STS_Pos                   18                                                      /*!< CCU4 GCSS: S2STS Position               */
#define CCU4_GCSS_S2STS_Msk                   (0x01UL << CCU4_GCSS_S2STS_Pos)                         /*!< CCU4 GCSS: S2STS Mask                   */
#define CCU4_GCSS_S3STS_Pos                   19                                                      /*!< CCU4 GCSS: S3STS Position               */
#define CCU4_GCSS_S3STS_Msk                   (0x01UL << CCU4_GCSS_S3STS_Pos)                         /*!< CCU4 GCSS: S3STS Mask                   */

/* ----------------------------------  CCU4_GCSC  --------------------------------- */
#define CCU4_GCSC_S0SC_Pos                    0                                                       /*!< CCU4 GCSC: S0SC Position                */
#define CCU4_GCSC_S0SC_Msk                    (0x01UL << CCU4_GCSC_S0SC_Pos)                          /*!< CCU4 GCSC: S0SC Mask                    */
#define CCU4_GCSC_S0DSC_Pos                   1                                                       /*!< CCU4 GCSC: S0DSC Position               */
#define CCU4_GCSC_S0DSC_Msk                   (0x01UL << CCU4_GCSC_S0DSC_Pos)                         /*!< CCU4 GCSC: S0DSC Mask                   */
#define CCU4_GCSC_S0PSC_Pos                   2                                                       /*!< CCU4 GCSC: S0PSC Position               */
#define CCU4_GCSC_S0PSC_Msk                   (0x01UL << CCU4_GCSC_S0PSC_Pos)                         /*!< CCU4 GCSC: S0PSC Mask                   */
#define CCU4_GCSC_S1SC_Pos                    4                                                       /*!< CCU4 GCSC: S1SC Position                */
#define CCU4_GCSC_S1SC_Msk                    (0x01UL << CCU4_GCSC_S1SC_Pos)                          /*!< CCU4 GCSC: S1SC Mask                    */
#define CCU4_GCSC_S1DSC_Pos                   5                                                       /*!< CCU4 GCSC: S1DSC Position               */
#define CCU4_GCSC_S1DSC_Msk                   (0x01UL << CCU4_GCSC_S1DSC_Pos)                         /*!< CCU4 GCSC: S1DSC Mask                   */
#define CCU4_GCSC_S1PSC_Pos                   6                                                       /*!< CCU4 GCSC: S1PSC Position               */
#define CCU4_GCSC_S1PSC_Msk                   (0x01UL << CCU4_GCSC_S1PSC_Pos)                         /*!< CCU4 GCSC: S1PSC Mask                   */
#define CCU4_GCSC_S2SC_Pos                    8                                                       /*!< CCU4 GCSC: S2SC Position                */
#define CCU4_GCSC_S2SC_Msk                    (0x01UL << CCU4_GCSC_S2SC_Pos)                          /*!< CCU4 GCSC: S2SC Mask                    */
#define CCU4_GCSC_S2DSC_Pos                   9                                                       /*!< CCU4 GCSC: S2DSC Position               */
#define CCU4_GCSC_S2DSC_Msk                   (0x01UL << CCU4_GCSC_S2DSC_Pos)                         /*!< CCU4 GCSC: S2DSC Mask                   */
#define CCU4_GCSC_S2PSC_Pos                   10                                                      /*!< CCU4 GCSC: S2PSC Position               */
#define CCU4_GCSC_S2PSC_Msk                   (0x01UL << CCU4_GCSC_S2PSC_Pos)                         /*!< CCU4 GCSC: S2PSC Mask                   */
#define CCU4_GCSC_S3SC_Pos                    12                                                      /*!< CCU4 GCSC: S3SC Position                */
#define CCU4_GCSC_S3SC_Msk                    (0x01UL << CCU4_GCSC_S3SC_Pos)                          /*!< CCU4 GCSC: S3SC Mask                    */
#define CCU4_GCSC_S3DSC_Pos                   13                                                      /*!< CCU4 GCSC: S3DSC Position               */
#define CCU4_GCSC_S3DSC_Msk                   (0x01UL << CCU4_GCSC_S3DSC_Pos)                         /*!< CCU4 GCSC: S3DSC Mask                   */
#define CCU4_GCSC_S3PSC_Pos                   14                                                      /*!< CCU4 GCSC: S3PSC Position               */
#define CCU4_GCSC_S3PSC_Msk                   (0x01UL << CCU4_GCSC_S3PSC_Pos)                         /*!< CCU4 GCSC: S3PSC Mask                   */
#define CCU4_GCSC_S0STC_Pos                   16                                                      /*!< CCU4 GCSC: S0STC Position               */
#define CCU4_GCSC_S0STC_Msk                   (0x01UL << CCU4_GCSC_S0STC_Pos)                         /*!< CCU4 GCSC: S0STC Mask                   */
#define CCU4_GCSC_S1STC_Pos                   17                                                      /*!< CCU4 GCSC: S1STC Position               */
#define CCU4_GCSC_S1STC_Msk                   (0x01UL << CCU4_GCSC_S1STC_Pos)                         /*!< CCU4 GCSC: S1STC Mask                   */
#define CCU4_GCSC_S2STC_Pos                   18                                                      /*!< CCU4 GCSC: S2STC Position               */
#define CCU4_GCSC_S2STC_Msk                   (0x01UL << CCU4_GCSC_S2STC_Pos)                         /*!< CCU4 GCSC: S2STC Mask                   */
#define CCU4_GCSC_S3STC_Pos                   19                                                      /*!< CCU4 GCSC: S3STC Position               */
#define CCU4_GCSC_S3STC_Msk                   (0x01UL << CCU4_GCSC_S3STC_Pos)                         /*!< CCU4 GCSC: S3STC Mask                   */

/* ----------------------------------  CCU4_GCST  --------------------------------- */
#define CCU4_GCST_S0SS_Pos                    0                                                       /*!< CCU4 GCST: S0SS Position                */
#define CCU4_GCST_S0SS_Msk                    (0x01UL << CCU4_GCST_S0SS_Pos)                          /*!< CCU4 GCST: S0SS Mask                    */
#define CCU4_GCST_S0DSS_Pos                   1                                                       /*!< CCU4 GCST: S0DSS Position               */
#define CCU4_GCST_S0DSS_Msk                   (0x01UL << CCU4_GCST_S0DSS_Pos)                         /*!< CCU4 GCST: S0DSS Mask                   */
#define CCU4_GCST_S0PSS_Pos                   2                                                       /*!< CCU4 GCST: S0PSS Position               */
#define CCU4_GCST_S0PSS_Msk                   (0x01UL << CCU4_GCST_S0PSS_Pos)                         /*!< CCU4 GCST: S0PSS Mask                   */
#define CCU4_GCST_S1SS_Pos                    4                                                       /*!< CCU4 GCST: S1SS Position                */
#define CCU4_GCST_S1SS_Msk                    (0x01UL << CCU4_GCST_S1SS_Pos)                          /*!< CCU4 GCST: S1SS Mask                    */
#define CCU4_GCST_S1DSS_Pos                   5                                                       /*!< CCU4 GCST: S1DSS Position               */
#define CCU4_GCST_S1DSS_Msk                   (0x01UL << CCU4_GCST_S1DSS_Pos)                         /*!< CCU4 GCST: S1DSS Mask                   */
#define CCU4_GCST_S1PSS_Pos                   6                                                       /*!< CCU4 GCST: S1PSS Position               */
#define CCU4_GCST_S1PSS_Msk                   (0x01UL << CCU4_GCST_S1PSS_Pos)                         /*!< CCU4 GCST: S1PSS Mask                   */
#define CCU4_GCST_S2SS_Pos                    8                                                       /*!< CCU4 GCST: S2SS Position                */
#define CCU4_GCST_S2SS_Msk                    (0x01UL << CCU4_GCST_S2SS_Pos)                          /*!< CCU4 GCST: S2SS Mask                    */
#define CCU4_GCST_S2DSS_Pos                   9                                                       /*!< CCU4 GCST: S2DSS Position               */
#define CCU4_GCST_S2DSS_Msk                   (0x01UL << CCU4_GCST_S2DSS_Pos)                         /*!< CCU4 GCST: S2DSS Mask                   */
#define CCU4_GCST_S2PSS_Pos                   10                                                      /*!< CCU4 GCST: S2PSS Position               */
#define CCU4_GCST_S2PSS_Msk                   (0x01UL << CCU4_GCST_S2PSS_Pos)                         /*!< CCU4 GCST: S2PSS Mask                   */
#define CCU4_GCST_S3SS_Pos                    12                                                      /*!< CCU4 GCST: S3SS Position                */
#define CCU4_GCST_S3SS_Msk                    (0x01UL << CCU4_GCST_S3SS_Pos)                          /*!< CCU4 GCST: S3SS Mask                    */
#define CCU4_GCST_S3DSS_Pos                   13                                                      /*!< CCU4 GCST: S3DSS Position               */
#define CCU4_GCST_S3DSS_Msk                   (0x01UL << CCU4_GCST_S3DSS_Pos)                         /*!< CCU4 GCST: S3DSS Mask                   */
#define CCU4_GCST_S3PSS_Pos                   14                                                      /*!< CCU4 GCST: S3PSS Position               */
#define CCU4_GCST_S3PSS_Msk                   (0x01UL << CCU4_GCST_S3PSS_Pos)                         /*!< CCU4 GCST: S3PSS Mask                   */
#define CCU4_GCST_CC40ST_Pos                  16                                                      /*!< CCU4 GCST: CC40ST Position              */
#define CCU4_GCST_CC40ST_Msk                  (0x01UL << CCU4_GCST_CC40ST_Pos)                        /*!< CCU4 GCST: CC40ST Mask                  */
#define CCU4_GCST_CC41ST_Pos                  17                                                      /*!< CCU4 GCST: CC41ST Position              */
#define CCU4_GCST_CC41ST_Msk                  (0x01UL << CCU4_GCST_CC41ST_Pos)                        /*!< CCU4 GCST: CC41ST Mask                  */
#define CCU4_GCST_CC42ST_Pos                  18                                                      /*!< CCU4 GCST: CC42ST Position              */
#define CCU4_GCST_CC42ST_Msk                  (0x01UL << CCU4_GCST_CC42ST_Pos)                        /*!< CCU4 GCST: CC42ST Mask                  */
#define CCU4_GCST_CC43ST_Pos                  19                                                      /*!< CCU4 GCST: CC43ST Position              */
#define CCU4_GCST_CC43ST_Msk                  (0x01UL << CCU4_GCST_CC43ST_Pos)                        /*!< CCU4 GCST: CC43ST Mask                  */

/* ----------------------------------  CCU4_MIDR  --------------------------------- */
#define CCU4_MIDR_MODR_Pos                    0                                                       /*!< CCU4 MIDR: MODR Position                */
#define CCU4_MIDR_MODR_Msk                    (0x000000ffUL << CCU4_MIDR_MODR_Pos)                    /*!< CCU4 MIDR: MODR Mask                    */
#define CCU4_MIDR_MODT_Pos                    8                                                       /*!< CCU4 MIDR: MODT Position                */
#define CCU4_MIDR_MODT_Msk                    (0x000000ffUL << CCU4_MIDR_MODT_Pos)                    /*!< CCU4 MIDR: MODT Mask                    */
#define CCU4_MIDR_MODN_Pos                    16                                                      /*!< CCU4 MIDR: MODN Position                */
#define CCU4_MIDR_MODN_Msk                    (0x0000ffffUL << CCU4_MIDR_MODN_Pos)                    /*!< CCU4 MIDR: MODN Mask                    */


/* ================================================================================ */
/* ================        Group 'CCU4_CC4' Position & Mask        ================ */
/* ================================================================================ */


/* --------------------------------  CCU4_CC4_INS  -------------------------------- */
#define CCU4_CC4_INS_EV0IS_Pos                0                                                       /*!< CCU4_CC4 INS: EV0IS Position            */
#define CCU4_CC4_INS_EV0IS_Msk                (0x0fUL << CCU4_CC4_INS_EV0IS_Pos)                      /*!< CCU4_CC4 INS: EV0IS Mask                */
#define CCU4_CC4_INS_EV1IS_Pos                4                                                       /*!< CCU4_CC4 INS: EV1IS Position            */
#define CCU4_CC4_INS_EV1IS_Msk                (0x0fUL << CCU4_CC4_INS_EV1IS_Pos)                      /*!< CCU4_CC4 INS: EV1IS Mask                */
#define CCU4_CC4_INS_EV2IS_Pos                8                                                       /*!< CCU4_CC4 INS: EV2IS Position            */
#define CCU4_CC4_INS_EV2IS_Msk                (0x0fUL << CCU4_CC4_INS_EV2IS_Pos)                      /*!< CCU4_CC4 INS: EV2IS Mask                */
#define CCU4_CC4_INS_EV0EM_Pos                16                                                      /*!< CCU4_CC4 INS: EV0EM Position            */
#define CCU4_CC4_INS_EV0EM_Msk                (0x03UL << CCU4_CC4_INS_EV0EM_Pos)                      /*!< CCU4_CC4 INS: EV0EM Mask                */
#define CCU4_CC4_INS_EV1EM_Pos                18                                                      /*!< CCU4_CC4 INS: EV1EM Position            */
#define CCU4_CC4_INS_EV1EM_Msk                (0x03UL << CCU4_CC4_INS_EV1EM_Pos)                      /*!< CCU4_CC4 INS: EV1EM Mask                */
#define CCU4_CC4_INS_EV2EM_Pos                20                                                      /*!< CCU4_CC4 INS: EV2EM Position            */
#define CCU4_CC4_INS_EV2EM_Msk                (0x03UL << CCU4_CC4_INS_EV2EM_Pos)                      /*!< CCU4_CC4 INS: EV2EM Mask                */
#define CCU4_CC4_INS_EV0LM_Pos                22                                                      /*!< CCU4_CC4 INS: EV0LM Position            */
#define CCU4_CC4_INS_EV0LM_Msk                (0x01UL << CCU4_CC4_INS_EV0LM_Pos)                      /*!< CCU4_CC4 INS: EV0LM Mask                */
#define CCU4_CC4_INS_EV1LM_Pos                23                                                      /*!< CCU4_CC4 INS: EV1LM Position            */
#define CCU4_CC4_INS_EV1LM_Msk                (0x01UL << CCU4_CC4_INS_EV1LM_Pos)                      /*!< CCU4_CC4 INS: EV1LM Mask                */
#define CCU4_CC4_INS_EV2LM_Pos                24                                                      /*!< CCU4_CC4 INS: EV2LM Position            */
#define CCU4_CC4_INS_EV2LM_Msk                (0x01UL << CCU4_CC4_INS_EV2LM_Pos)                      /*!< CCU4_CC4 INS: EV2LM Mask                */
#define CCU4_CC4_INS_LPF0M_Pos                25                                                      /*!< CCU4_CC4 INS: LPF0M Position            */
#define CCU4_CC4_INS_LPF0M_Msk                (0x03UL << CCU4_CC4_INS_LPF0M_Pos)                      /*!< CCU4_CC4 INS: LPF0M Mask                */
#define CCU4_CC4_INS_LPF1M_Pos                27                                                      /*!< CCU4_CC4 INS: LPF1M Position            */
#define CCU4_CC4_INS_LPF1M_Msk                (0x03UL << CCU4_CC4_INS_LPF1M_Pos)                      /*!< CCU4_CC4 INS: LPF1M Mask                */
#define CCU4_CC4_INS_LPF2M_Pos                29                                                      /*!< CCU4_CC4 INS: LPF2M Position            */
#define CCU4_CC4_INS_LPF2M_Msk                (0x03UL << CCU4_CC4_INS_LPF2M_Pos)                      /*!< CCU4_CC4 INS: LPF2M Mask                */

/* --------------------------------  CCU4_CC4_CMC  -------------------------------- */
#define CCU4_CC4_CMC_STRTS_Pos                0                                                       /*!< CCU4_CC4 CMC: STRTS Position            */
#define CCU4_CC4_CMC_STRTS_Msk                (0x03UL << CCU4_CC4_CMC_STRTS_Pos)                      /*!< CCU4_CC4 CMC: STRTS Mask                */
#define CCU4_CC4_CMC_ENDS_Pos                 2                                                       /*!< CCU4_CC4 CMC: ENDS Position             */
#define CCU4_CC4_CMC_ENDS_Msk                 (0x03UL << CCU4_CC4_CMC_ENDS_Pos)                       /*!< CCU4_CC4 CMC: ENDS Mask                 */
#define CCU4_CC4_CMC_CAP0S_Pos                4                                                       /*!< CCU4_CC4 CMC: CAP0S Position            */
#define CCU4_CC4_CMC_CAP0S_Msk                (0x03UL << CCU4_CC4_CMC_CAP0S_Pos)                      /*!< CCU4_CC4 CMC: CAP0S Mask                */
#define CCU4_CC4_CMC_CAP1S_Pos                6                                                       /*!< CCU4_CC4 CMC: CAP1S Position            */
#define CCU4_CC4_CMC_CAP1S_Msk                (0x03UL << CCU4_CC4_CMC_CAP1S_Pos)                      /*!< CCU4_CC4 CMC: CAP1S Mask                */
#define CCU4_CC4_CMC_GATES_Pos                8                                                       /*!< CCU4_CC4 CMC: GATES Position            */
#define CCU4_CC4_CMC_GATES_Msk                (0x03UL << CCU4_CC4_CMC_GATES_Pos)                      /*!< CCU4_CC4 CMC: GATES Mask                */
#define CCU4_CC4_CMC_UDS_Pos                  10                                                      /*!< CCU4_CC4 CMC: UDS Position              */
#define CCU4_CC4_CMC_UDS_Msk                  (0x03UL << CCU4_CC4_CMC_UDS_Pos)                        /*!< CCU4_CC4 CMC: UDS Mask                  */
#define CCU4_CC4_CMC_LDS_Pos                  12                                                      /*!< CCU4_CC4 CMC: LDS Position              */
#define CCU4_CC4_CMC_LDS_Msk                  (0x03UL << CCU4_CC4_CMC_LDS_Pos)                        /*!< CCU4_CC4 CMC: LDS Mask                  */
#define CCU4_CC4_CMC_CNTS_Pos                 14                                                      /*!< CCU4_CC4 CMC: CNTS Position             */
#define CCU4_CC4_CMC_CNTS_Msk                 (0x03UL << CCU4_CC4_CMC_CNTS_Pos)                       /*!< CCU4_CC4 CMC: CNTS Mask                 */
#define CCU4_CC4_CMC_OFS_Pos                  16                                                      /*!< CCU4_CC4 CMC: OFS Position              */
#define CCU4_CC4_CMC_OFS_Msk                  (0x01UL << CCU4_CC4_CMC_OFS_Pos)                        /*!< CCU4_CC4 CMC: OFS Mask                  */
#define CCU4_CC4_CMC_TS_Pos                   17                                                      /*!< CCU4_CC4 CMC: TS Position               */
#define CCU4_CC4_CMC_TS_Msk                   (0x01UL << CCU4_CC4_CMC_TS_Pos)                         /*!< CCU4_CC4 CMC: TS Mask                   */
#define CCU4_CC4_CMC_MOS_Pos                  18                                                      /*!< CCU4_CC4 CMC: MOS Position              */
#define CCU4_CC4_CMC_MOS_Msk                  (0x03UL << CCU4_CC4_CMC_MOS_Pos)                        /*!< CCU4_CC4 CMC: MOS Mask                  */
#define CCU4_CC4_CMC_TCE_Pos                  20                                                      /*!< CCU4_CC4 CMC: TCE Position              */
#define CCU4_CC4_CMC_TCE_Msk                  (0x01UL << CCU4_CC4_CMC_TCE_Pos)                        /*!< CCU4_CC4 CMC: TCE Mask                  */

/* --------------------------------  CCU4_CC4_TCST  ------------------------------- */
#define CCU4_CC4_TCST_TRB_Pos                 0                                                       /*!< CCU4_CC4 TCST: TRB Position             */
#define CCU4_CC4_TCST_TRB_Msk                 (0x01UL << CCU4_CC4_TCST_TRB_Pos)                       /*!< CCU4_CC4 TCST: TRB Mask                 */
#define CCU4_CC4_TCST_CDIR_Pos                1                                                       /*!< CCU4_CC4 TCST: CDIR Position            */
#define CCU4_CC4_TCST_CDIR_Msk                (0x01UL << CCU4_CC4_TCST_CDIR_Pos)                      /*!< CCU4_CC4 TCST: CDIR Mask                */

/* -------------------------------  CCU4_CC4_TCSET  ------------------------------- */
#define CCU4_CC4_TCSET_TRBS_Pos               0                                                       /*!< CCU4_CC4 TCSET: TRBS Position           */
#define CCU4_CC4_TCSET_TRBS_Msk               (0x01UL << CCU4_CC4_TCSET_TRBS_Pos)                     /*!< CCU4_CC4 TCSET: TRBS Mask               */

/* -------------------------------  CCU4_CC4_TCCLR  ------------------------------- */
#define CCU4_CC4_TCCLR_TRBC_Pos               0                                                       /*!< CCU4_CC4 TCCLR: TRBC Position           */
#define CCU4_CC4_TCCLR_TRBC_Msk               (0x01UL << CCU4_CC4_TCCLR_TRBC_Pos)                     /*!< CCU4_CC4 TCCLR: TRBC Mask               */
#define CCU4_CC4_TCCLR_TCC_Pos                1                                                       /*!< CCU4_CC4 TCCLR: TCC Position            */
#define CCU4_CC4_TCCLR_TCC_Msk                (0x01UL << CCU4_CC4_TCCLR_TCC_Pos)                      /*!< CCU4_CC4 TCCLR: TCC Mask                */
#define CCU4_CC4_TCCLR_DITC_Pos               2                                                       /*!< CCU4_CC4 TCCLR: DITC Position           */
#define CCU4_CC4_TCCLR_DITC_Msk               (0x01UL << CCU4_CC4_TCCLR_DITC_Pos)                     /*!< CCU4_CC4 TCCLR: DITC Mask               */

/* ---------------------------------  CCU4_CC4_TC  -------------------------------- */
#define CCU4_CC4_TC_TCM_Pos                   0                                                       /*!< CCU4_CC4 TC: TCM Position               */
#define CCU4_CC4_TC_TCM_Msk                   (0x01UL << CCU4_CC4_TC_TCM_Pos)                         /*!< CCU4_CC4 TC: TCM Mask                   */
#define CCU4_CC4_TC_TSSM_Pos                  1                                                       /*!< CCU4_CC4 TC: TSSM Position              */
#define CCU4_CC4_TC_TSSM_Msk                  (0x01UL << CCU4_CC4_TC_TSSM_Pos)                        /*!< CCU4_CC4 TC: TSSM Mask                  */
#define CCU4_CC4_TC_CLST_Pos                  2                                                       /*!< CCU4_CC4 TC: CLST Position              */
#define CCU4_CC4_TC_CLST_Msk                  (0x01UL << CCU4_CC4_TC_CLST_Pos)                        /*!< CCU4_CC4 TC: CLST Mask                  */
#define CCU4_CC4_TC_CMOD_Pos                  3                                                       /*!< CCU4_CC4 TC: CMOD Position              */
#define CCU4_CC4_TC_CMOD_Msk                  (0x01UL << CCU4_CC4_TC_CMOD_Pos)                        /*!< CCU4_CC4 TC: CMOD Mask                  */
#define CCU4_CC4_TC_ECM_Pos                   4                                                       /*!< CCU4_CC4 TC: ECM Position               */
#define CCU4_CC4_TC_ECM_Msk                   (0x01UL << CCU4_CC4_TC_ECM_Pos)                         /*!< CCU4_CC4 TC: ECM Mask                   */
#define CCU4_CC4_TC_CAPC_Pos                  5                                                       /*!< CCU4_CC4 TC: CAPC Position              */
#define CCU4_CC4_TC_CAPC_Msk                  (0x03UL << CCU4_CC4_TC_CAPC_Pos)                        /*!< CCU4_CC4 TC: CAPC Mask                  */
#define CCU4_CC4_TC_ENDM_Pos                  8                                                       /*!< CCU4_CC4 TC: ENDM Position              */
#define CCU4_CC4_TC_ENDM_Msk                  (0x03UL << CCU4_CC4_TC_ENDM_Pos)                        /*!< CCU4_CC4 TC: ENDM Mask                  */
#define CCU4_CC4_TC_STRM_Pos                  10                                                      /*!< CCU4_CC4 TC: STRM Position              */
#define CCU4_CC4_TC_STRM_Msk                  (0x01UL << CCU4_CC4_TC_STRM_Pos)                        /*!< CCU4_CC4 TC: STRM Mask                  */
#define CCU4_CC4_TC_SCE_Pos                   11                                                      /*!< CCU4_CC4 TC: SCE Position               */
#define CCU4_CC4_TC_SCE_Msk                   (0x01UL << CCU4_CC4_TC_SCE_Pos)                         /*!< CCU4_CC4 TC: SCE Mask                   */
#define CCU4_CC4_TC_CCS_Pos                   12                                                      /*!< CCU4_CC4 TC: CCS Position               */
#define CCU4_CC4_TC_CCS_Msk                   (0x01UL << CCU4_CC4_TC_CCS_Pos)                         /*!< CCU4_CC4 TC: CCS Mask                   */
#define CCU4_CC4_TC_DITHE_Pos                 13                                                      /*!< CCU4_CC4 TC: DITHE Position             */
#define CCU4_CC4_TC_DITHE_Msk                 (0x03UL << CCU4_CC4_TC_DITHE_Pos)                       /*!< CCU4_CC4 TC: DITHE Mask                 */
#define CCU4_CC4_TC_DIM_Pos                   15                                                      /*!< CCU4_CC4 TC: DIM Position               */
#define CCU4_CC4_TC_DIM_Msk                   (0x01UL << CCU4_CC4_TC_DIM_Pos)                         /*!< CCU4_CC4 TC: DIM Mask                   */
#define CCU4_CC4_TC_FPE_Pos                   16                                                      /*!< CCU4_CC4 TC: FPE Position               */
#define CCU4_CC4_TC_FPE_Msk                   (0x01UL << CCU4_CC4_TC_FPE_Pos)                         /*!< CCU4_CC4 TC: FPE Mask                   */
#define CCU4_CC4_TC_TRAPE_Pos                 17                                                      /*!< CCU4_CC4 TC: TRAPE Position             */
#define CCU4_CC4_TC_TRAPE_Msk                 (0x01UL << CCU4_CC4_TC_TRAPE_Pos)                       /*!< CCU4_CC4 TC: TRAPE Mask                 */
#define CCU4_CC4_TC_TRPSE_Pos                 21                                                      /*!< CCU4_CC4 TC: TRPSE Position             */
#define CCU4_CC4_TC_TRPSE_Msk                 (0x01UL << CCU4_CC4_TC_TRPSE_Pos)                       /*!< CCU4_CC4 TC: TRPSE Mask                 */
#define CCU4_CC4_TC_TRPSW_Pos                 22                                                      /*!< CCU4_CC4 TC: TRPSW Position             */
#define CCU4_CC4_TC_TRPSW_Msk                 (0x01UL << CCU4_CC4_TC_TRPSW_Pos)                       /*!< CCU4_CC4 TC: TRPSW Mask                 */
#define CCU4_CC4_TC_EMS_Pos                   23                                                      /*!< CCU4_CC4 TC: EMS Position               */
#define CCU4_CC4_TC_EMS_Msk                   (0x01UL << CCU4_CC4_TC_EMS_Pos)                         /*!< CCU4_CC4 TC: EMS Mask                   */
#define CCU4_CC4_TC_EMT_Pos                   24                                                      /*!< CCU4_CC4 TC: EMT Position               */
#define CCU4_CC4_TC_EMT_Msk                   (0x01UL << CCU4_CC4_TC_EMT_Pos)                         /*!< CCU4_CC4 TC: EMT Mask                   */
#define CCU4_CC4_TC_MCME_Pos                  25                                                      /*!< CCU4_CC4 TC: MCME Position              */
#define CCU4_CC4_TC_MCME_Msk                  (0x01UL << CCU4_CC4_TC_MCME_Pos)                        /*!< CCU4_CC4 TC: MCME Mask                  */

/* --------------------------------  CCU4_CC4_PSL  -------------------------------- */
#define CCU4_CC4_PSL_PSL_Pos                  0                                                       /*!< CCU4_CC4 PSL: PSL Position              */
#define CCU4_CC4_PSL_PSL_Msk                  (0x01UL << CCU4_CC4_PSL_PSL_Pos)                        /*!< CCU4_CC4 PSL: PSL Mask                  */

/* --------------------------------  CCU4_CC4_DIT  -------------------------------- */
#define CCU4_CC4_DIT_DCV_Pos                  0                                                       /*!< CCU4_CC4 DIT: DCV Position              */
#define CCU4_CC4_DIT_DCV_Msk                  (0x0fUL << CCU4_CC4_DIT_DCV_Pos)                        /*!< CCU4_CC4 DIT: DCV Mask                  */
#define CCU4_CC4_DIT_DCNT_Pos                 8                                                       /*!< CCU4_CC4 DIT: DCNT Position             */
#define CCU4_CC4_DIT_DCNT_Msk                 (0x0fUL << CCU4_CC4_DIT_DCNT_Pos)                       /*!< CCU4_CC4 DIT: DCNT Mask                 */

/* --------------------------------  CCU4_CC4_DITS  ------------------------------- */
#define CCU4_CC4_DITS_DCVS_Pos                0                                                       /*!< CCU4_CC4 DITS: DCVS Position            */
#define CCU4_CC4_DITS_DCVS_Msk                (0x0fUL << CCU4_CC4_DITS_DCVS_Pos)                      /*!< CCU4_CC4 DITS: DCVS Mask                */

/* --------------------------------  CCU4_CC4_PSC  -------------------------------- */
#define CCU4_CC4_PSC_PSIV_Pos                 0                                                       /*!< CCU4_CC4 PSC: PSIV Position             */
#define CCU4_CC4_PSC_PSIV_Msk                 (0x0fUL << CCU4_CC4_PSC_PSIV_Pos)                       /*!< CCU4_CC4 PSC: PSIV Mask                 */

/* --------------------------------  CCU4_CC4_FPC  -------------------------------- */
#define CCU4_CC4_FPC_PCMP_Pos                 0                                                       /*!< CCU4_CC4 FPC: PCMP Position             */
#define CCU4_CC4_FPC_PCMP_Msk                 (0x0fUL << CCU4_CC4_FPC_PCMP_Pos)                       /*!< CCU4_CC4 FPC: PCMP Mask                 */
#define CCU4_CC4_FPC_PVAL_Pos                 8                                                       /*!< CCU4_CC4 FPC: PVAL Position             */
#define CCU4_CC4_FPC_PVAL_Msk                 (0x0fUL << CCU4_CC4_FPC_PVAL_Pos)                       /*!< CCU4_CC4 FPC: PVAL Mask                 */

/* --------------------------------  CCU4_CC4_FPCS  ------------------------------- */
#define CCU4_CC4_FPCS_PCMP_Pos                0                                                       /*!< CCU4_CC4 FPCS: PCMP Position            */
#define CCU4_CC4_FPCS_PCMP_Msk                (0x0fUL << CCU4_CC4_FPCS_PCMP_Pos)                      /*!< CCU4_CC4 FPCS: PCMP Mask                */

/* ---------------------------------  CCU4_CC4_PR  -------------------------------- */
#define CCU4_CC4_PR_PR_Pos                    0                                                       /*!< CCU4_CC4 PR: PR Position                */
#define CCU4_CC4_PR_PR_Msk                    (0x0000ffffUL << CCU4_CC4_PR_PR_Pos)                    /*!< CCU4_CC4 PR: PR Mask                    */

/* --------------------------------  CCU4_CC4_PRS  -------------------------------- */
#define CCU4_CC4_PRS_PRS_Pos                  0                                                       /*!< CCU4_CC4 PRS: PRS Position              */
#define CCU4_CC4_PRS_PRS_Msk                  (0x0000ffffUL << CCU4_CC4_PRS_PRS_Pos)                  /*!< CCU4_CC4 PRS: PRS Mask                  */

/* ---------------------------------  CCU4_CC4_CR  -------------------------------- */
#define CCU4_CC4_CR_CR_Pos                    0                                                       /*!< CCU4_CC4 CR: CR Position                */
#define CCU4_CC4_CR_CR_Msk                    (0x0000ffffUL << CCU4_CC4_CR_CR_Pos)                    /*!< CCU4_CC4 CR: CR Mask                    */

/* --------------------------------  CCU4_CC4_CRS  -------------------------------- */
#define CCU4_CC4_CRS_CRS_Pos                  0                                                       /*!< CCU4_CC4 CRS: CRS Position              */
#define CCU4_CC4_CRS_CRS_Msk                  (0x0000ffffUL << CCU4_CC4_CRS_CRS_Pos)                  /*!< CCU4_CC4 CRS: CRS Mask                  */

/* -------------------------------  CCU4_CC4_TIMER  ------------------------------- */
#define CCU4_CC4_TIMER_TVAL_Pos               0                                                       /*!< CCU4_CC4 TIMER: TVAL Position           */
#define CCU4_CC4_TIMER_TVAL_Msk               (0x0000ffffUL << CCU4_CC4_TIMER_TVAL_Pos)               /*!< CCU4_CC4 TIMER: TVAL Mask               */

/* ---------------------------------  CCU4_CC4_CV  -------------------------------- */
#define CCU4_CC4_CV_CAPTV_Pos                 0                                                       /*!< CCU4_CC4 CV: CAPTV Position             */
#define CCU4_CC4_CV_CAPTV_Msk                 (0x0000ffffUL << CCU4_CC4_CV_CAPTV_Pos)                 /*!< CCU4_CC4 CV: CAPTV Mask                 */
#define CCU4_CC4_CV_FPCV_Pos                  16                                                      /*!< CCU4_CC4 CV: FPCV Position              */
#define CCU4_CC4_CV_FPCV_Msk                  (0x0fUL << CCU4_CC4_CV_FPCV_Pos)                        /*!< CCU4_CC4 CV: FPCV Mask                  */
#define CCU4_CC4_CV_FFL_Pos                   20                                                      /*!< CCU4_CC4 CV: FFL Position               */
#define CCU4_CC4_CV_FFL_Msk                   (0x01UL << CCU4_CC4_CV_FFL_Pos)                         /*!< CCU4_CC4 CV: FFL Mask                   */

/* --------------------------------  CCU4_CC4_INTS  ------------------------------- */
#define CCU4_CC4_INTS_PMUS_Pos                0                                                       /*!< CCU4_CC4 INTS: PMUS Position            */
#define CCU4_CC4_INTS_PMUS_Msk                (0x01UL << CCU4_CC4_INTS_PMUS_Pos)                      /*!< CCU4_CC4 INTS: PMUS Mask                */
#define CCU4_CC4_INTS_OMDS_Pos                1                                                       /*!< CCU4_CC4 INTS: OMDS Position            */
#define CCU4_CC4_INTS_OMDS_Msk                (0x01UL << CCU4_CC4_INTS_OMDS_Pos)                      /*!< CCU4_CC4 INTS: OMDS Mask                */
#define CCU4_CC4_INTS_CMUS_Pos                2                                                       /*!< CCU4_CC4 INTS: CMUS Position            */
#define CCU4_CC4_INTS_CMUS_Msk                (0x01UL << CCU4_CC4_INTS_CMUS_Pos)                      /*!< CCU4_CC4 INTS: CMUS Mask                */
#define CCU4_CC4_INTS_CMDS_Pos                3                                                       /*!< CCU4_CC4 INTS: CMDS Position            */
#define CCU4_CC4_INTS_CMDS_Msk                (0x01UL << CCU4_CC4_INTS_CMDS_Pos)                      /*!< CCU4_CC4 INTS: CMDS Mask                */
#define CCU4_CC4_INTS_E0AS_Pos                8                                                       /*!< CCU4_CC4 INTS: E0AS Position            */
#define CCU4_CC4_INTS_E0AS_Msk                (0x01UL << CCU4_CC4_INTS_E0AS_Pos)                      /*!< CCU4_CC4 INTS: E0AS Mask                */
#define CCU4_CC4_INTS_E1AS_Pos                9                                                       /*!< CCU4_CC4 INTS: E1AS Position            */
#define CCU4_CC4_INTS_E1AS_Msk                (0x01UL << CCU4_CC4_INTS_E1AS_Pos)                      /*!< CCU4_CC4 INTS: E1AS Mask                */
#define CCU4_CC4_INTS_E2AS_Pos                10                                                      /*!< CCU4_CC4 INTS: E2AS Position            */
#define CCU4_CC4_INTS_E2AS_Msk                (0x01UL << CCU4_CC4_INTS_E2AS_Pos)                      /*!< CCU4_CC4 INTS: E2AS Mask                */
#define CCU4_CC4_INTS_TRPF_Pos                11                                                      /*!< CCU4_CC4 INTS: TRPF Position            */
#define CCU4_CC4_INTS_TRPF_Msk                (0x01UL << CCU4_CC4_INTS_TRPF_Pos)                      /*!< CCU4_CC4 INTS: TRPF Mask                */

/* --------------------------------  CCU4_CC4_INTE  ------------------------------- */
#define CCU4_CC4_INTE_PME_Pos                 0                                                       /*!< CCU4_CC4 INTE: PME Position             */
#define CCU4_CC4_INTE_PME_Msk                 (0x01UL << CCU4_CC4_INTE_PME_Pos)                       /*!< CCU4_CC4 INTE: PME Mask                 */
#define CCU4_CC4_INTE_OME_Pos                 1                                                       /*!< CCU4_CC4 INTE: OME Position             */
#define CCU4_CC4_INTE_OME_Msk                 (0x01UL << CCU4_CC4_INTE_OME_Pos)                       /*!< CCU4_CC4 INTE: OME Mask                 */
#define CCU4_CC4_INTE_CMUE_Pos                2                                                       /*!< CCU4_CC4 INTE: CMUE Position            */
#define CCU4_CC4_INTE_CMUE_Msk                (0x01UL << CCU4_CC4_INTE_CMUE_Pos)                      /*!< CCU4_CC4 INTE: CMUE Mask                */
#define CCU4_CC4_INTE_CMDE_Pos                3                                                       /*!< CCU4_CC4 INTE: CMDE Position            */
#define CCU4_CC4_INTE_CMDE_Msk                (0x01UL << CCU4_CC4_INTE_CMDE_Pos)                      /*!< CCU4_CC4 INTE: CMDE Mask                */
#define CCU4_CC4_INTE_E0AE_Pos                8                                                       /*!< CCU4_CC4 INTE: E0AE Position            */
#define CCU4_CC4_INTE_E0AE_Msk                (0x01UL << CCU4_CC4_INTE_E0AE_Pos)                      /*!< CCU4_CC4 INTE: E0AE Mask                */
#define CCU4_CC4_INTE_E1AE_Pos                9                                                       /*!< CCU4_CC4 INTE: E1AE Position            */
#define CCU4_CC4_INTE_E1AE_Msk                (0x01UL << CCU4_CC4_INTE_E1AE_Pos)                      /*!< CCU4_CC4 INTE: E1AE Mask                */
#define CCU4_CC4_INTE_E2AE_Pos                10                                                      /*!< CCU4_CC4 INTE: E2AE Position            */
#define CCU4_CC4_INTE_E2AE_Msk                (0x01UL << CCU4_CC4_INTE_E2AE_Pos)                      /*!< CCU4_CC4 INTE: E2AE Mask                */

/* --------------------------------  CCU4_CC4_SRS  -------------------------------- */
#define CCU4_CC4_SRS_POSR_Pos                 0                                                       /*!< CCU4_CC4 SRS: POSR Position             */
#define CCU4_CC4_SRS_POSR_Msk                 (0x03UL << CCU4_CC4_SRS_POSR_Pos)                       /*!< CCU4_CC4 SRS: POSR Mask                 */
#define CCU4_CC4_SRS_CMSR_Pos                 2                                                       /*!< CCU4_CC4 SRS: CMSR Position             */
#define CCU4_CC4_SRS_CMSR_Msk                 (0x03UL << CCU4_CC4_SRS_CMSR_Pos)                       /*!< CCU4_CC4 SRS: CMSR Mask                 */
#define CCU4_CC4_SRS_E0SR_Pos                 8                                                       /*!< CCU4_CC4 SRS: E0SR Position             */
#define CCU4_CC4_SRS_E0SR_Msk                 (0x03UL << CCU4_CC4_SRS_E0SR_Pos)                       /*!< CCU4_CC4 SRS: E0SR Mask                 */
#define CCU4_CC4_SRS_E1SR_Pos                 10                                                      /*!< CCU4_CC4 SRS: E1SR Position             */
#define CCU4_CC4_SRS_E1SR_Msk                 (0x03UL << CCU4_CC4_SRS_E1SR_Pos)                       /*!< CCU4_CC4 SRS: E1SR Mask                 */
#define CCU4_CC4_SRS_E2SR_Pos                 12                                                      /*!< CCU4_CC4 SRS: E2SR Position             */
#define CCU4_CC4_SRS_E2SR_Msk                 (0x03UL << CCU4_CC4_SRS_E2SR_Pos)                       /*!< CCU4_CC4 SRS: E2SR Mask                 */

/* --------------------------------  CCU4_CC4_SWS  -------------------------------- */
#define CCU4_CC4_SWS_SPM_Pos                  0                                                       /*!< CCU4_CC4 SWS: SPM Position              */
#define CCU4_CC4_SWS_SPM_Msk                  (0x01UL << CCU4_CC4_SWS_SPM_Pos)                        /*!< CCU4_CC4 SWS: SPM Mask                  */
#define CCU4_CC4_SWS_SOM_Pos                  1                                                       /*!< CCU4_CC4 SWS: SOM Position              */
#define CCU4_CC4_SWS_SOM_Msk                  (0x01UL << CCU4_CC4_SWS_SOM_Pos)                        /*!< CCU4_CC4 SWS: SOM Mask                  */
#define CCU4_CC4_SWS_SCMU_Pos                 2                                                       /*!< CCU4_CC4 SWS: SCMU Position             */
#define CCU4_CC4_SWS_SCMU_Msk                 (0x01UL << CCU4_CC4_SWS_SCMU_Pos)                       /*!< CCU4_CC4 SWS: SCMU Mask                 */
#define CCU4_CC4_SWS_SCMD_Pos                 3                                                       /*!< CCU4_CC4 SWS: SCMD Position             */
#define CCU4_CC4_SWS_SCMD_Msk                 (0x01UL << CCU4_CC4_SWS_SCMD_Pos)                       /*!< CCU4_CC4 SWS: SCMD Mask                 */
#define CCU4_CC4_SWS_SE0A_Pos                 8                                                       /*!< CCU4_CC4 SWS: SE0A Position             */
#define CCU4_CC4_SWS_SE0A_Msk                 (0x01UL << CCU4_CC4_SWS_SE0A_Pos)                       /*!< CCU4_CC4 SWS: SE0A Mask                 */
#define CCU4_CC4_SWS_SE1A_Pos                 9                                                       /*!< CCU4_CC4 SWS: SE1A Position             */
#define CCU4_CC4_SWS_SE1A_Msk                 (0x01UL << CCU4_CC4_SWS_SE1A_Pos)                       /*!< CCU4_CC4 SWS: SE1A Mask                 */
#define CCU4_CC4_SWS_SE2A_Pos                 10                                                      /*!< CCU4_CC4 SWS: SE2A Position             */
#define CCU4_CC4_SWS_SE2A_Msk                 (0x01UL << CCU4_CC4_SWS_SE2A_Pos)                       /*!< CCU4_CC4 SWS: SE2A Mask                 */
#define CCU4_CC4_SWS_STRPF_Pos                11                                                      /*!< CCU4_CC4 SWS: STRPF Position            */
#define CCU4_CC4_SWS_STRPF_Msk                (0x01UL << CCU4_CC4_SWS_STRPF_Pos)                      /*!< CCU4_CC4 SWS: STRPF Mask                */

/* --------------------------------  CCU4_CC4_SWR  -------------------------------- */
#define CCU4_CC4_SWR_RPM_Pos                  0                                                       /*!< CCU4_CC4 SWR: RPM Position              */
#define CCU4_CC4_SWR_RPM_Msk                  (0x01UL << CCU4_CC4_SWR_RPM_Pos)                        /*!< CCU4_CC4 SWR: RPM Mask                  */
#define CCU4_CC4_SWR_ROM_Pos                  1                                                       /*!< CCU4_CC4 SWR: ROM Position              */
#define CCU4_CC4_SWR_ROM_Msk                  (0x01UL << CCU4_CC4_SWR_ROM_Pos)                        /*!< CCU4_CC4 SWR: ROM Mask                  */
#define CCU4_CC4_SWR_RCMU_Pos                 2                                                       /*!< CCU4_CC4 SWR: RCMU Position             */
#define CCU4_CC4_SWR_RCMU_Msk                 (0x01UL << CCU4_CC4_SWR_RCMU_Pos)                       /*!< CCU4_CC4 SWR: RCMU Mask                 */
#define CCU4_CC4_SWR_RCMD_Pos                 3                                                       /*!< CCU4_CC4 SWR: RCMD Position             */
#define CCU4_CC4_SWR_RCMD_Msk                 (0x01UL << CCU4_CC4_SWR_RCMD_Pos)                       /*!< CCU4_CC4 SWR: RCMD Mask                 */
#define CCU4_CC4_SWR_RE0A_Pos                 8                                                       /*!< CCU4_CC4 SWR: RE0A Position             */
#define CCU4_CC4_SWR_RE0A_Msk                 (0x01UL << CCU4_CC4_SWR_RE0A_Pos)                       /*!< CCU4_CC4 SWR: RE0A Mask                 */
#define CCU4_CC4_SWR_RE1A_Pos                 9                                                       /*!< CCU4_CC4 SWR: RE1A Position             */
#define CCU4_CC4_SWR_RE1A_Msk                 (0x01UL << CCU4_CC4_SWR_RE1A_Pos)                       /*!< CCU4_CC4 SWR: RE1A Mask                 */
#define CCU4_CC4_SWR_RE2A_Pos                 10                                                      /*!< CCU4_CC4 SWR: RE2A Position             */
#define CCU4_CC4_SWR_RE2A_Msk                 (0x01UL << CCU4_CC4_SWR_RE2A_Pos)                       /*!< CCU4_CC4 SWR: RE2A Mask                 */
#define CCU4_CC4_SWR_RTRPF_Pos                11                                                      /*!< CCU4_CC4 SWR: RTRPF Position            */
#define CCU4_CC4_SWR_RTRPF_Msk                (0x01UL << CCU4_CC4_SWR_RTRPF_Pos)                      /*!< CCU4_CC4 SWR: RTRPF Mask                */

/* -------------------------------  CCU4_CC4_ECRD0  ------------------------------- */
#define CCU4_CC4_ECRD0_CAPV_Pos               0                                                       /*!< CCU4_CC4 ECRD0: CAPV Position           */
#define CCU4_CC4_ECRD0_CAPV_Msk               (0x0000ffffUL << CCU4_CC4_ECRD0_CAPV_Pos)               /*!< CCU4_CC4 ECRD0: CAPV Mask               */
#define CCU4_CC4_ECRD0_FPCV_Pos               16                                                      /*!< CCU4_CC4 ECRD0: FPCV Position           */
#define CCU4_CC4_ECRD0_FPCV_Msk               (0x0fUL << CCU4_CC4_ECRD0_FPCV_Pos)                     /*!< CCU4_CC4 ECRD0: FPCV Mask               */
#define CCU4_CC4_ECRD0_SPTR_Pos               20                                                      /*!< CCU4_CC4 ECRD0: SPTR Position           */
#define CCU4_CC4_ECRD0_SPTR_Msk               (0x03UL << CCU4_CC4_ECRD0_SPTR_Pos)                     /*!< CCU4_CC4 ECRD0: SPTR Mask               */
#define CCU4_CC4_ECRD0_VPTR_Pos               22                                                      /*!< CCU4_CC4 ECRD0: VPTR Position           */
#define CCU4_CC4_ECRD0_VPTR_Msk               (0x03UL << CCU4_CC4_ECRD0_VPTR_Pos)                     /*!< CCU4_CC4 ECRD0: VPTR Mask               */
#define CCU4_CC4_ECRD0_FFL_Pos                24                                                      /*!< CCU4_CC4 ECRD0: FFL Position            */
#define CCU4_CC4_ECRD0_FFL_Msk                (0x01UL << CCU4_CC4_ECRD0_FFL_Pos)                      /*!< CCU4_CC4 ECRD0: FFL Mask                */
#define CCU4_CC4_ECRD0_LCV_Pos                25                                                      /*!< CCU4_CC4 ECRD0: LCV Position            */
#define CCU4_CC4_ECRD0_LCV_Msk                (0x01UL << CCU4_CC4_ECRD0_LCV_Pos)                      /*!< CCU4_CC4 ECRD0: LCV Mask                */

/* -------------------------------  CCU4_CC4_ECRD1  ------------------------------- */
#define CCU4_CC4_ECRD1_CAPV_Pos               0                                                       /*!< CCU4_CC4 ECRD1: CAPV Position           */
#define CCU4_CC4_ECRD1_CAPV_Msk               (0x0000ffffUL << CCU4_CC4_ECRD1_CAPV_Pos)               /*!< CCU4_CC4 ECRD1: CAPV Mask               */
#define CCU4_CC4_ECRD1_FPCV_Pos               16                                                      /*!< CCU4_CC4 ECRD1: FPCV Position           */
#define CCU4_CC4_ECRD1_FPCV_Msk               (0x0fUL << CCU4_CC4_ECRD1_FPCV_Pos)                     /*!< CCU4_CC4 ECRD1: FPCV Mask               */
#define CCU4_CC4_ECRD1_SPTR_Pos               20                                                      /*!< CCU4_CC4 ECRD1: SPTR Position           */
#define CCU4_CC4_ECRD1_SPTR_Msk               (0x03UL << CCU4_CC4_ECRD1_SPTR_Pos)                     /*!< CCU4_CC4 ECRD1: SPTR Mask               */
#define CCU4_CC4_ECRD1_VPTR_Pos               22                                                      /*!< CCU4_CC4 ECRD1: VPTR Position           */
#define CCU4_CC4_ECRD1_VPTR_Msk               (0x03UL << CCU4_CC4_ECRD1_VPTR_Pos)                     /*!< CCU4_CC4 ECRD1: VPTR Mask               */
#define CCU4_CC4_ECRD1_FFL_Pos                24                                                      /*!< CCU4_CC4 ECRD1: FFL Position            */
#define CCU4_CC4_ECRD1_FFL_Msk                (0x01UL << CCU4_CC4_ECRD1_FFL_Pos)                      /*!< CCU4_CC4 ECRD1: FFL Mask                */
#define CCU4_CC4_ECRD1_LCV_Pos                25                                                      /*!< CCU4_CC4 ECRD1: LCV Position            */
#define CCU4_CC4_ECRD1_LCV_Msk                (0x01UL << CCU4_CC4_ECRD1_LCV_Pos)                      /*!< CCU4_CC4 ECRD1: LCV Mask                */


/* ================================================================================ */
/* ================          Group 'VADC' Position & Mask          ================ */
/* ================================================================================ */


/* ----------------------------------  VADC_CLC  ---------------------------------- */
#define VADC_CLC_DISR_Pos                     0                                                       /*!< VADC CLC: DISR Position                 */
#define VADC_CLC_DISR_Msk                     (0x01UL << VADC_CLC_DISR_Pos)                           /*!< VADC CLC: DISR Mask                     */
#define VADC_CLC_DISS_Pos                     1                                                       /*!< VADC CLC: DISS Position                 */
#define VADC_CLC_DISS_Msk                     (0x01UL << VADC_CLC_DISS_Pos)                           /*!< VADC CLC: DISS Mask                     */
#define VADC_CLC_EDIS_Pos                     3                                                       /*!< VADC CLC: EDIS Position                 */
#define VADC_CLC_EDIS_Msk                     (0x01UL << VADC_CLC_EDIS_Pos)                           /*!< VADC CLC: EDIS Mask                     */

/* -----------------------------------  VADC_ID  ---------------------------------- */
#define VADC_ID_MOD_REV_Pos                   0                                                       /*!< VADC ID: MOD_REV Position               */
#define VADC_ID_MOD_REV_Msk                   (0x000000ffUL << VADC_ID_MOD_REV_Pos)                   /*!< VADC ID: MOD_REV Mask                   */
#define VADC_ID_MOD_TYPE_Pos                  8                                                       /*!< VADC ID: MOD_TYPE Position              */
#define VADC_ID_MOD_TYPE_Msk                  (0x000000ffUL << VADC_ID_MOD_TYPE_Pos)                  /*!< VADC ID: MOD_TYPE Mask                  */
#define VADC_ID_MOD_NUMBER_Pos                16                                                      /*!< VADC ID: MOD_NUMBER Position            */
#define VADC_ID_MOD_NUMBER_Msk                (0x0000ffffUL << VADC_ID_MOD_NUMBER_Pos)                /*!< VADC ID: MOD_NUMBER Mask                */

/* ----------------------------------  VADC_OCS  ---------------------------------- */
#define VADC_OCS_TGS_Pos                      0                                                       /*!< VADC OCS: TGS Position                  */
#define VADC_OCS_TGS_Msk                      (0x03UL << VADC_OCS_TGS_Pos)                            /*!< VADC OCS: TGS Mask                      */
#define VADC_OCS_TGB_Pos                      2                                                       /*!< VADC OCS: TGB Position                  */
#define VADC_OCS_TGB_Msk                      (0x01UL << VADC_OCS_TGB_Pos)                            /*!< VADC OCS: TGB Mask                      */
#define VADC_OCS_TG_P_Pos                     3                                                       /*!< VADC OCS: TG_P Position                 */
#define VADC_OCS_TG_P_Msk                     (0x01UL << VADC_OCS_TG_P_Pos)                           /*!< VADC OCS: TG_P Mask                     */
#define VADC_OCS_SUS_Pos                      24                                                      /*!< VADC OCS: SUS Position                  */
#define VADC_OCS_SUS_Msk                      (0x0fUL << VADC_OCS_SUS_Pos)                            /*!< VADC OCS: SUS Mask                      */
#define VADC_OCS_SUS_P_Pos                    28                                                      /*!< VADC OCS: SUS_P Position                */
#define VADC_OCS_SUS_P_Msk                    (0x01UL << VADC_OCS_SUS_P_Pos)                          /*!< VADC OCS: SUS_P Mask                    */
#define VADC_OCS_SUSSTA_Pos                   29                                                      /*!< VADC OCS: SUSSTA Position               */
#define VADC_OCS_SUSSTA_Msk                   (0x01UL << VADC_OCS_SUSSTA_Pos)                         /*!< VADC OCS: SUSSTA Mask                   */

/* --------------------------------  VADC_GLOBCFG  -------------------------------- */
#define VADC_GLOBCFG_DIVA_Pos                 0                                                       /*!< VADC GLOBCFG: DIVA Position             */
#define VADC_GLOBCFG_DIVA_Msk                 (0x1fUL << VADC_GLOBCFG_DIVA_Pos)                       /*!< VADC GLOBCFG: DIVA Mask                 */
#define VADC_GLOBCFG_DCMSB_Pos                7                                                       /*!< VADC GLOBCFG: DCMSB Position            */
#define VADC_GLOBCFG_DCMSB_Msk                (0x01UL << VADC_GLOBCFG_DCMSB_Pos)                      /*!< VADC GLOBCFG: DCMSB Mask                */
#define VADC_GLOBCFG_DIVD_Pos                 8                                                       /*!< VADC GLOBCFG: DIVD Position             */
#define VADC_GLOBCFG_DIVD_Msk                 (0x03UL << VADC_GLOBCFG_DIVD_Pos)                       /*!< VADC GLOBCFG: DIVD Mask                 */
#define VADC_GLOBCFG_DIVWC_Pos                15                                                      /*!< VADC GLOBCFG: DIVWC Position            */
#define VADC_GLOBCFG_DIVWC_Msk                (0x01UL << VADC_GLOBCFG_DIVWC_Pos)                      /*!< VADC GLOBCFG: DIVWC Mask                */
#define VADC_GLOBCFG_DPCAL0_Pos               16                                                      /*!< VADC GLOBCFG: DPCAL0 Position           */
#define VADC_GLOBCFG_DPCAL0_Msk               (0x01UL << VADC_GLOBCFG_DPCAL0_Pos)                     /*!< VADC GLOBCFG: DPCAL0 Mask               */
#define VADC_GLOBCFG_DPCAL1_Pos               17                                                      /*!< VADC GLOBCFG: DPCAL1 Position           */
#define VADC_GLOBCFG_DPCAL1_Msk               (0x01UL << VADC_GLOBCFG_DPCAL1_Pos)                     /*!< VADC GLOBCFG: DPCAL1 Mask               */
#define VADC_GLOBCFG_SUCAL_Pos                31                                                      /*!< VADC GLOBCFG: SUCAL Position            */
#define VADC_GLOBCFG_SUCAL_Msk                (0x01UL << VADC_GLOBCFG_SUCAL_Pos)                      /*!< VADC GLOBCFG: SUCAL Mask                */

/* -------------------------------  VADC_GLOBICLASS  ------------------------------ */
#define VADC_GLOBICLASS_STCS_Pos              0                                                       /*!< VADC GLOBICLASS: STCS Position          */
#define VADC_GLOBICLASS_STCS_Msk              (0x1fUL << VADC_GLOBICLASS_STCS_Pos)                    /*!< VADC GLOBICLASS: STCS Mask              */
#define VADC_GLOBICLASS_CMS_Pos               8                                                       /*!< VADC GLOBICLASS: CMS Position           */
#define VADC_GLOBICLASS_CMS_Msk               (0x07UL << VADC_GLOBICLASS_CMS_Pos)                     /*!< VADC GLOBICLASS: CMS Mask               */

/* -------------------------------  VADC_GLOBEFLAG  ------------------------------- */
#define VADC_GLOBEFLAG_SEVGLB_Pos             0                                                       /*!< VADC GLOBEFLAG: SEVGLB Position         */
#define VADC_GLOBEFLAG_SEVGLB_Msk             (0x01UL << VADC_GLOBEFLAG_SEVGLB_Pos)                   /*!< VADC GLOBEFLAG: SEVGLB Mask             */
#define VADC_GLOBEFLAG_REVGLB_Pos             8                                                       /*!< VADC GLOBEFLAG: REVGLB Position         */
#define VADC_GLOBEFLAG_REVGLB_Msk             (0x01UL << VADC_GLOBEFLAG_REVGLB_Pos)                   /*!< VADC GLOBEFLAG: REVGLB Mask             */
#define VADC_GLOBEFLAG_SEVGLBCLR_Pos          16                                                      /*!< VADC GLOBEFLAG: SEVGLBCLR Position      */
#define VADC_GLOBEFLAG_SEVGLBCLR_Msk          (0x01UL << VADC_GLOBEFLAG_SEVGLBCLR_Pos)                /*!< VADC GLOBEFLAG: SEVGLBCLR Mask          */
#define VADC_GLOBEFLAG_REVGLBCLR_Pos          24                                                      /*!< VADC GLOBEFLAG: REVGLBCLR Position      */
#define VADC_GLOBEFLAG_REVGLBCLR_Msk          (0x01UL << VADC_GLOBEFLAG_REVGLBCLR_Pos)                /*!< VADC GLOBEFLAG: REVGLBCLR Mask          */

/* --------------------------------  VADC_GLOBEVNP  ------------------------------- */
#define VADC_GLOBEVNP_SEV0NP_Pos              0                                                       /*!< VADC GLOBEVNP: SEV0NP Position          */
#define VADC_GLOBEVNP_SEV0NP_Msk              (0x0fUL << VADC_GLOBEVNP_SEV0NP_Pos)                    /*!< VADC GLOBEVNP: SEV0NP Mask              */
#define VADC_GLOBEVNP_REV0NP_Pos              16                                                      /*!< VADC GLOBEVNP: REV0NP Position          */
#define VADC_GLOBEVNP_REV0NP_Msk              (0x0fUL << VADC_GLOBEVNP_REV0NP_Pos)                    /*!< VADC GLOBEVNP: REV0NP Mask              */

/* ---------------------------------  VADC_BRSSEL  -------------------------------- */
#define VADC_BRSSEL_CHSELG0_Pos               0                                                       /*!< VADC BRSSEL: CHSELG0 Position           */
#define VADC_BRSSEL_CHSELG0_Msk               (0x01UL << VADC_BRSSEL_CHSELG0_Pos)                     /*!< VADC BRSSEL: CHSELG0 Mask               */
#define VADC_BRSSEL_CHSELG1_Pos               1                                                       /*!< VADC BRSSEL: CHSELG1 Position           */
#define VADC_BRSSEL_CHSELG1_Msk               (0x01UL << VADC_BRSSEL_CHSELG1_Pos)                     /*!< VADC BRSSEL: CHSELG1 Mask               */
#define VADC_BRSSEL_CHSELG2_Pos               2                                                       /*!< VADC BRSSEL: CHSELG2 Position           */
#define VADC_BRSSEL_CHSELG2_Msk               (0x01UL << VADC_BRSSEL_CHSELG2_Pos)                     /*!< VADC BRSSEL: CHSELG2 Mask               */
#define VADC_BRSSEL_CHSELG3_Pos               3                                                       /*!< VADC BRSSEL: CHSELG3 Position           */
#define VADC_BRSSEL_CHSELG3_Msk               (0x01UL << VADC_BRSSEL_CHSELG3_Pos)                     /*!< VADC BRSSEL: CHSELG3 Mask               */
#define VADC_BRSSEL_CHSELG4_Pos               4                                                       /*!< VADC BRSSEL: CHSELG4 Position           */
#define VADC_BRSSEL_CHSELG4_Msk               (0x01UL << VADC_BRSSEL_CHSELG4_Pos)                     /*!< VADC BRSSEL: CHSELG4 Mask               */
#define VADC_BRSSEL_CHSELG5_Pos               5                                                       /*!< VADC BRSSEL: CHSELG5 Position           */
#define VADC_BRSSEL_CHSELG5_Msk               (0x01UL << VADC_BRSSEL_CHSELG5_Pos)                     /*!< VADC BRSSEL: CHSELG5 Mask               */
#define VADC_BRSSEL_CHSELG6_Pos               6                                                       /*!< VADC BRSSEL: CHSELG6 Position           */
#define VADC_BRSSEL_CHSELG6_Msk               (0x01UL << VADC_BRSSEL_CHSELG6_Pos)                     /*!< VADC BRSSEL: CHSELG6 Mask               */
#define VADC_BRSSEL_CHSELG7_Pos               7                                                       /*!< VADC BRSSEL: CHSELG7 Position           */
#define VADC_BRSSEL_CHSELG7_Msk               (0x01UL << VADC_BRSSEL_CHSELG7_Pos)                     /*!< VADC BRSSEL: CHSELG7 Mask               */

/* ---------------------------------  VADC_BRSPND  -------------------------------- */
#define VADC_BRSPND_CHPNDG0_Pos               0                                                       /*!< VADC BRSPND: CHPNDG0 Position           */
#define VADC_BRSPND_CHPNDG0_Msk               (0x01UL << VADC_BRSPND_CHPNDG0_Pos)                     /*!< VADC BRSPND: CHPNDG0 Mask               */
#define VADC_BRSPND_CHPNDG1_Pos               1                                                       /*!< VADC BRSPND: CHPNDG1 Position           */
#define VADC_BRSPND_CHPNDG1_Msk               (0x01UL << VADC_BRSPND_CHPNDG1_Pos)                     /*!< VADC BRSPND: CHPNDG1 Mask               */
#define VADC_BRSPND_CHPNDG2_Pos               2                                                       /*!< VADC BRSPND: CHPNDG2 Position           */
#define VADC_BRSPND_CHPNDG2_Msk               (0x01UL << VADC_BRSPND_CHPNDG2_Pos)                     /*!< VADC BRSPND: CHPNDG2 Mask               */
#define VADC_BRSPND_CHPNDG3_Pos               3                                                       /*!< VADC BRSPND: CHPNDG3 Position           */
#define VADC_BRSPND_CHPNDG3_Msk               (0x01UL << VADC_BRSPND_CHPNDG3_Pos)                     /*!< VADC BRSPND: CHPNDG3 Mask               */
#define VADC_BRSPND_CHPNDG4_Pos               4                                                       /*!< VADC BRSPND: CHPNDG4 Position           */
#define VADC_BRSPND_CHPNDG4_Msk               (0x01UL << VADC_BRSPND_CHPNDG4_Pos)                     /*!< VADC BRSPND: CHPNDG4 Mask               */
#define VADC_BRSPND_CHPNDG5_Pos               5                                                       /*!< VADC BRSPND: CHPNDG5 Position           */
#define VADC_BRSPND_CHPNDG5_Msk               (0x01UL << VADC_BRSPND_CHPNDG5_Pos)                     /*!< VADC BRSPND: CHPNDG5 Mask               */
#define VADC_BRSPND_CHPNDG6_Pos               6                                                       /*!< VADC BRSPND: CHPNDG6 Position           */
#define VADC_BRSPND_CHPNDG6_Msk               (0x01UL << VADC_BRSPND_CHPNDG6_Pos)                     /*!< VADC BRSPND: CHPNDG6 Mask               */
#define VADC_BRSPND_CHPNDG7_Pos               7                                                       /*!< VADC BRSPND: CHPNDG7 Position           */
#define VADC_BRSPND_CHPNDG7_Msk               (0x01UL << VADC_BRSPND_CHPNDG7_Pos)                     /*!< VADC BRSPND: CHPNDG7 Mask               */

/* --------------------------------  VADC_BRSCTRL  -------------------------------- */
#define VADC_BRSCTRL_SRCRESREG_Pos            0                                                       /*!< VADC BRSCTRL: SRCRESREG Position        */
#define VADC_BRSCTRL_SRCRESREG_Msk            (0x0fUL << VADC_BRSCTRL_SRCRESREG_Pos)                  /*!< VADC BRSCTRL: SRCRESREG Mask            */
#define VADC_BRSCTRL_XTSEL_Pos                8                                                       /*!< VADC BRSCTRL: XTSEL Position            */
#define VADC_BRSCTRL_XTSEL_Msk                (0x0fUL << VADC_BRSCTRL_XTSEL_Pos)                      /*!< VADC BRSCTRL: XTSEL Mask                */
#define VADC_BRSCTRL_XTLVL_Pos                12                                                      /*!< VADC BRSCTRL: XTLVL Position            */
#define VADC_BRSCTRL_XTLVL_Msk                (0x01UL << VADC_BRSCTRL_XTLVL_Pos)                      /*!< VADC BRSCTRL: XTLVL Mask                */
#define VADC_BRSCTRL_XTMODE_Pos               13                                                      /*!< VADC BRSCTRL: XTMODE Position           */
#define VADC_BRSCTRL_XTMODE_Msk               (0x03UL << VADC_BRSCTRL_XTMODE_Pos)                     /*!< VADC BRSCTRL: XTMODE Mask               */
#define VADC_BRSCTRL_XTWC_Pos                 15                                                      /*!< VADC BRSCTRL: XTWC Position             */
#define VADC_BRSCTRL_XTWC_Msk                 (0x01UL << VADC_BRSCTRL_XTWC_Pos)                       /*!< VADC BRSCTRL: XTWC Mask                 */
#define VADC_BRSCTRL_GTSEL_Pos                16                                                      /*!< VADC BRSCTRL: GTSEL Position            */
#define VADC_BRSCTRL_GTSEL_Msk                (0x0fUL << VADC_BRSCTRL_GTSEL_Pos)                      /*!< VADC BRSCTRL: GTSEL Mask                */
#define VADC_BRSCTRL_GTLVL_Pos                20                                                      /*!< VADC BRSCTRL: GTLVL Position            */
#define VADC_BRSCTRL_GTLVL_Msk                (0x01UL << VADC_BRSCTRL_GTLVL_Pos)                      /*!< VADC BRSCTRL: GTLVL Mask                */
#define VADC_BRSCTRL_GTWC_Pos                 23                                                      /*!< VADC BRSCTRL: GTWC Position             */
#define VADC_BRSCTRL_GTWC_Msk                 (0x01UL << VADC_BRSCTRL_GTWC_Pos)                       /*!< VADC BRSCTRL: GTWC Mask                 */

/* ---------------------------------  VADC_BRSMR  --------------------------------- */
#define VADC_BRSMR_ENGT_Pos                   0                                                       /*!< VADC BRSMR: ENGT Position               */
#define VADC_BRSMR_ENGT_Msk                   (0x03UL << VADC_BRSMR_ENGT_Pos)                         /*!< VADC BRSMR: ENGT Mask                   */
#define VADC_BRSMR_ENTR_Pos                   2                                                       /*!< VADC BRSMR: ENTR Position               */
#define VADC_BRSMR_ENTR_Msk                   (0x01UL << VADC_BRSMR_ENTR_Pos)                         /*!< VADC BRSMR: ENTR Mask                   */
#define VADC_BRSMR_ENSI_Pos                   3                                                       /*!< VADC BRSMR: ENSI Position               */
#define VADC_BRSMR_ENSI_Msk                   (0x01UL << VADC_BRSMR_ENSI_Pos)                         /*!< VADC BRSMR: ENSI Mask                   */
#define VADC_BRSMR_SCAN_Pos                   4                                                       /*!< VADC BRSMR: SCAN Position               */
#define VADC_BRSMR_SCAN_Msk                   (0x01UL << VADC_BRSMR_SCAN_Pos)                         /*!< VADC BRSMR: SCAN Mask                   */
#define VADC_BRSMR_LDM_Pos                    5                                                       /*!< VADC BRSMR: LDM Position                */
#define VADC_BRSMR_LDM_Msk                    (0x01UL << VADC_BRSMR_LDM_Pos)                          /*!< VADC BRSMR: LDM Mask                    */
#define VADC_BRSMR_REQGT_Pos                  7                                                       /*!< VADC BRSMR: REQGT Position              */
#define VADC_BRSMR_REQGT_Msk                  (0x01UL << VADC_BRSMR_REQGT_Pos)                        /*!< VADC BRSMR: REQGT Mask                  */
#define VADC_BRSMR_CLRPND_Pos                 8                                                       /*!< VADC BRSMR: CLRPND Position             */
#define VADC_BRSMR_CLRPND_Msk                 (0x01UL << VADC_BRSMR_CLRPND_Pos)                       /*!< VADC BRSMR: CLRPND Mask                 */
#define VADC_BRSMR_LDEV_Pos                   9                                                       /*!< VADC BRSMR: LDEV Position               */
#define VADC_BRSMR_LDEV_Msk                   (0x01UL << VADC_BRSMR_LDEV_Pos)                         /*!< VADC BRSMR: LDEV Mask                   */
#define VADC_BRSMR_RPTDIS_Pos                 16                                                      /*!< VADC BRSMR: RPTDIS Position             */
#define VADC_BRSMR_RPTDIS_Msk                 (0x01UL << VADC_BRSMR_RPTDIS_Pos)                       /*!< VADC BRSMR: RPTDIS Mask                 */

/* --------------------------------  VADC_GLOBRCR  -------------------------------- */
#define VADC_GLOBRCR_DRCTR_Pos                16                                                      /*!< VADC GLOBRCR: DRCTR Position            */
#define VADC_GLOBRCR_DRCTR_Msk                (0x0fUL << VADC_GLOBRCR_DRCTR_Pos)                      /*!< VADC GLOBRCR: DRCTR Mask                */
#define VADC_GLOBRCR_WFR_Pos                  24                                                      /*!< VADC GLOBRCR: WFR Position              */
#define VADC_GLOBRCR_WFR_Msk                  (0x01UL << VADC_GLOBRCR_WFR_Pos)                        /*!< VADC GLOBRCR: WFR Mask                  */
#define VADC_GLOBRCR_SRGEN_Pos                31                                                      /*!< VADC GLOBRCR: SRGEN Position            */
#define VADC_GLOBRCR_SRGEN_Msk                (0x01UL << VADC_GLOBRCR_SRGEN_Pos)                      /*!< VADC GLOBRCR: SRGEN Mask                */

/* --------------------------------  VADC_GLOBRES  -------------------------------- */
#define VADC_GLOBRES_RESULT_Pos               0                                                       /*!< VADC GLOBRES: RESULT Position           */
#define VADC_GLOBRES_RESULT_Msk               (0x0000ffffUL << VADC_GLOBRES_RESULT_Pos)               /*!< VADC GLOBRES: RESULT Mask               */
#define VADC_GLOBRES_GNR_Pos                  16                                                      /*!< VADC GLOBRES: GNR Position              */
#define VADC_GLOBRES_GNR_Msk                  (0x0fUL << VADC_GLOBRES_GNR_Pos)                        /*!< VADC GLOBRES: GNR Mask                  */
#define VADC_GLOBRES_CHNR_Pos                 20                                                      /*!< VADC GLOBRES: CHNR Position             */
#define VADC_GLOBRES_CHNR_Msk                 (0x1fUL << VADC_GLOBRES_CHNR_Pos)                       /*!< VADC GLOBRES: CHNR Mask                 */
#define VADC_GLOBRES_EMUX_Pos                 25                                                      /*!< VADC GLOBRES: EMUX Position             */
#define VADC_GLOBRES_EMUX_Msk                 (0x07UL << VADC_GLOBRES_EMUX_Pos)                       /*!< VADC GLOBRES: EMUX Mask                 */
#define VADC_GLOBRES_CRS_Pos                  28                                                      /*!< VADC GLOBRES: CRS Position              */
#define VADC_GLOBRES_CRS_Msk                  (0x03UL << VADC_GLOBRES_CRS_Pos)                        /*!< VADC GLOBRES: CRS Mask                  */
#define VADC_GLOBRES_FCR_Pos                  30                                                      /*!< VADC GLOBRES: FCR Position              */
#define VADC_GLOBRES_FCR_Msk                  (0x01UL << VADC_GLOBRES_FCR_Pos)                        /*!< VADC GLOBRES: FCR Mask                  */
#define VADC_GLOBRES_VF_Pos                   31                                                      /*!< VADC GLOBRES: VF Position               */
#define VADC_GLOBRES_VF_Msk                   (0x01UL << VADC_GLOBRES_VF_Pos)                         /*!< VADC GLOBRES: VF Mask                   */

/* --------------------------------  VADC_GLOBRESD  ------------------------------- */
#define VADC_GLOBRESD_RESULT_Pos              0                                                       /*!< VADC GLOBRESD: RESULT Position          */
#define VADC_GLOBRESD_RESULT_Msk              (0x0000ffffUL << VADC_GLOBRESD_RESULT_Pos)              /*!< VADC GLOBRESD: RESULT Mask              */
#define VADC_GLOBRESD_GNR_Pos                 16                                                      /*!< VADC GLOBRESD: GNR Position             */
#define VADC_GLOBRESD_GNR_Msk                 (0x0fUL << VADC_GLOBRESD_GNR_Pos)                       /*!< VADC GLOBRESD: GNR Mask                 */
#define VADC_GLOBRESD_CHNR_Pos                20                                                      /*!< VADC GLOBRESD: CHNR Position            */
#define VADC_GLOBRESD_CHNR_Msk                (0x1fUL << VADC_GLOBRESD_CHNR_Pos)                      /*!< VADC GLOBRESD: CHNR Mask                */
#define VADC_GLOBRESD_EMUX_Pos                25                                                      /*!< VADC GLOBRESD: EMUX Position            */
#define VADC_GLOBRESD_EMUX_Msk                (0x07UL << VADC_GLOBRESD_EMUX_Pos)                      /*!< VADC GLOBRESD: EMUX Mask                */
#define VADC_GLOBRESD_CRS_Pos                 28                                                      /*!< VADC GLOBRESD: CRS Position             */
#define VADC_GLOBRESD_CRS_Msk                 (0x03UL << VADC_GLOBRESD_CRS_Pos)                       /*!< VADC GLOBRESD: CRS Mask                 */
#define VADC_GLOBRESD_FCR_Pos                 30                                                      /*!< VADC GLOBRESD: FCR Position             */
#define VADC_GLOBRESD_FCR_Msk                 (0x01UL << VADC_GLOBRESD_FCR_Pos)                       /*!< VADC GLOBRESD: FCR Mask                 */
#define VADC_GLOBRESD_VF_Pos                  31                                                      /*!< VADC GLOBRESD: VF Position              */
#define VADC_GLOBRESD_VF_Msk                  (0x01UL << VADC_GLOBRESD_VF_Pos)                        /*!< VADC GLOBRESD: VF Mask                  */


/* ================================================================================ */
/* ================           Group 'SHS' Position & Mask          ================ */
/* ================================================================================ */


/* -----------------------------------  SHS_ID  ----------------------------------- */
#define SHS_ID_MOD_REV_Pos                    0                                                       /*!< SHS ID: MOD_REV Position                */
#define SHS_ID_MOD_REV_Msk                    (0x000000ffUL << SHS_ID_MOD_REV_Pos)                    /*!< SHS ID: MOD_REV Mask                    */
#define SHS_ID_MOD_TYPE_Pos                   8                                                       /*!< SHS ID: MOD_TYPE Position               */
#define SHS_ID_MOD_TYPE_Msk                   (0x000000ffUL << SHS_ID_MOD_TYPE_Pos)                   /*!< SHS ID: MOD_TYPE Mask                   */
#define SHS_ID_MOD_NUMBER_Pos                 16                                                      /*!< SHS ID: MOD_NUMBER Position             */
#define SHS_ID_MOD_NUMBER_Msk                 (0x0000ffffUL << SHS_ID_MOD_NUMBER_Pos)                 /*!< SHS ID: MOD_NUMBER Mask                 */

/* ---------------------------------  SHS_SHSCFG  --------------------------------- */
#define SHS_SHSCFG_DIVS_Pos                   0                                                       /*!< SHS SHSCFG: DIVS Position               */
#define SHS_SHSCFG_DIVS_Msk                   (0x0fUL << SHS_SHSCFG_DIVS_Pos)                         /*!< SHS SHSCFG: DIVS Mask                   */
#define SHS_SHSCFG_AREF_Pos                   10                                                      /*!< SHS SHSCFG: AREF Position               */
#define SHS_SHSCFG_AREF_Msk                   (0x03UL << SHS_SHSCFG_AREF_Pos)                         /*!< SHS SHSCFG: AREF Mask                   */
#define SHS_SHSCFG_ANOFF_Pos                  12                                                      /*!< SHS SHSCFG: ANOFF Position              */
#define SHS_SHSCFG_ANOFF_Msk                  (0x01UL << SHS_SHSCFG_ANOFF_Pos)                        /*!< SHS SHSCFG: ANOFF Mask                  */
#define SHS_SHSCFG_ANRDY_Pos                  14                                                      /*!< SHS SHSCFG: ANRDY Position              */
#define SHS_SHSCFG_ANRDY_Msk                  (0x01UL << SHS_SHSCFG_ANRDY_Pos)                        /*!< SHS SHSCFG: ANRDY Mask                  */
#define SHS_SHSCFG_SCWC_Pos                   15                                                      /*!< SHS SHSCFG: SCWC Position               */
#define SHS_SHSCFG_SCWC_Msk                   (0x01UL << SHS_SHSCFG_SCWC_Pos)                         /*!< SHS SHSCFG: SCWC Mask                   */
#define SHS_SHSCFG_SP0_Pos                    16                                                      /*!< SHS SHSCFG: SP0 Position                */
#define SHS_SHSCFG_SP0_Msk                    (0x01UL << SHS_SHSCFG_SP0_Pos)                          /*!< SHS SHSCFG: SP0 Mask                    */
#define SHS_SHSCFG_SP1_Pos                    17                                                      /*!< SHS SHSCFG: SP1 Position                */
#define SHS_SHSCFG_SP1_Msk                    (0x01UL << SHS_SHSCFG_SP1_Pos)                          /*!< SHS SHSCFG: SP1 Mask                    */
#define SHS_SHSCFG_TC_Pos                     24                                                      /*!< SHS SHSCFG: TC Position                 */
#define SHS_SHSCFG_TC_Msk                     (0x0fUL << SHS_SHSCFG_TC_Pos)                           /*!< SHS SHSCFG: TC Mask                     */
#define SHS_SHSCFG_STATE_Pos                  28                                                      /*!< SHS SHSCFG: STATE Position              */
#define SHS_SHSCFG_STATE_Msk                  (0x0fUL << SHS_SHSCFG_STATE_Pos)                        /*!< SHS SHSCFG: STATE Mask                  */

/* ---------------------------------  SHS_STEPCFG  -------------------------------- */
#define SHS_STEPCFG_KSEL0_Pos                 0                                                       /*!< SHS STEPCFG: KSEL0 Position             */
#define SHS_STEPCFG_KSEL0_Msk                 (0x07UL << SHS_STEPCFG_KSEL0_Pos)                       /*!< SHS STEPCFG: KSEL0 Mask                 */
#define SHS_STEPCFG_SEN0_Pos                  3                                                       /*!< SHS STEPCFG: SEN0 Position              */
#define SHS_STEPCFG_SEN0_Msk                  (0x01UL << SHS_STEPCFG_SEN0_Pos)                        /*!< SHS STEPCFG: SEN0 Mask                  */
#define SHS_STEPCFG_KSEL1_Pos                 4                                                       /*!< SHS STEPCFG: KSEL1 Position             */
#define SHS_STEPCFG_KSEL1_Msk                 (0x07UL << SHS_STEPCFG_KSEL1_Pos)                       /*!< SHS STEPCFG: KSEL1 Mask                 */
#define SHS_STEPCFG_SEN1_Pos                  7                                                       /*!< SHS STEPCFG: SEN1 Position              */
#define SHS_STEPCFG_SEN1_Msk                  (0x01UL << SHS_STEPCFG_SEN1_Pos)                        /*!< SHS STEPCFG: SEN1 Mask                  */
#define SHS_STEPCFG_KSEL2_Pos                 8                                                       /*!< SHS STEPCFG: KSEL2 Position             */
#define SHS_STEPCFG_KSEL2_Msk                 (0x07UL << SHS_STEPCFG_KSEL2_Pos)                       /*!< SHS STEPCFG: KSEL2 Mask                 */
#define SHS_STEPCFG_SEN2_Pos                  11                                                      /*!< SHS STEPCFG: SEN2 Position              */
#define SHS_STEPCFG_SEN2_Msk                  (0x01UL << SHS_STEPCFG_SEN2_Pos)                        /*!< SHS STEPCFG: SEN2 Mask                  */
#define SHS_STEPCFG_KSEL3_Pos                 12                                                      /*!< SHS STEPCFG: KSEL3 Position             */
#define SHS_STEPCFG_KSEL3_Msk                 (0x07UL << SHS_STEPCFG_KSEL3_Pos)                       /*!< SHS STEPCFG: KSEL3 Mask                 */
#define SHS_STEPCFG_SEN3_Pos                  15                                                      /*!< SHS STEPCFG: SEN3 Position              */
#define SHS_STEPCFG_SEN3_Msk                  (0x01UL << SHS_STEPCFG_SEN3_Pos)                        /*!< SHS STEPCFG: SEN3 Mask                  */
#define SHS_STEPCFG_KSEL4_Pos                 16                                                      /*!< SHS STEPCFG: KSEL4 Position             */
#define SHS_STEPCFG_KSEL4_Msk                 (0x07UL << SHS_STEPCFG_KSEL4_Pos)                       /*!< SHS STEPCFG: KSEL4 Mask                 */
#define SHS_STEPCFG_SEN4_Pos                  19                                                      /*!< SHS STEPCFG: SEN4 Position              */
#define SHS_STEPCFG_SEN4_Msk                  (0x01UL << SHS_STEPCFG_SEN4_Pos)                        /*!< SHS STEPCFG: SEN4 Mask                  */
#define SHS_STEPCFG_KSEL5_Pos                 20                                                      /*!< SHS STEPCFG: KSEL5 Position             */
#define SHS_STEPCFG_KSEL5_Msk                 (0x07UL << SHS_STEPCFG_KSEL5_Pos)                       /*!< SHS STEPCFG: KSEL5 Mask                 */
#define SHS_STEPCFG_SEN5_Pos                  23                                                      /*!< SHS STEPCFG: SEN5 Position              */
#define SHS_STEPCFG_SEN5_Msk                  (0x01UL << SHS_STEPCFG_SEN5_Pos)                        /*!< SHS STEPCFG: SEN5 Mask                  */
#define SHS_STEPCFG_KSEL6_Pos                 24                                                      /*!< SHS STEPCFG: KSEL6 Position             */
#define SHS_STEPCFG_KSEL6_Msk                 (0x07UL << SHS_STEPCFG_KSEL6_Pos)                       /*!< SHS STEPCFG: KSEL6 Mask                 */
#define SHS_STEPCFG_SEN6_Pos                  27                                                      /*!< SHS STEPCFG: SEN6 Position              */
#define SHS_STEPCFG_SEN6_Msk                  (0x01UL << SHS_STEPCFG_SEN6_Pos)                        /*!< SHS STEPCFG: SEN6 Mask                  */
#define SHS_STEPCFG_KSEL7_Pos                 28                                                      /*!< SHS STEPCFG: KSEL7 Position             */
#define SHS_STEPCFG_KSEL7_Msk                 (0x07UL << SHS_STEPCFG_KSEL7_Pos)                       /*!< SHS STEPCFG: KSEL7 Mask                 */
#define SHS_STEPCFG_SEN7_Pos                  31                                                      /*!< SHS STEPCFG: SEN7 Position              */
#define SHS_STEPCFG_SEN7_Msk                  (0x01UL << SHS_STEPCFG_SEN7_Pos)                        /*!< SHS STEPCFG: SEN7 Mask                  */

/* ----------------------------------  SHS_LOOP  ---------------------------------- */
#define SHS_LOOP_LPCH0_Pos                    0                                                       /*!< SHS LOOP: LPCH0 Position                */
#define SHS_LOOP_LPCH0_Msk                    (0x1fUL << SHS_LOOP_LPCH0_Pos)                          /*!< SHS LOOP: LPCH0 Mask                    */
#define SHS_LOOP_LPSH0_Pos                    8                                                       /*!< SHS LOOP: LPSH0 Position                */
#define SHS_LOOP_LPSH0_Msk                    (0x01UL << SHS_LOOP_LPSH0_Pos)                          /*!< SHS LOOP: LPSH0 Mask                    */
#define SHS_LOOP_LPEN0_Pos                    15                                                      /*!< SHS LOOP: LPEN0 Position                */
#define SHS_LOOP_LPEN0_Msk                    (0x01UL << SHS_LOOP_LPEN0_Pos)                          /*!< SHS LOOP: LPEN0 Mask                    */
#define SHS_LOOP_LPCH1_Pos                    16                                                      /*!< SHS LOOP: LPCH1 Position                */
#define SHS_LOOP_LPCH1_Msk                    (0x1fUL << SHS_LOOP_LPCH1_Pos)                          /*!< SHS LOOP: LPCH1 Mask                    */
#define SHS_LOOP_LPSH1_Pos                    24                                                      /*!< SHS LOOP: LPSH1 Position                */
#define SHS_LOOP_LPSH1_Msk                    (0x01UL << SHS_LOOP_LPSH1_Pos)                          /*!< SHS LOOP: LPSH1 Mask                    */
#define SHS_LOOP_LPEN1_Pos                    31                                                      /*!< SHS LOOP: LPEN1 Position                */
#define SHS_LOOP_LPEN1_Msk                    (0x01UL << SHS_LOOP_LPEN1_Pos)                          /*!< SHS LOOP: LPEN1 Mask                    */

/* ---------------------------------  SHS_TIMCFG0  -------------------------------- */
#define SHS_TIMCFG0_AT_Pos                    0                                                       /*!< SHS TIMCFG0: AT Position                */
#define SHS_TIMCFG0_AT_Msk                    (0x01UL << SHS_TIMCFG0_AT_Pos)                          /*!< SHS TIMCFG0: AT Mask                    */
#define SHS_TIMCFG0_FCRT_Pos                  4                                                       /*!< SHS TIMCFG0: FCRT Position              */
#define SHS_TIMCFG0_FCRT_Msk                  (0x0fUL << SHS_TIMCFG0_FCRT_Pos)                        /*!< SHS TIMCFG0: FCRT Mask                  */
#define SHS_TIMCFG0_SST_Pos                   8                                                       /*!< SHS TIMCFG0: SST Position               */
#define SHS_TIMCFG0_SST_Msk                   (0x3fUL << SHS_TIMCFG0_SST_Pos)                         /*!< SHS TIMCFG0: SST Mask                   */
#define SHS_TIMCFG0_TGEN_Pos                  16                                                      /*!< SHS TIMCFG0: TGEN Position              */
#define SHS_TIMCFG0_TGEN_Msk                  (0x00003fffUL << SHS_TIMCFG0_TGEN_Pos)                  /*!< SHS TIMCFG0: TGEN Mask                  */

/* ---------------------------------  SHS_TIMCFG1  -------------------------------- */
#define SHS_TIMCFG1_AT_Pos                    0                                                       /*!< SHS TIMCFG1: AT Position                */
#define SHS_TIMCFG1_AT_Msk                    (0x01UL << SHS_TIMCFG1_AT_Pos)                          /*!< SHS TIMCFG1: AT Mask                    */
#define SHS_TIMCFG1_FCRT_Pos                  4                                                       /*!< SHS TIMCFG1: FCRT Position              */
#define SHS_TIMCFG1_FCRT_Msk                  (0x0fUL << SHS_TIMCFG1_FCRT_Pos)                        /*!< SHS TIMCFG1: FCRT Mask                  */
#define SHS_TIMCFG1_SST_Pos                   8                                                       /*!< SHS TIMCFG1: SST Position               */
#define SHS_TIMCFG1_SST_Msk                   (0x3fUL << SHS_TIMCFG1_SST_Pos)                         /*!< SHS TIMCFG1: SST Mask                   */
#define SHS_TIMCFG1_TGEN_Pos                  16                                                      /*!< SHS TIMCFG1: TGEN Position              */
#define SHS_TIMCFG1_TGEN_Msk                  (0x00003fffUL << SHS_TIMCFG1_TGEN_Pos)                  /*!< SHS TIMCFG1: TGEN Mask                  */

/* ---------------------------------  SHS_CALCTR  --------------------------------- */
#define SHS_CALCTR_CALORD_Pos                 0                                                       /*!< SHS CALCTR: CALORD Position             */
#define SHS_CALCTR_CALORD_Msk                 (0x01UL << SHS_CALCTR_CALORD_Pos)                       /*!< SHS CALCTR: CALORD Mask                 */
#define SHS_CALCTR_CALGNSTC_Pos               8                                                       /*!< SHS CALCTR: CALGNSTC Position           */
#define SHS_CALCTR_CALGNSTC_Msk               (0x3fUL << SHS_CALCTR_CALGNSTC_Pos)                     /*!< SHS CALCTR: CALGNSTC Mask               */
#define SHS_CALCTR_SUCALVAL_Pos               16                                                      /*!< SHS CALCTR: SUCALVAL Position           */
#define SHS_CALCTR_SUCALVAL_Msk               (0x7fUL << SHS_CALCTR_SUCALVAL_Pos)                     /*!< SHS CALCTR: SUCALVAL Mask               */
#define SHS_CALCTR_CALMAX_Pos                 24                                                      /*!< SHS CALCTR: CALMAX Position             */
#define SHS_CALCTR_CALMAX_Msk                 (0x3fUL << SHS_CALCTR_CALMAX_Pos)                       /*!< SHS CALCTR: CALMAX Mask                 */
#define SHS_CALCTR_SUCAL_Pos                  31                                                      /*!< SHS CALCTR: SUCAL Position              */
#define SHS_CALCTR_SUCAL_Msk                  (0x01UL << SHS_CALCTR_SUCAL_Pos)                        /*!< SHS CALCTR: SUCAL Mask                  */

/* ---------------------------------  SHS_CALGC0  --------------------------------- */
#define SHS_CALGC0_CALGNVALS_Pos              0                                                       /*!< SHS CALGC0: CALGNVALS Position          */
#define SHS_CALGC0_CALGNVALS_Msk              (0x00003fffUL << SHS_CALGC0_CALGNVALS_Pos)              /*!< SHS CALGC0: CALGNVALS Mask              */
#define SHS_CALGC0_GNSWC_Pos                  15                                                      /*!< SHS CALGC0: GNSWC Position              */
#define SHS_CALGC0_GNSWC_Msk                  (0x01UL << SHS_CALGC0_GNSWC_Pos)                        /*!< SHS CALGC0: GNSWC Mask                  */
#define SHS_CALGC0_CALGNVALA_Pos              16                                                      /*!< SHS CALGC0: CALGNVALA Position          */
#define SHS_CALGC0_CALGNVALA_Msk              (0x00003fffUL << SHS_CALGC0_CALGNVALA_Pos)              /*!< SHS CALGC0: CALGNVALA Mask              */
#define SHS_CALGC0_GNAWC_Pos                  31                                                      /*!< SHS CALGC0: GNAWC Position              */
#define SHS_CALGC0_GNAWC_Msk                  (0x01UL << SHS_CALGC0_GNAWC_Pos)                        /*!< SHS CALGC0: GNAWC Mask                  */

/* ---------------------------------  SHS_CALGC1  --------------------------------- */
#define SHS_CALGC1_CALGNVALS_Pos              0                                                       /*!< SHS CALGC1: CALGNVALS Position          */
#define SHS_CALGC1_CALGNVALS_Msk              (0x00003fffUL << SHS_CALGC1_CALGNVALS_Pos)              /*!< SHS CALGC1: CALGNVALS Mask              */
#define SHS_CALGC1_GNSWC_Pos                  15                                                      /*!< SHS CALGC1: GNSWC Position              */
#define SHS_CALGC1_GNSWC_Msk                  (0x01UL << SHS_CALGC1_GNSWC_Pos)                        /*!< SHS CALGC1: GNSWC Mask                  */
#define SHS_CALGC1_CALGNVALA_Pos              16                                                      /*!< SHS CALGC1: CALGNVALA Position          */
#define SHS_CALGC1_CALGNVALA_Msk              (0x00003fffUL << SHS_CALGC1_CALGNVALA_Pos)              /*!< SHS CALGC1: CALGNVALA Mask              */
#define SHS_CALGC1_GNAWC_Pos                  31                                                      /*!< SHS CALGC1: GNAWC Position              */
#define SHS_CALGC1_GNAWC_Msk                  (0x01UL << SHS_CALGC1_GNAWC_Pos)                        /*!< SHS CALGC1: GNAWC Mask                  */

/* ---------------------------------  SHS_GNCTR00  -------------------------------- */
#define SHS_GNCTR00_GAIN0_Pos                 0                                                       /*!< SHS GNCTR00: GAIN0 Position             */
#define SHS_GNCTR00_GAIN0_Msk                 (0x0fUL << SHS_GNCTR00_GAIN0_Pos)                       /*!< SHS GNCTR00: GAIN0 Mask                 */
#define SHS_GNCTR00_GAIN1_Pos                 4                                                       /*!< SHS GNCTR00: GAIN1 Position             */
#define SHS_GNCTR00_GAIN1_Msk                 (0x0fUL << SHS_GNCTR00_GAIN1_Pos)                       /*!< SHS GNCTR00: GAIN1 Mask                 */
#define SHS_GNCTR00_GAIN2_Pos                 8                                                       /*!< SHS GNCTR00: GAIN2 Position             */
#define SHS_GNCTR00_GAIN2_Msk                 (0x0fUL << SHS_GNCTR00_GAIN2_Pos)                       /*!< SHS GNCTR00: GAIN2 Mask                 */
#define SHS_GNCTR00_GAIN3_Pos                 12                                                      /*!< SHS GNCTR00: GAIN3 Position             */
#define SHS_GNCTR00_GAIN3_Msk                 (0x0fUL << SHS_GNCTR00_GAIN3_Pos)                       /*!< SHS GNCTR00: GAIN3 Mask                 */
#define SHS_GNCTR00_GAIN4_Pos                 16                                                      /*!< SHS GNCTR00: GAIN4 Position             */
#define SHS_GNCTR00_GAIN4_Msk                 (0x0fUL << SHS_GNCTR00_GAIN4_Pos)                       /*!< SHS GNCTR00: GAIN4 Mask                 */
#define SHS_GNCTR00_GAIN5_Pos                 20                                                      /*!< SHS GNCTR00: GAIN5 Position             */
#define SHS_GNCTR00_GAIN5_Msk                 (0x0fUL << SHS_GNCTR00_GAIN5_Pos)                       /*!< SHS GNCTR00: GAIN5 Mask                 */
#define SHS_GNCTR00_GAIN6_Pos                 24                                                      /*!< SHS GNCTR00: GAIN6 Position             */
#define SHS_GNCTR00_GAIN6_Msk                 (0x0fUL << SHS_GNCTR00_GAIN6_Pos)                       /*!< SHS GNCTR00: GAIN6 Mask                 */
#define SHS_GNCTR00_GAIN7_Pos                 28                                                      /*!< SHS GNCTR00: GAIN7 Position             */
#define SHS_GNCTR00_GAIN7_Msk                 (0x0fUL << SHS_GNCTR00_GAIN7_Pos)                       /*!< SHS GNCTR00: GAIN7 Mask                 */

/* ---------------------------------  SHS_GNCTR10  -------------------------------- */
#define SHS_GNCTR10_GAIN0_Pos                 0                                                       /*!< SHS GNCTR10: GAIN0 Position             */
#define SHS_GNCTR10_GAIN0_Msk                 (0x0fUL << SHS_GNCTR10_GAIN0_Pos)                       /*!< SHS GNCTR10: GAIN0 Mask                 */
#define SHS_GNCTR10_GAIN1_Pos                 4                                                       /*!< SHS GNCTR10: GAIN1 Position             */
#define SHS_GNCTR10_GAIN1_Msk                 (0x0fUL << SHS_GNCTR10_GAIN1_Pos)                       /*!< SHS GNCTR10: GAIN1 Mask                 */
#define SHS_GNCTR10_GAIN2_Pos                 8                                                       /*!< SHS GNCTR10: GAIN2 Position             */
#define SHS_GNCTR10_GAIN2_Msk                 (0x0fUL << SHS_GNCTR10_GAIN2_Pos)                       /*!< SHS GNCTR10: GAIN2 Mask                 */
#define SHS_GNCTR10_GAIN3_Pos                 12                                                      /*!< SHS GNCTR10: GAIN3 Position             */
#define SHS_GNCTR10_GAIN3_Msk                 (0x0fUL << SHS_GNCTR10_GAIN3_Pos)                       /*!< SHS GNCTR10: GAIN3 Mask                 */
#define SHS_GNCTR10_GAIN4_Pos                 16                                                      /*!< SHS GNCTR10: GAIN4 Position             */
#define SHS_GNCTR10_GAIN4_Msk                 (0x0fUL << SHS_GNCTR10_GAIN4_Pos)                       /*!< SHS GNCTR10: GAIN4 Mask                 */
#define SHS_GNCTR10_GAIN5_Pos                 20                                                      /*!< SHS GNCTR10: GAIN5 Position             */
#define SHS_GNCTR10_GAIN5_Msk                 (0x0fUL << SHS_GNCTR10_GAIN5_Pos)                       /*!< SHS GNCTR10: GAIN5 Mask                 */
#define SHS_GNCTR10_GAIN6_Pos                 24                                                      /*!< SHS GNCTR10: GAIN6 Position             */
#define SHS_GNCTR10_GAIN6_Msk                 (0x0fUL << SHS_GNCTR10_GAIN6_Pos)                       /*!< SHS GNCTR10: GAIN6 Mask                 */
#define SHS_GNCTR10_GAIN7_Pos                 28                                                      /*!< SHS GNCTR10: GAIN7 Position             */
#define SHS_GNCTR10_GAIN7_Msk                 (0x0fUL << SHS_GNCTR10_GAIN7_Pos)                       /*!< SHS GNCTR10: GAIN7 Mask                 */


/* ================================================================================ */
/* ================         struct 'PORT0' Position & Mask         ================ */
/* ================================================================================ */


/* ----------------------------------  PORT0_OUT  --------------------------------- */
#define PORT0_OUT_P0_Pos                      0                                                       /*!< PORT0 OUT: P0 Position                  */
#define PORT0_OUT_P0_Msk                      (0x01UL << PORT0_OUT_P0_Pos)                            /*!< PORT0 OUT: P0 Mask                      */
#define PORT0_OUT_P1_Pos                      1                                                       /*!< PORT0 OUT: P1 Position                  */
#define PORT0_OUT_P1_Msk                      (0x01UL << PORT0_OUT_P1_Pos)                            /*!< PORT0 OUT: P1 Mask                      */
#define PORT0_OUT_P2_Pos                      2                                                       /*!< PORT0 OUT: P2 Position                  */
#define PORT0_OUT_P2_Msk                      (0x01UL << PORT0_OUT_P2_Pos)                            /*!< PORT0 OUT: P2 Mask                      */
#define PORT0_OUT_P3_Pos                      3                                                       /*!< PORT0 OUT: P3 Position                  */
#define PORT0_OUT_P3_Msk                      (0x01UL << PORT0_OUT_P3_Pos)                            /*!< PORT0 OUT: P3 Mask                      */
#define PORT0_OUT_P4_Pos                      4                                                       /*!< PORT0 OUT: P4 Position                  */
#define PORT0_OUT_P4_Msk                      (0x01UL << PORT0_OUT_P4_Pos)                            /*!< PORT0 OUT: P4 Mask                      */
#define PORT0_OUT_P5_Pos                      5                                                       /*!< PORT0 OUT: P5 Position                  */
#define PORT0_OUT_P5_Msk                      (0x01UL << PORT0_OUT_P5_Pos)                            /*!< PORT0 OUT: P5 Mask                      */
#define PORT0_OUT_P6_Pos                      6                                                       /*!< PORT0 OUT: P6 Position                  */
#define PORT0_OUT_P6_Msk                      (0x01UL << PORT0_OUT_P6_Pos)                            /*!< PORT0 OUT: P6 Mask                      */
#define PORT0_OUT_P7_Pos                      7                                                       /*!< PORT0 OUT: P7 Position                  */
#define PORT0_OUT_P7_Msk                      (0x01UL << PORT0_OUT_P7_Pos)                            /*!< PORT0 OUT: P7 Mask                      */
#define PORT0_OUT_P8_Pos                      8                                                       /*!< PORT0 OUT: P8 Position                  */
#define PORT0_OUT_P8_Msk                      (0x01UL << PORT0_OUT_P8_Pos)                            /*!< PORT0 OUT: P8 Mask                      */
#define PORT0_OUT_P9_Pos                      9                                                       /*!< PORT0 OUT: P9 Position                  */
#define PORT0_OUT_P9_Msk                      (0x01UL << PORT0_OUT_P9_Pos)                            /*!< PORT0 OUT: P9 Mask                      */
#define PORT0_OUT_P10_Pos                     10                                                      /*!< PORT0 OUT: P10 Position                 */
#define PORT0_OUT_P10_Msk                     (0x01UL << PORT0_OUT_P10_Pos)                           /*!< PORT0 OUT: P10 Mask                     */
#define PORT0_OUT_P11_Pos                     11                                                      /*!< PORT0 OUT: P11 Position                 */
#define PORT0_OUT_P11_Msk                     (0x01UL << PORT0_OUT_P11_Pos)                           /*!< PORT0 OUT: P11 Mask                     */
#define PORT0_OUT_P12_Pos                     12                                                      /*!< PORT0 OUT: P12 Position                 */
#define PORT0_OUT_P12_Msk                     (0x01UL << PORT0_OUT_P12_Pos)                           /*!< PORT0 OUT: P12 Mask                     */
#define PORT0_OUT_P13_Pos                     13                                                      /*!< PORT0 OUT: P13 Position                 */
#define PORT0_OUT_P13_Msk                     (0x01UL << PORT0_OUT_P13_Pos)                           /*!< PORT0 OUT: P13 Mask                     */
#define PORT0_OUT_P14_Pos                     14                                                      /*!< PORT0 OUT: P14 Position                 */
#define PORT0_OUT_P14_Msk                     (0x01UL << PORT0_OUT_P14_Pos)                           /*!< PORT0 OUT: P14 Mask                     */
#define PORT0_OUT_P15_Pos                     15                                                      /*!< PORT0 OUT: P15 Position                 */
#define PORT0_OUT_P15_Msk                     (0x01UL << PORT0_OUT_P15_Pos)                           /*!< PORT0 OUT: P15 Mask                     */

/* ----------------------------------  PORT0_OMR  --------------------------------- */
#define PORT0_OMR_PS0_Pos                     0                                                       /*!< PORT0 OMR: PS0 Position                 */
#define PORT0_OMR_PS0_Msk                     (0x01UL << PORT0_OMR_PS0_Pos)                           /*!< PORT0 OMR: PS0 Mask                     */
#define PORT0_OMR_PS1_Pos                     1                                                       /*!< PORT0 OMR: PS1 Position                 */
#define PORT0_OMR_PS1_Msk                     (0x01UL << PORT0_OMR_PS1_Pos)                           /*!< PORT0 OMR: PS1 Mask                     */
#define PORT0_OMR_PS2_Pos                     2                                                       /*!< PORT0 OMR: PS2 Position                 */
#define PORT0_OMR_PS2_Msk                     (0x01UL << PORT0_OMR_PS2_Pos)                           /*!< PORT0 OMR: PS2 Mask                     */
#define PORT0_OMR_PS3_Pos                     3                                                       /*!< PORT0 OMR: PS3 Position                 */
#define PORT0_OMR_PS3_Msk                     (0x01UL << PORT0_OMR_PS3_Pos)                           /*!< PORT0 OMR: PS3 Mask                     */
#define PORT0_OMR_PS4_Pos                     4                                                       /*!< PORT0 OMR: PS4 Position                 */
#define PORT0_OMR_PS4_Msk                     (0x01UL << PORT0_OMR_PS4_Pos)                           /*!< PORT0 OMR: PS4 Mask                     */
#define PORT0_OMR_PS5_Pos                     5                                                       /*!< PORT0 OMR: PS5 Position                 */
#define PORT0_OMR_PS5_Msk                     (0x01UL << PORT0_OMR_PS5_Pos)                           /*!< PORT0 OMR: PS5 Mask                     */
#define PORT0_OMR_PS6_Pos                     6                                                       /*!< PORT0 OMR: PS6 Position                 */
#define PORT0_OMR_PS6_Msk                     (0x01UL << PORT0_OMR_PS6_Pos)                           /*!< PORT0 OMR: PS6 Mask                     */
#define PORT0_OMR_PS7_Pos                     7                                                       /*!< PORT0 OMR: PS7 Position                 */
#define PORT0_OMR_PS7_Msk                     (0x01UL << PORT0_OMR_PS7_Pos)                           /*!< PORT0 OMR: PS7 Mask                     */
#define PORT0_OMR_PS8_Pos                     8                                                       /*!< PORT0 OMR: PS8 Position                 */
#define PORT0_OMR_PS8_Msk                     (0x01UL << PORT0_OMR_PS8_Pos)                           /*!< PORT0 OMR: PS8 Mask                     */
#define PORT0_OMR_PS9_Pos                     9                                                       /*!< PORT0 OMR: PS9 Position                 */
#define PORT0_OMR_PS9_Msk                     (0x01UL << PORT0_OMR_PS9_Pos)                           /*!< PORT0 OMR: PS9 Mask                     */
#define PORT0_OMR_PS10_Pos                    10                                                      /*!< PORT0 OMR: PS10 Position                */
#define PORT0_OMR_PS10_Msk                    (0x01UL << PORT0_OMR_PS10_Pos)                          /*!< PORT0 OMR: PS10 Mask                    */
#define PORT0_OMR_PS11_Pos                    11                                                      /*!< PORT0 OMR: PS11 Position                */
#define PORT0_OMR_PS11_Msk                    (0x01UL << PORT0_OMR_PS11_Pos)                          /*!< PORT0 OMR: PS11 Mask                    */
#define PORT0_OMR_PS12_Pos                    12                                                      /*!< PORT0 OMR: PS12 Position                */
#define PORT0_OMR_PS12_Msk                    (0x01UL << PORT0_OMR_PS12_Pos)                          /*!< PORT0 OMR: PS12 Mask                    */
#define PORT0_OMR_PS13_Pos                    13                                                      /*!< PORT0 OMR: PS13 Position                */
#define PORT0_OMR_PS13_Msk                    (0x01UL << PORT0_OMR_PS13_Pos)                          /*!< PORT0 OMR: PS13 Mask                    */
#define PORT0_OMR_PS14_Pos                    14                                                      /*!< PORT0 OMR: PS14 Position                */
#define PORT0_OMR_PS14_Msk                    (0x01UL << PORT0_OMR_PS14_Pos)                          /*!< PORT0 OMR: PS14 Mask                    */
#define PORT0_OMR_PS15_Pos                    15                                                      /*!< PORT0 OMR: PS15 Position                */
#define PORT0_OMR_PS15_Msk                    (0x01UL << PORT0_OMR_PS15_Pos)                          /*!< PORT0 OMR: PS15 Mask                    */
#define PORT0_OMR_PR0_Pos                     16                                                      /*!< PORT0 OMR: PR0 Position                 */
#define PORT0_OMR_PR0_Msk                     (0x01UL << PORT0_OMR_PR0_Pos)                           /*!< PORT0 OMR: PR0 Mask                     */
#define PORT0_OMR_PR1_Pos                     17                                                      /*!< PORT0 OMR: PR1 Position                 */
#define PORT0_OMR_PR1_Msk                     (0x01UL << PORT0_OMR_PR1_Pos)                           /*!< PORT0 OMR: PR1 Mask                     */
#define PORT0_OMR_PR2_Pos                     18                                                      /*!< PORT0 OMR: PR2 Position                 */
#define PORT0_OMR_PR2_Msk                     (0x01UL << PORT0_OMR_PR2_Pos)                           /*!< PORT0 OMR: PR2 Mask                     */
#define PORT0_OMR_PR3_Pos                     19                                                      /*!< PORT0 OMR: PR3 Position                 */
#define PORT0_OMR_PR3_Msk                     (0x01UL << PORT0_OMR_PR3_Pos)                           /*!< PORT0 OMR: PR3 Mask                     */
#define PORT0_OMR_PR4_Pos                     20                                                      /*!< PORT0 OMR: PR4 Position                 */
#define PORT0_OMR_PR4_Msk                     (0x01UL << PORT0_OMR_PR4_Pos)                           /*!< PORT0 OMR: PR4 Mask                     */
#define PORT0_OMR_PR5_Pos                     21                                                      /*!< PORT0 OMR: PR5 Position                 */
#define PORT0_OMR_PR5_Msk                     (0x01UL << PORT0_OMR_PR5_Pos)                           /*!< PORT0 OMR: PR5 Mask                     */
#define PORT0_OMR_PR6_Pos                     22                                                      /*!< PORT0 OMR: PR6 Position                 */
#define PORT0_OMR_PR6_Msk                     (0x01UL << PORT0_OMR_PR6_Pos)                           /*!< PORT0 OMR: PR6 Mask                     */
#define PORT0_OMR_PR7_Pos                     23                                                      /*!< PORT0 OMR: PR7 Position                 */
#define PORT0_OMR_PR7_Msk                     (0x01UL << PORT0_OMR_PR7_Pos)                           /*!< PORT0 OMR: PR7 Mask                     */
#define PORT0_OMR_PR8_Pos                     24                                                      /*!< PORT0 OMR: PR8 Position                 */
#define PORT0_OMR_PR8_Msk                     (0x01UL << PORT0_OMR_PR8_Pos)                           /*!< PORT0 OMR: PR8 Mask                     */
#define PORT0_OMR_PR9_Pos                     25                                                      /*!< PORT0 OMR: PR9 Position                 */
#define PORT0_OMR_PR9_Msk                     (0x01UL << PORT0_OMR_PR9_Pos)                           /*!< PORT0 OMR: PR9 Mask                     */
#define PORT0_OMR_PR10_Pos                    26                                                      /*!< PORT0 OMR: PR10 Position                */
#define PORT0_OMR_PR10_Msk                    (0x01UL << PORT0_OMR_PR10_Pos)                          /*!< PORT0 OMR: PR10 Mask                    */
#define PORT0_OMR_PR11_Pos                    27                                                      /*!< PORT0 OMR: PR11 Position                */
#define PORT0_OMR_PR11_Msk                    (0x01UL << PORT0_OMR_PR11_Pos)                          /*!< PORT0 OMR: PR11 Mask                    */
#define PORT0_OMR_PR12_Pos                    28                                                      /*!< PORT0 OMR: PR12 Position                */
#define PORT0_OMR_PR12_Msk                    (0x01UL << PORT0_OMR_PR12_Pos)                          /*!< PORT0 OMR: PR12 Mask                    */
#define PORT0_OMR_PR13_Pos                    29                                                      /*!< PORT0 OMR: PR13 Position                */
#define PORT0_OMR_PR13_Msk                    (0x01UL << PORT0_OMR_PR13_Pos)                          /*!< PORT0 OMR: PR13 Mask                    */
#define PORT0_OMR_PR14_Pos                    30                                                      /*!< PORT0 OMR: PR14 Position                */
#define PORT0_OMR_PR14_Msk                    (0x01UL << PORT0_OMR_PR14_Pos)                          /*!< PORT0 OMR: PR14 Mask                    */
#define PORT0_OMR_PR15_Pos                    31                                                      /*!< PORT0 OMR: PR15 Position                */
#define PORT0_OMR_PR15_Msk                    (0x01UL << PORT0_OMR_PR15_Pos)                          /*!< PORT0 OMR: PR15 Mask                    */

/* ---------------------------------  PORT0_IOCR0  -------------------------------- */
#define PORT0_IOCR0_PC0_Pos                   3                                                       /*!< PORT0 IOCR0: PC0 Position               */
#define PORT0_IOCR0_PC0_Msk                   (0x1fUL << PORT0_IOCR0_PC0_Pos)                         /*!< PORT0 IOCR0: PC0 Mask                   */
#define PORT0_IOCR0_PC1_Pos                   11                                                      /*!< PORT0 IOCR0: PC1 Position               */
#define PORT0_IOCR0_PC1_Msk                   (0x1fUL << PORT0_IOCR0_PC1_Pos)                         /*!< PORT0 IOCR0: PC1 Mask                   */
#define PORT0_IOCR0_PC2_Pos                   19                                                      /*!< PORT0 IOCR0: PC2 Position               */
#define PORT0_IOCR0_PC2_Msk                   (0x1fUL << PORT0_IOCR0_PC2_Pos)                         /*!< PORT0 IOCR0: PC2 Mask                   */
#define PORT0_IOCR0_PC3_Pos                   27                                                      /*!< PORT0 IOCR0: PC3 Position               */
#define PORT0_IOCR0_PC3_Msk                   (0x1fUL << PORT0_IOCR0_PC3_Pos)                         /*!< PORT0 IOCR0: PC3 Mask                   */

/* ---------------------------------  PORT0_IOCR4  -------------------------------- */
#define PORT0_IOCR4_PC4_Pos                   3                                                       /*!< PORT0 IOCR4: PC4 Position               */
#define PORT0_IOCR4_PC4_Msk                   (0x1fUL << PORT0_IOCR4_PC4_Pos)                         /*!< PORT0 IOCR4: PC4 Mask                   */
#define PORT0_IOCR4_PC5_Pos                   11                                                      /*!< PORT0 IOCR4: PC5 Position               */
#define PORT0_IOCR4_PC5_Msk                   (0x1fUL << PORT0_IOCR4_PC5_Pos)                         /*!< PORT0 IOCR4: PC5 Mask                   */
#define PORT0_IOCR4_PC6_Pos                   19                                                      /*!< PORT0 IOCR4: PC6 Position               */
#define PORT0_IOCR4_PC6_Msk                   (0x1fUL << PORT0_IOCR4_PC6_Pos)                         /*!< PORT0 IOCR4: PC6 Mask                   */
#define PORT0_IOCR4_PC7_Pos                   27                                                      /*!< PORT0 IOCR4: PC7 Position               */
#define PORT0_IOCR4_PC7_Msk                   (0x1fUL << PORT0_IOCR4_PC7_Pos)                         /*!< PORT0 IOCR4: PC7 Mask                   */

/* ---------------------------------  PORT0_IOCR8  -------------------------------- */
#define PORT0_IOCR8_PC8_Pos                   3                                                       /*!< PORT0 IOCR8: PC8 Position               */
#define PORT0_IOCR8_PC8_Msk                   (0x1fUL << PORT0_IOCR8_PC8_Pos)                         /*!< PORT0 IOCR8: PC8 Mask                   */
#define PORT0_IOCR8_PC9_Pos                   11                                                      /*!< PORT0 IOCR8: PC9 Position               */
#define PORT0_IOCR8_PC9_Msk                   (0x1fUL << PORT0_IOCR8_PC9_Pos)                         /*!< PORT0 IOCR8: PC9 Mask                   */
#define PORT0_IOCR8_PC10_Pos                  19                                                      /*!< PORT0 IOCR8: PC10 Position              */
#define PORT0_IOCR8_PC10_Msk                  (0x1fUL << PORT0_IOCR8_PC10_Pos)                        /*!< PORT0 IOCR8: PC10 Mask                  */
#define PORT0_IOCR8_PC11_Pos                  27                                                      /*!< PORT0 IOCR8: PC11 Position              */
#define PORT0_IOCR8_PC11_Msk                  (0x1fUL << PORT0_IOCR8_PC11_Pos)                        /*!< PORT0 IOCR8: PC11 Mask                  */

/* --------------------------------  PORT0_IOCR12  -------------------------------- */
#define PORT0_IOCR12_PC12_Pos                 3                                                       /*!< PORT0 IOCR12: PC12 Position             */
#define PORT0_IOCR12_PC12_Msk                 (0x1fUL << PORT0_IOCR12_PC12_Pos)                       /*!< PORT0 IOCR12: PC12 Mask                 */
#define PORT0_IOCR12_PC13_Pos                 11                                                      /*!< PORT0 IOCR12: PC13 Position             */
#define PORT0_IOCR12_PC13_Msk                 (0x1fUL << PORT0_IOCR12_PC13_Pos)                       /*!< PORT0 IOCR12: PC13 Mask                 */
#define PORT0_IOCR12_PC14_Pos                 19                                                      /*!< PORT0 IOCR12: PC14 Position             */
#define PORT0_IOCR12_PC14_Msk                 (0x1fUL << PORT0_IOCR12_PC14_Pos)                       /*!< PORT0 IOCR12: PC14 Mask                 */
#define PORT0_IOCR12_PC15_Pos                 27                                                      /*!< PORT0 IOCR12: PC15 Position             */
#define PORT0_IOCR12_PC15_Msk                 (0x1fUL << PORT0_IOCR12_PC15_Pos)                       /*!< PORT0 IOCR12: PC15 Mask                 */

/* ----------------------------------  PORT0_IN  ---------------------------------- */
#define PORT0_IN_P0_Pos                       0                                                       /*!< PORT0 IN: P0 Position                   */
#define PORT0_IN_P0_Msk                       (0x01UL << PORT0_IN_P0_Pos)                             /*!< PORT0 IN: P0 Mask                       */
#define PORT0_IN_P1_Pos                       1                                                       /*!< PORT0 IN: P1 Position                   */
#define PORT0_IN_P1_Msk                       (0x01UL << PORT0_IN_P1_Pos)                             /*!< PORT0 IN: P1 Mask                       */
#define PORT0_IN_P2_Pos                       2                                                       /*!< PORT0 IN: P2 Position                   */
#define PORT0_IN_P2_Msk                       (0x01UL << PORT0_IN_P2_Pos)                             /*!< PORT0 IN: P2 Mask                       */
#define PORT0_IN_P3_Pos                       3                                                       /*!< PORT0 IN: P3 Position                   */
#define PORT0_IN_P3_Msk                       (0x01UL << PORT0_IN_P3_Pos)                             /*!< PORT0 IN: P3 Mask                       */
#define PORT0_IN_P4_Pos                       4                                                       /*!< PORT0 IN: P4 Position                   */
#define PORT0_IN_P4_Msk                       (0x01UL << PORT0_IN_P4_Pos)                             /*!< PORT0 IN: P4 Mask                       */
#define PORT0_IN_P5_Pos                       5                                                       /*!< PORT0 IN: P5 Position                   */
#define PORT0_IN_P5_Msk                       (0x01UL << PORT0_IN_P5_Pos)                             /*!< PORT0 IN: P5 Mask                       */
#define PORT0_IN_P6_Pos                       6                                                       /*!< PORT0 IN: P6 Position                   */
#define PORT0_IN_P6_Msk                       (0x01UL << PORT0_IN_P6_Pos)                             /*!< PORT0 IN: P6 Mask                       */
#define PORT0_IN_P7_Pos                       7                                                       /*!< PORT0 IN: P7 Position                   */
#define PORT0_IN_P7_Msk                       (0x01UL << PORT0_IN_P7_Pos)                             /*!< PORT0 IN: P7 Mask                       */
#define PORT0_IN_P8_Pos                       8                                                       /*!< PORT0 IN: P8 Position                   */
#define PORT0_IN_P8_Msk                       (0x01UL << PORT0_IN_P8_Pos)                             /*!< PORT0 IN: P8 Mask                       */
#define PORT0_IN_P9_Pos                       9                                                       /*!< PORT0 IN: P9 Position                   */
#define PORT0_IN_P9_Msk                       (0x01UL << PORT0_IN_P9_Pos)                             /*!< PORT0 IN: P9 Mask                       */
#define PORT0_IN_P10_Pos                      10                                                      /*!< PORT0 IN: P10 Position                  */
#define PORT0_IN_P10_Msk                      (0x01UL << PORT0_IN_P10_Pos)                            /*!< PORT0 IN: P10 Mask                      */
#define PORT0_IN_P11_Pos                      11                                                      /*!< PORT0 IN: P11 Position                  */
#define PORT0_IN_P11_Msk                      (0x01UL << PORT0_IN_P11_Pos)                            /*!< PORT0 IN: P11 Mask                      */
#define PORT0_IN_P12_Pos                      12                                                      /*!< PORT0 IN: P12 Position                  */
#define PORT0_IN_P12_Msk                      (0x01UL << PORT0_IN_P12_Pos)                            /*!< PORT0 IN: P12 Mask                      */
#define PORT0_IN_P13_Pos                      13                                                      /*!< PORT0 IN: P13 Position                  */
#define PORT0_IN_P13_Msk                      (0x01UL << PORT0_IN_P13_Pos)                            /*!< PORT0 IN: P13 Mask                      */
#define PORT0_IN_P14_Pos                      14                                                      /*!< PORT0 IN: P14 Position                  */
#define PORT0_IN_P14_Msk                      (0x01UL << PORT0_IN_P14_Pos)                            /*!< PORT0 IN: P14 Mask                      */
#define PORT0_IN_P15_Pos                      15                                                      /*!< PORT0 IN: P15 Position                  */
#define PORT0_IN_P15_Msk                      (0x01UL << PORT0_IN_P15_Pos)                            /*!< PORT0 IN: P15 Mask                      */

/* ---------------------------------  PORT0_PHCR0  -------------------------------- */
#define PORT0_PHCR0_PH0_Pos                   2                                                       /*!< PORT0 PHCR0: PH0 Position               */
#define PORT0_PHCR0_PH0_Msk                   (0x01UL << PORT0_PHCR0_PH0_Pos)                         /*!< PORT0 PHCR0: PH0 Mask                   */
#define PORT0_PHCR0_PH1_Pos                   6                                                       /*!< PORT0 PHCR0: PH1 Position               */
#define PORT0_PHCR0_PH1_Msk                   (0x01UL << PORT0_PHCR0_PH1_Pos)                         /*!< PORT0 PHCR0: PH1 Mask                   */
#define PORT0_PHCR0_PH2_Pos                   10                                                      /*!< PORT0 PHCR0: PH2 Position               */
#define PORT0_PHCR0_PH2_Msk                   (0x01UL << PORT0_PHCR0_PH2_Pos)                         /*!< PORT0 PHCR0: PH2 Mask                   */
#define PORT0_PHCR0_PH3_Pos                   14                                                      /*!< PORT0 PHCR0: PH3 Position               */
#define PORT0_PHCR0_PH3_Msk                   (0x01UL << PORT0_PHCR0_PH3_Pos)                         /*!< PORT0 PHCR0: PH3 Mask                   */
#define PORT0_PHCR0_PH4_Pos                   18                                                      /*!< PORT0 PHCR0: PH4 Position               */
#define PORT0_PHCR0_PH4_Msk                   (0x01UL << PORT0_PHCR0_PH4_Pos)                         /*!< PORT0 PHCR0: PH4 Mask                   */
#define PORT0_PHCR0_PH5_Pos                   22                                                      /*!< PORT0 PHCR0: PH5 Position               */
#define PORT0_PHCR0_PH5_Msk                   (0x01UL << PORT0_PHCR0_PH5_Pos)                         /*!< PORT0 PHCR0: PH5 Mask                   */
#define PORT0_PHCR0_PH6_Pos                   26                                                      /*!< PORT0 PHCR0: PH6 Position               */
#define PORT0_PHCR0_PH6_Msk                   (0x01UL << PORT0_PHCR0_PH6_Pos)                         /*!< PORT0 PHCR0: PH6 Mask                   */
#define PORT0_PHCR0_PH7_Pos                   30                                                      /*!< PORT0 PHCR0: PH7 Position               */
#define PORT0_PHCR0_PH7_Msk                   (0x01UL << PORT0_PHCR0_PH7_Pos)                         /*!< PORT0 PHCR0: PH7 Mask                   */

/* ---------------------------------  PORT0_PHCR1  -------------------------------- */
#define PORT0_PHCR1_PH8_Pos                   2                                                       /*!< PORT0 PHCR1: PH8 Position               */
#define PORT0_PHCR1_PH8_Msk                   (0x01UL << PORT0_PHCR1_PH8_Pos)                         /*!< PORT0 PHCR1: PH8 Mask                   */
#define PORT0_PHCR1_PH9_Pos                   6                                                       /*!< PORT0 PHCR1: PH9 Position               */
#define PORT0_PHCR1_PH9_Msk                   (0x01UL << PORT0_PHCR1_PH9_Pos)                         /*!< PORT0 PHCR1: PH9 Mask                   */
#define PORT0_PHCR1_PH10_Pos                  10                                                      /*!< PORT0 PHCR1: PH10 Position              */
#define PORT0_PHCR1_PH10_Msk                  (0x01UL << PORT0_PHCR1_PH10_Pos)                        /*!< PORT0 PHCR1: PH10 Mask                  */
#define PORT0_PHCR1_PH11_Pos                  14                                                      /*!< PORT0 PHCR1: PH11 Position              */
#define PORT0_PHCR1_PH11_Msk                  (0x01UL << PORT0_PHCR1_PH11_Pos)                        /*!< PORT0 PHCR1: PH11 Mask                  */
#define PORT0_PHCR1_PH12_Pos                  18                                                      /*!< PORT0 PHCR1: PH12 Position              */
#define PORT0_PHCR1_PH12_Msk                  (0x01UL << PORT0_PHCR1_PH12_Pos)                        /*!< PORT0 PHCR1: PH12 Mask                  */
#define PORT0_PHCR1_PH13_Pos                  22                                                      /*!< PORT0 PHCR1: PH13 Position              */
#define PORT0_PHCR1_PH13_Msk                  (0x01UL << PORT0_PHCR1_PH13_Pos)                        /*!< PORT0 PHCR1: PH13 Mask                  */
#define PORT0_PHCR1_PH14_Pos                  26                                                      /*!< PORT0 PHCR1: PH14 Position              */
#define PORT0_PHCR1_PH14_Msk                  (0x01UL << PORT0_PHCR1_PH14_Pos)                        /*!< PORT0 PHCR1: PH14 Mask                  */
#define PORT0_PHCR1_PH15_Pos                  30                                                      /*!< PORT0 PHCR1: PH15 Position              */
#define PORT0_PHCR1_PH15_Msk                  (0x01UL << PORT0_PHCR1_PH15_Pos)                        /*!< PORT0 PHCR1: PH15 Mask                  */

/* ---------------------------------  PORT0_PDISC  -------------------------------- */
#define PORT0_PDISC_PDIS0_Pos                 0                                                       /*!< PORT0 PDISC: PDIS0 Position             */
#define PORT0_PDISC_PDIS0_Msk                 (0x01UL << PORT0_PDISC_PDIS0_Pos)                       /*!< PORT0 PDISC: PDIS0 Mask                 */
#define PORT0_PDISC_PDIS1_Pos                 1                                                       /*!< PORT0 PDISC: PDIS1 Position             */
#define PORT0_PDISC_PDIS1_Msk                 (0x01UL << PORT0_PDISC_PDIS1_Pos)                       /*!< PORT0 PDISC: PDIS1 Mask                 */
#define PORT0_PDISC_PDIS2_Pos                 2                                                       /*!< PORT0 PDISC: PDIS2 Position             */
#define PORT0_PDISC_PDIS2_Msk                 (0x01UL << PORT0_PDISC_PDIS2_Pos)                       /*!< PORT0 PDISC: PDIS2 Mask                 */
#define PORT0_PDISC_PDIS3_Pos                 3                                                       /*!< PORT0 PDISC: PDIS3 Position             */
#define PORT0_PDISC_PDIS3_Msk                 (0x01UL << PORT0_PDISC_PDIS3_Pos)                       /*!< PORT0 PDISC: PDIS3 Mask                 */
#define PORT0_PDISC_PDIS4_Pos                 4                                                       /*!< PORT0 PDISC: PDIS4 Position             */
#define PORT0_PDISC_PDIS4_Msk                 (0x01UL << PORT0_PDISC_PDIS4_Pos)                       /*!< PORT0 PDISC: PDIS4 Mask                 */
#define PORT0_PDISC_PDIS5_Pos                 5                                                       /*!< PORT0 PDISC: PDIS5 Position             */
#define PORT0_PDISC_PDIS5_Msk                 (0x01UL << PORT0_PDISC_PDIS5_Pos)                       /*!< PORT0 PDISC: PDIS5 Mask                 */
#define PORT0_PDISC_PDIS6_Pos                 6                                                       /*!< PORT0 PDISC: PDIS6 Position             */
#define PORT0_PDISC_PDIS6_Msk                 (0x01UL << PORT0_PDISC_PDIS6_Pos)                       /*!< PORT0 PDISC: PDIS6 Mask                 */
#define PORT0_PDISC_PDIS7_Pos                 7                                                       /*!< PORT0 PDISC: PDIS7 Position             */
#define PORT0_PDISC_PDIS7_Msk                 (0x01UL << PORT0_PDISC_PDIS7_Pos)                       /*!< PORT0 PDISC: PDIS7 Mask                 */
#define PORT0_PDISC_PDIS8_Pos                 8                                                       /*!< PORT0 PDISC: PDIS8 Position             */
#define PORT0_PDISC_PDIS8_Msk                 (0x01UL << PORT0_PDISC_PDIS8_Pos)                       /*!< PORT0 PDISC: PDIS8 Mask                 */
#define PORT0_PDISC_PDIS9_Pos                 9                                                       /*!< PORT0 PDISC: PDIS9 Position             */
#define PORT0_PDISC_PDIS9_Msk                 (0x01UL << PORT0_PDISC_PDIS9_Pos)                       /*!< PORT0 PDISC: PDIS9 Mask                 */
#define PORT0_PDISC_PDIS10_Pos                10                                                      /*!< PORT0 PDISC: PDIS10 Position            */
#define PORT0_PDISC_PDIS10_Msk                (0x01UL << PORT0_PDISC_PDIS10_Pos)                      /*!< PORT0 PDISC: PDIS10 Mask                */
#define PORT0_PDISC_PDIS11_Pos                11                                                      /*!< PORT0 PDISC: PDIS11 Position            */
#define PORT0_PDISC_PDIS11_Msk                (0x01UL << PORT0_PDISC_PDIS11_Pos)                      /*!< PORT0 PDISC: PDIS11 Mask                */
#define PORT0_PDISC_PDIS12_Pos                12                                                      /*!< PORT0 PDISC: PDIS12 Position            */
#define PORT0_PDISC_PDIS12_Msk                (0x01UL << PORT0_PDISC_PDIS12_Pos)                      /*!< PORT0 PDISC: PDIS12 Mask                */
#define PORT0_PDISC_PDIS13_Pos                13                                                      /*!< PORT0 PDISC: PDIS13 Position            */
#define PORT0_PDISC_PDIS13_Msk                (0x01UL << PORT0_PDISC_PDIS13_Pos)                      /*!< PORT0 PDISC: PDIS13 Mask                */
#define PORT0_PDISC_PDIS14_Pos                14                                                      /*!< PORT0 PDISC: PDIS14 Position            */
#define PORT0_PDISC_PDIS14_Msk                (0x01UL << PORT0_PDISC_PDIS14_Pos)                      /*!< PORT0 PDISC: PDIS14 Mask                */
#define PORT0_PDISC_PDIS15_Pos                15                                                      /*!< PORT0 PDISC: PDIS15 Position            */
#define PORT0_PDISC_PDIS15_Msk                (0x01UL << PORT0_PDISC_PDIS15_Pos)                      /*!< PORT0 PDISC: PDIS15 Mask                */

/* ----------------------------------  PORT0_PPS  --------------------------------- */
#define PORT0_PPS_PPS0_Pos                    0                                                       /*!< PORT0 PPS: PPS0 Position                */
#define PORT0_PPS_PPS0_Msk                    (0x01UL << PORT0_PPS_PPS0_Pos)                          /*!< PORT0 PPS: PPS0 Mask                    */
#define PORT0_PPS_PPS1_Pos                    1                                                       /*!< PORT0 PPS: PPS1 Position                */
#define PORT0_PPS_PPS1_Msk                    (0x01UL << PORT0_PPS_PPS1_Pos)                          /*!< PORT0 PPS: PPS1 Mask                    */
#define PORT0_PPS_PPS2_Pos                    2                                                       /*!< PORT0 PPS: PPS2 Position                */
#define PORT0_PPS_PPS2_Msk                    (0x01UL << PORT0_PPS_PPS2_Pos)                          /*!< PORT0 PPS: PPS2 Mask                    */
#define PORT0_PPS_PPS3_Pos                    3                                                       /*!< PORT0 PPS: PPS3 Position                */
#define PORT0_PPS_PPS3_Msk                    (0x01UL << PORT0_PPS_PPS3_Pos)                          /*!< PORT0 PPS: PPS3 Mask                    */
#define PORT0_PPS_PPS4_Pos                    4                                                       /*!< PORT0 PPS: PPS4 Position                */
#define PORT0_PPS_PPS4_Msk                    (0x01UL << PORT0_PPS_PPS4_Pos)                          /*!< PORT0 PPS: PPS4 Mask                    */
#define PORT0_PPS_PPS5_Pos                    5                                                       /*!< PORT0 PPS: PPS5 Position                */
#define PORT0_PPS_PPS5_Msk                    (0x01UL << PORT0_PPS_PPS5_Pos)                          /*!< PORT0 PPS: PPS5 Mask                    */
#define PORT0_PPS_PPS6_Pos                    6                                                       /*!< PORT0 PPS: PPS6 Position                */
#define PORT0_PPS_PPS6_Msk                    (0x01UL << PORT0_PPS_PPS6_Pos)                          /*!< PORT0 PPS: PPS6 Mask                    */
#define PORT0_PPS_PPS7_Pos                    7                                                       /*!< PORT0 PPS: PPS7 Position                */
#define PORT0_PPS_PPS7_Msk                    (0x01UL << PORT0_PPS_PPS7_Pos)                          /*!< PORT0 PPS: PPS7 Mask                    */
#define PORT0_PPS_PPS8_Pos                    8                                                       /*!< PORT0 PPS: PPS8 Position                */
#define PORT0_PPS_PPS8_Msk                    (0x01UL << PORT0_PPS_PPS8_Pos)                          /*!< PORT0 PPS: PPS8 Mask                    */
#define PORT0_PPS_PPS9_Pos                    9                                                       /*!< PORT0 PPS: PPS9 Position                */
#define PORT0_PPS_PPS9_Msk                    (0x01UL << PORT0_PPS_PPS9_Pos)                          /*!< PORT0 PPS: PPS9 Mask                    */
#define PORT0_PPS_PPS10_Pos                   10                                                      /*!< PORT0 PPS: PPS10 Position               */
#define PORT0_PPS_PPS10_Msk                   (0x01UL << PORT0_PPS_PPS10_Pos)                         /*!< PORT0 PPS: PPS10 Mask                   */
#define PORT0_PPS_PPS11_Pos                   11                                                      /*!< PORT0 PPS: PPS11 Position               */
#define PORT0_PPS_PPS11_Msk                   (0x01UL << PORT0_PPS_PPS11_Pos)                         /*!< PORT0 PPS: PPS11 Mask                   */
#define PORT0_PPS_PPS12_Pos                   12                                                      /*!< PORT0 PPS: PPS12 Position               */
#define PORT0_PPS_PPS12_Msk                   (0x01UL << PORT0_PPS_PPS12_Pos)                         /*!< PORT0 PPS: PPS12 Mask                   */
#define PORT0_PPS_PPS13_Pos                   13                                                      /*!< PORT0 PPS: PPS13 Position               */
#define PORT0_PPS_PPS13_Msk                   (0x01UL << PORT0_PPS_PPS13_Pos)                         /*!< PORT0 PPS: PPS13 Mask                   */
#define PORT0_PPS_PPS14_Pos                   14                                                      /*!< PORT0 PPS: PPS14 Position               */
#define PORT0_PPS_PPS14_Msk                   (0x01UL << PORT0_PPS_PPS14_Pos)                         /*!< PORT0 PPS: PPS14 Mask                   */
#define PORT0_PPS_PPS15_Pos                   15                                                      /*!< PORT0 PPS: PPS15 Position               */
#define PORT0_PPS_PPS15_Msk                   (0x01UL << PORT0_PPS_PPS15_Pos)                         /*!< PORT0 PPS: PPS15 Mask                   */

/* ---------------------------------  PORT0_HWSEL  -------------------------------- */
#define PORT0_HWSEL_HW0_Pos                   0                                                       /*!< PORT0 HWSEL: HW0 Position               */
#define PORT0_HWSEL_HW0_Msk                   (0x03UL << PORT0_HWSEL_HW0_Pos)                         /*!< PORT0 HWSEL: HW0 Mask                   */
#define PORT0_HWSEL_HW1_Pos                   2                                                       /*!< PORT0 HWSEL: HW1 Position               */
#define PORT0_HWSEL_HW1_Msk                   (0x03UL << PORT0_HWSEL_HW1_Pos)                         /*!< PORT0 HWSEL: HW1 Mask                   */
#define PORT0_HWSEL_HW2_Pos                   4                                                       /*!< PORT0 HWSEL: HW2 Position               */
#define PORT0_HWSEL_HW2_Msk                   (0x03UL << PORT0_HWSEL_HW2_Pos)                         /*!< PORT0 HWSEL: HW2 Mask                   */
#define PORT0_HWSEL_HW3_Pos                   6                                                       /*!< PORT0 HWSEL: HW3 Position               */
#define PORT0_HWSEL_HW3_Msk                   (0x03UL << PORT0_HWSEL_HW3_Pos)                         /*!< PORT0 HWSEL: HW3 Mask                   */
#define PORT0_HWSEL_HW4_Pos                   8                                                       /*!< PORT0 HWSEL: HW4 Position               */
#define PORT0_HWSEL_HW4_Msk                   (0x03UL << PORT0_HWSEL_HW4_Pos)                         /*!< PORT0 HWSEL: HW4 Mask                   */
#define PORT0_HWSEL_HW5_Pos                   10                                                      /*!< PORT0 HWSEL: HW5 Position               */
#define PORT0_HWSEL_HW5_Msk                   (0x03UL << PORT0_HWSEL_HW5_Pos)                         /*!< PORT0 HWSEL: HW5 Mask                   */
#define PORT0_HWSEL_HW6_Pos                   12                                                      /*!< PORT0 HWSEL: HW6 Position               */
#define PORT0_HWSEL_HW6_Msk                   (0x03UL << PORT0_HWSEL_HW6_Pos)                         /*!< PORT0 HWSEL: HW6 Mask                   */
#define PORT0_HWSEL_HW7_Pos                   14                                                      /*!< PORT0 HWSEL: HW7 Position               */
#define PORT0_HWSEL_HW7_Msk                   (0x03UL << PORT0_HWSEL_HW7_Pos)                         /*!< PORT0 HWSEL: HW7 Mask                   */
#define PORT0_HWSEL_HW8_Pos                   16                                                      /*!< PORT0 HWSEL: HW8 Position               */
#define PORT0_HWSEL_HW8_Msk                   (0x03UL << PORT0_HWSEL_HW8_Pos)                         /*!< PORT0 HWSEL: HW8 Mask                   */
#define PORT0_HWSEL_HW9_Pos                   18                                                      /*!< PORT0 HWSEL: HW9 Position               */
#define PORT0_HWSEL_HW9_Msk                   (0x03UL << PORT0_HWSEL_HW9_Pos)                         /*!< PORT0 HWSEL: HW9 Mask                   */
#define PORT0_HWSEL_HW10_Pos                  20                                                      /*!< PORT0 HWSEL: HW10 Position              */
#define PORT0_HWSEL_HW10_Msk                  (0x03UL << PORT0_HWSEL_HW10_Pos)                        /*!< PORT0 HWSEL: HW10 Mask                  */
#define PORT0_HWSEL_HW11_Pos                  22                                                      /*!< PORT0 HWSEL: HW11 Position              */
#define PORT0_HWSEL_HW11_Msk                  (0x03UL << PORT0_HWSEL_HW11_Pos)                        /*!< PORT0 HWSEL: HW11 Mask                  */
#define PORT0_HWSEL_HW12_Pos                  24                                                      /*!< PORT0 HWSEL: HW12 Position              */
#define PORT0_HWSEL_HW12_Msk                  (0x03UL << PORT0_HWSEL_HW12_Pos)                        /*!< PORT0 HWSEL: HW12 Mask                  */
#define PORT0_HWSEL_HW13_Pos                  26                                                      /*!< PORT0 HWSEL: HW13 Position              */
#define PORT0_HWSEL_HW13_Msk                  (0x03UL << PORT0_HWSEL_HW13_Pos)                        /*!< PORT0 HWSEL: HW13 Mask                  */
#define PORT0_HWSEL_HW14_Pos                  28                                                      /*!< PORT0 HWSEL: HW14 Position              */
#define PORT0_HWSEL_HW14_Msk                  (0x03UL << PORT0_HWSEL_HW14_Pos)                        /*!< PORT0 HWSEL: HW14 Mask                  */
#define PORT0_HWSEL_HW15_Pos                  30                                                      /*!< PORT0 HWSEL: HW15 Position              */
#define PORT0_HWSEL_HW15_Msk                  (0x03UL << PORT0_HWSEL_HW15_Pos)                        /*!< PORT0 HWSEL: HW15 Mask                  */


/* ================================================================================ */
/* ================         struct 'PORT1' Position & Mask         ================ */
/* ================================================================================ */


/* ----------------------------------  PORT1_OUT  --------------------------------- */
#define PORT1_OUT_P0_Pos                      0                                                       /*!< PORT1 OUT: P0 Position                  */
#define PORT1_OUT_P0_Msk                      (0x01UL << PORT1_OUT_P0_Pos)                            /*!< PORT1 OUT: P0 Mask                      */
#define PORT1_OUT_P1_Pos                      1                                                       /*!< PORT1 OUT: P1 Position                  */
#define PORT1_OUT_P1_Msk                      (0x01UL << PORT1_OUT_P1_Pos)                            /*!< PORT1 OUT: P1 Mask                      */
#define PORT1_OUT_P2_Pos                      2                                                       /*!< PORT1 OUT: P2 Position                  */
#define PORT1_OUT_P2_Msk                      (0x01UL << PORT1_OUT_P2_Pos)                            /*!< PORT1 OUT: P2 Mask                      */
#define PORT1_OUT_P3_Pos                      3                                                       /*!< PORT1 OUT: P3 Position                  */
#define PORT1_OUT_P3_Msk                      (0x01UL << PORT1_OUT_P3_Pos)                            /*!< PORT1 OUT: P3 Mask                      */
#define PORT1_OUT_P4_Pos                      4                                                       /*!< PORT1 OUT: P4 Position                  */
#define PORT1_OUT_P4_Msk                      (0x01UL << PORT1_OUT_P4_Pos)                            /*!< PORT1 OUT: P4 Mask                      */
#define PORT1_OUT_P5_Pos                      5                                                       /*!< PORT1 OUT: P5 Position                  */
#define PORT1_OUT_P5_Msk                      (0x01UL << PORT1_OUT_P5_Pos)                            /*!< PORT1 OUT: P5 Mask                      */

/* ----------------------------------  PORT1_OMR  --------------------------------- */
#define PORT1_OMR_PS0_Pos                     0                                                       /*!< PORT1 OMR: PS0 Position                 */
#define PORT1_OMR_PS0_Msk                     (0x01UL << PORT1_OMR_PS0_Pos)                           /*!< PORT1 OMR: PS0 Mask                     */
#define PORT1_OMR_PS1_Pos                     1                                                       /*!< PORT1 OMR: PS1 Position                 */
#define PORT1_OMR_PS1_Msk                     (0x01UL << PORT1_OMR_PS1_Pos)                           /*!< PORT1 OMR: PS1 Mask                     */
#define PORT1_OMR_PS2_Pos                     2                                                       /*!< PORT1 OMR: PS2 Position                 */
#define PORT1_OMR_PS2_Msk                     (0x01UL << PORT1_OMR_PS2_Pos)                           /*!< PORT1 OMR: PS2 Mask                     */
#define PORT1_OMR_PS3_Pos                     3                                                       /*!< PORT1 OMR: PS3 Position                 */
#define PORT1_OMR_PS3_Msk                     (0x01UL << PORT1_OMR_PS3_Pos)                           /*!< PORT1 OMR: PS3 Mask                     */
#define PORT1_OMR_PS4_Pos                     4                                                       /*!< PORT1 OMR: PS4 Position                 */
#define PORT1_OMR_PS4_Msk                     (0x01UL << PORT1_OMR_PS4_Pos)                           /*!< PORT1 OMR: PS4 Mask                     */
#define PORT1_OMR_PS5_Pos                     5                                                       /*!< PORT1 OMR: PS5 Position                 */
#define PORT1_OMR_PS5_Msk                     (0x01UL << PORT1_OMR_PS5_Pos)                           /*!< PORT1 OMR: PS5 Mask                     */
#define PORT1_OMR_PR0_Pos                     16                                                      /*!< PORT1 OMR: PR0 Position                 */
#define PORT1_OMR_PR0_Msk                     (0x01UL << PORT1_OMR_PR0_Pos)                           /*!< PORT1 OMR: PR0 Mask                     */
#define PORT1_OMR_PR1_Pos                     17                                                      /*!< PORT1 OMR: PR1 Position                 */
#define PORT1_OMR_PR1_Msk                     (0x01UL << PORT1_OMR_PR1_Pos)                           /*!< PORT1 OMR: PR1 Mask                     */
#define PORT1_OMR_PR2_Pos                     18                                                      /*!< PORT1 OMR: PR2 Position                 */
#define PORT1_OMR_PR2_Msk                     (0x01UL << PORT1_OMR_PR2_Pos)                           /*!< PORT1 OMR: PR2 Mask                     */
#define PORT1_OMR_PR3_Pos                     19                                                      /*!< PORT1 OMR: PR3 Position                 */
#define PORT1_OMR_PR3_Msk                     (0x01UL << PORT1_OMR_PR3_Pos)                           /*!< PORT1 OMR: PR3 Mask                     */
#define PORT1_OMR_PR4_Pos                     20                                                      /*!< PORT1 OMR: PR4 Position                 */
#define PORT1_OMR_PR4_Msk                     (0x01UL << PORT1_OMR_PR4_Pos)                           /*!< PORT1 OMR: PR4 Mask                     */
#define PORT1_OMR_PR5_Pos                     21                                                      /*!< PORT1 OMR: PR5 Position                 */
#define PORT1_OMR_PR5_Msk                     (0x01UL << PORT1_OMR_PR5_Pos)                           /*!< PORT1 OMR: PR5 Mask                     */

/* ---------------------------------  PORT1_IOCR0  -------------------------------- */
#define PORT1_IOCR0_PC0_Pos                   3                                                       /*!< PORT1 IOCR0: PC0 Position               */
#define PORT1_IOCR0_PC0_Msk                   (0x1fUL << PORT1_IOCR0_PC0_Pos)                         /*!< PORT1 IOCR0: PC0 Mask                   */
#define PORT1_IOCR0_PC1_Pos                   11                                                      /*!< PORT1 IOCR0: PC1 Position               */
#define PORT1_IOCR0_PC1_Msk                   (0x1fUL << PORT1_IOCR0_PC1_Pos)                         /*!< PORT1 IOCR0: PC1 Mask                   */
#define PORT1_IOCR0_PC2_Pos                   19                                                      /*!< PORT1 IOCR0: PC2 Position               */
#define PORT1_IOCR0_PC2_Msk                   (0x1fUL << PORT1_IOCR0_PC2_Pos)                         /*!< PORT1 IOCR0: PC2 Mask                   */
#define PORT1_IOCR0_PC3_Pos                   27                                                      /*!< PORT1 IOCR0: PC3 Position               */
#define PORT1_IOCR0_PC3_Msk                   (0x1fUL << PORT1_IOCR0_PC3_Pos)                         /*!< PORT1 IOCR0: PC3 Mask                   */

/* ---------------------------------  PORT1_IOCR4  -------------------------------- */
#define PORT1_IOCR4_PC4_Pos                   3                                                       /*!< PORT1 IOCR4: PC4 Position               */
#define PORT1_IOCR4_PC4_Msk                   (0x1fUL << PORT1_IOCR4_PC4_Pos)                         /*!< PORT1 IOCR4: PC4 Mask                   */
#define PORT1_IOCR4_PC5_Pos                   11                                                      /*!< PORT1 IOCR4: PC5 Position               */
#define PORT1_IOCR4_PC5_Msk                   (0x1fUL << PORT1_IOCR4_PC5_Pos)                         /*!< PORT1 IOCR4: PC5 Mask                   */

/* ----------------------------------  PORT1_IN  ---------------------------------- */
#define PORT1_IN_P0_Pos                       0                                                       /*!< PORT1 IN: P0 Position                   */
#define PORT1_IN_P0_Msk                       (0x01UL << PORT1_IN_P0_Pos)                             /*!< PORT1 IN: P0 Mask                       */
#define PORT1_IN_P1_Pos                       1                                                       /*!< PORT1 IN: P1 Position                   */
#define PORT1_IN_P1_Msk                       (0x01UL << PORT1_IN_P1_Pos)                             /*!< PORT1 IN: P1 Mask                       */
#define PORT1_IN_P2_Pos                       2                                                       /*!< PORT1 IN: P2 Position                   */
#define PORT1_IN_P2_Msk                       (0x01UL << PORT1_IN_P2_Pos)                             /*!< PORT1 IN: P2 Mask                       */
#define PORT1_IN_P3_Pos                       3                                                       /*!< PORT1 IN: P3 Position                   */
#define PORT1_IN_P3_Msk                       (0x01UL << PORT1_IN_P3_Pos)                             /*!< PORT1 IN: P3 Mask                       */
#define PORT1_IN_P4_Pos                       4                                                       /*!< PORT1 IN: P4 Position                   */
#define PORT1_IN_P4_Msk                       (0x01UL << PORT1_IN_P4_Pos)                             /*!< PORT1 IN: P4 Mask                       */
#define PORT1_IN_P5_Pos                       5                                                       /*!< PORT1 IN: P5 Position                   */
#define PORT1_IN_P5_Msk                       (0x01UL << PORT1_IN_P5_Pos)                             /*!< PORT1 IN: P5 Mask                       */

/* ---------------------------------  PORT1_PHCR0  -------------------------------- */
#define PORT1_PHCR0_PH0_Pos                   2                                                       /*!< PORT1 PHCR0: PH0 Position               */
#define PORT1_PHCR0_PH0_Msk                   (0x01UL << PORT1_PHCR0_PH0_Pos)                         /*!< PORT1 PHCR0: PH0 Mask                   */
#define PORT1_PHCR0_PH1_Pos                   6                                                       /*!< PORT1 PHCR0: PH1 Position               */
#define PORT1_PHCR0_PH1_Msk                   (0x01UL << PORT1_PHCR0_PH1_Pos)                         /*!< PORT1 PHCR0: PH1 Mask                   */
#define PORT1_PHCR0_PH2_Pos                   10                                                      /*!< PORT1 PHCR0: PH2 Position               */
#define PORT1_PHCR0_PH2_Msk                   (0x01UL << PORT1_PHCR0_PH2_Pos)                         /*!< PORT1 PHCR0: PH2 Mask                   */
#define PORT1_PHCR0_PH3_Pos                   14                                                      /*!< PORT1 PHCR0: PH3 Position               */
#define PORT1_PHCR0_PH3_Msk                   (0x01UL << PORT1_PHCR0_PH3_Pos)                         /*!< PORT1 PHCR0: PH3 Mask                   */
#define PORT1_PHCR0_PH4_Pos                   18                                                      /*!< PORT1 PHCR0: PH4 Position               */
#define PORT1_PHCR0_PH4_Msk                   (0x01UL << PORT1_PHCR0_PH4_Pos)                         /*!< PORT1 PHCR0: PH4 Mask                   */
#define PORT1_PHCR0_PH5_Pos                   22                                                      /*!< PORT1 PHCR0: PH5 Position               */
#define PORT1_PHCR0_PH5_Msk                   (0x01UL << PORT1_PHCR0_PH5_Pos)                         /*!< PORT1 PHCR0: PH5 Mask                   */

/* ---------------------------------  PORT1_PDISC  -------------------------------- */
#define PORT1_PDISC_PDIS0_Pos                 0                                                       /*!< PORT1 PDISC: PDIS0 Position             */
#define PORT1_PDISC_PDIS0_Msk                 (0x01UL << PORT1_PDISC_PDIS0_Pos)                       /*!< PORT1 PDISC: PDIS0 Mask                 */
#define PORT1_PDISC_PDIS1_Pos                 1                                                       /*!< PORT1 PDISC: PDIS1 Position             */
#define PORT1_PDISC_PDIS1_Msk                 (0x01UL << PORT1_PDISC_PDIS1_Pos)                       /*!< PORT1 PDISC: PDIS1 Mask                 */
#define PORT1_PDISC_PDIS2_Pos                 2                                                       /*!< PORT1 PDISC: PDIS2 Position             */
#define PORT1_PDISC_PDIS2_Msk                 (0x01UL << PORT1_PDISC_PDIS2_Pos)                       /*!< PORT1 PDISC: PDIS2 Mask                 */
#define PORT1_PDISC_PDIS3_Pos                 3                                                       /*!< PORT1 PDISC: PDIS3 Position             */
#define PORT1_PDISC_PDIS3_Msk                 (0x01UL << PORT1_PDISC_PDIS3_Pos)                       /*!< PORT1 PDISC: PDIS3 Mask                 */
#define PORT1_PDISC_PDIS4_Pos                 4                                                       /*!< PORT1 PDISC: PDIS4 Position             */
#define PORT1_PDISC_PDIS4_Msk                 (0x01UL << PORT1_PDISC_PDIS4_Pos)                       /*!< PORT1 PDISC: PDIS4 Mask                 */
#define PORT1_PDISC_PDIS5_Pos                 5                                                       /*!< PORT1 PDISC: PDIS5 Position             */
#define PORT1_PDISC_PDIS5_Msk                 (0x01UL << PORT1_PDISC_PDIS5_Pos)                       /*!< PORT1 PDISC: PDIS5 Mask                 */

/* ----------------------------------  PORT1_PPS  --------------------------------- */
#define PORT1_PPS_PPS0_Pos                    0                                                       /*!< PORT1 PPS: PPS0 Position                */
#define PORT1_PPS_PPS0_Msk                    (0x01UL << PORT1_PPS_PPS0_Pos)                          /*!< PORT1 PPS: PPS0 Mask                    */
#define PORT1_PPS_PPS1_Pos                    1                                                       /*!< PORT1 PPS: PPS1 Position                */
#define PORT1_PPS_PPS1_Msk                    (0x01UL << PORT1_PPS_PPS1_Pos)                          /*!< PORT1 PPS: PPS1 Mask                    */
#define PORT1_PPS_PPS2_Pos                    2                                                       /*!< PORT1 PPS: PPS2 Position                */
#define PORT1_PPS_PPS2_Msk                    (0x01UL << PORT1_PPS_PPS2_Pos)                          /*!< PORT1 PPS: PPS2 Mask                    */
#define PORT1_PPS_PPS3_Pos                    3                                                       /*!< PORT1 PPS: PPS3 Position                */
#define PORT1_PPS_PPS3_Msk                    (0x01UL << PORT1_PPS_PPS3_Pos)                          /*!< PORT1 PPS: PPS3 Mask                    */
#define PORT1_PPS_PPS4_Pos                    4                                                       /*!< PORT1 PPS: PPS4 Position                */
#define PORT1_PPS_PPS4_Msk                    (0x01UL << PORT1_PPS_PPS4_Pos)                          /*!< PORT1 PPS: PPS4 Mask                    */
#define PORT1_PPS_PPS5_Pos                    5                                                       /*!< PORT1 PPS: PPS5 Position                */
#define PORT1_PPS_PPS5_Msk                    (0x01UL << PORT1_PPS_PPS5_Pos)                          /*!< PORT1 PPS: PPS5 Mask                    */

/* ---------------------------------  PORT1_HWSEL  -------------------------------- */
#define PORT1_HWSEL_HW0_Pos                   0                                                       /*!< PORT1 HWSEL: HW0 Position               */
#define PORT1_HWSEL_HW0_Msk                   (0x03UL << PORT1_HWSEL_HW0_Pos)                         /*!< PORT1 HWSEL: HW0 Mask                   */
#define PORT1_HWSEL_HW1_Pos                   2                                                       /*!< PORT1 HWSEL: HW1 Position               */
#define PORT1_HWSEL_HW1_Msk                   (0x03UL << PORT1_HWSEL_HW1_Pos)                         /*!< PORT1 HWSEL: HW1 Mask                   */
#define PORT1_HWSEL_HW2_Pos                   4                                                       /*!< PORT1 HWSEL: HW2 Position               */
#define PORT1_HWSEL_HW2_Msk                   (0x03UL << PORT1_HWSEL_HW2_Pos)                         /*!< PORT1 HWSEL: HW2 Mask                   */
#define PORT1_HWSEL_HW3_Pos                   6                                                       /*!< PORT1 HWSEL: HW3 Position               */
#define PORT1_HWSEL_HW3_Msk                   (0x03UL << PORT1_HWSEL_HW3_Pos)                         /*!< PORT1 HWSEL: HW3 Mask                   */
#define PORT1_HWSEL_HW4_Pos                   8                                                       /*!< PORT1 HWSEL: HW4 Position               */
#define PORT1_HWSEL_HW4_Msk                   (0x03UL << PORT1_HWSEL_HW4_Pos)                         /*!< PORT1 HWSEL: HW4 Mask                   */
#define PORT1_HWSEL_HW5_Pos                   10                                                      /*!< PORT1 HWSEL: HW5 Position               */
#define PORT1_HWSEL_HW5_Msk                   (0x03UL << PORT1_HWSEL_HW5_Pos)                         /*!< PORT1 HWSEL: HW5 Mask                   */


/* ================================================================================ */
/* ================         struct 'PORT2' Position & Mask         ================ */
/* ================================================================================ */


/* ----------------------------------  PORT2_OUT  --------------------------------- */
#define PORT2_OUT_P0_Pos                      0                                                       /*!< PORT2 OUT: P0 Position                  */
#define PORT2_OUT_P0_Msk                      (0x01UL << PORT2_OUT_P0_Pos)                            /*!< PORT2 OUT: P0 Mask                      */
#define PORT2_OUT_P1_Pos                      1                                                       /*!< PORT2 OUT: P1 Position                  */
#define PORT2_OUT_P1_Msk                      (0x01UL << PORT2_OUT_P1_Pos)                            /*!< PORT2 OUT: P1 Mask                      */
#define PORT2_OUT_P2_Pos                      2                                                       /*!< PORT2 OUT: P2 Position                  */
#define PORT2_OUT_P2_Msk                      (0x01UL << PORT2_OUT_P2_Pos)                            /*!< PORT2 OUT: P2 Mask                      */
#define PORT2_OUT_P3_Pos                      3                                                       /*!< PORT2 OUT: P3 Position                  */
#define PORT2_OUT_P3_Msk                      (0x01UL << PORT2_OUT_P3_Pos)                            /*!< PORT2 OUT: P3 Mask                      */
#define PORT2_OUT_P4_Pos                      4                                                       /*!< PORT2 OUT: P4 Position                  */
#define PORT2_OUT_P4_Msk                      (0x01UL << PORT2_OUT_P4_Pos)                            /*!< PORT2 OUT: P4 Mask                      */
#define PORT2_OUT_P5_Pos                      5                                                       /*!< PORT2 OUT: P5 Position                  */
#define PORT2_OUT_P5_Msk                      (0x01UL << PORT2_OUT_P5_Pos)                            /*!< PORT2 OUT: P5 Mask                      */
#define PORT2_OUT_P6_Pos                      6                                                       /*!< PORT2 OUT: P6 Position                  */
#define PORT2_OUT_P6_Msk                      (0x01UL << PORT2_OUT_P6_Pos)                            /*!< PORT2 OUT: P6 Mask                      */
#define PORT2_OUT_P7_Pos                      7                                                       /*!< PORT2 OUT: P7 Position                  */
#define PORT2_OUT_P7_Msk                      (0x01UL << PORT2_OUT_P7_Pos)                            /*!< PORT2 OUT: P7 Mask                      */
#define PORT2_OUT_P8_Pos                      8                                                       /*!< PORT2 OUT: P8 Position                  */
#define PORT2_OUT_P8_Msk                      (0x01UL << PORT2_OUT_P8_Pos)                            /*!< PORT2 OUT: P8 Mask                      */
#define PORT2_OUT_P9_Pos                      9                                                       /*!< PORT2 OUT: P9 Position                  */
#define PORT2_OUT_P9_Msk                      (0x01UL << PORT2_OUT_P9_Pos)                            /*!< PORT2 OUT: P9 Mask                      */
#define PORT2_OUT_P10_Pos                     10                                                      /*!< PORT2 OUT: P10 Position                 */
#define PORT2_OUT_P10_Msk                     (0x01UL << PORT2_OUT_P10_Pos)                           /*!< PORT2 OUT: P10 Mask                     */
#define PORT2_OUT_P11_Pos                     11                                                      /*!< PORT2 OUT: P11 Position                 */
#define PORT2_OUT_P11_Msk                     (0x01UL << PORT2_OUT_P11_Pos)                           /*!< PORT2 OUT: P11 Mask                     */

/* ----------------------------------  PORT2_OMR  --------------------------------- */
#define PORT2_OMR_PS0_Pos                     0                                                       /*!< PORT2 OMR: PS0 Position                 */
#define PORT2_OMR_PS0_Msk                     (0x01UL << PORT2_OMR_PS0_Pos)                           /*!< PORT2 OMR: PS0 Mask                     */
#define PORT2_OMR_PS1_Pos                     1                                                       /*!< PORT2 OMR: PS1 Position                 */
#define PORT2_OMR_PS1_Msk                     (0x01UL << PORT2_OMR_PS1_Pos)                           /*!< PORT2 OMR: PS1 Mask                     */
#define PORT2_OMR_PS2_Pos                     2                                                       /*!< PORT2 OMR: PS2 Position                 */
#define PORT2_OMR_PS2_Msk                     (0x01UL << PORT2_OMR_PS2_Pos)                           /*!< PORT2 OMR: PS2 Mask                     */
#define PORT2_OMR_PS3_Pos                     3                                                       /*!< PORT2 OMR: PS3 Position                 */
#define PORT2_OMR_PS3_Msk                     (0x01UL << PORT2_OMR_PS3_Pos)                           /*!< PORT2 OMR: PS3 Mask                     */
#define PORT2_OMR_PS4_Pos                     4                                                       /*!< PORT2 OMR: PS4 Position                 */
#define PORT2_OMR_PS4_Msk                     (0x01UL << PORT2_OMR_PS4_Pos)                           /*!< PORT2 OMR: PS4 Mask                     */
#define PORT2_OMR_PS5_Pos                     5                                                       /*!< PORT2 OMR: PS5 Position                 */
#define PORT2_OMR_PS5_Msk                     (0x01UL << PORT2_OMR_PS5_Pos)                           /*!< PORT2 OMR: PS5 Mask                     */
#define PORT2_OMR_PS6_Pos                     6                                                       /*!< PORT2 OMR: PS6 Position                 */
#define PORT2_OMR_PS6_Msk                     (0x01UL << PORT2_OMR_PS6_Pos)                           /*!< PORT2 OMR: PS6 Mask                     */
#define PORT2_OMR_PS7_Pos                     7                                                       /*!< PORT2 OMR: PS7 Position                 */
#define PORT2_OMR_PS7_Msk                     (0x01UL << PORT2_OMR_PS7_Pos)                           /*!< PORT2 OMR: PS7 Mask                     */
#define PORT2_OMR_PS8_Pos                     8                                                       /*!< PORT2 OMR: PS8 Position                 */
#define PORT2_OMR_PS8_Msk                     (0x01UL << PORT2_OMR_PS8_Pos)                           /*!< PORT2 OMR: PS8 Mask                     */
#define PORT2_OMR_PS9_Pos                     9                                                       /*!< PORT2 OMR: PS9 Position                 */
#define PORT2_OMR_PS9_Msk                     (0x01UL << PORT2_OMR_PS9_Pos)                           /*!< PORT2 OMR: PS9 Mask                     */
#define PORT2_OMR_PS10_Pos                    10                                                      /*!< PORT2 OMR: PS10 Position                */
#define PORT2_OMR_PS10_Msk                    (0x01UL << PORT2_OMR_PS10_Pos)                          /*!< PORT2 OMR: PS10 Mask                    */
#define PORT2_OMR_PS11_Pos                    11                                                      /*!< PORT2 OMR: PS11 Position                */
#define PORT2_OMR_PS11_Msk                    (0x01UL << PORT2_OMR_PS11_Pos)                          /*!< PORT2 OMR: PS11 Mask                    */
#define PORT2_OMR_PR0_Pos                     16                                                      /*!< PORT2 OMR: PR0 Position                 */
#define PORT2_OMR_PR0_Msk                     (0x01UL << PORT2_OMR_PR0_Pos)                           /*!< PORT2 OMR: PR0 Mask                     */
#define PORT2_OMR_PR1_Pos                     17                                                      /*!< PORT2 OMR: PR1 Position                 */
#define PORT2_OMR_PR1_Msk                     (0x01UL << PORT2_OMR_PR1_Pos)                           /*!< PORT2 OMR: PR1 Mask                     */
#define PORT2_OMR_PR2_Pos                     18                                                      /*!< PORT2 OMR: PR2 Position                 */
#define PORT2_OMR_PR2_Msk                     (0x01UL << PORT2_OMR_PR2_Pos)                           /*!< PORT2 OMR: PR2 Mask                     */
#define PORT2_OMR_PR3_Pos                     19                                                      /*!< PORT2 OMR: PR3 Position                 */
#define PORT2_OMR_PR3_Msk                     (0x01UL << PORT2_OMR_PR3_Pos)                           /*!< PORT2 OMR: PR3 Mask                     */
#define PORT2_OMR_PR4_Pos                     20                                                      /*!< PORT2 OMR: PR4 Position                 */
#define PORT2_OMR_PR4_Msk                     (0x01UL << PORT2_OMR_PR4_Pos)                           /*!< PORT2 OMR: PR4 Mask                     */
#define PORT2_OMR_PR5_Pos                     21                                                      /*!< PORT2 OMR: PR5 Position                 */
#define PORT2_OMR_PR5_Msk                     (0x01UL << PORT2_OMR_PR5_Pos)                           /*!< PORT2 OMR: PR5 Mask                     */
#define PORT2_OMR_PR6_Pos                     22                                                      /*!< PORT2 OMR: PR6 Position                 */
#define PORT2_OMR_PR6_Msk                     (0x01UL << PORT2_OMR_PR6_Pos)                           /*!< PORT2 OMR: PR6 Mask                     */
#define PORT2_OMR_PR7_Pos                     23                                                      /*!< PORT2 OMR: PR7 Position                 */
#define PORT2_OMR_PR7_Msk                     (0x01UL << PORT2_OMR_PR7_Pos)                           /*!< PORT2 OMR: PR7 Mask                     */
#define PORT2_OMR_PR8_Pos                     24                                                      /*!< PORT2 OMR: PR8 Position                 */
#define PORT2_OMR_PR8_Msk                     (0x01UL << PORT2_OMR_PR8_Pos)                           /*!< PORT2 OMR: PR8 Mask                     */
#define PORT2_OMR_PR9_Pos                     25                                                      /*!< PORT2 OMR: PR9 Position                 */
#define PORT2_OMR_PR9_Msk                     (0x01UL << PORT2_OMR_PR9_Pos)                           /*!< PORT2 OMR: PR9 Mask                     */
#define PORT2_OMR_PR10_Pos                    26                                                      /*!< PORT2 OMR: PR10 Position                */
#define PORT2_OMR_PR10_Msk                    (0x01UL << PORT2_OMR_PR10_Pos)                          /*!< PORT2 OMR: PR10 Mask                    */
#define PORT2_OMR_PR11_Pos                    27                                                      /*!< PORT2 OMR: PR11 Position                */
#define PORT2_OMR_PR11_Msk                    (0x01UL << PORT2_OMR_PR11_Pos)                          /*!< PORT2 OMR: PR11 Mask                    */

/* ---------------------------------  PORT2_IOCR0  -------------------------------- */
#define PORT2_IOCR0_PC0_Pos                   3                                                       /*!< PORT2 IOCR0: PC0 Position               */
#define PORT2_IOCR0_PC0_Msk                   (0x1fUL << PORT2_IOCR0_PC0_Pos)                         /*!< PORT2 IOCR0: PC0 Mask                   */
#define PORT2_IOCR0_PC1_Pos                   11                                                      /*!< PORT2 IOCR0: PC1 Position               */
#define PORT2_IOCR0_PC1_Msk                   (0x1fUL << PORT2_IOCR0_PC1_Pos)                         /*!< PORT2 IOCR0: PC1 Mask                   */
#define PORT2_IOCR0_PC2_Pos                   19                                                      /*!< PORT2 IOCR0: PC2 Position               */
#define PORT2_IOCR0_PC2_Msk                   (0x1fUL << PORT2_IOCR0_PC2_Pos)                         /*!< PORT2 IOCR0: PC2 Mask                   */
#define PORT2_IOCR0_PC3_Pos                   27                                                      /*!< PORT2 IOCR0: PC3 Position               */
#define PORT2_IOCR0_PC3_Msk                   (0x1fUL << PORT2_IOCR0_PC3_Pos)                         /*!< PORT2 IOCR0: PC3 Mask                   */

/* ---------------------------------  PORT2_IOCR4  -------------------------------- */
#define PORT2_IOCR4_PC4_Pos                   3                                                       /*!< PORT2 IOCR4: PC4 Position               */
#define PORT2_IOCR4_PC4_Msk                   (0x1fUL << PORT2_IOCR4_PC4_Pos)                         /*!< PORT2 IOCR4: PC4 Mask                   */
#define PORT2_IOCR4_PC5_Pos                   11                                                      /*!< PORT2 IOCR4: PC5 Position               */
#define PORT2_IOCR4_PC5_Msk                   (0x1fUL << PORT2_IOCR4_PC5_Pos)                         /*!< PORT2 IOCR4: PC5 Mask                   */
#define PORT2_IOCR4_PC6_Pos                   19                                                      /*!< PORT2 IOCR4: PC6 Position               */
#define PORT2_IOCR4_PC6_Msk                   (0x1fUL << PORT2_IOCR4_PC6_Pos)                         /*!< PORT2 IOCR4: PC6 Mask                   */
#define PORT2_IOCR4_PC7_Pos                   27                                                      /*!< PORT2 IOCR4: PC7 Position               */
#define PORT2_IOCR4_PC7_Msk                   (0x1fUL << PORT2_IOCR4_PC7_Pos)                         /*!< PORT2 IOCR4: PC7 Mask                   */

/* ---------------------------------  PORT2_IOCR8  -------------------------------- */
#define PORT2_IOCR8_PC8_Pos                   3                                                       /*!< PORT2 IOCR8: PC8 Position               */
#define PORT2_IOCR8_PC8_Msk                   (0x1fUL << PORT2_IOCR8_PC8_Pos)                         /*!< PORT2 IOCR8: PC8 Mask                   */
#define PORT2_IOCR8_PC9_Pos                   11                                                      /*!< PORT2 IOCR8: PC9 Position               */
#define PORT2_IOCR8_PC9_Msk                   (0x1fUL << PORT2_IOCR8_PC9_Pos)                         /*!< PORT2 IOCR8: PC9 Mask                   */
#define PORT2_IOCR8_PC10_Pos                  19                                                      /*!< PORT2 IOCR8: PC10 Position              */
#define PORT2_IOCR8_PC10_Msk                  (0x1fUL << PORT2_IOCR8_PC10_Pos)                        /*!< PORT2 IOCR8: PC10 Mask                  */
#define PORT2_IOCR8_PC11_Pos                  27                                                      /*!< PORT2 IOCR8: PC11 Position              */
#define PORT2_IOCR8_PC11_Msk                  (0x1fUL << PORT2_IOCR8_PC11_Pos)                        /*!< PORT2 IOCR8: PC11 Mask                  */

/* ----------------------------------  PORT2_IN  ---------------------------------- */
#define PORT2_IN_P0_Pos                       0                                                       /*!< PORT2 IN: P0 Position                   */
#define PORT2_IN_P0_Msk                       (0x01UL << PORT2_IN_P0_Pos)                             /*!< PORT2 IN: P0 Mask                       */
#define PORT2_IN_P1_Pos                       1                                                       /*!< PORT2 IN: P1 Position                   */
#define PORT2_IN_P1_Msk                       (0x01UL << PORT2_IN_P1_Pos)                             /*!< PORT2 IN: P1 Mask                       */
#define PORT2_IN_P2_Pos                       2                                                       /*!< PORT2 IN: P2 Position                   */
#define PORT2_IN_P2_Msk                       (0x01UL << PORT2_IN_P2_Pos)                             /*!< PORT2 IN: P2 Mask                       */
#define PORT2_IN_P3_Pos                       3                                                       /*!< PORT2 IN: P3 Position                   */
#define PORT2_IN_P3_Msk                       (0x01UL << PORT2_IN_P3_Pos)                             /*!< PORT2 IN: P3 Mask                       */
#define PORT2_IN_P4_Pos                       4                                                       /*!< PORT2 IN: P4 Position                   */
#define PORT2_IN_P4_Msk                       (0x01UL << PORT2_IN_P4_Pos)                             /*!< PORT2 IN: P4 Mask                       */
#define PORT2_IN_P5_Pos                       5                                                       /*!< PORT2 IN: P5 Position                   */
#define PORT2_IN_P5_Msk                       (0x01UL << PORT2_IN_P5_Pos)                             /*!< PORT2 IN: P5 Mask                       */
#define PORT2_IN_P6_Pos                       6                                                       /*!< PORT2 IN: P6 Position                   */
#define PORT2_IN_P6_Msk                       (0x01UL << PORT2_IN_P6_Pos)                             /*!< PORT2 IN: P6 Mask                       */
#define PORT2_IN_P7_Pos                       7                                                       /*!< PORT2 IN: P7 Position                   */
#define PORT2_IN_P7_Msk                       (0x01UL << PORT2_IN_P7_Pos)                             /*!< PORT2 IN: P7 Mask                       */
#define PORT2_IN_P8_Pos                       8                                                       /*!< PORT2 IN: P8 Position                   */
#define PORT2_IN_P8_Msk                       (0x01UL << PORT2_IN_P8_Pos)                             /*!< PORT2 IN: P8 Mask                       */
#define PORT2_IN_P9_Pos                       9                                                       /*!< PORT2 IN: P9 Position                   */
#define PORT2_IN_P9_Msk                       (0x01UL << PORT2_IN_P9_Pos)                             /*!< PORT2 IN: P9 Mask                       */
#define PORT2_IN_P10_Pos                      10                                                      /*!< PORT2 IN: P10 Position                  */
#define PORT2_IN_P10_Msk                      (0x01UL << PORT2_IN_P10_Pos)                            /*!< PORT2 IN: P10 Mask                      */
#define PORT2_IN_P11_Pos                      11                                                      /*!< PORT2 IN: P11 Position                  */
#define PORT2_IN_P11_Msk                      (0x01UL << PORT2_IN_P11_Pos)                            /*!< PORT2 IN: P11 Mask                      */

/* ---------------------------------  PORT2_PHCR0  -------------------------------- */
#define PORT2_PHCR0_PH0_Pos                   2                                                       /*!< PORT2 PHCR0: PH0 Position               */
#define PORT2_PHCR0_PH0_Msk                   (0x01UL << PORT2_PHCR0_PH0_Pos)                         /*!< PORT2 PHCR0: PH0 Mask                   */
#define PORT2_PHCR0_PH1_Pos                   6                                                       /*!< PORT2 PHCR0: PH1 Position               */
#define PORT2_PHCR0_PH1_Msk                   (0x01UL << PORT2_PHCR0_PH1_Pos)                         /*!< PORT2 PHCR0: PH1 Mask                   */
#define PORT2_PHCR0_PH2_Pos                   10                                                      /*!< PORT2 PHCR0: PH2 Position               */
#define PORT2_PHCR0_PH2_Msk                   (0x01UL << PORT2_PHCR0_PH2_Pos)                         /*!< PORT2 PHCR0: PH2 Mask                   */
#define PORT2_PHCR0_PH3_Pos                   14                                                      /*!< PORT2 PHCR0: PH3 Position               */
#define PORT2_PHCR0_PH3_Msk                   (0x01UL << PORT2_PHCR0_PH3_Pos)                         /*!< PORT2 PHCR0: PH3 Mask                   */
#define PORT2_PHCR0_PH4_Pos                   18                                                      /*!< PORT2 PHCR0: PH4 Position               */
#define PORT2_PHCR0_PH4_Msk                   (0x01UL << PORT2_PHCR0_PH4_Pos)                         /*!< PORT2 PHCR0: PH4 Mask                   */
#define PORT2_PHCR0_PH5_Pos                   22                                                      /*!< PORT2 PHCR0: PH5 Position               */
#define PORT2_PHCR0_PH5_Msk                   (0x01UL << PORT2_PHCR0_PH5_Pos)                         /*!< PORT2 PHCR0: PH5 Mask                   */
#define PORT2_PHCR0_PH6_Pos                   26                                                      /*!< PORT2 PHCR0: PH6 Position               */
#define PORT2_PHCR0_PH6_Msk                   (0x01UL << PORT2_PHCR0_PH6_Pos)                         /*!< PORT2 PHCR0: PH6 Mask                   */
#define PORT2_PHCR0_PH7_Pos                   30                                                      /*!< PORT2 PHCR0: PH7 Position               */
#define PORT2_PHCR0_PH7_Msk                   (0x01UL << PORT2_PHCR0_PH7_Pos)                         /*!< PORT2 PHCR0: PH7 Mask                   */

/* ---------------------------------  PORT2_PHCR1  -------------------------------- */
#define PORT2_PHCR1_PH8_Pos                   2                                                       /*!< PORT2 PHCR1: PH8 Position               */
#define PORT2_PHCR1_PH8_Msk                   (0x01UL << PORT2_PHCR1_PH8_Pos)                         /*!< PORT2 PHCR1: PH8 Mask                   */
#define PORT2_PHCR1_PH9_Pos                   6                                                       /*!< PORT2 PHCR1: PH9 Position               */
#define PORT2_PHCR1_PH9_Msk                   (0x01UL << PORT2_PHCR1_PH9_Pos)                         /*!< PORT2 PHCR1: PH9 Mask                   */
#define PORT2_PHCR1_PH10_Pos                  10                                                      /*!< PORT2 PHCR1: PH10 Position              */
#define PORT2_PHCR1_PH10_Msk                  (0x01UL << PORT2_PHCR1_PH10_Pos)                        /*!< PORT2 PHCR1: PH10 Mask                  */
#define PORT2_PHCR1_PH11_Pos                  14                                                      /*!< PORT2 PHCR1: PH11 Position              */
#define PORT2_PHCR1_PH11_Msk                  (0x01UL << PORT2_PHCR1_PH11_Pos)                        /*!< PORT2 PHCR1: PH11 Mask                  */

/* ---------------------------------  PORT2_PDISC  -------------------------------- */
#define PORT2_PDISC_PDIS0_Pos                 0                                                       /*!< PORT2 PDISC: PDIS0 Position             */
#define PORT2_PDISC_PDIS0_Msk                 (0x01UL << PORT2_PDISC_PDIS0_Pos)                       /*!< PORT2 PDISC: PDIS0 Mask                 */
#define PORT2_PDISC_PDIS1_Pos                 1                                                       /*!< PORT2 PDISC: PDIS1 Position             */
#define PORT2_PDISC_PDIS1_Msk                 (0x01UL << PORT2_PDISC_PDIS1_Pos)                       /*!< PORT2 PDISC: PDIS1 Mask                 */
#define PORT2_PDISC_PDIS2_Pos                 2                                                       /*!< PORT2 PDISC: PDIS2 Position             */
#define PORT2_PDISC_PDIS2_Msk                 (0x01UL << PORT2_PDISC_PDIS2_Pos)                       /*!< PORT2 PDISC: PDIS2 Mask                 */
#define PORT2_PDISC_PDIS3_Pos                 3                                                       /*!< PORT2 PDISC: PDIS3 Position             */
#define PORT2_PDISC_PDIS3_Msk                 (0x01UL << PORT2_PDISC_PDIS3_Pos)                       /*!< PORT2 PDISC: PDIS3 Mask                 */
#define PORT2_PDISC_PDIS4_Pos                 4                                                       /*!< PORT2 PDISC: PDIS4 Position             */
#define PORT2_PDISC_PDIS4_Msk                 (0x01UL << PORT2_PDISC_PDIS4_Pos)                       /*!< PORT2 PDISC: PDIS4 Mask                 */
#define PORT2_PDISC_PDIS5_Pos                 5                                                       /*!< PORT2 PDISC: PDIS5 Position             */
#define PORT2_PDISC_PDIS5_Msk                 (0x01UL << PORT2_PDISC_PDIS5_Pos)                       /*!< PORT2 PDISC: PDIS5 Mask                 */
#define PORT2_PDISC_PDIS6_Pos                 6                                                       /*!< PORT2 PDISC: PDIS6 Position             */
#define PORT2_PDISC_PDIS6_Msk                 (0x01UL << PORT2_PDISC_PDIS6_Pos)                       /*!< PORT2 PDISC: PDIS6 Mask                 */
#define PORT2_PDISC_PDIS7_Pos                 7                                                       /*!< PORT2 PDISC: PDIS7 Position             */
#define PORT2_PDISC_PDIS7_Msk                 (0x01UL << PORT2_PDISC_PDIS7_Pos)                       /*!< PORT2 PDISC: PDIS7 Mask                 */
#define PORT2_PDISC_PDIS8_Pos                 8                                                       /*!< PORT2 PDISC: PDIS8 Position             */
#define PORT2_PDISC_PDIS8_Msk                 (0x01UL << PORT2_PDISC_PDIS8_Pos)                       /*!< PORT2 PDISC: PDIS8 Mask                 */
#define PORT2_PDISC_PDIS9_Pos                 9                                                       /*!< PORT2 PDISC: PDIS9 Position             */
#define PORT2_PDISC_PDIS9_Msk                 (0x01UL << PORT2_PDISC_PDIS9_Pos)                       /*!< PORT2 PDISC: PDIS9 Mask                 */
#define PORT2_PDISC_PDIS10_Pos                10                                                      /*!< PORT2 PDISC: PDIS10 Position            */
#define PORT2_PDISC_PDIS10_Msk                (0x01UL << PORT2_PDISC_PDIS10_Pos)                      /*!< PORT2 PDISC: PDIS10 Mask                */
#define PORT2_PDISC_PDIS11_Pos                11                                                      /*!< PORT2 PDISC: PDIS11 Position            */
#define PORT2_PDISC_PDIS11_Msk                (0x01UL << PORT2_PDISC_PDIS11_Pos)                      /*!< PORT2 PDISC: PDIS11 Mask                */

/* ----------------------------------  PORT2_PPS  --------------------------------- */
#define PORT2_PPS_PPS0_Pos                    0                                                       /*!< PORT2 PPS: PPS0 Position                */
#define PORT2_PPS_PPS0_Msk                    (0x01UL << PORT2_PPS_PPS0_Pos)                          /*!< PORT2 PPS: PPS0 Mask                    */
#define PORT2_PPS_PPS1_Pos                    1                                                       /*!< PORT2 PPS: PPS1 Position                */
#define PORT2_PPS_PPS1_Msk                    (0x01UL << PORT2_PPS_PPS1_Pos)                          /*!< PORT2 PPS: PPS1 Mask                    */
#define PORT2_PPS_PPS2_Pos                    2                                                       /*!< PORT2 PPS: PPS2 Position                */
#define PORT2_PPS_PPS2_Msk                    (0x01UL << PORT2_PPS_PPS2_Pos)                          /*!< PORT2 PPS: PPS2 Mask                    */
#define PORT2_PPS_PPS3_Pos                    3                                                       /*!< PORT2 PPS: PPS3 Position                */
#define PORT2_PPS_PPS3_Msk                    (0x01UL << PORT2_PPS_PPS3_Pos)                          /*!< PORT2 PPS: PPS3 Mask                    */
#define PORT2_PPS_PPS4_Pos                    4                                                       /*!< PORT2 PPS: PPS4 Position                */
#define PORT2_PPS_PPS4_Msk                    (0x01UL << PORT2_PPS_PPS4_Pos)                          /*!< PORT2 PPS: PPS4 Mask                    */
#define PORT2_PPS_PPS5_Pos                    5                                                       /*!< PORT2 PPS: PPS5 Position                */
#define PORT2_PPS_PPS5_Msk                    (0x01UL << PORT2_PPS_PPS5_Pos)                          /*!< PORT2 PPS: PPS5 Mask                    */
#define PORT2_PPS_PPS6_Pos                    6                                                       /*!< PORT2 PPS: PPS6 Position                */
#define PORT2_PPS_PPS6_Msk                    (0x01UL << PORT2_PPS_PPS6_Pos)                          /*!< PORT2 PPS: PPS6 Mask                    */
#define PORT2_PPS_PPS7_Pos                    7                                                       /*!< PORT2 PPS: PPS7 Position                */
#define PORT2_PPS_PPS7_Msk                    (0x01UL << PORT2_PPS_PPS7_Pos)                          /*!< PORT2 PPS: PPS7 Mask                    */
#define PORT2_PPS_PPS8_Pos                    8                                                       /*!< PORT2 PPS: PPS8 Position                */
#define PORT2_PPS_PPS8_Msk                    (0x01UL << PORT2_PPS_PPS8_Pos)                          /*!< PORT2 PPS: PPS8 Mask                    */
#define PORT2_PPS_PPS9_Pos                    9                                                       /*!< PORT2 PPS: PPS9 Position                */
#define PORT2_PPS_PPS9_Msk                    (0x01UL << PORT2_PPS_PPS9_Pos)                          /*!< PORT2 PPS: PPS9 Mask                    */
#define PORT2_PPS_PPS10_Pos                   10                                                      /*!< PORT2 PPS: PPS10 Position               */
#define PORT2_PPS_PPS10_Msk                   (0x01UL << PORT2_PPS_PPS10_Pos)                         /*!< PORT2 PPS: PPS10 Mask                   */
#define PORT2_PPS_PPS11_Pos                   11                                                      /*!< PORT2 PPS: PPS11 Position               */
#define PORT2_PPS_PPS11_Msk                   (0x01UL << PORT2_PPS_PPS11_Pos)                         /*!< PORT2 PPS: PPS11 Mask                   */

/* ---------------------------------  PORT2_HWSEL  -------------------------------- */
#define PORT2_HWSEL_HW0_Pos                   0                                                       /*!< PORT2 HWSEL: HW0 Position               */
#define PORT2_HWSEL_HW0_Msk                   (0x03UL << PORT2_HWSEL_HW0_Pos)                         /*!< PORT2 HWSEL: HW0 Mask                   */
#define PORT2_HWSEL_HW1_Pos                   2                                                       /*!< PORT2 HWSEL: HW1 Position               */
#define PORT2_HWSEL_HW1_Msk                   (0x03UL << PORT2_HWSEL_HW1_Pos)                         /*!< PORT2 HWSEL: HW1 Mask                   */
#define PORT2_HWSEL_HW2_Pos                   4                                                       /*!< PORT2 HWSEL: HW2 Position               */
#define PORT2_HWSEL_HW2_Msk                   (0x03UL << PORT2_HWSEL_HW2_Pos)                         /*!< PORT2 HWSEL: HW2 Mask                   */
#define PORT2_HWSEL_HW3_Pos                   6                                                       /*!< PORT2 HWSEL: HW3 Position               */
#define PORT2_HWSEL_HW3_Msk                   (0x03UL << PORT2_HWSEL_HW3_Pos)                         /*!< PORT2 HWSEL: HW3 Mask                   */
#define PORT2_HWSEL_HW4_Pos                   8                                                       /*!< PORT2 HWSEL: HW4 Position               */
#define PORT2_HWSEL_HW4_Msk                   (0x03UL << PORT2_HWSEL_HW4_Pos)                         /*!< PORT2 HWSEL: HW4 Mask                   */
#define PORT2_HWSEL_HW5_Pos                   10                                                      /*!< PORT2 HWSEL: HW5 Position               */
#define PORT2_HWSEL_HW5_Msk                   (0x03UL << PORT2_HWSEL_HW5_Pos)                         /*!< PORT2 HWSEL: HW5 Mask                   */
#define PORT2_HWSEL_HW6_Pos                   12                                                      /*!< PORT2 HWSEL: HW6 Position               */
#define PORT2_HWSEL_HW6_Msk                   (0x03UL << PORT2_HWSEL_HW6_Pos)                         /*!< PORT2 HWSEL: HW6 Mask                   */
#define PORT2_HWSEL_HW7_Pos                   14                                                      /*!< PORT2 HWSEL: HW7 Position               */
#define PORT2_HWSEL_HW7_Msk                   (0x03UL << PORT2_HWSEL_HW7_Pos)                         /*!< PORT2 HWSEL: HW7 Mask                   */
#define PORT2_HWSEL_HW8_Pos                   16                                                      /*!< PORT2 HWSEL: HW8 Position               */
#define PORT2_HWSEL_HW8_Msk                   (0x03UL << PORT2_HWSEL_HW8_Pos)                         /*!< PORT2 HWSEL: HW8 Mask                   */
#define PORT2_HWSEL_HW9_Pos                   18                                                      /*!< PORT2 HWSEL: HW9 Position               */
#define PORT2_HWSEL_HW9_Msk                   (0x03UL << PORT2_HWSEL_HW9_Pos)                         /*!< PORT2 HWSEL: HW9 Mask                   */
#define PORT2_HWSEL_HW10_Pos                  20                                                      /*!< PORT2 HWSEL: HW10 Position              */
#define PORT2_HWSEL_HW10_Msk                  (0x03UL << PORT2_HWSEL_HW10_Pos)                        /*!< PORT2 HWSEL: HW10 Mask                  */
#define PORT2_HWSEL_HW11_Pos                  22                                                      /*!< PORT2 HWSEL: HW11 Position              */
#define PORT2_HWSEL_HW11_Msk                  (0x03UL << PORT2_HWSEL_HW11_Pos)                        /*!< PORT2 HWSEL: HW11 Mask                  */



/* ================================================================================ */
/* ================              Peripheral memory map             ================ */
/* ================================================================================ */

#define PPB_BASE                        0xE000E000UL
#define ERU0_BASE                       0x40010600UL
#define PAU_BASE                        0x40000000UL
#define NVM_BASE                        0x40050000UL
#define WDT_BASE                        0x40020000UL
#define RTC_BASE                        0x40010A00UL
#define PRNG_BASE                       0x48020000UL
#define USIC0_BASE                      0x48000008UL
#define USIC0_CH0_BASE                  0x48000000UL
#define USIC0_CH1_BASE                  0x48000200UL
#define SCU_GENERAL_BASE                0x40010000UL
#define SCU_INTERRUPT_BASE              0x40010038UL
#define SCU_POWER_BASE                  0x40010200UL
#define SCU_CLK_BASE                    0x40010300UL
#define SCU_RESET_BASE                  0x40010400UL
#define SCU_ANALOG_BASE                 0x40011000UL
#define CCU40_BASE                      0x48040000UL
#define CCU40_CC40_BASE                 0x48040100UL
#define CCU40_CC41_BASE                 0x48040200UL
#define CCU40_CC42_BASE                 0x48040300UL
#define CCU40_CC43_BASE                 0x48040400UL
#define VADC_BASE                       0x48030000UL
#define SHS0_BASE                       0x48034000UL
#define PORT0_BASE                      0x40040000UL
#define PORT1_BASE                      0x40040100UL
#define PORT2_BASE                      0x40040200UL


/* ================================================================================ */
/* ================             Peripheral declaration             ================ */
/* ================================================================================ */

#define PPB                             ((PPB_Type                *) PPB_BASE)
#define ERU0                            ((ERU_GLOBAL_TypeDef                *) ERU0_BASE)
#define PAU                             ((PAU_Type                *) PAU_BASE)
#define NVM                             ((NVM_Type                *) NVM_BASE)
#define WDT                             ((WDT_GLOBAL_TypeDef                *) WDT_BASE)
#define RTC                             ((RTC_GLOBAL_TypeDef                *) RTC_BASE)
#define PRNG                            ((PRNG_Type               *) PRNG_BASE)
#define USIC0                           ((USIC_GLOBAL_TypeDef               *) USIC0_BASE)
#define USIC0_CH0                       ((USIC_CH_TypeDef            *) USIC0_CH0_BASE)
#define USIC0_CH1                       ((USIC_CH_TypeDef            *) USIC0_CH1_BASE)
#define SCU_GENERAL                     ((SCU_GENERAL_Type        *) SCU_GENERAL_BASE)
#define SCU_INTERRUPT                   ((SCU_INTERRUPT_TypeDef      *) SCU_INTERRUPT_BASE)
#define SCU_POWER                       ((SCU_POWER_Type          *) SCU_POWER_BASE)
#define SCU_CLK                         ((SCU_CLK_TypeDef            *) SCU_CLK_BASE)
#define SCU_RESET                       ((SCU_RESET_Type          *) SCU_RESET_BASE)
#define SCU_ANALOG                      ((SCU_ANALOG_Type         *) SCU_ANALOG_BASE)
#define CCU40                           ((CCU4_GLOBAL_TypeDef               *) CCU40_BASE)
#define CCU40_CC40                      ((CCU4_CC4_TypeDef           *) CCU40_CC40_BASE)
#define CCU40_CC41                      ((CCU4_CC4_TypeDef           *) CCU40_CC41_BASE)
#define CCU40_CC42                      ((CCU4_CC4_TypeDef           *) CCU40_CC42_BASE)
#define CCU40_CC43                      ((CCU4_CC4_TypeDef           *) CCU40_CC43_BASE)
#define VADC                            ((VADC_GLOBAL_TypeDef               *) VADC_BASE)
#define SHS0                            ((SHS_Type                *) SHS0_BASE)
#define PORT0                           ((PORT0_Type              *) PORT0_BASE)
#define PORT1                           ((PORT1_Type              *) PORT1_BASE)
#define PORT2                           ((PORT2_Type              *) PORT2_BASE)


/** @} */ /* End of group Device_Peripheral_Registers */
/** @} */ /* End of group XMC1100 */
/** @} */ /* End of group Infineon */

#ifdef __cplusplus
}
#endif


#endif  /* XMC1100_H */

