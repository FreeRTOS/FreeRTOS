/**
 * \file
 *
 * \brief Header file for SAMD20G15
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef _SAMD20G15_
#define _SAMD20G15_

/**
 * \ingroup SAMD20_definitions
 * \addtogroup SAMD20G15_definitions SAMD20G15 definitions
 * This file defines all structures and symbols for SAMD20G15:
 *   - registers and bitfields
 *   - peripheral base address
 *   - peripheral ID
 *   - PIO definitions
*/
/*@{*/

#ifdef __cplusplus
 extern "C" {
#endif

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#include <stdint.h>
#ifndef __cplusplus
typedef volatile const uint32_t RoReg;   /**< Read only 32-bit register (volatile const unsigned int) */
typedef volatile const uint16_t RoReg16; /**< Read only 16-bit register (volatile const unsigned int) */
typedef volatile const uint8_t  RoReg8;  /**< Read only  8-bit register (volatile const unsigned int) */
#else
typedef volatile       uint32_t RoReg;   /**< Read only 32-bit register (volatile const unsigned int) */
typedef volatile       uint16_t RoReg16; /**< Read only 16-bit register (volatile const unsigned int) */
typedef volatile       uint8_t  RoReg8;  /**< Read only  8-bit register (volatile const unsigned int) */
#endif
typedef volatile       uint32_t WoReg;   /**< Write only 32-bit register (volatile unsigned int) */
typedef volatile       uint16_t WoReg16; /**< Write only 16-bit register (volatile unsigned int) */
typedef volatile       uint32_t WoReg8;  /**< Write only  8-bit register (volatile unsigned int) */
typedef volatile       uint32_t RwReg;   /**< Read-Write 32-bit register (volatile unsigned int) */
typedef volatile       uint16_t RwReg16; /**< Read-Write 16-bit register (volatile unsigned int) */
typedef volatile       uint8_t  RwReg8;  /**< Read-Write  8-bit register (volatile unsigned int) */
#define CAST(type, value) ((type *)(value))
#define REG_ACCESS(type, address) (*(type*)(address)) /**< C code: Register value */
#else
#define CAST(type, value) (value)
#define REG_ACCESS(type, address) (address) /**< Assembly code: Register address */
#endif

/* ************************************************************************** */
/**  CMSIS DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */
/** \defgroup SAMD20G15_cmsis CMSIS Definitions */
/*@{*/

/** Interrupt Number Definition */
typedef enum IRQn
{
  /******  Cortex-M0+ Processor Exceptions Numbers *******************************/
  NonMaskableInt_IRQn      = -14, /**<  2 Non Maskable Interrupt                 */
  HardFault_IRQn           = -13, /**<  3 Cortex-M0+ Hard Fault Interrupt        */
  SVCall_IRQn              = -5,  /**< 11 Cortex-M0+ SV Call Interrupt           */
  PendSV_IRQn              = -2,  /**< 14 Cortex-M0+ Pend SV Interrupt           */
  SysTick_IRQn             = -1,  /**< 15 Cortex-M0+ System Tick Interrupt       */
  /******  SAMD20G15-specific Interrupt Numbers ***********************/
  PM_IRQn                  =  0, /**<  0 SAMD20G15 Power Manager (PM) */
  SYSCTRL_IRQn             =  1, /**<  1 SAMD20G15 System Control (SYSCTRL) */
  WDT_IRQn                 =  2, /**<  2 SAMD20G15 Watchdog Timer (WDT) */
  RTC_IRQn                 =  3, /**<  3 SAMD20G15 Real-Time Counter (RTC) */
  EIC_IRQn                 =  4, /**<  4 SAMD20G15 External Interrupt Controller (EIC) */
  NVMCTRL_IRQn             =  5, /**<  5 SAMD20G15 Non-Volatile Memory Controller (NVMCTRL) */
  EVSYS_IRQn               =  6, /**<  6 SAMD20G15 Event System Interface (EVSYS) */
  SERCOM0_IRQn             =  7, /**<  7 SAMD20G15 Serial Communication Interface 0 (SERCOM0) */
  SERCOM1_IRQn             =  8, /**<  8 SAMD20G15 Serial Communication Interface 1 (SERCOM1) */
  SERCOM2_IRQn             =  9, /**<  9 SAMD20G15 Serial Communication Interface 2 (SERCOM2) */
  SERCOM3_IRQn             = 10, /**< 10 SAMD20G15 Serial Communication Interface 3 (SERCOM3) */
  SERCOM4_IRQn             = 11, /**< 11 SAMD20G15 Serial Communication Interface 4 (SERCOM4) */
  SERCOM5_IRQn             = 12, /**< 12 SAMD20G15 Serial Communication Interface 5 (SERCOM5) */
  TC0_IRQn                 = 13, /**< 13 SAMD20G15 Basic Timer Counter 0 (TC0) */
  TC1_IRQn                 = 14, /**< 14 SAMD20G15 Basic Timer Counter 1 (TC1) */
  TC2_IRQn                 = 15, /**< 15 SAMD20G15 Basic Timer Counter 2 (TC2) */
  TC3_IRQn                 = 16, /**< 16 SAMD20G15 Basic Timer Counter 3 (TC3) */
  TC4_IRQn                 = 17, /**< 17 SAMD20G15 Basic Timer Counter 4 (TC4) */
  TC5_IRQn                 = 18, /**< 18 SAMD20G15 Basic Timer Counter 5 (TC5) */
  TC6_IRQn                 = 19, /**< 19 SAMD20G15 Basic Timer Counter 6 (TC6) */
  TC7_IRQn                 = 20, /**< 20 SAMD20G15 Basic Timer Counter 7 (TC7) */
  ADC_IRQn                 = 21, /**< 21 SAMD20G15 Analog Digital Converter (ADC) */
  AC_IRQn                  = 22, /**< 22 SAMD20G15 Analog Comparators (AC) */
  DAC_IRQn                 = 23, /**< 23 SAMD20G15 Digital Analog Converter (DAC) */

  PERIPH_COUNT_IRQn        = 24  /**< Number of peripheral IDs */
} IRQn_Type;

typedef struct _DeviceVectors
{
  /* Stack pointer */
  void* pvStack;

  /* Cortex-M handlers */
  void* pfnReset_Handler;
  void* pfnNMI_Handler;
  void* pfnHardFault_Handler;
  void* pfnReservedM12;
  void* pfnReservedM11;
  void* pfnReservedM10;
  void* pfnReservedM9;
  void* pfnReservedM8;
  void* pfnReservedM7;
  void* pfnReservedM6;
  void* pfnSVC_Handler;
  void* pfnReservedM4;
  void* pfnReservedM3;
  void* pfnPendSV_Handler;
  void* pfnSysTick_Handler;

  /* Peripheral handlers */
  void* pfnPM_Handler;                    /*  0 Power Manager */
  void* pfnSYSCTRL_Handler;               /*  1 System Control */
  void* pfnWDT_Handler;                   /*  2 Watchdog Timer */
  void* pfnRTC_Handler;                   /*  3 Real-Time Counter */
  void* pfnEIC_Handler;                   /*  4 External Interrupt Controller */
  void* pfnNVMCTRL_Handler;               /*  5 Non-Volatile Memory Controller */
  void* pfnEVSYS_Handler;                 /*  6 Event System Interface */
  void* pfnSERCOM0_Handler;               /*  7 Serial Communication Interface 0 */
  void* pfnSERCOM1_Handler;               /*  8 Serial Communication Interface 1 */
  void* pfnSERCOM2_Handler;               /*  9 Serial Communication Interface 2 */
  void* pfnSERCOM3_Handler;               /* 10 Serial Communication Interface 3 */
  void* pfnSERCOM4_Handler;               /* 11 Serial Communication Interface 4 */
  void* pfnSERCOM5_Handler;               /* 12 Serial Communication Interface 5 */
  void* pfnTC0_Handler;                   /* 13 Basic Timer Counter 0 */
  void* pfnTC1_Handler;                   /* 14 Basic Timer Counter 1 */
  void* pfnTC2_Handler;                   /* 15 Basic Timer Counter 2 */
  void* pfnTC3_Handler;                   /* 16 Basic Timer Counter 3 */
  void* pfnTC4_Handler;                   /* 17 Basic Timer Counter 4 */
  void* pfnTC5_Handler;                   /* 18 Basic Timer Counter 5 */
  void* pfnTC6_Handler;                   /* 19 Basic Timer Counter 6 */
  void* pfnTC7_Handler;                   /* 20 Basic Timer Counter 7 */
  void* pfnADC_Handler;                   /* 21 Analog Digital Converter */
  void* pfnAC_Handler;                    /* 22 Analog Comparators */
  void* pfnDAC_Handler;                   /* 23 Digital Analog Converter */
} DeviceVectors;

/* Cortex-M0+ processor handlers */
void Reset_Handler               ( void );
void NMI_Handler                 ( void );
void HardFault_Handler           ( void );
void SVC_Handler                 ( void );
void PendSV_Handler              ( void );
void SysTick_Handler             ( void );

/* Peripherals handlers */
void PM_Handler                  ( void );
void SYSCTRL_Handler             ( void );
void WDT_Handler                 ( void );
void RTC_Handler                 ( void );
void EIC_Handler                 ( void );
void NVMCTRL_Handler             ( void );
void EVSYS_Handler               ( void );
void SERCOM0_Handler             ( void );
void SERCOM1_Handler             ( void );
void SERCOM2_Handler             ( void );
void SERCOM3_Handler             ( void );
void SERCOM4_Handler             ( void );
void SERCOM5_Handler             ( void );
void TC0_Handler                 ( void );
void TC1_Handler                 ( void );
void TC2_Handler                 ( void );
void TC3_Handler                 ( void );
void TC4_Handler                 ( void );
void TC5_Handler                 ( void );
void TC6_Handler                 ( void );
void TC7_Handler                 ( void );
void ADC_Handler                 ( void );
void AC_Handler                  ( void );
void DAC_Handler                 ( void );

/*
 * \brief Configuration of the Cortex-M0+ Processor and Core Peripherals
 */

#define LITTLE_ENDIAN          1        
#define __CM0PLUS_REV          1         /*!< Core revision r0p1 */
#define __MPU_PRESENT          0         /*!< MPU present or not */
#define __NVIC_PRIO_BITS       2         /*!< Number of bits used for Priority Levels */
#define __VTOR_PRESENT         1         /*!< VTOR present or not */
#define __Vendor_SysTickConfig 0         /*!< Set to 1 if different SysTick Config is used */

/**
 * \brief CMSIS includes
 */

#include <core_cm0plus.h>
#if !defined DONT_USE_CMSIS_INIT
#include "system_samd20.h"
#endif /* DONT_USE_CMSIS_INIT */

/*@}*/

/* ************************************************************************** */
/**  SOFTWARE PERIPHERAL API DEFINITION FOR SAMD20G15 */
/* ************************************************************************** */
/** \defgroup SAMD20G15_api Peripheral Software API */
/*@{*/

#include "component/component_ac.h"
#include "component/component_adc.h"
#include "component/component_dac.h"
#include "component/component_dsu.h"
#include "component/component_eic.h"
#include "component/component_evsys.h"
#include "component/component_gclk.h"
#include "component/component_nvmctrl.h"
#include "component/component_pac.h"
#include "component/component_pm.h"
#include "component/component_port.h"
#include "component/component_rtc.h"
#include "component/component_sercom.h"
#include "component/component_sysctrl.h"
#include "component/component_tc.h"
#include "component/component_wdt.h"
/*@}*/

/* ************************************************************************** */
/**  REGISTERS ACCESS DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */
/** \defgroup SAMD20G15_reg Registers Access Definitions */
/*@{*/

#include "instance/instance_ac.h"
#include "instance/instance_adc.h"
#include "instance/instance_dac.h"
#include "instance/instance_dsu.h"
#include "instance/instance_eic.h"
#include "instance/instance_evsys.h"
#include "instance/instance_gclk.h"
#include "instance/instance_nvmctrl.h"
#include "instance/instance_pac0.h"
#include "instance/instance_pac1.h"
#include "instance/instance_pac2.h"
#include "instance/instance_pm.h"
#include "instance/instance_port.h"
#include "instance/instance_rtc.h"
#include "instance/instance_sercom0.h"
#include "instance/instance_sercom1.h"
#include "instance/instance_sercom2.h"
#include "instance/instance_sercom3.h"
#include "instance/instance_sercom4.h"
#include "instance/instance_sercom5.h"
#include "instance/instance_sysctrl.h"
#include "instance/instance_tc0.h"
#include "instance/instance_tc1.h"
#include "instance/instance_tc2.h"
#include "instance/instance_tc3.h"
#include "instance/instance_tc4.h"
#include "instance/instance_tc5.h"
#include "instance/instance_tc6.h"
#include "instance/instance_tc7.h"
#include "instance/instance_wdt.h"
/*@}*/

/* ************************************************************************** */
/**  PERIPHERAL ID DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */
/** \defgroup SAMD20G15_id Peripheral Ids Definitions */
/*@{*/

// Peripheral instances on HPB0 bridge
#define ID_PAC0           0 /**< \brief Peripheral Access Controller PAC (PAC0) */
#define ID_PM             1 /**< \brief Power Manager (PM) */
#define ID_SYSCTRL        2 /**< \brief System Control (SYSCTRL) */
#define ID_GCLK           3 /**< \brief Generic Clock Generator (GCLK) */
#define ID_WDT            4 /**< \brief Watchdog Timer (WDT) */
#define ID_RTC            5 /**< \brief Real-Time Counter (RTC) */
#define ID_EIC            6 /**< \brief External Interrupt Controller (EIC) */

// Peripheral instances on HPB1 bridge
#define ID_PAC1          32 /**< \brief Peripheral Access Controller PAC (PAC1) */
#define ID_DSU           33 /**< \brief Device Service Unit (DSU) */
#define ID_NVMCTRL       34 /**< \brief Non-Volatile Memory Controller (NVMCTRL) */
#define ID_PORT          35 /**< \brief Port Module (PORT) */

// Peripheral instances on HPB2 bridge
#define ID_PAC2          64 /**< \brief Peripheral Access Controller PAC (PAC2) */
#define ID_EVSYS         65 /**< \brief Event System Interface (EVSYS) */
#define ID_SERCOM0       66 /**< \brief Serial Communication Interface SERCOM (SERCOM0) */
#define ID_SERCOM1       67 /**< \brief Serial Communication Interface SERCOM (SERCOM1) */
#define ID_SERCOM2       68 /**< \brief Serial Communication Interface SERCOM (SERCOM2) */
#define ID_SERCOM3       69 /**< \brief Serial Communication Interface SERCOM (SERCOM3) */
#define ID_SERCOM4       70 /**< \brief Serial Communication Interface SERCOM (SERCOM4) */
#define ID_SERCOM5       71 /**< \brief Serial Communication Interface SERCOM (SERCOM5) */
#define ID_TC0           72 /**< \brief Basic Timer Counter TC (TC0) */
#define ID_TC1           73 /**< \brief Basic Timer Counter TC (TC1) */
#define ID_TC2           74 /**< \brief Basic Timer Counter TC (TC2) */
#define ID_TC3           75 /**< \brief Basic Timer Counter TC (TC3) */
#define ID_TC4           76 /**< \brief Basic Timer Counter TC (TC4) */
#define ID_TC5           77 /**< \brief Basic Timer Counter TC (TC5) */
#define ID_TC6           78 /**< \brief Basic Timer Counter TC (TC6) */
#define ID_TC7           79 /**< \brief Basic Timer Counter TC (TC7) */
#define ID_ADC           80 /**< \brief Analog Digital Converter (ADC) */
#define ID_AC            81 /**< \brief Analog Comparators (AC) */
#define ID_DAC           82 /**< \brief Digital Analog Converter (DAC) */

#define ID_PERIPH_COUNT  83 /**< \brief Number of peripheral IDs */
/*@}*/

/* ************************************************************************** */
/**  BASE ADDRESS DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */
/** \defgroup SAMD20G15_base Peripheral Base Address Definitions */
/*@{*/

#if defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)
#define AC                            (0x42004400U) /**< \brief (AC) APB Base Address */
#define ADC                           (0x42004000U) /**< \brief (ADC) APB Base Address */
#define DAC                           (0x42004800U) /**< \brief (DAC) APB Base Address */
#define DSU                           (0x41002000U) /**< \brief (DSU) APB Base Address */
#define EIC                           (0x40001800U) /**< \brief (EIC) APB Base Address */
#define EVSYS                         (0x42000400U) /**< \brief (EVSYS) APB Base Address */
#define GCLK                          (0x40000C00U) /**< \brief (GCLK) APB Base Address */
#define NVMCTRL                       (0x41004000U) /**< \brief (NVMCTRL) APB Base Address */
#define NVMCTRL_CAL                   (0x00800000U) /**< \brief (NVMCTRL) CAL Base Address */
#define NVMCTRL_LOCKBIT               (0x00802000U) /**< \brief (NVMCTRL) LOCKBIT Base Address */
#define NVMCTRL_OTP1                  (0x00806000U) /**< \brief (NVMCTRL) OTP1 Base Address */
#define NVMCTRL_OTP2                  (0x00806008U) /**< \brief (NVMCTRL) OTP2 Base Address */
#define NVMCTRL_OTP4                  (0x00806020U) /**< \brief (NVMCTRL) OTP4 Base Address */
#define NVMCTRL_USER                  (0x00804000U) /**< \brief (NVMCTRL) USER Base Address */
#define PAC0                          (0x40000000U) /**< \brief (PAC0) APB Base Address */
#define PAC1                          (0x41000000U) /**< \brief (PAC1) APB Base Address */
#define PAC2                          (0x42000000U) /**< \brief (PAC2) APB Base Address */
#define PM                            (0x40000400U) /**< \brief (PM) APB Base Address */
#define PORT                          (0x41004400U) /**< \brief (PORT) APB Base Address */
#define PORT_IOBUS                    (0x60000000U) /**< \brief (PORT) IOBUS Base Address */
#define RTC                           (0x40001400U) /**< \brief (RTC) APB Base Address */
#define SERCOM0                       (0x42000800U) /**< \brief (SERCOM0) APB Base Address */
#define SERCOM1                       (0x42000C00U) /**< \brief (SERCOM1) APB Base Address */
#define SERCOM2                       (0x42001000U) /**< \brief (SERCOM2) APB Base Address */
#define SERCOM3                       (0x42001400U) /**< \brief (SERCOM3) APB Base Address */
#define SERCOM4                       (0x42001800U) /**< \brief (SERCOM4) APB Base Address */
#define SERCOM5                       (0x42001C00U) /**< \brief (SERCOM5) APB Base Address */
#define SYSCTRL                       (0x40000800U) /**< \brief (SYSCTRL) APB Base Address */
#define TC0                           (0x42002000U) /**< \brief (TC0) APB Base Address */
#define TC1                           (0x42002400U) /**< \brief (TC1) APB Base Address */
#define TC2                           (0x42002800U) /**< \brief (TC2) APB Base Address */
#define TC3                           (0x42002C00U) /**< \brief (TC3) APB Base Address */
#define TC4                           (0x42003000U) /**< \brief (TC4) APB Base Address */
#define TC5                           (0x42003400U) /**< \brief (TC5) APB Base Address */
#define TC6                           (0x42003800U) /**< \brief (TC6) APB Base Address */
#define TC7                           (0x42003C00U) /**< \brief (TC7) APB Base Address */
#define WDT                           (0x40001000U) /**< \brief (WDT) APB Base Address */
#else
#define AC                ((Ac       *)0x42004400U) /**< \brief (AC) APB Base Address */
#define AC_INST_NUM       1                         /**< \brief (AC) Number of instances */
#define AC_INSTS          { AC }                    /**< \brief (AC) Instances List */

#define ADC               ((Adc      *)0x42004000U) /**< \brief (ADC) APB Base Address */
#define ADC_INST_NUM      1                         /**< \brief (ADC) Number of instances */
#define ADC_INSTS         { ADC }                   /**< \brief (ADC) Instances List */

#define DAC               ((Dac      *)0x42004800U) /**< \brief (DAC) APB Base Address */
#define DAC_INST_NUM      1                         /**< \brief (DAC) Number of instances */
#define DAC_INSTS         { DAC }                   /**< \brief (DAC) Instances List */

#define DSU               ((Dsu      *)0x41002000U) /**< \brief (DSU) APB Base Address */
#define DSU_INST_NUM      1                         /**< \brief (DSU) Number of instances */
#define DSU_INSTS         { DSU }                   /**< \brief (DSU) Instances List */

#define EIC               ((Eic      *)0x40001800U) /**< \brief (EIC) APB Base Address */
#define EIC_INST_NUM      1                         /**< \brief (EIC) Number of instances */
#define EIC_INSTS         { EIC }                   /**< \brief (EIC) Instances List */

#define EVSYS             ((Evsys    *)0x42000400U) /**< \brief (EVSYS) APB Base Address */
#define EVSYS_INST_NUM    1                         /**< \brief (EVSYS) Number of instances */
#define EVSYS_INSTS       { EVSYS }                 /**< \brief (EVSYS) Instances List */

#define GCLK              ((Gclk     *)0x40000C00U) /**< \brief (GCLK) APB Base Address */
#define GCLK_INST_NUM     1                         /**< \brief (GCLK) Number of instances */
#define GCLK_INSTS        { GCLK }                  /**< \brief (GCLK) Instances List */

#define NVMCTRL           ((Nvmctrl  *)0x41004000U) /**< \brief (NVMCTRL) APB Base Address */
#define NVMCTRL_CAL                   (0x00800000U) /**< \brief (NVMCTRL) CAL Base Address */
#define NVMCTRL_LOCKBIT               (0x00802000U) /**< \brief (NVMCTRL) LOCKBIT Base Address */
#define NVMCTRL_OTP1                  (0x00806000U) /**< \brief (NVMCTRL) OTP1 Base Address */
#define NVMCTRL_OTP2                  (0x00806008U) /**< \brief (NVMCTRL) OTP2 Base Address */
#define NVMCTRL_OTP4                  (0x00806020U) /**< \brief (NVMCTRL) OTP4 Base Address */
#define NVMCTRL_USER                  (0x00804000U) /**< \brief (NVMCTRL) USER Base Address */
#define NVMCTRL_INST_NUM  1                         /**< \brief (NVMCTRL) Number of instances */
#define NVMCTRL_INSTS     { NVMCTRL }               /**< \brief (NVMCTRL) Instances List */

#define PAC0              ((Pac      *)0x40000000U) /**< \brief (PAC0) APB Base Address */
#define PAC1              ((Pac      *)0x41000000U) /**< \brief (PAC1) APB Base Address */
#define PAC2              ((Pac      *)0x42000000U) /**< \brief (PAC2) APB Base Address */
#define PAC_INST_NUM      3                         /**< \brief (PAC) Number of instances */
#define PAC_INSTS         { PAC0, PAC1, PAC2 }      /**< \brief (PAC) Instances List */

#define PM                ((Pm       *)0x40000400U) /**< \brief (PM) APB Base Address */
#define PM_INST_NUM       1                         /**< \brief (PM) Number of instances */
#define PM_INSTS          { PM }                    /**< \brief (PM) Instances List */

#define PORT              ((Port     *)0x41004400U) /**< \brief (PORT) APB Base Address */
#define PORT_IOBUS        ((Port     *)0x60000000U) /**< \brief (PORT) IOBUS Base Address */
#define PORT_INST_NUM     1                         /**< \brief (PORT) Number of instances */
#define PORT_INSTS        { PORT }                  /**< \brief (PORT) Instances List */

#define RTC               ((Rtc      *)0x40001400U) /**< \brief (RTC) APB Base Address */
#define RTC_INST_NUM      1                         /**< \brief (RTC) Number of instances */
#define RTC_INSTS         { RTC }                   /**< \brief (RTC) Instances List */

#define SERCOM0           ((Sercom   *)0x42000800U) /**< \brief (SERCOM0) APB Base Address */
#define SERCOM1           ((Sercom   *)0x42000C00U) /**< \brief (SERCOM1) APB Base Address */
#define SERCOM2           ((Sercom   *)0x42001000U) /**< \brief (SERCOM2) APB Base Address */
#define SERCOM3           ((Sercom   *)0x42001400U) /**< \brief (SERCOM3) APB Base Address */
#define SERCOM4           ((Sercom   *)0x42001800U) /**< \brief (SERCOM4) APB Base Address */
#define SERCOM5           ((Sercom   *)0x42001C00U) /**< \brief (SERCOM5) APB Base Address */
#define SERCOM_INST_NUM   6                         /**< \brief (SERCOM) Number of instances */
#define SERCOM_INSTS      { SERCOM0, SERCOM1, SERCOM2, SERCOM3, SERCOM4, SERCOM5 } /**< \brief (SERCOM) Instances List */

#define SYSCTRL           ((Sysctrl  *)0x40000800U) /**< \brief (SYSCTRL) APB Base Address */
#define SYSCTRL_INST_NUM  1                         /**< \brief (SYSCTRL) Number of instances */
#define SYSCTRL_INSTS     { SYSCTRL }               /**< \brief (SYSCTRL) Instances List */

#define TC0               ((Tc       *)0x42002000U) /**< \brief (TC0) APB Base Address */
#define TC1               ((Tc       *)0x42002400U) /**< \brief (TC1) APB Base Address */
#define TC2               ((Tc       *)0x42002800U) /**< \brief (TC2) APB Base Address */
#define TC3               ((Tc       *)0x42002C00U) /**< \brief (TC3) APB Base Address */
#define TC4               ((Tc       *)0x42003000U) /**< \brief (TC4) APB Base Address */
#define TC5               ((Tc       *)0x42003400U) /**< \brief (TC5) APB Base Address */
#define TC6               ((Tc       *)0x42003800U) /**< \brief (TC6) APB Base Address */
#define TC7               ((Tc       *)0x42003C00U) /**< \brief (TC7) APB Base Address */
#define TC_INST_NUM       8                         /**< \brief (TC) Number of instances */
#define TC_INSTS          { TC0, TC1, TC2, TC3, TC4, TC5, TC6, TC7 } /**< \brief (TC) Instances List */

#define WDT               ((Wdt      *)0x40001000U) /**< \brief (WDT) APB Base Address */
#define WDT_INST_NUM      1                         /**< \brief (WDT) Number of instances */
#define WDT_INSTS         { WDT }                   /**< \brief (WDT) Instances List */

#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/*@}*/

/* ************************************************************************** */
/**  PORT DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */
/** \defgroup SAMD20G15_port PORT Definitions */
/*@{*/

#include "pio/pio_samd20g15.h"
/*@}*/

/* ************************************************************************** */
/**  MEMORY MAPPING DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */

#define FLASH_SIZE            0x8000 /* 32 kB */
#define FLASH_PAGE_SIZE       64
#define FLASH_NB_OF_PAGES     512
#define FLASH_USER_PAGE_SIZE  64
#define HRAMC0_SIZE           0x1000 /* 4 kB */
#define FLASH_ADDR            (0x00000000U) /**< FLASH base address */
#define FLASH_USER_PAGE_ADDR  (0x00800000U) /**< FLASH_USER_PAGE base address */
#define HRAMC0_ADDR           (0x20000000U) /**< HRAMC0 base address */

/* ************************************************************************** */
/**  ELECTRICAL DEFINITIONS FOR SAMD20G15 */
/* ************************************************************************** */


#ifdef __cplusplus
}
#endif

/*@}*/

#endif /* SAMD20G15_H */
