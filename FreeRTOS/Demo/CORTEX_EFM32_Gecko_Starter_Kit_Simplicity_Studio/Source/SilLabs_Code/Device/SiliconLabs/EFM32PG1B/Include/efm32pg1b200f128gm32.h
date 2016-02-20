/**************************************************************************//**
 * @file efm32pg1b200f128gm32.h
 * @brief CMSIS Cortex-M Peripheral Access Layer Header File
 *        for EFM32PG1B200F128GM32
 * @version 4.2.1
 ******************************************************************************
 * @section License
 * <b>Copyright 2015 Silicon Laboratories, Inc. http://www.silabs.com</b>
 ******************************************************************************
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software.@n
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.@n
 * 3. This notice may not be removed or altered from any source distribution.
 *
 * DISCLAIMER OF WARRANTY/LIMITATION OF REMEDIES: Silicon Laboratories, Inc.
 * has no obligation to support this Software. Silicon Laboratories, Inc. is
 * providing the Software "AS IS", with no express or implied warranties of any
 * kind, including, but not limited to, any implied warranties of
 * merchantability or fitness for any particular purpose or warranties against
 * infringement of any proprietary rights of a third party.
 *
 * Silicon Laboratories, Inc. will not be liable for any consequential,
 * incidental, or special damages, or any other relief, or for any claim by
 * any third party, arising from your use of this Software.
 *
 *****************************************************************************/

#ifndef SILICON_LABS_EFM32PG1B200F128GM32_H
#define SILICON_LABS_EFM32PG1B200F128GM32_H

#ifdef __cplusplus
extern "C" {
#endif

/**************************************************************************//**
 * @addtogroup Parts
 * @{
 *****************************************************************************/

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32 EFM32PG1B200F128GM32
 * @{
 *****************************************************************************/

/** Interrupt Number Definition */
typedef enum IRQn
{
/******  Cortex-M4 Processor Exceptions Numbers *******************************************/
  NonMaskableInt_IRQn   = -14,              /*!< 2  Cortex-M4 Non Maskable Interrupt      */
  HardFault_IRQn        = -13,              /*!< 3  Cortex-M4 Hard Fault Interrupt        */
  MemoryManagement_IRQn = -12,              /*!< 4  Cortex-M4 Memory Management Interrupt */
  BusFault_IRQn         = -11,              /*!< 5  Cortex-M4 Bus Fault Interrupt         */
  UsageFault_IRQn       = -10,              /*!< 6  Cortex-M4 Usage Fault Interrupt       */
  SVCall_IRQn           = -5,               /*!< 11 Cortex-M4 SV Call Interrupt           */
  DebugMonitor_IRQn     = -4,               /*!< 12 Cortex-M4 Debug Monitor Interrupt     */
  PendSV_IRQn           = -2,               /*!< 14 Cortex-M4 Pend SV Interrupt           */
  SysTick_IRQn          = -1,               /*!< 15 Cortex-M4 System Tick Interrupt       */

/******  EFM32PG1B Peripheral Interrupt Numbers *********************************************/

  EMU_IRQn              = 0,  /*!< 16+0 EFM32 EMU Interrupt */
  WDOG0_IRQn            = 2,  /*!< 16+2 EFM32 WDOG0 Interrupt */
  LDMA_IRQn             = 8,  /*!< 16+8 EFM32 LDMA Interrupt */
  GPIO_EVEN_IRQn        = 9,  /*!< 16+9 EFM32 GPIO_EVEN Interrupt */
  TIMER0_IRQn           = 10, /*!< 16+10 EFM32 TIMER0 Interrupt */
  USART0_RX_IRQn        = 11, /*!< 16+11 EFM32 USART0_RX Interrupt */
  USART0_TX_IRQn        = 12, /*!< 16+12 EFM32 USART0_TX Interrupt */
  ACMP0_IRQn            = 13, /*!< 16+13 EFM32 ACMP0 Interrupt */
  ADC0_IRQn             = 14, /*!< 16+14 EFM32 ADC0 Interrupt */
  IDAC0_IRQn            = 15, /*!< 16+15 EFM32 IDAC0 Interrupt */
  I2C0_IRQn             = 16, /*!< 16+16 EFM32 I2C0 Interrupt */
  GPIO_ODD_IRQn         = 17, /*!< 16+17 EFM32 GPIO_ODD Interrupt */
  TIMER1_IRQn           = 18, /*!< 16+18 EFM32 TIMER1 Interrupt */
  USART1_RX_IRQn        = 19, /*!< 16+19 EFM32 USART1_RX Interrupt */
  USART1_TX_IRQn        = 20, /*!< 16+20 EFM32 USART1_TX Interrupt */
  LEUART0_IRQn          = 21, /*!< 16+21 EFM32 LEUART0 Interrupt */
  PCNT0_IRQn            = 22, /*!< 16+22 EFM32 PCNT0 Interrupt */
  CMU_IRQn              = 23, /*!< 16+23 EFM32 CMU Interrupt */
  MSC_IRQn              = 24, /*!< 16+24 EFM32 MSC Interrupt */
  CRYPTO_IRQn           = 25, /*!< 16+25 EFM32 CRYPTO Interrupt */
  LETIMER0_IRQn         = 26, /*!< 16+26 EFM32 LETIMER0 Interrupt */
  RTCC_IRQn             = 29, /*!< 16+29 EFM32 RTCC Interrupt */
  CRYOTIMER_IRQn        = 31, /*!< 16+31 EFM32 CRYOTIMER Interrupt */
  FPUEH_IRQn            = 33, /*!< 16+33 EFM32 FPUEH Interrupt */
} IRQn_Type;

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_Core EFM32PG1B200F128GM32 Core
 * @{
 * @brief Processor and Core Peripheral Section
 *****************************************************************************/
#define __MPU_PRESENT             1 /**< Presence of MPU  */
#define __FPU_PRESENT             1 /**< Presence of FPU  */
#define __NVIC_PRIO_BITS          3 /**< NVIC interrupt priority bits */
#define __Vendor_SysTickConfig    0 /**< Is 1 if different SysTick counter is used */

/** @} End of group EFM32PG1B200F128GM32_Core */

/**************************************************************************//**
* @defgroup EFM32PG1B200F128GM32_Part EFM32PG1B200F128GM32 Part
* @{
******************************************************************************/

/** Part family */
#define _EFM32_PEARL_FAMILY             1 /**< PEARL Gecko MCU Family  */
#define _EFM_DEVICE                       /**< Silicon Labs EFM-type microcontroller */
#define _SILICON_LABS_32B_PLATFORM_2      /**< Silicon Labs platform name */
#define _SILICON_LABS_32B_PLATFORM      2 /**< Silicon Labs platform name */

/* If part number is not defined as compiler option, define it */
#if !defined(EFM32PG1B200F128GM32)
#define EFM32PG1B200F128GM32    1 /**< PEARL Gecko Part */
#endif

/** Configure part number */
#define PART_NUMBER               "EFM32PG1B200F128GM32" /**< Part Number */

/** Memory Base addresses and limits */
#define FLASH_MEM_BASE            ((uint32_t) 0x00000000UL) /**< FLASH base address  */
#define FLASH_MEM_SIZE            ((uint32_t) 0x10000000UL) /**< FLASH available address space  */
#define FLASH_MEM_END             ((uint32_t) 0x0FFFFFFFUL) /**< FLASH end address  */
#define FLASH_MEM_BITS            ((uint32_t) 0x28UL)       /**< FLASH used bits  */
#define RAM_CODE_MEM_BASE         ((uint32_t) 0x10000000UL) /**< RAM_CODE base address  */
#define RAM_CODE_MEM_SIZE         ((uint32_t) 0x7C00UL)     /**< RAM_CODE available address space  */
#define RAM_CODE_MEM_END          ((uint32_t) 0x10007BFFUL) /**< RAM_CODE end address  */
#define RAM_CODE_MEM_BITS         ((uint32_t) 0x15UL)       /**< RAM_CODE used bits  */
#define PER_BITCLR_MEM_BASE       ((uint32_t) 0x44000000UL) /**< PER_BITCLR base address  */
#define PER_BITCLR_MEM_SIZE       ((uint32_t) 0xE8000UL)    /**< PER_BITCLR available address space  */
#define PER_BITCLR_MEM_END        ((uint32_t) 0x440E7FFFUL) /**< PER_BITCLR end address  */
#define PER_BITCLR_MEM_BITS       ((uint32_t) 0x20UL)       /**< PER_BITCLR used bits  */
#define CRYPTO_BITSET_MEM_BASE    ((uint32_t) 0x460F0000UL) /**< CRYPTO_BITSET base address  */
#define CRYPTO_BITSET_MEM_SIZE    ((uint32_t) 0x400UL)      /**< CRYPTO_BITSET available address space  */
#define CRYPTO_BITSET_MEM_END     ((uint32_t) 0x460F03FFUL) /**< CRYPTO_BITSET end address  */
#define CRYPTO_BITSET_MEM_BITS    ((uint32_t) 0x10UL)       /**< CRYPTO_BITSET used bits  */
#define CRYPTO_MEM_BASE           ((uint32_t) 0x400F0000UL) /**< CRYPTO base address  */
#define CRYPTO_MEM_SIZE           ((uint32_t) 0x400UL)      /**< CRYPTO available address space  */
#define CRYPTO_MEM_END            ((uint32_t) 0x400F03FFUL) /**< CRYPTO end address  */
#define CRYPTO_MEM_BITS           ((uint32_t) 0x10UL)       /**< CRYPTO used bits  */
#define CRYPTO_BITCLR_MEM_BASE    ((uint32_t) 0x440F0000UL) /**< CRYPTO_BITCLR base address  */
#define CRYPTO_BITCLR_MEM_SIZE    ((uint32_t) 0x400UL)      /**< CRYPTO_BITCLR available address space  */
#define CRYPTO_BITCLR_MEM_END     ((uint32_t) 0x440F03FFUL) /**< CRYPTO_BITCLR end address  */
#define CRYPTO_BITCLR_MEM_BITS    ((uint32_t) 0x10UL)       /**< CRYPTO_BITCLR used bits  */
#define PER_BITSET_MEM_BASE       ((uint32_t) 0x46000000UL) /**< PER_BITSET base address  */
#define PER_BITSET_MEM_SIZE       ((uint32_t) 0xE8000UL)    /**< PER_BITSET available address space  */
#define PER_BITSET_MEM_END        ((uint32_t) 0x460E7FFFUL) /**< PER_BITSET end address  */
#define PER_BITSET_MEM_BITS       ((uint32_t) 0x20UL)       /**< PER_BITSET used bits  */
#define PER_MEM_BASE              ((uint32_t) 0x40000000UL) /**< PER base address  */
#define PER_MEM_SIZE              ((uint32_t) 0xE8000UL)    /**< PER available address space  */
#define PER_MEM_END               ((uint32_t) 0x400E7FFFUL) /**< PER end address  */
#define PER_MEM_BITS              ((uint32_t) 0x20UL)       /**< PER used bits  */
#define RAM_MEM_BASE              ((uint32_t) 0x20000000UL) /**< RAM base address  */
#define RAM_MEM_SIZE              ((uint32_t) 0x7C00UL)     /**< RAM available address space  */
#define RAM_MEM_END               ((uint32_t) 0x20007BFFUL) /**< RAM end address  */
#define RAM_MEM_BITS              ((uint32_t) 0x15UL)       /**< RAM used bits  */

/** Bit banding area */
#define BITBAND_PER_BASE          ((uint32_t) 0x42000000UL) /**< Peripheral Address Space bit-band area */
#define BITBAND_RAM_BASE          ((uint32_t) 0x22000000UL) /**< SRAM Address Space bit-band area */

/** Flash and SRAM limits for EFM32PG1B200F128GM32 */
#define FLASH_BASE                (0x00000000UL) /**< Flash Base Address */
#define FLASH_SIZE                (0x00020000UL) /**< Available Flash Memory */
#define FLASH_PAGE_SIZE           2048           /**< Flash Memory page size */
#define SRAM_BASE                 (0x20000000UL) /**< SRAM Base Address */
#define SRAM_SIZE                 (0x00008000UL) /**< Available SRAM Memory */
#define __CM4_REV                 0x001          /**< Cortex-M4 Core revision r0p1 */
#define PRS_CHAN_COUNT            12             /**< Number of PRS channels */
#define DMA_CHAN_COUNT            8              /**< Number of DMA channels */

/** AF channels connect the different on-chip peripherals with the af-mux */
#define AFCHAN_MAX                72
#define AFCHANLOC_MAX             32
/** Analog AF channels */
#define AFACHAN_MAX               61

/* Part number capabilities */

#define TIMER_PRESENT         /**< TIMER is available in this part */
#define TIMER_COUNT         2 /**< 2 TIMERs available  */
#define USART_PRESENT         /**< USART is available in this part */
#define USART_COUNT         2 /**< 2 USARTs available  */
#define LEUART_PRESENT        /**< LEUART is available in this part */
#define LEUART_COUNT        1 /**< 1 LEUARTs available  */
#define LETIMER_PRESENT       /**< LETIMER is available in this part */
#define LETIMER_COUNT       1 /**< 1 LETIMERs available  */
#define PCNT_PRESENT          /**< PCNT is available in this part */
#define PCNT_COUNT          1 /**< 1 PCNTs available  */
#define I2C_PRESENT           /**< I2C is available in this part */
#define I2C_COUNT           1 /**< 1 I2Cs available  */
#define ADC_PRESENT           /**< ADC is available in this part */
#define ADC_COUNT           1 /**< 1 ADCs available  */
#define ACMP_PRESENT          /**< ACMP is available in this part */
#define ACMP_COUNT          2 /**< 2 ACMPs available  */
#define IDAC_PRESENT          /**< IDAC is available in this part */
#define IDAC_COUNT          1 /**< 1 IDACs available  */
#define WDOG_PRESENT          /**< WDOG is available in this part */
#define WDOG_COUNT          1 /**< 1 WDOGs available  */
#define MSC_PRESENT
#define MSC_COUNT           1
#define EMU_PRESENT
#define EMU_COUNT           1
#define RMU_PRESENT
#define RMU_COUNT           1
#define CMU_PRESENT
#define CMU_COUNT           1
#define CRYPTO_PRESENT
#define CRYPTO_COUNT        1
#define GPIO_PRESENT
#define GPIO_COUNT          1
#define PRS_PRESENT
#define PRS_COUNT           1
#define LDMA_PRESENT
#define LDMA_COUNT          1
#define FPUEH_PRESENT
#define FPUEH_COUNT         1
#define GPCRC_PRESENT
#define GPCRC_COUNT         1
#define CRYOTIMER_PRESENT
#define CRYOTIMER_COUNT     1
#define RTCC_PRESENT
#define RTCC_COUNT          1
#define BOOTLOADER_PRESENT
#define BOOTLOADER_COUNT    1

#include "core_cm4.h"         /* Cortex-M4 processor and core peripherals */
#include "system_efm32pg1b.h" /* System Header File */

/** @} End of group EFM32PG1B200F128GM32_Part */

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_Peripheral_TypeDefs EFM32PG1B200F128GM32 Peripheral TypeDefs
 * @{
 * @brief Device Specific Peripheral Register Structures
 *****************************************************************************/

#include "efm32pg1b_msc.h"
#include "efm32pg1b_emu.h"
#include "efm32pg1b_rmu.h"
#include "efm32pg1b_cmu.h"
#include "efm32pg1b_crypto.h"
#include "efm32pg1b_gpio_p.h"
#include "efm32pg1b_gpio.h"
#include "efm32pg1b_prs_ch.h"
#include "efm32pg1b_prs.h"
#include "efm32pg1b_ldma_ch.h"
#include "efm32pg1b_ldma.h"
#include "efm32pg1b_fpueh.h"
#include "efm32pg1b_gpcrc.h"
#include "efm32pg1b_timer_cc.h"
#include "efm32pg1b_timer.h"
#include "efm32pg1b_usart.h"
#include "efm32pg1b_leuart.h"
#include "efm32pg1b_letimer.h"
#include "efm32pg1b_cryotimer.h"
#include "efm32pg1b_pcnt.h"
#include "efm32pg1b_i2c.h"
#include "efm32pg1b_adc.h"
#include "efm32pg1b_acmp.h"
#include "efm32pg1b_idac.h"
#include "efm32pg1b_rtcc_cc.h"
#include "efm32pg1b_rtcc_ret.h"
#include "efm32pg1b_rtcc.h"
#include "efm32pg1b_wdog_pch.h"
#include "efm32pg1b_wdog.h"
#include "efm32pg1b_dma_descriptor.h"
#include "efm32pg1b_devinfo.h"
#include "efm32pg1b_romtable.h"

/** @} End of group EFM32PG1B200F128GM32_Peripheral_TypeDefs  */

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_Peripheral_Base EFM32PG1B200F128GM32 Peripheral Memory Map
 * @{
 *****************************************************************************/

#define MSC_BASE          (0x400E0000UL) /**< MSC base address  */
#define EMU_BASE          (0x400E3000UL) /**< EMU base address  */
#define RMU_BASE          (0x400E5000UL) /**< RMU base address  */
#define CMU_BASE          (0x400E4000UL) /**< CMU base address  */
#define CRYPTO_BASE       (0x400F0000UL) /**< CRYPTO base address  */
#define GPIO_BASE         (0x4000A000UL) /**< GPIO base address  */
#define PRS_BASE          (0x400E6000UL) /**< PRS base address  */
#define LDMA_BASE         (0x400E2000UL) /**< LDMA base address  */
#define FPUEH_BASE        (0x400E1000UL) /**< FPUEH base address  */
#define GPCRC_BASE        (0x4001C000UL) /**< GPCRC base address  */
#define TIMER0_BASE       (0x40018000UL) /**< TIMER0 base address  */
#define TIMER1_BASE       (0x40018400UL) /**< TIMER1 base address  */
#define USART0_BASE       (0x40010000UL) /**< USART0 base address  */
#define USART1_BASE       (0x40010400UL) /**< USART1 base address  */
#define LEUART0_BASE      (0x4004A000UL) /**< LEUART0 base address  */
#define LETIMER0_BASE     (0x40046000UL) /**< LETIMER0 base address  */
#define CRYOTIMER_BASE    (0x4001E000UL) /**< CRYOTIMER base address  */
#define PCNT0_BASE        (0x4004E000UL) /**< PCNT0 base address  */
#define I2C0_BASE         (0x4000C000UL) /**< I2C0 base address  */
#define ADC0_BASE         (0x40002000UL) /**< ADC0 base address  */
#define ACMP0_BASE        (0x40000000UL) /**< ACMP0 base address  */
#define ACMP1_BASE        (0x40000400UL) /**< ACMP1 base address  */
#define IDAC0_BASE        (0x40006000UL) /**< IDAC0 base address  */
#define RTCC_BASE         (0x40042000UL) /**< RTCC base address  */
#define WDOG0_BASE        (0x40052000UL) /**< WDOG0 base address  */
#define DEVINFO_BASE      (0x0FE081B0UL) /**< DEVINFO base address */
#define ROMTABLE_BASE     (0xE00FFFD0UL) /**< ROMTABLE base address */
#define LOCKBITS_BASE     (0x0FE04000UL) /**< Lock-bits page base address */
#define USERDATA_BASE     (0x0FE00000UL) /**< User data page base address */

/** @} End of group EFM32PG1B200F128GM32_Peripheral_Base */

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_Peripheral_Declaration  EFM32PG1B200F128GM32 Peripheral Declarations
 * @{
 *****************************************************************************/

#define MSC          ((MSC_TypeDef *) MSC_BASE)             /**< MSC base pointer */
#define EMU          ((EMU_TypeDef *) EMU_BASE)             /**< EMU base pointer */
#define RMU          ((RMU_TypeDef *) RMU_BASE)             /**< RMU base pointer */
#define CMU          ((CMU_TypeDef *) CMU_BASE)             /**< CMU base pointer */
#define CRYPTO       ((CRYPTO_TypeDef *) CRYPTO_BASE)       /**< CRYPTO base pointer */
#define GPIO         ((GPIO_TypeDef *) GPIO_BASE)           /**< GPIO base pointer */
#define PRS          ((PRS_TypeDef *) PRS_BASE)             /**< PRS base pointer */
#define LDMA         ((LDMA_TypeDef *) LDMA_BASE)           /**< LDMA base pointer */
#define FPUEH        ((FPUEH_TypeDef *) FPUEH_BASE)         /**< FPUEH base pointer */
#define GPCRC        ((GPCRC_TypeDef *) GPCRC_BASE)         /**< GPCRC base pointer */
#define TIMER0       ((TIMER_TypeDef *) TIMER0_BASE)        /**< TIMER0 base pointer */
#define TIMER1       ((TIMER_TypeDef *) TIMER1_BASE)        /**< TIMER1 base pointer */
#define USART0       ((USART_TypeDef *) USART0_BASE)        /**< USART0 base pointer */
#define USART1       ((USART_TypeDef *) USART1_BASE)        /**< USART1 base pointer */
#define LEUART0      ((LEUART_TypeDef *) LEUART0_BASE)      /**< LEUART0 base pointer */
#define LETIMER0     ((LETIMER_TypeDef *) LETIMER0_BASE)    /**< LETIMER0 base pointer */
#define CRYOTIMER    ((CRYOTIMER_TypeDef *) CRYOTIMER_BASE) /**< CRYOTIMER base pointer */
#define PCNT0        ((PCNT_TypeDef *) PCNT0_BASE)          /**< PCNT0 base pointer */
#define I2C0         ((I2C_TypeDef *) I2C0_BASE)            /**< I2C0 base pointer */
#define ADC0         ((ADC_TypeDef *) ADC0_BASE)            /**< ADC0 base pointer */
#define ACMP0        ((ACMP_TypeDef *) ACMP0_BASE)          /**< ACMP0 base pointer */
#define ACMP1        ((ACMP_TypeDef *) ACMP1_BASE)          /**< ACMP1 base pointer */
#define IDAC0        ((IDAC_TypeDef *) IDAC0_BASE)          /**< IDAC0 base pointer */
#define RTCC         ((RTCC_TypeDef *) RTCC_BASE)           /**< RTCC base pointer */
#define WDOG0        ((WDOG_TypeDef *) WDOG0_BASE)          /**< WDOG0 base pointer */
#define DEVINFO      ((DEVINFO_TypeDef *) DEVINFO_BASE)     /**< DEVINFO base pointer */
#define ROMTABLE     ((ROMTABLE_TypeDef *) ROMTABLE_BASE)   /**< ROMTABLE base pointer */

/** @} End of group EFM32PG1B200F128GM32_Peripheral_Declaration */

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_Peripheral_Offsets  EFM32PG1B200F128GM32 Peripheral Offsets
 * @{
 *****************************************************************************/

#define TIMER_OFFSET      0x400 /**< Offset in bytes between TIMER instances */
#define USART_OFFSET      0x400 /**< Offset in bytes between USART instances */
#define LEUART_OFFSET     0x400 /**< Offset in bytes between LEUART instances */
#define LETIMER_OFFSET    0x400 /**< Offset in bytes between LETIMER instances */
#define PCNT_OFFSET       0x400 /**< Offset in bytes between PCNT instances */
#define I2C_OFFSET        0x400 /**< Offset in bytes between I2C instances */
#define ADC_OFFSET        0x400 /**< Offset in bytes between ADC instances */
#define ACMP_OFFSET       0x400 /**< Offset in bytes between ACMP instances */
#define IDAC_OFFSET       0x400 /**< Offset in bytes between IDAC instances */
#define WDOG_OFFSET       0x400 /**< Offset in bytes between WDOG instances */

/** @} End of group EFM32PG1B200F128GM32_Peripheral_Offsets */


/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_BitFields EFM32PG1B200F128GM32 Bit Fields
 * @{
 *****************************************************************************/

#include "efm32pg1b_prs_signals.h"
#include "efm32pg1b_dmareq.h"

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_UNLOCK EFM32PG1B200F128GM32 Unlock Codes
 * @{
 *****************************************************************************/
#define MSC_UNLOCK_CODE      0x1B71 /**< MSC unlock code */
#define EMU_UNLOCK_CODE      0xADE8 /**< EMU unlock code */
#define RMU_UNLOCK_CODE      0xE084 /**< RMU unlock code */
#define CMU_UNLOCK_CODE      0x580E /**< CMU unlock code */
#define GPIO_UNLOCK_CODE     0xA534 /**< GPIO unlock code */
#define TIMER_UNLOCK_CODE    0xCE80 /**< TIMER unlock code */
#define RTCC_UNLOCK_CODE     0xAEE8 /**< RTCC unlock code */

/** @} End of group EFM32PG1B200F128GM32_UNLOCK */

/** @} End of group EFM32PG1B200F128GM32_BitFields */

/**************************************************************************//**
 * @defgroup EFM32PG1B200F128GM32_Alternate_Function EFM32PG1B200F128GM32 Alternate Function
 * @{
 *****************************************************************************/

#include "efm32pg1b_af_ports.h"
#include "efm32pg1b_af_pins.h"

/** @} End of group EFM32PG1B200F128GM32_Alternate_Function */

/**************************************************************************//**
 *  @brief Set the value of a bit field within a register.
 *
 *  @param REG
 *       The register to update
 *  @param MASK
 *       The mask for the bit field to update
 *  @param VALUE
 *       The value to write to the bit field
 *  @param OFFSET
 *       The number of bits that the field is offset within the register.
 *       0 (zero) means LSB.
 *****************************************************************************/
#define SET_BIT_FIELD(REG, MASK, VALUE, OFFSET) \
  REG = ((REG) &~(MASK)) | (((VALUE) << (OFFSET)) & (MASK));

/** @} End of group EFM32PG1B200F128GM32 */

/** @} End of group Parts */

#ifdef __cplusplus
}
#endif
#endif /* SILICON_LABS_EFM32PG1B200F128GM32_H */
