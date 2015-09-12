/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/


/** @file mec14xx.h
 *MEC14xx master header
 */
/** @defgroup MEC14xx
 */

/**
 * MEC14xx initial version
 */


#ifndef MEC14XX_DEFS_H 
#define MEC14XX_DEFS_H 

#ifdef __cplusplus
 extern "C" {
#endif 

/** @addtogroup MEC14xx_Definitions 
  This file defines all structures and symbols for MEC14xx:
    - registers and bitfields
    - peripheral base address
    - peripheral ID
    - Peripheral definitions
  @{
*/

/** MEC14xx Hardware memory maps.
 * @note
 * Common
 *
 * MEC1404
 * 96KB CODE SRAM
 * 32KB DATA SRAM
 * 
 *              Physical                    Virtual                     Length
 * CODE SRAM  0x1FD0_0000 - 0x1FD1_7FFF     0xBFD0_0000 - 0xBFD1_7FFF   96KB (0x18000)
 * DATA SRAM  0x1FD1_8000 - 0x1FD1_FFFF     0xBFD1_8000 - 0xBFD1_FFFF   32KB
 * CPP Regs   0x1FFF_C000 - 0x1FFF_FFFF     0xBFFF_C000 - 0xBFFF_FFFF   16KB
 *
 * MEC1418
 * 160KB CODE SRAM
 * 32KB  DATA SRAM
 *
 *              Physical                    Virtual                     Length
 * CODE SRAM  0x1FCF_0000 - 0x1FD1_7FFF     0xBFCF_0000 - 0xBFD1_7FFF   128KB (0x20000)
 * DATA SRAM  0x1FD1_8000 - 0x1FD1_FFFF     0xBFD1_8000 - 0xBFD1_FFFF   32KB
 * CPP Regs   0x1FFF_C000 - 0x1FFF_FFFF     0xBFFF_C000 - 0xBFFF_FFFF   16KB
 *
 */
 
#define MEC14XX_TRUE    (1ul)
#define MEC14XX_FALSE   (0ul)

#define MEC14XX_ON      (1ul)
#define MEC14XX_OFF     (0ul)

#define MEC14XX_ENABLE  (1ul)
#define MEC14XX_DISABLE (0ul)

#define MEC14XX_ROM_PBASE       (0x1FC00000ul)
#define MEC14XX_ROM_PBLEN       (1024ul * 64ul)
#define MEC14XX_ROM_PLIMIT      ((MEC14XX_ROM_PBASE) + (MEC14XX_ROM_PBLEN))

#define MEC14XX_ROM_VBASE       (0xBFC00000ul)
#define MEC14XX_ROM_VBLEN       (1024ul * 64ul)
#define MEC14XX_ROM_VLIMIT      ((MEC14XX_ROM_VBASE) + (MEC14XX_ROM_VBLEN))


/* MEC1404 */
#define MEC1404_ICODE_PSRAM_BASE    (0x1FD00000ul)
#define MEC1404_ICODE_PSRAM_BLEN    (1024ul * 96ul)
#define MEC1404_ICODE_PSRAM_LIMIT   ((MEC1404_ICODE_PSRAM_SM_BASE)+(MEC1404_ICODE_PSRAM_SM_BLEN))
// Virtual
#define MEC1404_ICODE_VSRAM_BASE    ((MEC1404_ICODE_PSRAM_BASE) | (0xA0000000ul))
#define MEC1404_ICODE_VSRAM_BLEN    (MEC1404_ICODE_PSRAM_BLEN)
#define MEC1404_ICODE_VSRAM_LIMIT   ((MEC1404_ICODE_PSRAM_LIMIT) | (0xA0000000ul))


/* MEC1418 */
#define MEC1418_ICODE_PSRAM_BASE    (0x1FCF0000ul)
#define MEC1418_ICODE_PSRAM_BLEN    (1024ul * 160ul)
#define MEC1418_ICODE_PSRAM_LIMIT   ((MEC1418_ICODE_PSRAM_SM_BASE)+(MEC1418_ICODE_PSRAM_SM_BLEN))
// Virtual
#define MEC1418_ICODE_VSRAM_BASE    ((MEC1418_ICODE_PSRAM_BASE) | (0xA0000000ul))
#define MEC1418_ICODE_VSRAM_BLEN    (MEC1418_ICODE_PSRAM_BLEN)
#define MEC1418_ICODE_VSRAM_LIMIT   ((MEC1418_ICODE_PSRAM_LIMIT) | (0xA0000000ul))


/* 32KB Data SRAM */
#define MEC14XX_DCODE_PSRAM_BASE         (0x1FD18000ul)
#define MEC14XX_DCODE_PSRAM_BLEN         (1024ul * 32ul)
#define MEC14XX_DCODE_PSRAM_LIMIT        ((MEC14XX_DCODE_PSRAM_BASE)+(MEC14XX_DCODE_PSRAM_BLEN))
#define MEC14XX_DCODE_PSRAM_MASK         ((MEC14XX_DCODE_PSRAM_BLEN) - 1ul)

#define MEC14XX_DCODE_VSRAM_BASE         (0xBFD18000ul)
#define MEC14XX_DCODE_VSRAM_BLEN         (1024ul * 32ul)
#define MEC14XX_DCODE_VSRAM_LIMIT        ((MEC14XX_DCODE_VSRAM_BASE)+(MEC14XX_DCODE_VSRAM_BLEN))
#define MEC14XX_DCODE_VSRAM_MASK         ((MEC14XX_DCODE_VSRAM_BLEN) - 1ul)

/* Closely Coupled Peripheral Region */
#define MEC14XX_CCP_PHYS_BASE           (0x1FFFC000ul)
#define MEC14XX_CCP_BLEN                (16ul * 1024ul)
#define MEC14XX_CCP_PHYS_LIMIT          ((MEC14XX_CCP_PHYS_BASE) + (MEC14XX_CCP_BLEN))
#define MEC14XX_CCP_VIRT_BASE           (0xBFFFC000ul)
#define MEC14XX_CCP_VIRT_LIMIT          ((MEC14XX_CCP_VIRT_BASE) + (MEC14XX_CCP_BLEN))


/******************************************************************************/
/*                Processor and Core Peripherals                              */
/******************************************************************************/
/** @addtogroup MEC14xx_DEFS Device Definitions
  Configuration of the MIPS microAptiv M14K Processor and Core Peripherals
  @{
*/


// Memory Mapped Control Register on AHB (system bus)
#define MMCR_BASE     (0xA0000000UL)
#define MMCR_MASK     (0x000FFFFFUL)

/*
 * ==========================================================================
 * ---------- Interrupt Number Definition -----------------------------------
 * ==========================================================================
 */

#define MEC14xx_GIRQ08_ID           (0)
#define MEC14xx_GIRQ09_ID           (1)
#define MEC14xx_GIRQ10_ID           (2)
#define MEC14xx_GIRQ11_ID           (3)
#define MEC14xx_GIRQ12_ID           (4)
#define MEC14xx_GIRQ13_ID           (5)
#define MEC14xx_GIRQ14_ID           (6)
#define MEC14xx_GIRQ15_ID           (7)
#define MEC14xx_GIRQ16_ID           (8)
#define MEC14xx_GIRQ17_ID           (9)
#define MEC14xx_GIRQ18_ID           (10)
#define MEC14xx_GIRQ19_ID           (11)
#define MEC14xx_GIRQ20_ID           (12)
#define MEC14xx_GIRQ21_ID           (13)
#define MEC14xx_GIRQ22_ID           (14)
#define MEC14xx_GIRQ23_ID           (15)
#define MEC14xx_GIRQ24_ID           (16)
#define MEC14xx_GIRQ25_ID           (17)
#define MEC14xx_GIRQ26_ID           (18)
#define MEC14xx_NUM_JTVIC_INTS      (18+1)
// 4-bits per GIRQ source bit (only lower 2-bits used)
// 4 * 32 * 19 = 2432 bits -> 76 32-bit registers 
#define MEC14xx_NUM_GIRQ_PRI_REGS   ((MEC14xx_NUM_JTVIC_INTS) << 2)


/*
 * ==========================================================================
 * ----------- Processor and Core Peripheral Section ------------------------
 * ==========================================================================
 */


/*@}*/ /* end of group MEC14xx_DEFS */


#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>


/******************************************************************************/
/*                Device Specific Peripheral registers structures             */
/******************************************************************************/
/** @addtogroup MEC14xx_Peripherals MEC14xx Peripherals
  MEC14xx Device Specific Peripheral registers structures
  @{
*/

/* Register Union */
typedef union
{
    volatile uint32_t w;
    volatile uint16_t h[2];
    volatile uint8_t  b[4];
} REG32_U;

typedef union
{
    uint32_t w;
    uint16_t hw[2];
    uint8_t  b[4];
} DATA32_U;

typedef struct buff8_s 
{
    uint32_t len;
    uint8_t *pd;
} BUFF8_T;

typedef struct buff16_s 
{
    uint32_t len;
    uint16_t *pd;
} BUFF16_T;

typedef struct buff32_s 
{
    uint32_t len;
    uint32_t *pd;
} BUFF32_T;


#ifndef __IO
#define __IO volatile
#ifdef __cplusplus
  #define   __I     volatile             
#else
  #define   __I     volatile const      
#endif
#define     __O     volatile      
#endif


/*---------!!!! M14K Closely Coupled Peripherals !!!!-----------------------*/

/*------------- Jump Table Interrupt Controller (JTVIC)------------------*/
/** @addtogroup JTVIC  MEC14xx External Interrupt Controller (JTVIC)
  @{
*/

typedef struct
{
    __IO uint32_t SOURCE;   /*!< Offset: 0x0000 Source RW1C */ 
    __IO uint32_t EN_SET;   /*!< Offset: 0x0004 Enable Set RW */ 
    __IO uint32_t EN_CLR;   /*!< Offset: 0x0008 Enable Clear RW */ 
    __IO uint32_t RESULT;   /*!< Offset: 0x000C Result RO */
} GIRQ_TypeDef;

typedef struct
{
    __IO uint32_t REG32[MEC14xx_NUM_GIRQ_PRI_REGS];
    uint8_t PAD[0x200ul - ((MEC14xx_NUM_GIRQ_PRI_REGS)<<2)];
} GIRQ_PRIORITY_TypeDef;


/*
 * JTVIC GIRQ Sub-block size = 512 bytes (0x200)
 * Pad structure to 512 bytes
*/
typedef struct
{
    GIRQ_TypeDef  REGS[MEC14xx_NUM_JTVIC_INTS]; 
    uint8_t PAD[0x200ul-((MEC14xx_NUM_JTVIC_INTS)<<4)]; 
} JTVIC_GIRQ_REGS_TypeDef; // at CPP_BASE

/*
 * JTVIC Aggregator Control Sub-block size = 256 bytes (0x100)
 * Pad structure to 256 bytes
*/
typedef struct
{
    __IO uint32_t REG32[MEC14xx_NUM_JTVIC_INTS];
    uint8_t PAD[0x100ul-((MEC14xx_NUM_JTVIC_INTS)<<2)];  
} JTVIC_AGG_CTRL_TypeDef; // at CCP_BASE+0x200

/*
 * JTVIC Priority Sub-block size = 512 bytes (0x200)
 * Pad structure to 512 bytes
*/
typedef struct
{
    __IO uint32_t REG32[(MEC14xx_NUM_JTVIC_INTS)<<4];
    uint8_t PAD[0x200ul-((MEC14xx_NUM_JTVIC_INTS)<<4)]; 
} JTVIC_PRIORITY_TypeDef; // at CPP_Base+0x300


typedef struct
{
    GIRQ_TypeDef GIRQ[MEC14xx_NUM_JTVIC_INTS];              // CPP_BASE
    uint8_t PADA[0x200ul-((MEC14xx_NUM_JTVIC_INTS)<<4)];    // 16 bytes/girq
    __IO uint32_t AGG_CTRL[MEC14xx_NUM_JTVIC_INTS];         // CPP_BASE + 0x200
    uint8_t PADB[0x100ul-((MEC14xx_NUM_JTVIC_INTS)<<2)];    // 4 bytes/girq
    GIRQ_PRIORITY_TypeDef GIRQPRI[MEC14xx_NUM_GIRQ_PRI_REGS];  // CPP_BASE + 0x300
    uint8_t PADC[0x200ul-((MEC14xx_NUM_JTVIC_INTS)<<4)];    // 16 bytes/girq
    __IO uint32_t CONTROL;                                  // CPP_BASE + 0x500
    __IO uint32_t PENDING;                                  // CPP_BASE + 0x504
    __IO uint32_t GROUP_ENABLE_SET;                         // CPP_BASE + 0x508
    __IO uint32_t GROUP_ENABLE_CLR;                         // CPP_BASE + 0x50c
    __IO uint32_t GIRQ_ACTIVE;                              // CPP_BASE + 0x510
} JTVIC_TypeDef;

#define JTVIC_BASE      (MEC14XX_CCP_VIRT_BASE)
#define JTVIC           ((JTVIC_TypeDef *) JTVIC_BASE)
#define JTVIC_GIRQ      ((JTVIC_GIRQ_REGS_TypeDef *)(JTVIC_BASE))
#define JTVIC_ACTRL     ((JTVIC_AGG_CTRL_TypeDef *)(JTVIC_BASE + 0x200ul))
#define JTVIC_PRI       ((GIRQ_PRIORITY_TypeDef *)(JTVIC_BASE + 0x300ul))
#define JTVIC_CTRL      ((REG32_U *)(JTVIC_BASE + 0x500ul))
#define JTVIC_PEND      ((REG32_U *)(JTVIC_BASE + 0x504ul))
#define JTVIC_GROUP_EN_SET ((REG32_U *)(JTVIC_BASE + 0x508ul))
#define JTVIC_GROUP_EN_CLR ((REG32_U *)(JTVIC_BASE + 0x50Cul))
#define JTVIC_GIRQ_ACTIVE  ((REG32_U *)(JTVIC_BASE + 0x510ul))

/*@}*/ /* end of group JTVIC */


/*---------!!!! EC AHB Bus Segment !!!!---------------------------*/

/*------------- Watch Dog Timer (WDT) --------------------------*/
/** @addtogroup WDT  MEC14xx Watch Dog Timer (WDT)
  @{
*/
typedef struct
{
    __IO uint16_t LOAD;
         uint16_t RESERVEDA[1];
    __IO uint8_t  CONTROL;
         uint8_t  RESERVEDB[3];
    __O  uint8_t  KICK;
         uint8_t  RESERVEDC[3];
    __I  uint16_t COUNT;
         uint16_t RESERVEDD[1];
} WDT_TypeDef;
/*@}*/ /* end of group WDT */

/*------------- Basic Timer (TMR) -----------------------------*/
/** @addtogroup BTMR  MEC14xx Basic Timer (TMR)
  @{
*/
#define MEC14xx_NUM_BASIC_TIMERS    (4)
typedef struct
{
  __IO uint32_t COUNT;                      /*!< Offset: 0x0000   Timer Count Register            */ 
  __IO uint32_t PRELOAD;                    /*!< Offset: 0x0004   Timer Preload Register          */
  __IO uint8_t  STATUS;                     /*!< Offset: 0x0008   Timer Status Register           */
       uint8_t  RESERVEDC[3];
  __IO uint8_t  INTEN;                      /*!< Offset: 0x000C   Timer Interrupt Enable Register */
       uint8_t  RESERVEDD[3];
  __IO uint32_t CONTROL;                    /*!< Offset: 0x0010   Timer Control Register          */
       uint32_t RESERVEDE[3];
} BTMR_TypeDef;

typedef struct
{
    BTMR_TypeDef BTimer[MEC14xx_NUM_BASIC_TIMERS];
} BTMRS_TypeDef;

/*@}*/ /* end of group BTMR */

/*------------- RTOS Timer (RTMR) -----------------------------*/
/** @addtogroup RTOS Timer (RTMR)
  @{
*/
typedef struct
{
    __IO    uint32_t COUNT;     /*!< Offset: 0x0000  Counter RO */
    __IO    uint32_t PRELOAD;   /*!< Offset: 0x0004  Pre-Load */
    __IO    uint8_t  CONTROL;   /*!< Offset: 0x0008  Control */
            uint8_t  RESERVEDA[3];
} RTMR_TypeDef;
/*@}*/ /* end of group RTMR */

/*------------- Trace FIFO Data Port (TFDP) -----------------------------*/
/** @addtogroup TFDP Trace FIFO Data Port (TFDP)
  @{
*/
typedef struct
{
   __IO uint8_t  DATA;
        uint8_t  RESERVEDA[3];
   __IO uint8_t  CONTROL;
        uint8_t  RESERVEDB[3];
} TFDP_TypeDef;
/*@}*/ /* end of group MEC14xx_TFDP */

/*------------- Breathing/Blinking LED (BBLED) -----------------------------*/
/** @addtogroup BBLED Breathing-Blinking LED (BBLED)
  @{
*/

typedef struct
{
  __IO uint32_t CONFIG;
  __IO uint32_t LIMIT;
  __IO uint32_t DELAY;
  __IO uint32_t STEP;
  __IO uint32_t INTERVAL;
} BBLED_TypeDef;
/*@}*/ /* end of group BBLED */

/*------------- VBAT Registers (VBATREGS) ---------------------------*/
/** @addtogroup PCR  MEC14xx VBAT Register  Block (VBATREGS)
  @{
*/
typedef struct
{
    __IO uint32_t POWER_FAIL_RESET;		/*!< Offset: 0x0000  Power-Fail and Reset Status  */
    __IO uint32_t ATE_REG_CTRL;			/*!< Offset: 0x0004  ATE Regulator Control Register */
    __IO uint32_t CLOCK_ENABLE;         /*!< Offset: 0x0008  Clock Enable  */
         uint32_t RESERVEDA[1];
    __IO uint32_t ATE_TEST;				/*!< Offset: 0x0010  ATE Test Register */
    __IO uint32_t OSC_32K_TRIM;			/*!< Offset: 0x0014  32KHz OSC trim */
    __IO uint32_t VTR_ALT_CTRL;			/*!< Offset: 0x0018  Alternate Function VTR Control */
    __IO uint32_t OSC_TRIM_CTRL;		/*!< Offset: 0x001C  32KHz Trim Control */
} VBATREGS_TypeDef;

/*@}*/ /* end of group VBATREGS */

/*------------- EC Subsystem (ECS) -----------------------------*/
/** @addtogroup ECS EC Subsystem (ECS)
  @{
*/
typedef struct
{
    __IO    uint32_t JTAG_ENABLE;           /*!< JTAG Enable */
} ECS_TypeDef;
/*@}*/ /* end of group MEC14xx_ECS */


/*----------!!!! Chip AHB Bus Segment !!!!-----------------------------*/

/*------------- Chip Power Control Reset (PCR) ------------------------*/
/** @addtogroup PCR  MEC14xx Power Control Reset Block (PCR)
  @{
*/
typedef struct
{
  __IO uint32_t CHIP_SLEEP_EN;                  /*!< Offset: 0x0000  Chip sleep enable */               
  __IO uint32_t CHIP_CLOCK_REQ_STS;             /*!< Offset: 0x0004  Chip Clocks required status */
  __IO uint32_t EC_SLEEP_EN;                    /*!< Offset: 0x0008  EC Sleep enable  */
  __IO uint32_t EC_CLOCK_REQ_STS;               /*!< Offset: 0x000C  EC Clocks required status */
  __IO uint32_t HOST_SLEEP_EN;                  /*!< Offset: 0x0010  Host Sleep enable */
  __IO uint32_t HOST_CLOCK_REQ_STS;             /*!< Offset: 0x0014  Host clocks required status */
  __IO uint32_t SYSTEM_SLEEP_CNTRL;             /*!< Offset: 0x0018  System Sleep control */
       uint32_t RESERVEDA[1];
  __IO uint32_t PROC_CLOCK_CNTRL;               /*!< Offset: 0x0020  Processor clock control */
  __IO uint32_t EC_SLEEP_EN2;                   /*!< Offset: 0x0024  EC Sleep Enable 2 */
  __IO uint32_t EC_CLOCK_REQ_STS2;              /*!< Offset: 0x0028  EC Clock Required 2 */
  __IO uint32_t SLOW_CLOCK_CNTRL;               /*!< Offset: 0x002C  Slow clock control */
  __IO uint32_t OSC_ID;                         /*!< Offset: 0x0030  Chip Oscillator ID, Read-Only */
  __IO uint32_t CHIP_PWR_RST_STS;               /*!< Offset: 0x0034  Chip Sub-system Power Reset Status */
  __IO uint32_t CHIP_RESET_EN;                  /*!< Offset: 0x0038  Chip block resets */
  __IO uint32_t HOST_RESET_EN;                  /*!< Offset: 0x003C  Host block resets */
  __IO uint32_t EC_RESET_EN;                    /*!< Offset: 0x0040  EC Block resets */
  __IO uint32_t EC_RESET_EN2;                   /*!< Offset: 0x0044  EC Block resets 2 */
  __IO uint32_t PWR_RST_CTRL;                   /*!< Offset: 0x0048  Power Reset Control */
} PCR_TypeDef;
/*@}*/ /* end of group PCR */


/*------------- General Purpose IO Pin Config (GPIO_CFG) -----------------------------*/
/** @addtogroup GPIO  MEC14xx GPIO Pin Config (GPIO_CFG)
  @{
*/
typedef struct
{
  __IO uint16_t CONFIG;
  __IO uint8_t  ALT_OUT;
  __I  uint8_t  PAD_IN;
} GPIO_CFG_TypeDef;
/*@}*/ /* end of group GPIO_CFG */

/*------------- General Purpose IO (GPIO) -----------------------------*/
/** @addtogroup GPIO  MEC14xx GPIO (GPIO)
  @{
*/
#define MEC14xx_NUM_GPIO_BANKS  (4)
#define MEC14xx_NUM_GPIO_PINS   ((MEC14xx_NUM_GPIO_BANKS) * 32)

typedef struct                               
{
    GPIO_CFG_TypeDef PIN_CFG[MEC14xx_NUM_GPIO_PINS];
} GPIO_TypeDef;

typedef union
{
    __IO uint32_t w;
    GPIO_CFG_TypeDef s;
} GPIO_CTRL_REG_TypeDef;

typedef struct
{
    GPIO_CTRL_REG_TypeDef REG[MEC14xx_NUM_GPIO_PINS];
} GPIO_CTRL_TypeDef;

typedef struct
{
    __IO uint32_t PINS[MEC14xx_NUM_GPIO_BANKS];
} GPIO_PAROUT_TypeDef; /*!< Offset: 0x0280 GPIO Pins Parallel Output */

#define GPIO_PAR_000_037_IDX    (0u)
#define GPIO_PAR_040_077_IDX    (1u)
#define GPIO_PAR_100_137_IDX    (2u)
#define GPIO_PAR_140_177_IDX    (3u)

#define GPIO_LOCK_140_177_IDX   (0u)
#define GPIO_LOCK_100_137_IDX   (1u)
#define GPIO_LOCK_040_077_IDX   (2u)
#define GPIO_LOCK_000_037_IDX   (3u)

#define GPIO_LOCK_140_177_OFS   ((GPIO_LOCK_140_177_IDX) << 2)
#define GPIO_LOCK_100_137_OFS   ((GPIO_LOCK_100_137_IDX) << 2)
#define GPIO_LOCK_040_077_OFS   ((GPIO_LOCK_040_077_IDX) << 2)
#define GPIO_LOCK_000_037_OFS   ((GPIO_LOCK_000_037_IDX) << 2)


typedef struct
{
    __IO uint32_t PINS[MEC14xx_NUM_GPIO_BANKS];
} GPIO_PARIN_TypeDef; /*!< Offset: 0x0300 GPIO Pins Parallel Input */

typedef struct
{
    __IO uint32_t PINS[MEC14xx_NUM_GPIO_BANKS];
} GPIO_LOCK_Typedef; /*!< Offset: 0x03EC GPIO Pins Lock */

typedef struct
{
    __IO uint32_t PINS[MEC14xx_NUM_GPIO_PINS];
} GPIO_DRVSTR_Typedef; /*!< Offset: 0x0500 GPIO Pins Lock */
/*@}*/ /* end of group GPIO */

/*@}*/ /* end of group MEC14xx_Peripherals */


/******************************************************************************/
/*                         Peripheral memory map                              */
/******************************************************************************/

/** @addtogroup MEC14xx_MemoryMap MEC14xx Memory Mapping
  @{
*/

/* Peripheral and SRAM base address */

#define MEC14xx_PERIPH_BASE      (0xA0000000UL)   /*!< (Peripheral) Base Address */
#define MEC14xx_SPB_PERIPH_BASE  (0xA0080000UL)   /*!< (Chip Subsystem SPB Peripheral) Base Address */
#define MEC14xx_HOST_PERIPH_BASE (0xA00F0000UL)   /*!< (Host Peripheral) Base Address */

/* Peripheral memory map */
#define WDT_BASE            ((MEC14xx_PERIPH_BASE) + 0x0400) /*!< (WDT ) Base */
#define BTMRS_BASE          ((MEC14xx_PERIPH_BASE) + 0x0C00) /*!< (Basic Timers ) Base Address */
#define BTMR0_BASE          ((MEC14xx_PERIPH_BASE) + 0x0C00) /*!< (Basic 16-bit timer 0 ) Base Address */
#define BTMR1_BASE          ((MEC14xx_PERIPH_BASE) + 0x0C20) /*!< (Basic 16-bit timer 1 ) Base Address */
#define BTMR2_BASE          ((MEC14xx_PERIPH_BASE) + 0x0C40) /*!< (Basic 16-bit timer 2 ) Base Address */
#define BTMR3_BASE          ((MEC14xx_PERIPH_BASE) + 0x0C60) /*!< (Basic 16-bit timer 3 ) Base Address */
#define RTOS_TIMER_BASE     ((MEC14xx_PERIPH_BASE) + 0x7400) /*!< (RTOS Timer) Base Address */
#define TFDP_BASE           ((MEC14xx_PERIPH_BASE) + 0x8C00) /*!< (TFDP ) Base Address */
#define VBAT_REGS_BASE      ((MEC14xx_PERIPH_BASE) + 0xA400) /*!< (PCR VBAT Regs ) Base Address */
#define VBAT_MEM_BASE       ((MEC14xx_PERIPH_BASE) + 0xA800) /*!< (VBAT MEM ) Base Address */
#define LED0_BASE           ((MEC14xx_PERIPH_BASE) + 0xB800) /*!< (LED0 ) Base Address */
#define LED1_BASE           ((MEC14xx_PERIPH_BASE) + 0xB900) /*!< (LED1 ) Base Address */
#define LED2_BASE           ((MEC14xx_PERIPH_BASE) + 0xBA00) /*!< (LED2 ) Base Address */
#define ECS_BASE            ((MEC14xx_PERIPH_BASE) + 0xFC00) /*!< (ECS ) Base Address */

/* SPB Peripheral memory map */
#define PCR_BASE           ((MEC14xx_SPB_PERIPH_BASE) + 0x0100) /*!< (PCR ) Base Address */
#define GPIO_BASE          ((MEC14xx_SPB_PERIPH_BASE) + 0x1000) /*!< (GPIO ) Base Address */
#define GPIO_CTRL_BASE     ((MEC14xx_SPB_PERIPH_BASE) + 0x1000)
#define GPIO_POUT_BASE     ((MEC14xx_SPB_PERIPH_BASE) + 0x1280)
#define GPIO_PIN_BASE      ((MEC14xx_SPB_PERIPH_BASE) + 0x1300)
#define GPIO_LOCK_BASE     ((MEC14xx_SPB_PERIPH_BASE) + 0x13F0) /*!< (GPIO Lock Regis) Base Address */
#define GPIO_PCTRL2_BASE   ((MEC14xx_SPB_PERIPH_BASE) + 0x1500) /*!< (GPIO Pin Ctrl 2) Base Address */

/*@}*/ /* end of group MEC14xx_MemoryMap */


/******************************************************************************/
/*                         Peripheral declaration                             */
/******************************************************************************/

/** @addtogroup MEC14xx_PeripheralDecl MEC14xx Peripheral Declaration
  @{
*/

/* EC Bus Segment Devices */
#define WDT         ((WDT_TypeDef *)(WDT_BASE))                 
#define RTOS_TIMER  ((RTMR_TypeDef *)(RTOS_TIMER_BASE))         
#define TFDP        ((TFDP_TypeDef *)(TFDP_BASE))               
#define VBAT_REGS   ((VBATREGS_TypeDef *)(VBAT_REGS_BASE))      
#define BBLED0      ((BBLED_TypeDef *)(LED0_BASE))              
#define BBLED1      ((BBLED_TypeDef *)(LED1_BASE))              
#define BBLED2      ((BBLED_TypeDef *)(LED2_BASE))              
#define ECS         ((ECS_TypeDef *)(ECS_BASE))
#define ECS_REG     ((ECS_TypeDef *)(ECS_BASE + 0x20))

/* Chip Bus Segment Devices */
#define PCR         ((PCR_TypeDef *)(PCR_BASE))                 
#define GPIO        ((GPIO_TypeDef *)(GPIO_BASE))               
#define GPIO_CTRL   ((GPIO_CTRL_TypeDef *) (GPIO_BASE))
#define GPIO_PAROUT ((GPIO_PAROUT_TypeDef *)(GPIO_POUT_BASE))
#define GPIO_PARIN  ((GPIO_PARIN_TypeDef *)(GPIO_PIN_BASE))
#define GPIO_LOCK   ((GPIO_LOCK_Typedef *)(GPIO_LOCK_BASE))
#define GPIO_DRVSTR ((GPIO_DRVSTR_Typedef *)(GPIO_PCTRL2_BASE))


/*@}*/ /* end of group MEC14xx_PeripheralDecl */

/*@}*/ /* end of group MEC14xx_Definitions */

/*
 * Convert MEC14xx MIPS M14K virtual address to physical
 * Physical address is bits [31:29] = 000b
 *                          [28:0]  = virtual [28:0]
 */
#define sys_virt_to_phys(v) ( (uint32_t)(v) & 0x1FFFFFFFul )


/*
 * Convert MEC14xx MIPS M14K physical address to virtual.
 * Bit-wise OR bits[31:29] of physical with 101b
 */
#define sys_phys_to_virt(p) ( (uint32_t)(p) | 0xA0000000ul )


#ifdef __cplusplus
}
#endif


#endif  /* MEC14XX_H */

/**   @}
 */

