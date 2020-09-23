/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : mcu_info.h
* Device(s)    : RX72N
* Description  : Information about the MCU.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.10.2019 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Gets MCU configuration information. */
#include "r_bsp_config.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef MCU_INFO
#define MCU_INFO

/* MCU CPU Version */
#define BSP_MCU_CPU_VERSION    (3)

/* CPU cycles. Known number of RXv3 CPU cycles required to execute the delay_wait() loop */
#define CPU_CYCLES_PER_LOOP    (3)

/* MCU Series. */
#if BSP_CFG_MCU_PART_SERIES == 0x0
    #define BSP_MCU_SERIES_RX700    (1)
#else
    #error "ERROR - BSP_CFG_MCU_PART_SERIES - Unknown MCU Series chosen in r_bsp_config.h"
#endif

/* This macro means that this MCU is part of the RX72x collection of MCUs (i.e. RX72N). */
#define BSP_MCU_RX72_ALL            (1)

/* MCU Group name. */
#if BSP_CFG_MCU_PART_GROUP == 0x0
    #define BSP_MCU_RX72N           (1)
#else
    #error "ERROR - BSP_CFG_MCU_PART_GROUP - Unknown MCU Group chosen in r_bsp_config.h"
#endif

/* Package. */
#if   BSP_CFG_MCU_PART_PACKAGE == 0x0
    #define BSP_PACKAGE_LFQFP176    (1)
    #define BSP_PACKAGE_PINS        (176)
#elif BSP_CFG_MCU_PART_PACKAGE == 0x1
    #define BSP_PACKAGE_LFBGA176    (1)
    #define BSP_PACKAGE_PINS        (176)
#elif BSP_CFG_MCU_PART_PACKAGE == 0x2
    #define BSP_PACKAGE_LFBGA224    (1)
    #define BSP_PACKAGE_PINS        (224)
#elif BSP_CFG_MCU_PART_PACKAGE == 0x3
    #define BSP_PACKAGE_LFQFP144    (1)
    #define BSP_PACKAGE_PINS        (144)
#elif BSP_CFG_MCU_PART_PACKAGE == 0x4
    #define BSP_PACKAGE_TFLGA145    (1)
    #define BSP_PACKAGE_PINS        (145)
#elif BSP_CFG_MCU_PART_PACKAGE == 0x5
    #define BSP_PACKAGE_LFQFP100    (1)
    #define BSP_PACKAGE_PINS        (100)
#else
    #error "ERROR - BSP_CFG_MCU_PART_PACKAGE - Unknown package chosen in r_bsp_config.h"
#endif

/* Memory size of your MCU. */
#if   BSP_CFG_MCU_PART_MEMORY_SIZE == 0xD
    #define BSP_ROM_SIZE_BYTES              (2097152)
    #define BSP_RAM_SIZE_BYTES              (1048576)
    #define BSP_DATA_FLASH_SIZE_BYTES       (32768)
#elif BSP_CFG_MCU_PART_MEMORY_SIZE == 0x17
    #define BSP_ROM_SIZE_BYTES              (4194304)
    #define BSP_RAM_SIZE_BYTES              (1048576)
    #define BSP_DATA_FLASH_SIZE_BYTES       (32768)
#else
    #error "ERROR - BSP_CFG_MCU_PART_MEMORY_SIZE - Unknown memory size chosen in r_bsp_config.h"
#endif

/* These macros define clock speeds for fixed speed clocks. */
#define BSP_LOCO_HZ                         (240000)
#define BSP_SUB_CLOCK_HZ                    (32768)

/* Define frequency of HOCO. */
#if   BSP_CFG_HOCO_FREQUENCY == 0
    #define BSP_HOCO_HZ                     (16000000)
#elif BSP_CFG_HOCO_FREQUENCY == 1
    #define BSP_HOCO_HZ                     (18000000)
#elif BSP_CFG_HOCO_FREQUENCY == 2
    #define BSP_HOCO_HZ                     (20000000)
#else
    #error "ERROR - Invalid HOCO frequency chosen in r_bsp_config.h! Set valid value for BSP_CFG_HOCO_FREQUENCY."
#endif

/* Clock source select (CKSEL).
   0 = Low Speed On-Chip Oscillator  (LOCO)
   1 = High Speed On-Chip Oscillator (HOCO)
   2 = Main Clock Oscillator
   3 = Sub-Clock Oscillator
   4 = PLL Circuit
*/ 
#if   BSP_CFG_CLOCK_SOURCE == 0
    #define BSP_SELECTED_CLOCK_HZ       (BSP_LOCO_HZ)
#elif BSP_CFG_CLOCK_SOURCE == 1
    #define BSP_SELECTED_CLOCK_HZ       (BSP_HOCO_HZ)
#elif BSP_CFG_CLOCK_SOURCE == 2
    #define BSP_SELECTED_CLOCK_HZ       (BSP_CFG_XTAL_HZ)
#elif BSP_CFG_CLOCK_SOURCE == 3
    #define BSP_SELECTED_CLOCK_HZ       (BSP_SUB_CLOCK_HZ)
#elif BSP_CFG_CLOCK_SOURCE == 4
    #if   BSP_CFG_PLL_SRC == 0
        #define BSP_SELECTED_CLOCK_HZ   ((BSP_CFG_XTAL_HZ/BSP_CFG_PLL_DIV) * BSP_CFG_PLL_MUL)
    #elif BSP_CFG_PLL_SRC == 1
        #define BSP_SELECTED_CLOCK_HZ   ((BSP_HOCO_HZ/BSP_CFG_PLL_DIV) * BSP_CFG_PLL_MUL)
    #else
        #error "ERROR - Valid PLL clock source must be chosen in r_bsp_config.h using BSP_CFG_PLL_SRC macro."
    #endif
#else
    #error "ERROR - BSP_CFG_CLOCK_SOURCE - Unknown clock source chosen in r_bsp_config.h"
#endif

/* Define frequency of PPLL clock. */
#if   BSP_CFG_PLL_SRC == 0
    #define BSP_PPLL_CLOCK_HZ           ((BSP_CFG_XTAL_HZ/BSP_CFG_PPLL_DIV) * BSP_CFG_PPLL_MUL)
#elif BSP_CFG_PLL_SRC == 1
    #define BSP_PPLL_CLOCK_HZ           ((BSP_HOCO_HZ/BSP_CFG_PPLL_DIV) * BSP_CFG_PPLL_MUL)
#else
    #error "ERROR - Valid PLL clock source must be chosen in r_bsp_config.h using BSP_CFG_PLL_SRC macro."
#endif

/*    Extended Bus Master Priority setting
   0 = GLCDC graphics 1 data read
   1 = DRW2D texture data read
   2 = DRW2D frame buffer data read write and display list data read
   3 = GLCDC graphics 2 data read
   4 = EDMAC
   
   Note : Settings other than above are prohibited.
          Duplicate priority settings can not be made.
*/
#if (BSP_CFG_EBMAPCR_1ST_PRIORITY == BSP_CFG_EBMAPCR_2ND_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_1ST_PRIORITY == BSP_CFG_EBMAPCR_3RD_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_1ST_PRIORITY == BSP_CFG_EBMAPCR_4TH_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_1ST_PRIORITY == BSP_CFG_EBMAPCR_5TH_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_2ND_PRIORITY == BSP_CFG_EBMAPCR_3RD_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_2ND_PRIORITY == BSP_CFG_EBMAPCR_4TH_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_2ND_PRIORITY == BSP_CFG_EBMAPCR_5TH_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_3RD_PRIORITY == BSP_CFG_EBMAPCR_4TH_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_3RD_PRIORITY == BSP_CFG_EBMAPCR_5TH_PRIORITY) ||\
    (BSP_CFG_EBMAPCR_4TH_PRIORITY == BSP_CFG_EBMAPCR_5TH_PRIORITY)
 #error "Error! Invalid setting for Extended Bus Master Priority in r_bsp_config.h. Please check BSP_CFG_EX_BUS_1ST_PRIORITY to BSP_CFG_EX_BUS_5TH_PRIORITY"
#endif
#if (5 <= BSP_CFG_EBMAPCR_1ST_PRIORITY) ||\
    (5 <= BSP_CFG_EBMAPCR_2ND_PRIORITY) ||\
    (5 <= BSP_CFG_EBMAPCR_3RD_PRIORITY) ||\
    (5 <= BSP_CFG_EBMAPCR_4TH_PRIORITY) ||\
    (5 <= BSP_CFG_EBMAPCR_5TH_PRIORITY)
 #error "Error! Invalid setting for Extended Bus Master Priority in r_bsp_config.h. Please check BSP_CFG_EX_BUS_1ST_PRIORITY to BSP_CFG_EX_BUS_5TH_PRIORITY"
#endif

/* System clock speed in Hz. */
#define BSP_ICLK_HZ                 (BSP_SELECTED_CLOCK_HZ / BSP_CFG_ICK_DIV)
/* Peripheral Module Clock A speed in Hz. Used for ETHERC and EDMAC. */
#define BSP_PCLKA_HZ                (BSP_SELECTED_CLOCK_HZ / BSP_CFG_PCKA_DIV)
/* Peripheral Module Clock B speed in Hz. */
#define BSP_PCLKB_HZ                (BSP_SELECTED_CLOCK_HZ / BSP_CFG_PCKB_DIV)
/* Peripheral Module Clock C speed in Hz. */
#define BSP_PCLKC_HZ                (BSP_SELECTED_CLOCK_HZ / BSP_CFG_PCKC_DIV)
/* Peripheral Module Clock D speed in Hz. */
#define BSP_PCLKD_HZ                (BSP_SELECTED_CLOCK_HZ / BSP_CFG_PCKD_DIV)
/* External bus clock speed in Hz. */
#define BSP_BCLK_HZ                 (BSP_SELECTED_CLOCK_HZ / BSP_CFG_BCK_DIV)
/* FlashIF clock speed in Hz. */
#define BSP_FCLK_HZ                 (BSP_SELECTED_CLOCK_HZ / BSP_CFG_FCK_DIV)
/* USB clock speed in Hz. */
#if   BSP_CFG_USB_CLOCK_SOURCE == 2
    #define BSP_UCLK_HZ             (BSP_SELECTED_CLOCK_HZ / BSP_CFG_UCK_DIV)
#elif BSP_CFG_USB_CLOCK_SOURCE == 3
    #define BSP_UCLK_HZ             (BSP_PPLL_CLOCK_HZ / BSP_CFG_PPLCK_DIV)
#else
    #error "ERROR - BSP_CFG_USB_CLOCK_SOURCE - Unknown usb clock source chosen in r_bsp_config.h"
#endif

/* CLKOUT25M clock speed in Hz. */
#if   BSP_CFG_PHY_CLOCK_SOURCE == 0
    #define BSP_CLKOUT25M_HZ        (BSP_SELECTED_CLOCK_HZ/8)
#elif BSP_CFG_PHY_CLOCK_SOURCE == 1
    #define BSP_CLKOUT25M_HZ        (BSP_PPLL_CLOCK_HZ / 8)
#elif BSP_CFG_PHY_CLOCK_SOURCE == 2
    /* Ethernet-PHY not use */
#else
    #error "ERROR - BSP_CFG_PHY_CLOCK_SOURCE - Unknown Ethernet-PHY clock source chosen in r_bsp_config.h"
#endif

/* Null argument definitions. */
#define FIT_NO_FUNC                 ((void (*)(void *))0x10000000)  /* Reserved space on RX */
#define FIT_NO_PTR                  ((void *)0x10000000)            /* Reserved space on RX */

/* Mininum and maximum IPL levels available for this MCU. */
#define BSP_MCU_IPL_MAX             (0xF)
#define BSP_MCU_IPL_MIN             (0)

/* Frequency threshold of memory wait cycle setting. */
#define BSP_MCU_MEMWAIT_FREQ_THRESHOLD (120000000)        /* ICLK > 120MHz requires MEMWAIT register update */

/* Frequency threshold of iclk. */
#define BSP_MCU_ICLK_FREQ_THRESHOLD    (70000000)

/* MCU functions */
#define BSP_MCU_REGISTER_WRITE_PROTECTION
#define BSP_MCU_RCPC_PRC0
#define BSP_MCU_RCPC_PRC1
#define BSP_MCU_RCPC_PRC3
#define BSP_MCU_FLOATING_POINT
#define BSP_MCU_DOUBLE_PRECISION_FLOATING_POINT
#define BSP_MCU_EXCEPTION_TABLE
#define BSP_MCU_GROUP_INTERRUPT
#define BSP_MCU_GROUP_INTERRUPT_IE0
#define BSP_MCU_GROUP_INTERRUPT_BE0
#define BSP_MCU_GROUP_INTERRUPT_BL0
#define BSP_MCU_GROUP_INTERRUPT_BL1
#define BSP_MCU_GROUP_INTERRUPT_BL2
#define BSP_MCU_GROUP_INTERRUPT_AL0
#define BSP_MCU_GROUP_INTERRUPT_AL1
#define BSP_MCU_SOFTWARE_CONFIGURABLE_INTERRUPT
#define BSP_MCU_EXCEP_SUPERVISOR_INST_ISR
#define BSP_MCU_EXCEP_ACCESS_ISR
#define BSP_MCU_EXCEP_UNDEFINED_INST_ISR
#define BSP_MCU_EXCEP_FLOATING_POINT_ISR
#define BSP_MCU_NON_MASKABLE_ISR
#define BSP_MCU_UNDEFINED_INTERRUPT_SOURCE_ISR
#define BSP_MCU_BUS_ERROR_ISR
#define BSP_MCU_TRIGONOMETRIC

#define BSP_MCU_NMI_EXC_NMI_PIN
#define BSP_MCU_NMI_OSC_STOP_DETECT
#define BSP_MCU_NMI_WDT_ERROR
#define BSP_MCU_NMI_IWDT_ERROR
#define BSP_MCU_NMI_LVD1
#define BSP_MCU_NMI_LVD2
#define BSP_MCU_NMI_EXNMI
#define BSP_MCU_NMI_EXNMI_RAM
#define BSP_MCU_NMI_EXNMI_RAM_EXRAM
#define BSP_MCU_NMI_EXNMI_RAM_ECCRAM
#define BSP_MCU_NMI_EXNMI_DPFPUEX

#endif /* MCU_INFO */

