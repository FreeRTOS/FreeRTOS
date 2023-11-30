/* %ATMEL_LICENCE% */

#ifndef _SAMA5D3x_
#define _SAMA5D3x_

/** \addtogroup SAMA5D3x_definitions SAMA5D3x definitions
  This file defines all structures and symbols for SAMA5D3x:
    - registers and bitfields
    - peripheral base address
    - peripheral ID
    - PIO definitions
*/
/*@{*/

#ifdef __cplusplus
 extern "C" {
#endif 

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#include <stdint.h>
#ifndef __cplusplus
typedef volatile const uint32_t RoReg; /**< Read only 32-bit register (volatile const unsigned int) */
#else
typedef volatile       uint32_t RoReg; /**< Read only 32-bit register (volatile const unsigned int) */
#endif
typedef volatile       uint32_t WoReg; /**< Write only 32-bit register (volatile unsigned int) */
typedef volatile       uint32_t RwReg; /**< Read-Write 32-bit register (volatile unsigned int) */
#endif

typedef enum IRQn
{
  FIQ_IRQn             =  0, /**<  0 SAMA5D3x Advanced Interrupt Controller (FIQ) */
  SYS_IRQn             =  1, /**<  1 SAMA5D3x System Controller Interrupt (SYS) */
  DBGU_IRQn            =  2, /**<  2 SAMA5D3x Debug Unit Interrupt (DBGU) */
  PIT_IRQn             =  3, /**<  3 SAMA5D3x Periodic Interval Timer Interrupt (PIT) */
  WDT_IRQn             =  4, /**<  4 SAMA5D3x Watchdog timer Interrupt (WDT) */
  SMC_IRQn             =  5, /**<  5 SAMA5D3x Multi-bit ECC Interrupt (SMC) */
  PIOA_IRQn            =  6, /**<  6 SAMA5D3x Parallel I/O Controller A (PIOA) */
  PIOB_IRQn            =  7, /**<  7 SAMA5D3x Parallel I/O Controller B (PIOB) */
  PIOC_IRQn            =  8, /**<  8 SAMA5D3x Parallel I/O Controller C (PIOC) */
  PIOD_IRQn            =  9, /**<  9 SAMA5D3x Parallel I/O Controller D (PIOD) */
  PIOE_IRQn            = 10, /**< 10 SAMA5D3x Parallel I/O Controller E (PIOE) */
  SMD_IRQn             = 11, /**< 11 SAMA5D3x SMD Soft Modem (SMD) */
  USART0_IRQn          = 12, /**< 12 SAMA5D3x USART 0 (USART0) */
  USART1_IRQn          = 13, /**< 13 SAMA5D3x USART 1 (USART1) */
  USART2_IRQn          = 14, /**< 14 SAMA5D3x USART 2 (USART2) */
  USART3_IRQn          = 15, /**< 15 SAMA5D3x USART 3 (USART3) */
  UART0_IRQn           = 16, /**< 16 SAMA5D3x UART 0 (UART0) */
  UART1_IRQn           = 17, /**< 17 SAMA5D3x UART 1 (UART1) */
  TWI0_IRQn            = 18, /**< 18 SAMA5D3x Two-Wire Interface 0 (TWI0) */
  TWI1_IRQn            = 19, /**< 19 SAMA5D3x Two-Wire Interface 1 (TWI1) */
  TWI2_IRQn            = 20, /**< 20 SAMA5D3x Two-Wire Interface 2 (TWI2) */
  HSMCI0_IRQn          = 21, /**< 21 SAMA5D3x High Speed Multimedia Card Interface 0 (HSMCI0) */
  HSMCI1_IRQn          = 22, /**< 22 SAMA5D3x High Speed Multimedia Card Interface 1 (HSMCI1) */
  HSMCI2_IRQn          = 23, /**< 23 SAMA5D3x High Speed Multimedia Card Interface 2 (HSMCI2) */
  SPI0_IRQn            = 24, /**< 24 SAMA5D3x Serial Peripheral Interface 0 (SPI0) */
  SPI1_IRQn            = 25, /**< 25 SAMA5D3x Serial Peripheral Interface 1 (SPI1) */
  TC0_IRQn             = 26, /**< 26 SAMA5D3x Timer Counter 0 (ch. 0, 1, 2) (TC0) */
  TC1_IRQn             = 27, /**< 27 SAMA5D3x Timer Counter 1 (ch. 3, 4, 5) (TC1) */
  PWM_IRQn             = 28, /**< 28 SAMA5D3x Pulse Width Modulation Controller (PWM) */
  ADC_IRQn             = 29, /**< 29 SAMA5D3x Touch Screen ADC Controller (ADC) */
  DMAC0_IRQn           = 30, /**< 30 SAMA5D3x DMA Controller 0 (DMAC0) */
  DMAC1_IRQn           = 31, /**< 31 SAMA5D3x DMA Controller 1 (DMAC1) */
  UHPHS_IRQn           = 32, /**< 32 SAMA5D3x USB Host High Speed (UHPHS) */
  UDPHS_IRQn           = 33, /**< 33 SAMA5D3x USB Device High Speed (UDPHS) */
  GMAC_IRQn            = 34, /**< 34 SAMA5D3x Gigabit Ethernet MAC (GMAC) */
  EMAC_IRQn            = 35, /**< 35 SAMA5D3x Ethernet MAC (EMAC) */
  LCDC_IRQn            = 36, /**< 36 SAMA5D3x LCD Controller (LCDC) */
  ISI_IRQn             = 37, /**< 37 SAMA5D3x Image Sensor Interface (ISI) */
  SSC0_IRQn            = 38, /**< 38 SAMA5D3x Synchronous Serial Controller 0 (SSC0) */
  SSC1_IRQn            = 39, /**< 39 SAMA5D3x Synchronous Serial Controller 1 (SSC1) */
  CAN0_IRQn            = 40, /**< 40 SAMA5D3x CAN controller 0 (CAN0) */
  CAN1_IRQn            = 41, /**< 41 SAMA5D3x CAN controller 1 (CAN1) */
  SHA_IRQn             = 42, /**< 42 SAMA5D3x Secure Hash Algorithm (SHA) */
  AES_IRQn             = 43, /**< 43 SAMA5D3x Advanced Encryption Standard (AES) */
  TDES_IRQn            = 44, /**< 44 SAMA5D3x Triple Data EncryptionStandard (TDES) */
  TRNG_IRQn            = 45, /**< 45 SAMA5D3x True Random Number Generator (TRNG) */
  ARM_IRQn             = 46, /**< 46 SAMA5D3x Performance Monitor Unit (ARM) */
  IRQ_IRQn             = 47, /**< 47 SAMA5D3x Advanced Interrupt Controller (IRQ) */
  FUSE_IRQn            = 48, /**< 48 SAMA5D3x Fuse Controller (FUSE) */
  MPDDRC_IRQn          = 49, /**< 49 SAMA5D3x MPDDR controller (MPDDRC) */

  PERIPH_COUNT_IRQn    = 50  /**< Number of peripheral IDs */
} IRQn_Type;

/* ************************************************************************** */
/**  SOFTWARE PERIPHERAL API DEFINITION FOR SAMA5D3x */
/* ************************************************************************** */
/** \addtogroup SAMA5D3x_api Peripheral Software API */
/*@{*/

#include "component/component_adc.h"
#include "component/component_aic.h"
#include "component/component_aximx.h"
#include "component/component_bsc.h"
#include "component/component_can.h"
#include "component/component_dbgu.h"
#include "component/component_dmac.h"
#include "component/component_emac.h"
#include "component/component_gmac.h"
#include "component/component_fuse.h"
#include "component/component_gpbr.h"
#include "component/component_hsmci.h"
#include "component/component_isi.h"
#include "component/component_lcdc.h"
#include "component/component_matrix.h"
#include "component/component_mpddrc.h"
#include "component/component_pio.h"
#include "component/component_pit.h"
#include "component/component_pmc.h"
#include "component/component_pwm.h"
#include "component/component_rstc.h"
#include "component/component_rtc.h"
#include "component/component_sckc.h"
#include "component/component_sfr.h"
#include "component/component_shdwc.h"
#include "component/component_smc.h"
#include "component/component_spi.h"
#include "component/component_ssc.h"
#include "component/component_tc.h"
#include "component/component_trng.h"
#include "component/component_twi.h"
#include "component/component_uart.h"
#include "component/component_udphs.h"
#include "component/component_usart.h"
#include "component/component_wdt.h"
#include "component/component_aes.h"
#include "component/component_sha.h"
#include "component/component_tdes.h"
/*@}*/

/* ************************************************************************** */
/*   REGISTER ACCESS DEFINITIONS FOR SAMA5D31 */
/* ************************************************************************** */
/** \addtogroup SAMA5D31_reg Registers Access Definitions */
/*@{*/

#include "instance/instance_smd.h"
#include "instance/instance_aximx.h"
#include "instance/instance_can0.h"
#include "instance/instance_can1.h"
#include "instance/instance_hsmci0.h"
#include "instance/instance_spi0.h"
#include "instance/instance_ssc0.h"
#include "instance/instance_tc0.h"
#include "instance/instance_tc1.h"
#include "instance/instance_twi0.h"
#include "instance/instance_twi1.h"
#include "instance/instance_usart0.h"
#include "instance/instance_usart1.h"
#include "instance/instance_uart0.h"
#include "instance/instance_pwm.h"
#include "instance/instance_lcdc.h"
#include "instance/instance_isi.h"
#include "instance/instance_sfr.h"
#include "instance/instance_hsmci1.h"
#include "instance/instance_hsmci2.h"
#include "instance/instance_spi1.h"
#include "instance/instance_ssc1.h"
#include "instance/instance_adc.h"
#include "instance/instance_twi2.h"
#include "instance/instance_usart2.h"
#include "instance/instance_usart3.h"
#include "instance/instance_uart1.h"
#include "instance/instance_emac.h"
#include "instance/instance_gmac.h"
#include "instance/instance_udphs.h"
#include "instance/instance_trng.h"
#include "instance/instance_smc.h"
#include "instance/instance_fuse.h"
#include "instance/instance_dmac0.h"
#include "instance/instance_dmac1.h"
#include "instance/instance_mpddrc.h"
#include "instance/instance_matrix.h"
#include "instance/instance_dbgu.h"
#include "instance/instance_aic.h"
#include "instance/instance_pioa.h"
#include "instance/instance_piob.h"
#include "instance/instance_pioc.h"
#include "instance/instance_piod.h"
#include "instance/instance_pioe.h"
#include "instance/instance_pmc.h"
#include "instance/instance_rstc.h"
#include "instance/instance_shdwc.h"
#include "instance/instance_pit.h"
#include "instance/instance_wdt.h"
#include "instance/instance_sckc.h"
#include "instance/instance_bsc.h"
#include "instance/instance_gpbr.h"
#include "instance/instance_rtc.h"
#include "instance/instance_aes.h"
#include "instance/instance_sha.h"
#include "instance/instance_tdes.h"
/*@}*/


/* ************************************************************************** */
/*   PERIPHERAL ID DEFINITIONS FOR SAMA5D3x */
/* ************************************************************************** */
/** \addtogroup SAMA5D3x_id Peripheral Ids Definitions */
/*@{*/

#define ID_FIQ    ( 0) /**< \brief Advanced Interrupt Controller (FIQ) */
#define ID_SYS    ( 1) /**< \brief System Controller Interrupt (SYS) */
#define ID_DBGU   ( 2) /**< \brief Debug Unit Interrupt (DBGU) */
#define ID_PIT    ( 3) /**< \brief Periodic Interval Timer Interrupt (PIT) */
#define ID_WDT    ( 4) /**< \brief Watchdog timer Interrupt (WDT) */
#define ID_SMC    ( 5) /**< \brief Multi-bit ECC Interrupt (SMC) */
#define ID_PIOA   ( 6) /**< \brief Parallel I/O Controller A (PIOA) */
#define ID_PIOB   ( 7) /**< \brief Parallel I/O Controller B (PIOB) */
#define ID_PIOC   ( 8) /**< \brief Parallel I/O Controller C (PIOC) */
#define ID_PIOD   ( 9) /**< \brief Parallel I/O Controller D (PIOD) */
#define ID_PIOE   (10) /**< \brief Parallel I/O Controller E (PIOE) */
#define ID_SMD    (11) /**< \brief SMD Soft Modem (SMD) */
#define ID_USART0 (12) /**< \brief USART 0 (USART0) */
#define ID_USART1 (13) /**< \brief USART 1 (USART1) */
#define ID_USART2 (14) /**< \brief USART 2 (USART2) */
#define ID_USART3 (15) /**< \brief USART 3 (USART3) */
#define ID_UART0  (16) /**< \brief UART 0 (UART0) */
#define ID_UART1  (17) /**< \brief UART 1 (UART1) */
#define ID_TWI0   (18) /**< \brief Two-Wire Interface 0 (TWI0) */
#define ID_TWI1   (19) /**< \brief Two-Wire Interface 1 (TWI1) */
#define ID_TWI2   (20) /**< \brief Two-Wire Interface 2 (TWI2) */
#define ID_HSMCI0 (21) /**< \brief High Speed Multimedia Card Interface 0 (HSMCI0) */
#define ID_HSMCI1 (22) /**< \brief High Speed Multimedia Card Interface 1 (HSMCI1) */
#define ID_HSMCI2 (23) /**< \brief High Speed Multimedia Card Interface 2 (HSMCI2) */
#define ID_SPI0   (24) /**< \brief Serial Peripheral Interface 0 (SPI0) */
#define ID_SPI1   (25) /**< \brief Serial Peripheral Interface 1 (SPI1) */
#define ID_TC0    (26) /**< \brief Timer Counter 0 (ch. 0, 1, 2) (TC0) */
#define ID_TC1    (27) /**< \brief Timer Counter 1 (ch. 3, 4, 5) (TC1) */
#define ID_PWM    (28) /**< \brief Pulse Width Modulation Controller (PWM) */
#define ID_ADC    (29) /**< \brief Touch Screen ADC Controller (ADC) */
#define ID_DMAC0  (30) /**< \brief DMA Controller 0 (DMAC0) */
#define ID_DMAC1  (31) /**< \brief DMA Controller 1 (DMAC1) */
#define ID_UHPHS  (32) /**< \brief USB Host High Speed (UHPHS) */
#define ID_UDPHS  (33) /**< \brief USB Device High Speed (UDPHS) */
#define ID_GMAC   (34) /**< \brief Gigabit Ethernet MAC (GMAC) */
#define ID_EMAC   (35) /**< \brief Ethernet MAC (EMAC) */
#define ID_LCDC   (36) /**< \brief LCD Controller (LCDC) */
#define ID_ISI    (37) /**< \brief Image Sensor Interface (ISI) */
#define ID_SSC0   (38) /**< \brief Synchronous Serial Controller 0 (SSC0) */
#define ID_SSC1   (39) /**< \brief Synchronous Serial Controller 1 (SSC1) */
#define ID_CAN0   (40) /**< \brief CAN controller 0 (CAN0) */
#define ID_CAN1   (41) /**< \brief CAN controller 1 (CAN1) */
#define ID_SHA    (42) /**< \brief Secure Hash Algorithm (SHA) */
#define ID_AES    (43) /**< \brief Advanced Encryption Standard (AES) */
#define ID_TDES   (44) /**< \brief Triple Data EncryptionStandard (TDES) */
#define ID_TRNG   (45) /**< \brief True Random Number Generator (TRNG) */
#define ID_ARM    (46) /**< \brief Performance Monitor Unit (ARM) */
#define ID_IRQ    (47) /**< \brief Advanced Interrupt Controller (IRQ) */
#define ID_FUSE   (48) /**< \brief Fuse Controller (FUSE) */
#define ID_MPDDRC (49) /**< \brief MPDDR controller (MPDDRC) */

#define ID_PERIPH_COUNT (50) /**< \brief Number of peripheral IDs */
/*@}*/

/* ************************************************************************** */
/*   BASE ADDRESS DEFINITIONS FOR SAMA5D3x */
/* ************************************************************************** */
/** \addtogroup SAMA5D3x_base Peripheral Base Address Definitions */
/*@{*/

#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define SMD    (0x00400000U) /**< \brief (SMD   ) Base Address */
#define AXIMX  (0x00800000U) /**< \brief (AXIMX ) Base Address */
#define HSMCI0 (0xF0000000U) /**< \brief (HSMCI0) Base Address */
#define SPI0   (0xF0004000U) /**< \brief (SPI0  ) Base Address */
#define SSC0   (0xF0008000U) /**< \brief (SSC0  ) Base Address */
#define CAN0   (0xF000C000U) /**< \brief (CAN0  ) Base Address */
#define TC0    (0xF0010000U) /**< \brief (TC0   ) Base Address */
#define TWI0   (0xF0014000U) /**< \brief (TWI0  ) Base Address */
#define TWI1   (0xF0018000U) /**< \brief (TWI1  ) Base Address */
#define USART0 (0xF001C000U) /**< \brief (USART0) Base Address */
#define USART1 (0xF0020000U) /**< \brief (USART1) Base Address */
#define UART0  (0xF0024000U) /**< \brief (UART0 ) Base Address */
#define GMAC   (0xF0028000U) /**< \brief (GMAC  ) Base Address */
#define PWM    (0xF002C000U) /**< \brief (PWM   ) Base Address */
#define LCDC   (0xF0030000U) /**< \brief (LCDC  ) Base Address */
#define ISI    (0xF0034000U) /**< \brief (ISI   ) Base Address */
#define SFR    (0xF0038000U) /**< \brief (SFR   ) Base Address */
#define HSMCI1 (0xF8000000U) /**< \brief (HSMCI1) Base Address */
#define HSMCI2 (0xF8004000U) /**< \brief (HSMCI2) Base Address */
#define SPI1   (0xF8008000U) /**< \brief (SPI1  ) Base Address */
#define SSC1   (0xF800C000U) /**< \brief (SSC1  ) Base Address */
#define CAN1   (0xF8010000U) /**< \brief (CAN1  ) Base Address */
#define TC1    (0xF8014000U) /**< \brief (TC1   ) Base Address */
#define ADC    (0xF8018000U) /**< \brief (ADC   ) Base Address */
#define TWI2   (0xF801C000U) /**< \brief (TWI2  ) Base Address */
#define USART2 (0xF8020000U) /**< \brief (USART2) Base Address */
#define USART3 (0xF8024000U) /**< \brief (USART3) Base Address */
#define UART1  (0xF8028000U) /**< \brief (UART1 ) Base Address */
#define EMAC   (0xF802C000U) /**< \brief (EMAC  ) Base Address */
#define UDPHS  (0xF8030000U) /**< \brief (UDPHS ) Base Address */
#define SHA    (0xF8034000U) /**< \brief (SHA   ) Base Address */
#define AES    (0xF8038000U) /**< \brief (AES   ) Base Address */
#define TDES   (0xF803C000U) /**< \brief (TDES  ) Base Address */
#define TRNG   (0xF8040000U) /**< \brief (TRNG  ) Base Address */
#define SMC    (0xFFFFC000U) /**< \brief (SMC   ) Base Address */
#define FUSE   (0xFFFFE400U) /**< \brief (FUSE  ) Base Address */
#define DMAC0  (0xFFFFE600U) /**< \brief (DMAC0 ) Base Address */
#define DMAC1  (0xFFFFE800U) /**< \brief (DMAC1 ) Base Address */
#define MPDDRC (0xFFFFEA00U) /**< \brief (MPDDRC) Base Address */
#define MATRIX (0xFFFFEC00U) /**< \brief (MATRIX) Base Address */
#define DBGU   (0xFFFFEE00U) /**< \brief (DBGU  ) Base Address */
#define AIC    (0xFFFFF000U) /**< \brief (AIC   ) Base Address */
#define PIOA   (0xFFFFF200U) /**< \brief (PIOA  ) Base Address */
#define PIOB   (0xFFFFF400U) /**< \brief (PIOB  ) Base Address */
#define PIOC   (0xFFFFF600U) /**< \brief (PIOC  ) Base Address */
#define PIOD   (0xFFFFF800U) /**< \brief (PIOD  ) Base Address */
#define PIOE   (0xFFFFFA00U) /**< \brief (PIOE  ) Base Address */
#define PMC    (0xFFFFFC00U) /**< \brief (PMC   ) Base Address */
#define RSTC   (0xFFFFFE00U) /**< \brief (RSTC  ) Base Address */
#define SHDWC  (0xFFFFFE10U) /**< \brief (SHDWC ) Base Address */
#define PIT    (0xFFFFFE30U) /**< \brief (PIT   ) Base Address */
#define WDT    (0xFFFFFE40U) /**< \brief (WDT   ) Base Address */
#define SCKC   (0xFFFFFE50U) /**< \brief (SCKC  ) Base Address */
#define BSC    (0xFFFFFE54U) /**< \brief (BSC   ) Base Address */
#define GPBR   (0xFFFFFE60U) /**< \brief (GPBR  ) Base Address */
#define RTC    (0xFFFFFEB0U) /**< \brief (RTC   ) Base Address */
#else
#define SMD    ((Smd    *)0x00400000U) /**< \brief (SMD   ) Base Address */
#define AXIMX  ((Aximx  *)0x00800000U) /**< \brief (AXIMX ) Base Address */
#define HSMCI0 ((Hsmci  *)0xF0000000U) /**< \brief (HSMCI0) Base Address */
#define SPI0   ((Spi    *)0xF0004000U) /**< \brief (SPI0  ) Base Address */
#define SSC0   ((Ssc    *)0xF0008000U) /**< \brief (SSC0  ) Base Address */
#define CAN0   ((Can    *)0xF000C000U) /**< \brief (CAN0  ) Base Address */
#define TC0    ((Tc     *)0xF0010000U) /**< \brief (TC0   ) Base Address */
#define TWI0   ((Twi    *)0xF0014000U) /**< \brief (TWI0  ) Base Address */
#define TWI1   ((Twi    *)0xF0018000U) /**< \brief (TWI1  ) Base Address */
#define USART0 ((Usart  *)0xF001C000U) /**< \brief (USART0) Base Address */
#define USART1 ((Usart  *)0xF0020000U) /**< \brief (USART1) Base Address */
#define UART0  ((Uart   *)0xF0024000U) /**< \brief (UART0 ) Base Address */
#define GMAC   ((Gmac   *)0xF0028000U) /**< \brief (GMAC  ) Base Address */
#define PWM    ((Pwm    *)0xF002C000U) /**< \brief (PWM   ) Base Address */
#define LCDC   ((Lcdc   *)0xF0030000U) /**< \brief (LCDC  ) Base Address */
#define ISI    ((Isi    *)0xF0034000U) /**< \brief (ISI   ) Base Address */
#define SFR    ((Sfr    *)0xF0038000U) /**< \brief (SFR   ) Base Address */
#define HSMCI1 ((Hsmci  *)0xF8000000U) /**< \brief (HSMCI1) Base Address */
#define HSMCI2 ((Hsmci  *)0xF8004000U) /**< \brief (HSMCI2) Base Address */
#define SPI1   ((Spi    *)0xF8008000U) /**< \brief (SPI1  ) Base Address */
#define SSC1   ((Ssc    *)0xF800C000U) /**< \brief (SSC1  ) Base Address */
#define CAN1   ((Can    *)0xF8010000U) /**< \brief (CAN1  ) Base Address */
#define TC1    ((Tc     *)0xF8014000U) /**< \brief (TC1   ) Base Address */
#define ADC    ((Adc    *)0xF8018000U) /**< \brief (ADC   ) Base Address */
#define TWI2   ((Twi    *)0xF801C000U) /**< \brief (TWI2  ) Base Address */
#define USART2 ((Usart  *)0xF8020000U) /**< \brief (USART2) Base Address */
#define USART3 ((Usart  *)0xF8024000U) /**< \brief (USART3) Base Address */
#define UART1  ((Uart   *)0xF8028000U) /**< \brief (UART1 ) Base Address */
#define EMAC   ((Emac   *)0xF802C000U) /**< \brief (EMAC  ) Base Address */
#define UDPHS  ((Udphs  *)0xF8030000U) /**< \brief (UDPHS ) Base Address */
#define SHA    ((Sha    *)0xF8034000U) /**< \brief (SHA   ) Base Address */
#define AES    ((Aes    *)0xF8038000U) /**< \brief (AES   ) Base Address */
#define TDES   ((Tdes   *)0xF803C000U) /**< \brief (TDES  ) Base Address */
#define TRNG   ((Trng   *)0xF8040000U) /**< \brief (TRNG  ) Base Address */
#define SMC    ((Smc    *)0xFFFFC000U) /**< \brief (SMC   ) Base Address */
#define FUSE   ((Fuse   *)0xFFFFE400U) /**< \brief (FUSE  ) Base Address */
#define DMAC0  ((Dmac   *)0xFFFFE600U) /**< \brief (DMAC0 ) Base Address */
#define DMAC1  ((Dmac   *)0xFFFFE800U) /**< \brief (DMAC1 ) Base Address */
#define MPDDRC ((Mpddrc *)0xFFFFEA00U) /**< \brief (MPDDRC) Base Address */
#define MATRIX ((Matrix *)0xFFFFEC00U) /**< \brief (MATRIX) Base Address */
#define DBGU   ((Dbgu   *)0xFFFFEE00U) /**< \brief (DBGU  ) Base Address */
#define AIC    ((Aic    *)0xFFFFF000U) /**< \brief (AIC   ) Base Address */
#define PIOA   ((Pio    *)0xFFFFF200U) /**< \brief (PIOA  ) Base Address */
#define PIOB   ((Pio    *)0xFFFFF400U) /**< \brief (PIOB  ) Base Address */
#define PIOC   ((Pio    *)0xFFFFF600U) /**< \brief (PIOC  ) Base Address */
#define PIOD   ((Pio    *)0xFFFFF800U) /**< \brief (PIOD  ) Base Address */
#define PIOE   ((Pio    *)0xFFFFFA00U) /**< \brief (PIOE  ) Base Address */
#define PMC    ((Pmc    *)0xFFFFFC00U) /**< \brief (PMC   ) Base Address */
#define RSTC   ((Rstc   *)0xFFFFFE00U) /**< \brief (RSTC  ) Base Address */
#define SHDWC  ((Shdwc  *)0xFFFFFE10U) /**< \brief (SHDWC ) Base Address */
#define PIT    ((Pit    *)0xFFFFFE30U) /**< \brief (PIT   ) Base Address */
#define WDT    ((Wdt    *)0xFFFFFE40U) /**< \brief (WDT   ) Base Address */
#define SCKC   ((Sckc   *)0xFFFFFE50U) /**< \brief (SCKC  ) Base Address */
#define BSC    ((Bsc    *)0xFFFFFE54U) /**< \brief (BSC   ) Base Address */
#define GPBR   ((Gpbr   *)0xFFFFFE60U) /**< \brief (GPBR  ) Base Address */
#define RTC    ((Rtc    *)0xFFFFFEB0U) /**< \brief (RTC   ) Base Address */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/*@}*/

/* ************************************************************************** */
/*   PIO DEFINITIONS FOR SAMA5D3x */
/* ************************************************************************** */
/** \addtogroup SAMA5D3x_pio Peripheral Pio Definitions */
/*@{*/

#define PIO_PA0              (1u << 0)  /**< \brief Pin Controlled by PA0 */
#define PIO_PA1              (1u << 1)  /**< \brief Pin Controlled by PA1 */
#define PIO_PA2              (1u << 2)  /**< \brief Pin Controlled by PA2 */
#define PIO_PA3              (1u << 3)  /**< \brief Pin Controlled by PA3 */
#define PIO_PA4              (1u << 4)  /**< \brief Pin Controlled by PA4 */
#define PIO_PA5              (1u << 5)  /**< \brief Pin Controlled by PA5 */
#define PIO_PA6              (1u << 6)  /**< \brief Pin Controlled by PA6 */
#define PIO_PA7              (1u << 7)  /**< \brief Pin Controlled by PA7 */
#define PIO_PA8              (1u << 8)  /**< \brief Pin Controlled by PA8 */
#define PIO_PA9              (1u << 9)  /**< \brief Pin Controlled by PA9 */
#define PIO_PA10             (1u << 10) /**< \brief Pin Controlled by PA10 */
#define PIO_PA11             (1u << 11) /**< \brief Pin Controlled by PA11 */
#define PIO_PA12             (1u << 12) /**< \brief Pin Controlled by PA12 */
#define PIO_PA13             (1u << 13) /**< \brief Pin Controlled by PA13 */
#define PIO_PA14             (1u << 14) /**< \brief Pin Controlled by PA14 */
#define PIO_PA15             (1u << 15) /**< \brief Pin Controlled by PA15 */
#define PIO_PA16             (1u << 16) /**< \brief Pin Controlled by PA16 */
#define PIO_PA17             (1u << 17) /**< \brief Pin Controlled by PA17 */
#define PIO_PA18             (1u << 18) /**< \brief Pin Controlled by PA18 */
#define PIO_PA19             (1u << 19) /**< \brief Pin Controlled by PA19 */
#define PIO_PA20             (1u << 20) /**< \brief Pin Controlled by PA20 */
#define PIO_PA21             (1u << 21) /**< \brief Pin Controlled by PA21 */
#define PIO_PA22             (1u << 22) /**< \brief Pin Controlled by PA22 */
#define PIO_PA23             (1u << 23) /**< \brief Pin Controlled by PA23 */
#define PIO_PA24             (1u << 24) /**< \brief Pin Controlled by PA24 */
#define PIO_PA25             (1u << 25) /**< \brief Pin Controlled by PA25 */
#define PIO_PA26             (1u << 26) /**< \brief Pin Controlled by PA26 */
#define PIO_PA27             (1u << 27) /**< \brief Pin Controlled by PA27 */
#define PIO_PA28             (1u << 28) /**< \brief Pin Controlled by PA28 */
#define PIO_PA29             (1u << 29) /**< \brief Pin Controlled by PA29 */
#define PIO_PA30             (1u << 30) /**< \brief Pin Controlled by PA30 */
#define PIO_PA31             (1u << 31) /**< \brief Pin Controlled by PA31 */
#define PIO_PB0              (1u << 0)  /**< \brief Pin Controlled by PB0 */
#define PIO_PB1              (1u << 1)  /**< \brief Pin Controlled by PB1 */
#define PIO_PB2              (1u << 2)  /**< \brief Pin Controlled by PB2 */
#define PIO_PB3              (1u << 3)  /**< \brief Pin Controlled by PB3 */
#define PIO_PB4              (1u << 4)  /**< \brief Pin Controlled by PB4 */
#define PIO_PB5              (1u << 5)  /**< \brief Pin Controlled by PB5 */
#define PIO_PB6              (1u << 6)  /**< \brief Pin Controlled by PB6 */
#define PIO_PB7              (1u << 7)  /**< \brief Pin Controlled by PB7 */
#define PIO_PB8              (1u << 8)  /**< \brief Pin Controlled by PB8 */
#define PIO_PB9              (1u << 9)  /**< \brief Pin Controlled by PB9 */
#define PIO_PB10             (1u << 10) /**< \brief Pin Controlled by PB10 */
#define PIO_PB11             (1u << 11) /**< \brief Pin Controlled by PB11 */
#define PIO_PB12             (1u << 12) /**< \brief Pin Controlled by PB12 */
#define PIO_PB13             (1u << 13) /**< \brief Pin Controlled by PB13 */
#define PIO_PB14             (1u << 14) /**< \brief Pin Controlled by PB14 */
#define PIO_PB15             (1u << 15) /**< \brief Pin Controlled by PB15 */
#define PIO_PB16             (1u << 16) /**< \brief Pin Controlled by PB16 */
#define PIO_PB17             (1u << 17) /**< \brief Pin Controlled by PB17 */
#define PIO_PB18             (1u << 18) /**< \brief Pin Controlled by PB18 */
#define PIO_PB19             (1u << 19) /**< \brief Pin Controlled by PB19 */
#define PIO_PB20             (1u << 20) /**< \brief Pin Controlled by PB20 */
#define PIO_PB21             (1u << 21) /**< \brief Pin Controlled by PB21 */
#define PIO_PB22             (1u << 22) /**< \brief Pin Controlled by PB22 */
#define PIO_PB23             (1u << 23) /**< \brief Pin Controlled by PB23 */
#define PIO_PB24             (1u << 24) /**< \brief Pin Controlled by PB24 */
#define PIO_PB25             (1u << 25) /**< \brief Pin Controlled by PB25 */
#define PIO_PB26             (1u << 26) /**< \brief Pin Controlled by PB26 */
#define PIO_PB27             (1u << 27) /**< \brief Pin Controlled by PB27 */
#define PIO_PB28             (1u << 28) /**< \brief Pin Controlled by PB28 */
#define PIO_PB29             (1u << 29) /**< \brief Pin Controlled by PB29 */
#define PIO_PB30             (1u << 30) /**< \brief Pin Controlled by PB30 */
#define PIO_PB31             (1u << 31) /**< \brief Pin Controlled by PB31 */
#define PIO_PC0              (1u << 0)  /**< \brief Pin Controlled by PC0 */
#define PIO_PC1              (1u << 1)  /**< \brief Pin Controlled by PC1 */
#define PIO_PC2              (1u << 2)  /**< \brief Pin Controlled by PC2 */
#define PIO_PC3              (1u << 3)  /**< \brief Pin Controlled by PC3 */
#define PIO_PC4              (1u << 4)  /**< \brief Pin Controlled by PC4 */
#define PIO_PC5              (1u << 5)  /**< \brief Pin Controlled by PC5 */
#define PIO_PC6              (1u << 6)  /**< \brief Pin Controlled by PC6 */
#define PIO_PC7              (1u << 7)  /**< \brief Pin Controlled by PC7 */
#define PIO_PC8              (1u << 8)  /**< \brief Pin Controlled by PC8 */
#define PIO_PC9              (1u << 9)  /**< \brief Pin Controlled by PC9 */
#define PIO_PC10             (1u << 10) /**< \brief Pin Controlled by PC10 */
#define PIO_PC11             (1u << 11) /**< \brief Pin Controlled by PC11 */
#define PIO_PC12             (1u << 12) /**< \brief Pin Controlled by PC12 */
#define PIO_PC13             (1u << 13) /**< \brief Pin Controlled by PC13 */
#define PIO_PC14             (1u << 14) /**< \brief Pin Controlled by PC14 */
#define PIO_PC15             (1u << 15) /**< \brief Pin Controlled by PC15 */
#define PIO_PC16             (1u << 16) /**< \brief Pin Controlled by PC16 */
#define PIO_PC17             (1u << 17) /**< \brief Pin Controlled by PC17 */
#define PIO_PC18             (1u << 18) /**< \brief Pin Controlled by PC18 */
#define PIO_PC19             (1u << 19) /**< \brief Pin Controlled by PC19 */
#define PIO_PC20             (1u << 20) /**< \brief Pin Controlled by PC20 */
#define PIO_PC21             (1u << 21) /**< \brief Pin Controlled by PC21 */
#define PIO_PC22             (1u << 22) /**< \brief Pin Controlled by PC22 */
#define PIO_PC23             (1u << 23) /**< \brief Pin Controlled by PC23 */
#define PIO_PC24             (1u << 24) /**< \brief Pin Controlled by PC24 */
#define PIO_PC25             (1u << 25) /**< \brief Pin Controlled by PC25 */
#define PIO_PC26             (1u << 26) /**< \brief Pin Controlled by PC26 */
#define PIO_PC27             (1u << 27) /**< \brief Pin Controlled by PC27 */
#define PIO_PC28             (1u << 28) /**< \brief Pin Controlled by PC28 */
#define PIO_PC29             (1u << 29) /**< \brief Pin Controlled by PC29 */
#define PIO_PC30             (1u << 30) /**< \brief Pin Controlled by PC30 */
#define PIO_PC31             (1u << 31) /**< \brief Pin Controlled by PC31 */
#define PIO_PD0              (1u << 0)  /**< \brief Pin Controlled by PD0 */
#define PIO_PD1              (1u << 1)  /**< \brief Pin Controlled by PD1 */
#define PIO_PD2              (1u << 2)  /**< \brief Pin Controlled by PD2 */
#define PIO_PD3              (1u << 3)  /**< \brief Pin Controlled by PD3 */
#define PIO_PD4              (1u << 4)  /**< \brief Pin Controlled by PD4 */
#define PIO_PD5              (1u << 5)  /**< \brief Pin Controlled by PD5 */
#define PIO_PD6              (1u << 6)  /**< \brief Pin Controlled by PD6 */
#define PIO_PD7              (1u << 7)  /**< \brief Pin Controlled by PD7 */
#define PIO_PD8              (1u << 8)  /**< \brief Pin Controlled by PD8 */
#define PIO_PD9              (1u << 9)  /**< \brief Pin Controlled by PD9 */
#define PIO_PD10             (1u << 10) /**< \brief Pin Controlled by PD10 */
#define PIO_PD11             (1u << 11) /**< \brief Pin Controlled by PD11 */
#define PIO_PD12             (1u << 12) /**< \brief Pin Controlled by PD12 */
#define PIO_PD13             (1u << 13) /**< \brief Pin Controlled by PD13 */
#define PIO_PD14             (1u << 14) /**< \brief Pin Controlled by PD14 */
#define PIO_PD15             (1u << 15) /**< \brief Pin Controlled by PD15 */
#define PIO_PD16             (1u << 16) /**< \brief Pin Controlled by PD16 */
#define PIO_PD17             (1u << 17) /**< \brief Pin Controlled by PD17 */
#define PIO_PD18             (1u << 18) /**< \brief Pin Controlled by PD18 */
#define PIO_PD19             (1u << 19) /**< \brief Pin Controlled by PD19 */
#define PIO_PD20             (1u << 20) /**< \brief Pin Controlled by PD20 */
#define PIO_PD21             (1u << 21) /**< \brief Pin Controlled by PD21 */
#define PIO_PD22             (1u << 22) /**< \brief Pin Controlled by PD22 */
#define PIO_PD23             (1u << 23) /**< \brief Pin Controlled by PD23 */
#define PIO_PD24             (1u << 24) /**< \brief Pin Controlled by PD24 */
#define PIO_PD25             (1u << 25) /**< \brief Pin Controlled by PD25 */
#define PIO_PD26             (1u << 26) /**< \brief Pin Controlled by PD26 */
#define PIO_PD27             (1u << 27) /**< \brief Pin Controlled by PD27 */
#define PIO_PD28             (1u << 28) /**< \brief Pin Controlled by PD28 */
#define PIO_PD29             (1u << 29) /**< \brief Pin Controlled by PD29 */
#define PIO_PD30             (1u << 30) /**< \brief Pin Controlled by PD30 */
#define PIO_PD31             (1u << 31) /**< \brief Pin Controlled by PD31 */
#define PIO_PE0              (1u << 0)  /**< \brief Pin Controlled by PE0 */
#define PIO_PE1              (1u << 1)  /**< \brief Pin Controlled by PE1 */
#define PIO_PE2              (1u << 2)  /**< \brief Pin Controlled by PE2 */
#define PIO_PE3              (1u << 3)  /**< \brief Pin Controlled by PE3 */
#define PIO_PE4              (1u << 4)  /**< \brief Pin Controlled by PE4 */
#define PIO_PE5              (1u << 5)  /**< \brief Pin Controlled by PE5 */
#define PIO_PE6              (1u << 6)  /**< \brief Pin Controlled by PE6 */
#define PIO_PE7              (1u << 7)  /**< \brief Pin Controlled by PE7 */
#define PIO_PE8              (1u << 8)  /**< \brief Pin Controlled by PE8 */
#define PIO_PE9              (1u << 9)  /**< \brief Pin Controlled by PE9 */
#define PIO_PE10             (1u << 10) /**< \brief Pin Controlled by PE10 */
#define PIO_PE11             (1u << 11) /**< \brief Pin Controlled by PE11 */
#define PIO_PE12             (1u << 12) /**< \brief Pin Controlled by PE12 */
#define PIO_PE13             (1u << 13) /**< \brief Pin Controlled by PE13 */
#define PIO_PE14             (1u << 14) /**< \brief Pin Controlled by PE14 */
#define PIO_PE15             (1u << 15) /**< \brief Pin Controlled by PE15 */
#define PIO_PE16             (1u << 16) /**< \brief Pin Controlled by PE16 */
#define PIO_PE17             (1u << 17) /**< \brief Pin Controlled by PE17 */
#define PIO_PE18             (1u << 18) /**< \brief Pin Controlled by PE18 */
#define PIO_PE19             (1u << 19) /**< \brief Pin Controlled by PE19 */
#define PIO_PE20             (1u << 20) /**< \brief Pin Controlled by PE20 */
#define PIO_PE21             (1u << 21) /**< \brief Pin Controlled by PE21 */
#define PIO_PE22             (1u << 22) /**< \brief Pin Controlled by PE22 */
#define PIO_PE23             (1u << 23) /**< \brief Pin Controlled by PE23 */
#define PIO_PE24             (1u << 24) /**< \brief Pin Controlled by PE24 */
#define PIO_PE25             (1u << 25) /**< \brief Pin Controlled by PE25 */
#define PIO_PE26             (1u << 26) /**< \brief Pin Controlled by PE26 */
#define PIO_PE27             (1u << 27) /**< \brief Pin Controlled by PE27 */
#define PIO_PE28             (1u << 28) /**< \brief Pin Controlled by PE28 */
#define PIO_PE29             (1u << 29) /**< \brief Pin Controlled by PE29 */
#define PIO_PE30             (1u << 30) /**< \brief Pin Controlled by PE30 */
#define PIO_PE31             (1u << 31) /**< \brief Pin Controlled by PE31 */
/* ========== Pio definition for ADC peripheral ========== */
#define PIO_PD20A_AD0        (1u << 20) /**< \brief Adc signal: AD0 */
#define PIO_PD21A_AD1        (1u << 21) /**< \brief Adc signal: AD1 */
#define PIO_PD30A_AD10       (1u << 30) /**< \brief Adc signal: AD10 */
#define PIO_PD31A_AD11       (1u << 31) /**< \brief Adc signal: AD11 */
#define PIO_PD22A_AD2        (1u << 22) /**< \brief Adc signal: AD2 */
#define PIO_PD23A_AD3        (1u << 23) /**< \brief Adc signal: AD3 */
#define PIO_PD24A_AD4        (1u << 24) /**< \brief Adc signal: AD4 */
#define PIO_PD25A_AD5        (1u << 25) /**< \brief Adc signal: AD5 */
#define PIO_PD26A_AD6        (1u << 26) /**< \brief Adc signal: AD6 */
#define PIO_PD27A_AD7        (1u << 27) /**< \brief Adc signal: AD7 */
#define PIO_PD28A_AD8        (1u << 28) /**< \brief Adc signal: AD8 */
#define PIO_PD29A_AD9        (1u << 29) /**< \brief Adc signal: AD9 */
#define PIO_PD19A_ADTRG      (1u << 19) /**< \brief Adc signal: ADTRG */
/* ========== Pio definition for AIC peripheral ========== */
#define PIO_PC31A_FIQ        (1u << 31) /**< \brief Aic signal: FIQ */
#define PIO_PE31A_IRQ        (1u << 31) /**< \brief Aic signal: IRQ */
/* ========== Pio definition for CAN0 peripheral ========== */
#define PIO_PD14C_CANRX0     (1u << 14) /**< \brief Can0 signal: CANRX0 */
#define PIO_PD15C_CANTX0     (1u << 15) /**< \brief Can0 signal: CANTX0 */
/* ========== Pio definition for CAN1 peripheral ========== */
#define PIO_PB14B_CANRX1     (1u << 14) /**< \brief Can1 signal: CANRX1 */
#define PIO_PB15B_CANTX1     (1u << 15) /**< \brief Can1 signal: CANTX1 */
/* ========== Pio definition for DBGU peripheral ========== */
#define PIO_PB30A_DRXD       (1u << 30) /**< \brief Dbgu signal: DRXD */
#define PIO_PB31A_DTXD       (1u << 31) /**< \brief Dbgu signal: DTXD */
/* ========== Pio definition for EBI peripheral ========== */
#define PIO_PE0A_A0          (1u << 0)  /**< \brief Ebi signal: A0/NBS0 */
#define PIO_PE0A_NBS0        (1u << 0)  /**< \brief Ebi signal: A0/NBS0 */
#define PIO_PE1A_A1          (1u << 1)  /**< \brief Ebi signal: A1 */
#define PIO_PE10A_A10        (1u << 10) /**< \brief Ebi signal: A10 */
#define PIO_PE11A_A11        (1u << 11) /**< \brief Ebi signal: A11 */
#define PIO_PE12A_A12        (1u << 12) /**< \brief Ebi signal: A12 */
#define PIO_PE13A_A13        (1u << 13) /**< \brief Ebi signal: A13 */
#define PIO_PE14A_A14        (1u << 14) /**< \brief Ebi signal: A14 */
#define PIO_PE15A_A15        (1u << 15) /**< \brief Ebi signal: A15 */
#define PIO_PE16A_A16        (1u << 16) /**< \brief Ebi signal: A16 */
#define PIO_PE17A_A17        (1u << 17) /**< \brief Ebi signal: A17 */
#define PIO_PE18A_A18        (1u << 18) /**< \brief Ebi signal: A18 */
#define PIO_PE19A_A19        (1u << 19) /**< \brief Ebi signal: A19 */
#define PIO_PE2A_A2          (1u << 2)  /**< \brief Ebi signal: A2 */
#define PIO_PE20A_A20        (1u << 20) /**< \brief Ebi signal: A20 */
#define PIO_PE21A_A21        (1u << 21) /**< \brief Ebi signal: A21/NANDALE */
#define PIO_PE21A_NANDALE    (1u << 21) /**< \brief Ebi signal: A21/NANDALE */
#define PIO_PE22A_A22        (1u << 22) /**< \brief Ebi signal: A22/NANDCLE */
#define PIO_PE22A_NANDCLE    (1u << 22) /**< \brief Ebi signal: A22/NANDCLE */
#define PIO_PE23A_A23        (1u << 23) /**< \brief Ebi signal: A23 */
#define PIO_PE24A_A24        (1u << 24) /**< \brief Ebi signal: A24 */
#define PIO_PE25A_A25        (1u << 25) /**< \brief Ebi signal: A25 */
#define PIO_PE3A_A3          (1u << 3)  /**< \brief Ebi signal: A3 */
#define PIO_PE4A_A4          (1u << 4)  /**< \brief Ebi signal: A4 */
#define PIO_PE5A_A5          (1u << 5)  /**< \brief Ebi signal: A5 */
#define PIO_PE6A_A6          (1u << 6)  /**< \brief Ebi signal: A6 */
#define PIO_PE7A_A7          (1u << 7)  /**< \brief Ebi signal: A7 */
#define PIO_PE8A_A8          (1u << 8)  /**< \brief Ebi signal: A8 */
#define PIO_PE9A_A9          (1u << 9)  /**< \brief Ebi signal: A9 */
#define PIO_PE26A_NCS0       (1u << 26) /**< \brief Ebi signal: NCS0 */
#define PIO_PE27A_NCS1       (1u << 27) /**< \brief Ebi signal: NCS1 */
#define PIO_PE28A_NCS2       (1u << 28) /**< \brief Ebi signal: NCS2 */
#define PIO_PE30A_NWAIT      (1u << 30) /**< \brief Ebi signal: NWAIT */
#define PIO_PE29A_NWR1       (1u << 29) /**< \brief Ebi signal: NWR1/NBS1 */
#define PIO_PE29A_NBS1       (1u << 29) /**< \brief Ebi signal: NWR1/NBS1 */
/* ========== Pio definition for EMAC peripheral ========== */
#define PIO_PC5A_ECRSDV      (1u << 5)  /**< \brief Emac signal: ECRSDV */
#define PIO_PC8A_EMDC        (1u << 8)  /**< \brief Emac signal: EMDC */
#define PIO_PC9A_EMDIO       (1u << 9)  /**< \brief Emac signal: EMDIO */
#define PIO_PC7A_EREFCK      (1u << 7)  /**< \brief Emac signal: EREFCK */
#define PIO_PC2A_ERX0        (1u << 2)  /**< \brief Emac signal: ERX0 */
#define PIO_PC3A_ERX1        (1u << 3)  /**< \brief Emac signal: ERX1 */
#define PIO_PC6A_ERXER       (1u << 6)  /**< \brief Emac signal: ERXER */
#define PIO_PC0A_ETX0        (1u << 0)  /**< \brief Emac signal: ETX0 */
#define PIO_PC1A_ETX1        (1u << 1)  /**< \brief Emac signal: ETX1 */
#define PIO_PC4A_ETXEN       (1u << 4)  /**< \brief Emac signal: ETXEN */
/* ========== Pio definition for GMAC peripheral ========== */
#define PIO_PB18A_G125CK     (1u << 18) /**< \brief Gmac signal: G125CK */
#define PIO_PB27B_G125CKO    (1u << 27) /**< \brief Gmac signal: G125CKO */
#define PIO_PB15A_GCOL       (1u << 15) /**< \brief Gmac signal: GCOL */
#define PIO_PB14A_GCRS       (1u << 14) /**< \brief Gmac signal: GCRS */
#define PIO_PB16A_GMDC       (1u << 16) /**< \brief Gmac signal: GMDC */
#define PIO_PB17A_GMDIO      (1u << 17) /**< \brief Gmac signal: GMDIO */
#define PIO_PB4A_GRX0        (1u << 4)  /**< \brief Gmac signal: GRX0 */
#define PIO_PB5A_GRX1        (1u << 5)  /**< \brief Gmac signal: GRX1 */
#define PIO_PB6A_GRX2        (1u << 6)  /**< \brief Gmac signal: GRX2 */
#define PIO_PB7A_GRX3        (1u << 7)  /**< \brief Gmac signal: GRX3 */
#define PIO_PB23B_GRX4       (1u << 23) /**< \brief Gmac signal: GRX4 */
#define PIO_PB24B_GRX5       (1u << 24) /**< \brief Gmac signal: GRX5 */
#define PIO_PB25B_GRX6       (1u << 25) /**< \brief Gmac signal: GRX6 */
#define PIO_PB26B_GRX7       (1u << 26) /**< \brief Gmac signal: GRX7 */
#define PIO_PB11A_GRXCK      (1u << 11) /**< \brief Gmac signal: GRXCK */
#define PIO_PB12A_GRXDV      (1u << 12) /**< \brief Gmac signal: GRXDV */
#define PIO_PB13A_GRXER      (1u << 13) /**< \brief Gmac signal: GRXER */
#define PIO_PB0A_GTX0        (1u << 0)  /**< \brief Gmac signal: GTX0 */
#define PIO_PB1A_GTX1        (1u << 1)  /**< \brief Gmac signal: GTX1 */
#define PIO_PB2A_GTX2        (1u << 2)  /**< \brief Gmac signal: GTX2 */
#define PIO_PB3A_GTX3        (1u << 3)  /**< \brief Gmac signal: GTX3 */
#define PIO_PB19B_GTX4       (1u << 19) /**< \brief Gmac signal: GTX4 */
#define PIO_PB20B_GTX5       (1u << 20) /**< \brief Gmac signal: GTX5 */
#define PIO_PB21B_GTX6       (1u << 21) /**< \brief Gmac signal: GTX6 */
#define PIO_PB22B_GTX7       (1u << 22) /**< \brief Gmac signal: GTX7 */
#define PIO_PB8A_GTXCK       (1u << 8)  /**< \brief Gmac signal: GTXCK */
#define PIO_PB9A_GTXEN       (1u << 9)  /**< \brief Gmac signal: GTXEN */
#define PIO_PB10A_GTXER      (1u << 10) /**< \brief Gmac signal: GTXER */
/* ========== Pio definition for HSMCI0 peripheral ========== */
#define PIO_PD0A_MCI0_CDA    (1u << 0)  /**< \brief Hsmci0 signal: MCI0_CDA */
#define PIO_PD9A_MCI0_CK     (1u << 9)  /**< \brief Hsmci0 signal: MCI0_CK */
#define PIO_PD1A_MCI0_DA0    (1u << 1)  /**< \brief Hsmci0 signal: MCI0_DA0 */
#define PIO_PD2A_MCI0_DA1    (1u << 2)  /**< \brief Hsmci0 signal: MCI0_DA1 */
#define PIO_PD3A_MCI0_DA2    (1u << 3)  /**< \brief Hsmci0 signal: MCI0_DA2 */
#define PIO_PD4A_MCI0_DA3    (1u << 4)  /**< \brief Hsmci0 signal: MCI0_DA3 */
#define PIO_PD5A_MCI0_DA4    (1u << 5)  /**< \brief Hsmci0 signal: MCI0_DA4 */
#define PIO_PD6A_MCI0_DA5    (1u << 6)  /**< \brief Hsmci0 signal: MCI0_DA5 */
#define PIO_PD7A_MCI0_DA6    (1u << 7)  /**< \brief Hsmci0 signal: MCI0_DA6 */
#define PIO_PD8A_MCI0_DA7    (1u << 8)  /**< \brief Hsmci0 signal: MCI0_DA7 */
/* ========== Pio definition for HSMCI1 peripheral ========== */
#define PIO_PB19A_MCI1_CDA   (1u << 19) /**< \brief Hsmci1 signal: MCI1_CDA */
#define PIO_PB24A_MCI1_CK    (1u << 24) /**< \brief Hsmci1 signal: MCI1_CK */
#define PIO_PB20A_MCI1_DA0   (1u << 20) /**< \brief Hsmci1 signal: MCI1_DA0 */
#define PIO_PB21A_MCI1_DA1   (1u << 21) /**< \brief Hsmci1 signal: MCI1_DA1 */
#define PIO_PB22A_MCI1_DA2   (1u << 22) /**< \brief Hsmci1 signal: MCI1_DA2 */
#define PIO_PB23A_MCI1_DA3   (1u << 23) /**< \brief Hsmci1 signal: MCI1_DA3 */
/* ========== Pio definition for HSMCI2 peripheral ========== */
#define PIO_PC10A_MCI2_CDA   (1u << 10) /**< \brief Hsmci2 signal: MCI2_CDA */
#define PIO_PC15A_MCI2_CK    (1u << 15) /**< \brief Hsmci2 signal: MCI2_CK */
#define PIO_PC11A_MCI2_DA0   (1u << 11) /**< \brief Hsmci2 signal: MCI2_DA0 */
#define PIO_PC12A_MCI2_DA1   (1u << 12) /**< \brief Hsmci2 signal: MCI2_DA1 */
#define PIO_PC13A_MCI2_DA2   (1u << 13) /**< \brief Hsmci2 signal: MCI2_DA2 */
#define PIO_PC14A_MCI2_DA3   (1u << 14) /**< \brief Hsmci2 signal: MCI2_DA3 */
/* ========== Pio definition for ISI peripheral ========== */
#define PIO_PA16C_ISI_D0     (1u << 16) /**< \brief Isi signal: ISI_D0 */
#define PIO_PA17C_ISI_D1     (1u << 17) /**< \brief Isi signal: ISI_D1 */
#define PIO_PC27C_ISI_D10    (1u << 27) /**< \brief Isi signal: ISI_D10 */
#define PIO_PC26C_ISI_D11    (1u << 26) /**< \brief Isi signal: ISI_D11 */
#define PIO_PA18C_ISI_D2     (1u << 18) /**< \brief Isi signal: ISI_D2 */
#define PIO_PA19C_ISI_D3     (1u << 19) /**< \brief Isi signal: ISI_D3 */
#define PIO_PA20C_ISI_D4     (1u << 20) /**< \brief Isi signal: ISI_D4 */
#define PIO_PA21C_ISI_D5     (1u << 21) /**< \brief Isi signal: ISI_D5 */
#define PIO_PA22C_ISI_D6     (1u << 22) /**< \brief Isi signal: ISI_D6 */
#define PIO_PA23C_ISI_D7     (1u << 23) /**< \brief Isi signal: ISI_D7 */
#define PIO_PC29C_ISI_D8     (1u << 29) /**< \brief Isi signal: ISI_D8 */
#define PIO_PC28C_ISI_D9     (1u << 28) /**< \brief Isi signal: ISI_D9 */
#define PIO_PA31C_ISI_HSYNC  (1u << 31) /**< \brief Isi signal: ISI_HSYNC */
#define PIO_PC30C_ISI_PCK    (1u << 30) /**< \brief Isi signal: ISI_PCK */
#define PIO_PA30C_ISI_VSYNC  (1u << 30) /**< \brief Isi signal: ISI_VSYNC */
/* ========== Pio definition for LCDC peripheral ========== */
#define PIO_PA0A_LCDDAT0     (1u << 0)  /**< \brief Lcdc signal: LCDDAT0 */
#define PIO_PA1A_LCDDAT1     (1u << 1)  /**< \brief Lcdc signal: LCDDAT1 */
#define PIO_PA10A_LCDDAT10   (1u << 10) /**< \brief Lcdc signal: LCDDAT10 */
#define PIO_PA11A_LCDDAT11   (1u << 11) /**< \brief Lcdc signal: LCDDAT11 */
#define PIO_PA12A_LCDDAT12   (1u << 12) /**< \brief Lcdc signal: LCDDAT12 */
#define PIO_PA13A_LCDDAT13   (1u << 13) /**< \brief Lcdc signal: LCDDAT13 */
#define PIO_PA14A_LCDDAT14   (1u << 14) /**< \brief Lcdc signal: LCDDAT14 */
#define PIO_PA15A_LCDDAT15   (1u << 15) /**< \brief Lcdc signal: LCDDAT15 */
#define PIO_PA16A_LCDDAT16   (1u << 16) /**< \brief Lcdc signal: LCDDAT16 */
#define PIO_PC14C_LCDDAT16   (1u << 14) /**< \brief Lcdc signal: LCDDAT16 */
#define PIO_PA17A_LCDDAT17   (1u << 17) /**< \brief Lcdc signal: LCDDAT17 */
#define PIO_PC13C_LCDDAT17   (1u << 13) /**< \brief Lcdc signal: LCDDAT17 */
#define PIO_PA18A_LCDDAT18   (1u << 18) /**< \brief Lcdc signal: LCDDAT18 */
#define PIO_PC12C_LCDDAT18   (1u << 12) /**< \brief Lcdc signal: LCDDAT18 */
#define PIO_PA19A_LCDDAT19   (1u << 19) /**< \brief Lcdc signal: LCDDAT19 */
#define PIO_PC11C_LCDDAT19   (1u << 11) /**< \brief Lcdc signal: LCDDAT19 */
#define PIO_PA2A_LCDDAT2     (1u << 2)  /**< \brief Lcdc signal: LCDDAT2 */
#define PIO_PA20A_LCDDAT20   (1u << 20) /**< \brief Lcdc signal: LCDDAT20 */
#define PIO_PC10C_LCDDAT20   (1u << 10) /**< \brief Lcdc signal: LCDDAT20 */
#define PIO_PA21A_LCDDAT21   (1u << 21) /**< \brief Lcdc signal: LCDDAT21 */
#define PIO_PC15C_LCDDAT21   (1u << 15) /**< \brief Lcdc signal: LCDDAT21 */
#define PIO_PA22A_LCDDAT22   (1u << 22) /**< \brief Lcdc signal: LCDDAT22 */
#define PIO_PE27C_LCDDAT22   (1u << 27) /**< \brief Lcdc signal: LCDDAT22 */
#define PIO_PA23A_LCDDAT23   (1u << 23) /**< \brief Lcdc signal: LCDDAT23 */
#define PIO_PE28C_LCDDAT23   (1u << 28) /**< \brief Lcdc signal: LCDDAT23 */
#define PIO_PA3A_LCDDAT3     (1u << 3)  /**< \brief Lcdc signal: LCDDAT3 */
#define PIO_PA4A_LCDDAT4     (1u << 4)  /**< \brief Lcdc signal: LCDDAT4 */
#define PIO_PA5A_LCDDAT5     (1u << 5)  /**< \brief Lcdc signal: LCDDAT5 */
#define PIO_PA6A_LCDDAT6     (1u << 6)  /**< \brief Lcdc signal: LCDDAT6 */
#define PIO_PA7A_LCDDAT7     (1u << 7)  /**< \brief Lcdc signal: LCDDAT7 */
#define PIO_PA8A_LCDDAT8     (1u << 8)  /**< \brief Lcdc signal: LCDDAT8 */
#define PIO_PA9A_LCDDAT9     (1u << 9)  /**< \brief Lcdc signal: LCDDAT9 */
#define PIO_PA29A_LCDDEN     (1u << 29) /**< \brief Lcdc signal: LCDDEN */
#define PIO_PA25A_LCDDISP    (1u << 25) /**< \brief Lcdc signal: LCDDISP */
#define PIO_PA27A_LCDHSYNC   (1u << 27) /**< \brief Lcdc signal: LCDHSYNC */
#define PIO_PA28A_LCDPCK     (1u << 28) /**< \brief Lcdc signal: LCDPCK */
#define PIO_PA24A_LCDPWM     (1u << 24) /**< \brief Lcdc signal: LCDPWM */
#define PIO_PA26A_LCDVSYNC   (1u << 26) /**< \brief Lcdc signal: LCDVSYNC */
/* ========== Pio definition for PMC peripheral ========== */
#define PIO_PD30B_PCK0       (1u << 30) /**< \brief Pmc signal: PCK0 */
#define PIO_PD31B_PCK1       (1u << 31) /**< \brief Pmc signal: PCK1 */
#define PIO_PC15B_PCK2       (1u << 15) /**< \brief Pmc signal: PCK2 */
/* ========== Pio definition for PWM peripheral ========== */
#define PIO_PC28B_PWMFI0     (1u << 28) /**< \brief Pwm signal: PWMFI0 */
#define PIO_PC31B_PWMFI1     (1u << 31) /**< \brief Pwm signal: PWMFI1 */
#define PIO_PC29B_PWMFI2     (1u << 29) /**< \brief Pwm signal: PWMFI2 */
#define PIO_PD16C_PWMFI3     (1u << 16) /**< \brief Pwm signal: PWMFI3 */
#define PIO_PA20B_PWMH0      (1u << 20) /**< \brief Pwm signal: PWMH0 */
#define PIO_PB0B_PWMH0       (1u << 0)  /**< \brief Pwm signal: PWMH0 */
#define PIO_PA22B_PWMH1      (1u << 22) /**< \brief Pwm signal: PWMH1 */
#define PIO_PB4B_PWMH1       (1u << 4)  /**< \brief Pwm signal: PWMH1 */
#define PIO_PB27C_PWMH1      (1u << 27) /**< \brief Pwm signal: PWMH1 */
#define PIO_PB8B_PWMH2       (1u << 8)  /**< \brief Pwm signal: PWMH2 */
#define PIO_PD5C_PWMH2       (1u << 5)  /**< \brief Pwm signal: PWMH2 */
#define PIO_PB12B_PWMH3      (1u << 12) /**< \brief Pwm signal: PWMH3 */
#define PIO_PD7C_PWMH3       (1u << 7)  /**< \brief Pwm signal: PWMH3 */
#define PIO_PA21B_PWML0      (1u << 21) /**< \brief Pwm signal: PWML0 */
#define PIO_PB1B_PWML0       (1u << 1)  /**< \brief Pwm signal: PWML0 */
#define PIO_PA23B_PWML1      (1u << 23) /**< \brief Pwm signal: PWML1 */
#define PIO_PB5B_PWML1       (1u << 5)  /**< \brief Pwm signal: PWML1 */
#define PIO_PE31B_PWML1      (1u << 31) /**< \brief Pwm signal: PWML1 */
#define PIO_PB9B_PWML2       (1u << 9)  /**< \brief Pwm signal: PWML2 */
#define PIO_PD6C_PWML2       (1u << 6)  /**< \brief Pwm signal: PWML2 */
#define PIO_PB13B_PWML3      (1u << 13) /**< \brief Pwm signal: PWML3 */
#define PIO_PD8C_PWML3       (1u << 8)  /**< \brief Pwm signal: PWML3 */
/* ========== Pio definition for SPI0 peripheral ========== */
#define PIO_PD10A_SPI0_MISO  (1u << 10) /**< \brief Spi0 signal: SPI0_MISO */
#define PIO_PD11A_SPI0_MOSI  (1u << 11) /**< \brief Spi0 signal: SPI0_MOSI */
#define PIO_PD13A_SPI0_NPCS0 (1u << 13) /**< \brief Spi0 signal: SPI0_NPCS0 */
#define PIO_PD14B_SPI0_NPCS1 (1u << 14) /**< \brief Spi0 signal: SPI0_NPCS1 */
#define PIO_PD15B_SPI0_NPCS2 (1u << 15) /**< \brief Spi0 signal: SPI0_NPCS2 */
#define PIO_PD16B_SPI0_NPCS3 (1u << 16) /**< \brief Spi0 signal: SPI0_NPCS3 */
#define PIO_PD12A_SPI0_SPCK  (1u << 12) /**< \brief Spi0 signal: SPI0_SPCK */
/* ========== Pio definition for SPI1 peripheral ========== */
#define PIO_PC22A_SPI1_MISO  (1u << 22) /**< \brief Spi1 signal: SPI1_MISO */
#define PIO_PC23A_SPI1_MOSI  (1u << 23) /**< \brief Spi1 signal: SPI1_MOSI */
#define PIO_PC25A_SPI1_NPCS0 (1u << 25) /**< \brief Spi1 signal: SPI1_NPCS0 */
#define PIO_PC26A_SPI1_NPCS1 (1u << 26) /**< \brief Spi1 signal: SPI1_NPCS1 */
#define PIO_PC27A_SPI1_NPCS2 (1u << 27) /**< \brief Spi1 signal: SPI1_NPCS2 */
#define PIO_PC28A_SPI1_NPCS3 (1u << 28) /**< \brief Spi1 signal: SPI1_NPCS3 */
#define PIO_PC24A_SPI1_SPCK  (1u << 24) /**< \brief Spi1 signal: SPI1_SPCK */
/* ========== Pio definition for SSC0 peripheral ========== */
#define PIO_PC21A_RD0        (1u << 21) /**< \brief Ssc0 signal: RD0 */
#define PIO_PC20A_RF0        (1u << 20) /**< \brief Ssc0 signal: RF0 */
#define PIO_PC19A_RK0        (1u << 19) /**< \brief Ssc0 signal: RK0 */
#define PIO_PC18A_TD0        (1u << 18) /**< \brief Ssc0 signal: TD0 */
#define PIO_PC17A_TF0        (1u << 17) /**< \brief Ssc0 signal: TF0 */
#define PIO_PC16A_TK0        (1u << 16) /**< \brief Ssc0 signal: TK0 */
/* ========== Pio definition for SSC1 peripheral ========== */
#define PIO_PB11B_RD1        (1u << 11) /**< \brief Ssc1 signal: RD1 */
#define PIO_PB10B_RF1        (1u << 10) /**< \brief Ssc1 signal: RF1 */
#define PIO_PB7B_RK1         (1u << 7)  /**< \brief Ssc1 signal: RK1 */
#define PIO_PB6B_TD1         (1u << 6)  /**< \brief Ssc1 signal: TD1 */
#define PIO_PB3B_TF1         (1u << 3)  /**< \brief Ssc1 signal: TF1 */
#define PIO_PB2B_TK1         (1u << 2)  /**< \brief Ssc1 signal: TK1 */
/* ========== Pio definition for TC0 peripheral ========== */
#define PIO_PD7B_TCLK0       (1u << 7)  /**< \brief Tc0 signal: TCLK0 */
#define PIO_PC14B_TCLK1      (1u << 14) /**< \brief Tc0 signal: TCLK1 */
#define PIO_PE29B_TCLK2      (1u << 29) /**< \brief Tc0 signal: TCLK2 */
#define PIO_PD5B_TIOA0       (1u << 5)  /**< \brief Tc0 signal: TIOA0 */
#define PIO_PC12B_TIOA1      (1u << 12) /**< \brief Tc0 signal: TIOA1 */
#define PIO_PE27B_TIOA2      (1u << 27) /**< \brief Tc0 signal: TIOA2 */
#define PIO_PD6B_TIOB0       (1u << 6)  /**< \brief Tc0 signal: TIOB0 */
#define PIO_PC13B_TIOB1      (1u << 13) /**< \brief Tc0 signal: TIOB1 */
#define PIO_PE28B_TIOB2      (1u << 28) /**< \brief Tc0 signal: TIOB2 */
/* ========== Pio definition for TC1 peripheral ========== */
#define PIO_PC2B_TCLK3       (1u << 2)  /**< \brief Tc1 signal: TCLK3 */
#define PIO_PC5B_TCLK4       (1u << 5)  /**< \brief Tc1 signal: TCLK4 */
#define PIO_PC8B_TCLK5       (1u << 8)  /**< \brief Tc1 signal: TCLK5 */
#define PIO_PC0B_TIOA3       (1u << 0)  /**< \brief Tc1 signal: TIOA3 */
#define PIO_PC3B_TIOA4       (1u << 3)  /**< \brief Tc1 signal: TIOA4 */
#define PIO_PC6B_TIOA5       (1u << 6)  /**< \brief Tc1 signal: TIOA5 */
#define PIO_PC1B_TIOB3       (1u << 1)  /**< \brief Tc1 signal: TIOB3 */
#define PIO_PC4B_TIOB4       (1u << 4)  /**< \brief Tc1 signal: TIOB4 */
#define PIO_PC7B_TIOB5       (1u << 7)  /**< \brief Tc1 signal: TIOB5 */
/* ========== Pio definition for TWI0 peripheral ========== */
#define PIO_PA31A_TWCK0      (1u << 31) /**< \brief Twi0 signal: TWCK0 */
#define PIO_PA30A_TWD0       (1u << 30) /**< \brief Twi0 signal: TWD0 */
/* ========== Pio definition for TWI1 peripheral ========== */
#define PIO_PC27B_TWCK1      (1u << 27) /**< \brief Twi1 signal: TWCK1 */
#define PIO_PC26B_TWD1       (1u << 26) /**< \brief Twi1 signal: TWD1 */
/* ========== Pio definition for TWI2 peripheral ========== */
#define PIO_PA19B_TWCK2      (1u << 19) /**< \brief Twi2 signal: TWCK2 */
#define PIO_PA18B_TWD2       (1u << 18) /**< \brief Twi2 signal: TWD2 */
/* ========== Pio definition for UART0 peripheral ========== */
#define PIO_PC29A_URXD0      (1u << 29) /**< \brief Uart0 signal: URXD0 */
#define PIO_PC30A_UTXD0      (1u << 30) /**< \brief Uart0 signal: UTXD0 */
/* ========== Pio definition for UART1 peripheral ========== */
#define PIO_PA30B_URXD1      (1u << 30) /**< \brief Uart1 signal: URXD1 */
#define PIO_PA31B_UTXD1      (1u << 31) /**< \brief Uart1 signal: UTXD1 */
/* ========== Pio definition for USART0 peripheral ========== */
#define PIO_PD15A_CTS0       (1u << 15) /**< \brief Usart0 signal: CTS0 */
#define PIO_PD16A_RTS0       (1u << 16) /**< \brief Usart0 signal: RTS0 */
#define PIO_PD17A_RXD0       (1u << 17) /**< \brief Usart0 signal: RXD0 */
#define PIO_PD14A_SCK0       (1u << 14) /**< \brief Usart0 signal: SCK0 */
#define PIO_PD18A_TXD0       (1u << 18) /**< \brief Usart0 signal: TXD0 */
/* ========== Pio definition for USART1 peripheral ========== */
#define PIO_PB26A_CTS1       (1u << 26) /**< \brief Usart1 signal: CTS1 */
#define PIO_PB27A_RTS1       (1u << 27) /**< \brief Usart1 signal: RTS1 */
#define PIO_PB28A_RXD1       (1u << 28) /**< \brief Usart1 signal: RXD1 */
#define PIO_PB25A_SCK1       (1u << 25) /**< \brief Usart1 signal: SCK1 */
#define PIO_PB29A_TXD1       (1u << 29) /**< \brief Usart1 signal: TXD1 */
/* ========== Pio definition for USART2 peripheral ========== */
#define PIO_PE23B_CTS2       (1u << 23) /**< \brief Usart2 signal: CTS2 */
#define PIO_PE24B_RTS2       (1u << 24) /**< \brief Usart2 signal: RTS2 */
#define PIO_PE25B_RXD2       (1u << 25) /**< \brief Usart2 signal: RXD2 */
#define PIO_PE20B_SCK2       (1u << 20) /**< \brief Usart2 signal: SCK2 */
#define PIO_PE26B_TXD2       (1u << 26) /**< \brief Usart2 signal: TXD2 */
/* ========== Pio definition for USART3 peripheral ========== */
#define PIO_PE16B_CTS3       (1u << 16) /**< \brief Usart3 signal: CTS3 */
#define PIO_PE17B_RTS3       (1u << 17) /**< \brief Usart3 signal: RTS3 */
#define PIO_PE18B_RXD3       (1u << 18) /**< \brief Usart3 signal: RXD3 */
#define PIO_PE15B_SCK3       (1u << 15) /**< \brief Usart3 signal: SCK3 */
#define PIO_PE19B_TXD3       (1u << 19) /**< \brief Usart3 signal: TXD3 */
/* ========== Pio indexes ========== */
#define PIO_PA0_IDX          0
#define PIO_PA1_IDX          1
#define PIO_PA2_IDX          2
#define PIO_PA3_IDX          3
#define PIO_PA4_IDX          4
#define PIO_PA5_IDX          5
#define PIO_PA6_IDX          6
#define PIO_PA7_IDX          7
#define PIO_PA8_IDX          8
#define PIO_PA9_IDX          9
#define PIO_PA10_IDX         10
#define PIO_PA11_IDX         11
#define PIO_PA12_IDX         12
#define PIO_PA13_IDX         13
#define PIO_PA14_IDX         14
#define PIO_PA15_IDX         15
#define PIO_PA16_IDX         16
#define PIO_PA17_IDX         17
#define PIO_PA18_IDX         18
#define PIO_PA19_IDX         19
#define PIO_PA20_IDX         20
#define PIO_PA21_IDX         21
#define PIO_PA22_IDX         22
#define PIO_PA23_IDX         23
#define PIO_PA24_IDX         24
#define PIO_PA25_IDX         25
#define PIO_PA26_IDX         26
#define PIO_PA27_IDX         27
#define PIO_PA28_IDX         28
#define PIO_PA29_IDX         29
#define PIO_PA30_IDX         30
#define PIO_PA31_IDX         31
#define PIO_PB0_IDX          32
#define PIO_PB1_IDX          33
#define PIO_PB2_IDX          34
#define PIO_PB3_IDX          35
#define PIO_PB4_IDX          36
#define PIO_PB5_IDX          37
#define PIO_PB6_IDX          38
#define PIO_PB7_IDX          39
#define PIO_PB8_IDX          40
#define PIO_PB9_IDX          41
#define PIO_PB10_IDX         42
#define PIO_PB11_IDX         43
#define PIO_PB12_IDX         44
#define PIO_PB13_IDX         45
#define PIO_PB14_IDX         46
#define PIO_PB15_IDX         47
#define PIO_PB16_IDX         48
#define PIO_PB17_IDX         49
#define PIO_PB18_IDX         50
#define PIO_PB19_IDX         51
#define PIO_PB20_IDX         52
#define PIO_PB21_IDX         53
#define PIO_PB22_IDX         54
#define PIO_PB23_IDX         55
#define PIO_PB24_IDX         56
#define PIO_PB25_IDX         57
#define PIO_PB26_IDX         58
#define PIO_PB27_IDX         59
#define PIO_PB28_IDX         60
#define PIO_PB29_IDX         61
#define PIO_PB30_IDX         62
#define PIO_PB31_IDX         63
#define PIO_PC0_IDX          64
#define PIO_PC1_IDX          65
#define PIO_PC2_IDX          66
#define PIO_PC3_IDX          67
#define PIO_PC4_IDX          68
#define PIO_PC5_IDX          69
#define PIO_PC6_IDX          70
#define PIO_PC7_IDX          71
#define PIO_PC8_IDX          72
#define PIO_PC9_IDX          73
#define PIO_PC10_IDX         74
#define PIO_PC11_IDX         75
#define PIO_PC12_IDX         76
#define PIO_PC13_IDX         77
#define PIO_PC14_IDX         78
#define PIO_PC15_IDX         79
#define PIO_PC16_IDX         80
#define PIO_PC17_IDX         81
#define PIO_PC18_IDX         82
#define PIO_PC19_IDX         83
#define PIO_PC20_IDX         84
#define PIO_PC21_IDX         85
#define PIO_PC22_IDX         86
#define PIO_PC23_IDX         87
#define PIO_PC24_IDX         88
#define PIO_PC25_IDX         89
#define PIO_PC26_IDX         90
#define PIO_PC27_IDX         91
#define PIO_PC28_IDX         92
#define PIO_PC29_IDX         93
#define PIO_PC30_IDX         94
#define PIO_PC31_IDX         95
#define PIO_PD0_IDX          96
#define PIO_PD1_IDX          97
#define PIO_PD2_IDX          98
#define PIO_PD3_IDX          99
#define PIO_PD4_IDX          100
#define PIO_PD5_IDX          101
#define PIO_PD6_IDX          102
#define PIO_PD7_IDX          103
#define PIO_PD8_IDX          104
#define PIO_PD9_IDX          105
#define PIO_PD10_IDX         106
#define PIO_PD11_IDX         107
#define PIO_PD12_IDX         108
#define PIO_PD13_IDX         109
#define PIO_PD14_IDX         110
#define PIO_PD15_IDX         111
#define PIO_PD16_IDX         112
#define PIO_PD17_IDX         113
#define PIO_PD18_IDX         114
#define PIO_PD19_IDX         115
#define PIO_PD20_IDX         116
#define PIO_PD21_IDX         117
#define PIO_PD22_IDX         118
#define PIO_PD23_IDX         119
#define PIO_PD24_IDX         120
#define PIO_PD25_IDX         121
#define PIO_PD26_IDX         122
#define PIO_PD27_IDX         123
#define PIO_PD28_IDX         124
#define PIO_PD29_IDX         125
#define PIO_PD30_IDX         126
#define PIO_PD31_IDX         127
#define PIO_PE0_IDX          128
#define PIO_PE1_IDX          129
#define PIO_PE2_IDX          130
#define PIO_PE3_IDX          131
#define PIO_PE4_IDX          132
#define PIO_PE5_IDX          133
#define PIO_PE6_IDX          134
#define PIO_PE7_IDX          135
#define PIO_PE8_IDX          136
#define PIO_PE9_IDX          137
#define PIO_PE10_IDX         138
#define PIO_PE11_IDX         139
#define PIO_PE12_IDX         140
#define PIO_PE13_IDX         141
#define PIO_PE14_IDX         142
#define PIO_PE15_IDX         143
#define PIO_PE16_IDX         144
#define PIO_PE17_IDX         145
#define PIO_PE18_IDX         146
#define PIO_PE19_IDX         147
#define PIO_PE20_IDX         148
#define PIO_PE21_IDX         149
#define PIO_PE22_IDX         150
#define PIO_PE23_IDX         151
#define PIO_PE24_IDX         152
#define PIO_PE25_IDX         153
#define PIO_PE26_IDX         154
#define PIO_PE27_IDX         155
#define PIO_PE28_IDX         156
#define PIO_PE29_IDX         157
#define PIO_PE30_IDX         158
#define PIO_PE31_IDX         159
/*@}*/

/* ************************************************************************** */
/*   MEMORY MAPPING DEFINITIONS FOR SAMA5D3x */
/* ************************************************************************** */

#define IRAM0_SIZE (0x10000u)
#define IRAM1_SIZE (0x10000u)
#define IROM_SIZE  (0x20000u)
#define IRAM_SIZE  (IRAM0_SIZE+IRAM1_SIZE)

#define EBI_CS0_ADDR   (0x10000000u) /**< EBI Chip Select 0 base address */
#define DDR_CS_ADDR    (0x20000000u) /**< DDR Chip Select base address */
#define EBI_CS1_ADDR   (0x40000000u) /**< EBI Chip Select 1 base address */
#define EBI_CS2_ADDR   (0x50000000u) /**< EBI Chip Select 2 base address */
#define EBI_CS3_ADDR   (0x60000000u) /**< EBI Chip Select 3 base address */
#define EBI_NF_ADDR    (0x60000000u) /**< NAND Flash on EBI Chip Select 3 base address */
#define NFC_ADDR       (0x70000000u) /**< NAND Flash Controller Command base address */
#define IROM_ADDR      (0x00100000u) /**< Internal ROM base address */
#define IRAM0_ADDR     (0x00300000u) /**< Internal RAM 0 base address */
#if defined IRAM0_SIZE
#define IRAM1_ADDR     (IRAM0_ADDR+IRAM0_SIZE) /**< Internal RAM 1 base address */
#endif
#define SMD_ADDR       (0x00400000u) /**< Software Modem Device base address */
#define UDPHS_RAM_ADDR (0x00500000u) /**< USB High Speed Device Port RAM base address */
#define UHP_OHCI_ADDR  (0x00600000u) /**< USB Host Port OHCI base address */
#define UHP_EHCI_ADDR  (0x00700000u) /**< USB Host Port EHCI base address */
#define AXIMX_ADDR     (0x00800000u) /**< AXI Bus Matrix base address */
#define DAP_ADDR       (0x00900000u) /**< Debug Access Port base address */

/* ************************************************************************** */
/*   ELECTRICAL DEFINITIONS FOR SAMA5D3x */
/* ************************************************************************** */

/* %ATMEL_ELECTRICAL% */

#ifdef __cplusplus
}
#endif

/*@}*/

#endif /* _SAMA5D3x_ */

