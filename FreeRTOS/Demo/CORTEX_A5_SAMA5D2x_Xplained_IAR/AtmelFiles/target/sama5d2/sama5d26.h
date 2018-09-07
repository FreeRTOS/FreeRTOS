/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMA5D26_
#define _SAMA5D26_

/** \addtogroup SAMA5D26_definitions SAMA5D26 definitions
  This file defines all structures and symbols for SAMA5D26:
    - registers and bitfields
    - peripheral base address
    - peripheral ID
    - PIO definitions
*/
/*@{*/

#ifdef __cplusplus
 extern "C" {
#endif

#include <stdint.h>

/* ************************************************************************** */
/**  SOFTWARE PERIPHERAL API DEFINITION FOR SAMA5D26 */
/* ************************************************************************** */
/** \addtogroup SAMA5D26_api Peripheral Software API */
/*@{*/

#include "component/component_acc.h"
#include "component/component_adc.h"
#include "component/component_aesb.h"
#include "component/component_aes.h"
#include "component/component_aic.h"
#include "component/component_aximx.h"
#include "component/component_chipid.h"
#include "component/component_classd.h"
#include "component/component_flexcom.h"
#include "component/component_gmac.h"
#include "component/component_i2sc.h"
#include "component/component_icm.h"
#include "component/component_isc.h"
#include "component/component_l2cc.h"
#include "component/component_lcdc.h"
#include "component/component_matrix.h"
#include "component/component_mpddrc.h"
#include "component/component_pdmic.h"
#include "component/component_pio.h"
#include "component/component_pit.h"
#include "component/component_pmc.h"
#include "component/component_pwm.h"
#include "component/component_qspi.h"
#include "component/component_rstc.h"
#include "component/component_rtc.h"
#include "component/component_rxlp.h"
#include "component/component_sckc.h"
#include "component/component_sdmmc.h"
#include "component/component_sfc.h"
#include "component/component_sfr.h"
#include "component/component_sfrbu.h"
#include "component/component_sha.h"
#include "component/component_shdwc.h"
#include "component/component_smc.h"
#include "component/component_ssc.h"
#include "component/component_tc.h"
#include "component/component_tdes.h"
#include "component/component_trng.h"
#include "component/component_twihs.h"
#include "component/component_uart.h"
#include "component/component_udphs.h"
#include "component/component_wdt.h"
#include "component/component_xdmac.h"
/*@}*/

/* ************************************************************************** */
/*   BASE ADDRESS DEFINITIONS FOR SAMA5D26 */
/* ************************************************************************** */
/** \addtogroup SAMA5D26_base Peripheral Base Address Definitions */
/*@{*/

#define AXIMX    ((Aximx    *)0x00600000U) /**< \brief (AXIMX   ) Base Address */
#define L2CC     ((L2cc     *)0x00A00000U) /**< \brief (L2CC    ) Base Address */
#define SDMMC0   ((Sdmmc    *)0xA0000000U) /**< \brief (SDMMC0  ) Base Address */
#define SDMMC1   ((Sdmmc    *)0xB0000000U) /**< \brief (SDMMC1  ) Base Address */
#define LCDC     ((Lcdc     *)0xF0000000U) /**< \brief (LCDC    ) Base Address */
#define XDMAC1   ((Xdmac    *)0xF0004000U) /**< \brief (XDMAC1  ) Base Address */
#define ISC      ((Isc      *)0xF0008000U) /**< \brief (ISC     ) Base Address */
#define MPDDRC   ((Mpddrc   *)0xF000C000U) /**< \brief (MPDDRC  ) Base Address */
#define XDMAC0   ((Xdmac    *)0xF0010000U) /**< \brief (XDMAC0  ) Base Address */
#define PMC      ((Pmc      *)0xF0014000U) /**< \brief (PMC     ) Base Address */
#define MATRIX0  ((Matrix   *)0xF0018000U) /**< \brief (MATRIX0 ) Base Address */
#define AESB     ((Aesb     *)0xF001C000U) /**< \brief (AESB    ) Base Address */
#define QSPI0    ((Qspi     *)0xF0020000U) /**< \brief (QSPI0   ) Base Address */
#define QSPI1    ((Qspi     *)0xF0024000U) /**< \brief (QSPI1   ) Base Address */
#define SHA      ((Sha      *)0xF0028000U) /**< \brief (SHA     ) Base Address */
#define AES      ((Aes      *)0xF002C000U) /**< \brief (AES     ) Base Address */
#define SPI0     ((Spi      *)0xF8000000U) /**< \brief (SPI0    ) Base Address */
#define SSC0     ((Ssc      *)0xF8004000U) /**< \brief (SSC0    ) Base Address */
#define GMAC0    ((Gmac     *)0xF8008000U) /**< \brief (GMAC0   ) Base Address */
#define TC0      ((Tc       *)0xF800C000U) /**< \brief (TC0     ) Base Address */
#define TC1      ((Tc       *)0xF8010000U) /**< \brief (TC1     ) Base Address */
#define HSMC     ((Smc      *)0xF8014000U) /**< \brief (HSMC    ) Base Address */
#define PDMIC    ((Pdmic    *)0xF8018000U) /**< \brief (PDMIC   ) Base Address */
#define UART0    ((Uart     *)0xF801C000U) /**< \brief (UART0   ) Base Address */
#define UART1    ((Uart     *)0xF8020000U) /**< \brief (UART1   ) Base Address */
#define UART2    ((Uart     *)0xF8024000U) /**< \brief (UART2   ) Base Address */
#define TWIHS0   ((Twihs    *)0xF8028000U) /**< \brief (TWIHS0  ) Base Address */
#define PWM      ((Pwm      *)0xF802C000U) /**< \brief (PWM     ) Base Address */
#define SFR      ((Sfr      *)0xF8030000U) /**< \brief (SFR     ) Base Address */
#define FLEXCOM0 ((Flexcom  *)0xF8034000U) /**< \brief (FLEXCOM0) Base Address */
#define FLEXCOM1 ((Flexcom  *)0xF8038000U) /**< \brief (FLEXCOM1) Base Address */
#define SAIC     ((Aic      *)0xF803C000U) /**< \brief (SAIC    ) Base Address */
#define ICM      ((Icm      *)0xF8040000U) /**< \brief (ICM     ) Base Address */
#define RSTC     ((Rstc     *)0xF8048000U) /**< \brief (RSTC    ) Base Address */
#define SHDWC    ((Shdwc    *)0xF8048010U) /**< \brief (SHDWC   ) Base Address */
#define PIT      ((Pit      *)0xF8048030U) /**< \brief (PIT     ) Base Address */
#define WDT      ((Wdt      *)0xF8048040U) /**< \brief (WDT     ) Base Address */
#define SCKC     ((Sckc     *)0xF8048050U) /**< \brief (SCKC    ) Base Address */
#define RTC      ((Rtc      *)0xF80480B0U) /**< \brief (RTC     ) Base Address */
#define RXLP     ((Rxlp     *)0xF8049000U) /**< \brief (RXLP    ) Base Address */
#define ACC      ((Acc      *)0xF804A000U) /**< \brief (ACC     ) Base Address */
#define SFC      ((Sfc      *)0xF804C000U) /**< \brief (SFC     ) Base Address */
#define I2SC0    ((I2sc     *)0xF8050000U) /**< \brief (I2SC0   ) Base Address */
#define SPI1     ((Spi      *)0xFC000000U) /**< \brief (SPI1    ) Base Address */
#define SSC1     ((Ssc      *)0xFC004000U) /**< \brief (SSC1    ) Base Address */
#define UART3    ((Uart     *)0xFC008000U) /**< \brief (UART3   ) Base Address */
#define UART4    ((Uart     *)0xFC00C000U) /**< \brief (UART4   ) Base Address */
#define FLEXCOM2 ((Flexcom  *)0xFC010000U) /**< \brief (FLEXCOM2) Base Address */
#define FLEXCOM3 ((Flexcom  *)0xFC014000U) /**< \brief (FLEXCOM3) Base Address */
#define FLEXCOM4 ((Flexcom  *)0xFC018000U) /**< \brief (FLEXCOM4) Base Address */
#define TRNG     ((Trng     *)0xFC01C000U) /**< \brief (TRNG    ) Base Address */
#define AIC      ((Aic      *)0xFC020000U) /**< \brief (AIC     ) Base Address */
#define TWIHS1   ((Twihs    *)0xFC028000U) /**< \brief (TWIHS1  ) Base Address */
#define UDPHS    ((Udphs    *)0xFC02C000U) /**< \brief (UDPHS   ) Base Address */
#define ADC      ((Adc      *)0xFC030000U) /**< \brief (ADC     ) Base Address */
#define PIOA     ((Pio      *)0xFC038000U) /**< \brief (PIOA    ) Base Address */
#define MATRIX1  ((Matrix   *)0xFC03C000U) /**< \brief (MATRIX1 ) Base Address */
#define TDES     ((Tdes     *)0xFC044000U) /**< \brief (TDES    ) Base Address */
#define CLASSD   ((Classd   *)0xFC048000U) /**< \brief (CLASSD  ) Base Address */
#define I2SC1    ((I2sc     *)0xFC04C000U) /**< \brief (I2SC1   ) Base Address */
#define SFRBU    ((Sfrbu    *)0xFC05C000U) /**< \brief (SFRBU   ) Base Address */
#define CHIPID   ((Chipid   *)0xFC069000U) /**< \brief (CHIPID  ) Base Address */

/*@}*/

/* ************************************************************************** */
/*   PIO DEFINITIONS FOR SAMA5D26 */
/* ************************************************************************** */
/** \addtogroup SAMA5D26_pio Peripheral Pio Definitions */
/*@{*/

#include "pio/pio_sama5d26.h"

/*@}*/

/* ************************************************************************** */
/*   MEMORY MAPPING DEFINITIONS FOR SAMA5D26 */
/* ************************************************************************** */


#define EBI_CS0_ADDR    (0x10000000u) /**< EBI Chip Select 0 base address */
#define DDR_CS_ADDR     (0x20000000u) /**< DDR Chip Select base address */
#define DDR_AES_CS_ADDR (0x40000000u) /**< DDR with AES Chip Select base address */
#define EBI_CS1_ADDR    (0x60000000u) /**< EBI Chip Select 1 base address */
#define EBI_CS2_ADDR    (0x70000000u) /**< EBI Chip Select 2 base address */
#define EBI_CS3_ADDR    (0x80000000u) /**< EBI Chip Select 3 base address */
#define QSPI_AES0_ADDR  (0x90000000u) /**< QPSI Memory crypted with AES 0 base address */
#define QSPI_AES1_ADDR  (0x98000000u) /**< QPSI Memory crypted with AES 1 base address */
#define SDMMC0_ADDR     (0xA0000000u) /**< SDMMC 0 base address */
#define SDMMC1_ADDR     (0xB0000000u) /**< SDMMC 1 base address */
#define NFC_ADDR        (0xC0000000u) /**< NAND Flash Controller Command base address */
#define QSPIMEM0_ADDR   (0xD0000000u) /**< QSPI Memory 0 base address */
#define QSPIMEM1_ADDR   (0xD8000000u) /**< QSPI Memory 1 base address */
#define IROM_ADDR       (0x00000000u) /**< Internal ROM base address */
#define ECC_ROM_ADDR    (0x00040000u) /**< ECC ROM base address */
#define NFC_RAM_ADDR    (0x00100000u) /**< NAND Flash Controller RAM base address */
#define IRAM0_ADDR      (0x00200000u) /**< Internal RAM 0 base address */
#define IRAM1_ADDR      (0x00220000u) /**< Internal RAM 1 base address */
#define UDPHS_RAM_ADDR  (0x00300000u) /**< USB High Speed Device Port RAM base address */
#define UHPHS_OHCI_ADDR (0x00400000u) /**< USB High Speed Device Port RAM base address */
#define UHPHS_EHCI_ADDR (0x00500000u) /**< USB High Speed Device Port RAM base address */
#define AXIMX_ADDR      (0x00600000u) /**< AXI Bus Matrix base address */
#define DAP_ADDR        (0x00700000u) /**< Debug Access Port base address */
#define PTCMEM_ADDR     (0x00800000u) /**< PTC Memory base address */

/* ************************************************************************** */
/*   MISCELLANEOUS DEFINITIONS FOR SAMA5D26 */
/* ************************************************************************** */

#define CHIP_JTAGID (0x05B3F03FUL)
#define CHIP_CIDR   (0x8A5C08C0UL)
#define CHIP_EXID   (0x00000002UL)

/* ************************************************************************** */
/*   ELECTRICAL DEFINITIONS FOR SAMA5D26 */
/* ************************************************************************** */

/* %ATMEL_ELECTRICAL% */

/* Device characteristics */
#define CHIP_FREQ_SLCK_RC_MIN           (20000UL)
#define CHIP_FREQ_SLCK_RC               (32000UL)
#define CHIP_FREQ_SLCK_RC_MAX           (44000UL)
#define CHIP_FREQ_MAINCK_RC_4MHZ        (4000000UL)
#define CHIP_FREQ_MAINCK_RC_8MHZ        (8000000UL)
#define CHIP_FREQ_MAINCK_RC_12MHZ       (12000000UL)
#define CHIP_FREQ_CPU_MAX               (120000000UL)
#define CHIP_FREQ_XTAL_32K              (32768UL)
#define CHIP_FREQ_XTAL_12M              (12000000UL)

/* Embedded Flash Read Wait State (VDDCORE set at 1.20V) */
#define CHIP_FREQ_FWS_0                 (20000000UL)  /**< \brief Maximum operating frequency when FWS is 0 */
#define CHIP_FREQ_FWS_1                 (40000000UL)  /**< \brief Maximum operating frequency when FWS is 1 */
#define CHIP_FREQ_FWS_2                 (60000000UL)  /**< \brief Maximum operating frequency when FWS is 2 */
#define CHIP_FREQ_FWS_3                 (80000000UL)  /**< \brief Maximum operating frequency when FWS is 3 */
#define CHIP_FREQ_FWS_4                 (100000000UL) /**< \brief Maximum operating frequency when FWS is 4 */
#define CHIP_FREQ_FWS_5                 (123000000UL) /**< \brief Maximum operating frequency when FWS is 5 */

#ifdef __cplusplus
}
#endif

/*@}*/

#endif /* _SAMA5D26_ */
