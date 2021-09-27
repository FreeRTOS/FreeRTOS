/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_scb_nwc_regs.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief SCB registers and associated structures relating to the NWC
 *
 */


#ifndef MSS_DDR_SGMII_MSS_SCB_NWC_REGS_H_
#define MSS_DDR_SGMII_MSS_SCB_NWC_REGS_H_

#include "mpfs_hal/mss_hal.h"


#ifdef __cplusplus
extern "C" {
#endif

#ifndef __I
#define __I  const volatile
#endif
#ifndef __IO
#define __IO volatile
#endif
#ifndef __O
#define __O volatile
#endif

/*------------ NWC PLL definition -----------*/
typedef struct
{
  __IO  uint32_t SOFT_RESET;                            /*!< Offset: 0x0  */
  __IO  uint32_t PLL_CTRL;                              /*!< Offset: 0x4  */
  __IO  uint32_t PLL_REF_FB;                            /*!< Offset: 0x8  */
  __IO  uint32_t PLL_FRACN;                             /*!< Offset: 0xc  */
  __IO  uint32_t PLL_DIV_0_1;                           /*!< Offset: 0x10  */
  __IO  uint32_t PLL_DIV_2_3;                           /*!< Offset: 0x14  */
  __IO  uint32_t PLL_CTRL2;                             /*!< Offset: 0x18  */
  __IO  uint32_t PLL_CAL;                               /*!< Offset: 0x1c  */
  __IO  uint32_t PLL_PHADJ;                             /*!< Offset: 0x20  */
  __IO  uint32_t SSCG_REG_0;                        	/*!< Offset: 0x24  */
  __IO  uint32_t SSCG_REG_1;                            /*!< Offset: 0x28  */
  __IO  uint32_t SSCG_REG_2;                            /*!< Offset: 0x2c  */
  __IO  uint32_t SSCG_REG_3;                            /*!< Offset: 0x30  */
} PLL_TypeDef;

/*------------ NWC PLL MUX definition -----------*/

typedef struct
{
  __IO  uint32_t SOFT_RESET;                                /*!< Offset: 0x0  */
  __IO  uint32_t BCLKMUX;                              		/*!< Offset: 0x4  */
  __IO  uint32_t PLL_CKMUX;                            		/*!< Offset: 0x8  */
  __IO  uint32_t MSSCLKMUX;                             	/*!< Offset: 0xc  */
  __IO  uint32_t SPARE0;                           			/*!< Offset: 0x10  */
  __IO  uint32_t FMETER_ADDR;                           	/*!< Offset: 0x14  */
  __IO  uint32_t FMETER_DATAW;                             	/*!< Offset: 0x18  */
  __IO  uint32_t FMETER_DATAR;                              /*!< Offset: 0x1c  */
  __IO  uint32_t TEST_CTRL;                             	/*!< Offset: 0x20  */
} IOSCB_CFM_MSS;

typedef struct
{
  __IO  uint32_t SOFT_RESET;                                /*!< Offset: 0x0  */
  __IO  uint32_t RFCKMUX;                              		/*!< Offset: 0x4  */
  __IO  uint32_t SGMII_CLKMUX;                            	/*!< Offset: 0x8  */
  __IO  uint32_t SPARE0;                             		/*!< Offset: 0xc  */
  __IO  uint32_t CLK_XCVR;                           		/*!< Offset: 0x10  */
  __IO  uint32_t TEST_CTRL;                           		/*!< Offset: 0x14  */
} IOSCB_CFM_SGMII;


typedef struct
{
  __IO  uint32_t SOFT_RESET_IOCALIB;                                 /*!< Offset: 0x00  */
  __IO  uint32_t IOC_REG0;                                           /*!< Offset: 0x04  */
  __I   uint32_t IOC_REG1;                                           /*!< Offset: 0x08  */
  __I   uint32_t IOC_REG2;                                           /*!< Offset: 0x0c  */
  __I   uint32_t IOC_REG3;                                           /*!< Offset: 0x10  */
  __I   uint32_t IOC_REG4;                                           /*!< Offset: 0x14  */
  __I   uint32_t IOC_REG5;                                           /*!< Offset: 0x18  */
  __IO  uint32_t IOC_REG6;                                           /*!< Offset: 0x1c  */
} IOSCB_IO_CALIB_STRUCT;


#define MSS_SCB_MSS_PLL_BASE         		(0x3E001000U)         /*!< ( MSS_SCB_MSS_PLL_BASE ) Base Address */
#define MSS_SCB_DDR_PLL_BASE         		(0x3E010000U)         /*!< ( MSS_SCB_DDR_PLL_BASE ) Base Address */
#define MSS_SCB_SGMII_PLL_BASE         		(0x3E080000U)         /*!< ( MSS_SCB_SGMII_PLL_BASE ) Base Address */

#define MSS_SCB_MSS_MUX_BASE         		(0x3E002000U)         /*!< ( MSS_SCB_MSS_MUX_BASE ) Base Address */
#define MSS_SCB_SGMII_MUX_BASE         		(0x3E200000U)         /*!< ( MSS_SCB_SGMII_PLL_BASE ) Base Address */

#define IOSCB_IO_CALIB_SGMII_BASE         	(0x3E800000U)         /*!< ( IOSCB_IO_CALIB_SGMII_BASE ) Base Address */
#define IOSCB_IO_CALIB_DDR_BASE         	(0x3E040000U)         /*!< ( IOSCB_IO_CALIB_SGMII_BASE ) Base Address */


extern PLL_TypeDef * const MSS_SCB_MSS_PLL;
extern PLL_TypeDef * const MSS_SCB_DDR_PLL;
extern PLL_TypeDef * const MSS_SCB_SGMII_PLL;
extern IOSCB_CFM_MSS * const MSS_SCB_CFM_MSS_MUX;
extern IOSCB_CFM_SGMII * const MSS_SCB_CFM_SGMII_MUX;
extern IOSCB_IO_CALIB_STRUCT * const IOSCB_IO_CALIB_SGMII;
extern IOSCB_IO_CALIB_STRUCT * const IOSCB_IO_CALIB_DDR;


#ifdef __cplusplus
}
#endif

#endif /* MSS_DDR_SGMII_MSS_SCB_NWC_REGS_H_ */
