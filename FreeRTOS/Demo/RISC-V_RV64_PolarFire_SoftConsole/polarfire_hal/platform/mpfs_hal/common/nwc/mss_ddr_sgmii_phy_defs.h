/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_ddr_sgmii_phy_defs.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief Register bit offsets and masks definitions for MPFS MSS DDR
 * This was generated directly from the RTL
 *
 */

#ifndef MSS_DDR_SGMII_PHY_DEFS_H_
#define MSS_DDR_SGMII_PHY_DEFS_H_


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

/*----------------------------------------------------------------------------*/
/*----------------------------------- DDR -----------------------------------*/
/*----------------------------------------------------------------------------*/


/*============================== CFG_DDR_SGMII_PHY definitions ===========================*/

typedef enum {                                                         /*!< SOFT_RESET_DDR_PHY.PERIPH_DDR_PHY bitfield definition*/
    scb_periph_not_in_soft_reset_ddr_phy = 0,
    scb_periph_reset_ddr_phy = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_PERIPH_DDR_PHY_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DDR_PHY.V_MAP_DDR_PHY bitfield definition*/
    scb_v_regs_not_in_soft_reset_ddr_phy = 0,
    scb_v_regs_reset_ddr_phy = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_V_MAP_DDR_PHY_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DDR_PHY.NV_MAP_DDR_PHY bitfield definition*/
    scb_nv_regs_not_in_soft_reset_ddr_phy = 0,
    scb_nv_regs_reset_ddr_phy = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_NV_MAP_DDR_PHY_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_MAIN_PLL.BLOCKID_MAIN_PLL bitfield definition*/
    block_address_main_pll = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_BLOCKID_MAIN_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_MAIN_PLL.PERIPH_MAIN_PLL bitfield definition*/
    scb_periph_not_in_soft_reset_main_pll = 0,
    scb_periph_reset_main_pll = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_PERIPH_MAIN_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_MAIN_PLL.V_MAP_MAIN_PLL bitfield definition*/
    scb_v_regs_not_in_soft_reset_main_pll = 0,
    scb_v_regs_reset_main_pll = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_V_MAP_MAIN_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_MAIN_PLL.NV_MAP_MAIN_PLL bitfield definition*/
    scb_nv_regs_not_in_soft_reset_main_pll = 0,
    scb_nv_regs_reset_main_pll = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_NV_MAP_MAIN_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOSCB_PLL.BLOCKID_IOSCB_PLL bitfield definition*/
    block_address_ioscb_pll = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_BLOCKID_IOSCB_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOSCB_PLL.PERIPH_IOSCB_PLL bitfield definition*/
    scb_periph_not_in_soft_reset_ioscb_pll = 0,
    scb_periph_reset_ioscb_pll = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_PERIPH_IOSCB_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOSCB_PLL.V_MAP_IOSCB_PLL bitfield definition*/
    scb_v_regs_not_in_soft_reset_ioscb_pll = 0,
    scb_v_regs_reset_ioscb_pll = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_V_MAP_IOSCB_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOSCB_PLL.NV_MAP_IOSCB_PLL bitfield definition*/
    scb_nv_regs_not_in_soft_reset_ioscb_pll = 0,
    scb_nv_regs_reset_ioscb_pll = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_NV_MAP_IOSCB_PLL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_BANK_CTRL.BLOCKID_BANK_CTRL bitfield definition*/
    block_address_bank_ctrl = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_BLOCKID_BANK_CTRL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_BANK_CTRL.PERIPH_BANK_CTRL bitfield definition*/
    scb_periph_not_in_soft_reset_bank_ctrl = 0,
    scb_periph_reset_bank_ctrl = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_PERIPH_BANK_CTRL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_BANK_CTRL.V_MAP_BANK_CTRL bitfield definition*/
    scb_v_regs_not_in_soft_reset_bank_ctrl = 0,
    scb_v_regs_reset_bank_ctrl = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_V_MAP_BANK_CTRL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_BANK_CTRL.NV_MAP_BANK_CTRL bitfield definition*/
    scb_nv_regs_not_in_soft_reset_bank_ctrl = 0,
    scb_nv_regs_reset_bank_ctrl = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_NV_MAP_BANK_CTRL_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOCALIB.BLOCKID_IOCALIB bitfield definition*/
    block_address_iocalib = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_BLOCKID_IOCALIB_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOCALIB.PERIPH_IOCALIB bitfield definition*/
    scb_periph_not_in_soft_reset_iocalib = 0,
    scb_periph_reset_iocalib = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_PERIPH_IOCALIB_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOCALIB.V_MAP_IOCALIB bitfield definition*/
    scb_v_regs_not_in_soft_reset_iocalib = 0,
    scb_v_regs_reset_iocalib = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_V_MAP_IOCALIB_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_IOCALIB.NV_MAP_IOCALIB bitfield definition*/
    scb_nv_regs_not_in_soft_reset_iocalib = 0,
    scb_nv_regs_reset_iocalib = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_NV_MAP_IOCALIB_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_CFM.BLOCKID_CFM bitfield definition*/
    block_address_cfm = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_BLOCKID_CFM_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_CFM.PERIPH_CFM bitfield definition*/
    scb_periph_not_in_soft_reset_cfm = 0,
    scb_periph_reset_cfm = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_PERIPH_CFM_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_CFM.V_MAP_CFM bitfield definition*/
    scb_v_regs_not_in_soft_reset_cfm = 0,
    scb_v_regs_reset_cfm = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_V_MAP_CFM_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_CFM.NV_MAP_CFM bitfield definition*/
    scb_nv_regs_not_in_soft_reset_cfm = 0,
    scb_nv_regs_reset_cfm = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_NV_MAP_CFM_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_DRIVER.BLOCKID_DECODER_DRIVER bitfield definition*/
    block_address_decoder_driver = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_BLOCKID_DECODER_DRIVER_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_DRIVER.PERIPH_DECODER_DRIVER bitfield definition*/
    scb_periph_not_in_soft_reset_decoder_driver = 0,
    scb_periph_reset_decoder_driver = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_PERIPH_DECODER_DRIVER_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_DRIVER.V_MAP_DECODER_DRIVER bitfield definition*/
    scb_v_regs_not_in_soft_reset_decoder_driver = 0,
    scb_v_regs_reset_decoder_driver = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_V_MAP_DECODER_DRIVER_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_DRIVER.NV_MAP_DECODER_DRIVER bitfield definition*/
    scb_nv_regs_not_in_soft_reset_decoder_driver = 0,
    scb_nv_regs_reset_decoder_driver = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_NV_MAP_DECODER_DRIVER_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_ODT.BLOCKID_DECODER_ODT bitfield definition*/
    block_address_decoder_odt = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_BLOCKID_DECODER_ODT_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_ODT.PERIPH_DECODER_ODT bitfield definition*/
    scb_periph_not_in_soft_reset_decoder_odt = 0,
    scb_periph_reset_decoder_odt = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_PERIPH_DECODER_ODT_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_ODT.V_MAP_DECODER_ODT bitfield definition*/
    scb_v_regs_not_in_soft_reset_decoder_odt = 0,
    scb_v_regs_reset_decoder_odt = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_V_MAP_DECODER_ODT_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_ODT.NV_MAP_DECODER_ODT bitfield definition*/
    scb_nv_regs_not_in_soft_reset_decoder_odt = 0,
    scb_nv_regs_reset_decoder_odt = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_NV_MAP_DECODER_ODT_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_IO.BLOCKID_DECODER_IO bitfield definition*/
    block_address_decoder_io = 0
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_BLOCKID_DECODER_IO_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_IO.PERIPH_DECODER_IO bitfield definition*/
    scb_periph_not_in_soft_reset_decoder_io = 0,
    scb_periph_reset_decoder_io = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_PERIPH_DECODER_IO_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_IO.V_MAP_DECODER_IO bitfield definition*/
    scb_v_regs_not_in_soft_reset_decoder_io = 0,
    scb_v_regs_reset_decoder_io = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_V_MAP_DECODER_IO_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_DECODER_IO.NV_MAP_DECODER_IO bitfield definition*/
    scb_nv_regs_not_in_soft_reset_decoder_io = 0,
    scb_nv_regs_reset_decoder_io = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_NV_MAP_DECODER_IO_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_TIP.PERIPH_TIP bitfield definition*/
    scb_periph_not_in_soft_reset_ddr_tip = 0,
    scb_periph_reset_ddr_tip = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_PERIPH_TIP_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_TIP.V_MAP_TIP bitfield definition*/
    scb_v_regs_not_in_soft_reset_ddr_tip = 0,
    scb_v_regs_reset_ddr_tip = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_V_MAP_TIP_TypeDef;

typedef enum {                                                         /*!< SOFT_RESET_TIP.NV_MAP_TIP bitfield definition*/
    scb_nv_regs_not_in_soft_reset_ddr_tip = 0,
    scb_nv_regs_reset_ddr_tip = 1
} CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_NV_MAP_TIP_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_DDR_PHY register definition*/
  __IO  uint32_t                       SOFT_RESET_DDR_PHY;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_NV_MAP_DDR_PHY_TypeDef NV_MAP_DDR_PHY       :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_V_MAP_DDR_PHY_TypeDef V_MAP_DDR_PHY        :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_PERIPH_DDR_PHY_TypeDef PERIPH_DDR_PHY       :1;
    __I   uint32_t                       reserved_02          :7;
    __I   uint32_t                       BLOCKID_DDR_PHY      :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_TypeDef;

typedef union{                                                         /*!< DDRPHY_MODE register definition*/
  __IO  uint32_t                       DDRPHY_MODE;
  struct
  {
    __IO  uint32_t                       DDRMODE              :3;
    __IO  uint32_t                       ECC                  :1;
    __IO  uint32_t                       CRC                  :1;
    __IO  uint32_t                       Bus_width            :3;
    __IO  uint32_t                       DMI_DBI              :1;
    __IO  uint32_t                       DQ_drive             :2;
    __IO  uint32_t                       DQS_drive            :2;
    __IO  uint32_t                       ADD_CMD_drive        :2;
    __IO  uint32_t                       Clock_out_drive      :2;
    __IO  uint32_t                       DQ_termination       :2;
    __IO  uint32_t                       DQS_termination      :2;
    __IO  uint32_t                       ADD_CMD_input_pin_termination :2;
    __IO  uint32_t                       preset_odt_clk       :2;
    __IO  uint32_t                       Power_down           :1;
    __IO  uint32_t                       rank                 :1;
    __IO  uint32_t                       Command_Address_Pipe :2;
    __I   uint32_t                       Reserved             :3;
  } bitfield;
} CFG_DDR_SGMII_PHY_DDRPHY_MODE_TypeDef;

typedef union{                                                         /*!< DDRPHY_STARTUP register definition*/
  __IO  uint32_t                       DDRPHY_STARTUP;
  struct
  {
    __IO  uint32_t                       ADD_CMD_Lockdn       :1;
    __IO  uint32_t                       DATA_Lockdn          :1;
    __IO  uint32_t                       PERSIST_ADD_CMD      :1;
    __IO  uint32_t                       Persist_CLKOUT       :1;
    __IO  uint32_t                       Persist_DATA         :1;
    __I   uint32_t                       reserved             :3;
    __IO  uint32_t                       DYNEN_SCB_PLL0       :1;
    __IO  uint32_t                       DYNEN_SCB_PLL1       :1;
    __IO  uint32_t                       DYNEN_SCB_CFM        :1;
    __IO  uint32_t                       DYNEN_SCB_IO_CALIB   :1;
    __IO  uint32_t                       DYNEN_SCB_BANKCNTL   :1;
    __I   uint32_t                       reserved2            :3;
    __IO  uint32_t                       DYNEN_APB_PLL0       :1;
    __IO  uint32_t                       DYNEN_APB_PLL1       :1;
    __IO  uint32_t                       DYNEN_APB_CFM        :1;
    __IO  uint32_t                       DYNEN_APB_IO_CALIB   :1;
    __IO  uint32_t                       DYNEN_APB_BANKCNTL   :1;
    __IO  uint32_t                       DYNEN_APB_DECODER_PRESETS :1;
    __IO  uint32_t                       reserved3            :10;
  } bitfield;
} CFG_DDR_SGMII_PHY_DDRPHY_STARTUP_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_MAIN_PLL register definition*/
  __IO  uint32_t                       SOFT_RESET_MAIN_PLL;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_NV_MAP_MAIN_PLL_TypeDef NV_MAP_MAIN_PLL      :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_V_MAP_MAIN_PLL_TypeDef V_MAP_MAIN_PLL       :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_PERIPH_MAIN_PLL_TypeDef PERIPH_MAIN_PLL      :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_BLOCKID_MAIN_PLL_TypeDef BLOCKID_MAIN_PLL     :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_TypeDef;

typedef union{                                                         /*!< PLL_CTRL_MAIN register definition*/
  __IO  uint32_t                       PLL_CTRL_MAIN;
  struct
  {
    __IO  uint32_t                       REG_POWERDOWN_B      :1;
    __IO  uint32_t                       REG_RFDIV_EN         :1;
    __IO  uint32_t                       REG_DIVQ0_EN         :1;
    __IO  uint32_t                       REG_DIVQ1_EN         :1;
    __IO  uint32_t                       REG_DIVQ2_EN         :1;
    __IO  uint32_t                       REG_DIVQ3_EN         :1;
    __IO  uint32_t                       REG_RFCLK_SEL        :1;
    __I   uint32_t                       RESETONLOCK          :1;
    __I   uint32_t                       BYPCK_SEL            :4;
    __I   uint32_t                       REG_BYPASS_GO_B      :1;
    __I   uint32_t                       reserve10            :3;
    __I   uint32_t                       REG_BYPASSPRE        :4;
    __I   uint32_t                       REG_BYPASSPOST       :4;
    __IO  uint32_t                       LP_REQUIRES_LOCK     :1;
    __I   uint32_t                       LOCK                 :1;
    __I   uint32_t                       LOCK_INT_EN          :1;
    __I   uint32_t                       UNLOCK_INT_EN        :1;
    __I   uint32_t                       LOCK_INT             :1;
    __I   uint32_t                       UNLOCK_INT           :1;
    __I   uint32_t                       reserve11            :1;
    __I   uint32_t                       LOCK_B               :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CTRL_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_REF_FB_MAIN register definition*/
  __IO  uint32_t                       PLL_REF_FB_MAIN;
  struct
  {
    __I   uint32_t                       FSE_B                :1;
    __I   uint32_t                       FBCK_SEL             :2;
    __I   uint32_t                       FOUTFB_SELMUX_EN     :1;
    __I   uint32_t                       reserve12            :4;
    __IO  uint32_t                       RFDIV                :6;
    __I   uint32_t                       reserve13            :2;
    __I   uint32_t                       reserve14            :12;
    __I   uint32_t                       reserve15            :4;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_REF_FB_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_FRACN_MAIN register definition*/
  __IO   uint32_t                       PLL_FRACN_MAIN;
  struct
  {
    __I   uint32_t                       FRACN_EN             :1;
    __I   uint32_t                       FRACN_DAC_EN         :1;
    __I   uint32_t                       reserve16            :6;
    __I   uint32_t                       reserve17            :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_FRACN_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_DIV_0_1_MAIN register definition*/
  __IO  uint32_t                       PLL_DIV_0_1_MAIN;
  struct
  {
    __I   uint32_t                       VCO0PH_SEL           :3;
    __I   uint32_t                       DIV0_START           :3;
    __I   uint32_t                       reserve18            :2;
    __IO  uint32_t                       POST0DIV             :7;
    __I   uint32_t                       reserve19            :1;
    __I   uint32_t                       VCO1PH_SEL           :3;
    __I   uint32_t                       DIV1_START           :3;
    __I   uint32_t                       reserve20            :2;
    __IO  uint32_t                       POST1DIV             :7;
    __I   uint32_t                       reserve21            :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_DIV_0_1_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_DIV_2_3_MAIN register definition*/
  __IO  uint32_t                       PLL_DIV_2_3_MAIN;
  struct
  {
    __I   uint32_t                       VCO2PH_SEL           :3;
    __I   uint32_t                       DIV2_START           :3;
    __I   uint32_t                       reserve22            :2;
    __IO  uint32_t                       POST2DIV             :7;
    __I   uint32_t                       reserve23            :1;
    __I   uint32_t                       VCO3PH_SEL           :3;
    __I   uint32_t                       DIV3_START           :3;
    __I   uint32_t                       reserve24            :2;
    __IO  uint32_t                       POST3DIV             :7;
    __I   uint32_t                       CKPOST3_SEL          :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_DIV_2_3_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_CTRL2_MAIN register definition*/
  __IO  uint32_t                       PLL_CTRL2_MAIN;
  struct
  {
    __IO  uint32_t                       BWI                  :2;
    __IO  uint32_t                       BWP                  :2;
    __I   uint32_t                       IREF_EN              :1;
    __I   uint32_t                       IREF_TOGGLE          :1;
    __I   uint32_t                       reserve25            :3;
    __I   uint32_t                       LOCKCNT              :4;
    __I   uint32_t                       reserve26            :4;
    __I   uint32_t                       ATEST_EN             :1;
    __I   uint32_t                       ATEST_SEL            :3;
    __I   uint32_t                       reserve27            :11;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CTRL2_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_CAL_MAIN register definition*/
  __I   uint32_t                       PLL_CAL_MAIN;
  struct
  {
    __I   uint32_t                       DSKEWCALCNT          :3;
    __I   uint32_t                       DSKEWCAL_EN          :1;
    __I   uint32_t                       DSKEWCALBYP          :1;
    __I   uint32_t                       reserve28            :3;
    __I   uint32_t                       DSKEWCALIN           :7;
    __I   uint32_t                       reserve29            :1;
    __I   uint32_t                       DSKEWCALOUT          :7;
    __I   uint32_t                       reserve30            :9;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CAL_MAIN_TypeDef;

typedef union{                                                         /*!< PLL_PHADJ_MAIN register definition*/
  __IO  uint32_t                       PLL_PHADJ_MAIN;
  struct
  {
    __I   uint32_t                       PLL_REG_SYNCREFDIV_EN :1;
    __I   uint32_t                       PLL_REG_ENABLE_SYNCREFDIV :1;
    __IO  uint32_t                       REG_OUT0_PHSINIT     :3;
    __IO  uint32_t                       REG_OUT1_PHSINIT     :3;
    __IO  uint32_t                       REG_OUT2_PHSINIT     :3;
    __IO  uint32_t                       REG_OUT3_PHSINIT     :3;
    __IO  uint32_t                       REG_LOADPHS_B        :1;
    __I   uint32_t                       reserve31            :17;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_PHADJ_MAIN_TypeDef;

typedef union{                                                         /*!< SSCG_REG_0_MAIN register definition*/
  __IO   uint32_t                       SSCG_REG_0_MAIN;				/* todo: verify should be r/w, it is not in source file from Duolog */
  struct
  {
    __I   uint32_t                       DIVVAL               :6;
    __I   uint32_t                       FRACIN               :24;
    __I   uint32_t                       reserve00            :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_0_MAIN_TypeDef;

typedef union{                                                         /*!< SSCG_REG_1_MAIN register definition*/
  __I   uint32_t                       SSCG_REG_1_MAIN;
  struct
  {
    __I   uint32_t                       DOWNSPREAD           :1;
    __I   uint32_t                       SSMD                 :5;
    __I   uint32_t                       FRACMOD              :24;
    __I   uint32_t                       reserve01            :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_1_MAIN_TypeDef;

typedef union{                                                         /*!< SSCG_REG_2_MAIN register definition*/
  __IO  uint32_t                       SSCG_REG_2_MAIN;
  struct
  {
    __IO  uint32_t                       INTIN                :12;
    __I   uint32_t                       INTMOD               :12;
    __I   uint32_t                       reserve02            :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_2_MAIN_TypeDef;

typedef union{                                                         /*!< SSCG_REG_3_MAIN register definition*/
  __IO   uint32_t                       SSCG_REG_3_MAIN;  /* todo: verify if should be __IO */
  struct
  {
    __I   uint32_t                       SSE_B                :1;
    __I   uint32_t                       SEL_EXTWAVE          :2;
    __I   uint32_t                       EXT_MAXADDR          :8;
    __I   uint32_t                       TBLADDR              :8;
    __I   uint32_t                       RANDOM_FILTER        :1;
    __I   uint32_t                       RANDOM_SEL           :2;
    __I   uint32_t                       reserve03            :1;
    __I   uint32_t                       reserve04            :9;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_3_MAIN_TypeDef;

typedef union{                                                         /*!< RPC_RESET_MAIN_PLL register definition*/
  __IO  uint32_t                       RPC_RESET_MAIN_PLL;
  struct
  {
    __IO  uint32_t                       soft_reset_periph_MAIN_PLL :1;
    __I   uint32_t                       Reserved             :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_RPC_RESET_MAIN_PLL_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_IOSCB_PLL register definition*/
  __IO  uint32_t                       SOFT_RESET_IOSCB_PLL;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_NV_MAP_IOSCB_PLL_TypeDef NV_MAP_IOSCB_PLL     :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_V_MAP_IOSCB_PLL_TypeDef V_MAP_IOSCB_PLL      :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_PERIPH_IOSCB_PLL_TypeDef PERIPH_IOSCB_PLL     :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_BLOCKID_IOSCB_PLL_TypeDef BLOCKID_IOSCB_PLL    :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_TypeDef;

typedef union{                                                         /*!< PLL_CTRL_IOSCB register definition*/
  __IO  uint32_t                       PLL_CTRL_IOSCB;
  struct
  {
    __IO  uint32_t                       REG_POWERDOWN_B      :1;
    __IO  uint32_t                       REG_RFDIV_EN         :1;
    __IO  uint32_t                       REG_DIVQ0_EN         :1;
    __IO  uint32_t                       REG_DIVQ1_EN         :1;
    __IO  uint32_t                       REG_DIVQ2_EN         :1;
    __IO  uint32_t                       REG_DIVQ3_EN         :1;
    __IO  uint32_t                       REG_RFCLK_SEL        :1;
    __I   uint32_t                       RESETONLOCK          :1;
    __I   uint32_t                       BYPCK_SEL            :4;
    __I   uint32_t                       REG_BYPASS_GO_B      :1;
    __I   uint32_t                       reserve10            :3;
    __I   uint32_t                       REG_BYPASSPRE        :4;
    __I   uint32_t                       REG_BYPASSPOST       :4;
    __IO  uint32_t                       LP_REQUIRES_LOCK     :1;
    __I   uint32_t                       LOCK                 :1;
    __I   uint32_t                       LOCK_INT_EN          :1;
    __I   uint32_t                       UNLOCK_INT_EN        :1;
    __I   uint32_t                       LOCK_INT             :1;
    __I   uint32_t                       UNLOCK_INT           :1;
    __I   uint32_t                       reserve11            :1;
    __I   uint32_t                       LOCK_B               :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CTRL_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_REF_FB_IOSCB register definition*/
  __IO  uint32_t                       PLL_REF_FB_IOSCB;
  struct
  {
    __I   uint32_t                       FSE_B                :1;
    __I   uint32_t                       FBCK_SEL             :2;
    __I   uint32_t                       FOUTFB_SELMUX_EN     :1;
    __I   uint32_t                       reserve12            :4;
    __IO  uint32_t                       RFDIV                :6;
    __I   uint32_t                       reserve13            :2;
    __I   uint32_t                       reserve14            :12;
    __I   uint32_t                       reserve15            :4;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_REF_FB_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_FRACN_IOSCB register definition*/
  __I   uint32_t                       PLL_FRACN_IOSCB;
  struct
  {
    __I   uint32_t                       FRACN_EN             :1;
    __I   uint32_t                       FRACN_DAC_EN         :1;
    __I   uint32_t                       reserve16            :6;
    __I   uint32_t                       reserve17            :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_FRACN_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_DIV_0_1_IOSCB register definition*/
  __IO  uint32_t                       PLL_DIV_0_1_IOSCB;
  struct
  {
    __I   uint32_t                       VCO0PH_SEL           :3;
    __I   uint32_t                       DIV0_START           :3;
    __I   uint32_t                       reserve18            :2;
    __IO  uint32_t                       POST0DIV             :7;
    __I   uint32_t                       reserve19            :1;
    __I   uint32_t                       VCO1PH_SEL           :3;
    __I   uint32_t                       DIV1_START           :3;
    __I   uint32_t                       reserve20            :2;
    __IO  uint32_t                       POST1DIV             :7;
    __I   uint32_t                       reserve21            :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_DIV_0_1_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_DIV_2_3_IOSCB register definition*/
  __IO  uint32_t                       PLL_DIV_2_3_IOSCB;
  struct
  {
    __I   uint32_t                       VCO2PH_SEL           :3;
    __I   uint32_t                       DIV2_START           :3;
    __I   uint32_t                       reserve22            :2;
    __IO  uint32_t                       POST2DIV             :7;
    __I   uint32_t                       reserve23            :1;
    __I   uint32_t                       VCO3PH_SEL           :3;
    __I   uint32_t                       DIV3_START           :3;
    __I   uint32_t                       reserve24            :2;
    __IO  uint32_t                       POST3DIV             :7;
    __I   uint32_t                       CKPOST3_SEL          :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_DIV_2_3_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_CTRL2_IOSCB register definition*/
  __IO  uint32_t                       PLL_CTRL2_IOSCB;
  struct
  {
    __IO  uint32_t                       BWI                  :2;
    __IO  uint32_t                       BWP                  :2;
    __I   uint32_t                       IREF_EN              :1;
    __I   uint32_t                       IREF_TOGGLE          :1;
    __I   uint32_t                       reserve25            :3;
    __I   uint32_t                       LOCKCNT              :4;
    __I   uint32_t                       reserve26            :4;
    __I   uint32_t                       ATEST_EN             :1;
    __I   uint32_t                       ATEST_SEL            :3;
    __I   uint32_t                       reserve27            :11;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CTRL2_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_CAL_IOSCB register definition*/
  __I   uint32_t                       PLL_CAL_IOSCB;
  struct
  {
    __I   uint32_t                       DSKEWCALCNT          :3;
    __I   uint32_t                       DSKEWCAL_EN          :1;
    __I   uint32_t                       DSKEWCALBYP          :1;
    __I   uint32_t                       reserve28            :3;
    __I   uint32_t                       DSKEWCALIN           :7;
    __I   uint32_t                       reserve29            :1;
    __I   uint32_t                       DSKEWCALOUT          :7;
    __I   uint32_t                       reserve30            :9;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CAL_IOSCB_TypeDef;

typedef union{                                                         /*!< PLL_PHADJ_IOSCB register definition*/
  __IO  uint32_t                       PLL_PHADJ_IOSCB;
  struct
  {
    __I   uint32_t                       PLL_REG_SYNCREFDIV_EN :1;
    __I   uint32_t                       PLL_REG_ENABLE_SYNCREFDIV :1;
    __IO  uint32_t                       REG_OUT0_PHSINIT     :3;
    __IO  uint32_t                       REG_OUT1_PHSINIT     :3;
    __IO  uint32_t                       REG_OUT2_PHSINIT     :3;
    __IO  uint32_t                       REG_OUT3_PHSINIT     :3;
    __IO  uint32_t                       REG_LOADPHS_B        :1;
    __I   uint32_t                       reserve31            :17;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_PHADJ_IOSCB_TypeDef;

typedef union{                                                         /*!< SSCG_REG_0_IOSCB register definition*/
  __I   uint32_t                       SSCG_REG_0_IOSCB;
  struct
  {
    __I   uint32_t                       DIVVAL               :6;
    __I   uint32_t                       FRACIN               :24;
    __I   uint32_t                       reserve00            :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_0_IOSCB_TypeDef;

typedef union{                                                         /*!< SSCG_REG_1_IOSCB register definition*/
  __I   uint32_t                       SSCG_REG_1_IOSCB;
  struct
  {
    __I   uint32_t                       DOWNSPREAD           :1;
    __I   uint32_t                       SSMD                 :5;
    __I   uint32_t                       FRACMOD              :24;
    __I   uint32_t                       reserve01            :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_1_IOSCB_TypeDef;

typedef union{                                                         /*!< SSCG_REG_2_IOSCB register definition*/
  __IO  uint32_t                       SSCG_REG_2_IOSCB;
  struct
  {
    __IO  uint32_t                       INTIN                :12;
    __I   uint32_t                       INTMOD               :12;
    __I   uint32_t                       reserve02            :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_2_IOSCB_TypeDef;

typedef union{                                                         /*!< SSCG_REG_3_IOSCB register definition*/
  __I   uint32_t                       SSCG_REG_3_IOSCB;
  struct
  {
    __I   uint32_t                       SSE_B                :1;
    __I   uint32_t                       SEL_EXTWAVE          :2;
    __I   uint32_t                       EXT_MAXADDR          :8;
    __I   uint32_t                       TBLADDR              :8;
    __I   uint32_t                       RANDOM_FILTER        :1;
    __I   uint32_t                       RANDOM_SEL           :2;
    __I   uint32_t                       reserve03            :1;
    __I   uint32_t                       reserve04            :9;
  } bitfield;
} CFG_DDR_SGMII_PHY_SSCG_REG_3_IOSCB_TypeDef;

typedef union{                                                         /*!< RPC_RESET_IOSCB register definition*/
  __IO  uint32_t                       RPC_RESET_IOSCB;
  struct
  {
    __IO  uint32_t                       soft_reset_periph_IOSCB :1;
    __I   uint32_t                       Reserved             :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_RPC_RESET_IOSCB_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_BANK_CTRL register definition*/
  __IO  uint32_t                       SOFT_RESET_BANK_CTRL;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_NV_MAP_BANK_CTRL_TypeDef NV_MAP_BANK_CTRL     :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_V_MAP_BANK_CTRL_TypeDef V_MAP_BANK_CTRL      :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_PERIPH_BANK_CTRL_TypeDef PERIPH_BANK_CTRL     :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_BLOCKID_BANK_CTRL_TypeDef BLOCKID_BANK_CTRL    :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_TypeDef;

typedef union{                                                         /*!< DPC_BITS register definition*/
  __IO  uint32_t                       DPC_BITS;
  struct
  {
    __IO  uint32_t                       dpc_vs               :4;
    __IO  uint32_t                       dpc_vrgen_h          :6;
    __IO  uint32_t                       dpc_vrgen_en_h       :1;
    __IO  uint32_t                       dpc_move_en_h        :1;
    __IO  uint32_t                       dpc_vrgen_v          :6;
    __IO  uint32_t                       dpc_vrgen_en_v       :1;
    __IO  uint32_t                       dpc_move_en_v        :1;
    __I   uint32_t                       reserve01            :12;
  } bitfield;
} CFG_DDR_SGMII_PHY_DPC_BITS_TypeDef;

typedef union{                                                         /*!< BANK_STATUS register definition*/
  __I   uint32_t                       BANK_STATUS;
  struct
  {
    __I   uint32_t                       sro_calib_status_b   :1;
    __I   uint32_t                       sro_ioen_bnk_b       :1;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_BANK_STATUS_TypeDef;

typedef union{                                                         /*!< RPC_RESET_BANK_CTRL register definition*/
  __IO  uint32_t                       RPC_RESET_BANK_CTRL;
  struct
  {
    __IO  uint32_t                       soft_reset_periph_BANK_CTRL :1;
    __I   uint32_t                       Reserved             :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_RPC_RESET_BANK_CTRL_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_IOCALIB register definition*/
  __IO  uint32_t                       SOFT_RESET_IOCALIB;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_NV_MAP_IOCALIB_TypeDef NV_MAP_IOCALIB       :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_V_MAP_IOCALIB_TypeDef V_MAP_IOCALIB        :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_PERIPH_IOCALIB_TypeDef PERIPH_IOCALIB       :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_BLOCKID_IOCALIB_TypeDef BLOCKID_IOCALIB      :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_TypeDef;

typedef union{                                                         /*!< IOC_REG0 register definition*/
  __IO  uint32_t                       IOC_REG0;
  struct
  {
    __IO   uint32_t                      reg_pcode            :6;
    __IO   uint32_t                      reg_ncode            :6;
    __I   uint32_t                       reg_calib_trim       :1;
    __IO  uint32_t                       reg_calib_start      :1;
    __IO  uint32_t                       reg_calib_lock       :1;
    __I   uint32_t                       reg_calib_load       :1;
    __I   uint32_t                       reg_calib_direction  :1;
    __I   uint32_t                       reg_calib_move_pcode :1;
    __I   uint32_t                       reg_calib_move_ncode :1;
    __I   uint32_t                       reserve01            :13;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG0_TypeDef;

typedef union{                                                         /*!< IOC_REG1 register definition*/
  __I   uint32_t                       IOC_REG1;
  struct
  {
    __I   uint32_t                       sro_code_done_p      :1;
    __I   uint32_t                       sro_code_done_n      :1;
    __I   uint32_t                       sro_calib_status     :1;
    __I   uint32_t                       sro_calib_intrpt     :1;
    __I   uint32_t                       sro_ioen_out         :1;
    __I   uint32_t                       sro_power_on         :1;
    __I   uint32_t                       sro_comp_sel         :1;
    __I   uint32_t                       sro_comp_en          :1;
    __I   uint32_t                       reserve02            :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG1_TypeDef;

typedef union{                                                         /*!< IOC_REG2 register definition*/
  __I   uint32_t                       IOC_REG2;
  struct
  {
    __I   uint32_t                       sro_pcode            :7;
    __I   uint32_t                       sro_ncode            :7;
    __I   uint32_t                       sro_ref_pcode        :7;
    __I   uint32_t                       sro_ref_ncode        :7;
    __I   uint32_t                       sro_comp_out         :1;
    __I   uint32_t                       reserve03            :3;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG2_TypeDef;

typedef union{                                                         /*!< IOC_REG3 register definition*/
  __I   uint32_t                       IOC_REG3;
  struct
  {
    __I   uint32_t                       reserve04            :5;
    __I   uint32_t                       reg_calib_poffset    :6;
    __I   uint32_t                       reg_calib_poffset_dir :1;
    __I   uint32_t                       reg_calib_noffset    :6;
    __I   uint32_t                       reg_calib_noffset_dir :1;
    __I   uint32_t                       reg_calib_move_slewr :1;
    __I   uint32_t                       reg_calib_move_slewf :1;
    __I   uint32_t                       reg_calib_roffset_dir :1;
    __I   uint32_t                       reg_calib_foffset_dir :1;
    __I   uint32_t                       reserve05            :9;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG3_TypeDef;

typedef union{                                                         /*!< IOC_REG4 register definition*/
  __I   uint32_t                       IOC_REG4;
  struct
  {
    __I   uint32_t                       reg_roffset          :6;
    __I   uint32_t                       reg_foffset          :6;
    __I   uint32_t                       reg_slewr            :6;
    __I   uint32_t                       reg_slewf            :6;
    __I   uint32_t                       sro_slew_intrpt      :1;
    __I   uint32_t                       sro_slew_status      :1;
    __I   uint32_t                       sro_slew_comp_out    :1;
    __I   uint32_t                       sro_slew_comp_en     :1;
    __I   uint32_t                       sro_slew_comp_sel    :1;
    __I   uint32_t                       sro_slew_ioen_out    :1;
    __I   uint32_t                       sro_slew_power_on    :1;
    __I   uint32_t                       reserve06            :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG4_TypeDef;

typedef union{                                                         /*!< IOC_REG5 register definition*/
  __I   uint32_t                       IOC_REG5;
  struct
  {
    __I   uint32_t                       sro_ref_slewr        :6;
    __I   uint32_t                       sro_ref_slewf        :12;
    __I   uint32_t                       sro_slewr            :6;
    __I   uint32_t                       sro_slewf            :6;
    __I   uint32_t                       reserve07            :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG5_TypeDef;

typedef union{                                                         /*!< IOC_REG6 register definition*/
  __IO  uint32_t                       IOC_REG6;
  struct
  {
    __IO  uint32_t                       reg_calib_reset      :1;
    __IO  uint32_t                       reg_calib_clkdiv     :2;
    __I   uint32_t                       reserve08            :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_IOC_REG6_TypeDef;

typedef union{                                                         /*!< RPC_RESET_IOCALIB register definition*/
  __IO  uint32_t                       RPC_RESET_IOCALIB;
  struct
  {
    __IO  uint32_t                       soft_reset_periph_IOCALIB :1;
    __I   uint32_t                       Reserved             :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_RPC_RESET_IOCALIB_TypeDef;

typedef union{                                                         /*!< rpc_calib register definition*/
  __IO  uint32_t                       rpc_calib;
  struct
  {
    __IO  uint32_t                       start_pvt            :1;
    __IO  uint32_t                       lock_pvt             :1;
    __I   uint32_t                       Reserved             :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc_calib_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_CFM register definition*/
  __IO  uint32_t                       SOFT_RESET_CFM;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_NV_MAP_CFM_TypeDef NV_MAP_CFM           :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_V_MAP_CFM_TypeDef V_MAP_CFM            :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_PERIPH_CFM_TypeDef PERIPH_CFM           :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_BLOCKID_CFM_TypeDef BLOCKID_CFM          :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_TypeDef;

typedef union{                                                         /*!< BCLKMUX register definition*/
  __IO  uint32_t                       BCLKMUX;
  struct
  {
    __IO  uint32_t                       bclk0_sel            :5;
    __IO  uint32_t                       bclk1_sel            :5;
    __IO  uint32_t                       bclk2_sel            :5;
    __IO  uint32_t                       bclk3_sel            :5;
    __IO  uint32_t                       bclk4_sel            :5;
    __IO  uint32_t                       bclk5_sel            :5;
    __I   uint32_t                       reserve0             :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_BCLKMUX_TypeDef;

typedef union{                                                         /*!< PLL_CKMUX register definition*/
  __IO  uint32_t                       PLL_CKMUX;
  struct
  {
    __IO  uint32_t                       clk_in_mac_tsu       :2;
    __IO  uint32_t                       pll0_rfclk0_sel      :2;
    __IO  uint32_t                       pll0_rfclk1_sel      :2;
    __IO  uint32_t                       pll1_rfclk0_sel      :2;
    __IO  uint32_t                       pll1_rfclk1_sel      :2;
    __IO  uint32_t                       pll1_fdr_sel         :5;
    __I   uint32_t                       reserve1             :17;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CKMUX_TypeDef;

typedef union{                                                         /*!< MSSCLKMUX register definition*/
  __IO  uint32_t                       MSSCLKMUX;
  struct
  {
    __IO  uint32_t                       mssclk_mux_sel       :2;
    __IO  uint32_t                       mssclk_mux_md        :2;
    __IO  uint32_t                       clk_standby_sel      :1;
    __I   uint32_t                       reserve2             :27;
  } bitfield;
} CFG_DDR_SGMII_PHY_MSSCLKMUX_TypeDef;

typedef union{                                                         /*!< SPARE0 register definition*/
  __IO  uint32_t                       SPARE0;
  struct
  {
    __IO  uint32_t                       spare0               :32;
  } bitfield;
} CFG_DDR_SGMII_PHY_SPARE0_TypeDef;

typedef union{                                                         /*!< FMETER_ADDR register definition*/
  __I   uint32_t                       FMETER_ADDR;
  struct
  {
    __I   uint32_t                       addr10               :2;
    __I   uint32_t                       addr                 :4;
    __I   uint32_t                       reserve3             :26;
  } bitfield;
} CFG_DDR_SGMII_PHY_FMETER_ADDR_TypeDef;

typedef union{                                                         /*!< FMETER_DATAW register definition*/
  __I   uint32_t                       FMETER_DATAW;
  struct
  {
    __I   uint32_t                       data                 :24;
    __I   uint32_t                       strobe               :1;
    __I   uint32_t                       reserve4             :7;
  } bitfield;
} CFG_DDR_SGMII_PHY_FMETER_DATAW_TypeDef;

typedef union{                                                         /*!< FMETER_DATAR register definition*/
  __I   uint32_t                       FMETER_DATAR;
  struct
  {
    __I   uint32_t                       data                 :24;
    __I   uint32_t                       reserve5             :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_FMETER_DATAR_TypeDef;

typedef union{                                                         /*!< TEST_CTRL register definition*/
  __I   uint32_t                       TEST_CTRL;
  struct
  {
    __I   uint32_t                       atest_en             :1;
    __I   uint32_t                       atest_sel            :5;
    __I   uint32_t                       dtest_en             :1;
    __I   uint32_t                       dtest_sel            :5;
    __I   uint32_t                       reserve6             :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_TEST_CTRL_TypeDef;

typedef union{                                                         /*!< RPC_RESET_CFM register definition*/
  __IO  uint32_t                       RPC_RESET_CFM;
  struct
  {
    __IO  uint32_t                       soft_reset_periph_CFM :1;
    __I   uint32_t                       Reserved             :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_RPC_RESET_CFM_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_DECODER_DRIVER register definition*/
  __IO  uint32_t                       SOFT_RESET_DECODER_DRIVER;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_NV_MAP_DECODER_DRIVER_TypeDef NV_MAP_DECODER_DRIVER :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_V_MAP_DECODER_DRIVER_TypeDef V_MAP_DECODER_DRIVER :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_PERIPH_DECODER_DRIVER_TypeDef PERIPH_DECODER_DRIVER :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_BLOCKID_DECODER_DRIVER_TypeDef BLOCKID_DECODER_DRIVER :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_TypeDef;

typedef union{                                                         /*!< rpc1_DRV register definition*/
  __IO  uint32_t                       rpc1_DRV;
  struct
  {
    __IO  uint32_t                       drv_addcmd           :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc1_DRV_TypeDef;

typedef union{                                                         /*!< rpc2_DRV register definition*/
  __IO  uint32_t                       rpc2_DRV;
  struct
  {
    __IO  uint32_t                       drv_clk              :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc2_DRV_TypeDef;

typedef union{                                                         /*!< rpc3_DRV register definition*/
  __IO  uint32_t                       rpc3_DRV;
  struct
  {
    __IO  uint32_t                       drv_dq               :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc3_DRV_TypeDef;

typedef union{                                                         /*!< rpc4_DRV register definition*/
  __IO  uint32_t                       rpc4_DRV;
  struct
  {
    __IO  uint32_t                       drv_dqs              :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc4_DRV_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_DECODER_ODT register definition*/
  __IO  uint32_t                       SOFT_RESET_DECODER_ODT;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_NV_MAP_DECODER_ODT_TypeDef NV_MAP_DECODER_ODT   :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_V_MAP_DECODER_ODT_TypeDef V_MAP_DECODER_ODT    :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_PERIPH_DECODER_ODT_TypeDef PERIPH_DECODER_ODT   :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_BLOCKID_DECODER_ODT_TypeDef BLOCKID_DECODER_ODT  :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_TypeDef;

typedef union{                                                         /*!< rpc1_ODT register definition*/
  __IO  uint32_t                       rpc1_ODT;
  struct
  {
    __IO  uint32_t                       odt_addcmd           :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc1_ODT_TypeDef;

typedef union{                                                         /*!< rpc2_ODT register definition*/
  __IO  uint32_t                       rpc2_ODT;
  struct
  {
    __IO  uint32_t                       odt_clk              :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc2_ODT_TypeDef;

typedef union{                                                         /*!< rpc3_ODT register definition*/
  __IO  uint32_t                       rpc3_ODT;
  struct
  {
    __IO  uint32_t                       odt_dq               :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc3_ODT_TypeDef;

typedef union{                                                         /*!< rpc4_ODT register definition*/
  __IO  uint32_t                       rpc4_ODT;
  struct
  {
    __IO  uint32_t                       odt_dqs              :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc4_ODT_TypeDef;

typedef union{                                                         /*!< rpc5_ODT register definition*/
  __IO  uint32_t                       rpc5_ODT;
  struct
  {
    __IO  uint32_t                       odt_dyn_sel_addcmd   :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc5_ODT_TypeDef;

typedef union{                                                         /*!< rpc6_ODT register definition*/
  __IO  uint32_t                       rpc6_ODT;
  struct
  {
    __IO  uint32_t                       odt_dyn_sel_data     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc6_ODT_TypeDef;

typedef union{                                                         /*!< rpc7_ODT register definition*/
  __IO  uint32_t                       rpc7_ODT;
  struct
  {
    __IO  uint32_t                       odt_static_addcmd    :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc7_ODT_TypeDef;

typedef union{                                                         /*!< rpc8_ODT register definition*/
  __IO  uint32_t                       rpc8_ODT;
  struct
  {
    __IO  uint32_t                       odt_static_clkn      :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc8_ODT_TypeDef;

typedef union{                                                         /*!< rpc9_ODT register definition*/
  __IO  uint32_t                       rpc9_ODT;
  struct
  {
    __IO  uint32_t                       odt_static_clkp      :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc9_ODT_TypeDef;

typedef union{                                                         /*!< rpc10_ODT register definition*/
  __IO  uint32_t                       rpc10_ODT;
  struct
  {
    __IO  uint32_t                       odt_static_dq        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc10_ODT_TypeDef;

typedef union{                                                         /*!< rpc11_ODT register definition*/
  __IO  uint32_t                       rpc11_ODT;
  struct
  {
    __IO  uint32_t                       odt_static_dqs       :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc11_ODT_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_DECODER_IO register definition*/
  __IO  uint32_t                       SOFT_RESET_DECODER_IO;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_NV_MAP_DECODER_IO_TypeDef NV_MAP_DECODER_IO    :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_V_MAP_DECODER_IO_TypeDef V_MAP_DECODER_IO     :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_PERIPH_DECODER_IO_TypeDef PERIPH_DECODER_IO    :1;
    __I   uint32_t                       reserved_02          :7;
    __I   CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_BLOCKID_DECODER_IO_TypeDef BLOCKID_DECODER_IO   :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_TypeDef;

typedef union{                                                         /*!< ovrt1 register definition*/
  __IO  uint32_t                       ovrt1;
  struct
  {
    __IO  uint32_t                       drv_addcmd0          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt1_TypeDef;

typedef union{                                                         /*!< ovrt2 register definition*/
  __IO  uint32_t                       ovrt2;
  struct
  {
    __IO  uint32_t                       drv_addcmd1          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt2_TypeDef;

typedef union{                                                         /*!< ovrt3 register definition*/
  __IO  uint32_t                       ovrt3;
  struct
  {
    __IO  uint32_t                       drv_addcmd2          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt3_TypeDef;

typedef union{                                                         /*!< ovrt4 register definition*/
  __IO  uint32_t                       ovrt4;
  struct
  {
    __IO  uint32_t                       drv_data0            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt4_TypeDef;

typedef union{                                                         /*!< ovrt5 register definition*/
  __IO  uint32_t                       ovrt5;
  struct
  {
    __IO  uint32_t                       drv_data1            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt5_TypeDef;

typedef union{                                                         /*!< ovrt6 register definition*/
  __IO  uint32_t                       ovrt6;
  struct
  {
    __IO  uint32_t                       drv_data2            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt6_TypeDef;

typedef union{                                                         /*!< ovrt7 register definition*/
  __IO  uint32_t                       ovrt7;
  struct
  {
    __IO  uint32_t                       drv_data3            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt7_TypeDef;

typedef union{                                                         /*!< ovrt8 register definition*/
  __IO  uint32_t                       ovrt8;
  struct
  {
    __IO  uint32_t                       drv_ecc              :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt8_TypeDef;

typedef union{                                                         /*!< ovrt9 register definition*/
  __IO  uint32_t                       ovrt9;
  struct
  {
    __IO  uint32_t                       en_addcmd0           :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt9_TypeDef;

typedef union{                                                         /*!< ovrt10 register definition*/
  __IO  uint32_t                       ovrt10;
  struct
  {
    __IO  uint32_t                       en_addcmd1           :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt10_TypeDef;

typedef union{                                                         /*!< ovrt11 register definition*/
  __IO  uint32_t                       ovrt11;
  struct
  {
    __IO  uint32_t                       en_addcmd2           :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt11_TypeDef;

typedef union{                                                         /*!< ovrt12 register definition*/
  __IO  uint32_t                       ovrt12;
  struct
  {
    __IO  uint32_t                       en_data0             :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt12_TypeDef;

typedef union{                                                         /*!< ovrt13 register definition*/
  __IO  uint32_t                       ovrt13;
  struct
  {
    __IO  uint32_t                       en_data1             :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt13_TypeDef;

typedef union{                                                         /*!< ovrt14 register definition*/
  __IO  uint32_t                       ovrt14;
  struct
  {
    __IO  uint32_t                       en_data2             :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt14_TypeDef;

typedef union{                                                         /*!< ovrt15 register definition*/
  __IO  uint32_t                       ovrt15;
  struct
  {
    __IO  uint32_t                       en_data3             :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt15_TypeDef;

typedef union{                                                         /*!< ovrt16 register definition*/
  __IO  uint32_t                       ovrt16;
  struct
  {
    __IO  uint32_t                       en_ecc               :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_ovrt16_TypeDef;

typedef union{                                                         /*!< rpc17 register definition*/
  __IO  uint32_t                       rpc17;
  struct
  {
    __IO  uint32_t                       bclk_sel_ac          :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc17_TypeDef;

typedef union{                                                         /*!< rpc18 register definition*/
  __IO  uint32_t                       rpc18;
  struct
  {
    __IO  uint32_t                       bclk_sel_addcmd      :9;
    __I   uint32_t                       reserved_01          :23;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc18_TypeDef;

typedef union{                                                         /*!< rpc19 register definition*/
  __IO  uint32_t                       rpc19;
  struct
  {
    __IO  uint32_t                       bclk_sel_clkn        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc19_TypeDef;

typedef union{                                                         /*!< rpc20 register definition*/
  __IO  uint32_t                       rpc20;
  struct
  {
    __IO  uint32_t                       bclk_sel_clkp        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc20_TypeDef;

typedef union{                                                         /*!< rpc21 register definition*/
  __IO  uint32_t                       rpc21;
  struct
  {
    __IO  uint32_t                       bclk_sel_data        :9;
    __I   uint32_t                       reserved_01          :23;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc21_TypeDef;

typedef union{                                                         /*!< rpc22 register definition*/
  __IO  uint32_t                       rpc22;
  struct
  {
    __IO  uint32_t                       bclk_sel_dq          :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc22_TypeDef;

typedef union{                                                         /*!< rpc23 register definition*/
  __IO  uint32_t                       rpc23;
  struct
  {
    __IO  uint32_t                       bclk_sel_dqsn        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc23_TypeDef;

typedef union{                                                         /*!< rpc24 register definition*/
  __IO  uint32_t                       rpc24;
  struct
  {
    __IO  uint32_t                       bclk_sel_dqsp        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc24_TypeDef;

typedef union{                                                         /*!< rpc25 register definition*/
  __IO  uint32_t                       rpc25;
  struct
  {
    __IO  uint32_t                       cdr_md_addcmd        :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc25_TypeDef;

typedef union{                                                         /*!< rpc26 register definition*/
  __IO  uint32_t                       rpc26;
  struct
  {
    __IO  uint32_t                       cdr_md_data          :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc26_TypeDef;

typedef union{                                                         /*!< rpc27 register definition*/
  __IO  uint32_t                       rpc27;
  struct
  {
    __IO  uint32_t                       clk_md_addcmd        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc27_TypeDef;

typedef union{                                                         /*!< rpc28 register definition*/
  __IO  uint32_t                       rpc28;
  struct
  {
    __IO  uint32_t                       clk_sel_addcmd       :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc28_TypeDef;

typedef union{                                                         /*!< rpc29 register definition*/
  __IO  uint32_t                       rpc29;
  struct
  {
    __IO  uint32_t                       clk_sel_data         :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc29_TypeDef;

typedef union{                                                         /*!< rpc30 register definition*/
  __IO  uint32_t                       rpc30;
  struct
  {
    __IO  uint32_t                       code_sel_addcmd      :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc30_TypeDef;

typedef union{                                                         /*!< rpc31 register definition*/
  __IO  uint32_t                       rpc31;
  struct
  {
    __IO  uint32_t                       code_sel_data        :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc31_TypeDef;

typedef union{                                                         /*!< rpc32 register definition*/
  __IO  uint32_t                       rpc32;
  struct
  {
    __IO  uint32_t                       comp_addcmd          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc32_TypeDef;

typedef union{                                                         /*!< rpc33 register definition*/
  __IO  uint32_t                       rpc33;
  struct
  {
    __IO  uint32_t                       comp_clkn            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc33_TypeDef;

typedef union{                                                         /*!< rpc34 register definition*/
  __IO  uint32_t                       rpc34;
  struct
  {
    __IO  uint32_t                       comp_clkp            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc34_TypeDef;

typedef union{                                                         /*!< rpc35 register definition*/
  __IO  uint32_t                       rpc35;
  struct
  {
    __IO  uint32_t                       comp_dq              :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc35_TypeDef;

typedef union{                                                         /*!< rpc36 register definition*/
  __IO  uint32_t                       rpc36;
  struct
  {
    __IO  uint32_t                       comp_dqsn            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc36_TypeDef;

typedef union{                                                         /*!< rpc37 register definition*/
  __IO  uint32_t                       rpc37;
  struct
  {
    __IO  uint32_t                       comp_dqsp            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc37_TypeDef;

typedef union{                                                         /*!< rpc38 register definition*/
  __IO  uint32_t                       rpc38;
  struct
  {
    __IO  uint32_t                       divclk_sel_addcmd    :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc38_TypeDef;

typedef union{                                                         /*!< rpc39 register definition*/
  __IO  uint32_t                       rpc39;
  struct
  {
    __IO  uint32_t                       divclk_sel_data      :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc39_TypeDef;

typedef union{                                                         /*!< rpc40 register definition*/
  __IO  uint32_t                       rpc40;
  struct
  {
    __IO  uint32_t                       div_addcmd           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc40_TypeDef;

typedef union{                                                         /*!< rpc41 register definition*/
  __IO  uint32_t                       rpc41;
  struct
  {
    __IO  uint32_t                       div_data             :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc41_TypeDef;

typedef union{                                                         /*!< rpc42 register definition*/
  __IO  uint32_t                       rpc42;
  struct
  {
    __IO  uint32_t                       dly_md_addcmd        :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc42_TypeDef;

typedef union{                                                         /*!< rpc43 register definition*/
  __IO  uint32_t                       rpc43;
  struct
  {
    __IO  uint32_t                       dly_md_clkn          :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc43_TypeDef;

typedef union{                                                         /*!< rpc44 register definition*/
  __IO  uint32_t                       rpc44;
  struct
  {
    __IO  uint32_t                       dly_md_clkp          :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc44_TypeDef;

typedef union{                                                         /*!< rpc45 register definition*/
  __IO  uint32_t                       rpc45;
  struct
  {
    __IO  uint32_t                       dly_md_dq            :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc45_TypeDef;

typedef union{                                                         /*!< rpc46 register definition*/
  __IO  uint32_t                       rpc46;
  struct
  {
    __IO  uint32_t                       dly_md_dqsn          :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc46_TypeDef;

typedef union{                                                         /*!< rpc47 register definition*/
  __IO  uint32_t                       rpc47;
  struct
  {
    __IO  uint32_t                       dly_md_dqsp          :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc47_TypeDef;

typedef union{                                                         /*!< rpc48 register definition*/
  __IO  uint32_t                       rpc48;
  struct
  {
    __IO  uint32_t                       dqs_md_data          :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc48_TypeDef;

typedef union{                                                         /*!< rpc49 register definition*/
  __IO  uint32_t                       rpc49;
  struct
  {
    __IO  uint32_t                       dynen_addcmd         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc49_TypeDef;

typedef union{                                                         /*!< rpc50 register definition*/
  __IO  uint32_t                       rpc50;
  struct
  {
    __IO  uint32_t                       dynen_data           :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc50_TypeDef;

typedef union{                                                         /*!< rpc51 register definition*/
  __IO  uint32_t                       rpc51;
  struct
  {
    __IO  uint32_t                       dynen_soft_reset_addcmd :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc51_TypeDef;

typedef union{                                                         /*!< rpc52 register definition*/
  __IO  uint32_t                       rpc52;
  struct
  {
    __IO  uint32_t                       dynen_soft_reset_data :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc52_TypeDef;

typedef union{                                                         /*!< rpc53 register definition*/
  __IO  uint32_t                       rpc53;
  struct
  {
    __IO  uint32_t                       edgedet_addcmd       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc53_TypeDef;

typedef union{                                                         /*!< rpc54 register definition*/
  __IO  uint32_t                       rpc54;
  struct
  {
    __IO  uint32_t                       edgedet_clkn         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc54_TypeDef;

typedef union{                                                         /*!< rpc55 register definition*/
  __IO  uint32_t                       rpc55;
  struct
  {
    __IO  uint32_t                       edgedet_clkp         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc55_TypeDef;

typedef union{                                                         /*!< rpc56 register definition*/
  __IO  uint32_t                       rpc56;
  struct
  {
    __IO  uint32_t                       edgedet_dq           :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc56_TypeDef;

typedef union{                                                         /*!< rpc57 register definition*/
  __IO  uint32_t                       rpc57;
  struct
  {
    __IO  uint32_t                       edgedet_dqsn         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc57_TypeDef;

typedef union{                                                         /*!< rpc58 register definition*/
  __IO  uint32_t                       rpc58;
  struct
  {
    __IO  uint32_t                       edgedet_dqsp         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc58_TypeDef;

typedef union{                                                         /*!< rpc59 register definition*/
  __IO  uint32_t                       rpc59;
  struct
  {
    __IO  uint32_t                       eyewidth_addcmd      :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc59_TypeDef;

typedef union{                                                         /*!< rpc60 register definition*/
  __IO  uint32_t                       rpc60;
  struct
  {
    __IO  uint32_t                       eyewidth_clkn        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc60_TypeDef;

typedef union{                                                         /*!< rpc61 register definition*/
  __IO  uint32_t                       rpc61;
  struct
  {
    __IO  uint32_t                       eyewidth_clkp        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc61_TypeDef;

typedef union{                                                         /*!< rpc62 register definition*/
  __IO  uint32_t                       rpc62;
  struct
  {
    __IO  uint32_t                       eyewidth_dq          :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc62_TypeDef;

typedef union{                                                         /*!< rpc63 register definition*/
  __IO  uint32_t                       rpc63;
  struct
  {
    __IO  uint32_t                       eyewidth_dqsn        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc63_TypeDef;

typedef union{                                                         /*!< rpc64 register definition*/
  __IO  uint32_t                       rpc64;
  struct
  {
    __IO  uint32_t                       eyewidth_dqsp        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc64_TypeDef;

typedef union{                                                         /*!< rpc65 register definition*/
  __IO  uint32_t                       rpc65;
  struct
  {
    __IO  uint32_t                       eyewidth_sel_addcmd  :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc65_TypeDef;

typedef union{                                                         /*!< rpc66 register definition*/
  __IO  uint32_t                       rpc66;
  struct
  {
    __IO  uint32_t                       eyewidth_sel_clkn    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc66_TypeDef;

typedef union{                                                         /*!< rpc67 register definition*/
  __IO  uint32_t                       rpc67;
  struct
  {
    __IO  uint32_t                       eyewidth_sel_clkp    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc67_TypeDef;

typedef union{                                                         /*!< rpc68 register definition*/
  __IO  uint32_t                       rpc68;
  struct
  {
    __IO  uint32_t                       eyewidth_sel_dq      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc68_TypeDef;

typedef union{                                                         /*!< rpc69 register definition*/
  __IO  uint32_t                       rpc69;
  struct
  {
    __IO  uint32_t                       eyewidth_sel_dqsn    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc69_TypeDef;

typedef union{                                                         /*!< rpc70 register definition*/
  __IO  uint32_t                       rpc70;
  struct
  {
    __IO  uint32_t                       eyewidth_sel_dqsp    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc70_TypeDef;

typedef union{                                                         /*!< rpc71 register definition*/
  __IO  uint32_t                       rpc71;
  struct
  {
    __IO  uint32_t                       eye_en_addcmd        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc71_TypeDef;

typedef union{                                                         /*!< rpc72 register definition*/
  __IO  uint32_t                       rpc72;
  struct
  {
    __IO  uint32_t                       eye_en_clkn          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc72_TypeDef;

typedef union{                                                         /*!< rpc73 register definition*/
  __IO  uint32_t                       rpc73;
  struct
  {
    __IO  uint32_t                       eye_en_clkp          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc73_TypeDef;

typedef union{                                                         /*!< rpc74 register definition*/
  __IO  uint32_t                       rpc74;
  struct
  {
    __IO  uint32_t                       eye_en_dq            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc74_TypeDef;

typedef union{                                                         /*!< rpc75 register definition*/
  __IO  uint32_t                       rpc75;
  struct
  {
    __IO  uint32_t                       eye_en_dqsn          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc75_TypeDef;

typedef union{                                                         /*!< rpc76 register definition*/
  __IO  uint32_t                       rpc76;
  struct
  {
    __IO  uint32_t                       eye_en_dqsp          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc76_TypeDef;

typedef union{                                                         /*!< rpc77 register definition*/
  __IO  uint32_t                       rpc77;
  struct
  {
    __IO  uint32_t                       eye_sdr_addcmd       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc77_TypeDef;

typedef union{                                                         /*!< rpc78 register definition*/
  __IO  uint32_t                       rpc78;
  struct
  {
    __IO  uint32_t                       eye_sdr_clkn         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc78_TypeDef;

typedef union{                                                         /*!< rpc79 register definition*/
  __IO  uint32_t                       rpc79;
  struct
  {
    __IO  uint32_t                       eye_sdr_clkp         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc79_TypeDef;

typedef union{                                                         /*!< rpc80 register definition*/
  __IO  uint32_t                       rpc80;
  struct
  {
    __IO  uint32_t                       eye_sdr_dq           :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc80_TypeDef;

typedef union{                                                         /*!< rpc81 register definition*/
  __IO  uint32_t                       rpc81;
  struct
  {
    __IO  uint32_t                       eye_sdr_dqsn         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc81_TypeDef;

typedef union{                                                         /*!< rpc82 register definition*/
  __IO  uint32_t                       rpc82;
  struct
  {
    __IO  uint32_t                       eye_sdr_dqsp         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc82_TypeDef;

typedef union{                                                         /*!< rpc83 register definition*/
  __IO  uint32_t                       rpc83;
  struct
  {
    __IO  uint32_t                       fifowe_addcmd        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc83_TypeDef;

typedef union{                                                         /*!< rpc84 register definition*/
  __IO  uint32_t                       rpc84;
  struct
  {
    __IO  uint32_t                       fifowe_clkn          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc84_TypeDef;

typedef union{                                                         /*!< rpc85 register definition*/
  __IO  uint32_t                       rpc85;
  struct
  {
    __IO  uint32_t                       fifowe_clkp          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc85_TypeDef;

typedef union{                                                         /*!< rpc86 register definition*/
  __IO  uint32_t                       rpc86;
  struct
  {
    __IO  uint32_t                       fifowe_dq            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc86_TypeDef;

typedef union{                                                         /*!< rpc87 register definition*/
  __IO  uint32_t                       rpc87;
  struct
  {
    __IO  uint32_t                       fifowe_dqsn          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc87_TypeDef;

typedef union{                                                         /*!< rpc88 register definition*/
  __IO  uint32_t                       rpc88;
  struct
  {
    __IO  uint32_t                       fifowe_dqsp          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc88_TypeDef;

typedef union{                                                         /*!< rpc89 register definition*/
  __IO  uint32_t                       rpc89;
  struct
  {
    __IO  uint32_t                       fifo_en_addcmd       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc89_TypeDef;

typedef union{                                                         /*!< rpc90 register definition*/
  __IO  uint32_t                       rpc90;
  struct
  {
    __IO  uint32_t                       fifo_en_data         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc90_TypeDef;

typedef union{                                                         /*!< rpc91 register definition*/
  __IO  uint32_t                       rpc91;
  struct
  {
    __IO  uint32_t                       fifo_run_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc91_TypeDef;

typedef union{                                                         /*!< rpc92 register definition*/
  __IO  uint32_t                       rpc92;
  struct
  {
    __IO  uint32_t                       fifo_run_data        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc92_TypeDef;

typedef union{                                                         /*!< rpc93 register definition*/
  __IO  uint32_t                       rpc93;
  struct
  {
    __IO  uint32_t                       gsr_disable_addcmd   :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc93_TypeDef;

typedef union{                                                         /*!< rpc94 register definition*/
  __IO  uint32_t                       rpc94;
  struct
  {
    __IO  uint32_t                       gsr_disable_data     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc94_TypeDef;

typedef union{                                                         /*!< rpc95 register definition*/
  __IO  uint32_t                       rpc95;
  struct
  {
    __IO  uint32_t                       ibufmd_addcmd        :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc95_TypeDef;

typedef union{                                                         /*!< rpc96 register definition*/
  __IO  uint32_t                       rpc96;
  struct
  {
    __IO  uint32_t                       ibufmd_clk           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc96_TypeDef;

typedef union{                                                         /*!< rpc97 register definition*/
  __IO  uint32_t                       rpc97;
  struct
  {
    __IO  uint32_t                       ibufmd_dq            :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc97_TypeDef;

typedef union{                                                         /*!< rpc98 register definition*/
  __IO  uint32_t                       rpc98;
  struct
  {
    __IO  uint32_t                       ibufmd_dqs           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc98_TypeDef;

typedef union{                                                         /*!< rpc99 register definition*/
  __IO  uint32_t                       rpc99;
  struct
  {
    __IO  uint32_t                       indly_sel_addcmd     :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc99_TypeDef;

typedef union{                                                         /*!< rpc100 register definition*/
  __IO  uint32_t                       rpc100;
  struct
  {
    __IO  uint32_t                       indly_sel_clkn       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc100_TypeDef;

typedef union{                                                         /*!< rpc101 register definition*/
  __IO  uint32_t                       rpc101;
  struct
  {
    __IO  uint32_t                       indly_sel_clkp       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc101_TypeDef;

typedef union{                                                         /*!< rpc102 register definition*/
  __IO  uint32_t                       rpc102;
  struct
  {
    __IO  uint32_t                       indly_sel_dq         :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc102_TypeDef;

typedef union{                                                         /*!< rpc103 register definition*/
  __IO  uint32_t                       rpc103;
  struct
  {
    __IO  uint32_t                       indly_sel_dqsn       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc103_TypeDef;

typedef union{                                                         /*!< rpc104 register definition*/
  __IO  uint32_t                       rpc104;
  struct
  {
    __IO  uint32_t                       indly_sel_dqsp       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc104_TypeDef;

typedef union{                                                         /*!< rpc105 register definition*/
  __IO  uint32_t                       rpc105;
  struct
  {
    __IO  uint32_t                       lane_pvt_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc105_TypeDef;

typedef union{                                                         /*!< rpc106 register definition*/
  __IO  uint32_t                       rpc106;
  struct
  {
    __IO  uint32_t                       lane_pvt_data        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc106_TypeDef;

typedef union{                                                         /*!< rpc107 register definition*/
  __IO  uint32_t                       rpc107;
  struct
  {
    __IO  uint32_t                       lsr_disable_addcmd   :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc107_TypeDef;

typedef union{                                                         /*!< rpc108 register definition*/
  __IO  uint32_t                       rpc108;
  struct
  {
    __IO  uint32_t                       lsr_disable_clkn     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc108_TypeDef;

typedef union{                                                         /*!< rpc109 register definition*/
  __IO  uint32_t                       rpc109;
  struct
  {
    __IO  uint32_t                       lsr_disable_clkp     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc109_TypeDef;

typedef union{                                                         /*!< rpc110 register definition*/
  __IO  uint32_t                       rpc110;
  struct
  {
    __IO  uint32_t                       lsr_disable_dq       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc110_TypeDef;

typedef union{                                                         /*!< rpc111 register definition*/
  __IO  uint32_t                       rpc111;
  struct
  {
    __IO  uint32_t                       lsr_disable_dqsn     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc111_TypeDef;

typedef union{                                                         /*!< rpc112 register definition*/
  __IO  uint32_t                       rpc112;
  struct
  {
    __IO  uint32_t                       lsr_disable_dqsp     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc112_TypeDef;

typedef union{                                                         /*!< rpc113 register definition*/
  __IO  uint32_t                       rpc113;
  struct
  {
    __IO  uint32_t                       mvdly_en_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc113_TypeDef;

typedef union{                                                         /*!< rpc114 register definition*/
  __IO  uint32_t                       rpc114;
  struct
  {
    __IO  uint32_t                       mvdly_en_clkn        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc114_TypeDef;

typedef union{                                                         /*!< rpc115 register definition*/
  __IO  uint32_t                       rpc115;
  struct
  {
    __IO  uint32_t                       mvdly_en_clkp        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc115_TypeDef;

typedef union{                                                         /*!< rpc116 register definition*/
  __IO  uint32_t                       rpc116;
  struct
  {
    __IO  uint32_t                       mvdly_en_dq          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc116_TypeDef;

typedef union{                                                         /*!< rpc117 register definition*/
  __IO  uint32_t                       rpc117;
  struct
  {
    __IO  uint32_t                       mvdly_en_dqsn        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc117_TypeDef;

typedef union{                                                         /*!< rpc118 register definition*/
  __IO  uint32_t                       rpc118;
  struct
  {
    __IO  uint32_t                       mvdly_en_dqsp        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc118_TypeDef;

typedef union{                                                         /*!< rpc119 register definition*/
  __IO  uint32_t                       rpc119;
  struct
  {
    __IO  uint32_t                       oeclk_inv_addcmd     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc119_TypeDef;

typedef union{                                                         /*!< rpc120 register definition*/
  __IO  uint32_t                       rpc120;
  struct
  {
    __IO  uint32_t                       oeclk_inv_clkn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc120_TypeDef;

typedef union{                                                         /*!< rpc121 register definition*/
  __IO  uint32_t                       rpc121;
  struct
  {
    __IO  uint32_t                       oeclk_inv_clkp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc121_TypeDef;

typedef union{                                                         /*!< rpc122 register definition*/
  __IO  uint32_t                       rpc122;
  struct
  {
    __IO  uint32_t                       oeclk_inv_dq         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc122_TypeDef;

typedef union{                                                         /*!< rpc123 register definition*/
  __IO  uint32_t                       rpc123;
  struct
  {
    __IO  uint32_t                       oeclk_inv_dqsn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc123_TypeDef;

typedef union{                                                         /*!< rpc124 register definition*/
  __IO  uint32_t                       rpc124;
  struct
  {
    __IO  uint32_t                       oeclk_inv_dqsp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc124_TypeDef;

typedef union{                                                         /*!< rpc125 register definition*/
  __IO  uint32_t                       rpc125;
  struct
  {
    __IO  uint32_t                       oe_md_addcmd         :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc125_TypeDef;

typedef union{                                                         /*!< rpc126 register definition*/
  __IO  uint32_t                       rpc126;
  struct
  {
    __IO  uint32_t                       oe_md_clkn           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc126_TypeDef;

typedef union{                                                         /*!< rpc127 register definition*/
  __IO  uint32_t                       rpc127;
  struct
  {
    __IO  uint32_t                       oe_md_clkp           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc127_TypeDef;

typedef union{                                                         /*!< rpc128 register definition*/
  __IO  uint32_t                       rpc128;
  struct
  {
    __IO  uint32_t                       oe_md_dq             :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc128_TypeDef;

typedef union{                                                         /*!< rpc129 register definition*/
  __IO  uint32_t                       rpc129;
  struct
  {
    __IO  uint32_t                       oe_md_dqsn           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc129_TypeDef;

typedef union{                                                         /*!< rpc130 register definition*/
  __IO  uint32_t                       rpc130;
  struct
  {
    __IO  uint32_t                       oe_md_dqsp           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc130_TypeDef;

typedef union{                                                         /*!< rpc131 register definition*/
  __IO  uint32_t                       rpc131;
  struct
  {
    __IO  uint32_t                       pause_en_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc131_TypeDef;

typedef union{                                                         /*!< rpc132 register definition*/
  __IO  uint32_t                       rpc132;
  struct
  {
    __IO  uint32_t                       pause_en_data        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc132_TypeDef;

typedef union{                                                         /*!< rpc133 register definition*/
  __IO  uint32_t                       rpc133;
  struct
  {
    __IO  uint32_t                       qdr_addcmd           :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc133_TypeDef;

typedef union{                                                         /*!< rpc134 register definition*/
  __IO  uint32_t                       rpc134;
  struct
  {
    __IO  uint32_t                       qdr_data             :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc134_TypeDef;

typedef union{                                                         /*!< rpc135 register definition*/
  __IO  uint32_t                       rpc135;
  struct
  {
    __IO  uint32_t                       qdr_md_addcmd        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc135_TypeDef;

typedef union{                                                         /*!< rpc136 register definition*/
  __IO  uint32_t                       rpc136;
  struct
  {
    __IO  uint32_t                       qdr_md_clkn          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc136_TypeDef;

typedef union{                                                         /*!< rpc137 register definition*/
  __IO  uint32_t                       rpc137;
  struct
  {
    __IO  uint32_t                       qdr_md_clkp          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc137_TypeDef;

typedef union{                                                         /*!< rpc138 register definition*/
  __IO  uint32_t                       rpc138;
  struct
  {
    __IO  uint32_t                       qdr_md_dq            :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc138_TypeDef;

typedef union{                                                         /*!< rpc139 register definition*/
  __IO  uint32_t                       rpc139;
  struct
  {
    __IO  uint32_t                       qdr_md_dqsn          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc139_TypeDef;

typedef union{                                                         /*!< rpc140 register definition*/
  __IO  uint32_t                       rpc140;
  struct
  {
    __IO  uint32_t                       qdr_md_dqsp          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc140_TypeDef;

typedef union{                                                         /*!< rpc141 register definition*/
  __IO  uint32_t                       rpc141;
  struct
  {
    __IO  uint32_t                       rank2_addcmd         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc141_TypeDef;

typedef union{                                                         /*!< rpc142 register definition*/
  __IO  uint32_t                       rpc142;
  struct
  {
    __IO  uint32_t                       rank2_data           :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc142_TypeDef;

typedef union{                                                         /*!< rpc143 register definition*/
  __IO  uint32_t                       rpc143;
  struct
  {
    __IO  uint32_t                       rst_inv_addcmd       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc143_TypeDef;

typedef union{                                                         /*!< rpc144 register definition*/
  __IO  uint32_t                       rpc144;
  struct
  {
    __IO  uint32_t                       rst_inv_data         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc144_TypeDef;

typedef union{                                                         /*!< rpc145 register definition*/
  __IO  uint32_t                       rpc145;
  struct
  {
    __IO  uint32_t                       rxdly_addcmd         :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc145_TypeDef;

typedef union{                                                         /*!< rpc146 register definition*/
  __IO  uint32_t                       rpc146;
  struct
  {
    __IO  uint32_t                       rxdly_clkn           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc146_TypeDef;

typedef union{                                                         /*!< rpc147 register definition*/
  __IO  uint32_t                       rpc147;
  struct
  {
    __IO  uint32_t                       rxdly_clkp           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc147_TypeDef;

typedef union{                                                         /*!< rpc148 register definition*/
  __IO  uint32_t                       rpc148;
  struct
  {
    __IO  uint32_t                       rxdly_dir_addcmd     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc148_TypeDef;

typedef union{                                                         /*!< rpc149 register definition*/
  __IO  uint32_t                       rpc149;
  struct
  {
    __IO  uint32_t                       rxdly_dir_data       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc149_TypeDef;

typedef union{                                                         /*!< rpc150 register definition*/
  __IO  uint32_t                       rpc150;
  struct
  {
    __IO  uint32_t                       rxdly_dq             :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc150_TypeDef;

typedef union{                                                         /*!< rpc151 register definition*/
  __IO  uint32_t                       rpc151;
  struct
  {
    __IO  uint32_t                       rxdly_dqsn           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc151_TypeDef;

typedef union{                                                         /*!< rpc152 register definition*/
  __IO  uint32_t                       rpc152;
  struct
  {
    __IO  uint32_t                       rxdly_dqsp           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc152_TypeDef;

typedef union{                                                         /*!< rpc153 register definition*/
  __IO  uint32_t                       rpc153;
  struct
  {
    __IO  uint32_t                       rxdly_en_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc153_TypeDef;

typedef union{                                                         /*!< rpc154 register definition*/
  __IO  uint32_t                       rpc154;
  struct
  {
    __IO  uint32_t                       rxdly_en_data        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc154_TypeDef;

typedef union{                                                         /*!< rpc155 register definition*/
  __IO  uint32_t                       rpc155;
  struct
  {
    __IO  uint32_t                       rxdly_offset_addcmd  :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc155_TypeDef;

typedef union{                                                         /*!< rpc156 register definition*/
  __IO  uint32_t                       rpc156;
  struct
  {
    __IO  uint32_t                       rxdly_offset_data    :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc156_TypeDef;

typedef union{                                                         /*!< rpc157 register definition*/
  __IO  uint32_t                       rpc157;
  struct
  {
    __IO  uint32_t                       rxdly_wide_addcmd    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc157_TypeDef;

typedef union{                                                         /*!< rpc158 register definition*/
  __IO  uint32_t                       rpc158;
  struct
  {
    __IO  uint32_t                       rxdly_wide_clkn      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc158_TypeDef;

typedef union{                                                         /*!< rpc159 register definition*/
  __IO  uint32_t                       rpc159;
  struct
  {
    __IO  uint32_t                       rxdly_wide_clkp      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc159_TypeDef;

typedef union{                                                         /*!< rpc160 register definition*/
  __IO  uint32_t                       rpc160;
  struct
  {
    __IO  uint32_t                       rxdly_wide_dq        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc160_TypeDef;

typedef union{                                                         /*!< rpc161 register definition*/
  __IO  uint32_t                       rpc161;
  struct
  {
    __IO  uint32_t                       rxdly_wide_dqsn      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc161_TypeDef;

typedef union{                                                         /*!< rpc162 register definition*/
  __IO  uint32_t                       rpc162;
  struct
  {
    __IO  uint32_t                       rxdly_wide_dqsp      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc162_TypeDef;

typedef union{                                                         /*!< rpc163 register definition*/
  __IO  uint32_t                       rpc163;
  struct
  {
    __IO  uint32_t                       rxmvdly_en_addcmd    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc163_TypeDef;

typedef union{                                                         /*!< rpc164 register definition*/
  __IO  uint32_t                       rpc164;
  struct
  {
    __IO  uint32_t                       rxmvdly_en_data      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc164_TypeDef;

typedef union{                                                         /*!< rpc165 register definition*/
  __IO  uint32_t                       rpc165;
  struct
  {
    __IO  uint32_t                       rxptr_addcmd         :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc165_TypeDef;

typedef union{                                                         /*!< rpc166 register definition*/
  __IO  uint32_t                       rpc166;
  struct
  {
    __IO  uint32_t                       rxptr_data           :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc166_TypeDef;

typedef union{                                                         /*!< rpc167 register definition*/
  __IO  uint32_t                       rpc167;
  struct
  {
    __IO  uint32_t                       rx_md_addcmd         :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc167_TypeDef;

typedef union{                                                         /*!< rpc168 register definition*/
  __IO  uint32_t                       rpc168;
  struct
  {
    __IO  uint32_t                       rx_md_clkn           :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc168_TypeDef;

typedef union{                                                         /*!< rpc169 register definition*/
  __IO  uint32_t                       rpc169;
  struct
  {
    __IO  uint32_t                       rx_md_clkp           :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc169_TypeDef;

typedef union{                                                         /*!< rpc170 register definition*/
  __IO  uint32_t                       rpc170;
  struct
  {
    __IO  uint32_t                       rx_md_dq             :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc170_TypeDef;

typedef union{                                                         /*!< rpc171 register definition*/
  __IO  uint32_t                       rpc171;
  struct
  {
    __IO  uint32_t                       rx_md_dqsn           :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc171_TypeDef;

typedef union{                                                         /*!< rpc172 register definition*/
  __IO  uint32_t                       rpc172;
  struct
  {
    __IO  uint32_t                       rx_md_dqsp           :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc172_TypeDef;

typedef union{                                                         /*!< rpc173 register definition*/
  __IO  uint32_t                       rpc173;
  struct
  {
    __IO  uint32_t                       sclk0_en_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc173_TypeDef;

typedef union{                                                         /*!< rpc174 register definition*/
  __IO  uint32_t                       rpc174;
  struct
  {
    __IO  uint32_t                       sclk0_en_clkn        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc174_TypeDef;

typedef union{                                                         /*!< rpc175 register definition*/
  __IO  uint32_t                       rpc175;
  struct
  {
    __IO  uint32_t                       sclk0_en_clkp        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc175_TypeDef;

typedef union{                                                         /*!< rpc176 register definition*/
  __IO  uint32_t                       rpc176;
  struct
  {
    __IO  uint32_t                       sclk0_en_dq          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc176_TypeDef;

typedef union{                                                         /*!< rpc177 register definition*/
  __IO  uint32_t                       rpc177;
  struct
  {
    __IO  uint32_t                       sclk0_en_dqsn        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc177_TypeDef;

typedef union{                                                         /*!< rpc178 register definition*/
  __IO  uint32_t                       rpc178;
  struct
  {
    __IO  uint32_t                       sclk0_en_dqsp        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc178_TypeDef;

typedef union{                                                         /*!< rpc179 register definition*/
  __IO  uint32_t                       rpc179;
  struct
  {
    __IO  uint32_t                       sclk0_inv_addcmd     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc179_TypeDef;

typedef union{                                                         /*!< rpc180 register definition*/
  __IO  uint32_t                       rpc180;
  struct
  {
    __IO  uint32_t                       sclk0_inv_clkn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc180_TypeDef;

typedef union{                                                         /*!< rpc181 register definition*/
  __IO  uint32_t                       rpc181;
  struct
  {
    __IO  uint32_t                       sclk0_inv_clkp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc181_TypeDef;

typedef union{                                                         /*!< rpc182 register definition*/
  __IO  uint32_t                       rpc182;
  struct
  {
    __IO  uint32_t                       sclk0_inv_dq         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc182_TypeDef;

typedef union{                                                         /*!< rpc183 register definition*/
  __IO  uint32_t                       rpc183;
  struct
  {
    __IO  uint32_t                       sclk0_inv_dqsn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc183_TypeDef;

typedef union{                                                         /*!< rpc184 register definition*/
  __IO  uint32_t                       rpc184;
  struct
  {
    __IO  uint32_t                       sclk0_inv_dqsp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc184_TypeDef;

typedef union{                                                         /*!< rpc185 register definition*/
  __IO  uint32_t                       rpc185;
  struct
  {
    __IO  uint32_t                       sclk1_en_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc185_TypeDef;

typedef union{                                                         /*!< rpc186 register definition*/
  __IO  uint32_t                       rpc186;
  struct
  {
    __IO  uint32_t                       sclk1_en_clkn        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc186_TypeDef;

typedef union{                                                         /*!< rpc187 register definition*/
  __IO  uint32_t                       rpc187;
  struct
  {
    __IO  uint32_t                       sclk1_en_clkp        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc187_TypeDef;

typedef union{                                                         /*!< rpc188 register definition*/
  __IO  uint32_t                       rpc188;
  struct
  {
    __IO  uint32_t                       sclk1_en_dq          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc188_TypeDef;

typedef union{                                                         /*!< rpc189 register definition*/
  __IO  uint32_t                       rpc189;
  struct
  {
    __IO  uint32_t                       sclk1_en_dqsn        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc189_TypeDef;

typedef union{                                                         /*!< rpc190 register definition*/
  __IO  uint32_t                       rpc190;
  struct
  {
    __IO  uint32_t                       sclk1_en_dqsp        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc190_TypeDef;

typedef union{                                                         /*!< rpc191 register definition*/
  __IO  uint32_t                       rpc191;
  struct
  {
    __IO  uint32_t                       sclk1_inv_addcmd     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc191_TypeDef;

typedef union{                                                         /*!< rpc192 register definition*/
  __IO  uint32_t                       rpc192;
  struct
  {
    __IO  uint32_t                       sclk1_inv_clkn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc192_TypeDef;

typedef union{                                                         /*!< rpc193 register definition*/
  __IO  uint32_t                       rpc193;
  struct
  {
    __IO  uint32_t                       sclk1_inv_clkp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc193_TypeDef;

typedef union{                                                         /*!< rpc194 register definition*/
  __IO  uint32_t                       rpc194;
  struct
  {
    __IO  uint32_t                       sclk1_inv_dq         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc194_TypeDef;

typedef union{                                                         /*!< rpc195 register definition*/
  __IO  uint32_t                       rpc195;
  struct
  {
    __IO  uint32_t                       sclk1_inv_dqsn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc195_TypeDef;

typedef union{                                                         /*!< rpc196 register definition*/
  __IO  uint32_t                       rpc196;
  struct
  {
    __IO  uint32_t                       sclk1_inv_dqsp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc196_TypeDef;

typedef union{                                                         /*!< rpc197 register definition*/
  __IO  uint32_t                       rpc197;
  struct
  {
    __IO  uint32_t                       soft_reset_addcmd    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc197_TypeDef;

typedef union{                                                         /*!< rpc198 register definition*/
  __IO  uint32_t                       rpc198;
  struct
  {
    __IO  uint32_t                       soft_reset_data      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc198_TypeDef;

typedef union{                                                         /*!< rpc199 register definition*/
  __IO  uint32_t                       rpc199;
  struct
  {
    __IO  uint32_t                       spare_iog_addcmd     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc199_TypeDef;

typedef union{                                                         /*!< rpc200 register definition*/
  __IO  uint32_t                       rpc200;
  struct
  {
    __IO  uint32_t                       spare_iog_clkn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc200_TypeDef;

typedef union{                                                         /*!< rpc201 register definition*/
  __IO  uint32_t                       rpc201;
  struct
  {
    __IO  uint32_t                       spare_iog_clkp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc201_TypeDef;

typedef union{                                                         /*!< rpc202 register definition*/
  __IO  uint32_t                       rpc202;
  struct
  {
    __IO  uint32_t                       spare_iog_dq         :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc202_TypeDef;

typedef union{                                                         /*!< rpc203 register definition*/
  __IO  uint32_t                       rpc203;
  struct
  {
    __IO  uint32_t                       spare_iog_dqsn       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc203_TypeDef;

typedef union{                                                         /*!< rpc204 register definition*/
  __IO  uint32_t                       rpc204;
  struct
  {
    __IO  uint32_t                       spare_iog_dqsp       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc204_TypeDef;

typedef union{                                                         /*!< rpc205 register definition*/
  __IO  uint32_t                       rpc205;
  struct
  {
    __IO  uint32_t                       spio_sel_di_dqsn     :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc205_TypeDef;

typedef union{                                                         /*!< rpc206 register definition*/
  __IO  uint32_t                       rpc206;
  struct
  {
    __IO  uint32_t                       spio_sel_di_dqsp     :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc206_TypeDef;

typedef union{                                                         /*!< rpc207 register definition*/
  __IO  uint32_t                       rpc207;
  struct
  {
    __IO  uint32_t                       stop_sel_addcmd      :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc207_TypeDef;

typedef union{                                                         /*!< rpc208 register definition*/
  __IO  uint32_t                       rpc208;
  struct
  {
    __IO  uint32_t                       stop_sel_data        :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc208_TypeDef;

typedef union{                                                         /*!< rpc209 register definition*/
  __IO  uint32_t                       rpc209;
  struct
  {
    __IO  uint32_t                       txclk_sel_addcmd     :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc209_TypeDef;

typedef union{                                                         /*!< rpc210 register definition*/
  __IO  uint32_t                       rpc210;
  struct
  {
    __IO  uint32_t                       txclk_sel_clkn       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc210_TypeDef;

typedef union{                                                         /*!< rpc211 register definition*/
  __IO  uint32_t                       rpc211;
  struct
  {
    __IO  uint32_t                       txclk_sel_clkp       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc211_TypeDef;

typedef union{                                                         /*!< rpc212 register definition*/
  __IO  uint32_t                       rpc212;
  struct
  {
    __IO  uint32_t                       txclk_sel_dq         :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc212_TypeDef;

typedef union{                                                         /*!< rpc213 register definition*/
  __IO  uint32_t                       rpc213;
  struct
  {
    __IO  uint32_t                       txclk_sel_dqsn       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc213_TypeDef;

typedef union{                                                         /*!< rpc214 register definition*/
  __IO  uint32_t                       rpc214;
  struct
  {
    __IO  uint32_t                       txclk_sel_dqsp       :2;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc214_TypeDef;

typedef union{                                                         /*!< rpc215 register definition*/
  __IO  uint32_t                       rpc215;
  struct
  {
    __IO  uint32_t                       txdly_addcmd         :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc215_TypeDef;

typedef union{                                                         /*!< rpc216 register definition*/
  __IO  uint32_t                       rpc216;
  struct
  {
    __IO  uint32_t                       txdly_clkn           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc216_TypeDef;

typedef union{                                                         /*!< rpc217 register definition*/
  __IO  uint32_t                       rpc217;
  struct
  {
    __IO  uint32_t                       txdly_clkp           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc217_TypeDef;

typedef union{                                                         /*!< rpc218 register definition*/
  __IO  uint32_t                       rpc218;
  struct
  {
    __IO  uint32_t                       txdly_dir_addcmd     :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc218_TypeDef;

typedef union{                                                         /*!< rpc219 register definition*/
  __IO  uint32_t                       rpc219;
  struct
  {
    __IO  uint32_t                       txdly_dir_data       :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc219_TypeDef;

typedef union{                                                         /*!< rpc220 register definition*/
  __IO  uint32_t                       rpc220;
  struct
  {
    __IO  uint32_t                       txdly_dq             :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc220_TypeDef;

typedef union{                                                         /*!< rpc221 register definition*/
  __IO  uint32_t                       rpc221;
  struct
  {
    __IO  uint32_t                       txdly_dqsn           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc221_TypeDef;

typedef union{                                                         /*!< rpc222 register definition*/
  __IO  uint32_t                       rpc222;
  struct
  {
    __IO  uint32_t                       txdly_dqsp           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc222_TypeDef;

typedef union{                                                         /*!< rpc223 register definition*/
  __IO  uint32_t                       rpc223;
  struct
  {
    __IO  uint32_t                       txdly_en_addcmd      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc223_TypeDef;

typedef union{                                                         /*!< rpc224 register definition*/
  __IO  uint32_t                       rpc224;
  struct
  {
    __IO  uint32_t                       txdly_en_data        :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc224_TypeDef;

typedef union{                                                         /*!< rpc225 register definition*/
  __IO  uint32_t                       rpc225;
  struct
  {
    __IO  uint32_t                       txdly_offset_addcmd  :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc225_TypeDef;

typedef union{                                                         /*!< rpc226 register definition*/
  __IO  uint32_t                       rpc226;
  struct
  {
    __IO  uint32_t                       txdly_offset_data    :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc226_TypeDef;

typedef union{                                                         /*!< rpc227 register definition*/
  __IO  uint32_t                       rpc227;
  struct
  {
    __IO  uint32_t                       txmvdly_en_addcmd    :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc227_TypeDef;

typedef union{                                                         /*!< rpc228 register definition*/
  __IO  uint32_t                       rpc228;
  struct
  {
    __IO  uint32_t                       txmvdly_en_data      :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc228_TypeDef;

typedef union{                                                         /*!< rpc229 register definition*/
  __IO  uint32_t                       rpc229;
  struct
  {
    __IO  uint32_t                       tx_md_addcmd         :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc229_TypeDef;

typedef union{                                                         /*!< rpc230 register definition*/
  __IO  uint32_t                       rpc230;
  struct
  {
    __IO  uint32_t                       tx_md_clkn           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc230_TypeDef;

typedef union{                                                         /*!< rpc231 register definition*/
  __IO  uint32_t                       rpc231;
  struct
  {
    __IO  uint32_t                       tx_md_clkp           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc231_TypeDef;

typedef union{                                                         /*!< rpc232 register definition*/
  __IO  uint32_t                       rpc232;
  struct
  {
    __IO  uint32_t                       tx_md_dq             :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc232_TypeDef;

typedef union{                                                         /*!< rpc233 register definition*/
  __IO  uint32_t                       rpc233;
  struct
  {
    __IO  uint32_t                       tx_md_dqsn           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc233_TypeDef;

typedef union{                                                         /*!< rpc234 register definition*/
  __IO  uint32_t                       rpc234;
  struct
  {
    __IO  uint32_t                       tx_md_dqsp           :7;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc234_TypeDef;

typedef union{                                                         /*!< rpc235 register definition*/
  __IO  uint32_t                       rpc235;
  struct
  {
    __IO  uint32_t                       wpd_addcmd0          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc235_TypeDef;

typedef union{                                                         /*!< rpc236 register definition*/
  __IO  uint32_t                       rpc236;
  struct
  {
    __IO  uint32_t                       wpd_addcmd1          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc236_TypeDef;

typedef union{                                                         /*!< rpc237 register definition*/
  __IO  uint32_t                       rpc237;
  struct
  {
    __IO  uint32_t                       wpd_addcmd2          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc237_TypeDef;

typedef union{                                                         /*!< rpc238 register definition*/
  __IO  uint32_t                       rpc238;
  struct
  {
    __IO  uint32_t                       wpd_data0            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc238_TypeDef;

typedef union{                                                         /*!< rpc239 register definition*/
  __IO  uint32_t                       rpc239;
  struct
  {
    __IO  uint32_t                       wpd_data1            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc239_TypeDef;

typedef union{                                                         /*!< rpc240 register definition*/
  __IO  uint32_t                       rpc240;
  struct
  {
    __IO  uint32_t                       wpd_data2            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc240_TypeDef;

typedef union{                                                         /*!< rpc241 register definition*/
  __IO  uint32_t                       rpc241;
  struct
  {
    __IO  uint32_t                       wpd_data3            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc241_TypeDef;

typedef union{                                                         /*!< rpc242 register definition*/
  __IO  uint32_t                       rpc242;
  struct
  {
    __IO  uint32_t                       wpd_ecc              :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc242_TypeDef;

typedef union{                                                         /*!< rpc243 register definition*/
  __IO  uint32_t                       rpc243;
  struct
  {
    __IO  uint32_t                       wpu_addcmd0          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc243_TypeDef;

typedef union{                                                         /*!< rpc244 register definition*/
  __IO  uint32_t                       rpc244;
  struct
  {
    __IO  uint32_t                       wpu_addcmd1          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc244_TypeDef;

typedef union{                                                         /*!< rpc245 register definition*/
  __IO  uint32_t                       rpc245;
  struct
  {
    __IO  uint32_t                       wpu_addcmd2          :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc245_TypeDef;

typedef union{                                                         /*!< rpc246 register definition*/
  __IO  uint32_t                       rpc246;
  struct
  {
    __IO  uint32_t                       wpu_data0            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc246_TypeDef;

typedef union{                                                         /*!< rpc247 register definition*/
  __IO  uint32_t                       rpc247;
  struct
  {
    __IO  uint32_t                       wpu_data1            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc247_TypeDef;

typedef union{                                                         /*!< rpc248 register definition*/
  __IO  uint32_t                       rpc248;
  struct
  {
    __IO  uint32_t                       wpu_data2            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc248_TypeDef;

typedef union{                                                         /*!< rpc249 register definition*/
  __IO  uint32_t                       rpc249;
  struct
  {
    __IO  uint32_t                       wpu_data3            :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc249_TypeDef;

typedef union{                                                         /*!< rpc250 register definition*/
  __IO  uint32_t                       rpc250;
  struct
  {
    __IO  uint32_t                       wpu_ecc              :12;
    __I   uint32_t                       reserved_01          :20;
  } bitfield;
} CFG_DDR_SGMII_PHY_rpc250_TypeDef;

typedef union{                                                         /*!< spio251 register definition*/
  __IO  uint32_t                       spio251;
  struct
  {
    __IO  uint32_t                       sel_refclk0          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_spio251_TypeDef;

typedef union{                                                         /*!< spio252 register definition*/
  __IO  uint32_t                       spio252;
  struct
  {
    __IO  uint32_t                       sel_refclk1          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_spio252_TypeDef;

typedef union{                                                         /*!< spio253 register definition*/
  __IO  uint32_t                       spio253;
  struct
  {
    __IO  uint32_t                       sel_refclk2          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_spio253_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_TIP register definition*/
  __IO  uint32_t                       SOFT_RESET_TIP;
  struct
  {
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_NV_MAP_TIP_TypeDef NV_MAP_TIP           :1;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_V_MAP_TIP_TypeDef V_MAP_TIP            :1;
    __I   uint32_t                       reserved_01          :6;
    __O   CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_PERIPH_TIP_TypeDef PERIPH_TIP           :1;
    __I   uint32_t                       reserved_02          :7;
    __I   uint32_t                       BLOCKID_TIP          :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_TypeDef;

typedef union{                                                         /*!< rank_select register definition*/
  __IO  uint32_t                       rank_select;
  struct
  {
    __IO  uint32_t                       rank                 :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_rank_select_TypeDef;

typedef union{                                                         /*!< lane_select register definition*/
  __IO  uint32_t                       lane_select;
  struct
  {
    __IO  uint32_t                       lane                 :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_lane_select_TypeDef;

typedef union{                                                         /*!< training_skip register definition*/
  __IO  uint32_t                       training_skip;
  struct
  {
    __IO  uint32_t                       skip_bclksclk        :1;
    __IO  uint32_t                       skip_addcmd          :1;
    __IO  uint32_t                       skip_wrlvl           :1;
    __IO  uint32_t                       skip_rdgate          :1;
    __IO  uint32_t                       skip_dq_dqs_opt      :1;
    __IO  uint32_t                       skip_write_calibration :1;
    __IO  uint32_t                       skip_vref_mr6        :1;
    __IO  uint32_t                       step7                :1;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_training_skip_TypeDef;

typedef union{                                                         /*!< training_start register definition*/
  __IO  uint32_t                       training_start;
  struct
  {
    __IO  uint32_t                       start                :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_training_start_TypeDef;

typedef union{                                                         /*!< training_status register definition*/
  __I   uint32_t                       training_status;
  struct
  {
    __I   uint32_t                       status               :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_training_status_TypeDef;

typedef union{                                                         /*!< training_reset register definition*/
  __IO  uint32_t                       training_reset;
  struct
  {
    __IO  uint32_t                       reset                :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} CFG_DDR_SGMII_PHY_training_reset_TypeDef;

typedef union{                                                         /*!< gt_err_comb register definition*/
  __I   uint32_t                       gt_err_comb;
  struct
  {
    __I   uint32_t                       error_comb_lanex     :6;
    __I   uint32_t                       reserved_01          :26;
  } bitfield;
} CFG_DDR_SGMII_PHY_gt_err_comb_TypeDef;

typedef union{                                                         /*!< gt_clk_sel register definition*/
  __I   uint32_t                       gt_clk_sel;
  struct
  {
    __I   uint32_t                       clk_sel_lanex_rankx  :3;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} CFG_DDR_SGMII_PHY_gt_clk_sel_TypeDef;

typedef union{                                                         /*!< gt_txdly register definition*/
  __I   uint32_t                       gt_txdly;
  struct
  {
    __I   uint32_t                       txdly0_lanex         :8;
    __I   uint32_t                       txdly1_lanex         :8;
    __I   uint32_t                       txdly2_lanex         :8;
    __I   uint32_t                       txdly3_lanex         :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_gt_txdly_TypeDef;

typedef union{                                                         /*!< gt_steps_180 register definition*/
  __I   uint32_t                       gt_steps_180;
  struct
  {
    __I   uint32_t                       steps_180_lanex_rankx :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_gt_steps_180_TypeDef;

typedef union{                                                         /*!< gt_state register definition*/
  __I   uint32_t                       gt_state;
  struct
  {
    __I   uint32_t                       gt_state_lanex       :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_gt_state_TypeDef;

typedef union{                                                         /*!< wl_delay_0 register definition*/
  __I   uint32_t                       wl_delay_0;
  struct
  {
    __I   uint32_t                       wldelay_lanex_rankx  :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_wl_delay_0_TypeDef;

typedef union{                                                         /*!< dq_dqs_err_done register definition*/
  __I   uint32_t                       dq_dqs_err_done;
  struct
  {
    __I   uint32_t                       dq_dqs_error_done_lanex_rankx :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_dq_dqs_err_done_TypeDef;

typedef union{                                                         /*!< dqdqs_window register definition*/
  __I   uint32_t                       dqdqs_window;
  struct
  {
    __I   uint32_t                       ils_lanex_rankx      :8;
    __I   uint32_t                       irs_lanex_rankx      :8;
    __I   uint32_t                       reserved_01          :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_window_TypeDef;

typedef union{                                                         /*!< dqdqs_state register definition*/
  __I   uint32_t                       dqdqs_state;
  struct
  {
    __I   uint32_t                       state_lanex_rankx    :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_state_TypeDef;

typedef union{                                                         /*!< delta0 register definition*/
  __I   uint32_t                       delta0;
  struct
  {
    __I   uint32_t                       delay0_lanex         :8;
    __I   uint32_t                       delay1_lanex         :8;
    __I   uint32_t                       delay2_lanex         :8;
    __I   uint32_t                       delay3_lanex         :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_delta0_TypeDef;

typedef union{                                                         /*!< delta1 register definition*/
  __I   uint32_t                       delta1;
  struct
  {
    __I   uint32_t                       delay4_lanex         :8;
    __I   uint32_t                       delay5_lanex         :8;
    __I   uint32_t                       delay6_lanex         :8;
    __I   uint32_t                       delay7_lanex         :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_delta1_TypeDef;

typedef union{                                                         /*!< dqdqs_status0 register definition*/
  __I   uint32_t                       dqdqs_status0;
  struct
  {
    __I   uint32_t                       init_dly_lanex       :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status0_TypeDef;

typedef union{                                                         /*!< dqdqs_status1 register definition*/
  __I   uint32_t                       dqdqs_status1;
  struct
  {
    __I   uint32_t                       dqs_dly_lanex_rankx  :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status1_TypeDef;

typedef union{                                                         /*!< dqdqs_status2 register definition*/
  __I   uint32_t                       dqdqs_status2;
  struct
  {
    __I   uint32_t                       bit_width_lanex      :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status2_TypeDef;

typedef union{                                                         /*!< dqdqs_status3 register definition*/
  __I   uint32_t                       dqdqs_status3;
  struct
  {
    __I   uint32_t                       initldqs_2_mid_lanex_rankx :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status3_TypeDef;

typedef union{                                                         /*!< dqdqs_status4 register definition*/
  __I   uint32_t                       dqdqs_status4;
  struct
  {
    __I   uint32_t                       mid_2_initldqs_lanex_rankx :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status4_TypeDef;

typedef union{                                                         /*!< dqdqs_status5 register definition*/
  __I   uint32_t                       dqdqs_status5;
  struct
  {
    __I   uint32_t                       stw_2_initldqs_lanex_rankx :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status5_TypeDef;

typedef union{                                                         /*!< dqdqs_status6 register definition*/
  __I   uint32_t                       dqdqs_status6;
  struct
  {
    __I   uint32_t                       initldqs_2_stw_lanex_rankx :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_status6_TypeDef;

typedef union{                                                         /*!< addcmd_status0 register definition*/
  __I   uint32_t                       addcmd_status0;
  struct
  {
    __I   uint32_t                       delay_vcophs_sel0    :8;
    __I   uint32_t                       delay_vcophs_sel1    :8;
    __I   uint32_t                       delay_vcophs_sel2    :8;
    __I   uint32_t                       delay_vcophs_sel3    :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_addcmd_status0_TypeDef;

typedef union{                                                         /*!< addcmd_status1 register definition*/
  __I   uint32_t                       addcmd_status1;
  struct
  {
    __I   uint32_t                       delay_vcophs_sel4    :8;
    __I   uint32_t                       delay_vcophs_sel5    :8;
    __I   uint32_t                       delay_vcophs_sel6    :8;
    __I   uint32_t                       delay_vcophs_sel7    :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_addcmd_status1_TypeDef;

typedef union{                                                         /*!< addcmd_answer register definition*/
  __I   uint32_t                       addcmd_answer;
  struct
  {
    __I   uint32_t                       vcophs_sel_after_training :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_addcmd_answer_TypeDef;

typedef union{                                                         /*!< bclksclk_answer register definition*/
  __I   uint32_t                       bclksclk_answer;
  struct
  {
    __I   uint32_t                       bclk0_vcophs_sel     :4;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} CFG_DDR_SGMII_PHY_bclksclk_answer_TypeDef;

typedef union{                                                         /*!< dqdqs_wrcalib_offset register definition*/
  __I   uint32_t                       dqdqs_wrcalib_offset;
  struct
  {
    __I   uint32_t                       wrcalib_offset_lanex :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_dqdqs_wrcalib_offset_TypeDef;

typedef union{                                                         /*!< expert_mode_en register definition*/
  __IO  uint32_t                       expert_mode_en;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_en    :1;
    __IO  uint32_t                       dyn_ovr_pllcnt_en    :1;
    __IO  uint32_t                       dyn_ovr_rdgate_en    :1;
    __IO  uint32_t                       dyn_ovr_wrcalib_en   :1;
    __IO  uint32_t                       dyn_ovr_calif_en     :1;
    __IO  uint32_t                       dyn_ovr_dfi_shim_en  :1;
    __I   uint32_t                       reserved_01          :26;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_mode_en_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_move_reg0 register definition*/
  __IO  uint32_t                       expert_dlycnt_move_reg0;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_move0 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_move1 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_move2 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_move3 :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_move_reg0_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_move_reg1 register definition*/
  __IO  uint32_t                       expert_dlycnt_move_reg1;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_move4 :4;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_move0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_move1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_move2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_move3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_move4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_move0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_move1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_move2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_move3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_move4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_move0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_move1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_move2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_move3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_move4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_catrn_move :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_ca_move :1;
    __I   uint32_t                       reserved_01          :11;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_move_reg1_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_direction_reg0 register definition*/
  __IO  uint32_t                       expert_dlycnt_direction_reg0;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_direction0 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_direction1 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_direction2 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_direction3 :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_direction_reg0_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_direction_reg1 register definition*/
  __IO  uint32_t                       expert_dlycnt_direction_reg1;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_direction4 :4;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_direction0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_direction1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_direction2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_direction3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_direction4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_direction0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_direction1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_direction2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_direction3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_direction4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_direction0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_direction1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_direction2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_direction3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_direction4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_catrn_direction :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_ca_direction :1;
    __I   uint32_t                       reserved_01          :11;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_direction_reg1_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_load_reg0 register definition*/
  __IO  uint32_t                       expert_dlycnt_load_reg0;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_load0 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_load1 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_load2 :8;
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_load3 :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_load_reg0_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_load_reg1 register definition*/
  __IO  uint32_t                       expert_dlycnt_load_reg1;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_dq_load4 :4;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_load0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_load1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_load2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_load3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_load4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_load0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_load1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_load2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_load3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw270_load4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_load0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_load1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_load2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_load3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_dqsw_load4 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_catrn_load :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_ca_load :1;
    __I   uint32_t                       reserved_01          :11;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_load_reg1_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_oor_reg0 register definition*/
  __I   uint32_t                       expert_dlycnt_oor_reg0;
  struct
  {
    __I   uint32_t                       dyn_ovr_dlycnt_dq_oor0 :8;
    __I   uint32_t                       dyn_ovr_dlycnt_dq_oor1 :8;
    __I   uint32_t                       dyn_ovr_dlycnt_dq_oor2 :8;
    __I   uint32_t                       dyn_ovr_dlycnt_dq_oor3 :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_oor_reg0_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_oor_reg1 register definition*/
  __I   uint32_t                       expert_dlycnt_oor_reg1;
  struct
  {
    __I   uint32_t                       dyn_ovr_dlycnt_dq_oor4 :4;
    __I   uint32_t                       dyn_ovr_dlycnt_lanectrl_oor0 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_lanectrl_oor1 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_lanectrl_oor2 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_lanectrl_oor3 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_lanectrl_oor4 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw270_oor0 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw270_oor1 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw270_oor2 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw270_oor3 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw270_oor4 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw_oor0 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw_oor1 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw_oor2 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw_oor3 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_dqsw_oor4 :1;
    __I   uint32_t                       dyn_ovr_dlycnt_catrn_oor :1;
    __I   uint32_t                       dyn_ovr_dlycnt_ca_oor :1;
    __I   uint32_t                       reserved_01          :11;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_oor_reg1_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_mv_rd_dly_reg register definition*/
  __IO  uint32_t                       expert_dlycnt_mv_rd_dly_reg;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_mv_rd_dly0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_mv_rd_dly1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_mv_rd_dly2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_mv_rd_dly3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_mv_rd_dly4 :1;
    __I   uint32_t                       reserved_01          :27;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_mv_rd_dly_reg_TypeDef;

typedef union{                                                         /*!< expert_dlycnt_pause register definition*/
  __IO  uint32_t                       expert_dlycnt_pause;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_pause_addcmd :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_pause_data0 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_pause_data1 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_pause_data2 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_pause_data3 :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_lanectrl_pause_data4 :1;
    __I   uint32_t                       reserved_01          :26;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dlycnt_pause_TypeDef;

typedef union{                                                         /*!< expert_pllcnt register definition*/
  __IO  uint32_t                       expert_pllcnt;
  struct
  {
    __IO  uint32_t                       dyn_ovr_dlycnt_rotate :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_direction :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_loadphs_b :1;
    __IO  uint32_t                       dyn_ovr_dlycnt_phsel :4;
    __I   uint32_t                       reserved_01          :25;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_pllcnt_TypeDef;

typedef union{                                                         /*!< expert_dqlane_readback register definition*/
  __I   uint32_t                       expert_dqlane_readback;
  struct
  {
    __I   uint32_t                       dq_or                :5;
    __I   uint32_t                       dq_and               :5;
    __I   uint32_t                       burst_valid          :5;
    __I   uint32_t                       reserved_01          :17;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dqlane_readback_TypeDef;

typedef union{                                                         /*!< expert_addcmd_ln_readback register definition*/
  __I   uint32_t                       expert_addcmd_ln_readback;
  struct
  {
    __I   uint32_t                       rx_refclk            :8;
    __I   uint32_t                       rx_addcmd            :4;
    __I   uint32_t                       rx_bclksclk          :2;
    __I   uint32_t                       reserved_01          :18;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_addcmd_ln_readback_TypeDef;

typedef union{                                                         /*!< expert_read_gate_controls register definition*/
  __IO  uint32_t                       expert_read_gate_controls;
  struct
  {
    __IO  uint32_t                       dyn_ovr_rdgate_clksel :10;
    __IO  uint32_t                       dyn_ovr_rdgate_steps180 :20;
    __I   uint32_t                       reserved_01          :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_read_gate_controls_TypeDef;

typedef union{                                                         /*!< expert_dq_dqs_optimization0 register definition*/
  __I   uint32_t                       expert_dq_dqs_optimization0;
  struct
  {
    __I   uint32_t                       dyn_ovr_dqdqs_data_match_lane0 :8;
    __I   uint32_t                       dyn_ovr_dqdqs_data_match_lane1 :8;
    __I   uint32_t                       dyn_ovr_dqdqs_data_match_lane2 :8;
    __I   uint32_t                       dyn_ovr_dqdqs_data_match_lane3 :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dq_dqs_optimization0_TypeDef;

typedef union{                                                         /*!< expert_dq_dqs_optimization1 register definition*/
  __I   uint32_t                       expert_dq_dqs_optimization1;
  struct
  {
    __I   uint32_t                       dyn_ovr_dqdqs_data_match_lane4 :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dq_dqs_optimization1_TypeDef;

typedef union{                                                         /*!< expert_wrcalib register definition*/
  __IO  uint32_t                       expert_wrcalib;
  struct
  {
    __IO  uint32_t                       dyn_ovr_wrcalib_offset_lane0 :4;
    __IO  uint32_t                       dyn_ovr_wrcalib_offset_lane1 :4;
    __IO  uint32_t                       dyn_ovr_wrcalib_offset_lane2 :4;
    __IO  uint32_t                       dyn_ovr_wrcalib_offset_lane3 :4;
    __IO  uint32_t                       dyn_ovr_wrcalib_offset_lane4 :4;
    __I   uint32_t                       reserved_01          :12;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_wrcalib_TypeDef;

typedef union{                                                         /*!< expert_calif register definition*/
  __IO  uint32_t                       expert_calif;
  struct
  {
    __IO  uint32_t                       dyn_ovr_calif_read   :1;
    __IO  uint32_t                       dyn_ovr_calif_write  :1;
    __IO  uint32_t                       dyn_ovr_pattern_sel  :4;
    __I   uint32_t                       reserved_01          :26;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_calif_TypeDef;

typedef union{                                                         /*!< expert_calif_readback register definition*/
  __I   uint32_t                       expert_calif_readback;
  struct
  {
    __I   uint32_t                       wrcalib_pattern_match_lane0 :8;
    __I   uint32_t                       wrcalib_pattern_match_lane1 :8;
    __I   uint32_t                       wrcalib_pattern_match_lane2 :8;
    __I   uint32_t                       wrcalib_pattern_match_lane3 :8;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_calif_readback_TypeDef;

typedef union{                                                         /*!< expert_calif_readback1 register definition*/
  __I   uint32_t                       expert_calif_readback1;
  struct
  {
    __I   uint32_t                       wrcalib_pattern_match_lane4 :8;
    __I   uint32_t                       reserved_01          :24;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_calif_readback1_TypeDef;

typedef union{                                                         /*!< expert_dfi_status_override_to_shim register definition*/
  __IO  uint32_t                       expert_dfi_status_override_to_shim;
  struct
  {
    __IO  uint32_t                       dfi_init_complete_shim :1;
    __IO  uint32_t                       dfi_training_complete_shim :1;
    __IO  uint32_t                       dfi_wrlvl_en_shim    :1;
    __IO  uint32_t                       dfi_rdlvl_en_shim    :1;
    __IO  uint32_t                       dfi_rdlvl_gate_en_shim :1;
    __I   uint32_t                       reserved_01          :27;
  } bitfield;
} CFG_DDR_SGMII_PHY_expert_dfi_status_override_to_shim_TypeDef;

typedef union{                                                         /*!< tip_cfg_params register definition*/
  __IO  uint32_t                       tip_cfg_params;
  struct
  {
    __IO  uint32_t                       addcmd_offset        :3;
    __IO  uint32_t                       bcklsclk_offset      :3;
    __IO  uint32_t                       wrcalib_write_count  :7;
    __IO  uint32_t                       read_gate_min_reads  :9;
    __IO  uint32_t                       addrcmd_wait_count   :9;
    __I   uint32_t                       reserved_01          :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_tip_cfg_params_TypeDef;

typedef union{                                                         /*!< tip_vref_param register definition*/
  __IO  uint32_t                       tip_vref_param;
  struct
  {
    __IO  uint32_t                       vref_override        :1;
    __IO  uint32_t                       data_vref            :8;
    __IO  uint32_t                       ca_vref              :8;
    __I   uint32_t                       reserved_01          :15;
  } bitfield;
} CFG_DDR_SGMII_PHY_tip_vref_param_TypeDef;

typedef union{                                                         /*!< lane_alignment_fifo_control register definition*/
  __IO  uint32_t                       lane_alignment_fifo_control;
  struct
  {
    __IO  uint32_t                       block_fifo           :1;
    __IO  uint32_t                       fifo_reset_n         :1;
    __I   uint32_t                       reserved_01          :30;
  } bitfield;
} CFG_DDR_SGMII_PHY_lane_alignment_fifo_control_TypeDef;

typedef union{                                                         /*!< SOFT_RESET_SGMII register definition*/
  __IO  uint32_t                       SOFT_RESET_SGMII;
  struct
  {
    __O   uint32_t                       nv_map_SGMII         :1;
    __O   uint32_t                       v_map_SGMII          :1;
    __I   uint32_t                       reserved_01          :6;
    __O   uint32_t                       periph_SGMII         :1;
    __I   uint32_t                       reserved_02          :7;
    __I   uint32_t                       blockid_SGMII        :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_SOFT_RESET_SGMII_TypeDef;

typedef union{                                                         /*!< SGMII_MODE register definition*/
  __IO  uint32_t                       SGMII_MODE;
  struct
  {
    __IO  uint32_t                       reg_pll_en           :1;
    __IO  uint32_t                       reg_dll_en           :1;
    __IO  uint32_t                       reg_pvt_en           :1;
    __IO  uint32_t                       reg_bc_vrgen_en      :1;
    __IO  uint32_t                       reg_tx0_en           :1;
    __IO  uint32_t                       reg_rx0_en           :1;
    __IO  uint32_t                       reg_tx1_en           :1;
    __IO  uint32_t                       reg_rx1_en           :1;
    __IO  uint32_t                       reg_dll_lock_flt     :2;
    __IO  uint32_t                       reg_dll_adj_code     :4;
    __IO  uint32_t                       reg_rx0_cdr_reset_b  :1;
    __IO  uint32_t                       reg_rx1_cdr_reset_b  :1;
    __IO  uint32_t                       reg_bc_vrgen         :6;
    __IO  uint32_t                       reg_cdr_move_step    :1;
    __IO  uint32_t                       reg_refclk_en_rdiff  :1;
    __IO  uint32_t                       reg_bc_vs            :4;
    __IO  uint32_t                       reg_refclk_en_udrive_p :1;
    __IO  uint32_t                       reg_refclk_en_ins_hyst_p :1;
    __IO  uint32_t                       reg_refclk_en_udrive_n :1;
    __IO  uint32_t                       reg_refclk_en_ins_hyst_n :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_SGMII_MODE_TypeDef;

typedef union{                                                         /*!< PLL_CNTL register definition*/
  __IO  uint32_t                       PLL_CNTL;
  struct
  {
    __IO  uint32_t                       reg_pll_postdiv      :7;
    __I   uint32_t                       aro_pll0_lock        :1;
    __IO  uint32_t                       reg_pll_rfdiv        :6;
    __IO  uint32_t                       reg_pll_reg_rfclk_sel :1;
    __IO  uint32_t                       reg_pll_lp_requires_lock :1;
    __IO  uint32_t                       reg_pll_intin        :12;
    __IO  uint32_t                       reg_pll_bwi          :2;
    __IO  uint32_t                       reg_pll_bwp          :2;
  } bitfield;
} CFG_DDR_SGMII_PHY_PLL_CNTL_TypeDef;

typedef union{                                                         /*!< CH0_CNTL register definition*/
  __IO  uint32_t                       CH0_CNTL;
  struct
  {
    __IO  uint32_t                       reg_tx0_wpu_p        :1;
    __IO  uint32_t                       reg_tx0_wpd_p        :1;
    __IO  uint32_t                       reg_tx0_slew_p       :2;
    __IO  uint32_t                       reg_tx0_drv_p        :4;
    __IO  uint32_t                       reg_tx0_odt_p        :4;
    __IO  uint32_t                       reg_tx0_odt_static_p :3;
    __IO  uint32_t                       reg_rx0_tim_long     :1;
    __IO  uint32_t                       reg_rx0_wpu_p        :1;
    __IO  uint32_t                       reg_rx0_wpd_p        :1;
    __IO  uint32_t                       reg_rx0_ibufmd_p     :3;
    __IO  uint32_t                       reg_rx0_eyewidth_p   :3;
    __IO  uint32_t                       reg_rx0_odt_p        :4;
    __IO  uint32_t                       reg_rx0_odt_static_p :3;
    __I   uint32_t                       reserved_01          :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_CH0_CNTL_TypeDef;

typedef union{                                                         /*!< CH1_CNTL register definition*/
  __IO  uint32_t                       CH1_CNTL;
  struct
  {
    __IO  uint32_t                       reg_tx1_wpu_p        :1;
    __IO  uint32_t                       reg_tx1_wpd_p        :1;
    __IO  uint32_t                       reg_tx1_slew_p       :2;
    __IO  uint32_t                       reg_tx1_drv_p        :4;
    __IO  uint32_t                       reg_tx1_odt_p        :4;
    __IO  uint32_t                       reg_tx1_odt_static_p :3;
    __IO  uint32_t                       reg_rx1_tim_long     :1;
    __IO  uint32_t                       reg_rx1_wpu_p        :1;
    __IO  uint32_t                       reg_rx1_wpd_p        :1;
    __IO  uint32_t                       reg_rx1_ibufmd_p     :3;
    __IO  uint32_t                       reg_rx1_eyewidth_p   :3;
    __IO  uint32_t                       reg_rx1_odt_p        :4;
    __IO  uint32_t                       reg_rx1_odt_static_p :3;
    __I   uint32_t                       reserved_01          :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_CH1_CNTL_TypeDef;

typedef union{                                                         /*!< RECAL_CNTL register definition*/
  __IO  uint32_t                       RECAL_CNTL;
  struct
  {
    __IO  uint32_t                       reg_recal_diff_range :5;
    __IO  uint32_t                       reg_recal_start_en   :1;
    __IO  uint32_t                       reg_pvt_calib_start  :1;
    __IO  uint32_t                       reg_pvt_calib_lock   :1;
    __IO  uint32_t                       reg_recal_upd        :1;
    __IO  uint32_t                       bc_vrgen_direction   :1;
    __IO  uint32_t                       bc_vrgen_load        :1;
    __IO  uint32_t                       bc_vrgen_move        :1;
    __IO  uint32_t                       reg_pvt_reg_calib_clkdiv :2;
    __IO  uint32_t                       reg_pvt_reg_calib_diffr_vsel :2;
    __I   uint32_t                       sro_dll_90_code      :7;
    __I   uint32_t                       sro_dll_lock         :1;
    __I   uint32_t                       sro_dll_st_code      :7;
    __I   uint32_t                       sro_recal_start      :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_RECAL_CNTL_TypeDef;

typedef union{                                                         /*!< CLK_CNTL register definition*/
  __IO  uint32_t                       CLK_CNTL;
  struct
  {
    __IO  uint32_t                       reg_refclk_en_term_p :2;
    __IO  uint32_t                       reg_refclk_en_rxmode_p :2;
    __IO  uint32_t                       reg_refclk_en_term_n :2;
    __IO  uint32_t                       reg_refclk_en_rxmode_n :2;
    __IO  uint32_t                       reg_refclk_clkbuf_en_pullup :1;
    __IO  uint32_t                       reg_clkmux_fclk_sel  :3;
    __IO  uint32_t                       reg_clkmux_pll0_rfclk0_sel :2;
    __IO  uint32_t                       reg_clkmux_pll0_rfclk1_sel :2;
    __IO  uint32_t                       reg_clkmux_spare0    :16;
  } bitfield;
} CFG_DDR_SGMII_PHY_CLK_CNTL_TypeDef;

typedef union{                                                         /*!< DYN_CNTL register definition*/
  __IO  uint32_t                       DYN_CNTL;
  struct
  {
    __IO  uint32_t                       reg_pll_dynen        :1;
    __IO  uint32_t                       reg_dll_dynen        :1;
    __IO  uint32_t                       reg_pvt_dynen        :1;
    __IO  uint32_t                       reg_bc_dynen         :1;
    __IO  uint32_t                       reg_clkmux_dynen     :1;
    __IO  uint32_t                       reg_lane0_dynen      :1;
    __IO  uint32_t                       reg_lane1_dynen      :1;
    __I   uint32_t                       bc_vrgen_oor         :1;
    __IO  uint32_t                       reg_pll_soft_reset_periph :1;
    __IO  uint32_t                       reg_dll_soft_reset_periph :1;
    __IO  uint32_t                       reg_pvt_soft_reset_periph :1;
    __IO  uint32_t                       reg_bc_soft_reset_periph :1;
    __IO  uint32_t                       reg_clkmux_soft_reset_periph :1;
    __IO  uint32_t                       reg_lane0_soft_reset_periph :1;
    __IO  uint32_t                       reg_lane1_soft_reset_periph :1;
    __I   uint32_t                       pvt_calib_status     :1;
    __I   uint32_t                       aro_pll0_vco0ph_sel  :3;
    __I   uint32_t                       aro_pll0_vco1ph_sel  :3;
    __I   uint32_t                       aro_pll0_vco2ph_sel  :3;
    __I   uint32_t                       aro_pll0_vco3ph_sel  :3;
    __I   uint32_t                       aro_ref_diffr        :4;
  } bitfield;
} CFG_DDR_SGMII_PHY_DYN_CNTL_TypeDef;

typedef union{                                                         /*!< PVT_STAT register definition*/
  __IO  uint32_t                       PVT_STAT;
  struct
  {
    __I   uint32_t                       aro_ref_pcode        :6;
    __I   uint32_t                       aro_ioen_bnk         :1;
    __I   uint32_t                       aro_ioen_bnk_b       :1;
    __I   uint32_t                       aro_ref_ncode        :6;
    __I   uint32_t                       aro_calib_status     :1;
    __I   uint32_t                       aro_calib_status_b   :1;
    __I   uint32_t                       aro_pcode            :6;
    __I   uint32_t                       aro_calib_intrpt     :1;
    __I   uint32_t                       pvt_calib_intrpt     :1;
    __I   uint32_t                       aro_ncode            :6;
    __IO  uint32_t                       pvt_calib_lock       :1;
    __IO  uint32_t                       pvt_calib_start      :1;
  } bitfield;
} CFG_DDR_SGMII_PHY_PVT_STAT_TypeDef;

typedef union{                                                         /*!< SPARE_CNTL register definition*/
  __IO  uint32_t                       SPARE_CNTL;
  struct
  {
    __IO  uint32_t                       reg_spare            :32;
  } bitfield;
} CFG_DDR_SGMII_PHY_SPARE_CNTL_TypeDef;

typedef union{                                                         /*!< SPARE_STAT register definition*/
  __I   uint32_t                       SPARE_STAT;
  struct
  {
    __I   uint32_t                       sro_spare            :32;
  } bitfield;
} CFG_DDR_SGMII_PHY_SPARE_STAT_TypeDef;

/*------------ CFG_DDR_SGMII_PHY definition -----------*/
typedef struct
{
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_DDR_PHY_TypeDef SOFT_RESET_DDR_PHY;                                 /*!< Offset: 0x0  */
  __IO  CFG_DDR_SGMII_PHY_DDRPHY_MODE_TypeDef DDRPHY_MODE;                                        /*!< Offset: 0x4  */
  __IO  CFG_DDR_SGMII_PHY_DDRPHY_STARTUP_TypeDef DDRPHY_STARTUP;                                     /*!< Offset: 0x8  */
  __IO   uint32_t                       UNUSED_SPACE0[29];                                  /*!< Offset: 0xc */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_MAIN_PLL_TypeDef SOFT_RESET_MAIN_PLL;                                /*!< Offset: 0x80  */
  __IO  CFG_DDR_SGMII_PHY_PLL_CTRL_MAIN_TypeDef PLL_CTRL_MAIN;                                      /*!< Offset: 0x84  */
  __IO  CFG_DDR_SGMII_PHY_PLL_REF_FB_MAIN_TypeDef PLL_REF_FB_MAIN;                                    /*!< Offset: 0x88  */
  __I  CFG_DDR_SGMII_PHY_PLL_FRACN_MAIN_TypeDef PLL_FRACN_MAIN;                                     /*!< Offset: 0x8c  */
  __IO  CFG_DDR_SGMII_PHY_PLL_DIV_0_1_MAIN_TypeDef PLL_DIV_0_1_MAIN;                                   /*!< Offset: 0x90  */
  __IO  CFG_DDR_SGMII_PHY_PLL_DIV_2_3_MAIN_TypeDef PLL_DIV_2_3_MAIN;                                   /*!< Offset: 0x94  */
  __IO  CFG_DDR_SGMII_PHY_PLL_CTRL2_MAIN_TypeDef PLL_CTRL2_MAIN;                                     /*!< Offset: 0x98  */
  __I   CFG_DDR_SGMII_PHY_PLL_CAL_MAIN_TypeDef PLL_CAL_MAIN;                                       /*!< Offset: 0x9c  */
  __IO  CFG_DDR_SGMII_PHY_PLL_PHADJ_MAIN_TypeDef PLL_PHADJ_MAIN;                                     /*!< Offset: 0xa0  */
  __I  CFG_DDR_SGMII_PHY_SSCG_REG_0_MAIN_TypeDef SSCG_REG_0_MAIN;                                    /*!< Offset: 0xa4  */
  __I  CFG_DDR_SGMII_PHY_SSCG_REG_1_MAIN_TypeDef SSCG_REG_1_MAIN;                                    /*!< Offset: 0xa8  */
  __IO  CFG_DDR_SGMII_PHY_SSCG_REG_2_MAIN_TypeDef SSCG_REG_2_MAIN;                                    /*!< Offset: 0xac  */
  __I  CFG_DDR_SGMII_PHY_SSCG_REG_3_MAIN_TypeDef SSCG_REG_3_MAIN;                                    /*!< Offset: 0xb0  */
  __IO  CFG_DDR_SGMII_PHY_RPC_RESET_MAIN_PLL_TypeDef RPC_RESET_MAIN_PLL;                                 /*!< Offset: 0xb4  */
  __I   uint32_t                       UNUSED_SPACE1[18];                                  /*!< Offset: 0xb8 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_IOSCB_PLL_TypeDef SOFT_RESET_IOSCB_PLL;                               /*!< Offset: 0x100  */
  __IO  CFG_DDR_SGMII_PHY_PLL_CTRL_IOSCB_TypeDef PLL_CTRL_IOSCB;                                     /*!< Offset: 0x104  */
  __IO  CFG_DDR_SGMII_PHY_PLL_REF_FB_IOSCB_TypeDef PLL_REF_FB_IOSCB;                                   /*!< Offset: 0x108  */
  __I   CFG_DDR_SGMII_PHY_PLL_FRACN_IOSCB_TypeDef PLL_FRACN_IOSCB;                                    /*!< Offset: 0x10c  */
  __IO  CFG_DDR_SGMII_PHY_PLL_DIV_0_1_IOSCB_TypeDef PLL_DIV_0_1_IOSCB;                                  /*!< Offset: 0x110  */
  __IO  CFG_DDR_SGMII_PHY_PLL_DIV_2_3_IOSCB_TypeDef PLL_DIV_2_3_IOSCB;                                  /*!< Offset: 0x114  */
  __IO  CFG_DDR_SGMII_PHY_PLL_CTRL2_IOSCB_TypeDef PLL_CTRL2_IOSCB;                                    /*!< Offset: 0x118  */
  __I  CFG_DDR_SGMII_PHY_PLL_CAL_IOSCB_TypeDef PLL_CAL_IOSCB;                                      /*!< Offset: 0x11c  */
  __IO  CFG_DDR_SGMII_PHY_PLL_PHADJ_IOSCB_TypeDef PLL_PHADJ_IOSCB;                                    /*!< Offset: 0x120  */
  __I   CFG_DDR_SGMII_PHY_SSCG_REG_0_IOSCB_TypeDef SSCG_REG_0_IOSCB;                                   /*!< Offset: 0x124  */
  __I   CFG_DDR_SGMII_PHY_SSCG_REG_1_IOSCB_TypeDef SSCG_REG_1_IOSCB;                                   /*!< Offset: 0x128  */
  __IO  CFG_DDR_SGMII_PHY_SSCG_REG_2_IOSCB_TypeDef SSCG_REG_2_IOSCB;                                   /*!< Offset: 0x12c  */
  __I   CFG_DDR_SGMII_PHY_SSCG_REG_3_IOSCB_TypeDef SSCG_REG_3_IOSCB;                                   /*!< Offset: 0x130  */
  __IO  CFG_DDR_SGMII_PHY_RPC_RESET_IOSCB_TypeDef RPC_RESET_IOSCB;                                    /*!< Offset: 0x134  */
  __I   uint32_t                       UNUSED_SPACE2[18];                                  /*!< Offset: 0x138 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_BANK_CTRL_TypeDef SOFT_RESET_BANK_CTRL;                               /*!< Offset: 0x180  */
  __IO  CFG_DDR_SGMII_PHY_DPC_BITS_TypeDef DPC_BITS;                                           /*!< Offset: 0x184  */
  __I   CFG_DDR_SGMII_PHY_BANK_STATUS_TypeDef BANK_STATUS;                                        /*!< Offset: 0x188  */
  __IO  CFG_DDR_SGMII_PHY_RPC_RESET_BANK_CTRL_TypeDef RPC_RESET_BANK_CTRL;                                /*!< Offset: 0x18c  */
  __I   uint32_t                       UNUSED_SPACE3[28];                                  /*!< Offset: 0x190 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_IOCALIB_TypeDef SOFT_RESET_IOCALIB;                       /*!< Offset: 0x200  */
  __IO  CFG_DDR_SGMII_PHY_IOC_REG0_TypeDef IOC_REG0;                                           /*!< Offset: 0x204  */
  __I   CFG_DDR_SGMII_PHY_IOC_REG1_TypeDef IOC_REG1;                                           /*!< Offset: 0x208  */
  __I   CFG_DDR_SGMII_PHY_IOC_REG2_TypeDef IOC_REG2;                                           /*!< Offset: 0x20c  */
  __I   CFG_DDR_SGMII_PHY_IOC_REG3_TypeDef IOC_REG3;                                           /*!< Offset: 0x210  */
  __I   CFG_DDR_SGMII_PHY_IOC_REG4_TypeDef IOC_REG4;                                           /*!< Offset: 0x214  */
  __I   CFG_DDR_SGMII_PHY_IOC_REG5_TypeDef IOC_REG5;                                           /*!< Offset: 0x218  */
  __IO  CFG_DDR_SGMII_PHY_IOC_REG6_TypeDef IOC_REG6;                                           /*!< Offset: 0x21c  */
  __IO  CFG_DDR_SGMII_PHY_RPC_RESET_IOCALIB_TypeDef RPC_RESET_IOCALIB;                                  /*!< Offset: 0x220  */
  __IO  CFG_DDR_SGMII_PHY_rpc_calib_TypeDef rpc_calib;                                          /*!< Offset: 0x224  */
  __I   uint32_t                       UNUSED_SPACE4[22];                                  /*!< Offset: 0x228 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_CFM_TypeDef SOFT_RESET_CFM;                                     /*!< Offset: 0x280  */
  __IO  CFG_DDR_SGMII_PHY_BCLKMUX_TypeDef BCLKMUX;                                            /*!< Offset: 0x284  */
  __IO  CFG_DDR_SGMII_PHY_PLL_CKMUX_TypeDef PLL_CKMUX;                                          /*!< Offset: 0x288  */
  __IO  CFG_DDR_SGMII_PHY_MSSCLKMUX_TypeDef MSSCLKMUX;                                          /*!< Offset: 0x28c  */
  __IO  CFG_DDR_SGMII_PHY_SPARE0_TypeDef SPARE0;                                             /*!< Offset: 0x290  */
  __I   CFG_DDR_SGMII_PHY_FMETER_ADDR_TypeDef FMETER_ADDR;                                        /*!< Offset: 0x294  */
  __I   CFG_DDR_SGMII_PHY_FMETER_DATAW_TypeDef FMETER_DATAW;                                       /*!< Offset: 0x298  */
  __I   CFG_DDR_SGMII_PHY_FMETER_DATAR_TypeDef FMETER_DATAR;                                       /*!< Offset: 0x29c  */
  __I   CFG_DDR_SGMII_PHY_TEST_CTRL_TypeDef TEST_CTRL;                                          /*!< Offset: 0x2a0  */
  __IO  CFG_DDR_SGMII_PHY_RPC_RESET_CFM_TypeDef RPC_RESET_CFM;                                      /*!< Offset: 0x2a4  */
  __I   uint32_t                       UNUSED_SPACE5[22];                                  /*!< Offset: 0x2a8 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_DRIVER_TypeDef SOFT_RESET_DECODER_DRIVER;                          /*!< Offset: 0x300  */
  __IO  CFG_DDR_SGMII_PHY_rpc1_DRV_TypeDef rpc1_DRV;                                           /*!< Offset: 0x304  */
  __IO  CFG_DDR_SGMII_PHY_rpc2_DRV_TypeDef rpc2_DRV;                                           /*!< Offset: 0x308  */
  __IO  CFG_DDR_SGMII_PHY_rpc3_DRV_TypeDef rpc3_DRV;                                           /*!< Offset: 0x30c  */
  __IO  CFG_DDR_SGMII_PHY_rpc4_DRV_TypeDef rpc4_DRV;                                           /*!< Offset: 0x310  */
  __I   uint32_t                       UNUSED_SPACE6[27];                                  /*!< Offset: 0x314 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_ODT_TypeDef SOFT_RESET_DECODER_ODT;                             /*!< Offset: 0x380  */
  __IO  CFG_DDR_SGMII_PHY_rpc1_ODT_TypeDef rpc1_ODT;                                           /*!< Offset: 0x384  */
  __IO  CFG_DDR_SGMII_PHY_rpc2_ODT_TypeDef rpc2_ODT;                                           /*!< Offset: 0x388  */
  __IO  CFG_DDR_SGMII_PHY_rpc3_ODT_TypeDef rpc3_ODT;                                           /*!< Offset: 0x38c  */
  __IO  CFG_DDR_SGMII_PHY_rpc4_ODT_TypeDef rpc4_ODT;                                           /*!< Offset: 0x390  */
  __IO  CFG_DDR_SGMII_PHY_rpc5_ODT_TypeDef rpc5_ODT;                                           /*!< Offset: 0x394  */
  __IO  CFG_DDR_SGMII_PHY_rpc6_ODT_TypeDef rpc6_ODT;                                           /*!< Offset: 0x398  */
  __IO  CFG_DDR_SGMII_PHY_rpc7_ODT_TypeDef rpc7_ODT;                                           /*!< Offset: 0x39c  */
  __IO  CFG_DDR_SGMII_PHY_rpc8_ODT_TypeDef rpc8_ODT;                                           /*!< Offset: 0x3a0  */
  __IO  CFG_DDR_SGMII_PHY_rpc9_ODT_TypeDef rpc9_ODT;                                           /*!< Offset: 0x3a4  */
  __IO  CFG_DDR_SGMII_PHY_rpc10_ODT_TypeDef rpc10_ODT;                                          /*!< Offset: 0x3a8  */
  __IO  CFG_DDR_SGMII_PHY_rpc11_ODT_TypeDef rpc11_ODT;                                          /*!< Offset: 0x3ac  */
  __I   uint32_t                       UNUSED_SPACE7[20];                                  /*!< Offset: 0x3b0 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_DECODER_IO_TypeDef SOFT_RESET_DECODER_IO;                              /*!< Offset: 0x400  */
  __IO  CFG_DDR_SGMII_PHY_ovrt1_TypeDef ovrt1;                                              /*!< Offset: 0x404  */
  __IO  CFG_DDR_SGMII_PHY_ovrt2_TypeDef ovrt2;                                              /*!< Offset: 0x408  */
  __IO  CFG_DDR_SGMII_PHY_ovrt3_TypeDef ovrt3;                                              /*!< Offset: 0x40c  */
  __IO  CFG_DDR_SGMII_PHY_ovrt4_TypeDef ovrt4;                                              /*!< Offset: 0x410  */
  __IO  CFG_DDR_SGMII_PHY_ovrt5_TypeDef ovrt5;                                              /*!< Offset: 0x414  */
  __IO  CFG_DDR_SGMII_PHY_ovrt6_TypeDef ovrt6;                                              /*!< Offset: 0x418  */
  __IO  CFG_DDR_SGMII_PHY_ovrt7_TypeDef ovrt7;                                              /*!< Offset: 0x41c  */
  __IO  CFG_DDR_SGMII_PHY_ovrt8_TypeDef ovrt8;                                              /*!< Offset: 0x420  */
  __IO  CFG_DDR_SGMII_PHY_ovrt9_TypeDef ovrt9;                                              /*!< Offset: 0x424  */
  __IO  CFG_DDR_SGMII_PHY_ovrt10_TypeDef ovrt10;                                             /*!< Offset: 0x428  */
  __IO  CFG_DDR_SGMII_PHY_ovrt11_TypeDef ovrt11;                                             /*!< Offset: 0x42c  */
  __IO  CFG_DDR_SGMII_PHY_ovrt12_TypeDef ovrt12;                                             /*!< Offset: 0x430  */
  __IO  CFG_DDR_SGMII_PHY_ovrt13_TypeDef ovrt13;                                             /*!< Offset: 0x434  */
  __IO  CFG_DDR_SGMII_PHY_ovrt14_TypeDef ovrt14;                                             /*!< Offset: 0x438  */
  __IO  CFG_DDR_SGMII_PHY_ovrt15_TypeDef ovrt15;                                             /*!< Offset: 0x43c  */
  __IO  CFG_DDR_SGMII_PHY_ovrt16_TypeDef ovrt16;                                             /*!< Offset: 0x440  */
  __IO  CFG_DDR_SGMII_PHY_rpc17_TypeDef rpc17;                                              /*!< Offset: 0x444  */
  __IO  CFG_DDR_SGMII_PHY_rpc18_TypeDef rpc18;                                              /*!< Offset: 0x448  */
  __IO  CFG_DDR_SGMII_PHY_rpc19_TypeDef rpc19;                                              /*!< Offset: 0x44c  */
  __IO  CFG_DDR_SGMII_PHY_rpc20_TypeDef rpc20;                                              /*!< Offset: 0x450  */
  __IO  CFG_DDR_SGMII_PHY_rpc21_TypeDef rpc21;                                              /*!< Offset: 0x454  */
  __IO  CFG_DDR_SGMII_PHY_rpc22_TypeDef rpc22;                                              /*!< Offset: 0x458  */
  __IO  CFG_DDR_SGMII_PHY_rpc23_TypeDef rpc23;                                              /*!< Offset: 0x45c  */
  __IO  CFG_DDR_SGMII_PHY_rpc24_TypeDef rpc24;                                              /*!< Offset: 0x460  */
  __IO  CFG_DDR_SGMII_PHY_rpc25_TypeDef rpc25;                                              /*!< Offset: 0x464  */
  __IO  CFG_DDR_SGMII_PHY_rpc26_TypeDef rpc26;                                              /*!< Offset: 0x468  */
  __IO  CFG_DDR_SGMII_PHY_rpc27_TypeDef rpc27;                                              /*!< Offset: 0x46c  */
  __IO  CFG_DDR_SGMII_PHY_rpc28_TypeDef rpc28;                                              /*!< Offset: 0x470  */
  __IO  CFG_DDR_SGMII_PHY_rpc29_TypeDef rpc29;                                              /*!< Offset: 0x474  */
  __IO  CFG_DDR_SGMII_PHY_rpc30_TypeDef rpc30;                                              /*!< Offset: 0x478  */
  __IO  CFG_DDR_SGMII_PHY_rpc31_TypeDef rpc31;                                              /*!< Offset: 0x47c  */
  __IO  CFG_DDR_SGMII_PHY_rpc32_TypeDef rpc32;                                              /*!< Offset: 0x480  */
  __IO  CFG_DDR_SGMII_PHY_rpc33_TypeDef rpc33;                                              /*!< Offset: 0x484  */
  __IO  CFG_DDR_SGMII_PHY_rpc34_TypeDef rpc34;                                              /*!< Offset: 0x488  */
  __IO  CFG_DDR_SGMII_PHY_rpc35_TypeDef rpc35;                                              /*!< Offset: 0x48c  */
  __IO  CFG_DDR_SGMII_PHY_rpc36_TypeDef rpc36;                                              /*!< Offset: 0x490  */
  __IO  CFG_DDR_SGMII_PHY_rpc37_TypeDef rpc37;                                              /*!< Offset: 0x494  */
  __IO  CFG_DDR_SGMII_PHY_rpc38_TypeDef rpc38;                                              /*!< Offset: 0x498  */
  __IO  CFG_DDR_SGMII_PHY_rpc39_TypeDef rpc39;                                              /*!< Offset: 0x49c  */
  __IO  CFG_DDR_SGMII_PHY_rpc40_TypeDef rpc40;                                              /*!< Offset: 0x4a0  */
  __IO  CFG_DDR_SGMII_PHY_rpc41_TypeDef rpc41;                                              /*!< Offset: 0x4a4  */
  __IO  CFG_DDR_SGMII_PHY_rpc42_TypeDef rpc42;                                              /*!< Offset: 0x4a8  */
  __IO  CFG_DDR_SGMII_PHY_rpc43_TypeDef rpc43;                                              /*!< Offset: 0x4ac  */
  __IO  CFG_DDR_SGMII_PHY_rpc44_TypeDef rpc44;                                              /*!< Offset: 0x4b0  */
  __IO  CFG_DDR_SGMII_PHY_rpc45_TypeDef rpc45;                                              /*!< Offset: 0x4b4  */
  __IO  CFG_DDR_SGMII_PHY_rpc46_TypeDef rpc46;                                              /*!< Offset: 0x4b8  */
  __IO  CFG_DDR_SGMII_PHY_rpc47_TypeDef rpc47;                                              /*!< Offset: 0x4bc  */
  __IO  CFG_DDR_SGMII_PHY_rpc48_TypeDef rpc48;                                              /*!< Offset: 0x4c0  */
  __IO  CFG_DDR_SGMII_PHY_rpc49_TypeDef rpc49;                                              /*!< Offset: 0x4c4  */
  __IO  CFG_DDR_SGMII_PHY_rpc50_TypeDef rpc50;                                              /*!< Offset: 0x4c8  */
  __IO  CFG_DDR_SGMII_PHY_rpc51_TypeDef rpc51;                                              /*!< Offset: 0x4cc  */
  __IO  CFG_DDR_SGMII_PHY_rpc52_TypeDef rpc52;                                              /*!< Offset: 0x4d0  */
  __IO  CFG_DDR_SGMII_PHY_rpc53_TypeDef rpc53;                                              /*!< Offset: 0x4d4  */
  __IO  CFG_DDR_SGMII_PHY_rpc54_TypeDef rpc54;                                              /*!< Offset: 0x4d8  */
  __IO  CFG_DDR_SGMII_PHY_rpc55_TypeDef rpc55;                                              /*!< Offset: 0x4dc  */
  __IO  CFG_DDR_SGMII_PHY_rpc56_TypeDef rpc56;                                              /*!< Offset: 0x4e0  */
  __IO  CFG_DDR_SGMII_PHY_rpc57_TypeDef rpc57;                                              /*!< Offset: 0x4e4  */
  __IO  CFG_DDR_SGMII_PHY_rpc58_TypeDef rpc58;                                              /*!< Offset: 0x4e8  */
  __IO  CFG_DDR_SGMII_PHY_rpc59_TypeDef rpc59;                                              /*!< Offset: 0x4ec  */
  __IO  CFG_DDR_SGMII_PHY_rpc60_TypeDef rpc60;                                              /*!< Offset: 0x4f0  */
  __IO  CFG_DDR_SGMII_PHY_rpc61_TypeDef rpc61;                                              /*!< Offset: 0x4f4  */
  __IO  CFG_DDR_SGMII_PHY_rpc62_TypeDef rpc62;                                              /*!< Offset: 0x4f8  */
  __IO  CFG_DDR_SGMII_PHY_rpc63_TypeDef rpc63;                                              /*!< Offset: 0x4fc  */
  __IO  CFG_DDR_SGMII_PHY_rpc64_TypeDef rpc64;                                              /*!< Offset: 0x500  */
  __IO  CFG_DDR_SGMII_PHY_rpc65_TypeDef rpc65;                                              /*!< Offset: 0x504  */
  __IO  CFG_DDR_SGMII_PHY_rpc66_TypeDef rpc66;                                              /*!< Offset: 0x508  */
  __IO  CFG_DDR_SGMII_PHY_rpc67_TypeDef rpc67;                                              /*!< Offset: 0x50c  */
  __IO  CFG_DDR_SGMII_PHY_rpc68_TypeDef rpc68;                                              /*!< Offset: 0x510  */
  __IO  CFG_DDR_SGMII_PHY_rpc69_TypeDef rpc69;                                              /*!< Offset: 0x514  */
  __IO  CFG_DDR_SGMII_PHY_rpc70_TypeDef rpc70;                                              /*!< Offset: 0x518  */
  __IO  CFG_DDR_SGMII_PHY_rpc71_TypeDef rpc71;                                              /*!< Offset: 0x51c  */
  __IO  CFG_DDR_SGMII_PHY_rpc72_TypeDef rpc72;                                              /*!< Offset: 0x520  */
  __IO  CFG_DDR_SGMII_PHY_rpc73_TypeDef rpc73;                                              /*!< Offset: 0x524  */
  __IO  CFG_DDR_SGMII_PHY_rpc74_TypeDef rpc74;                                              /*!< Offset: 0x528  */
  __IO  CFG_DDR_SGMII_PHY_rpc75_TypeDef rpc75;                                              /*!< Offset: 0x52c  */
  __IO  CFG_DDR_SGMII_PHY_rpc76_TypeDef rpc76;                                              /*!< Offset: 0x530  */
  __IO  CFG_DDR_SGMII_PHY_rpc77_TypeDef rpc77;                                              /*!< Offset: 0x534  */
  __IO  CFG_DDR_SGMII_PHY_rpc78_TypeDef rpc78;                                              /*!< Offset: 0x538  */
  __IO  CFG_DDR_SGMII_PHY_rpc79_TypeDef rpc79;                                              /*!< Offset: 0x53c  */
  __IO  CFG_DDR_SGMII_PHY_rpc80_TypeDef rpc80;                                              /*!< Offset: 0x540  */
  __IO  CFG_DDR_SGMII_PHY_rpc81_TypeDef rpc81;                                              /*!< Offset: 0x544  */
  __IO  CFG_DDR_SGMII_PHY_rpc82_TypeDef rpc82;                                              /*!< Offset: 0x548  */
  __IO  CFG_DDR_SGMII_PHY_rpc83_TypeDef rpc83;                                              /*!< Offset: 0x54c  */
  __IO  CFG_DDR_SGMII_PHY_rpc84_TypeDef rpc84;                                              /*!< Offset: 0x550  */
  __IO  CFG_DDR_SGMII_PHY_rpc85_TypeDef rpc85;                                              /*!< Offset: 0x554  */
  __IO  CFG_DDR_SGMII_PHY_rpc86_TypeDef rpc86;                                              /*!< Offset: 0x558  */
  __IO  CFG_DDR_SGMII_PHY_rpc87_TypeDef rpc87;                                              /*!< Offset: 0x55c  */
  __IO  CFG_DDR_SGMII_PHY_rpc88_TypeDef rpc88;                                              /*!< Offset: 0x560  */
  __IO  CFG_DDR_SGMII_PHY_rpc89_TypeDef rpc89;                                              /*!< Offset: 0x564  */
  __IO  CFG_DDR_SGMII_PHY_rpc90_TypeDef rpc90;                                              /*!< Offset: 0x568  */
  __IO  CFG_DDR_SGMII_PHY_rpc91_TypeDef rpc91;                                              /*!< Offset: 0x56c  */
  __IO  CFG_DDR_SGMII_PHY_rpc92_TypeDef rpc92;                                              /*!< Offset: 0x570  */
  __IO  CFG_DDR_SGMII_PHY_rpc93_TypeDef rpc93;                                              /*!< Offset: 0x574  */
  __IO  CFG_DDR_SGMII_PHY_rpc94_TypeDef rpc94;                                              /*!< Offset: 0x578  */
  __IO  CFG_DDR_SGMII_PHY_rpc95_TypeDef rpc95;                                              /*!< Offset: 0x57c  */
  __IO  CFG_DDR_SGMII_PHY_rpc96_TypeDef rpc96;                                              /*!< Offset: 0x580  */
  __IO  CFG_DDR_SGMII_PHY_rpc97_TypeDef rpc97;                                              /*!< Offset: 0x584  */
  __IO  CFG_DDR_SGMII_PHY_rpc98_TypeDef rpc98;                                              /*!< Offset: 0x588  */
  __IO  CFG_DDR_SGMII_PHY_rpc99_TypeDef rpc99;                                              /*!< Offset: 0x58c  */
  __IO  CFG_DDR_SGMII_PHY_rpc100_TypeDef rpc100;                                             /*!< Offset: 0x590  */
  __IO  CFG_DDR_SGMII_PHY_rpc101_TypeDef rpc101;                                             /*!< Offset: 0x594  */
  __IO  CFG_DDR_SGMII_PHY_rpc102_TypeDef rpc102;                                             /*!< Offset: 0x598  */
  __IO  CFG_DDR_SGMII_PHY_rpc103_TypeDef rpc103;                                             /*!< Offset: 0x59c  */
  __IO  CFG_DDR_SGMII_PHY_rpc104_TypeDef rpc104;                                             /*!< Offset: 0x5a0  */
  __IO  CFG_DDR_SGMII_PHY_rpc105_TypeDef rpc105;                                             /*!< Offset: 0x5a4  */
  __IO  CFG_DDR_SGMII_PHY_rpc106_TypeDef rpc106;                                             /*!< Offset: 0x5a8  */
  __IO  CFG_DDR_SGMII_PHY_rpc107_TypeDef rpc107;                                             /*!< Offset: 0x5ac  */
  __IO  CFG_DDR_SGMII_PHY_rpc108_TypeDef rpc108;                                             /*!< Offset: 0x5b0  */
  __IO  CFG_DDR_SGMII_PHY_rpc109_TypeDef rpc109;                                             /*!< Offset: 0x5b4  */
  __IO  CFG_DDR_SGMII_PHY_rpc110_TypeDef rpc110;                                             /*!< Offset: 0x5b8  */
  __IO  CFG_DDR_SGMII_PHY_rpc111_TypeDef rpc111;                                             /*!< Offset: 0x5bc  */
  __IO  CFG_DDR_SGMII_PHY_rpc112_TypeDef rpc112;                                             /*!< Offset: 0x5c0  */
  __IO  CFG_DDR_SGMII_PHY_rpc113_TypeDef rpc113;                                             /*!< Offset: 0x5c4  */
  __IO  CFG_DDR_SGMII_PHY_rpc114_TypeDef rpc114;                                             /*!< Offset: 0x5c8  */
  __IO  CFG_DDR_SGMII_PHY_rpc115_TypeDef rpc115;                                             /*!< Offset: 0x5cc  */
  __IO  CFG_DDR_SGMII_PHY_rpc116_TypeDef rpc116;                                             /*!< Offset: 0x5d0  */
  __IO  CFG_DDR_SGMII_PHY_rpc117_TypeDef rpc117;                                             /*!< Offset: 0x5d4  */
  __IO  CFG_DDR_SGMII_PHY_rpc118_TypeDef rpc118;                                             /*!< Offset: 0x5d8  */
  __IO  CFG_DDR_SGMII_PHY_rpc119_TypeDef rpc119;                                             /*!< Offset: 0x5dc  */
  __IO  CFG_DDR_SGMII_PHY_rpc120_TypeDef rpc120;                                             /*!< Offset: 0x5e0  */
  __IO  CFG_DDR_SGMII_PHY_rpc121_TypeDef rpc121;                                             /*!< Offset: 0x5e4  */
  __IO  CFG_DDR_SGMII_PHY_rpc122_TypeDef rpc122;                                             /*!< Offset: 0x5e8  */
  __IO  CFG_DDR_SGMII_PHY_rpc123_TypeDef rpc123;                                             /*!< Offset: 0x5ec  */
  __IO  CFG_DDR_SGMII_PHY_rpc124_TypeDef rpc124;                                             /*!< Offset: 0x5f0  */
  __IO  CFG_DDR_SGMII_PHY_rpc125_TypeDef rpc125;                                             /*!< Offset: 0x5f4  */
  __IO  CFG_DDR_SGMII_PHY_rpc126_TypeDef rpc126;                                             /*!< Offset: 0x5f8  */
  __IO  CFG_DDR_SGMII_PHY_rpc127_TypeDef rpc127;                                             /*!< Offset: 0x5fc  */
  __IO  CFG_DDR_SGMII_PHY_rpc128_TypeDef rpc128;                                             /*!< Offset: 0x600  */
  __IO  CFG_DDR_SGMII_PHY_rpc129_TypeDef rpc129;                                             /*!< Offset: 0x604  */
  __IO  CFG_DDR_SGMII_PHY_rpc130_TypeDef rpc130;                                             /*!< Offset: 0x608  */
  __IO  CFG_DDR_SGMII_PHY_rpc131_TypeDef rpc131;                                             /*!< Offset: 0x60c  */
  __IO  CFG_DDR_SGMII_PHY_rpc132_TypeDef rpc132;                                             /*!< Offset: 0x610  */
  __IO  CFG_DDR_SGMII_PHY_rpc133_TypeDef rpc133;                                             /*!< Offset: 0x614  */
  __IO  CFG_DDR_SGMII_PHY_rpc134_TypeDef rpc134;                                             /*!< Offset: 0x618  */
  __IO  CFG_DDR_SGMII_PHY_rpc135_TypeDef rpc135;                                             /*!< Offset: 0x61c  */
  __IO  CFG_DDR_SGMII_PHY_rpc136_TypeDef rpc136;                                             /*!< Offset: 0x620  */
  __IO  CFG_DDR_SGMII_PHY_rpc137_TypeDef rpc137;                                             /*!< Offset: 0x624  */
  __IO  CFG_DDR_SGMII_PHY_rpc138_TypeDef rpc138;                                             /*!< Offset: 0x628  */
  __IO  CFG_DDR_SGMII_PHY_rpc139_TypeDef rpc139;                                             /*!< Offset: 0x62c  */
  __IO  CFG_DDR_SGMII_PHY_rpc140_TypeDef rpc140;                                             /*!< Offset: 0x630  */
  __IO  CFG_DDR_SGMII_PHY_rpc141_TypeDef rpc141;                                             /*!< Offset: 0x634  */
  __IO  CFG_DDR_SGMII_PHY_rpc142_TypeDef rpc142;                                             /*!< Offset: 0x638  */
  __IO  CFG_DDR_SGMII_PHY_rpc143_TypeDef rpc143;                                             /*!< Offset: 0x63c  */
  __IO  CFG_DDR_SGMII_PHY_rpc144_TypeDef rpc144;                                             /*!< Offset: 0x640  */
  __IO  CFG_DDR_SGMII_PHY_rpc145_TypeDef rpc145;                                             /*!< Offset: 0x644  */
  __IO  CFG_DDR_SGMII_PHY_rpc146_TypeDef rpc146;                                             /*!< Offset: 0x648  */
  __IO  CFG_DDR_SGMII_PHY_rpc147_TypeDef rpc147;                                             /*!< Offset: 0x64c  */
  __IO  CFG_DDR_SGMII_PHY_rpc148_TypeDef rpc148;                                             /*!< Offset: 0x650  */
  __IO  CFG_DDR_SGMII_PHY_rpc149_TypeDef rpc149;                                             /*!< Offset: 0x654  */
  __IO  CFG_DDR_SGMII_PHY_rpc150_TypeDef rpc150;                                             /*!< Offset: 0x658  */
  __IO  CFG_DDR_SGMII_PHY_rpc151_TypeDef rpc151;                                             /*!< Offset: 0x65c  */
  __IO  CFG_DDR_SGMII_PHY_rpc152_TypeDef rpc152;                                             /*!< Offset: 0x660  */
  __IO  CFG_DDR_SGMII_PHY_rpc153_TypeDef rpc153;                                             /*!< Offset: 0x664  */
  __IO  CFG_DDR_SGMII_PHY_rpc154_TypeDef rpc154;                                             /*!< Offset: 0x668  */
  __IO  CFG_DDR_SGMII_PHY_rpc155_TypeDef rpc155;                                             /*!< Offset: 0x66c  */
  __IO  CFG_DDR_SGMII_PHY_rpc156_TypeDef rpc156;                                             /*!< Offset: 0x670  */
  __IO  CFG_DDR_SGMII_PHY_rpc157_TypeDef rpc157;                                             /*!< Offset: 0x674  */
  __IO  CFG_DDR_SGMII_PHY_rpc158_TypeDef rpc158;                                             /*!< Offset: 0x678  */
  __IO  CFG_DDR_SGMII_PHY_rpc159_TypeDef rpc159;                                             /*!< Offset: 0x67c  */
  __IO  CFG_DDR_SGMII_PHY_rpc160_TypeDef rpc160;                                             /*!< Offset: 0x680  */
  __IO  CFG_DDR_SGMII_PHY_rpc161_TypeDef rpc161;                                             /*!< Offset: 0x684  */
  __IO  CFG_DDR_SGMII_PHY_rpc162_TypeDef rpc162;                                             /*!< Offset: 0x688  */
  __IO  CFG_DDR_SGMII_PHY_rpc163_TypeDef rpc163;                                             /*!< Offset: 0x68c  */
  __IO  CFG_DDR_SGMII_PHY_rpc164_TypeDef rpc164;                                             /*!< Offset: 0x690  */
  __IO  CFG_DDR_SGMII_PHY_rpc165_TypeDef rpc165;                                             /*!< Offset: 0x694  */
  __IO  CFG_DDR_SGMII_PHY_rpc166_TypeDef rpc166;                                             /*!< Offset: 0x698  */
  __IO  CFG_DDR_SGMII_PHY_rpc167_TypeDef rpc167;                                             /*!< Offset: 0x69c  */
  __IO  CFG_DDR_SGMII_PHY_rpc168_TypeDef rpc168;                                             /*!< Offset: 0x6a0  */
  __IO  CFG_DDR_SGMII_PHY_rpc169_TypeDef rpc169;                                             /*!< Offset: 0x6a4  */
  __IO  CFG_DDR_SGMII_PHY_rpc170_TypeDef rpc170;                                             /*!< Offset: 0x6a8  */
  __IO  CFG_DDR_SGMII_PHY_rpc171_TypeDef rpc171;                                             /*!< Offset: 0x6ac  */
  __IO  CFG_DDR_SGMII_PHY_rpc172_TypeDef rpc172;                                             /*!< Offset: 0x6b0  */
  __IO  CFG_DDR_SGMII_PHY_rpc173_TypeDef rpc173;                                             /*!< Offset: 0x6b4  */
  __IO  CFG_DDR_SGMII_PHY_rpc174_TypeDef rpc174;                                             /*!< Offset: 0x6b8  */
  __IO  CFG_DDR_SGMII_PHY_rpc175_TypeDef rpc175;                                             /*!< Offset: 0x6bc  */
  __IO  CFG_DDR_SGMII_PHY_rpc176_TypeDef rpc176;                                             /*!< Offset: 0x6c0  */
  __IO  CFG_DDR_SGMII_PHY_rpc177_TypeDef rpc177;                                             /*!< Offset: 0x6c4  */
  __IO  CFG_DDR_SGMII_PHY_rpc178_TypeDef rpc178;                                             /*!< Offset: 0x6c8  */
  __IO  CFG_DDR_SGMII_PHY_rpc179_TypeDef rpc179;                                             /*!< Offset: 0x6cc  */
  __IO  CFG_DDR_SGMII_PHY_rpc180_TypeDef rpc180;                                             /*!< Offset: 0x6d0  */
  __IO  CFG_DDR_SGMII_PHY_rpc181_TypeDef rpc181;                                             /*!< Offset: 0x6d4  */
  __IO  CFG_DDR_SGMII_PHY_rpc182_TypeDef rpc182;                                             /*!< Offset: 0x6d8  */
  __IO  CFG_DDR_SGMII_PHY_rpc183_TypeDef rpc183;                                             /*!< Offset: 0x6dc  */
  __IO  CFG_DDR_SGMII_PHY_rpc184_TypeDef rpc184;                                             /*!< Offset: 0x6e0  */
  __IO  CFG_DDR_SGMII_PHY_rpc185_TypeDef rpc185;                                             /*!< Offset: 0x6e4  */
  __IO  CFG_DDR_SGMII_PHY_rpc186_TypeDef rpc186;                                             /*!< Offset: 0x6e8  */
  __IO  CFG_DDR_SGMII_PHY_rpc187_TypeDef rpc187;                                             /*!< Offset: 0x6ec  */
  __IO  CFG_DDR_SGMII_PHY_rpc188_TypeDef rpc188;                                             /*!< Offset: 0x6f0  */
  __IO  CFG_DDR_SGMII_PHY_rpc189_TypeDef rpc189;                                             /*!< Offset: 0x6f4  */
  __IO  CFG_DDR_SGMII_PHY_rpc190_TypeDef rpc190;                                             /*!< Offset: 0x6f8  */
  __IO  CFG_DDR_SGMII_PHY_rpc191_TypeDef rpc191;                                             /*!< Offset: 0x6fc  */
  __IO  CFG_DDR_SGMII_PHY_rpc192_TypeDef rpc192;                                             /*!< Offset: 0x700  */
  __IO  CFG_DDR_SGMII_PHY_rpc193_TypeDef rpc193;                                             /*!< Offset: 0x704  */
  __IO  CFG_DDR_SGMII_PHY_rpc194_TypeDef rpc194;                                             /*!< Offset: 0x708  */
  __IO  CFG_DDR_SGMII_PHY_rpc195_TypeDef rpc195;                                             /*!< Offset: 0x70c  */
  __IO  CFG_DDR_SGMII_PHY_rpc196_TypeDef rpc196;                                             /*!< Offset: 0x710  */
  __IO  CFG_DDR_SGMII_PHY_rpc197_TypeDef rpc197;                                             /*!< Offset: 0x714  */
  __IO  CFG_DDR_SGMII_PHY_rpc198_TypeDef rpc198;                                             /*!< Offset: 0x718  */
  __IO  CFG_DDR_SGMII_PHY_rpc199_TypeDef rpc199;                                             /*!< Offset: 0x71c  */
  __IO  CFG_DDR_SGMII_PHY_rpc200_TypeDef rpc200;                                             /*!< Offset: 0x720  */
  __IO  CFG_DDR_SGMII_PHY_rpc201_TypeDef rpc201;                                             /*!< Offset: 0x724  */
  __IO  CFG_DDR_SGMII_PHY_rpc202_TypeDef rpc202;                                             /*!< Offset: 0x728  */
  __IO  CFG_DDR_SGMII_PHY_rpc203_TypeDef rpc203;                                             /*!< Offset: 0x72c  */
  __IO  CFG_DDR_SGMII_PHY_rpc204_TypeDef rpc204;                                             /*!< Offset: 0x730  */
  __IO  CFG_DDR_SGMII_PHY_rpc205_TypeDef rpc205;                                             /*!< Offset: 0x734  */
  __IO  CFG_DDR_SGMII_PHY_rpc206_TypeDef rpc206;                                             /*!< Offset: 0x738  */
  __IO  CFG_DDR_SGMII_PHY_rpc207_TypeDef rpc207;                                             /*!< Offset: 0x73c  */
  __IO  CFG_DDR_SGMII_PHY_rpc208_TypeDef rpc208;                                             /*!< Offset: 0x740  */
  __IO  CFG_DDR_SGMII_PHY_rpc209_TypeDef rpc209;                                             /*!< Offset: 0x744  */
  __IO  CFG_DDR_SGMII_PHY_rpc210_TypeDef rpc210;                                             /*!< Offset: 0x748  */
  __IO  CFG_DDR_SGMII_PHY_rpc211_TypeDef rpc211;                                             /*!< Offset: 0x74c  */
  __IO  CFG_DDR_SGMII_PHY_rpc212_TypeDef rpc212;                                             /*!< Offset: 0x750  */
  __IO  CFG_DDR_SGMII_PHY_rpc213_TypeDef rpc213;                                             /*!< Offset: 0x754  */
  __IO  CFG_DDR_SGMII_PHY_rpc214_TypeDef rpc214;                                             /*!< Offset: 0x758  */
  __IO  CFG_DDR_SGMII_PHY_rpc215_TypeDef rpc215;                                             /*!< Offset: 0x75c  */
  __IO  CFG_DDR_SGMII_PHY_rpc216_TypeDef rpc216;                                             /*!< Offset: 0x760  */
  __IO  CFG_DDR_SGMII_PHY_rpc217_TypeDef rpc217;                                             /*!< Offset: 0x764  */
  __IO  CFG_DDR_SGMII_PHY_rpc218_TypeDef rpc218;                                             /*!< Offset: 0x768  */
  __IO  CFG_DDR_SGMII_PHY_rpc219_TypeDef rpc219;                                             /*!< Offset: 0x76c  */
  __IO  CFG_DDR_SGMII_PHY_rpc220_TypeDef rpc220;                                             /*!< Offset: 0x770  */
  __IO  CFG_DDR_SGMII_PHY_rpc221_TypeDef rpc221;                                             /*!< Offset: 0x774  */
  __IO  CFG_DDR_SGMII_PHY_rpc222_TypeDef rpc222;                                             /*!< Offset: 0x778  */
  __IO  CFG_DDR_SGMII_PHY_rpc223_TypeDef rpc223;                                             /*!< Offset: 0x77c  */
  __IO  CFG_DDR_SGMII_PHY_rpc224_TypeDef rpc224;                                             /*!< Offset: 0x780  */
  __IO  CFG_DDR_SGMII_PHY_rpc225_TypeDef rpc225;                                             /*!< Offset: 0x784  */
  __IO  CFG_DDR_SGMII_PHY_rpc226_TypeDef rpc226;                                             /*!< Offset: 0x788  */
  __IO  CFG_DDR_SGMII_PHY_rpc227_TypeDef rpc227;                                             /*!< Offset: 0x78c  */
  __IO  CFG_DDR_SGMII_PHY_rpc228_TypeDef rpc228;                                             /*!< Offset: 0x790  */
  __IO  CFG_DDR_SGMII_PHY_rpc229_TypeDef rpc229;                                             /*!< Offset: 0x794  */
  __IO  CFG_DDR_SGMII_PHY_rpc230_TypeDef rpc230;                                             /*!< Offset: 0x798  */
  __IO  CFG_DDR_SGMII_PHY_rpc231_TypeDef rpc231;                                             /*!< Offset: 0x79c  */
  __IO  CFG_DDR_SGMII_PHY_rpc232_TypeDef rpc232;                                             /*!< Offset: 0x7a0  */
  __IO  CFG_DDR_SGMII_PHY_rpc233_TypeDef rpc233;                                             /*!< Offset: 0x7a4  */
  __IO  CFG_DDR_SGMII_PHY_rpc234_TypeDef rpc234;                                             /*!< Offset: 0x7a8  */
  __IO  CFG_DDR_SGMII_PHY_rpc235_TypeDef rpc235;                                             /*!< Offset: 0x7ac  */
  __IO  CFG_DDR_SGMII_PHY_rpc236_TypeDef rpc236;                                             /*!< Offset: 0x7b0  */
  __IO  CFG_DDR_SGMII_PHY_rpc237_TypeDef rpc237;                                             /*!< Offset: 0x7b4  */
  __IO  CFG_DDR_SGMII_PHY_rpc238_TypeDef rpc238;                                             /*!< Offset: 0x7b8  */
  __IO  CFG_DDR_SGMII_PHY_rpc239_TypeDef rpc239;                                             /*!< Offset: 0x7bc  */
  __IO  CFG_DDR_SGMII_PHY_rpc240_TypeDef rpc240;                                             /*!< Offset: 0x7c0  */
  __IO  CFG_DDR_SGMII_PHY_rpc241_TypeDef rpc241;                                             /*!< Offset: 0x7c4  */
  __IO  CFG_DDR_SGMII_PHY_rpc242_TypeDef rpc242;                                             /*!< Offset: 0x7c8  */
  __IO  CFG_DDR_SGMII_PHY_rpc243_TypeDef rpc243;                                             /*!< Offset: 0x7cc  */
  __IO  CFG_DDR_SGMII_PHY_rpc244_TypeDef rpc244;                                             /*!< Offset: 0x7d0  */
  __IO  CFG_DDR_SGMII_PHY_rpc245_TypeDef rpc245;                                             /*!< Offset: 0x7d4  */
  __IO  CFG_DDR_SGMII_PHY_rpc246_TypeDef rpc246;                                             /*!< Offset: 0x7d8  */
  __IO  CFG_DDR_SGMII_PHY_rpc247_TypeDef rpc247;                                             /*!< Offset: 0x7dc  */
  __IO  CFG_DDR_SGMII_PHY_rpc248_TypeDef rpc248;                                             /*!< Offset: 0x7e0  */
  __IO  CFG_DDR_SGMII_PHY_rpc249_TypeDef rpc249;                                             /*!< Offset: 0x7e4  */
  __IO  CFG_DDR_SGMII_PHY_rpc250_TypeDef rpc250;                                             /*!< Offset: 0x7e8  */
  __IO  CFG_DDR_SGMII_PHY_spio251_TypeDef spio251;                                            /*!< Offset: 0x7ec  */
  __IO  CFG_DDR_SGMII_PHY_spio252_TypeDef spio252;                                            /*!< Offset: 0x7f0  */
  __IO  CFG_DDR_SGMII_PHY_spio253_TypeDef spio253;                                            /*!< Offset: 0x7f4  */
  __I   uint32_t                       UNUSED_SPACE8[2];                                   /*!< Offset: 0x7f8 */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_TIP_TypeDef SOFT_RESET_TIP;                                     /*!< Offset: 0x800  */
  __IO  CFG_DDR_SGMII_PHY_rank_select_TypeDef rank_select;                                        /*!< Offset: 0x804  */
  __IO  CFG_DDR_SGMII_PHY_lane_select_TypeDef lane_select;                                        /*!< Offset: 0x808  */
  __IO  CFG_DDR_SGMII_PHY_training_skip_TypeDef training_skip;                                      /*!< Offset: 0x80c  */
  __IO  CFG_DDR_SGMII_PHY_training_start_TypeDef training_start;                                     /*!< Offset: 0x810  */
  __I   CFG_DDR_SGMII_PHY_training_status_TypeDef training_status;                                    /*!< Offset: 0x814  */
  __IO  CFG_DDR_SGMII_PHY_training_reset_TypeDef training_reset;                                     /*!< Offset: 0x818  */
  __I   CFG_DDR_SGMII_PHY_gt_err_comb_TypeDef gt_err_comb;                                        /*!< Offset: 0x81c  */
  __I   CFG_DDR_SGMII_PHY_gt_clk_sel_TypeDef gt_clk_sel;                                         /*!< Offset: 0x820  */
  __I   CFG_DDR_SGMII_PHY_gt_txdly_TypeDef gt_txdly;                                           /*!< Offset: 0x824  */
  __I   CFG_DDR_SGMII_PHY_gt_steps_180_TypeDef gt_steps_180;                                       /*!< Offset: 0x828  */
  __I   CFG_DDR_SGMII_PHY_gt_state_TypeDef gt_state;                                           /*!< Offset: 0x82c  */
  __I   CFG_DDR_SGMII_PHY_wl_delay_0_TypeDef wl_delay_0;                                         /*!< Offset: 0x830  */
  __I   CFG_DDR_SGMII_PHY_dq_dqs_err_done_TypeDef dq_dqs_err_done;                                    /*!< Offset: 0x834  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_window_TypeDef dqdqs_window;                                       /*!< Offset: 0x838  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_state_TypeDef dqdqs_state;                                        /*!< Offset: 0x83c  */
  __I   CFG_DDR_SGMII_PHY_delta0_TypeDef delta0;                                             /*!< Offset: 0x840  */
  __I   CFG_DDR_SGMII_PHY_delta1_TypeDef delta1;                                             /*!< Offset: 0x844  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status0_TypeDef dqdqs_status0;                                      /*!< Offset: 0x848  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status1_TypeDef dqdqs_status1;                                      /*!< Offset: 0x84c  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status2_TypeDef dqdqs_status2;                                      /*!< Offset: 0x850  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status3_TypeDef dqdqs_status3;                                      /*!< Offset: 0x854  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status4_TypeDef dqdqs_status4;                                      /*!< Offset: 0x858  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status5_TypeDef dqdqs_status5;                                      /*!< Offset: 0x85c  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_status6_TypeDef dqdqs_status6;                                      /*!< Offset: 0x860  */
  __I   CFG_DDR_SGMII_PHY_addcmd_status0_TypeDef addcmd_status0;                                     /*!< Offset: 0x864  */
  __I   CFG_DDR_SGMII_PHY_addcmd_status1_TypeDef addcmd_status1;                                     /*!< Offset: 0x868  */
  __I   CFG_DDR_SGMII_PHY_addcmd_answer_TypeDef addcmd_answer;                                      /*!< Offset: 0x86c  */
  __I   CFG_DDR_SGMII_PHY_bclksclk_answer_TypeDef bclksclk_answer;                                    /*!< Offset: 0x870  */
  __I   CFG_DDR_SGMII_PHY_dqdqs_wrcalib_offset_TypeDef dqdqs_wrcalib_offset;                               /*!< Offset: 0x874  */
  __IO  CFG_DDR_SGMII_PHY_expert_mode_en_TypeDef expert_mode_en;                                     /*!< Offset: 0x878  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_move_reg0_TypeDef expert_dlycnt_move_reg0;                            /*!< Offset: 0x87c  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_move_reg1_TypeDef expert_dlycnt_move_reg1;                            /*!< Offset: 0x880  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_direction_reg0_TypeDef expert_dlycnt_direction_reg0;                       /*!< Offset: 0x884  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_direction_reg1_TypeDef expert_dlycnt_direction_reg1;                       /*!< Offset: 0x888  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_load_reg0_TypeDef expert_dlycnt_load_reg0;                            /*!< Offset: 0x88c  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_load_reg1_TypeDef expert_dlycnt_load_reg1;                            /*!< Offset: 0x890  */
  __I   CFG_DDR_SGMII_PHY_expert_dlycnt_oor_reg0_TypeDef expert_dlycnt_oor_reg0;                             /*!< Offset: 0x894  */
  __I   CFG_DDR_SGMII_PHY_expert_dlycnt_oor_reg1_TypeDef expert_dlycnt_oor_reg1;                             /*!< Offset: 0x898  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_mv_rd_dly_reg_TypeDef expert_dlycnt_mv_rd_dly_reg;                        /*!< Offset: 0x89c  */
  __IO  CFG_DDR_SGMII_PHY_expert_dlycnt_pause_TypeDef expert_dlycnt_pause;                                /*!< Offset: 0x8a0  */
  __IO  CFG_DDR_SGMII_PHY_expert_pllcnt_TypeDef expert_pllcnt;                                      /*!< Offset: 0x8a4  */
  __I   CFG_DDR_SGMII_PHY_expert_dqlane_readback_TypeDef expert_dqlane_readback;                             /*!< Offset: 0x8a8  */
  __I   CFG_DDR_SGMII_PHY_expert_addcmd_ln_readback_TypeDef expert_addcmd_ln_readback;                          /*!< Offset: 0x8ac  */
  __IO  CFG_DDR_SGMII_PHY_expert_read_gate_controls_TypeDef expert_read_gate_controls;                          /*!< Offset: 0x8b0  */
  __I   CFG_DDR_SGMII_PHY_expert_dq_dqs_optimization0_TypeDef expert_dq_dqs_optimization0;                        /*!< Offset: 0x8b4  */
  __I   CFG_DDR_SGMII_PHY_expert_dq_dqs_optimization1_TypeDef expert_dq_dqs_optimization1;                        /*!< Offset: 0x8b8  */
  __IO  CFG_DDR_SGMII_PHY_expert_wrcalib_TypeDef expert_wrcalib;                                     /*!< Offset: 0x8bc  */
  __IO  CFG_DDR_SGMII_PHY_expert_calif_TypeDef expert_calif;                                       /*!< Offset: 0x8c0  */
  __I   CFG_DDR_SGMII_PHY_expert_calif_readback_TypeDef expert_calif_readback;                              /*!< Offset: 0x8c4  */
  __I   CFG_DDR_SGMII_PHY_expert_calif_readback1_TypeDef expert_calif_readback1;                             /*!< Offset: 0x8c8  */
  __IO  CFG_DDR_SGMII_PHY_expert_dfi_status_override_to_shim_TypeDef expert_dfi_status_override_to_shim;                 /*!< Offset: 0x8cc  */
  __IO  CFG_DDR_SGMII_PHY_tip_cfg_params_TypeDef tip_cfg_params;                                     /*!< Offset: 0x8d0  */
  __IO  CFG_DDR_SGMII_PHY_tip_vref_param_TypeDef tip_vref_param;                                     /*!< Offset: 0x8d4  */
  __IO  CFG_DDR_SGMII_PHY_lane_alignment_fifo_control_TypeDef lane_alignment_fifo_control;                        /*!< Offset: 0x8d8  */
  __I   uint32_t                       UNUSED_SPACE9[201];                                 /*!< Offset: 0x8dc */
  __IO  CFG_DDR_SGMII_PHY_SOFT_RESET_SGMII_TypeDef SOFT_RESET_SGMII;                                   /*!< Offset: 0xc00  */
  __IO  CFG_DDR_SGMII_PHY_SGMII_MODE_TypeDef SGMII_MODE;                                         /*!< Offset: 0xc04  */
  __IO  CFG_DDR_SGMII_PHY_PLL_CNTL_TypeDef PLL_CNTL;                                           /*!< Offset: 0xc08  */
  __IO  CFG_DDR_SGMII_PHY_CH0_CNTL_TypeDef CH0_CNTL;                                           /*!< Offset: 0xc0c  */
  __IO  CFG_DDR_SGMII_PHY_CH1_CNTL_TypeDef CH1_CNTL;                                           /*!< Offset: 0xc10  */
  __IO  CFG_DDR_SGMII_PHY_RECAL_CNTL_TypeDef RECAL_CNTL;                                         /*!< Offset: 0xc14  */
  __IO  CFG_DDR_SGMII_PHY_CLK_CNTL_TypeDef CLK_CNTL;                                           /*!< Offset: 0xc18  */
  __IO  CFG_DDR_SGMII_PHY_DYN_CNTL_TypeDef DYN_CNTL;                                           /*!< Offset: 0xc1c  */
  __IO  CFG_DDR_SGMII_PHY_PVT_STAT_TypeDef PVT_STAT;                                           /*!< Offset: 0xc20  */
  __IO  CFG_DDR_SGMII_PHY_SPARE_CNTL_TypeDef SPARE_CNTL;                                         /*!< Offset: 0xc24  */
  __I   CFG_DDR_SGMII_PHY_SPARE_STAT_TypeDef SPARE_STAT;                                         /*!< Offset: 0xc28  */
} CFG_DDR_SGMII_PHY_TypeDef;


/******************************************************************************/
/*              finish of   CFG_DDR_SGMII_PHY definitions                     */
/******************************************************************************/



#ifdef __cplusplus
}
#endif

#endif /* MSS_DDR_SGMII_PHY_DEFS_H_ */
