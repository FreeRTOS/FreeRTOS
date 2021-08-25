/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_hal.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief Register bit offsets and masks definitions for MPFS MSS DDR
 * This was generated directly from the RTL
 *
 */

#ifndef MSS_DDR_REGS_H_
#define MSS_DDR_REGS_H_

#include "../mss_sysreg.h"
#include "mss_ddr_sgmii_phy_defs.h"

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------*/
/*----------------------------------- DDR -----------------------------------*/
/*----------------------------------------------------------------------------*/


/*============================== CFG_DDR_SGMII_PHY definitions ===========================*/

/* see mss_ddr_sgmii_phy_defs.h */

/******************************************************************************/
/*              finish of   CFG_DDR_SGMII_PHY definitions                     */
/******************************************************************************/


/*============================== DDR_CSR_APB definitions ===========================*/

typedef union{                                                         /*!< CFG_MANUAL_ADDRESS_MAP register definition*/
  __IO  uint32_t                       CFG_MANUAL_ADDRESS_MAP;
  struct
  {
    __IO  uint32_t                       cfg_manual_address_map :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_MANUAL_ADDRESS_MAP_TypeDef;

typedef union{                                                         /*!< CFG_CHIPADDR_MAP register definition*/
  __IO  uint32_t                       CFG_CHIPADDR_MAP;
  struct
  {
    __IO  uint32_t                       cfg_chipaddr_map     :24;
    __I   uint32_t                       reserved             :8;
  } bitfield;
} DDR_CSR_APB_CFG_CHIPADDR_MAP_TypeDef;

typedef union{                                                         /*!< CFG_CIDADDR_MAP register definition*/
  __IO  uint32_t                       CFG_CIDADDR_MAP;
  struct
  {
    __IO  uint32_t                       cfg_cidaddr_map      :18;
    __I   uint32_t                       reserved             :14;
  } bitfield;
} DDR_CSR_APB_CFG_CIDADDR_MAP_TypeDef;

typedef union{                                                         /*!< CFG_MB_AUTOPCH_COL_BIT_POS_LOW register definition*/
  __IO  uint32_t                       CFG_MB_AUTOPCH_COL_BIT_POS_LOW;
  struct
  {
    __IO  uint32_t                       cfg_mb_autopch_col_bit_pos_low :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_MB_AUTOPCH_COL_BIT_POS_LOW_TypeDef;

typedef union{                                                         /*!< CFG_MB_AUTOPCH_COL_BIT_POS_HIGH register definition*/
  __IO  uint32_t                       CFG_MB_AUTOPCH_COL_BIT_POS_HIGH;
  struct
  {
    __IO  uint32_t                       cfg_mb_autopch_col_bit_pos_high :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_MB_AUTOPCH_COL_BIT_POS_HIGH_TypeDef;

typedef union{                                                         /*!< CFG_BANKADDR_MAP_0 register definition*/
  __IO  uint32_t                       CFG_BANKADDR_MAP_0;
  struct
  {
    __IO  uint32_t                       cfg_bankaddr_map_0   :32;
  } bitfield;
} DDR_CSR_APB_CFG_BANKADDR_MAP_0_TypeDef;

typedef union{                                                         /*!< CFG_BANKADDR_MAP_1 register definition*/
  __IO  uint32_t                       CFG_BANKADDR_MAP_1;
  struct
  {
    __IO  uint32_t                       cfg_bankaddr_map_1   :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_BANKADDR_MAP_1_TypeDef;

typedef union{                                                         /*!< CFG_ROWADDR_MAP_0 register definition*/
  __IO  uint32_t                       CFG_ROWADDR_MAP_0;
  struct
  {
    __IO  uint32_t                       cfg_rowaddr_map_0    :32;
  } bitfield;
} DDR_CSR_APB_CFG_ROWADDR_MAP_0_TypeDef;

typedef union{                                                         /*!< CFG_ROWADDR_MAP_1 register definition*/
  __IO  uint32_t                       CFG_ROWADDR_MAP_1;
  struct
  {
    __IO  uint32_t                       cfg_rowaddr_map_1    :32;
  } bitfield;
} DDR_CSR_APB_CFG_ROWADDR_MAP_1_TypeDef;

typedef union{                                                         /*!< CFG_ROWADDR_MAP_2 register definition*/
  __IO  uint32_t                       CFG_ROWADDR_MAP_2;
  struct
  {
    __IO  uint32_t                       cfg_rowaddr_map_2    :32;
  } bitfield;
} DDR_CSR_APB_CFG_ROWADDR_MAP_2_TypeDef;

typedef union{                                                         /*!< CFG_ROWADDR_MAP_3 register definition*/
  __IO  uint32_t                       CFG_ROWADDR_MAP_3;
  struct
  {
    __IO  uint32_t                       cfg_rowaddr_map_3    :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_ROWADDR_MAP_3_TypeDef;

typedef union{                                                         /*!< CFG_COLADDR_MAP_0 register definition*/
  __IO  uint32_t                       CFG_COLADDR_MAP_0;
  struct
  {
    __IO  uint32_t                       cfg_coladdr_map_0    :32;
  } bitfield;
} DDR_CSR_APB_CFG_COLADDR_MAP_0_TypeDef;

typedef union{                                                         /*!< CFG_COLADDR_MAP_1 register definition*/
  __IO  uint32_t                       CFG_COLADDR_MAP_1;
  struct
  {
    __IO  uint32_t                       cfg_coladdr_map_1    :32;
  } bitfield;
} DDR_CSR_APB_CFG_COLADDR_MAP_1_TypeDef;

typedef union{                                                         /*!< CFG_COLADDR_MAP_2 register definition*/
  __IO  uint32_t                       CFG_COLADDR_MAP_2;
  struct
  {
    __IO  uint32_t                       cfg_coladdr_map_2    :32;
  } bitfield;
} DDR_CSR_APB_CFG_COLADDR_MAP_2_TypeDef;

typedef union{                                                         /*!< CFG_VRCG_ENABLE register definition*/
  __IO  uint32_t                       CFG_VRCG_ENABLE;
  struct
  {
    __IO  uint32_t                       cfg_vrcg_enable      :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_VRCG_ENABLE_TypeDef;

typedef union{                                                         /*!< CFG_VRCG_DISABLE register definition*/
  __IO  uint32_t                       CFG_VRCG_DISABLE;
  struct
  {
    __IO  uint32_t                       cfg_vrcg_disable     :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_VRCG_DISABLE_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_LATENCY_SET register definition*/
  __IO  uint32_t                       CFG_WRITE_LATENCY_SET;
  struct
  {
    __IO  uint32_t                       cfg_write_latency_set :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_LATENCY_SET_TypeDef;

typedef union{                                                         /*!< CFG_THERMAL_OFFSET register definition*/
  __IO  uint32_t                       CFG_THERMAL_OFFSET;
  struct
  {
    __IO  uint32_t                       cfg_thermal_offset   :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_THERMAL_OFFSET_TypeDef;

typedef union{                                                         /*!< CFG_SOC_ODT register definition*/
  __IO  uint32_t                       CFG_SOC_ODT;
  struct
  {
    __IO  uint32_t                       cfg_soc_odt          :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_SOC_ODT_TypeDef;

typedef union{                                                         /*!< CFG_ODTE_CK register definition*/
  __IO  uint32_t                       CFG_ODTE_CK;
  struct
  {
    __IO  uint32_t                       cfg_odte_ck          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ODTE_CK_TypeDef;

typedef union{                                                         /*!< CFG_ODTE_CS register definition*/
  __IO  uint32_t                       CFG_ODTE_CS;
  struct
  {
    __IO  uint32_t                       cfg_odte_cs          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ODTE_CS_TypeDef;

typedef union{                                                         /*!< CFG_ODTD_CA register definition*/
  __IO  uint32_t                       CFG_ODTD_CA;
  struct
  {
    __IO  uint32_t                       cfg_odtd_ca          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ODTD_CA_TypeDef;

typedef union{                                                         /*!< CFG_LPDDR4_FSP_OP register definition*/
  __IO  uint32_t                       CFG_LPDDR4_FSP_OP;
  struct
  {
    __IO  uint32_t                       cfg_lpddr4_fsp_op    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_LPDDR4_FSP_OP_TypeDef;

typedef union{                                                         /*!< CFG_GENERATE_REFRESH_ON_SRX register definition*/
  __IO  uint32_t                       CFG_GENERATE_REFRESH_ON_SRX;
  struct
  {
    __IO  uint32_t                       cfg_generate_refresh_on_srx :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_GENERATE_REFRESH_ON_SRX_TypeDef;

typedef union{                                                         /*!< CFG_DBI_CL register definition*/
  __IO  uint32_t                       CFG_DBI_CL;
  struct
  {
    __IO  uint32_t                       cfg_dbi_cl           :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_DBI_CL_TypeDef;

typedef union{                                                         /*!< CFG_NON_DBI_CL register definition*/
  __IO  uint32_t                       CFG_NON_DBI_CL;
  struct
  {
    __IO  uint32_t                       cfg_non_dbi_cl       :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_NON_DBI_CL_TypeDef;

typedef union{                                                         /*!< INIT_FORCE_WRITE_DATA_0 register definition*/
  __IO  uint32_t                       INIT_FORCE_WRITE_DATA_0;
  struct
  {
    __IO  uint32_t                       init_force_write_data_0 :9;
    __I   uint32_t                       reserved             :23;
  } bitfield;
} DDR_CSR_APB_INIT_FORCE_WRITE_DATA_0_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_CRC register definition*/
  __IO  uint32_t                       CFG_WRITE_CRC;
  struct
  {
    __IO  uint32_t                       cfg_write_crc        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_CRC_TypeDef;

typedef union{                                                         /*!< CFG_MPR_READ_FORMAT register definition*/
  __IO  uint32_t                       CFG_MPR_READ_FORMAT;
  struct
  {
    __IO  uint32_t                       cfg_mpr_read_format  :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_MPR_READ_FORMAT_TypeDef;

typedef union{                                                         /*!< CFG_WR_CMD_LAT_CRC_DM register definition*/
  __IO  uint32_t                       CFG_WR_CMD_LAT_CRC_DM;
  struct
  {
    __IO  uint32_t                       cfg_wr_cmd_lat_crc_dm :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_WR_CMD_LAT_CRC_DM_TypeDef;

typedef union{                                                         /*!< CFG_FINE_GRAN_REF_MODE register definition*/
  __IO  uint32_t                       CFG_FINE_GRAN_REF_MODE;
  struct
  {
    __IO  uint32_t                       cfg_fine_gran_ref_mode :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_FINE_GRAN_REF_MODE_TypeDef;

typedef union{                                                         /*!< CFG_TEMP_SENSOR_READOUT register definition*/
  __IO  uint32_t                       CFG_TEMP_SENSOR_READOUT;
  struct
  {
    __IO  uint32_t                       cfg_temp_sensor_readout :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TEMP_SENSOR_READOUT_TypeDef;

typedef union{                                                         /*!< CFG_PER_DRAM_ADDR_EN register definition*/
  __IO  uint32_t                       CFG_PER_DRAM_ADDR_EN;
  struct
  {
    __IO  uint32_t                       cfg_per_dram_addr_en :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_PER_DRAM_ADDR_EN_TypeDef;

typedef union{                                                         /*!< CFG_GEARDOWN_MODE register definition*/
  __IO  uint32_t                       CFG_GEARDOWN_MODE;
  struct
  {
    __IO  uint32_t                       cfg_geardown_mode    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_GEARDOWN_MODE_TypeDef;

typedef union{                                                         /*!< CFG_WR_PREAMBLE register definition*/
  __IO  uint32_t                       CFG_WR_PREAMBLE;
  struct
  {
    __IO  uint32_t                       cfg_wr_preamble      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_WR_PREAMBLE_TypeDef;

typedef union{                                                         /*!< CFG_RD_PREAMBLE register definition*/
  __IO  uint32_t                       CFG_RD_PREAMBLE;
  struct
  {
    __IO  uint32_t                       cfg_rd_preamble      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RD_PREAMBLE_TypeDef;

typedef union{                                                         /*!< CFG_RD_PREAMB_TRN_MODE register definition*/
  __IO  uint32_t                       CFG_RD_PREAMB_TRN_MODE;
  struct
  {
    __IO  uint32_t                       cfg_rd_preamb_trn_mode :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RD_PREAMB_TRN_MODE_TypeDef;

typedef union{                                                         /*!< CFG_SR_ABORT register definition*/
  __IO  uint32_t                       CFG_SR_ABORT;
  struct
  {
    __IO  uint32_t                       cfg_sr_abort         :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_SR_ABORT_TypeDef;

typedef union{                                                         /*!< CFG_CS_TO_CMDADDR_LATENCY register definition*/
  __IO  uint32_t                       CFG_CS_TO_CMDADDR_LATENCY;
  struct
  {
    __IO  uint32_t                       cfg_cs_to_cmdaddr_latency :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_CS_TO_CMDADDR_LATENCY_TypeDef;

typedef union{                                                         /*!< CFG_INT_VREF_MON register definition*/
  __IO  uint32_t                       CFG_INT_VREF_MON;
  struct
  {
    __IO  uint32_t                       cfg_int_vref_mon     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_INT_VREF_MON_TypeDef;

typedef union{                                                         /*!< CFG_TEMP_CTRL_REF_MODE register definition*/
  __IO  uint32_t                       CFG_TEMP_CTRL_REF_MODE;
  struct
  {
    __IO  uint32_t                       cfg_temp_ctrl_ref_mode :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TEMP_CTRL_REF_MODE_TypeDef;

typedef union{                                                         /*!< CFG_TEMP_CTRL_REF_RANGE register definition*/
  __IO  uint32_t                       CFG_TEMP_CTRL_REF_RANGE;
  struct
  {
    __IO  uint32_t                       cfg_temp_ctrl_ref_range :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TEMP_CTRL_REF_RANGE_TypeDef;

typedef union{                                                         /*!< CFG_MAX_PWR_DOWN_MODE register definition*/
  __IO  uint32_t                       CFG_MAX_PWR_DOWN_MODE;
  struct
  {
    __IO  uint32_t                       cfg_max_pwr_down_mode :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_MAX_PWR_DOWN_MODE_TypeDef;

typedef union{                                                         /*!< CFG_READ_DBI register definition*/
  __IO  uint32_t                       CFG_READ_DBI;
  struct
  {
    __IO  uint32_t                       cfg_read_dbi         :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_READ_DBI_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_DBI register definition*/
  __IO  uint32_t                       CFG_WRITE_DBI;
  struct
  {
    __IO  uint32_t                       cfg_write_dbi        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_DBI_TypeDef;

typedef union{                                                         /*!< CFG_DATA_MASK register definition*/
  __IO  uint32_t                       CFG_DATA_MASK;
  struct
  {
    __IO  uint32_t                       cfg_data_mask        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DATA_MASK_TypeDef;

typedef union{                                                         /*!< CFG_CA_PARITY_PERSIST_ERR register definition*/
  __IO  uint32_t                       CFG_CA_PARITY_PERSIST_ERR;
  struct
  {
    __IO  uint32_t                       cfg_ca_parity_persist_err :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CA_PARITY_PERSIST_ERR_TypeDef;

typedef union{                                                         /*!< CFG_RTT_PARK register definition*/
  __IO  uint32_t                       CFG_RTT_PARK;
  struct
  {
    __IO  uint32_t                       cfg_rtt_park         :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_RTT_PARK_TypeDef;

typedef union{                                                         /*!< CFG_ODT_INBUF_4_PD register definition*/
  __IO  uint32_t                       CFG_ODT_INBUF_4_PD;
  struct
  {
    __IO  uint32_t                       cfg_odt_inbuf_4_pd   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_INBUF_4_PD_TypeDef;

typedef union{                                                         /*!< CFG_CA_PARITY_ERR_STATUS register definition*/
  __IO  uint32_t                       CFG_CA_PARITY_ERR_STATUS;
  struct
  {
    __IO  uint32_t                       cfg_ca_parity_err_status :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CA_PARITY_ERR_STATUS_TypeDef;

typedef union{                                                         /*!< CFG_CRC_ERROR_CLEAR register definition*/
  __IO  uint32_t                       CFG_CRC_ERROR_CLEAR;
  struct
  {
    __IO  uint32_t                       cfg_crc_error_clear  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CRC_ERROR_CLEAR_TypeDef;

typedef union{                                                         /*!< CFG_CA_PARITY_LATENCY register definition*/
  __IO  uint32_t                       CFG_CA_PARITY_LATENCY;
  struct
  {
    __IO  uint32_t                       cfg_ca_parity_latency :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_CA_PARITY_LATENCY_TypeDef;

typedef union{                                                         /*!< CFG_CCD_S register definition*/
  __IO  uint32_t                       CFG_CCD_S;
  struct
  {
    __IO  uint32_t                       cfg_ccd_s            :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_CCD_S_TypeDef;

typedef union{                                                         /*!< CFG_CCD_L register definition*/
  __IO  uint32_t                       CFG_CCD_L;
  struct
  {
    __IO  uint32_t                       cfg_ccd_l            :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_CCD_L_TypeDef;

typedef union{                                                         /*!< CFG_VREFDQ_TRN_ENABLE register definition*/
  __IO  uint32_t                       CFG_VREFDQ_TRN_ENABLE;
  struct
  {
    __IO  uint32_t                       cfg_vrefdq_trn_enable :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_VREFDQ_TRN_ENABLE_TypeDef;

typedef union{                                                         /*!< CFG_VREFDQ_TRN_RANGE register definition*/
  __IO  uint32_t                       CFG_VREFDQ_TRN_RANGE;
  struct
  {
    __IO  uint32_t                       cfg_vrefdq_trn_range :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_VREFDQ_TRN_RANGE_TypeDef;

typedef union{                                                         /*!< CFG_VREFDQ_TRN_VALUE register definition*/
  __IO  uint32_t                       CFG_VREFDQ_TRN_VALUE;
  struct
  {
    __IO  uint32_t                       cfg_vrefdq_trn_value :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_VREFDQ_TRN_VALUE_TypeDef;

typedef union{                                                         /*!< CFG_RRD_S register definition*/
  __IO  uint32_t                       CFG_RRD_S;
  struct
  {
    __IO  uint32_t                       cfg_rrd_s            :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_RRD_S_TypeDef;

typedef union{                                                         /*!< CFG_RRD_L register definition*/
  __IO  uint32_t                       CFG_RRD_L;
  struct
  {
    __IO  uint32_t                       cfg_rrd_l            :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_RRD_L_TypeDef;

typedef union{                                                         /*!< CFG_WTR_S register definition*/
  __IO  uint32_t                       CFG_WTR_S;
  struct
  {
    __IO  uint32_t                       cfg_wtr_s            :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_WTR_S_TypeDef;

typedef union{                                                         /*!< CFG_WTR_L register definition*/
  __IO  uint32_t                       CFG_WTR_L;
  struct
  {
    __IO  uint32_t                       cfg_wtr_l            :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_WTR_L_TypeDef;

typedef union{                                                         /*!< CFG_WTR_S_CRC_DM register definition*/
  __IO  uint32_t                       CFG_WTR_S_CRC_DM;
  struct
  {
    __IO  uint32_t                       cfg_wtr_s_crc_dm     :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_WTR_S_CRC_DM_TypeDef;

typedef union{                                                         /*!< CFG_WTR_L_CRC_DM register definition*/
  __IO  uint32_t                       CFG_WTR_L_CRC_DM;
  struct
  {
    __IO  uint32_t                       cfg_wtr_l_crc_dm     :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_WTR_L_CRC_DM_TypeDef;

typedef union{                                                         /*!< CFG_WR_CRC_DM register definition*/
  __IO  uint32_t                       CFG_WR_CRC_DM;
  struct
  {
    __IO  uint32_t                       cfg_wr_crc_dm        :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_WR_CRC_DM_TypeDef;

typedef union{                                                         /*!< CFG_RFC1 register definition*/
  __IO  uint32_t                       CFG_RFC1;
  struct
  {
    __IO  uint32_t                       cfg_rfc1             :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC1_TypeDef;

typedef union{                                                         /*!< CFG_RFC2 register definition*/
  __IO  uint32_t                       CFG_RFC2;
  struct
  {
    __IO  uint32_t                       cfg_rfc2             :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC2_TypeDef;

typedef union{                                                         /*!< CFG_RFC4 register definition*/
  __IO  uint32_t                       CFG_RFC4;
  struct
  {
    __IO  uint32_t                       cfg_rfc4             :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC4_TypeDef;

typedef union{                                                         /*!< CFG_NIBBLE_DEVICES register definition*/
  __IO  uint32_t                       CFG_NIBBLE_DEVICES;
  struct
  {
    __IO  uint32_t                       cfg_nibble_devices   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_NIBBLE_DEVICES_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS0_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS0_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs0_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS0_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS0_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS0_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs0_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS0_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS1_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS1_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs1_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS1_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS1_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS1_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs1_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS1_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS2_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS2_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs2_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS2_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS2_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS2_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs2_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS2_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS3_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS3_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs3_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS3_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS3_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS3_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs3_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS3_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS4_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS4_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs4_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS4_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS4_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS4_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs4_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS4_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS5_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS5_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs5_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS5_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS5_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS5_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs5_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS5_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS6_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS6_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs6_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS6_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS6_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS6_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs6_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS6_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS7_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS7_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs7_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS7_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS7_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS7_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs7_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS7_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS8_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS8_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs8_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS8_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS8_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS8_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs8_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS8_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS9_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS9_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs9_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS9_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS9_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS9_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs9_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS9_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS10_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS10_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs10_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS10_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS10_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS10_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs10_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS10_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS11_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS11_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs11_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS11_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS11_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS11_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs11_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS11_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS12_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS12_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs12_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS12_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS12_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS12_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs12_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS12_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS13_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS13_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs13_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS13_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS13_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS13_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs13_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS13_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS14_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS14_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs14_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS14_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS14_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS14_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs14_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS14_1_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS15_0 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS15_0;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs15_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS15_0_TypeDef;

typedef union{                                                         /*!< CFG_BIT_MAP_INDEX_CS15_1 register definition*/
  __IO  uint32_t                       CFG_BIT_MAP_INDEX_CS15_1;
  struct
  {
    __IO  uint32_t                       cfg_bit_map_index_cs15_1 :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS15_1_TypeDef;

typedef union{                                                         /*!< CFG_NUM_LOGICAL_RANKS_PER_3DS register definition*/
  __IO  uint32_t                       CFG_NUM_LOGICAL_RANKS_PER_3DS;
  struct
  {
    __IO  uint32_t                       cfg_num_logical_ranks_per_3ds :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_NUM_LOGICAL_RANKS_PER_3DS_TypeDef;

typedef union{                                                         /*!< CFG_RFC_DLR1 register definition*/
  __IO  uint32_t                       CFG_RFC_DLR1;
  struct
  {
    __IO  uint32_t                       cfg_rfc_dlr1         :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC_DLR1_TypeDef;

typedef union{                                                         /*!< CFG_RFC_DLR2 register definition*/
  __IO  uint32_t                       CFG_RFC_DLR2;
  struct
  {
    __IO  uint32_t                       cfg_rfc_dlr2         :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC_DLR2_TypeDef;

typedef union{                                                         /*!< CFG_RFC_DLR4 register definition*/
  __IO  uint32_t                       CFG_RFC_DLR4;
  struct
  {
    __IO  uint32_t                       cfg_rfc_dlr4         :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC_DLR4_TypeDef;

typedef union{                                                         /*!< CFG_RRD_DLR register definition*/
  __IO  uint32_t                       CFG_RRD_DLR;
  struct
  {
    __IO  uint32_t                       cfg_rrd_dlr          :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_RRD_DLR_TypeDef;

typedef union{                                                         /*!< CFG_FAW_DLR register definition*/
  __IO  uint32_t                       CFG_FAW_DLR;
  struct
  {
    __IO  uint32_t                       cfg_faw_dlr          :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_FAW_DLR_TypeDef;

typedef union{                                                         /*!< CFG_ADVANCE_ACTIVATE_READY register definition*/
  __IO  uint32_t                       CFG_ADVANCE_ACTIVATE_READY;
  struct
  {
    __IO  uint32_t                       cfg_advance_activate_ready :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_ADVANCE_ACTIVATE_READY_TypeDef;

typedef union{                                                         /*!< CTRLR_SOFT_RESET_N register definition*/
  __IO  uint32_t                       CTRLR_SOFT_RESET_N;
  struct
  {
    __IO  uint32_t                       ctrlr_soft_reset_n   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CTRLR_SOFT_RESET_N_TypeDef;

typedef union{                                                         /*!< CFG_LOOKAHEAD_PCH register definition*/
  __IO  uint32_t                       CFG_LOOKAHEAD_PCH;
  struct
  {
    __IO  uint32_t                       cfg_lookahead_pch    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_LOOKAHEAD_PCH_TypeDef;

typedef union{                                                         /*!< CFG_LOOKAHEAD_ACT register definition*/
  __IO  uint32_t                       CFG_LOOKAHEAD_ACT;
  struct
  {
    __IO  uint32_t                       cfg_lookahead_act    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_LOOKAHEAD_ACT_TypeDef;

typedef union{                                                         /*!< INIT_AUTOINIT_DISABLE register definition*/
  __IO  uint32_t                       INIT_AUTOINIT_DISABLE;
  struct
  {
    __IO  uint32_t                       init_autoinit_disable :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_AUTOINIT_DISABLE_TypeDef;

typedef union{                                                         /*!< INIT_FORCE_RESET register definition*/
  __IO  uint32_t                       INIT_FORCE_RESET;
  struct
  {
    __IO  uint32_t                       init_force_reset     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_FORCE_RESET_TypeDef;

typedef union{                                                         /*!< INIT_GEARDOWN_EN register definition*/
  __IO  uint32_t                       INIT_GEARDOWN_EN;
  struct
  {
    __IO  uint32_t                       init_geardown_en     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_GEARDOWN_EN_TypeDef;

typedef union{                                                         /*!< INIT_DISABLE_CKE register definition*/
  __IO  uint32_t                       INIT_DISABLE_CKE;
  struct
  {
    __IO  uint32_t                       init_disable_cke     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_DISABLE_CKE_TypeDef;

typedef union{                                                         /*!< INIT_CS register definition*/
  __IO  uint32_t                       INIT_CS;
  struct
  {
    __IO  uint32_t                       init_cs              :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_CS_TypeDef;

typedef union{                                                         /*!< INIT_PRECHARGE_ALL register definition*/
  __IO  uint32_t                       INIT_PRECHARGE_ALL;
  struct
  {
    __IO  uint32_t                       init_precharge_all   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_PRECHARGE_ALL_TypeDef;

typedef union{                                                         /*!< INIT_REFRESH register definition*/
  __IO  uint32_t                       INIT_REFRESH;
  struct
  {
    __IO  uint32_t                       init_refresh         :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_REFRESH_TypeDef;

typedef union{                                                         /*!< INIT_ZQ_CAL_REQ register definition*/
  __IO  uint32_t                       INIT_ZQ_CAL_REQ;
  struct
  {
    __IO  uint32_t                       init_zq_cal_req      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_ZQ_CAL_REQ_TypeDef;

typedef union{                                                         /*!< INIT_ACK register definition*/
  __I   uint32_t                       INIT_ACK;
  struct
  {
    __I   uint32_t                       init_ack             :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_ACK_TypeDef;

typedef union{                                                         /*!< CFG_BL register definition*/
  __IO  uint32_t                       CFG_BL;
  struct
  {
    __IO  uint32_t                       cfg_bl               :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_BL_TypeDef;

typedef union{                                                         /*!< CTRLR_INIT register definition*/
  __IO  uint32_t                       CTRLR_INIT;
  struct
  {
    __IO  uint32_t                       ctrlr_init           :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CTRLR_INIT_TypeDef;

typedef union{                                                         /*!< CTRLR_INIT_DONE register definition*/
  __I   uint32_t                       CTRLR_INIT_DONE;
  struct
  {
    __I   uint32_t                       ctrlr_init_done      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CTRLR_INIT_DONE_TypeDef;

typedef union{                                                         /*!< CFG_AUTO_REF_EN register definition*/
  __IO  uint32_t                       CFG_AUTO_REF_EN;
  struct
  {
    __IO  uint32_t                       cfg_auto_ref_en      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_AUTO_REF_EN_TypeDef;

typedef union{                                                         /*!< CFG_RAS register definition*/
  __IO  uint32_t                       CFG_RAS;
  struct
  {
    __IO  uint32_t                       cfg_ras              :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_RAS_TypeDef;

typedef union{                                                         /*!< CFG_RCD register definition*/
  __IO  uint32_t                       CFG_RCD;
  struct
  {
    __IO  uint32_t                       cfg_rcd              :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_RCD_TypeDef;

typedef union{                                                         /*!< CFG_RRD register definition*/
  __IO  uint32_t                       CFG_RRD;
  struct
  {
    __IO  uint32_t                       cfg_rrd              :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_RRD_TypeDef;

typedef union{                                                         /*!< CFG_RP register definition*/
  __IO  uint32_t                       CFG_RP;
  struct
  {
    __IO  uint32_t                       cfg_rp               :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_RP_TypeDef;

typedef union{                                                         /*!< CFG_RC register definition*/
  __IO  uint32_t                       CFG_RC;
  struct
  {
    __IO  uint32_t                       cfg_rc               :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_RC_TypeDef;

typedef union{                                                         /*!< CFG_FAW register definition*/
  __IO  uint32_t                       CFG_FAW;
  struct
  {
    __IO  uint32_t                       cfg_faw              :9;
    __I   uint32_t                       reserved             :23;
  } bitfield;
} DDR_CSR_APB_CFG_FAW_TypeDef;

typedef union{                                                         /*!< CFG_RFC register definition*/
  __IO  uint32_t                       CFG_RFC;
  struct
  {
    __IO  uint32_t                       cfg_rfc              :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_RFC_TypeDef;

typedef union{                                                         /*!< CFG_RTP register definition*/
  __IO  uint32_t                       CFG_RTP;
  struct
  {
    __IO  uint32_t                       cfg_rtp              :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_RTP_TypeDef;

typedef union{                                                         /*!< CFG_WR register definition*/
  __IO  uint32_t                       CFG_WR;
  struct
  {
    __IO  uint32_t                       cfg_wr               :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_WR_TypeDef;

typedef union{                                                         /*!< CFG_WTR register definition*/
  __IO  uint32_t                       CFG_WTR;
  struct
  {
    __IO  uint32_t                       cfg_wtr              :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_WTR_TypeDef;

typedef union{                                                         /*!< CFG_PASR register definition*/
  __IO  uint32_t                       CFG_PASR;
  struct
  {
    __IO  uint32_t                       cfg_pasr             :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_PASR_TypeDef;

typedef union{                                                         /*!< CFG_XP register definition*/
  __IO  uint32_t                       CFG_XP;
  struct
  {
    __IO  uint32_t                       cfg_xp               :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_XP_TypeDef;

typedef union{                                                         /*!< CFG_XSR register definition*/
  __IO  uint32_t                       CFG_XSR;
  struct
  {
    __IO  uint32_t                       cfg_xsr              :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_XSR_TypeDef;

typedef union{                                                         /*!< CFG_CL register definition*/
  __IO  uint32_t                       CFG_CL;
  struct
  {
    __IO  uint32_t                       cfg_cl               :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_CL_TypeDef;

typedef union{                                                         /*!< CFG_READ_TO_WRITE register definition*/
  __IO  uint32_t                       CFG_READ_TO_WRITE;
  struct
  {
    __IO  uint32_t                       cfg_read_to_write    :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_READ_TO_WRITE_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_TO_WRITE register definition*/
  __IO  uint32_t                       CFG_WRITE_TO_WRITE;
  struct
  {
    __IO  uint32_t                       cfg_write_to_write   :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_TO_WRITE_TypeDef;

typedef union{                                                         /*!< CFG_READ_TO_READ register definition*/
  __IO  uint32_t                       CFG_READ_TO_READ;
  struct
  {
    __IO  uint32_t                       cfg_read_to_read     :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_READ_TO_READ_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_TO_READ register definition*/
  __IO  uint32_t                       CFG_WRITE_TO_READ;
  struct
  {
    __IO  uint32_t                       cfg_write_to_read    :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_TO_READ_TypeDef;

typedef union{                                                         /*!< CFG_READ_TO_WRITE_ODT register definition*/
  __IO  uint32_t                       CFG_READ_TO_WRITE_ODT;
  struct
  {
    __IO  uint32_t                       cfg_read_to_write_odt :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_READ_TO_WRITE_ODT_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_TO_WRITE_ODT register definition*/
  __IO  uint32_t                       CFG_WRITE_TO_WRITE_ODT;
  struct
  {
    __IO  uint32_t                       cfg_write_to_write_odt :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_TO_WRITE_ODT_TypeDef;

typedef union{                                                         /*!< CFG_READ_TO_READ_ODT register definition*/
  __IO  uint32_t                       CFG_READ_TO_READ_ODT;
  struct
  {
    __IO  uint32_t                       cfg_read_to_read_odt :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_READ_TO_READ_ODT_TypeDef;

typedef union{                                                         /*!< CFG_WRITE_TO_READ_ODT register definition*/
  __IO  uint32_t                       CFG_WRITE_TO_READ_ODT;
  struct
  {
    __IO  uint32_t                       cfg_write_to_read_odt :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_WRITE_TO_READ_ODT_TypeDef;

typedef union{                                                         /*!< CFG_MIN_READ_IDLE register definition*/
  __IO  uint32_t                       CFG_MIN_READ_IDLE;
  struct
  {
    __IO  uint32_t                       cfg_min_read_idle    :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_MIN_READ_IDLE_TypeDef;

typedef union{                                                         /*!< CFG_MRD register definition*/
  __IO  uint32_t                       CFG_MRD;
  struct
  {
    __IO  uint32_t                       cfg_mrd              :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_MRD_TypeDef;

typedef union{                                                         /*!< CFG_BT register definition*/
  __IO  uint32_t                       CFG_BT;
  struct
  {
    __IO  uint32_t                       cfg_bt               :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_BT_TypeDef;

typedef union{                                                         /*!< CFG_DS register definition*/
  __IO  uint32_t                       CFG_DS;
  struct
  {
    __IO  uint32_t                       cfg_ds               :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_DS_TypeDef;

typedef union{                                                         /*!< CFG_QOFF register definition*/
  __IO  uint32_t                       CFG_QOFF;
  struct
  {
    __IO  uint32_t                       cfg_qoff             :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_QOFF_TypeDef;

typedef union{                                                         /*!< CFG_RTT register definition*/
  __IO  uint32_t                       CFG_RTT;
  struct
  {
    __IO  uint32_t                       cfg_rtt              :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_RTT_TypeDef;

typedef union{                                                         /*!< CFG_DLL_DISABLE register definition*/
  __IO  uint32_t                       CFG_DLL_DISABLE;
  struct
  {
    __IO  uint32_t                       cfg_dll_disable      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DLL_DISABLE_TypeDef;

typedef union{                                                         /*!< CFG_REF_PER register definition*/
  __IO  uint32_t                       CFG_REF_PER;
  struct
  {
    __IO  uint32_t                       cfg_ref_per          :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_CFG_REF_PER_TypeDef;

typedef union{                                                         /*!< CFG_STARTUP_DELAY register definition*/
  __IO  uint32_t                       CFG_STARTUP_DELAY;
  struct
  {
    __IO  uint32_t                       cfg_startup_delay    :19;
    __I   uint32_t                       reserved             :13;
  } bitfield;
} DDR_CSR_APB_CFG_STARTUP_DELAY_TypeDef;

typedef union{                                                         /*!< CFG_MEM_COLBITS register definition*/
  __IO  uint32_t                       CFG_MEM_COLBITS;
  struct
  {
    __IO  uint32_t                       cfg_mem_colbits      :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_COLBITS_TypeDef;

typedef union{                                                         /*!< CFG_MEM_ROWBITS register definition*/
  __IO  uint32_t                       CFG_MEM_ROWBITS;
  struct
  {
    __IO  uint32_t                       cfg_mem_rowbits      :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_ROWBITS_TypeDef;

typedef union{                                                         /*!< CFG_MEM_BANKBITS register definition*/
  __IO  uint32_t                       CFG_MEM_BANKBITS;
  struct
  {
    __IO  uint32_t                       cfg_mem_bankbits     :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_BANKBITS_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS0 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS0;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs0   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS0_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS1 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS1;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs1   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS1_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS2 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS2;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs2   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS2_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS3 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS3;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs3   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS3_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS4 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS4;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs4   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS4_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS5 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS5;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs5   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS5_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS6 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS6;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs6   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS6_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_MAP_CS7 register definition*/
  __IO  uint32_t                       CFG_ODT_RD_MAP_CS7;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_map_cs7   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_MAP_CS7_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS0 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS0;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs0   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS0_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS1 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS1;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs1   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS1_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS2 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS2;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs2   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS2_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS3 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS3;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs3   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS3_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS4 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS4;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs4   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS4_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS5 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS5;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs5   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS5_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS6 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS6;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs6   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS6_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_MAP_CS7 register definition*/
  __IO  uint32_t                       CFG_ODT_WR_MAP_CS7;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_map_cs7   :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_MAP_CS7_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_TURN_ON register definition*/
  __IO  uint32_t                       CFG_ODT_RD_TURN_ON;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_turn_on   :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_TURN_ON_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_TURN_ON register definition*/
  __IO  uint32_t                       CFG_ODT_WR_TURN_ON;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_turn_on   :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_TURN_ON_TypeDef;

typedef union{                                                         /*!< CFG_ODT_RD_TURN_OFF register definition*/
  __IO  uint32_t                       CFG_ODT_RD_TURN_OFF;
  struct
  {
    __IO  uint32_t                       cfg_odt_rd_turn_off  :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_RD_TURN_OFF_TypeDef;

typedef union{                                                         /*!< CFG_ODT_WR_TURN_OFF register definition*/
  __IO  uint32_t                       CFG_ODT_WR_TURN_OFF;
  struct
  {
    __IO  uint32_t                       cfg_odt_wr_turn_off  :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_WR_TURN_OFF_TypeDef;

typedef union{                                                         /*!< CFG_EMR3 register definition*/
  __IO  uint32_t                       CFG_EMR3;
  struct
  {
    __IO  uint32_t                       cfg_emr3             :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_CFG_EMR3_TypeDef;

typedef union{                                                         /*!< CFG_TWO_T register definition*/
  __IO  uint32_t                       CFG_TWO_T;
  struct
  {
    __IO  uint32_t                       cfg_two_t            :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TWO_T_TypeDef;

typedef union{                                                         /*!< CFG_TWO_T_SEL_CYCLE register definition*/
  __IO  uint32_t                       CFG_TWO_T_SEL_CYCLE;
  struct
  {
    __IO  uint32_t                       cfg_two_t_sel_cycle  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TWO_T_SEL_CYCLE_TypeDef;

typedef union{                                                         /*!< CFG_REGDIMM register definition*/
  __IO  uint32_t                       CFG_REGDIMM;
  struct
  {
    __IO  uint32_t                       cfg_regdimm          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_REGDIMM_TypeDef;

typedef union{                                                         /*!< CFG_MOD register definition*/
  __IO  uint32_t                       CFG_MOD;
  struct
  {
    __IO  uint32_t                       cfg_mod              :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_MOD_TypeDef;

typedef union{                                                         /*!< CFG_XS register definition*/
  __IO  uint32_t                       CFG_XS;
  struct
  {
    __IO  uint32_t                       cfg_xs               :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_XS_TypeDef;

typedef union{                                                         /*!< CFG_XSDLL register definition*/
  __IO  uint32_t                       CFG_XSDLL;
  struct
  {
    __IO  uint32_t                       cfg_xsdll            :11;
    __I   uint32_t                       reserved             :21;
  } bitfield;
} DDR_CSR_APB_CFG_XSDLL_TypeDef;

typedef union{                                                         /*!< CFG_XPR register definition*/
  __IO  uint32_t                       CFG_XPR;
  struct
  {
    __IO  uint32_t                       cfg_xpr              :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_XPR_TypeDef;

typedef union{                                                         /*!< CFG_AL_MODE register definition*/
  __IO  uint32_t                       CFG_AL_MODE;
  struct
  {
    __IO  uint32_t                       cfg_al_mode          :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_AL_MODE_TypeDef;

typedef union{                                                         /*!< CFG_CWL register definition*/
  __IO  uint32_t                       CFG_CWL;
  struct
  {
    __IO  uint32_t                       cfg_cwl              :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_CWL_TypeDef;

typedef union{                                                         /*!< CFG_BL_MODE register definition*/
  __IO  uint32_t                       CFG_BL_MODE;
  struct
  {
    __IO  uint32_t                       cfg_bl_mode          :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_BL_MODE_TypeDef;

typedef union{                                                         /*!< CFG_TDQS register definition*/
  __IO  uint32_t                       CFG_TDQS;
  struct
  {
    __IO  uint32_t                       cfg_tdqs             :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TDQS_TypeDef;

typedef union{                                                         /*!< CFG_RTT_WR register definition*/
  __IO  uint32_t                       CFG_RTT_WR;
  struct
  {
    __IO  uint32_t                       cfg_rtt_wr           :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_RTT_WR_TypeDef;

typedef union{                                                         /*!< CFG_LP_ASR register definition*/
  __IO  uint32_t                       CFG_LP_ASR;
  struct
  {
    __IO  uint32_t                       cfg_lp_asr           :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_LP_ASR_TypeDef;

typedef union{                                                         /*!< CFG_AUTO_SR register definition*/
  __IO  uint32_t                       CFG_AUTO_SR;
  struct
  {
    __IO  uint32_t                       cfg_auto_sr          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_AUTO_SR_TypeDef;

typedef union{                                                         /*!< CFG_SRT register definition*/
  __IO  uint32_t                       CFG_SRT;
  struct
  {
    __IO  uint32_t                       cfg_srt              :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_SRT_TypeDef;

typedef union{                                                         /*!< CFG_ADDR_MIRROR register definition*/
  __IO  uint32_t                       CFG_ADDR_MIRROR;
  struct
  {
    __IO  uint32_t                       cfg_addr_mirror      :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ADDR_MIRROR_TypeDef;

typedef union{                                                         /*!< CFG_ZQ_CAL_TYPE register definition*/
  __IO  uint32_t                       CFG_ZQ_CAL_TYPE;
  struct
  {
    __IO  uint32_t                       cfg_zq_cal_type      :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_ZQ_CAL_TYPE_TypeDef;

typedef union{                                                         /*!< CFG_ZQ_CAL_PER register definition*/
  __IO  uint32_t                       CFG_ZQ_CAL_PER;
  struct
  {
    __IO  uint32_t                       cfg_zq_cal_per       :32;
  } bitfield;
} DDR_CSR_APB_CFG_ZQ_CAL_PER_TypeDef;

typedef union{                                                         /*!< CFG_AUTO_ZQ_CAL_EN register definition*/
  __IO  uint32_t                       CFG_AUTO_ZQ_CAL_EN;
  struct
  {
    __IO  uint32_t                       cfg_auto_zq_cal_en   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_AUTO_ZQ_CAL_EN_TypeDef;

typedef union{                                                         /*!< CFG_MEMORY_TYPE register definition*/
  __IO  uint32_t                       CFG_MEMORY_TYPE;
  struct
  {
    __IO  uint32_t                       cfg_memory_type      :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_CFG_MEMORY_TYPE_TypeDef;

typedef union{                                                         /*!< CFG_ONLY_SRANK_CMDS register definition*/
  __IO  uint32_t                       CFG_ONLY_SRANK_CMDS;
  struct
  {
    __IO  uint32_t                       cfg_only_srank_cmds  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ONLY_SRANK_CMDS_TypeDef;

typedef union{                                                         /*!< CFG_NUM_RANKS register definition*/
  __IO  uint32_t                       CFG_NUM_RANKS;
  struct
  {
    __IO  uint32_t                       cfg_num_ranks        :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_NUM_RANKS_TypeDef;

typedef union{                                                         /*!< CFG_QUAD_RANK register definition*/
  __IO  uint32_t                       CFG_QUAD_RANK;
  struct
  {
    __IO  uint32_t                       cfg_quad_rank        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_QUAD_RANK_TypeDef;

typedef union{                                                         /*!< CFG_EARLY_RANK_TO_WR_START register definition*/
  __IO  uint32_t                       CFG_EARLY_RANK_TO_WR_START;
  struct
  {
    __IO  uint32_t                       cfg_early_rank_to_wr_start :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_EARLY_RANK_TO_WR_START_TypeDef;

typedef union{                                                         /*!< CFG_EARLY_RANK_TO_RD_START register definition*/
  __IO  uint32_t                       CFG_EARLY_RANK_TO_RD_START;
  struct
  {
    __IO  uint32_t                       cfg_early_rank_to_rd_start :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_EARLY_RANK_TO_RD_START_TypeDef;

typedef union{                                                         /*!< CFG_PASR_BANK register definition*/
  __IO  uint32_t                       CFG_PASR_BANK;
  struct
  {
    __IO  uint32_t                       cfg_pasr_bank        :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_PASR_BANK_TypeDef;

typedef union{                                                         /*!< CFG_PASR_SEG register definition*/
  __IO  uint32_t                       CFG_PASR_SEG;
  struct
  {
    __IO  uint32_t                       cfg_pasr_seg         :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_PASR_SEG_TypeDef;

typedef union{                                                         /*!< INIT_MRR_MODE register definition*/
  __IO  uint32_t                       INIT_MRR_MODE;
  struct
  {
    __IO  uint32_t                       init_mrr_mode        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_MRR_MODE_TypeDef;

typedef union{                                                         /*!< INIT_MR_W_REQ register definition*/
  __IO  uint32_t                       INIT_MR_W_REQ;
  struct
  {
    __IO  uint32_t                       init_mr_w_req        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_MR_W_REQ_TypeDef;

typedef union{                                                         /*!< INIT_MR_ADDR register definition*/
  __IO  uint32_t                       INIT_MR_ADDR;
  struct
  {
    __IO  uint32_t                       init_mr_addr         :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_MR_ADDR_TypeDef;

typedef union{                                                         /*!< INIT_MR_WR_DATA register definition*/
  __IO  uint32_t                       INIT_MR_WR_DATA;
  struct
  {
    __IO  uint32_t                       init_mr_wr_data      :18;
    __I   uint32_t                       reserved             :14;
  } bitfield;
} DDR_CSR_APB_INIT_MR_WR_DATA_TypeDef;

typedef union{                                                         /*!< INIT_MR_WR_MASK register definition*/
  __IO  uint32_t                       INIT_MR_WR_MASK;
  struct
  {
    __IO  uint32_t                       init_mr_wr_mask      :18;
    __I   uint32_t                       reserved             :14;
  } bitfield;
} DDR_CSR_APB_INIT_MR_WR_MASK_TypeDef;

typedef union{                                                         /*!< INIT_NOP register definition*/
  __IO  uint32_t                       INIT_NOP;
  struct
  {
    __IO  uint32_t                       init_nop             :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_NOP_TypeDef;

typedef union{                                                         /*!< CFG_INIT_DURATION register definition*/
  __IO  uint32_t                       CFG_INIT_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_init_duration    :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_CFG_INIT_DURATION_TypeDef;

typedef union{                                                         /*!< CFG_ZQINIT_CAL_DURATION register definition*/
  __IO  uint32_t                       CFG_ZQINIT_CAL_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_zqinit_cal_duration :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_ZQINIT_CAL_DURATION_TypeDef;

typedef union{                                                         /*!< CFG_ZQ_CAL_L_DURATION register definition*/
  __IO  uint32_t                       CFG_ZQ_CAL_L_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_zq_cal_l_duration :11;
    __I   uint32_t                       reserved             :21;
  } bitfield;
} DDR_CSR_APB_CFG_ZQ_CAL_L_DURATION_TypeDef;

typedef union{                                                         /*!< CFG_ZQ_CAL_S_DURATION register definition*/
  __IO  uint32_t                       CFG_ZQ_CAL_S_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_zq_cal_s_duration :11;
    __I   uint32_t                       reserved             :21;
  } bitfield;
} DDR_CSR_APB_CFG_ZQ_CAL_S_DURATION_TypeDef;

typedef union{                                                         /*!< CFG_ZQ_CAL_R_DURATION register definition*/
  __IO  uint32_t                       CFG_ZQ_CAL_R_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_zq_cal_r_duration :11;
    __I   uint32_t                       reserved             :21;
  } bitfield;
} DDR_CSR_APB_CFG_ZQ_CAL_R_DURATION_TypeDef;

typedef union{                                                         /*!< CFG_MRR register definition*/
  __IO  uint32_t                       CFG_MRR;
  struct
  {
    __IO  uint32_t                       cfg_mrr              :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_MRR_TypeDef;

typedef union{                                                         /*!< CFG_MRW register definition*/
  __IO  uint32_t                       CFG_MRW;
  struct
  {
    __IO  uint32_t                       cfg_mrw              :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_MRW_TypeDef;

typedef union{                                                         /*!< CFG_ODT_POWERDOWN register definition*/
  __IO  uint32_t                       CFG_ODT_POWERDOWN;
  struct
  {
    __IO  uint32_t                       cfg_odt_powerdown    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ODT_POWERDOWN_TypeDef;

typedef union{                                                         /*!< CFG_WL register definition*/
  __IO  uint32_t                       CFG_WL;
  struct
  {
    __IO  uint32_t                       cfg_wl               :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_WL_TypeDef;

typedef union{                                                         /*!< CFG_RL register definition*/
  __IO  uint32_t                       CFG_RL;
  struct
  {
    __IO  uint32_t                       cfg_rl               :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_RL_TypeDef;

typedef union{                                                         /*!< CFG_CAL_READ_PERIOD register definition*/
  __IO  uint32_t                       CFG_CAL_READ_PERIOD;
  struct
  {
    __IO  uint32_t                       cfg_cal_read_period  :22;
    __I   uint32_t                       reserved             :10;
  } bitfield;
} DDR_CSR_APB_CFG_CAL_READ_PERIOD_TypeDef;

typedef union{                                                         /*!< CFG_NUM_CAL_READS register definition*/
  __IO  uint32_t                       CFG_NUM_CAL_READS;
  struct
  {
    __IO  uint32_t                       cfg_num_cal_reads    :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_NUM_CAL_READS_TypeDef;

typedef union{                                                         /*!< INIT_SELF_REFRESH register definition*/
  __IO  uint32_t                       INIT_SELF_REFRESH;
  struct
  {
    __IO  uint32_t                       init_self_refresh    :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_SELF_REFRESH_TypeDef;

typedef union{                                                         /*!< INIT_SELF_REFRESH_STATUS register definition*/
  __I   uint32_t                       INIT_SELF_REFRESH_STATUS;
  struct
  {
    __I   uint32_t                       init_self_refresh_status :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_SELF_REFRESH_STATUS_TypeDef;

typedef union{                                                         /*!< INIT_POWER_DOWN register definition*/
  __IO  uint32_t                       INIT_POWER_DOWN;
  struct
  {
    __IO  uint32_t                       init_power_down      :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_POWER_DOWN_TypeDef;

typedef union{                                                         /*!< INIT_POWER_DOWN_STATUS register definition*/
  __I   uint32_t                       INIT_POWER_DOWN_STATUS;
  struct
  {
    __I   uint32_t                       init_power_down_status :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_POWER_DOWN_STATUS_TypeDef;

typedef union{                                                         /*!< INIT_FORCE_WRITE register definition*/
  __IO  uint32_t                       INIT_FORCE_WRITE;
  struct
  {
    __IO  uint32_t                       init_force_write     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_FORCE_WRITE_TypeDef;

typedef union{                                                         /*!< INIT_FORCE_WRITE_CS register definition*/
  __IO  uint32_t                       INIT_FORCE_WRITE_CS;
  struct
  {
    __IO  uint32_t                       init_force_write_cs  :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_INIT_FORCE_WRITE_CS_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_INIT_DISABLE register definition*/
  __IO  uint32_t                       CFG_CTRLR_INIT_DISABLE;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_init_disable :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_INIT_DISABLE_TypeDef;

typedef union{                                                         /*!< CTRLR_READY register definition*/
  __I   uint32_t                       CTRLR_READY;
  struct
  {
    __I   uint32_t                       ctrlr_ready          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CTRLR_READY_TypeDef;

typedef union{                                                         /*!< INIT_RDIMM_READY register definition*/
  __I   uint32_t                       INIT_RDIMM_READY;
  struct
  {
    __I   uint32_t                       init_rdimm_ready     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_RDIMM_READY_TypeDef;

typedef union{                                                         /*!< INIT_RDIMM_COMPLETE register definition*/
  __IO  uint32_t                       INIT_RDIMM_COMPLETE;
  struct
  {
    __IO  uint32_t                       init_rdimm_complete  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_RDIMM_COMPLETE_TypeDef;

typedef union{                                                         /*!< CFG_RDIMM_LAT register definition*/
  __IO  uint32_t                       CFG_RDIMM_LAT;
  struct
  {
    __IO  uint32_t                       cfg_rdimm_lat        :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_RDIMM_LAT_TypeDef;

typedef union{                                                         /*!< CFG_RDIMM_BSIDE_INVERT register definition*/
  __IO  uint32_t                       CFG_RDIMM_BSIDE_INVERT;
  struct
  {
    __IO  uint32_t                       cfg_rdimm_bside_invert :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RDIMM_BSIDE_INVERT_TypeDef;

typedef union{                                                         /*!< CFG_LRDIMM register definition*/
  __IO  uint32_t                       CFG_LRDIMM;
  struct
  {
    __IO  uint32_t                       cfg_lrdimm           :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_LRDIMM_TypeDef;

typedef union{                                                         /*!< INIT_MEMORY_RESET_MASK register definition*/
  __IO  uint32_t                       INIT_MEMORY_RESET_MASK;
  struct
  {
    __IO  uint32_t                       init_memory_reset_mask :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_MEMORY_RESET_MASK_TypeDef;

typedef union{                                                         /*!< CFG_RD_PREAMB_TOGGLE register definition*/
  __IO  uint32_t                       CFG_RD_PREAMB_TOGGLE;
  struct
  {
    __IO  uint32_t                       cfg_rd_preamb_toggle :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RD_PREAMB_TOGGLE_TypeDef;

typedef union{                                                         /*!< CFG_RD_POSTAMBLE register definition*/
  __IO  uint32_t                       CFG_RD_POSTAMBLE;
  struct
  {
    __IO  uint32_t                       cfg_rd_postamble     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RD_POSTAMBLE_TypeDef;

typedef union{                                                         /*!< CFG_PU_CAL register definition*/
  __IO  uint32_t                       CFG_PU_CAL;
  struct
  {
    __IO  uint32_t                       cfg_pu_cal           :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_PU_CAL_TypeDef;

typedef union{                                                         /*!< CFG_DQ_ODT register definition*/
  __IO  uint32_t                       CFG_DQ_ODT;
  struct
  {
    __IO  uint32_t                       cfg_dq_odt           :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_DQ_ODT_TypeDef;

typedef union{                                                         /*!< CFG_CA_ODT register definition*/
  __IO  uint32_t                       CFG_CA_ODT;
  struct
  {
    __IO  uint32_t                       cfg_ca_odt           :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_CA_ODT_TypeDef;

typedef union{                                                         /*!< CFG_ZQLATCH_DURATION register definition*/
  __IO  uint32_t                       CFG_ZQLATCH_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_zqlatch_duration :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ZQLATCH_DURATION_TypeDef;

typedef union{                                                         /*!< INIT_CAL_SELECT register definition*/
  __IO  uint32_t                       INIT_CAL_SELECT;
  struct
  {
    __IO  uint32_t                       init_cal_select      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_SELECT_TypeDef;

typedef union{                                                         /*!< INIT_CAL_L_R_REQ register definition*/
  __IO  uint32_t                       INIT_CAL_L_R_REQ;
  struct
  {
    __IO  uint32_t                       init_cal_l_r_req     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_L_R_REQ_TypeDef;

typedef union{                                                         /*!< INIT_CAL_L_B_SIZE register definition*/
  __IO  uint32_t                       INIT_CAL_L_B_SIZE;
  struct
  {
    __IO  uint32_t                       init_cal_l_b_size    :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_L_B_SIZE_TypeDef;

typedef union{                                                         /*!< INIT_CAL_L_R_ACK register definition*/
  __I   uint32_t                       INIT_CAL_L_R_ACK;
  struct
  {
    __I   uint32_t                       init_cal_l_r_ack     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_L_R_ACK_TypeDef;

typedef union{                                                         /*!< INIT_CAL_L_READ_COMPLETE register definition*/
  __I   uint32_t                       INIT_CAL_L_READ_COMPLETE;
  struct
  {
    __I   uint32_t                       init_cal_l_read_complete :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_L_READ_COMPLETE_TypeDef;

typedef union{                                                         /*!< INIT_RWFIFO register definition*/
  __IO  uint32_t                       INIT_RWFIFO;
  struct
  {
    __IO  uint32_t                       init_rwfifo          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_RWFIFO_TypeDef;

typedef union{                                                         /*!< INIT_RD_DQCAL register definition*/
  __IO  uint32_t                       INIT_RD_DQCAL;
  struct
  {
    __IO  uint32_t                       init_rd_dqcal        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_RD_DQCAL_TypeDef;

typedef union{                                                         /*!< INIT_START_DQSOSC register definition*/
  __IO  uint32_t                       INIT_START_DQSOSC;
  struct
  {
    __IO  uint32_t                       init_start_dqsosc    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_START_DQSOSC_TypeDef;

typedef union{                                                         /*!< INIT_STOP_DQSOSC register definition*/
  __IO  uint32_t                       INIT_STOP_DQSOSC;
  struct
  {
    __IO  uint32_t                       init_stop_dqsosc     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_STOP_DQSOSC_TypeDef;

typedef union{                                                         /*!< INIT_ZQ_CAL_START register definition*/
  __IO  uint32_t                       INIT_ZQ_CAL_START;
  struct
  {
    __IO  uint32_t                       init_zq_cal_start    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_ZQ_CAL_START_TypeDef;

typedef union{                                                         /*!< CFG_WR_POSTAMBLE register definition*/
  __IO  uint32_t                       CFG_WR_POSTAMBLE;
  struct
  {
    __IO  uint32_t                       cfg_wr_postamble     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_WR_POSTAMBLE_TypeDef;

typedef union{                                                         /*!< INIT_CAL_L_ADDR_0 register definition*/
  __IO  uint32_t                       INIT_CAL_L_ADDR_0;
  struct
  {
    __IO  uint32_t                       init_cal_l_addr_0    :32;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_L_ADDR_0_TypeDef;

typedef union{                                                         /*!< INIT_CAL_L_ADDR_1 register definition*/
  __IO  uint32_t                       INIT_CAL_L_ADDR_1;
  struct
  {
    __IO  uint32_t                       init_cal_l_addr_1    :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_INIT_CAL_L_ADDR_1_TypeDef;

typedef union{                                                         /*!< CFG_CTRLUPD_TRIG register definition*/
  __IO  uint32_t                       CFG_CTRLUPD_TRIG;
  struct
  {
    __IO  uint32_t                       cfg_ctrlupd_trig     :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLUPD_TRIG_TypeDef;

typedef union{                                                         /*!< CFG_CTRLUPD_START_DELAY register definition*/
  __IO  uint32_t                       CFG_CTRLUPD_START_DELAY;
  struct
  {
    __IO  uint32_t                       cfg_ctrlupd_start_delay :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLUPD_START_DELAY_TypeDef;

typedef union{                                                         /*!< CFG_DFI_T_CTRLUPD_MAX register definition*/
  __IO  uint32_t                       CFG_DFI_T_CTRLUPD_MAX;
  struct
  {
    __IO  uint32_t                       cfg_dfi_t_ctrlupd_max :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_T_CTRLUPD_MAX_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_BUSY_SEL register definition*/
  __IO  uint32_t                       CFG_CTRLR_BUSY_SEL;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_busy_sel   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_BUSY_SEL_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_BUSY_VALUE register definition*/
  __IO  uint32_t                       CFG_CTRLR_BUSY_VALUE;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_busy_value :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_BUSY_VALUE_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_BUSY_TURN_OFF_DELAY register definition*/
  __IO  uint32_t                       CFG_CTRLR_BUSY_TURN_OFF_DELAY;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_busy_turn_off_delay :9;
    __I   uint32_t                       reserved             :23;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_BUSY_TURN_OFF_DELAY_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW register definition*/
  __IO  uint32_t                       CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_busy_slow_restart_window :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_BUSY_RESTART_HOLDOFF register definition*/
  __IO  uint32_t                       CFG_CTRLR_BUSY_RESTART_HOLDOFF;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_busy_restart_holdoff :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_BUSY_RESTART_HOLDOFF_TypeDef;

typedef union{                                                         /*!< CFG_PARITY_RDIMM_DELAY register definition*/
  __IO  uint32_t                       CFG_PARITY_RDIMM_DELAY;
  struct
  {
    __IO  uint32_t                       cfg_parity_rdimm_delay :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_PARITY_RDIMM_DELAY_TypeDef;

typedef union{                                                         /*!< CFG_CTRLR_BUSY_ENABLE register definition*/
  __IO  uint32_t                       CFG_CTRLR_BUSY_ENABLE;
  struct
  {
    __IO  uint32_t                       cfg_ctrlr_busy_enable :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_CTRLR_BUSY_ENABLE_TypeDef;

typedef union{                                                         /*!< CFG_ASYNC_ODT register definition*/
  __IO  uint32_t                       CFG_ASYNC_ODT;
  struct
  {
    __IO  uint32_t                       cfg_async_odt        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ASYNC_ODT_TypeDef;

typedef union{                                                         /*!< CFG_ZQ_CAL_DURATION register definition*/
  __IO  uint32_t                       CFG_ZQ_CAL_DURATION;
  struct
  {
    __IO  uint32_t                       cfg_zq_cal_duration  :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_ZQ_CAL_DURATION_TypeDef;

typedef union{                                                         /*!< CFG_MRRI register definition*/
  __IO  uint32_t                       CFG_MRRI;
  struct
  {
    __IO  uint32_t                       cfg_mrri             :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_MRRI_TypeDef;

typedef union{                                                         /*!< INIT_ODT_FORCE_EN register definition*/
  __IO  uint32_t                       INIT_ODT_FORCE_EN;
  struct
  {
    __IO  uint32_t                       init_odt_force_en    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_ODT_FORCE_EN_TypeDef;

typedef union{                                                         /*!< INIT_ODT_FORCE_RANK register definition*/
  __IO  uint32_t                       INIT_ODT_FORCE_RANK;
  struct
  {
    __IO  uint32_t                       init_odt_force_rank  :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_INIT_ODT_FORCE_RANK_TypeDef;

typedef union{                                                         /*!< CFG_PHYUPD_ACK_DELAY register definition*/
  __IO  uint32_t                       CFG_PHYUPD_ACK_DELAY;
  struct
  {
    __IO  uint32_t                       cfg_phyupd_ack_delay :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_CFG_PHYUPD_ACK_DELAY_TypeDef;

typedef union{                                                         /*!< CFG_MIRROR_X16_BG0_BG1 register definition*/
  __IO  uint32_t                       CFG_MIRROR_X16_BG0_BG1;
  struct
  {
    __IO  uint32_t                       cfg_mirror_x16_bg0_bg1 :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_MIRROR_X16_BG0_BG1_TypeDef;

typedef union{                                                         /*!< INIT_PDA_MR_W_REQ register definition*/
  __IO  uint32_t                       INIT_PDA_MR_W_REQ;
  struct
  {
    __IO  uint32_t                       init_pda_mr_w_req    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_PDA_MR_W_REQ_TypeDef;

typedef union{                                                         /*!< INIT_PDA_NIBBLE_SELECT register definition*/
  __IO  uint32_t                       INIT_PDA_NIBBLE_SELECT;
  struct
  {
    __IO  uint32_t                       init_pda_nibble_select :18;
    __I   uint32_t                       reserved             :14;
  } bitfield;
} DDR_CSR_APB_INIT_PDA_NIBBLE_SELECT_TypeDef;

typedef union{                                                         /*!< CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH register definition*/
  __IO  uint32_t                       CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH;
  struct
  {
    __IO  uint32_t                       cfg_dram_clk_disable_in_self_refresh :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH_TypeDef;

typedef union{                                                         /*!< CFG_CKSRE register definition*/
  __IO  uint32_t                       CFG_CKSRE;
  struct
  {
    __IO  uint32_t                       cfg_cksre            :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_CKSRE_TypeDef;

typedef union{                                                         /*!< CFG_CKSRX register definition*/
  __IO  uint32_t                       CFG_CKSRX;
  struct
  {
    __IO  uint32_t                       cfg_cksrx            :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_CKSRX_TypeDef;

typedef union{                                                         /*!< CFG_RCD_STAB register definition*/
  __IO  uint32_t                       CFG_RCD_STAB;
  struct
  {
    __IO  uint32_t                       cfg_rcd_stab         :14;
    __I   uint32_t                       reserved             :18;
  } bitfield;
} DDR_CSR_APB_CFG_RCD_STAB_TypeDef;

typedef union{                                                         /*!< CFG_DFI_T_CTRL_DELAY register definition*/
  __IO  uint32_t                       CFG_DFI_T_CTRL_DELAY;
  struct
  {
    __IO  uint32_t                       cfg_dfi_t_ctrl_delay :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_T_CTRL_DELAY_TypeDef;

typedef union{                                                         /*!< CFG_DFI_T_DRAM_CLK_ENABLE register definition*/
  __IO  uint32_t                       CFG_DFI_T_DRAM_CLK_ENABLE;
  struct
  {
    __IO  uint32_t                       cfg_dfi_t_dram_clk_enable :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_T_DRAM_CLK_ENABLE_TypeDef;

typedef union{                                                         /*!< CFG_IDLE_TIME_TO_SELF_REFRESH register definition*/
  __IO  uint32_t                       CFG_IDLE_TIME_TO_SELF_REFRESH;
  struct
  {
    __IO  uint32_t                       cfg_idle_time_to_self_refresh :32;
  } bitfield;
} DDR_CSR_APB_CFG_IDLE_TIME_TO_SELF_REFRESH_TypeDef;

typedef union{                                                         /*!< CFG_IDLE_TIME_TO_POWER_DOWN register definition*/
  __IO  uint32_t                       CFG_IDLE_TIME_TO_POWER_DOWN;
  struct
  {
    __IO  uint32_t                       cfg_idle_time_to_power_down :32;
  } bitfield;
} DDR_CSR_APB_CFG_IDLE_TIME_TO_POWER_DOWN_TypeDef;

typedef union{                                                         /*!< CFG_BURST_RW_REFRESH_HOLDOFF register definition*/
  __IO  uint32_t                       CFG_BURST_RW_REFRESH_HOLDOFF;
  struct
  {
    __IO  uint32_t                       cfg_burst_rw_refresh_holdoff :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_BURST_RW_REFRESH_HOLDOFF_TypeDef;

typedef union{                                                         /*!< INIT_REFRESH_COUNT register definition*/
  __I   uint32_t                       INIT_REFRESH_COUNT;
  struct
  {
    __I   uint32_t                       init_refresh_count   :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_INIT_REFRESH_COUNT_TypeDef;

typedef union{                                                         /*!< CFG_BG_INTERLEAVE register definition*/
  __IO  uint32_t                       CFG_BG_INTERLEAVE;
  struct
  {
    __IO  uint32_t                       cfg_bg_interleave    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_BG_INTERLEAVE_TypeDef;

typedef union{                                                         /*!< CFG_REFRESH_DURING_PHY_TRAINING register definition*/
  __IO  uint32_t                       CFG_REFRESH_DURING_PHY_TRAINING;
  struct
  {
    __IO  uint32_t                       cfg_refresh_during_phy_training :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_REFRESH_DURING_PHY_TRAINING_TypeDef;

typedef union{                                                         /*!< MT_EN register definition*/
  __IO  uint32_t                       MT_EN;
  struct
  {
    __IO  uint32_t                       mt_en                :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_EN_TypeDef;

typedef union{                                                         /*!< MT_EN_SINGLE register definition*/
  __IO  uint32_t                       MT_EN_SINGLE;
  struct
  {
    __IO  uint32_t                       mt_en_single         :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_EN_SINGLE_TypeDef;

typedef union{                                                         /*!< MT_STOP_ON_ERROR register definition*/
  __IO  uint32_t                       MT_STOP_ON_ERROR;
  struct
  {
    __IO  uint32_t                       mt_stop_on_error     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_STOP_ON_ERROR_TypeDef;

typedef union{                                                         /*!< MT_RD_ONLY register definition*/
  __IO  uint32_t                       MT_RD_ONLY;
  struct
  {
    __IO  uint32_t                       mt_rd_only           :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_RD_ONLY_TypeDef;

typedef union{                                                         /*!< MT_WR_ONLY register definition*/
  __IO  uint32_t                       MT_WR_ONLY;
  struct
  {
    __IO  uint32_t                       mt_wr_only           :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_WR_ONLY_TypeDef;

typedef union{                                                         /*!< MT_DATA_PATTERN register definition*/
  __IO  uint32_t                       MT_DATA_PATTERN;
  struct
  {
    __IO  uint32_t                       mt_data_pattern      :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_MT_DATA_PATTERN_TypeDef;

typedef union{                                                         /*!< MT_ADDR_PATTERN register definition*/
  __IO  uint32_t                       MT_ADDR_PATTERN;
  struct
  {
    __IO  uint32_t                       mt_addr_pattern      :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_MT_ADDR_PATTERN_TypeDef;

typedef union{                                                         /*!< MT_DATA_INVERT register definition*/
  __IO  uint32_t                       MT_DATA_INVERT;
  struct
  {
    __IO  uint32_t                       mt_data_invert       :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_DATA_INVERT_TypeDef;

typedef union{                                                         /*!< MT_ADDR_BITS register definition*/
  __IO  uint32_t                       MT_ADDR_BITS;
  struct
  {
    __IO  uint32_t                       mt_addr_bits         :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_MT_ADDR_BITS_TypeDef;

typedef union{                                                         /*!< MT_ERROR_STS register definition*/
  __I   uint32_t                       MT_ERROR_STS;
  struct
  {
    __I   uint32_t                       mt_error_sts         :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_ERROR_STS_TypeDef;

typedef union{                                                         /*!< MT_DONE_ACK register definition*/
  __I   uint32_t                       MT_DONE_ACK;
  struct
  {
    __I   uint32_t                       mt_done_ack          :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_DONE_ACK_TypeDef;

typedef union{                                                         /*!< MT_START_ADDR_0 register definition*/
  __IO  uint32_t                       MT_START_ADDR_0;
  struct
  {
    __IO  uint32_t                       mt_start_addr_0      :32;
  } bitfield;
} DDR_CSR_APB_MT_START_ADDR_0_TypeDef;

typedef union{                                                         /*!< MT_START_ADDR_1 register definition*/
  __IO  uint32_t                       MT_START_ADDR_1;
  struct
  {
    __IO  uint32_t                       mt_start_addr_1      :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_MT_START_ADDR_1_TypeDef;

typedef union{                                                         /*!< MT_ERROR_MASK_0 register definition*/
  __IO  uint32_t                       MT_ERROR_MASK_0;
  struct
  {
    __IO  uint32_t                       mt_error_mask_0      :32;
  } bitfield;
} DDR_CSR_APB_MT_ERROR_MASK_0_TypeDef;

typedef union{                                                         /*!< MT_ERROR_MASK_1 register definition*/
  __IO  uint32_t                       MT_ERROR_MASK_1;
  struct
  {
    __IO  uint32_t                       mt_error_mask_1      :32;
  } bitfield;
} DDR_CSR_APB_MT_ERROR_MASK_1_TypeDef;

typedef union{                                                         /*!< MT_ERROR_MASK_2 register definition*/
  __IO  uint32_t                       MT_ERROR_MASK_2;
  struct
  {
    __IO  uint32_t                       mt_error_mask_2      :32;
  } bitfield;
} DDR_CSR_APB_MT_ERROR_MASK_2_TypeDef;

typedef union{                                                         /*!< MT_ERROR_MASK_3 register definition*/
  __IO  uint32_t                       MT_ERROR_MASK_3;
  struct
  {
    __IO  uint32_t                       mt_error_mask_3      :32;
  } bitfield;
} DDR_CSR_APB_MT_ERROR_MASK_3_TypeDef;

typedef union{                                                         /*!< MT_ERROR_MASK_4 register definition*/
  __IO  uint32_t                       MT_ERROR_MASK_4;
  struct
  {
    __IO  uint32_t                       mt_error_mask_4      :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_MT_ERROR_MASK_4_TypeDef;

typedef union{                                                         /*!< MT_USER_DATA_PATTERN register definition*/
  __IO  uint32_t                       MT_USER_DATA_PATTERN;
  struct
  {
    __IO  uint32_t                       mt_user_data_pattern :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_MT_USER_DATA_PATTERN_TypeDef;

typedef union{                                                         /*!< MT_ALG_AUTO_PCH register definition*/
  __IO  uint32_t                       MT_ALG_AUTO_PCH;
  struct
  {
    __IO  uint32_t                       mt_alg_auto_pch      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MT_ALG_AUTO_PCH_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P0 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P0;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p0 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P0_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P1 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P1;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p1 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P1_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P2 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P2;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p2 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P2_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P3 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P3;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p3 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P3_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P4 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P4;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p4 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P4_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P5 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P5;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p5 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P5_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P6 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P6;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p6 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P6_TypeDef;

typedef union{                                                         /*!< CFG_STARVE_TIMEOUT_P7 register definition*/
  __IO  uint32_t                       CFG_STARVE_TIMEOUT_P7;
  struct
  {
    __IO  uint32_t                       cfg_starve_timeout_p7 :12;
    __I   uint32_t                       reserved             :20;
  } bitfield;
} DDR_CSR_APB_CFG_STARVE_TIMEOUT_P7_TypeDef;

typedef union{                                                         /*!< CFG_REORDER_EN register definition*/
  __IO  uint32_t                       CFG_REORDER_EN;
  struct
  {
    __IO  uint32_t                       cfg_reorder_en       :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_REORDER_EN_TypeDef;

typedef union{                                                         /*!< CFG_REORDER_QUEUE_EN register definition*/
  __IO  uint32_t                       CFG_REORDER_QUEUE_EN;
  struct
  {
    __IO  uint32_t                       cfg_reorder_queue_en :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_REORDER_QUEUE_EN_TypeDef;

typedef union{                                                         /*!< CFG_INTRAPORT_REORDER_EN register definition*/
  __IO  uint32_t                       CFG_INTRAPORT_REORDER_EN;
  struct
  {
    __IO  uint32_t                       cfg_intraport_reorder_en :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_INTRAPORT_REORDER_EN_TypeDef;

typedef union{                                                         /*!< CFG_MAINTAIN_COHERENCY register definition*/
  __IO  uint32_t                       CFG_MAINTAIN_COHERENCY;
  struct
  {
    __IO  uint32_t                       cfg_maintain_coherency :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_MAINTAIN_COHERENCY_TypeDef;

typedef union{                                                         /*!< CFG_Q_AGE_LIMIT register definition*/
  __IO  uint32_t                       CFG_Q_AGE_LIMIT;
  struct
  {
    __IO  uint32_t                       cfg_q_age_limit      :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_Q_AGE_LIMIT_TypeDef;

typedef union{                                                         /*!< CFG_RO_CLOSED_PAGE_POLICY register definition*/
  __IO  uint32_t                       CFG_RO_CLOSED_PAGE_POLICY;
  struct
  {
    __IO  uint32_t                       cfg_ro_closed_page_policy :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RO_CLOSED_PAGE_POLICY_TypeDef;

typedef union{                                                         /*!< CFG_REORDER_RW_ONLY register definition*/
  __IO  uint32_t                       CFG_REORDER_RW_ONLY;
  struct
  {
    __IO  uint32_t                       cfg_reorder_rw_only  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_REORDER_RW_ONLY_TypeDef;

typedef union{                                                         /*!< CFG_RO_PRIORITY_EN register definition*/
  __IO  uint32_t                       CFG_RO_PRIORITY_EN;
  struct
  {
    __IO  uint32_t                       cfg_ro_priority_en   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RO_PRIORITY_EN_TypeDef;

typedef union{                                                         /*!< CFG_DM_EN register definition*/
  __IO  uint32_t                       CFG_DM_EN;
  struct
  {
    __IO  uint32_t                       cfg_dm_en            :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DM_EN_TypeDef;

typedef union{                                                         /*!< CFG_RMW_EN register definition*/
  __IO  uint32_t                       CFG_RMW_EN;
  struct
  {
    __IO  uint32_t                       cfg_rmw_en           :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_RMW_EN_TypeDef;

typedef union{                                                         /*!< CFG_ECC_CORRECTION_EN register definition*/
  __IO  uint32_t                       CFG_ECC_CORRECTION_EN;
  struct
  {
    __IO  uint32_t                       cfg_ecc_correction_en :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ECC_CORRECTION_EN_TypeDef;

typedef union{                                                         /*!< CFG_ECC_BYPASS register definition*/
  __IO  uint32_t                       CFG_ECC_BYPASS;
  struct
  {
    __IO  uint32_t                       cfg_ecc_bypass       :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ECC_BYPASS_TypeDef;

typedef union{                                                         /*!< INIT_WRITE_DATA_1B_ECC_ERROR_GEN register definition*/
  __IO  uint32_t                       INIT_WRITE_DATA_1B_ECC_ERROR_GEN;
  struct
  {
    __IO  uint32_t                       init_write_data_1b_ecc_error_gen :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_INIT_WRITE_DATA_1B_ECC_ERROR_GEN_TypeDef;

typedef union{                                                         /*!< INIT_WRITE_DATA_2B_ECC_ERROR_GEN register definition*/
  __IO  uint32_t                       INIT_WRITE_DATA_2B_ECC_ERROR_GEN;
  struct
  {
    __IO  uint32_t                       init_write_data_2b_ecc_error_gen :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_INIT_WRITE_DATA_2B_ECC_ERROR_GEN_TypeDef;

typedef union{                                                         /*!< CFG_ECC_1BIT_INT_THRESH register definition*/
  __IO  uint32_t                       CFG_ECC_1BIT_INT_THRESH;
  struct
  {
    __IO  uint32_t                       cfg_ecc_1bit_int_thresh :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_CFG_ECC_1BIT_INT_THRESH_TypeDef;

typedef union{                                                         /*!< STAT_INT_ECC_1BIT_THRESH register definition*/
  __I   uint32_t                       STAT_INT_ECC_1BIT_THRESH;
  struct
  {
    __I   uint32_t                       stat_int_ecc_1bit_thresh :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_INT_ECC_1BIT_THRESH_TypeDef;

typedef union{                                                         /*!< INIT_READ_CAPTURE_ADDR register definition*/
  __IO  uint32_t                       INIT_READ_CAPTURE_ADDR;
  struct
  {
    __IO  uint32_t                       init_read_capture_addr :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_INIT_READ_CAPTURE_ADDR_TypeDef;

typedef union{                                                         /*!< INIT_READ_CAPTURE_DATA_0 register definition*/
  __I   uint32_t                       INIT_READ_CAPTURE_DATA_0;
  struct
  {
    __I   uint32_t                       init_read_capture_data_0 :32;
  } bitfield;
} DDR_CSR_APB_INIT_READ_CAPTURE_DATA_0_TypeDef;

typedef union{                                                         /*!< INIT_READ_CAPTURE_DATA_1 register definition*/
  __I   uint32_t                       INIT_READ_CAPTURE_DATA_1;
  struct
  {
    __I   uint32_t                       init_read_capture_data_1 :32;
  } bitfield;
} DDR_CSR_APB_INIT_READ_CAPTURE_DATA_1_TypeDef;

typedef union{                                                         /*!< INIT_READ_CAPTURE_DATA_2 register definition*/
  __I   uint32_t                       INIT_READ_CAPTURE_DATA_2;
  struct
  {
    __I   uint32_t                       init_read_capture_data_2 :32;
  } bitfield;
} DDR_CSR_APB_INIT_READ_CAPTURE_DATA_2_TypeDef;

typedef union{                                                         /*!< INIT_READ_CAPTURE_DATA_3 register definition*/
  __I   uint32_t                       INIT_READ_CAPTURE_DATA_3;
  struct
  {
    __I   uint32_t                       init_read_capture_data_3 :32;
  } bitfield;
} DDR_CSR_APB_INIT_READ_CAPTURE_DATA_3_TypeDef;

typedef union{                                                         /*!< INIT_READ_CAPTURE_DATA_4 register definition*/
  __I   uint32_t                       INIT_READ_CAPTURE_DATA_4;
  struct
  {
    __I   uint32_t                       init_read_capture_data_4 :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_INIT_READ_CAPTURE_DATA_4_TypeDef;

typedef union{                                                         /*!< CFG_ERROR_GROUP_SEL register definition*/
  __IO  uint32_t                       CFG_ERROR_GROUP_SEL;
  struct
  {
    __IO  uint32_t                       cfg_error_group_sel  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ERROR_GROUP_SEL_TypeDef;

typedef union{                                                         /*!< CFG_DATA_SEL register definition*/
  __IO  uint32_t                       CFG_DATA_SEL;
  struct
  {
    __IO  uint32_t                       cfg_data_sel         :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_DATA_SEL_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_MODE register definition*/
  __IO  uint32_t                       CFG_TRIG_MODE;
  struct
  {
    __IO  uint32_t                       cfg_trig_mode        :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_MODE_TypeDef;

typedef union{                                                         /*!< CFG_POST_TRIG_CYCS register definition*/
  __IO  uint32_t                       CFG_POST_TRIG_CYCS;
  struct
  {
    __IO  uint32_t                       cfg_post_trig_cycs   :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_POST_TRIG_CYCS_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_MASK register definition*/
  __IO  uint32_t                       CFG_TRIG_MASK;
  struct
  {
    __IO  uint32_t                       cfg_trig_mask        :3;
    __I   uint32_t                       reserved             :29;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_MASK_TypeDef;

typedef union{                                                         /*!< CFG_EN_MASK register definition*/
  __IO  uint32_t                       CFG_EN_MASK;
  struct
  {
    __IO  uint32_t                       cfg_en_mask          :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_EN_MASK_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_ADDR register definition*/
  __IO  uint32_t                       MTC_ACQ_ADDR;
  struct
  {
    __IO  uint32_t                       mtc_acq_addr         :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_ADDR_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_CYCS_STORED register definition*/
  __I   uint32_t                       MTC_ACQ_CYCS_STORED;
  struct
  {
    __I   uint32_t                       mtc_acq_cycs_stored  :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_CYCS_STORED_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_TRIG_DETECT register definition*/
  __I   uint32_t                       MTC_ACQ_TRIG_DETECT;
  struct
  {
    __I   uint32_t                       mtc_acq_trig_detect  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_TRIG_DETECT_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_MEM_TRIG_ADDR register definition*/
  __I   uint32_t                       MTC_ACQ_MEM_TRIG_ADDR;
  struct
  {
    __I   uint32_t                       mtc_acq_mem_trig_addr :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_MEM_TRIG_ADDR_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_MEM_LAST_ADDR register definition*/
  __I   uint32_t                       MTC_ACQ_MEM_LAST_ADDR;
  struct
  {
    __I   uint32_t                       mtc_acq_mem_last_addr :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_MEM_LAST_ADDR_TypeDef;

typedef union{                                                         /*!< MTC_ACK register definition*/
  __I   uint32_t                       MTC_ACK;
  struct
  {
    __I   uint32_t                       mtc_ack              :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MTC_ACK_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_MT_ADDR_0 register definition*/
  __IO  uint32_t                       CFG_TRIG_MT_ADDR_0;
  struct
  {
    __IO  uint32_t                       cfg_trig_mt_addr_0   :32;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_MT_ADDR_0_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_MT_ADDR_1 register definition*/
  __IO  uint32_t                       CFG_TRIG_MT_ADDR_1;
  struct
  {
    __IO  uint32_t                       cfg_trig_mt_addr_1   :7;
    __I   uint32_t                       reserved             :25;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_MT_ADDR_1_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_ERR_MASK_0 register definition*/
  __IO  uint32_t                       CFG_TRIG_ERR_MASK_0;
  struct
  {
    __IO  uint32_t                       cfg_trig_err_mask_0  :32;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_ERR_MASK_0_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_ERR_MASK_1 register definition*/
  __IO  uint32_t                       CFG_TRIG_ERR_MASK_1;
  struct
  {
    __IO  uint32_t                       cfg_trig_err_mask_1  :32;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_ERR_MASK_1_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_ERR_MASK_2 register definition*/
  __IO  uint32_t                       CFG_TRIG_ERR_MASK_2;
  struct
  {
    __IO  uint32_t                       cfg_trig_err_mask_2  :32;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_ERR_MASK_2_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_ERR_MASK_3 register definition*/
  __IO  uint32_t                       CFG_TRIG_ERR_MASK_3;
  struct
  {
    __IO  uint32_t                       cfg_trig_err_mask_3  :32;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_ERR_MASK_3_TypeDef;

typedef union{                                                         /*!< CFG_TRIG_ERR_MASK_4 register definition*/
  __IO  uint32_t                       CFG_TRIG_ERR_MASK_4;
  struct
  {
    __IO  uint32_t                       cfg_trig_err_mask_4  :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_CFG_TRIG_ERR_MASK_4_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_WR_DATA_0 register definition*/
  __IO  uint32_t                       MTC_ACQ_WR_DATA_0;
  struct
  {
    __IO  uint32_t                       mtc_acq_wr_data_0    :32;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_WR_DATA_0_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_WR_DATA_1 register definition*/
  __IO  uint32_t                       MTC_ACQ_WR_DATA_1;
  struct
  {
    __IO  uint32_t                       mtc_acq_wr_data_1    :32;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_WR_DATA_1_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_WR_DATA_2 register definition*/
  __IO  uint32_t                       MTC_ACQ_WR_DATA_2;
  struct
  {
    __IO  uint32_t                       mtc_acq_wr_data_2    :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_WR_DATA_2_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_RD_DATA_0 register definition*/
  __I   uint32_t                       MTC_ACQ_RD_DATA_0;
  struct
  {
    __I   uint32_t                       mtc_acq_rd_data_0    :32;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_RD_DATA_0_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_RD_DATA_1 register definition*/
  __I   uint32_t                       MTC_ACQ_RD_DATA_1;
  struct
  {
    __I   uint32_t                       mtc_acq_rd_data_1    :32;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_RD_DATA_1_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_RD_DATA_2 register definition*/
  __I   uint32_t                       MTC_ACQ_RD_DATA_2;
  struct
  {
    __I   uint32_t                       mtc_acq_rd_data_2    :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_RD_DATA_2_TypeDef;

typedef union{                                                         /*!< CFG_PRE_TRIG_CYCS register definition*/
  __IO  uint32_t                       CFG_PRE_TRIG_CYCS;
  struct
  {
    __IO  uint32_t                       cfg_pre_trig_cycs    :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_CFG_PRE_TRIG_CYCS_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_ERROR_CNT register definition*/
  __I   uint32_t                       MTC_ACQ_ERROR_CNT;
  struct
  {
    __I   uint32_t                       mtc_acq_error_cnt    :10;
    __I   uint32_t                       reserved             :22;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_ERROR_CNT_TypeDef;

typedef union{                                                         /*!< MTC_ACQ_ERROR_CNT_OVFL register definition*/
  __I   uint32_t                       MTC_ACQ_ERROR_CNT_OVFL;
  struct
  {
    __I   uint32_t                       mtc_acq_error_cnt_ovfl :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_MTC_ACQ_ERROR_CNT_OVFL_TypeDef;

typedef union{                                                         /*!< CFG_DATA_SEL_FIRST_ERROR register definition*/
  __IO  uint32_t                       CFG_DATA_SEL_FIRST_ERROR;
  struct
  {
    __IO  uint32_t                       cfg_data_sel_first_error :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DATA_SEL_FIRST_ERROR_TypeDef;

typedef union{                                                         /*!< CFG_DQ_WIDTH register definition*/
  __IO  uint32_t                       CFG_DQ_WIDTH;
  struct
  {
    __IO  uint32_t                       cfg_dq_width         :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_DQ_WIDTH_TypeDef;

typedef union{                                                         /*!< CFG_ACTIVE_DQ_SEL register definition*/
  __IO  uint32_t                       CFG_ACTIVE_DQ_SEL;
  struct
  {
    __IO  uint32_t                       cfg_active_dq_sel    :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_ACTIVE_DQ_SEL_TypeDef;

typedef union{                                                         /*!< STAT_CA_PARITY_ERROR register definition*/
  __I   uint32_t                       STAT_CA_PARITY_ERROR;
  struct
  {
    __I   uint32_t                       stat_ca_parity_error :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_CA_PARITY_ERROR_TypeDef;

typedef union{                                                         /*!< INIT_CA_PARITY_ERROR_GEN_REQ register definition*/
  __IO  uint32_t                       INIT_CA_PARITY_ERROR_GEN_REQ;
  struct
  {
    __IO  uint32_t                       init_ca_parity_error_gen_req :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_CA_PARITY_ERROR_GEN_REQ_TypeDef;

typedef union{                                                         /*!< INIT_CA_PARITY_ERROR_GEN_CMD register definition*/
  __IO  uint32_t                       INIT_CA_PARITY_ERROR_GEN_CMD;
  struct
  {
    __IO  uint32_t                       init_ca_parity_error_gen_cmd :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_INIT_CA_PARITY_ERROR_GEN_CMD_TypeDef;

typedef union{                                                         /*!< INIT_CA_PARITY_ERROR_GEN_ACK register definition*/
  __I   uint32_t                       INIT_CA_PARITY_ERROR_GEN_ACK;
  struct
  {
    __I   uint32_t                       init_ca_parity_error_gen_ack :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_CA_PARITY_ERROR_GEN_ACK_TypeDef;

typedef union{                                                         /*!< CFG_DFI_T_RDDATA_EN register definition*/
  __IO  uint32_t                       CFG_DFI_T_RDDATA_EN;
  struct
  {
    __IO  uint32_t                       cfg_dfi_t_rddata_en  :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_T_RDDATA_EN_TypeDef;

typedef union{                                                         /*!< CFG_DFI_T_PHY_RDLAT register definition*/
  __IO  uint32_t                       CFG_DFI_T_PHY_RDLAT;
  struct
  {
    __IO  uint32_t                       cfg_dfi_t_phy_rdlat  :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_T_PHY_RDLAT_TypeDef;

typedef union{                                                         /*!< CFG_DFI_T_PHY_WRLAT register definition*/
  __IO  uint32_t                       CFG_DFI_T_PHY_WRLAT;
  struct
  {
    __IO  uint32_t                       cfg_dfi_t_phy_wrlat  :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_T_PHY_WRLAT_TypeDef;

typedef union{                                                         /*!< CFG_DFI_PHYUPD_EN register definition*/
  __IO  uint32_t                       CFG_DFI_PHYUPD_EN;
  struct
  {
    __IO  uint32_t                       cfg_dfi_phyupd_en    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_PHYUPD_EN_TypeDef;

typedef union{                                                         /*!< INIT_DFI_LP_DATA_REQ register definition*/
  __IO  uint32_t                       INIT_DFI_LP_DATA_REQ;
  struct
  {
    __IO  uint32_t                       init_dfi_lp_data_req :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_DFI_LP_DATA_REQ_TypeDef;

typedef union{                                                         /*!< INIT_DFI_LP_CTRL_REQ register definition*/
  __IO  uint32_t                       INIT_DFI_LP_CTRL_REQ;
  struct
  {
    __IO  uint32_t                       init_dfi_lp_ctrl_req :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_INIT_DFI_LP_CTRL_REQ_TypeDef;

typedef union{                                                         /*!< STAT_DFI_LP_ACK register definition*/
  __I   uint32_t                       STAT_DFI_LP_ACK;
  struct
  {
    __I   uint32_t                       stat_dfi_lp_ack      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_DFI_LP_ACK_TypeDef;

typedef union{                                                         /*!< INIT_DFI_LP_WAKEUP register definition*/
  __IO  uint32_t                       INIT_DFI_LP_WAKEUP;
  struct
  {
    __IO  uint32_t                       init_dfi_lp_wakeup   :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_INIT_DFI_LP_WAKEUP_TypeDef;

typedef union{                                                         /*!< INIT_DFI_DRAM_CLK_DISABLE register definition*/
  __IO  uint32_t                       INIT_DFI_DRAM_CLK_DISABLE;
  struct
  {
    __IO  uint32_t                       init_dfi_dram_clk_disable :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_INIT_DFI_DRAM_CLK_DISABLE_TypeDef;

typedef union{                                                         /*!< STAT_DFI_TRAINING_ERROR register definition*/
  __I   uint32_t                       STAT_DFI_TRAINING_ERROR;
  struct
  {
    __I   uint32_t                       stat_dfi_training_error :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_DFI_TRAINING_ERROR_TypeDef;

typedef union{                                                         /*!< STAT_DFI_ERROR register definition*/
  __I   uint32_t                       STAT_DFI_ERROR;
  struct
  {
    __I   uint32_t                       stat_dfi_error       :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_DFI_ERROR_TypeDef;

typedef union{                                                         /*!< STAT_DFI_ERROR_INFO register definition*/
  __I   uint32_t                       STAT_DFI_ERROR_INFO;
  struct
  {
    __I   uint32_t                       stat_dfi_error_info  :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_STAT_DFI_ERROR_INFO_TypeDef;

typedef union{                                                         /*!< CFG_DFI_DATA_BYTE_DISABLE register definition*/
  __IO  uint32_t                       CFG_DFI_DATA_BYTE_DISABLE;
  struct
  {
    __IO  uint32_t                       cfg_dfi_data_byte_disable :5;
    __I   uint32_t                       reserved             :27;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_DATA_BYTE_DISABLE_TypeDef;

typedef union{                                                         /*!< STAT_DFI_INIT_COMPLETE register definition*/
  __I   uint32_t                       STAT_DFI_INIT_COMPLETE;
  struct
  {
    __I   uint32_t                       stat_dfi_init_complete :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_DFI_INIT_COMPLETE_TypeDef;

typedef union{                                                         /*!< STAT_DFI_TRAINING_COMPLETE register definition*/
  __I   uint32_t                       STAT_DFI_TRAINING_COMPLETE;
  struct
  {
    __I   uint32_t                       stat_dfi_training_complete :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_STAT_DFI_TRAINING_COMPLETE_TypeDef;

typedef union{                                                         /*!< CFG_DFI_LVL_SEL register definition*/
  __IO  uint32_t                       CFG_DFI_LVL_SEL;
  struct
  {
    __IO  uint32_t                       cfg_dfi_lvl_sel      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_LVL_SEL_TypeDef;

typedef union{                                                         /*!< CFG_DFI_LVL_PERIODIC register definition*/
  __IO  uint32_t                       CFG_DFI_LVL_PERIODIC;
  struct
  {
    __IO  uint32_t                       cfg_dfi_lvl_periodic :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_LVL_PERIODIC_TypeDef;

typedef union{                                                         /*!< CFG_DFI_LVL_PATTERN register definition*/
  __IO  uint32_t                       CFG_DFI_LVL_PATTERN;
  struct
  {
    __IO  uint32_t                       cfg_dfi_lvl_pattern  :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_CFG_DFI_LVL_PATTERN_TypeDef;

typedef union{                                                         /*!< PHY_DFI_INIT_START register definition*/
  __IO  uint32_t                       PHY_DFI_INIT_START;
  struct
  {
    __IO  uint32_t                       phy_dfi_init_start   :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_DFI_INIT_START_TypeDef;

typedef union{                                                         /*!< CFG_AXI_START_ADDRESS_AXI1_0 register definition*/
  __IO  uint32_t                       CFG_AXI_START_ADDRESS_AXI1_0;
  struct
  {
    __IO  uint32_t                       cfg_axi_start_address_axi1_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI1_0_TypeDef;

typedef union{                                                         /*!< CFG_AXI_START_ADDRESS_AXI1_1 register definition*/
  __IO  uint32_t                       CFG_AXI_START_ADDRESS_AXI1_1;
  struct
  {
    __IO  uint32_t                       cfg_axi_start_address_axi1_1 :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI1_1_TypeDef;

typedef union{                                                         /*!< CFG_AXI_START_ADDRESS_AXI2_0 register definition*/
  __IO  uint32_t                       CFG_AXI_START_ADDRESS_AXI2_0;
  struct
  {
    __IO  uint32_t                       cfg_axi_start_address_axi2_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI2_0_TypeDef;

typedef union{                                                         /*!< CFG_AXI_START_ADDRESS_AXI2_1 register definition*/
  __IO  uint32_t                       CFG_AXI_START_ADDRESS_AXI2_1;
  struct
  {
    __IO  uint32_t                       cfg_axi_start_address_axi2_1 :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI2_1_TypeDef;

typedef union{                                                         /*!< CFG_AXI_END_ADDRESS_AXI1_0 register definition*/
  __IO  uint32_t                       CFG_AXI_END_ADDRESS_AXI1_0;
  struct
  {
    __IO  uint32_t                       cfg_axi_end_address_axi1_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI1_0_TypeDef;

typedef union{                                                         /*!< CFG_AXI_END_ADDRESS_AXI1_1 register definition*/
  __IO  uint32_t                       CFG_AXI_END_ADDRESS_AXI1_1;
  struct
  {
    __IO  uint32_t                       cfg_axi_end_address_axi1_1 :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI1_1_TypeDef;

typedef union{                                                         /*!< CFG_AXI_END_ADDRESS_AXI2_0 register definition*/
  __IO  uint32_t                       CFG_AXI_END_ADDRESS_AXI2_0;
  struct
  {
    __IO  uint32_t                       cfg_axi_end_address_axi2_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI2_0_TypeDef;

typedef union{                                                         /*!< CFG_AXI_END_ADDRESS_AXI2_1 register definition*/
  __IO  uint32_t                       CFG_AXI_END_ADDRESS_AXI2_1;
  struct
  {
    __IO  uint32_t                       cfg_axi_end_address_axi2_1 :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI2_1_TypeDef;

typedef union{                                                         /*!< CFG_MEM_START_ADDRESS_AXI1_0 register definition*/
  __IO  uint32_t                       CFG_MEM_START_ADDRESS_AXI1_0;
  struct
  {
    __IO  uint32_t                       cfg_mem_start_address_axi1_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI1_0_TypeDef;

typedef union{                                                         /*!< CFG_MEM_START_ADDRESS_AXI1_1 register definition*/
  __IO  uint32_t                       CFG_MEM_START_ADDRESS_AXI1_1;
  struct
  {
    __IO  uint32_t                       cfg_mem_start_address_axi1_1 :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI1_1_TypeDef;

typedef union{                                                         /*!< CFG_MEM_START_ADDRESS_AXI2_0 register definition*/
  __IO  uint32_t                       CFG_MEM_START_ADDRESS_AXI2_0;
  struct
  {
    __IO  uint32_t                       cfg_mem_start_address_axi2_0 :32;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI2_0_TypeDef;

typedef union{                                                         /*!< CFG_MEM_START_ADDRESS_AXI2_1 register definition*/
  __IO  uint32_t                       CFG_MEM_START_ADDRESS_AXI2_1;
  struct
  {
    __IO  uint32_t                       cfg_mem_start_address_axi2_1 :2;
    __I   uint32_t                       reserved             :30;
  } bitfield;
} DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI2_1_TypeDef;

typedef union{                                                         /*!< CFG_ENABLE_BUS_HOLD_AXI1 register definition*/
  __IO  uint32_t                       CFG_ENABLE_BUS_HOLD_AXI1;
  struct
  {
    __IO  uint32_t                       cfg_enable_bus_hold_axi1 :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ENABLE_BUS_HOLD_AXI1_TypeDef;

typedef union{                                                         /*!< CFG_ENABLE_BUS_HOLD_AXI2 register definition*/
  __IO  uint32_t                       CFG_ENABLE_BUS_HOLD_AXI2;
  struct
  {
    __IO  uint32_t                       cfg_enable_bus_hold_axi2 :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_CFG_ENABLE_BUS_HOLD_AXI2_TypeDef;

typedef union{                                                         /*!< CFG_AXI_AUTO_PCH register definition*/
  __IO  uint32_t                       CFG_AXI_AUTO_PCH;
  struct
  {
    __IO  uint32_t                       cfg_axi_auto_pch     :32;
  } bitfield;
} DDR_CSR_APB_CFG_AXI_AUTO_PCH_TypeDef;

typedef union{                                                         /*!< PHY_RESET_CONTROL register definition*/
  __IO  uint32_t                       PHY_RESET_CONTROL;
  struct
  {
    __IO  uint32_t                       phy_reset_control    :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_PHY_RESET_CONTROL_TypeDef;

typedef union{                                                         /*!< PHY_PC_RANK register definition*/
  __IO  uint32_t                       PHY_PC_RANK;
  struct
  {
    __IO  uint32_t                       phy_pc_rank          :4;
    __I   uint32_t                       reserved             :28;
  } bitfield;
} DDR_CSR_APB_PHY_PC_RANK_TypeDef;

typedef union{                                                         /*!< PHY_RANKS_TO_TRAIN register definition*/
  __IO  uint32_t                       PHY_RANKS_TO_TRAIN;
  struct
  {
    __IO  uint32_t                       phy_ranks_to_train   :16;
    __I   uint32_t                       reserved             :16;
  } bitfield;
} DDR_CSR_APB_PHY_RANKS_TO_TRAIN_TypeDef;

typedef union{                                                         /*!< PHY_WRITE_REQUEST register definition*/
  __IO  uint32_t                       PHY_WRITE_REQUEST;
  struct
  {
    __IO  uint32_t                       phy_write_request    :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_WRITE_REQUEST_TypeDef;

typedef union{                                                         /*!< PHY_WRITE_REQUEST_DONE register definition*/
  __I   uint32_t                       PHY_WRITE_REQUEST_DONE;
  struct
  {
    __I   uint32_t                       phy_write_request_done :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_WRITE_REQUEST_DONE_TypeDef;

typedef union{                                                         /*!< PHY_READ_REQUEST register definition*/
  __IO  uint32_t                       PHY_READ_REQUEST;
  struct
  {
    __IO  uint32_t                       phy_read_request     :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_READ_REQUEST_TypeDef;

typedef union{                                                         /*!< PHY_READ_REQUEST_DONE register definition*/
  __I   uint32_t                       PHY_READ_REQUEST_DONE;
  struct
  {
    __I   uint32_t                       phy_read_request_done :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_READ_REQUEST_DONE_TypeDef;

typedef union{                                                         /*!< PHY_WRITE_LEVEL_DELAY register definition*/
  __IO  uint32_t                       PHY_WRITE_LEVEL_DELAY;
  struct
  {
    __IO  uint32_t                       phy_write_level_delay :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_PHY_WRITE_LEVEL_DELAY_TypeDef;

typedef union{                                                         /*!< PHY_GATE_TRAIN_DELAY register definition*/
  __IO  uint32_t                       PHY_GATE_TRAIN_DELAY;
  struct
  {
    __IO  uint32_t                       phy_gate_train_delay :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_PHY_GATE_TRAIN_DELAY_TypeDef;

typedef union{                                                         /*!< PHY_EYE_TRAIN_DELAY register definition*/
  __IO  uint32_t                       PHY_EYE_TRAIN_DELAY;
  struct
  {
    __IO  uint32_t                       phy_eye_train_delay  :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_PHY_EYE_TRAIN_DELAY_TypeDef;

typedef union{                                                         /*!< PHY_EYE_PAT register definition*/
  __IO  uint32_t                       PHY_EYE_PAT;
  struct
  {
    __IO  uint32_t                       phy_eye_pat          :8;
    __I   uint32_t                       reserved             :24;
  } bitfield;
} DDR_CSR_APB_PHY_EYE_PAT_TypeDef;

typedef union{                                                         /*!< PHY_START_RECAL register definition*/
  __IO  uint32_t                       PHY_START_RECAL;
  struct
  {
    __IO  uint32_t                       phy_start_recal      :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_START_RECAL_TypeDef;

typedef union{                                                         /*!< PHY_CLR_DFI_LVL_PERIODIC register definition*/
  __IO  uint32_t                       PHY_CLR_DFI_LVL_PERIODIC;
  struct
  {
    __IO  uint32_t                       phy_clr_dfi_lvl_periodic :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_CLR_DFI_LVL_PERIODIC_TypeDef;

typedef union{                                                         /*!< PHY_TRAIN_STEP_ENABLE register definition*/
  __IO  uint32_t                       PHY_TRAIN_STEP_ENABLE;
  struct
  {
    __IO  uint32_t                       phy_train_step_enable :6;
    __I   uint32_t                       reserved             :26;
  } bitfield;
} DDR_CSR_APB_PHY_TRAIN_STEP_ENABLE_TypeDef;

typedef union{                                                         /*!< PHY_LPDDR_DQ_CAL_PAT register definition*/
  __IO  uint32_t                       PHY_LPDDR_DQ_CAL_PAT;
  struct
  {
    __IO  uint32_t                       phy_lpddr_dq_cal_pat :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_LPDDR_DQ_CAL_PAT_TypeDef;

typedef union{                                                         /*!< PHY_INDPNDT_TRAINING register definition*/
  __IO  uint32_t                       PHY_INDPNDT_TRAINING;
  struct
  {
    __IO  uint32_t                       phy_indpndt_training :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_INDPNDT_TRAINING_TypeDef;

typedef union{                                                         /*!< PHY_ENCODED_QUAD_CS register definition*/
  __IO  uint32_t                       PHY_ENCODED_QUAD_CS;
  struct
  {
    __IO  uint32_t                       phy_encoded_quad_cs  :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_ENCODED_QUAD_CS_TypeDef;

typedef union{                                                         /*!< PHY_HALF_CLK_DLY_ENABLE register definition*/
  __IO  uint32_t                       PHY_HALF_CLK_DLY_ENABLE;
  struct
  {
    __IO  uint32_t                       phy_half_clk_dly_enable :1;
    __I   uint32_t                       reserved             :31;
  } bitfield;
} DDR_CSR_APB_PHY_HALF_CLK_DLY_ENABLE_TypeDef;

/*------------ ADDR_MAP register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_MANUAL_ADDRESS_MAP_TypeDef CFG_MANUAL_ADDRESS_MAP;                             /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_CHIPADDR_MAP_TypeDef CFG_CHIPADDR_MAP;                                   /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_CIDADDR_MAP_TypeDef CFG_CIDADDR_MAP;                                    /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_MB_AUTOPCH_COL_BIT_POS_LOW_TypeDef CFG_MB_AUTOPCH_COL_BIT_POS_LOW;                     /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_CFG_MB_AUTOPCH_COL_BIT_POS_HIGH_TypeDef CFG_MB_AUTOPCH_COL_BIT_POS_HIGH;                    /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_CFG_BANKADDR_MAP_0_TypeDef CFG_BANKADDR_MAP_0;                                 /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_CFG_BANKADDR_MAP_1_TypeDef CFG_BANKADDR_MAP_1;                                 /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_CFG_ROWADDR_MAP_0_TypeDef CFG_ROWADDR_MAP_0;                                  /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_CFG_ROWADDR_MAP_1_TypeDef CFG_ROWADDR_MAP_1;                                  /*!< Offset: 0x20  */
  __IO  DDR_CSR_APB_CFG_ROWADDR_MAP_2_TypeDef CFG_ROWADDR_MAP_2;                                  /*!< Offset: 0x24  */
  __IO  DDR_CSR_APB_CFG_ROWADDR_MAP_3_TypeDef CFG_ROWADDR_MAP_3;                                  /*!< Offset: 0x28  */
  __IO  DDR_CSR_APB_CFG_COLADDR_MAP_0_TypeDef CFG_COLADDR_MAP_0;                                  /*!< Offset: 0x2c  */
  __IO  DDR_CSR_APB_CFG_COLADDR_MAP_1_TypeDef CFG_COLADDR_MAP_1;                                  /*!< Offset: 0x30  */
  __IO  DDR_CSR_APB_CFG_COLADDR_MAP_2_TypeDef CFG_COLADDR_MAP_2;                                  /*!< Offset: 0x34  */
} DDR_CSR_APB_ADDR_MAP_TypeDef;

/*------------ MC_BASE3 register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_VRCG_ENABLE_TypeDef CFG_VRCG_ENABLE;                                    /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_VRCG_DISABLE_TypeDef CFG_VRCG_DISABLE;                                   /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_WRITE_LATENCY_SET_TypeDef CFG_WRITE_LATENCY_SET;                              /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_THERMAL_OFFSET_TypeDef CFG_THERMAL_OFFSET;                                 /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_CFG_SOC_ODT_TypeDef CFG_SOC_ODT;                                        /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_CFG_ODTE_CK_TypeDef CFG_ODTE_CK;                                        /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_CFG_ODTE_CS_TypeDef CFG_ODTE_CS;                                        /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_CFG_ODTD_CA_TypeDef CFG_ODTD_CA;                                        /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_CFG_LPDDR4_FSP_OP_TypeDef CFG_LPDDR4_FSP_OP;                                  /*!< Offset: 0x20  */
  __IO  DDR_CSR_APB_CFG_GENERATE_REFRESH_ON_SRX_TypeDef CFG_GENERATE_REFRESH_ON_SRX;                        /*!< Offset: 0x24  */
  __IO  DDR_CSR_APB_CFG_DBI_CL_TypeDef CFG_DBI_CL;                                         /*!< Offset: 0x28  */
  __IO  DDR_CSR_APB_CFG_NON_DBI_CL_TypeDef CFG_NON_DBI_CL;                                     /*!< Offset: 0x2c  */
  __IO  DDR_CSR_APB_INIT_FORCE_WRITE_DATA_0_TypeDef INIT_FORCE_WRITE_DATA_0;                            /*!< Offset: 0x30  */
  __I   uint32_t                       UNUSED_SPACE0[63];                                  /*!< Offset: 0x34 */
} DDR_CSR_APB_MC_BASE3_TypeDef;

/*------------ MC_BASE1 register bundle definition -----------*/
typedef struct  /*!< Offset: 0x3c00 */
{
  __IO  DDR_CSR_APB_CFG_WRITE_CRC_TypeDef CFG_WRITE_CRC;                                      /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_MPR_READ_FORMAT_TypeDef CFG_MPR_READ_FORMAT;                                /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_WR_CMD_LAT_CRC_DM_TypeDef CFG_WR_CMD_LAT_CRC_DM;                              /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_FINE_GRAN_REF_MODE_TypeDef CFG_FINE_GRAN_REF_MODE;                             /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_CFG_TEMP_SENSOR_READOUT_TypeDef CFG_TEMP_SENSOR_READOUT;                            /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_CFG_PER_DRAM_ADDR_EN_TypeDef CFG_PER_DRAM_ADDR_EN;                               /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_CFG_GEARDOWN_MODE_TypeDef CFG_GEARDOWN_MODE;                                  /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_CFG_WR_PREAMBLE_TypeDef CFG_WR_PREAMBLE;                                    /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_CFG_RD_PREAMBLE_TypeDef CFG_RD_PREAMBLE;                                    /*!< Offset: 0x20  */
  __IO  DDR_CSR_APB_CFG_RD_PREAMB_TRN_MODE_TypeDef CFG_RD_PREAMB_TRN_MODE;                             /*!< Offset: 0x24  */
  __IO  DDR_CSR_APB_CFG_SR_ABORT_TypeDef CFG_SR_ABORT;                                       /*!< Offset: 0x28  */
  __IO  DDR_CSR_APB_CFG_CS_TO_CMDADDR_LATENCY_TypeDef CFG_CS_TO_CMDADDR_LATENCY;                          /*!< Offset: 0x2c  */
  __IO  DDR_CSR_APB_CFG_INT_VREF_MON_TypeDef CFG_INT_VREF_MON;                                   /*!< Offset: 0x30  */
  __IO  DDR_CSR_APB_CFG_TEMP_CTRL_REF_MODE_TypeDef CFG_TEMP_CTRL_REF_MODE;                             /*!< Offset: 0x34  */
  __IO  DDR_CSR_APB_CFG_TEMP_CTRL_REF_RANGE_TypeDef CFG_TEMP_CTRL_REF_RANGE;                            /*!< Offset: 0x38  */
  __IO  DDR_CSR_APB_CFG_MAX_PWR_DOWN_MODE_TypeDef CFG_MAX_PWR_DOWN_MODE;                              /*!< Offset: 0x3c  */
  __IO  DDR_CSR_APB_CFG_READ_DBI_TypeDef CFG_READ_DBI;                                       /*!< Offset: 0x40  */
  __IO  DDR_CSR_APB_CFG_WRITE_DBI_TypeDef CFG_WRITE_DBI;                                      /*!< Offset: 0x44  */
  __IO  DDR_CSR_APB_CFG_DATA_MASK_TypeDef CFG_DATA_MASK;                                      /*!< Offset: 0x48  */
  __IO  DDR_CSR_APB_CFG_CA_PARITY_PERSIST_ERR_TypeDef CFG_CA_PARITY_PERSIST_ERR;                          /*!< Offset: 0x4c  */
  __IO  DDR_CSR_APB_CFG_RTT_PARK_TypeDef CFG_RTT_PARK;                                       /*!< Offset: 0x50  */
  __IO  DDR_CSR_APB_CFG_ODT_INBUF_4_PD_TypeDef CFG_ODT_INBUF_4_PD;                                 /*!< Offset: 0x54  */
  __IO  DDR_CSR_APB_CFG_CA_PARITY_ERR_STATUS_TypeDef CFG_CA_PARITY_ERR_STATUS;                           /*!< Offset: 0x58  */
  __IO  DDR_CSR_APB_CFG_CRC_ERROR_CLEAR_TypeDef CFG_CRC_ERROR_CLEAR;                                /*!< Offset: 0x5c  */
  __IO  DDR_CSR_APB_CFG_CA_PARITY_LATENCY_TypeDef CFG_CA_PARITY_LATENCY;                              /*!< Offset: 0x60  */
  __IO  DDR_CSR_APB_CFG_CCD_S_TypeDef  CFG_CCD_S;                                          /*!< Offset: 0x64  */
  __IO  DDR_CSR_APB_CFG_CCD_L_TypeDef  CFG_CCD_L;                                          /*!< Offset: 0x68  */
  __IO  DDR_CSR_APB_CFG_VREFDQ_TRN_ENABLE_TypeDef CFG_VREFDQ_TRN_ENABLE;                              /*!< Offset: 0x6c  */
  __IO  DDR_CSR_APB_CFG_VREFDQ_TRN_RANGE_TypeDef CFG_VREFDQ_TRN_RANGE;                               /*!< Offset: 0x70  */
  __IO  DDR_CSR_APB_CFG_VREFDQ_TRN_VALUE_TypeDef CFG_VREFDQ_TRN_VALUE;                               /*!< Offset: 0x74  */
  __IO  DDR_CSR_APB_CFG_RRD_S_TypeDef  CFG_RRD_S;                                          /*!< Offset: 0x78  */
  __IO  DDR_CSR_APB_CFG_RRD_L_TypeDef  CFG_RRD_L;                                          /*!< Offset: 0x7c  */
  __IO  DDR_CSR_APB_CFG_WTR_S_TypeDef  CFG_WTR_S;                                          /*!< Offset: 0x80  */
  __IO  DDR_CSR_APB_CFG_WTR_L_TypeDef  CFG_WTR_L;                                          /*!< Offset: 0x84  */
  __IO  DDR_CSR_APB_CFG_WTR_S_CRC_DM_TypeDef CFG_WTR_S_CRC_DM;                                   /*!< Offset: 0x88  */
  __IO  DDR_CSR_APB_CFG_WTR_L_CRC_DM_TypeDef CFG_WTR_L_CRC_DM;                                   /*!< Offset: 0x8c  */
  __IO  DDR_CSR_APB_CFG_WR_CRC_DM_TypeDef CFG_WR_CRC_DM;                                      /*!< Offset: 0x90  */
  __IO  DDR_CSR_APB_CFG_RFC1_TypeDef   CFG_RFC1;                                           /*!< Offset: 0x94  */
  __IO  DDR_CSR_APB_CFG_RFC2_TypeDef   CFG_RFC2;                                           /*!< Offset: 0x98  */
  __IO  DDR_CSR_APB_CFG_RFC4_TypeDef   CFG_RFC4;                                           /*!< Offset: 0x9c  */
  __I   uint32_t                       UNUSED_SPACE0[9];                                   /*!< Offset: 0xa0 */
  __IO  DDR_CSR_APB_CFG_NIBBLE_DEVICES_TypeDef CFG_NIBBLE_DEVICES;                                 /*!< Offset: 0xc4  */
  __I   uint32_t                       UNUSED_SPACE1[6];                                   /*!< Offset: 0xc8 */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS0_0_TypeDef CFG_BIT_MAP_INDEX_CS0_0;                            /*!< Offset: 0xe0  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS0_1_TypeDef CFG_BIT_MAP_INDEX_CS0_1;                            /*!< Offset: 0xe4  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS1_0_TypeDef CFG_BIT_MAP_INDEX_CS1_0;                            /*!< Offset: 0xe8  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS1_1_TypeDef CFG_BIT_MAP_INDEX_CS1_1;                            /*!< Offset: 0xec  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS2_0_TypeDef CFG_BIT_MAP_INDEX_CS2_0;                            /*!< Offset: 0xf0  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS2_1_TypeDef CFG_BIT_MAP_INDEX_CS2_1;                            /*!< Offset: 0xf4  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS3_0_TypeDef CFG_BIT_MAP_INDEX_CS3_0;                            /*!< Offset: 0xf8  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS3_1_TypeDef CFG_BIT_MAP_INDEX_CS3_1;                            /*!< Offset: 0xfc  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS4_0_TypeDef CFG_BIT_MAP_INDEX_CS4_0;                            /*!< Offset: 0x100  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS4_1_TypeDef CFG_BIT_MAP_INDEX_CS4_1;                            /*!< Offset: 0x104  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS5_0_TypeDef CFG_BIT_MAP_INDEX_CS5_0;                            /*!< Offset: 0x108  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS5_1_TypeDef CFG_BIT_MAP_INDEX_CS5_1;                            /*!< Offset: 0x10c  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS6_0_TypeDef CFG_BIT_MAP_INDEX_CS6_0;                            /*!< Offset: 0x110  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS6_1_TypeDef CFG_BIT_MAP_INDEX_CS6_1;                            /*!< Offset: 0x114  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS7_0_TypeDef CFG_BIT_MAP_INDEX_CS7_0;                            /*!< Offset: 0x118  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS7_1_TypeDef CFG_BIT_MAP_INDEX_CS7_1;                            /*!< Offset: 0x11c  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS8_0_TypeDef CFG_BIT_MAP_INDEX_CS8_0;                            /*!< Offset: 0x120  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS8_1_TypeDef CFG_BIT_MAP_INDEX_CS8_1;                            /*!< Offset: 0x124  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS9_0_TypeDef CFG_BIT_MAP_INDEX_CS9_0;                            /*!< Offset: 0x128  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS9_1_TypeDef CFG_BIT_MAP_INDEX_CS9_1;                            /*!< Offset: 0x12c  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS10_0_TypeDef CFG_BIT_MAP_INDEX_CS10_0;                           /*!< Offset: 0x130  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS10_1_TypeDef CFG_BIT_MAP_INDEX_CS10_1;                           /*!< Offset: 0x134  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS11_0_TypeDef CFG_BIT_MAP_INDEX_CS11_0;                           /*!< Offset: 0x138  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS11_1_TypeDef CFG_BIT_MAP_INDEX_CS11_1;                           /*!< Offset: 0x13c  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS12_0_TypeDef CFG_BIT_MAP_INDEX_CS12_0;                           /*!< Offset: 0x140  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS12_1_TypeDef CFG_BIT_MAP_INDEX_CS12_1;                           /*!< Offset: 0x144  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS13_0_TypeDef CFG_BIT_MAP_INDEX_CS13_0;                           /*!< Offset: 0x148  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS13_1_TypeDef CFG_BIT_MAP_INDEX_CS13_1;                           /*!< Offset: 0x14c  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS14_0_TypeDef CFG_BIT_MAP_INDEX_CS14_0;                           /*!< Offset: 0x150  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS14_1_TypeDef CFG_BIT_MAP_INDEX_CS14_1;                           /*!< Offset: 0x154  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS15_0_TypeDef CFG_BIT_MAP_INDEX_CS15_0;                           /*!< Offset: 0x158  */
  __IO  DDR_CSR_APB_CFG_BIT_MAP_INDEX_CS15_1_TypeDef CFG_BIT_MAP_INDEX_CS15_1;                           /*!< Offset: 0x15c  */
  __IO  DDR_CSR_APB_CFG_NUM_LOGICAL_RANKS_PER_3DS_TypeDef CFG_NUM_LOGICAL_RANKS_PER_3DS;                      /*!< Offset: 0x160  */
  __IO  DDR_CSR_APB_CFG_RFC_DLR1_TypeDef CFG_RFC_DLR1;                                       /*!< Offset: 0x164  */
  __IO  DDR_CSR_APB_CFG_RFC_DLR2_TypeDef CFG_RFC_DLR2;                                       /*!< Offset: 0x168  */
  __IO  DDR_CSR_APB_CFG_RFC_DLR4_TypeDef CFG_RFC_DLR4;                                       /*!< Offset: 0x16c  */
  __IO  DDR_CSR_APB_CFG_RRD_DLR_TypeDef CFG_RRD_DLR;                                        /*!< Offset: 0x170  */
  __IO  DDR_CSR_APB_CFG_FAW_DLR_TypeDef CFG_FAW_DLR;                                        /*!< Offset: 0x174  */
  __I   uint32_t                       UNUSED_SPACE2[8];                                   /*!< Offset: 0x178 */
  __IO  DDR_CSR_APB_CFG_ADVANCE_ACTIVATE_READY_TypeDef CFG_ADVANCE_ACTIVATE_READY;                         /*!< Offset: 0x198  */
  __I   uint32_t                       UNUSED_SPACE3[6];                                   /*!< Offset: 0x19c */
} DDR_CSR_APB_MC_BASE1_TypeDef;

/*------------ MC_BASE2 register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CTRLR_SOFT_RESET_N_TypeDef CTRLR_SOFT_RESET_N;                                 /*!< Offset: 0x0  */
  __I   uint32_t                       UNUSED_SPACE0;                                      /*!< Offset: 0x4 */
  __IO  DDR_CSR_APB_CFG_LOOKAHEAD_PCH_TypeDef CFG_LOOKAHEAD_PCH;                                  /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_LOOKAHEAD_ACT_TypeDef CFG_LOOKAHEAD_ACT;                                  /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_INIT_AUTOINIT_DISABLE_TypeDef INIT_AUTOINIT_DISABLE;                              /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_INIT_FORCE_RESET_TypeDef INIT_FORCE_RESET;                                   /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_INIT_GEARDOWN_EN_TypeDef INIT_GEARDOWN_EN;                                   /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_INIT_DISABLE_CKE_TypeDef INIT_DISABLE_CKE;                                   /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_INIT_CS_TypeDef    INIT_CS;                                            /*!< Offset: 0x20  */
  __IO  DDR_CSR_APB_INIT_PRECHARGE_ALL_TypeDef INIT_PRECHARGE_ALL;                                 /*!< Offset: 0x24  */
  __IO  DDR_CSR_APB_INIT_REFRESH_TypeDef INIT_REFRESH;                                       /*!< Offset: 0x28  */
  __IO  DDR_CSR_APB_INIT_ZQ_CAL_REQ_TypeDef INIT_ZQ_CAL_REQ;                                    /*!< Offset: 0x2c  */
  __I   DDR_CSR_APB_INIT_ACK_TypeDef   INIT_ACK;                                           /*!< Offset: 0x30  */
  __IO  DDR_CSR_APB_CFG_BL_TypeDef     CFG_BL;                                             /*!< Offset: 0x34  */
  __IO  DDR_CSR_APB_CTRLR_INIT_TypeDef CTRLR_INIT;                                         /*!< Offset: 0x38  */
  __I   DDR_CSR_APB_CTRLR_INIT_DONE_TypeDef CTRLR_INIT_DONE;                                    /*!< Offset: 0x3c  */
  __IO  DDR_CSR_APB_CFG_AUTO_REF_EN_TypeDef CFG_AUTO_REF_EN;                                    /*!< Offset: 0x40  */
  __IO  DDR_CSR_APB_CFG_RAS_TypeDef    CFG_RAS;                                            /*!< Offset: 0x44  */
  __IO  DDR_CSR_APB_CFG_RCD_TypeDef    CFG_RCD;                                            /*!< Offset: 0x48  */
  __IO  DDR_CSR_APB_CFG_RRD_TypeDef    CFG_RRD;                                            /*!< Offset: 0x4c  */
  __IO  DDR_CSR_APB_CFG_RP_TypeDef     CFG_RP;                                             /*!< Offset: 0x50  */
  __IO  DDR_CSR_APB_CFG_RC_TypeDef     CFG_RC;                                             /*!< Offset: 0x54  */
  __IO  DDR_CSR_APB_CFG_FAW_TypeDef    CFG_FAW;                                            /*!< Offset: 0x58  */
  __IO  DDR_CSR_APB_CFG_RFC_TypeDef    CFG_RFC;                                            /*!< Offset: 0x5c  */
  __IO  DDR_CSR_APB_CFG_RTP_TypeDef    CFG_RTP;                                            /*!< Offset: 0x60  */
  __IO  DDR_CSR_APB_CFG_WR_TypeDef     CFG_WR;                                             /*!< Offset: 0x64  */
  __IO  DDR_CSR_APB_CFG_WTR_TypeDef    CFG_WTR;                                            /*!< Offset: 0x68  */
  __I   uint32_t                       UNUSED_SPACE1;                                      /*!< Offset: 0x6c */
  __IO  DDR_CSR_APB_CFG_PASR_TypeDef   CFG_PASR;                                           /*!< Offset: 0x70  */
  __IO  DDR_CSR_APB_CFG_XP_TypeDef     CFG_XP;                                             /*!< Offset: 0x74  */
  __IO  DDR_CSR_APB_CFG_XSR_TypeDef    CFG_XSR;                                            /*!< Offset: 0x78  */
  __I   uint32_t                       UNUSED_SPACE2;                                      /*!< Offset: 0x7c */
  __IO  DDR_CSR_APB_CFG_CL_TypeDef     CFG_CL;                                             /*!< Offset: 0x80  */
  __I   uint32_t                       UNUSED_SPACE3;                                      /*!< Offset: 0x84 */
  __IO  DDR_CSR_APB_CFG_READ_TO_WRITE_TypeDef CFG_READ_TO_WRITE;                                  /*!< Offset: 0x88  */
  __IO  DDR_CSR_APB_CFG_WRITE_TO_WRITE_TypeDef CFG_WRITE_TO_WRITE;                                 /*!< Offset: 0x8c  */
  __IO  DDR_CSR_APB_CFG_READ_TO_READ_TypeDef CFG_READ_TO_READ;                                   /*!< Offset: 0x90  */
  __IO  DDR_CSR_APB_CFG_WRITE_TO_READ_TypeDef CFG_WRITE_TO_READ;                                  /*!< Offset: 0x94  */
  __IO  DDR_CSR_APB_CFG_READ_TO_WRITE_ODT_TypeDef CFG_READ_TO_WRITE_ODT;                              /*!< Offset: 0x98  */
  __IO  DDR_CSR_APB_CFG_WRITE_TO_WRITE_ODT_TypeDef CFG_WRITE_TO_WRITE_ODT;                             /*!< Offset: 0x9c  */
  __IO  DDR_CSR_APB_CFG_READ_TO_READ_ODT_TypeDef CFG_READ_TO_READ_ODT;                               /*!< Offset: 0xa0  */
  __IO  DDR_CSR_APB_CFG_WRITE_TO_READ_ODT_TypeDef CFG_WRITE_TO_READ_ODT;                              /*!< Offset: 0xa4  */
  __IO  DDR_CSR_APB_CFG_MIN_READ_IDLE_TypeDef CFG_MIN_READ_IDLE;                                  /*!< Offset: 0xa8  */
  __IO  DDR_CSR_APB_CFG_MRD_TypeDef    CFG_MRD;                                            /*!< Offset: 0xac  */
  __IO  DDR_CSR_APB_CFG_BT_TypeDef     CFG_BT;                                             /*!< Offset: 0xb0  */
  __IO  DDR_CSR_APB_CFG_DS_TypeDef     CFG_DS;                                             /*!< Offset: 0xb4  */
  __IO  DDR_CSR_APB_CFG_QOFF_TypeDef   CFG_QOFF;                                           /*!< Offset: 0xb8  */
  __I   uint32_t                       UNUSED_SPACE4[2];                                   /*!< Offset: 0xbc */
  __IO  DDR_CSR_APB_CFG_RTT_TypeDef    CFG_RTT;                                            /*!< Offset: 0xc4  */
  __IO  DDR_CSR_APB_CFG_DLL_DISABLE_TypeDef CFG_DLL_DISABLE;                                    /*!< Offset: 0xc8  */
  __IO  DDR_CSR_APB_CFG_REF_PER_TypeDef CFG_REF_PER;                                        /*!< Offset: 0xcc  */
  __IO  DDR_CSR_APB_CFG_STARTUP_DELAY_TypeDef CFG_STARTUP_DELAY;                                  /*!< Offset: 0xd0  */
  __IO  DDR_CSR_APB_CFG_MEM_COLBITS_TypeDef CFG_MEM_COLBITS;                                    /*!< Offset: 0xd4  */
  __IO  DDR_CSR_APB_CFG_MEM_ROWBITS_TypeDef CFG_MEM_ROWBITS;                                    /*!< Offset: 0xd8  */
  __IO  DDR_CSR_APB_CFG_MEM_BANKBITS_TypeDef CFG_MEM_BANKBITS;                                   /*!< Offset: 0xdc  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS0_TypeDef CFG_ODT_RD_MAP_CS0;                                 /*!< Offset: 0xe0  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS1_TypeDef CFG_ODT_RD_MAP_CS1;                                 /*!< Offset: 0xe4  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS2_TypeDef CFG_ODT_RD_MAP_CS2;                                 /*!< Offset: 0xe8  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS3_TypeDef CFG_ODT_RD_MAP_CS3;                                 /*!< Offset: 0xec  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS4_TypeDef CFG_ODT_RD_MAP_CS4;                                 /*!< Offset: 0xf0  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS5_TypeDef CFG_ODT_RD_MAP_CS5;                                 /*!< Offset: 0xf4  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS6_TypeDef CFG_ODT_RD_MAP_CS6;                                 /*!< Offset: 0xf8  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_MAP_CS7_TypeDef CFG_ODT_RD_MAP_CS7;                                 /*!< Offset: 0xfc  */
  __I   uint32_t                       UNUSED_SPACE5[8];                                   /*!< Offset: 0x100 */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS0_TypeDef CFG_ODT_WR_MAP_CS0;                                 /*!< Offset: 0x120  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS1_TypeDef CFG_ODT_WR_MAP_CS1;                                 /*!< Offset: 0x124  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS2_TypeDef CFG_ODT_WR_MAP_CS2;                                 /*!< Offset: 0x128  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS3_TypeDef CFG_ODT_WR_MAP_CS3;                                 /*!< Offset: 0x12c  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS4_TypeDef CFG_ODT_WR_MAP_CS4;                                 /*!< Offset: 0x130  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS5_TypeDef CFG_ODT_WR_MAP_CS5;                                 /*!< Offset: 0x134  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS6_TypeDef CFG_ODT_WR_MAP_CS6;                                 /*!< Offset: 0x138  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_MAP_CS7_TypeDef CFG_ODT_WR_MAP_CS7;                                 /*!< Offset: 0x13c  */
  __I   uint32_t                       UNUSED_SPACE6[8];                                   /*!< Offset: 0x140 */
  __IO  DDR_CSR_APB_CFG_ODT_RD_TURN_ON_TypeDef CFG_ODT_RD_TURN_ON;                                 /*!< Offset: 0x160  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_TURN_ON_TypeDef CFG_ODT_WR_TURN_ON;                                 /*!< Offset: 0x164  */
  __IO  DDR_CSR_APB_CFG_ODT_RD_TURN_OFF_TypeDef CFG_ODT_RD_TURN_OFF;                                /*!< Offset: 0x168  */
  __IO  DDR_CSR_APB_CFG_ODT_WR_TURN_OFF_TypeDef CFG_ODT_WR_TURN_OFF;                                /*!< Offset: 0x16c  */
  __I   uint32_t                       UNUSED_SPACE7[2];                                   /*!< Offset: 0x170 */
  __IO  DDR_CSR_APB_CFG_EMR3_TypeDef   CFG_EMR3;                                           /*!< Offset: 0x178  */
  __IO  DDR_CSR_APB_CFG_TWO_T_TypeDef  CFG_TWO_T;                                          /*!< Offset: 0x17c  */
  __IO  DDR_CSR_APB_CFG_TWO_T_SEL_CYCLE_TypeDef CFG_TWO_T_SEL_CYCLE;                                /*!< Offset: 0x180  */
  __IO  DDR_CSR_APB_CFG_REGDIMM_TypeDef CFG_REGDIMM;                                        /*!< Offset: 0x184  */
  __IO  DDR_CSR_APB_CFG_MOD_TypeDef    CFG_MOD;                                            /*!< Offset: 0x188  */
  __IO  DDR_CSR_APB_CFG_XS_TypeDef     CFG_XS;                                             /*!< Offset: 0x18c  */
  __IO  DDR_CSR_APB_CFG_XSDLL_TypeDef  CFG_XSDLL;                                          /*!< Offset: 0x190  */
  __IO  DDR_CSR_APB_CFG_XPR_TypeDef    CFG_XPR;                                            /*!< Offset: 0x194  */
  __IO  DDR_CSR_APB_CFG_AL_MODE_TypeDef CFG_AL_MODE;                                        /*!< Offset: 0x198  */
  __IO  DDR_CSR_APB_CFG_CWL_TypeDef    CFG_CWL;                                            /*!< Offset: 0x19c  */
  __IO  DDR_CSR_APB_CFG_BL_MODE_TypeDef CFG_BL_MODE;                                        /*!< Offset: 0x1a0  */
  __IO  DDR_CSR_APB_CFG_TDQS_TypeDef   CFG_TDQS;                                           /*!< Offset: 0x1a4  */
  __IO  DDR_CSR_APB_CFG_RTT_WR_TypeDef CFG_RTT_WR;                                         /*!< Offset: 0x1a8  */
  __IO  DDR_CSR_APB_CFG_LP_ASR_TypeDef CFG_LP_ASR;                                         /*!< Offset: 0x1ac  */
  __IO  DDR_CSR_APB_CFG_AUTO_SR_TypeDef CFG_AUTO_SR;                                        /*!< Offset: 0x1b0  */
  __IO  DDR_CSR_APB_CFG_SRT_TypeDef    CFG_SRT;                                            /*!< Offset: 0x1b4  */
  __IO  DDR_CSR_APB_CFG_ADDR_MIRROR_TypeDef CFG_ADDR_MIRROR;                                    /*!< Offset: 0x1b8  */
  __IO  DDR_CSR_APB_CFG_ZQ_CAL_TYPE_TypeDef CFG_ZQ_CAL_TYPE;                                    /*!< Offset: 0x1bc  */
  __IO  DDR_CSR_APB_CFG_ZQ_CAL_PER_TypeDef CFG_ZQ_CAL_PER;                                     /*!< Offset: 0x1c0  */
  __IO  DDR_CSR_APB_CFG_AUTO_ZQ_CAL_EN_TypeDef CFG_AUTO_ZQ_CAL_EN;                                 /*!< Offset: 0x1c4  */
  __IO  DDR_CSR_APB_CFG_MEMORY_TYPE_TypeDef CFG_MEMORY_TYPE;                                    /*!< Offset: 0x1c8  */
  __IO  DDR_CSR_APB_CFG_ONLY_SRANK_CMDS_TypeDef CFG_ONLY_SRANK_CMDS;                                /*!< Offset: 0x1cc  */
  __IO  DDR_CSR_APB_CFG_NUM_RANKS_TypeDef CFG_NUM_RANKS;                                      /*!< Offset: 0x1d0  */
  __IO  DDR_CSR_APB_CFG_QUAD_RANK_TypeDef CFG_QUAD_RANK;                                      /*!< Offset: 0x1d4  */
  __I   uint32_t                       UNUSED_SPACE8;                                      /*!< Offset: 0x1d8 */
  __IO  DDR_CSR_APB_CFG_EARLY_RANK_TO_WR_START_TypeDef CFG_EARLY_RANK_TO_WR_START;                         /*!< Offset: 0x1dc  */
  __IO  DDR_CSR_APB_CFG_EARLY_RANK_TO_RD_START_TypeDef CFG_EARLY_RANK_TO_RD_START;                         /*!< Offset: 0x1e0  */
  __IO  DDR_CSR_APB_CFG_PASR_BANK_TypeDef CFG_PASR_BANK;                                      /*!< Offset: 0x1e4  */
  __IO  DDR_CSR_APB_CFG_PASR_SEG_TypeDef CFG_PASR_SEG;                                       /*!< Offset: 0x1e8  */
  __IO  DDR_CSR_APB_INIT_MRR_MODE_TypeDef INIT_MRR_MODE;                                      /*!< Offset: 0x1ec  */
  __IO  DDR_CSR_APB_INIT_MR_W_REQ_TypeDef INIT_MR_W_REQ;                                      /*!< Offset: 0x1f0  */
  __IO  DDR_CSR_APB_INIT_MR_ADDR_TypeDef INIT_MR_ADDR;                                       /*!< Offset: 0x1f4  */
  __IO  DDR_CSR_APB_INIT_MR_WR_DATA_TypeDef INIT_MR_WR_DATA;                                    /*!< Offset: 0x1f8  */
  __IO  DDR_CSR_APB_INIT_MR_WR_MASK_TypeDef INIT_MR_WR_MASK;                                    /*!< Offset: 0x1fc  */
  __IO  DDR_CSR_APB_INIT_NOP_TypeDef   INIT_NOP;                                           /*!< Offset: 0x200  */
  __IO  DDR_CSR_APB_CFG_INIT_DURATION_TypeDef CFG_INIT_DURATION;                                  /*!< Offset: 0x204  */
  __IO  DDR_CSR_APB_CFG_ZQINIT_CAL_DURATION_TypeDef CFG_ZQINIT_CAL_DURATION;                            /*!< Offset: 0x208  */
  __IO  DDR_CSR_APB_CFG_ZQ_CAL_L_DURATION_TypeDef CFG_ZQ_CAL_L_DURATION;                              /*!< Offset: 0x20c  */
  __IO  DDR_CSR_APB_CFG_ZQ_CAL_S_DURATION_TypeDef CFG_ZQ_CAL_S_DURATION;                              /*!< Offset: 0x210  */
  __IO  DDR_CSR_APB_CFG_ZQ_CAL_R_DURATION_TypeDef CFG_ZQ_CAL_R_DURATION;                              /*!< Offset: 0x214  */
  __IO  DDR_CSR_APB_CFG_MRR_TypeDef    CFG_MRR;                                            /*!< Offset: 0x218  */
  __IO  DDR_CSR_APB_CFG_MRW_TypeDef    CFG_MRW;                                            /*!< Offset: 0x21c  */
  __IO  DDR_CSR_APB_CFG_ODT_POWERDOWN_TypeDef CFG_ODT_POWERDOWN;                                  /*!< Offset: 0x220  */
  __IO  DDR_CSR_APB_CFG_WL_TypeDef     CFG_WL;                                             /*!< Offset: 0x224  */
  __IO  DDR_CSR_APB_CFG_RL_TypeDef     CFG_RL;                                             /*!< Offset: 0x228  */
  __IO  DDR_CSR_APB_CFG_CAL_READ_PERIOD_TypeDef CFG_CAL_READ_PERIOD;                                /*!< Offset: 0x22c  */
  __IO  DDR_CSR_APB_CFG_NUM_CAL_READS_TypeDef CFG_NUM_CAL_READS;                                  /*!< Offset: 0x230  */
  __IO  DDR_CSR_APB_INIT_SELF_REFRESH_TypeDef INIT_SELF_REFRESH;                                  /*!< Offset: 0x234  */
  __I   DDR_CSR_APB_INIT_SELF_REFRESH_STATUS_TypeDef INIT_SELF_REFRESH_STATUS;                           /*!< Offset: 0x238  */
  __IO  DDR_CSR_APB_INIT_POWER_DOWN_TypeDef INIT_POWER_DOWN;                                    /*!< Offset: 0x23c  */
  __I   DDR_CSR_APB_INIT_POWER_DOWN_STATUS_TypeDef INIT_POWER_DOWN_STATUS;                             /*!< Offset: 0x240  */
  __IO  DDR_CSR_APB_INIT_FORCE_WRITE_TypeDef INIT_FORCE_WRITE;                                   /*!< Offset: 0x244  */
  __IO  DDR_CSR_APB_INIT_FORCE_WRITE_CS_TypeDef INIT_FORCE_WRITE_CS;                                /*!< Offset: 0x248  */
  __IO  DDR_CSR_APB_CFG_CTRLR_INIT_DISABLE_TypeDef CFG_CTRLR_INIT_DISABLE;                             /*!< Offset: 0x24c  */
  __I   DDR_CSR_APB_CTRLR_READY_TypeDef CTRLR_READY;                                        /*!< Offset: 0x250  */
  __I   DDR_CSR_APB_INIT_RDIMM_READY_TypeDef INIT_RDIMM_READY;                                   /*!< Offset: 0x254  */
  __IO  DDR_CSR_APB_INIT_RDIMM_COMPLETE_TypeDef INIT_RDIMM_COMPLETE;                                /*!< Offset: 0x258  */
  __IO  DDR_CSR_APB_CFG_RDIMM_LAT_TypeDef CFG_RDIMM_LAT;                                      /*!< Offset: 0x25c  */
  __IO  DDR_CSR_APB_CFG_RDIMM_BSIDE_INVERT_TypeDef CFG_RDIMM_BSIDE_INVERT;                             /*!< Offset: 0x260  */
  __IO  DDR_CSR_APB_CFG_LRDIMM_TypeDef CFG_LRDIMM;                                         /*!< Offset: 0x264  */
  __IO  DDR_CSR_APB_INIT_MEMORY_RESET_MASK_TypeDef INIT_MEMORY_RESET_MASK;                             /*!< Offset: 0x268  */
  __IO  DDR_CSR_APB_CFG_RD_PREAMB_TOGGLE_TypeDef CFG_RD_PREAMB_TOGGLE;                               /*!< Offset: 0x26c  */
  __IO  DDR_CSR_APB_CFG_RD_POSTAMBLE_TypeDef CFG_RD_POSTAMBLE;                                   /*!< Offset: 0x270  */
  __IO  DDR_CSR_APB_CFG_PU_CAL_TypeDef CFG_PU_CAL;                                         /*!< Offset: 0x274  */
  __IO  DDR_CSR_APB_CFG_DQ_ODT_TypeDef CFG_DQ_ODT;                                         /*!< Offset: 0x278  */
  __IO  DDR_CSR_APB_CFG_CA_ODT_TypeDef CFG_CA_ODT;                                         /*!< Offset: 0x27c  */
  __IO  DDR_CSR_APB_CFG_ZQLATCH_DURATION_TypeDef CFG_ZQLATCH_DURATION;                               /*!< Offset: 0x280  */
  __IO  DDR_CSR_APB_INIT_CAL_SELECT_TypeDef INIT_CAL_SELECT;                                    /*!< Offset: 0x284  */
  __IO  DDR_CSR_APB_INIT_CAL_L_R_REQ_TypeDef INIT_CAL_L_R_REQ;                                   /*!< Offset: 0x288  */
  __IO  DDR_CSR_APB_INIT_CAL_L_B_SIZE_TypeDef INIT_CAL_L_B_SIZE;                                  /*!< Offset: 0x28c  */
  __I   DDR_CSR_APB_INIT_CAL_L_R_ACK_TypeDef INIT_CAL_L_R_ACK;                                   /*!< Offset: 0x290  */
  __I   DDR_CSR_APB_INIT_CAL_L_READ_COMPLETE_TypeDef INIT_CAL_L_READ_COMPLETE;                           /*!< Offset: 0x294  */
  __I   uint32_t                       UNUSED_SPACE9[2];                                   /*!< Offset: 0x298 */
  __IO  DDR_CSR_APB_INIT_RWFIFO_TypeDef INIT_RWFIFO;                                        /*!< Offset: 0x2a0  */
  __IO  DDR_CSR_APB_INIT_RD_DQCAL_TypeDef INIT_RD_DQCAL;                                      /*!< Offset: 0x2a4  */
  __IO  DDR_CSR_APB_INIT_START_DQSOSC_TypeDef INIT_START_DQSOSC;                                  /*!< Offset: 0x2a8  */
  __IO  DDR_CSR_APB_INIT_STOP_DQSOSC_TypeDef INIT_STOP_DQSOSC;                                   /*!< Offset: 0x2ac  */
  __IO  DDR_CSR_APB_INIT_ZQ_CAL_START_TypeDef INIT_ZQ_CAL_START;                                  /*!< Offset: 0x2b0  */
  __IO  DDR_CSR_APB_CFG_WR_POSTAMBLE_TypeDef CFG_WR_POSTAMBLE;                                   /*!< Offset: 0x2b4  */
  __I   uint32_t                       UNUSED_SPACE10;                                     /*!< Offset: 0x2b8 */
  __IO  DDR_CSR_APB_INIT_CAL_L_ADDR_0_TypeDef INIT_CAL_L_ADDR_0;                                  /*!< Offset: 0x2bc  */
  __IO  DDR_CSR_APB_INIT_CAL_L_ADDR_1_TypeDef INIT_CAL_L_ADDR_1;                                  /*!< Offset: 0x2c0  */
  __IO  DDR_CSR_APB_CFG_CTRLUPD_TRIG_TypeDef CFG_CTRLUPD_TRIG;                                   /*!< Offset: 0x2c4  */
  __IO  DDR_CSR_APB_CFG_CTRLUPD_START_DELAY_TypeDef CFG_CTRLUPD_START_DELAY;                            /*!< Offset: 0x2c8  */
  __IO  DDR_CSR_APB_CFG_DFI_T_CTRLUPD_MAX_TypeDef CFG_DFI_T_CTRLUPD_MAX;                              /*!< Offset: 0x2cc  */
  __IO  DDR_CSR_APB_CFG_CTRLR_BUSY_SEL_TypeDef CFG_CTRLR_BUSY_SEL;                                 /*!< Offset: 0x2d0  */
  __IO  DDR_CSR_APB_CFG_CTRLR_BUSY_VALUE_TypeDef CFG_CTRLR_BUSY_VALUE;                               /*!< Offset: 0x2d4  */
  __IO  DDR_CSR_APB_CFG_CTRLR_BUSY_TURN_OFF_DELAY_TypeDef CFG_CTRLR_BUSY_TURN_OFF_DELAY;                      /*!< Offset: 0x2d8  */
  __IO  DDR_CSR_APB_CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW_TypeDef CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW;                 /*!< Offset: 0x2dc  */
  __IO  DDR_CSR_APB_CFG_CTRLR_BUSY_RESTART_HOLDOFF_TypeDef CFG_CTRLR_BUSY_RESTART_HOLDOFF;                     /*!< Offset: 0x2e0  */
  __IO  DDR_CSR_APB_CFG_PARITY_RDIMM_DELAY_TypeDef CFG_PARITY_RDIMM_DELAY;                             /*!< Offset: 0x2e4  */
  __IO  DDR_CSR_APB_CFG_CTRLR_BUSY_ENABLE_TypeDef CFG_CTRLR_BUSY_ENABLE;                              /*!< Offset: 0x2e8  */
  __IO  DDR_CSR_APB_CFG_ASYNC_ODT_TypeDef CFG_ASYNC_ODT;                                      /*!< Offset: 0x2ec  */
  __IO  DDR_CSR_APB_CFG_ZQ_CAL_DURATION_TypeDef CFG_ZQ_CAL_DURATION;                                /*!< Offset: 0x2f0  */
  __IO  DDR_CSR_APB_CFG_MRRI_TypeDef   CFG_MRRI;                                           /*!< Offset: 0x2f4  */
  __IO  DDR_CSR_APB_INIT_ODT_FORCE_EN_TypeDef INIT_ODT_FORCE_EN;                                  /*!< Offset: 0x2f8  */
  __IO  DDR_CSR_APB_INIT_ODT_FORCE_RANK_TypeDef INIT_ODT_FORCE_RANK;                                /*!< Offset: 0x2fc  */
  __IO  DDR_CSR_APB_CFG_PHYUPD_ACK_DELAY_TypeDef CFG_PHYUPD_ACK_DELAY;                               /*!< Offset: 0x300  */
  __IO  DDR_CSR_APB_CFG_MIRROR_X16_BG0_BG1_TypeDef CFG_MIRROR_X16_BG0_BG1;                             /*!< Offset: 0x304  */
  __IO  DDR_CSR_APB_INIT_PDA_MR_W_REQ_TypeDef INIT_PDA_MR_W_REQ;                                  /*!< Offset: 0x308  */
  __IO  DDR_CSR_APB_INIT_PDA_NIBBLE_SELECT_TypeDef INIT_PDA_NIBBLE_SELECT;                             /*!< Offset: 0x30c  */
  __IO  DDR_CSR_APB_CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH_TypeDef CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH;               /*!< Offset: 0x310  */
  __IO  DDR_CSR_APB_CFG_CKSRE_TypeDef  CFG_CKSRE;                                          /*!< Offset: 0x314  */
  __IO  DDR_CSR_APB_CFG_CKSRX_TypeDef  CFG_CKSRX;                                          /*!< Offset: 0x318  */
  __IO  DDR_CSR_APB_CFG_RCD_STAB_TypeDef CFG_RCD_STAB;                                       /*!< Offset: 0x31c  */
  __IO  DDR_CSR_APB_CFG_DFI_T_CTRL_DELAY_TypeDef CFG_DFI_T_CTRL_DELAY;                               /*!< Offset: 0x320  */
  __IO  DDR_CSR_APB_CFG_DFI_T_DRAM_CLK_ENABLE_TypeDef CFG_DFI_T_DRAM_CLK_ENABLE;                          /*!< Offset: 0x324  */
  __IO  DDR_CSR_APB_CFG_IDLE_TIME_TO_SELF_REFRESH_TypeDef CFG_IDLE_TIME_TO_SELF_REFRESH;                      /*!< Offset: 0x328  */
  __IO  DDR_CSR_APB_CFG_IDLE_TIME_TO_POWER_DOWN_TypeDef CFG_IDLE_TIME_TO_POWER_DOWN;                        /*!< Offset: 0x32c  */
  __IO  DDR_CSR_APB_CFG_BURST_RW_REFRESH_HOLDOFF_TypeDef CFG_BURST_RW_REFRESH_HOLDOFF;                       /*!< Offset: 0x330  */
  __I   DDR_CSR_APB_INIT_REFRESH_COUNT_TypeDef INIT_REFRESH_COUNT;                                 /*!< Offset: 0x334  */
  __I   uint32_t                       UNUSED_SPACE11[19];                                 /*!< Offset: 0x338 */
  __IO  DDR_CSR_APB_CFG_BG_INTERLEAVE_TypeDef CFG_BG_INTERLEAVE;                                  /*!< Offset: 0x384  */
  __I   uint32_t                       UNUSED_SPACE12[29];                                 /*!< Offset: 0x388 */
  __IO  DDR_CSR_APB_CFG_REFRESH_DURING_PHY_TRAINING_TypeDef CFG_REFRESH_DURING_PHY_TRAINING;                    /*!< Offset: 0x3fc  */
} DDR_CSR_APB_MC_BASE2_TypeDef;

/*------------ MEM_TEST register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_MT_EN_TypeDef      MT_EN;                                              /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_MT_EN_SINGLE_TypeDef MT_EN_SINGLE;                                       /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_MT_STOP_ON_ERROR_TypeDef MT_STOP_ON_ERROR;                                   /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_MT_RD_ONLY_TypeDef MT_RD_ONLY;                                         /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_MT_WR_ONLY_TypeDef MT_WR_ONLY;                                         /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_MT_DATA_PATTERN_TypeDef MT_DATA_PATTERN;                                    /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_MT_ADDR_PATTERN_TypeDef MT_ADDR_PATTERN;                                    /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_MT_DATA_INVERT_TypeDef MT_DATA_INVERT;                                     /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_MT_ADDR_BITS_TypeDef MT_ADDR_BITS;                                       /*!< Offset: 0x20  */
  __I   DDR_CSR_APB_MT_ERROR_STS_TypeDef MT_ERROR_STS;                                       /*!< Offset: 0x24  */
  __I   DDR_CSR_APB_MT_DONE_ACK_TypeDef MT_DONE_ACK;                                        /*!< Offset: 0x28  */
  __I   uint32_t                       UNUSED_SPACE0[34];                                  /*!< Offset: 0x2c */
  __IO  DDR_CSR_APB_MT_START_ADDR_0_TypeDef MT_START_ADDR_0;                                    /*!< Offset: 0xb4  */
  __IO  DDR_CSR_APB_MT_START_ADDR_1_TypeDef MT_START_ADDR_1;                                    /*!< Offset: 0xb8  */
  __IO  DDR_CSR_APB_MT_ERROR_MASK_0_TypeDef MT_ERROR_MASK_0;                                    /*!< Offset: 0xbc  */
  __IO  DDR_CSR_APB_MT_ERROR_MASK_1_TypeDef MT_ERROR_MASK_1;                                    /*!< Offset: 0xc0  */
  __IO  DDR_CSR_APB_MT_ERROR_MASK_2_TypeDef MT_ERROR_MASK_2;                                    /*!< Offset: 0xc4  */
  __IO  DDR_CSR_APB_MT_ERROR_MASK_3_TypeDef MT_ERROR_MASK_3;                                    /*!< Offset: 0xc8  */
  __IO  DDR_CSR_APB_MT_ERROR_MASK_4_TypeDef MT_ERROR_MASK_4;                                    /*!< Offset: 0xcc  */
  __I   uint32_t                       UNUSED_SPACE1[104];                                 /*!< Offset: 0xd0 */
  __IO  DDR_CSR_APB_MT_USER_DATA_PATTERN_TypeDef MT_USER_DATA_PATTERN;                               /*!< Offset: 0x270  */
  __I   uint32_t                       UNUSED_SPACE2[2];                                   /*!< Offset: 0x274 */
  __IO  DDR_CSR_APB_MT_ALG_AUTO_PCH_TypeDef MT_ALG_AUTO_PCH;                                    /*!< Offset: 0x27c  */
  __I   uint32_t                       UNUSED_SPACE3[2];                                   /*!< Offset: 0x280 */
} DDR_CSR_APB_MEM_TEST_TypeDef;

/*------------ MPFE register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P0_TypeDef CFG_STARVE_TIMEOUT_P0;                              /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P1_TypeDef CFG_STARVE_TIMEOUT_P1;                              /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P2_TypeDef CFG_STARVE_TIMEOUT_P2;                              /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P3_TypeDef CFG_STARVE_TIMEOUT_P3;                              /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P4_TypeDef CFG_STARVE_TIMEOUT_P4;                              /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P5_TypeDef CFG_STARVE_TIMEOUT_P5;                              /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P6_TypeDef CFG_STARVE_TIMEOUT_P6;                              /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_CFG_STARVE_TIMEOUT_P7_TypeDef CFG_STARVE_TIMEOUT_P7;                              /*!< Offset: 0x1c  */
  __I   uint32_t                       UNUSED_SPACE0[33];                                  /*!< Offset: 0x20 */
} DDR_CSR_APB_MPFE_TypeDef;

/*------------ REORDER register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_REORDER_EN_TypeDef CFG_REORDER_EN;                                     /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_REORDER_QUEUE_EN_TypeDef CFG_REORDER_QUEUE_EN;                               /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_INTRAPORT_REORDER_EN_TypeDef CFG_INTRAPORT_REORDER_EN;                           /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_MAINTAIN_COHERENCY_TypeDef CFG_MAINTAIN_COHERENCY;                             /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_CFG_Q_AGE_LIMIT_TypeDef CFG_Q_AGE_LIMIT;                                    /*!< Offset: 0x10  */
  __I   uint32_t                       UNUSED_SPACE0;                                      /*!< Offset: 0x14 */
  __IO  DDR_CSR_APB_CFG_RO_CLOSED_PAGE_POLICY_TypeDef CFG_RO_CLOSED_PAGE_POLICY;                          /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_CFG_REORDER_RW_ONLY_TypeDef CFG_REORDER_RW_ONLY;                                /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_CFG_RO_PRIORITY_EN_TypeDef CFG_RO_PRIORITY_EN;                                 /*!< Offset: 0x20  */
} DDR_CSR_APB_REORDER_TypeDef;

/*------------ RMW register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_DM_EN_TypeDef  CFG_DM_EN;                                          /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_RMW_EN_TypeDef CFG_RMW_EN;                                         /*!< Offset: 0x4  */
} DDR_CSR_APB_RMW_TypeDef;

/*------------ ECC register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_ECC_CORRECTION_EN_TypeDef CFG_ECC_CORRECTION_EN;                              /*!< Offset: 0x0  */
  __I   uint32_t                       UNUSED_SPACE0[15];                                  /*!< Offset: 0x4 */
  __IO  DDR_CSR_APB_CFG_ECC_BYPASS_TypeDef CFG_ECC_BYPASS;                                     /*!< Offset: 0x40  */
  __IO  DDR_CSR_APB_INIT_WRITE_DATA_1B_ECC_ERROR_GEN_TypeDef INIT_WRITE_DATA_1B_ECC_ERROR_GEN;                   /*!< Offset: 0x44  */
  __IO  DDR_CSR_APB_INIT_WRITE_DATA_2B_ECC_ERROR_GEN_TypeDef INIT_WRITE_DATA_2B_ECC_ERROR_GEN;                   /*!< Offset: 0x48  */
  __I   uint32_t                       UNUSED_SPACE1[4];                                   /*!< Offset: 0x4c */
  __IO  DDR_CSR_APB_CFG_ECC_1BIT_INT_THRESH_TypeDef CFG_ECC_1BIT_INT_THRESH;                            /*!< Offset: 0x5c  */
  __I   DDR_CSR_APB_STAT_INT_ECC_1BIT_THRESH_TypeDef STAT_INT_ECC_1BIT_THRESH;                           /*!< Offset: 0x60  */
  __I   uint32_t                       UNUSED_SPACE2[2];                                   /*!< Offset: 0x64 */
} DDR_CSR_APB_ECC_TypeDef;

/*------------ READ_CAPT register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_INIT_READ_CAPTURE_ADDR_TypeDef INIT_READ_CAPTURE_ADDR;                             /*!< Offset: 0x0  */
  __I   DDR_CSR_APB_INIT_READ_CAPTURE_DATA_0_TypeDef INIT_READ_CAPTURE_DATA_0;                           /*!< Offset: 0x4  */
  __I   DDR_CSR_APB_INIT_READ_CAPTURE_DATA_1_TypeDef INIT_READ_CAPTURE_DATA_1;                           /*!< Offset: 0x8  */
  __I   DDR_CSR_APB_INIT_READ_CAPTURE_DATA_2_TypeDef INIT_READ_CAPTURE_DATA_2;                           /*!< Offset: 0xc  */
  __I   DDR_CSR_APB_INIT_READ_CAPTURE_DATA_3_TypeDef INIT_READ_CAPTURE_DATA_3;                           /*!< Offset: 0x10  */
  __I   DDR_CSR_APB_INIT_READ_CAPTURE_DATA_4_TypeDef INIT_READ_CAPTURE_DATA_4;                           /*!< Offset: 0x14  */
  __I   uint32_t                       UNUSED_SPACE0[12];                                  /*!< Offset: 0x18 */
} DDR_CSR_APB_READ_CAPT_TypeDef;

/*------------ MTA register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_ERROR_GROUP_SEL_TypeDef CFG_ERROR_GROUP_SEL;                                /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_DATA_SEL_TypeDef CFG_DATA_SEL;                                       /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_TRIG_MODE_TypeDef CFG_TRIG_MODE;                                      /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_POST_TRIG_CYCS_TypeDef CFG_POST_TRIG_CYCS;                                 /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_CFG_TRIG_MASK_TypeDef CFG_TRIG_MASK;                                      /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_CFG_EN_MASK_TypeDef CFG_EN_MASK;                                        /*!< Offset: 0x14  */
  __IO  DDR_CSR_APB_MTC_ACQ_ADDR_TypeDef MTC_ACQ_ADDR;                                       /*!< Offset: 0x18  */
  __I   DDR_CSR_APB_MTC_ACQ_CYCS_STORED_TypeDef MTC_ACQ_CYCS_STORED;                                /*!< Offset: 0x1c  */
  __I   DDR_CSR_APB_MTC_ACQ_TRIG_DETECT_TypeDef MTC_ACQ_TRIG_DETECT;                                /*!< Offset: 0x20  */
  __I   DDR_CSR_APB_MTC_ACQ_MEM_TRIG_ADDR_TypeDef MTC_ACQ_MEM_TRIG_ADDR;                              /*!< Offset: 0x24  */
  __I   DDR_CSR_APB_MTC_ACQ_MEM_LAST_ADDR_TypeDef MTC_ACQ_MEM_LAST_ADDR;                              /*!< Offset: 0x28  */
  __I   DDR_CSR_APB_MTC_ACK_TypeDef    MTC_ACK;                                            /*!< Offset: 0x2c  */
  __IO  DDR_CSR_APB_CFG_TRIG_MT_ADDR_0_TypeDef CFG_TRIG_MT_ADDR_0;                                 /*!< Offset: 0x30  */
  __IO  DDR_CSR_APB_CFG_TRIG_MT_ADDR_1_TypeDef CFG_TRIG_MT_ADDR_1;                                 /*!< Offset: 0x34  */
  __IO  DDR_CSR_APB_CFG_TRIG_ERR_MASK_0_TypeDef CFG_TRIG_ERR_MASK_0;                                /*!< Offset: 0x38  */
  __IO  DDR_CSR_APB_CFG_TRIG_ERR_MASK_1_TypeDef CFG_TRIG_ERR_MASK_1;                                /*!< Offset: 0x3c  */
  __IO  DDR_CSR_APB_CFG_TRIG_ERR_MASK_2_TypeDef CFG_TRIG_ERR_MASK_2;                                /*!< Offset: 0x40  */
  __IO  DDR_CSR_APB_CFG_TRIG_ERR_MASK_3_TypeDef CFG_TRIG_ERR_MASK_3;                                /*!< Offset: 0x44  */
  __IO  DDR_CSR_APB_CFG_TRIG_ERR_MASK_4_TypeDef CFG_TRIG_ERR_MASK_4;                                /*!< Offset: 0x48  */
  __IO  DDR_CSR_APB_MTC_ACQ_WR_DATA_0_TypeDef MTC_ACQ_WR_DATA_0;                                  /*!< Offset: 0x4c  */
  __IO  DDR_CSR_APB_MTC_ACQ_WR_DATA_1_TypeDef MTC_ACQ_WR_DATA_1;                                  /*!< Offset: 0x50  */
  __IO  DDR_CSR_APB_MTC_ACQ_WR_DATA_2_TypeDef MTC_ACQ_WR_DATA_2;                                  /*!< Offset: 0x54  */
  __I   DDR_CSR_APB_MTC_ACQ_RD_DATA_0_TypeDef MTC_ACQ_RD_DATA_0;                                  /*!< Offset: 0x58  */
  __I   DDR_CSR_APB_MTC_ACQ_RD_DATA_1_TypeDef MTC_ACQ_RD_DATA_1;                                  /*!< Offset: 0x5c  */
  __I   DDR_CSR_APB_MTC_ACQ_RD_DATA_2_TypeDef MTC_ACQ_RD_DATA_2;                                  /*!< Offset: 0x60  */
  __I   uint32_t                       UNUSED_SPACE0[50];                                  /*!< Offset: 0x64 */
  __IO  DDR_CSR_APB_CFG_PRE_TRIG_CYCS_TypeDef CFG_PRE_TRIG_CYCS;                                  /*!< Offset: 0x12c  */
  __I   uint32_t                       UNUSED_SPACE1[2];                                   /*!< Offset: 0x130 */
  __I   DDR_CSR_APB_MTC_ACQ_ERROR_CNT_TypeDef MTC_ACQ_ERROR_CNT;                                  /*!< Offset: 0x138  */
  __I   uint32_t                       UNUSED_SPACE2[2];                                   /*!< Offset: 0x13c */
  __I   DDR_CSR_APB_MTC_ACQ_ERROR_CNT_OVFL_TypeDef MTC_ACQ_ERROR_CNT_OVFL;                             /*!< Offset: 0x144  */
  __I   uint32_t                       UNUSED_SPACE3[2];                                   /*!< Offset: 0x148 */
  __IO  DDR_CSR_APB_CFG_DATA_SEL_FIRST_ERROR_TypeDef CFG_DATA_SEL_FIRST_ERROR;                           /*!< Offset: 0x150  */
  __I   uint32_t                       UNUSED_SPACE4[2];                                   /*!< Offset: 0x154 */
} DDR_CSR_APB_MTA_TypeDef;

/*------------ DYN_WIDTH_ADJ register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_DQ_WIDTH_TypeDef CFG_DQ_WIDTH;                                       /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_ACTIVE_DQ_SEL_TypeDef CFG_ACTIVE_DQ_SEL;                                  /*!< Offset: 0x4  */
} DDR_CSR_APB_DYN_WIDTH_ADJ_TypeDef;

/*------------ CA_PAR_ERR register bundle definition -----------*/
typedef struct
{
  __I   DDR_CSR_APB_STAT_CA_PARITY_ERROR_TypeDef STAT_CA_PARITY_ERROR;                               /*!< Offset: 0x0  */
  __I   uint32_t                       UNUSED_SPACE0[2];                                   /*!< Offset: 0x4 */
  __IO  DDR_CSR_APB_INIT_CA_PARITY_ERROR_GEN_REQ_TypeDef INIT_CA_PARITY_ERROR_GEN_REQ;                       /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_INIT_CA_PARITY_ERROR_GEN_CMD_TypeDef INIT_CA_PARITY_ERROR_GEN_CMD;                       /*!< Offset: 0x10  */
  __I   DDR_CSR_APB_INIT_CA_PARITY_ERROR_GEN_ACK_TypeDef INIT_CA_PARITY_ERROR_GEN_ACK;                       /*!< Offset: 0x14  */
  __I   uint32_t                       UNUSED_SPACE1[2];                                   /*!< Offset: 0x18 */
} DDR_CSR_APB_CA_PAR_ERR_TypeDef;

/*------------ DFI register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_CFG_DFI_T_RDDATA_EN_TypeDef CFG_DFI_T_RDDATA_EN;                                /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_CFG_DFI_T_PHY_RDLAT_TypeDef CFG_DFI_T_PHY_RDLAT;                                /*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_CFG_DFI_T_PHY_WRLAT_TypeDef CFG_DFI_T_PHY_WRLAT;                                /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_CFG_DFI_PHYUPD_EN_TypeDef CFG_DFI_PHYUPD_EN;                                  /*!< Offset: 0xc  */
  __IO  DDR_CSR_APB_INIT_DFI_LP_DATA_REQ_TypeDef INIT_DFI_LP_DATA_REQ;                               /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_INIT_DFI_LP_CTRL_REQ_TypeDef INIT_DFI_LP_CTRL_REQ;                               /*!< Offset: 0x14  */
  __I   DDR_CSR_APB_STAT_DFI_LP_ACK_TypeDef STAT_DFI_LP_ACK;                                    /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_INIT_DFI_LP_WAKEUP_TypeDef INIT_DFI_LP_WAKEUP;                                 /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_INIT_DFI_DRAM_CLK_DISABLE_TypeDef INIT_DFI_DRAM_CLK_DISABLE;                          /*!< Offset: 0x20  */
  __I   DDR_CSR_APB_STAT_DFI_TRAINING_ERROR_TypeDef STAT_DFI_TRAINING_ERROR;                            /*!< Offset: 0x24  */
  __I   DDR_CSR_APB_STAT_DFI_ERROR_TypeDef STAT_DFI_ERROR;                                     /*!< Offset: 0x28  */
  __I   DDR_CSR_APB_STAT_DFI_ERROR_INFO_TypeDef STAT_DFI_ERROR_INFO;                                /*!< Offset: 0x2c  */
  __IO  DDR_CSR_APB_CFG_DFI_DATA_BYTE_DISABLE_TypeDef CFG_DFI_DATA_BYTE_DISABLE;                          /*!< Offset: 0x30  */
  __I   DDR_CSR_APB_STAT_DFI_INIT_COMPLETE_TypeDef STAT_DFI_INIT_COMPLETE;                             /*!< Offset: 0x34  */
  __I   DDR_CSR_APB_STAT_DFI_TRAINING_COMPLETE_TypeDef STAT_DFI_TRAINING_COMPLETE;                         /*!< Offset: 0x38  */
  __IO  DDR_CSR_APB_CFG_DFI_LVL_SEL_TypeDef CFG_DFI_LVL_SEL;                                    /*!< Offset: 0x3c  */
  __IO  DDR_CSR_APB_CFG_DFI_LVL_PERIODIC_TypeDef CFG_DFI_LVL_PERIODIC;                               /*!< Offset: 0x40  */
  __IO  DDR_CSR_APB_CFG_DFI_LVL_PATTERN_TypeDef CFG_DFI_LVL_PATTERN;                                /*!< Offset: 0x44  */
  __I   uint32_t                       UNUSED_SPACE0[2];                                   /*!< Offset: 0x48 */
  __IO  DDR_CSR_APB_PHY_DFI_INIT_START_TypeDef PHY_DFI_INIT_START;                                 /*!< Offset: 0x50  */
  __I   uint32_t                       UNUSED_SPACE1;                                      /*!< Offset: 0x54 */
} DDR_CSR_APB_DFI_TypeDef;

/*------------ AXI_IF register bundle definition -----------*/
typedef struct
{
  __I   uint32_t                       UNUSED_SPACE0[6];                                   /*!< Offset: 0x0 */
  __IO  DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI1_0_TypeDef CFG_AXI_START_ADDRESS_AXI1_0;                       /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI1_1_TypeDef CFG_AXI_START_ADDRESS_AXI1_1;                       /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI2_0_TypeDef CFG_AXI_START_ADDRESS_AXI2_0;                       /*!< Offset: 0x20  */
  __IO  DDR_CSR_APB_CFG_AXI_START_ADDRESS_AXI2_1_TypeDef CFG_AXI_START_ADDRESS_AXI2_1;                       /*!< Offset: 0x24  */
  __I   uint32_t                       UNUSED_SPACE1[188];                                 /*!< Offset: 0x28 */
  __IO  DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI1_0_TypeDef CFG_AXI_END_ADDRESS_AXI1_0;                         /*!< Offset: 0x318  */
  __IO  DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI1_1_TypeDef CFG_AXI_END_ADDRESS_AXI1_1;                         /*!< Offset: 0x31c  */
  __IO  DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI2_0_TypeDef CFG_AXI_END_ADDRESS_AXI2_0;                         /*!< Offset: 0x320  */
  __IO  DDR_CSR_APB_CFG_AXI_END_ADDRESS_AXI2_1_TypeDef CFG_AXI_END_ADDRESS_AXI2_1;                         /*!< Offset: 0x324  */
  __I   uint32_t                       UNUSED_SPACE2[188];                                 /*!< Offset: 0x328 */
  __IO  DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI1_0_TypeDef CFG_MEM_START_ADDRESS_AXI1_0;                       /*!< Offset: 0x618  */
  __IO  DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI1_1_TypeDef CFG_MEM_START_ADDRESS_AXI1_1;                       /*!< Offset: 0x61c  */
  __IO  DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI2_0_TypeDef CFG_MEM_START_ADDRESS_AXI2_0;                       /*!< Offset: 0x620  */
  __IO  DDR_CSR_APB_CFG_MEM_START_ADDRESS_AXI2_1_TypeDef CFG_MEM_START_ADDRESS_AXI2_1;                       /*!< Offset: 0x624  */
  __I   uint32_t                       UNUSED_SPACE3[187];                                 /*!< Offset: 0x628 */
  __IO  DDR_CSR_APB_CFG_ENABLE_BUS_HOLD_AXI1_TypeDef CFG_ENABLE_BUS_HOLD_AXI1;                           /*!< Offset: 0x914  */
  __IO  DDR_CSR_APB_CFG_ENABLE_BUS_HOLD_AXI2_TypeDef CFG_ENABLE_BUS_HOLD_AXI2;                           /*!< Offset: 0x918  */
  __I   uint32_t                       UNUSED_SPACE4[93];                                  /*!< Offset: 0x91c */
  __IO  DDR_CSR_APB_CFG_AXI_AUTO_PCH_TypeDef CFG_AXI_AUTO_PCH;                                   /*!< Offset: 0xa90  */
} DDR_CSR_APB_AXI_IF_TypeDef;

/*------------ csr_custom register bundle definition -----------*/
typedef struct
{
  __IO  DDR_CSR_APB_PHY_RESET_CONTROL_TypeDef PHY_RESET_CONTROL;                                  /*!< Offset: 0x0  */
  __IO  DDR_CSR_APB_PHY_PC_RANK_TypeDef PHY_PC_RANK;                                        	/*!< Offset: 0x4  */
  __IO  DDR_CSR_APB_PHY_RANKS_TO_TRAIN_TypeDef PHY_RANKS_TO_TRAIN;                                 /*!< Offset: 0x8  */
  __IO  DDR_CSR_APB_PHY_WRITE_REQUEST_TypeDef PHY_WRITE_REQUEST;                                  /*!< Offset: 0xc  */
  __I   DDR_CSR_APB_PHY_WRITE_REQUEST_DONE_TypeDef PHY_WRITE_REQUEST_DONE;                             /*!< Offset: 0x10  */
  __IO  DDR_CSR_APB_PHY_READ_REQUEST_TypeDef PHY_READ_REQUEST;                                   /*!< Offset: 0x14  */
  __I   DDR_CSR_APB_PHY_READ_REQUEST_DONE_TypeDef PHY_READ_REQUEST_DONE;                              /*!< Offset: 0x18  */
  __IO  DDR_CSR_APB_PHY_WRITE_LEVEL_DELAY_TypeDef PHY_WRITE_LEVEL_DELAY;                              /*!< Offset: 0x1c  */
  __IO  DDR_CSR_APB_PHY_GATE_TRAIN_DELAY_TypeDef PHY_GATE_TRAIN_DELAY;                               /*!< Offset: 0x20  */
  __IO  DDR_CSR_APB_PHY_EYE_TRAIN_DELAY_TypeDef PHY_EYE_TRAIN_DELAY;                                /*!< Offset: 0x24  */
  __IO  DDR_CSR_APB_PHY_EYE_PAT_TypeDef PHY_EYE_PAT;                                        /*!< Offset: 0x28  */
  __IO  DDR_CSR_APB_PHY_START_RECAL_TypeDef PHY_START_RECAL;                                    /*!< Offset: 0x2c  */
  __IO  DDR_CSR_APB_PHY_CLR_DFI_LVL_PERIODIC_TypeDef PHY_CLR_DFI_LVL_PERIODIC;                           /*!< Offset: 0x30  */
  __IO  DDR_CSR_APB_PHY_TRAIN_STEP_ENABLE_TypeDef PHY_TRAIN_STEP_ENABLE;                              /*!< Offset: 0x34  */
  __IO  DDR_CSR_APB_PHY_LPDDR_DQ_CAL_PAT_TypeDef PHY_LPDDR_DQ_CAL_PAT;                               /*!< Offset: 0x38  */
  __IO  DDR_CSR_APB_PHY_INDPNDT_TRAINING_TypeDef PHY_INDPNDT_TRAINING;                               /*!< Offset: 0x3c  */
  __IO  DDR_CSR_APB_PHY_ENCODED_QUAD_CS_TypeDef PHY_ENCODED_QUAD_CS;                                /*!< Offset: 0x40  */
  __IO  DDR_CSR_APB_PHY_HALF_CLK_DLY_ENABLE_TypeDef PHY_HALF_CLK_DLY_ENABLE;                            /*!< Offset: 0x44  */
  __I   uint32_t                       UNUSED_SPACE0[25];                                  /*!< Offset: 0x48 */
} DDR_CSR_APB_csr_custom_TypeDef;

/*------------ DDR_CSR_APB definition -----------*/
typedef struct
{
  __I   uint32_t                       UNUSED_SPACE0[2304];                                /*!< Offset: 0x0 */
  __IO  DDR_CSR_APB_ADDR_MAP_TypeDef ADDR_MAP;              /*!< Offset: 0x2400 */
  __I   uint32_t                       UNUSED_SPACE1[242];                                 /*!< Offset: 0x2438 */
  __IO  DDR_CSR_APB_MC_BASE3_TypeDef MC_BASE3;              /*!< Offset: 0x2800 */
  __I   uint32_t                       UNUSED_SPACE2[1204];                                /*!< Offset: 0x2930 */
  __IO  DDR_CSR_APB_MC_BASE1_TypeDef MC_BASE1;              /*!< Offset: 0x3c00 */
  __I   uint32_t                       UNUSED_SPACE3[147];                                 /*!< Offset: 0x3db4 */
  __IO  DDR_CSR_APB_MC_BASE2_TypeDef MC_BASE2;              /*!< Offset: 0x4000 */
  __IO  DDR_CSR_APB_MEM_TEST_TypeDef MEM_TEST;              /*!< Offset: 0x4400 */
  __I   uint32_t                       UNUSED_SPACE4[350];                                 /*!< Offset: 0x4688 */
  __IO  DDR_CSR_APB_MPFE_TypeDef MPFE;                      /*!< Offset: 0x4c00 */
  __I   uint32_t                       UNUSED_SPACE5[215];                                 /*!< Offset: 0x4ca4 */
  __IO  DDR_CSR_APB_REORDER_TypeDef REORDER;                /*!< Offset: 0x5000 */
  __I   uint32_t                       UNUSED_SPACE6[247];                                 /*!< Offset: 0x5024 */
  __IO  DDR_CSR_APB_RMW_TypeDef RMW;                        /*!< Offset: 0x5400 */
  __I   uint32_t                       UNUSED_SPACE7[254];                                 /*!< Offset: 0x5408 */
  __IO  DDR_CSR_APB_ECC_TypeDef ECC;                        /*!< Offset: 0x5800 */
  __I   uint32_t                       UNUSED_SPACE8[229];                                 /*!< Offset: 0x586c */
  __IO  DDR_CSR_APB_READ_CAPT_TypeDef READ_CAPT;            /*!< Offset: 0x5c00 */
  __I   uint32_t                       UNUSED_SPACE9[494];                                 /*!< Offset: 0x5c48 */
  __IO  DDR_CSR_APB_MTA_TypeDef MTA;                        /*!< Offset: 0x6400 */
  __I   uint32_t                       UNUSED_SPACE10[1449];                               /*!< Offset: 0x655c */
  __IO  DDR_CSR_APB_DYN_WIDTH_ADJ_TypeDef DYN_WIDTH_ADJ;    /*!< Offset: 0x7c00 */
  __I   uint32_t                       UNUSED_SPACE11[254];                                /*!< Offset: 0x7c08 */
  __IO  DDR_CSR_APB_CA_PAR_ERR_TypeDef CA_PAR_ERR;          /*!< Offset: 0x8000 */
  __I   uint32_t                       UNUSED_SPACE12[8184];                               /*!< Offset: 0x8020 */
  __IO  DDR_CSR_APB_DFI_TypeDef DFI;                        /*!< Offset: 0x10000 */
  __I   uint32_t                       UNUSED_SPACE13[2794];                               /*!< Offset: 0x10058 */
  __IO  DDR_CSR_APB_AXI_IF_TypeDef AXI_IF;                  /*!< Offset: 0x12c00 */
  __I   uint32_t                       UNUSED_SPACE14[41563];                              /*!< Offset: 0x13694 */
  __IO  DDR_CSR_APB_csr_custom_TypeDef csr_custom;          /*!< Offset: 0x3c000 */
} DDR_CSR_APB_TypeDef;


/*============================== IOSCBCFG definitions ===========================*/

typedef union{                                                         /*!< CONTROL__1 register definition*/
  __IO  uint32_t                       CONTROL__1;
  struct
  {
    __IO  uint32_t                       INTEN_SCB            :1;
    __IO  uint32_t                       INTEN_ERROR          :1;
    __IO  uint32_t                       INTEN_TIMEOUT        :1;
    __IO  uint32_t                       INTEN_BUSERR         :1;
    __I   uint32_t                       Reserved             :4;
    __IO  uint32_t                       RESET_CYCLE          :1;
    __I   uint32_t                       Reserved1            :7;
    __IO  uint32_t                       SCBCLOCK_ON          :1;
    __I   uint32_t                       Reserved2            :15;
  } bitfield;
} IOSCBCFG_CONTROL__1_TypeDef;

typedef union{                                                         /*!< STATUS register definition*/
  __I   uint32_t                       STATUS;
  struct
  {
    __I   uint32_t                       SCB_INTERRUPT        :1;
    __I   uint32_t                       SCB_ERROR            :1;
    __I   uint32_t                       TIMEOUT              :1;
    __I   uint32_t                       SCB_BUSERR           :1;
    __I   uint32_t                       Reserved             :28;
  } bitfield;
} IOSCBCFG_STATUS_TypeDef;

typedef union{                                                         /*!< TIMER register definition*/
  __IO  uint32_t                       TIMER;
  struct
  {
    __IO  uint32_t                       TIMEOUT              :8;
    __IO  uint32_t                       REQUEST_TIME         :8;
    __I   uint32_t                       Reserved             :16;
  } bitfield;
} IOSCBCFG_TIMER_TypeDef;

/*------------ IOSCBCFG definition -----------*/
typedef struct
{
  __IO  IOSCBCFG_CONTROL__1_TypeDef    CONTROL__1;                                         /*!< Offset: 0x0  */
  __I   IOSCBCFG_STATUS_TypeDef        STATUS;                                             /*!< Offset: 0x4  */
  __IO  IOSCBCFG_TIMER_TypeDef         TIMER;                                              /*!< Offset: 0x8  */
} IOSCBCFG_TypeDef;


/*============================== g5_mss_top_scb_regs definitions ===========================*/

typedef union{                                                         /*!< SOFT_RESET register definition*/
  __IO  uint32_t                       SOFT_RESET;
  struct
  {
    __O   uint32_t                       NV_MAP               :1;
    __O   uint32_t                       V_MAP                :1;
    __I   uint32_t                       reserved_01          :6;
    __O   uint32_t                       PERIPH               :1;
    __I   uint32_t                       reserved_02          :7;
    __I   uint32_t                       BLOCKID              :16;
  } bitfield;
} g5_mss_top_scb_regs_SOFT_RESET_TypeDef;

typedef union{                                                         /*!< AXI_WSETUP register definition*/
  __IO  uint32_t                       AXI_WSETUP;
  struct
  {
    __IO  uint32_t                       ADDR                 :6;
    __IO  uint32_t                       BURST                :2;
    __IO  uint32_t                       LENGTH               :8;
    __IO  uint32_t                       SIZE                 :3;
    __IO  uint32_t                       LOCK                 :1;
    __IO  uint32_t                       CACHE                :4;
    __IO  uint32_t                       PROT                 :3;
    __IO  uint32_t                       QOS                  :4;
    __IO  uint32_t                       SYSTEM               :1;
  } bitfield;
} g5_mss_top_scb_regs_AXI_WSETUP_TypeDef;

typedef union{                                                         /*!< AXI_WADDR register definition*/
  __IO  uint32_t                       AXI_WADDR;
  struct
  {
    __IO  uint32_t                       ADDR                 :32;
  } bitfield;
} g5_mss_top_scb_regs_AXI_WADDR_TypeDef;

typedef union{                                                         /*!< AXI_WDATA register definition*/
  __IO  uint32_t                       AXI_WDATA;
  struct
  {
    __IO  uint32_t                       DATA                 :32;
  } bitfield;
} g5_mss_top_scb_regs_AXI_WDATA_TypeDef;

typedef union{                                                         /*!< AXI_RSETUP register definition*/
  __IO  uint32_t                       AXI_RSETUP;
  struct
  {
    __IO  uint32_t                       ADDR                 :6;
    __IO  uint32_t                       BURST                :2;
    __IO  uint32_t                       LENGTH               :8;
    __IO  uint32_t                       SIZE                 :3;
    __IO  uint32_t                       LOCK                 :1;
    __IO  uint32_t                       CACHE                :4;
    __IO  uint32_t                       PROT                 :3;
    __IO  uint32_t                       QOS                  :4;
    __IO  uint32_t                       SYSTEM               :1;
  } bitfield;
} g5_mss_top_scb_regs_AXI_RSETUP_TypeDef;

typedef union{                                                         /*!< AXI_RADDR register definition*/
  __IO  uint32_t                       AXI_RADDR;
  struct
  {
    __IO  uint32_t                       ADDR                 :32;
  } bitfield;
} g5_mss_top_scb_regs_AXI_RADDR_TypeDef;

typedef union{                                                         /*!< AXI_RDATA register definition*/
  __IO  uint32_t                       AXI_RDATA;
  struct
  {
    __IO  uint32_t                       DATA                 :32;
  } bitfield;
} g5_mss_top_scb_regs_AXI_RDATA_TypeDef;

typedef union{                                                         /*!< AXI_STATUS register definition*/
  __IO  uint32_t                       AXI_STATUS;
  struct
  {
    __IO  uint32_t                       WRITE_BUSY           :1;
    __IO  uint32_t                       READ_BUSY            :1;
    __IO  uint32_t                       WRITE_ERROR          :1;
    __IO  uint32_t                       READ_ERROR           :1;
    __IO  uint32_t                       WRITE_COUNT          :5;
    __IO  uint32_t                       READ_COUNT           :5;
    __IO  uint32_t                       READ_OVERRUN         :1;
    __IO  uint32_t                       WRITE_OVERRUN        :1;
    __IO  uint32_t                       WRITE_RESPONSE       :2;
    __IO  uint32_t                       READ_RESPONSE        :2;
    __IO  uint32_t                       MSS_RESET            :1;
    __I   uint32_t                       reserved_01          :3;
    __IO  uint32_t                       INT_ENABLE_READ_ORUN :1;
    __IO  uint32_t                       INT_ENABLE_WRITE_ORUN :1;
    __IO  uint32_t                       INT_ENABLE_RRESP     :1;
    __IO  uint32_t                       INT_ENABLE_WRESP     :1;
    __IO  uint32_t                       INT_ENABLE_SYSREG    :1;
    __I   uint32_t                       reserved_02          :3;
  } bitfield;
} g5_mss_top_scb_regs_AXI_STATUS_TypeDef;

typedef union{                                                         /*!< AXI_CONTROL register definition*/
  __IO  uint32_t                       AXI_CONTROL;
  struct
  {
    __IO  uint32_t                       ABORT                :1;
    __I   uint32_t                       reserved_01          :7;
    __IO  uint32_t                       STALL_WRITE          :1;
    __I   uint32_t                       reserved_02          :7;
    __IO  uint32_t                       START_WRITE          :1;
    __I   uint32_t                       reserved_03          :15;
  } bitfield;
} g5_mss_top_scb_regs_AXI_CONTROL_TypeDef;

typedef union{                                                         /*!< REDUNDANCY register definition*/
  __IO  uint32_t                       REDUNDANCY;
  struct
  {
    __IO  uint32_t                       RESET                :1;
    __IO  uint32_t                       ISOLATE              :1;
    __IO  uint32_t                       NOCLOCK              :1;
    __I   uint32_t                       reserved_01          :29;
  } bitfield;
} g5_mss_top_scb_regs_REDUNDANCY_TypeDef;

typedef union{                                                         /*!< BIST_CONFIG register definition*/
  __IO  uint32_t                       BIST_CONFIG;
  struct
  {
    __I   uint32_t                       enabled              :1;
    __IO  uint32_t                       enable               :1;
    __IO  uint32_t                       reset                :1;
    __IO  uint32_t                       diag_select          :1;
    __I   uint32_t                       reserved_01          :4;
    __IO  uint32_t                       select               :5;
    __I   uint32_t                       reserved_02          :3;
    __IO  uint32_t                       margin               :3;
    __I   uint32_t                       reserved_03          :13;
  } bitfield;
} g5_mss_top_scb_regs_BIST_CONFIG_TypeDef;

typedef union{                                                         /*!< BIST_DATA register definition*/
  __IO  uint32_t                       BIST_DATA;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BIST_DATA_TypeDef;

typedef union{                                                         /*!< BIST_COMMAND register definition*/
  __IO  uint32_t                       BIST_COMMAND;
  struct
  {
    __IO  uint32_t                       update               :1;
    __IO  uint32_t                       capture              :1;
    __IO  uint32_t                       shift                :1;
    __I   uint32_t                       busy                 :1;
    __I   uint32_t                       reserved_01          :4;
    __IO  uint32_t                       length               :7;
    __I   uint32_t                       reserved_02          :17;
  } bitfield;
} g5_mss_top_scb_regs_BIST_COMMAND_TypeDef;

typedef union{                                                         /*!< MSS_RESET_CR register definition*/
  __IO  uint32_t                       MSS_RESET_CR;
  struct
  {
    __IO  uint32_t                       CPU                  :1;
    __IO  uint32_t                       MSS                  :1;
    __I   uint32_t                       CPUINRESET           :1;
    __IO  uint32_t                       REBOOT_REQUEST       :1;
    __I   uint32_t                       reserved_01          :4;
    __IO  uint32_t                       SGMII                :1;
    __I   uint32_t                       reserved_02          :7;
    __I   uint32_t                       REASON               :9;
    __I   uint32_t                       reserved_03          :7;
  } bitfield;
} g5_mss_top_scb_regs_MSS_RESET_CR_TypeDef;

typedef union{                                                         /*!< MSS_STATUS register definition*/
  __IO  uint32_t                       MSS_STATUS;
  struct
  {
    __IO  uint32_t                       boot_status          :4;
    __I   uint32_t                       watchdog             :5;
    __I   uint32_t                       debug_active         :1;
    __I   uint32_t                       halt_cpu0            :1;
    __I   uint32_t                       halt_cpu1            :1;
    __I   uint32_t                       halt_cpu2            :1;
    __I   uint32_t                       halt_cpu3            :1;
    __I   uint32_t                       halt_cpu4            :1;
    __I   uint32_t                       ecc_error_l2         :1;
    __I   uint32_t                       ecc_error_other      :1;
    __I   uint32_t                       reserved_01          :15;
  } bitfield;
} g5_mss_top_scb_regs_MSS_STATUS_TypeDef;

typedef union{                                                         /*!< BOOT_ADDR0 register definition*/
  __IO  uint32_t                       BOOT_ADDR0;
  struct
  {
    __IO  uint32_t                       address              :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ADDR0_TypeDef;

typedef union{                                                         /*!< BOOT_ADDR1 register definition*/
  __IO  uint32_t                       BOOT_ADDR1;
  struct
  {
    __IO  uint32_t                       address              :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ADDR1_TypeDef;

typedef union{                                                         /*!< BOOT_ADDR2 register definition*/
  __IO  uint32_t                       BOOT_ADDR2;
  struct
  {
    __IO  uint32_t                       address              :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ADDR2_TypeDef;

typedef union{                                                         /*!< BOOT_ADDR3 register definition*/
  __IO  uint32_t                       BOOT_ADDR3;
  struct
  {
    __IO  uint32_t                       address              :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ADDR3_TypeDef;

typedef union{                                                         /*!< BOOT_ADDR4 register definition*/
  __IO  uint32_t                       BOOT_ADDR4;
  struct
  {
    __IO  uint32_t                       address              :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ADDR4_TypeDef;

typedef union{                                                         /*!< BOOT_ROM0 register definition*/
  __IO  uint32_t                       BOOT_ROM0;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM0_TypeDef;

typedef union{                                                         /*!< BOOT_ROM1 register definition*/
  __IO  uint32_t                       BOOT_ROM1;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM1_TypeDef;

typedef union{                                                         /*!< BOOT_ROM2 register definition*/
  __IO  uint32_t                       BOOT_ROM2;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM2_TypeDef;

typedef union{                                                         /*!< BOOT_ROM3 register definition*/
  __IO  uint32_t                       BOOT_ROM3;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM3_TypeDef;

typedef union{                                                         /*!< BOOT_ROM4 register definition*/
  __IO  uint32_t                       BOOT_ROM4;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM4_TypeDef;

typedef union{                                                         /*!< BOOT_ROM5 register definition*/
  __IO  uint32_t                       BOOT_ROM5;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM5_TypeDef;

typedef union{                                                         /*!< BOOT_ROM6 register definition*/
  __IO  uint32_t                       BOOT_ROM6;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM6_TypeDef;

typedef union{                                                         /*!< BOOT_ROM7 register definition*/
  __IO  uint32_t                       BOOT_ROM7;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_BOOT_ROM7_TypeDef;

typedef union{                                                         /*!< FLASH_FREEZE register definition*/
  __IO  uint32_t                       FLASH_FREEZE;
  struct
  {
    __IO  uint32_t                       in_progress          :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} g5_mss_top_scb_regs_FLASH_FREEZE_TypeDef;

typedef union{                                                         /*!< G5CIO register definition*/
  __IO  uint32_t                       G5CIO;
  struct
  {
    __IO  uint32_t                       ioout                :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} g5_mss_top_scb_regs_G5CIO_TypeDef;

typedef union{                                                         /*!< DEVICE_ID register definition*/
  __IO  uint32_t                       DEVICE_ID;
  struct
  {
    __IO  uint32_t                       idp                  :16;
    __IO  uint32_t                       idv                  :4;
    __I   uint32_t                       reserved_01          :12;
  } bitfield;
} g5_mss_top_scb_regs_DEVICE_ID_TypeDef;

typedef union{                                                         /*!< MESSAGE_INT register definition*/
  __IO  uint32_t                       MESSAGE_INT;
  struct
  {
    __IO  uint32_t                       active               :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} g5_mss_top_scb_regs_MESSAGE_INT_TypeDef;

typedef union{                                                         /*!< MESSAGE register definition*/
  __IO  uint32_t                       MESSAGE;
  struct
  {
    __IO  uint32_t                       data                 :32;
  } bitfield;
} g5_mss_top_scb_regs_MESSAGE_TypeDef;

typedef union{                                                         /*!< DEVRST_INT register definition*/
  __IO  uint32_t                       DEVRST_INT;
  struct
  {
    __IO  uint32_t                       active               :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} g5_mss_top_scb_regs_DEVRST_INT_TypeDef;

typedef union{                                                         /*!< SCB_INTERRUPT register definition*/
  __IO  uint32_t                       SCB_INTERRUPT;
  struct
  {
    __IO  uint32_t                       active               :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} g5_mss_top_scb_regs_SCB_INTERRUPT_TypeDef;

typedef union{                                                         /*!< MSS_INTERRUPT register definition*/
  __IO  uint32_t                       MSS_INTERRUPT;
  struct
  {
    __IO  uint32_t                       active               :1;
    __I   uint32_t                       reserved_01          :31;
  } bitfield;
} g5_mss_top_scb_regs_MSS_INTERRUPT_TypeDef;

typedef union{                                                         /*!< DEVICE_CONFIG_CR register definition*/
  __IO  uint32_t                       DEVICE_CONFIG_CR;
  struct
  {
    __IO  uint32_t                       FACTORY_TEST_MODE    :1;
    __I   uint32_t                       RESERVED             :1;
    __IO  uint32_t                       CRYPTO_DISABLE       :1;
    __IO  uint32_t                       CAN_ALLOWED          :1;
    __IO  uint32_t                       CPU_ALLOWED          :1;
    __IO  uint32_t                       CPU_DISABLE          :1;
    __I   uint32_t                       reserved_01          :2;
    __IO  uint32_t                       CPU_BIST_DISABLE     :1;
    __I   uint32_t                       reserved_02          :7;
    __IO  uint32_t                       DISABLE_XIP          :1;
    __I   uint32_t                       reserved_03          :15;
  } bitfield;
} g5_mss_top_scb_regs_DEVICE_CONFIG_CR_TypeDef;

typedef union{                                                         /*!< ATHENA_CR register definition*/
  __IO  uint32_t                       ATHENA_CR;
  struct
  {
    __IO  uint32_t                       mss_mode             :3;
    __I   uint32_t                       reserved_01          :1;
    __IO  uint32_t                       stream_enable        :1;
    __I   uint32_t                       reserved_02          :27;
  } bitfield;
} g5_mss_top_scb_regs_ATHENA_CR_TypeDef;

typedef union{                                                         /*!< ENVM_CR register definition*/
  __IO  uint32_t                       ENVM_CR;
  struct
  {
    __IO  uint32_t                       clock_period         :6;
    __I   uint32_t                       reserved_01          :2;
    __IO  uint32_t                       clock_continuous     :1;
    __IO  uint32_t                       clock_suppress       :1;
    __I   uint32_t                       reserved_02          :6;
    __IO  uint32_t                       readahead            :1;
    __IO  uint32_t                       slowread             :1;
    __IO  uint32_t                       interrupt_enable     :1;
    __I   uint32_t                       reserved_03          :5;
    __IO  uint32_t                       timer                :8;
  } bitfield;
} g5_mss_top_scb_regs_ENVM_CR_TypeDef;

typedef union{                                                         /*!< ENVM_POWER_CR register definition*/
  __IO  uint32_t                       ENVM_POWER_CR;
  struct
  {
    __IO  uint32_t                       reset                :1;
    __IO  uint32_t                       pd1                  :1;
    __IO  uint32_t                       pd2                  :1;
    __IO  uint32_t                       pd3                  :1;
    __IO  uint32_t                       pd4                  :1;
    __IO  uint32_t                       iso                  :1;
    __IO  uint32_t                       sleep                :1;
    __I   uint32_t                       reserved_01          :1;
    __IO  uint32_t                       override             :1;
    __I   uint32_t                       reserved_02          :23;
  } bitfield;
} g5_mss_top_scb_regs_ENVM_POWER_CR_TypeDef;

typedef union{                                                         /*!< RAM_SHUTDOWN_CR register definition*/
  __IO  uint32_t                       RAM_SHUTDOWN_CR;
  struct
  {
    __IO  uint32_t                       can0                 :1;
    __IO  uint32_t                       can1                 :1;
    __IO  uint32_t                       usb                  :1;
    __IO  uint32_t                       gem0                 :1;
    __IO  uint32_t                       gem1                 :1;
    __IO  uint32_t                       mmc                  :1;
    __IO  uint32_t                       athena               :1;
    __IO  uint32_t                       ddrc                 :1;
    __IO  uint32_t                       e51                  :1;
    __IO  uint32_t                       u54_1                :1;
    __IO  uint32_t                       u54_2                :1;
    __IO  uint32_t                       u54_3                :1;
    __IO  uint32_t                       u54_4                :1;
    __IO  uint32_t                       l2                   :1;
    __I   uint32_t                       reserved_01          :18;
  } bitfield;
} g5_mss_top_scb_regs_RAM_SHUTDOWN_CR_TypeDef;

typedef union{                                                         /*!< RAM_MARGIN_CR register definition*/
  __IO  uint32_t                       RAM_MARGIN_CR;
  struct
  {
    __IO  uint32_t                       enable               :1;
    __IO  uint32_t                       can0                 :2;
    __IO  uint32_t                       can1                 :2;
    __IO  uint32_t                       usb                  :2;
    __IO  uint32_t                       gem0                 :2;
    __IO  uint32_t                       gem1                 :2;
    __IO  uint32_t                       mmc                  :2;
    __IO  uint32_t                       ddrc                 :2;
    __IO  uint32_t                       e51                  :2;
    __IO  uint32_t                       u54_1                :2;
    __IO  uint32_t                       u54_2                :2;
    __IO  uint32_t                       u54_3                :2;
    __IO  uint32_t                       u54_4                :2;
    __IO  uint32_t                       l2                   :2;
    __I   uint32_t                       reserved_01          :5;
  } bitfield;
} g5_mss_top_scb_regs_RAM_MARGIN_CR_TypeDef;

typedef union{                                                         /*!< TRACE_CR register definition*/
  __IO  uint32_t                       TRACE_CR;
  struct
  {
    __IO  uint32_t                       CPU_DEBUG_DISABLE    :1;
    __IO  uint32_t                       ULTRASOC_DISABLE_JTAG :1;
    __IO  uint32_t                       ULTRASOC_DISABLE_AXI :1;
    __I   uint32_t                       reserved_01          :5;
    __IO  uint32_t                       ULTRASOC_FABRIC      :1;
    __I   uint32_t                       reserved_02          :23;
  } bitfield;
} g5_mss_top_scb_regs_TRACE_CR_TypeDef;

typedef union{                                                         /*!< MSSIO_CONTROL_CR register definition*/
  __IO  uint32_t                       MSSIO_CONTROL_CR;
  struct
  {
    __IO  uint32_t                       lp_state_mss         :1;
    __IO  uint32_t                       lp_state_ip_mss      :1;
    __IO  uint32_t                       lp_state_op_mss      :1;
    __IO  uint32_t                       lp_state_persist_mss :1;
    __IO  uint32_t                       lp_state_bypass_mss  :1;
    __IO  uint32_t                       lp_pll_locked_mss    :1;
    __IO  uint32_t                       lp_stop_clocks_out_mss :1;
    __I   uint32_t                       lp_stop_clocks_done_mss :1;
    __IO  uint32_t                       mss_dce              :3;
    __IO  uint32_t                       mss_core_up          :1;
    __IO  uint32_t                       mss_flash_valid      :1;
    __IO  uint32_t                       mss_io_en            :1;
    __IO  uint32_t                       mss_sel_hw_dyn       :1;
    __IO  uint32_t                       mss_sel_hw_def       :1;
    __I   uint32_t                       reserved_01          :16;
  } bitfield;
} g5_mss_top_scb_regs_MSSIO_CONTROL_CR_TypeDef;

typedef union{                                                         /*!< MSS_IO_LOCKDOWN_CR register definition*/
  __I   uint32_t                       MSS_IO_LOCKDOWN_CR;
  struct
  {
    __I   uint32_t                       mssio_b2_lockdn_en   :1;
    __I   uint32_t                       mssio_b4_lockdn_en   :1;
    __I   uint32_t                       sgmii_io_lockdn_en   :1;
    __I   uint32_t                       ddr_io_lockdn_en     :1;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} g5_mss_top_scb_regs_MSS_IO_LOCKDOWN_CR_TypeDef;

typedef union{                                                         /*!< MSSIO_BANK2_CFG_CR register definition*/
  __IO  uint32_t                       MSSIO_BANK2_CFG_CR;
  struct
  {
    __IO  uint32_t                       bank_pcode           :6;
    __I   uint32_t                       reserved_01          :2;
    __IO  uint32_t                       bank_ncode           :6;
    __I   uint32_t                       reserved_02          :2;
    __IO  uint32_t                       vs                   :4;
    __I   uint32_t                       reserved_03          :12;
  } bitfield;
} g5_mss_top_scb_regs_MSSIO_BANK2_CFG_CR_TypeDef;

typedef union{                                                         /*!< MSSIO_BANK4_CFG_CR register definition*/
  __IO  uint32_t                       MSSIO_BANK4_CFG_CR;
  struct
  {
    __IO  uint32_t                       bank_pcode           :6;
    __I   uint32_t                       reserved_01          :2;
    __IO  uint32_t                       bank_ncode           :6;
    __I   uint32_t                       reserved_02          :2;
    __IO  uint32_t                       vs                   :4;
    __I   uint32_t                       reserved_03          :12;
  } bitfield;
} g5_mss_top_scb_regs_MSSIO_BANK4_CFG_CR_TypeDef;

typedef union{                                                         /*!< DLL0_CTRL0 register definition*/
  __IO  uint32_t                       DLL0_CTRL0;
  struct
  {
    __IO  uint32_t                       phase_p              :2;
    __IO  uint32_t                       phase_s              :2;
    __IO  uint32_t                       sel_p                :2;
    __IO  uint32_t                       sel_s                :2;
    __IO  uint32_t                       ref_sel              :1;
    __IO  uint32_t                       fb_sel               :1;
    __IO  uint32_t                       div_sel              :1;
    __I   uint32_t                       reserved             :3;
    __IO  uint32_t                       alu_upd              :2;
    __I   uint32_t                       reserved2            :3;
    __IO  uint32_t                       lock_frc             :1;
    __IO  uint32_t                       lock_flt             :2;
    __I   uint32_t                       reserved3            :2;
    __IO  uint32_t                       lock_high            :4;
    __IO  uint32_t                       lock_low             :4;
  } bitfield;
} g5_mss_top_scb_regs_DLL0_CTRL0_TypeDef;

typedef union{                                                         /*!< DLL0_CTRL1 register definition*/
  __IO  uint32_t                       DLL0_CTRL1;
  struct
  {
    __IO  uint32_t                       set_alu              :8;
    __IO  uint32_t                       adj_del4             :7;
    __IO  uint32_t                       test_s               :1;
    __I   uint32_t                       reserved             :7;
    __IO  uint32_t                       test_ring            :1;
    __IO  uint32_t                       init_code            :6;
    __IO  uint32_t                       relock_fast          :1;
    __I   uint32_t                       reserved2            :1;
  } bitfield;
} g5_mss_top_scb_regs_DLL0_CTRL1_TypeDef;

typedef union{                                                         /*!< DLL0_STAT0 register definition*/
  __IO  uint32_t                       DLL0_STAT0;
  struct
  {
    __IO  uint32_t                       reset                :1;
    __IO  uint32_t                       bypass               :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :3;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :1;
    __I   uint32_t                       reserved8            :1;
    __IO  uint32_t                       phase_move_clk       :1;
    __I   uint32_t                       reserved9            :1;
    __I   uint32_t                       reserved10           :2;
    __I   uint32_t                       reserved11           :8;
    __I   uint32_t                       reserved12           :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL0_STAT0_TypeDef;

typedef union{                                                         /*!< DLL0_STAT1 register definition*/
  __I   uint32_t                       DLL0_STAT1;
  struct
  {
    __I   uint32_t                       sro_del4             :7;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :8;
    __I   uint32_t                       sro_alu_cnt          :9;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :2;
    __I   uint32_t                       reserved5            :2;
    __I   uint32_t                       reserved6            :2;
  } bitfield;
} g5_mss_top_scb_regs_DLL0_STAT1_TypeDef;

typedef union{                                                         /*!< DLL0_STAT2 register definition*/
  __I   uint32_t                       DLL0_STAT2;
  struct
  {
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       sro_lock             :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :1;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :9;
    __I   uint32_t                       reserved8            :8;
    __I   uint32_t                       reserved9            :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL0_STAT2_TypeDef;

typedef union{                                                         /*!< DLL0_TEST register definition*/
  __IO  uint32_t                       DLL0_TEST;
  struct
  {
    __IO  uint32_t                       cfm_enable           :1;
    __IO  uint32_t                       cfm_select           :1;
    __IO  uint32_t                       ref_select           :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} g5_mss_top_scb_regs_DLL0_TEST_TypeDef;

typedef union{                                                         /*!< DLL1_CTRL0 register definition*/
  __IO  uint32_t                       DLL1_CTRL0;
  struct
  {
    __IO  uint32_t                       phase_p              :2;
    __IO  uint32_t                       phase_s              :2;
    __IO  uint32_t                       sel_p                :2;
    __IO  uint32_t                       sel_s                :2;
    __IO  uint32_t                       ref_sel              :1;
    __IO  uint32_t                       fb_sel               :1;
    __IO  uint32_t                       div_sel              :1;
    __I   uint32_t                       reserved             :3;
    __IO  uint32_t                       alu_upd              :2;
    __I   uint32_t                       reserved2            :3;
    __IO  uint32_t                       lock_frc             :1;
    __IO  uint32_t                       lock_flt             :2;
    __I   uint32_t                       reserved3            :2;
    __IO  uint32_t                       lock_high            :4;
    __IO  uint32_t                       lock_low             :4;
  } bitfield;
} g5_mss_top_scb_regs_DLL1_CTRL0_TypeDef;

typedef union{                                                         /*!< DLL1_CTRL1 register definition*/
  __IO  uint32_t                       DLL1_CTRL1;
  struct
  {
    __IO  uint32_t                       set_alu              :8;
    __IO  uint32_t                       adj_del4             :7;
    __IO  uint32_t                       test_s               :1;
    __I   uint32_t                       reserved             :7;
    __IO  uint32_t                       test_ring            :1;
    __IO  uint32_t                       init_code            :6;
    __IO  uint32_t                       relock_fast          :1;
    __I   uint32_t                       reserved2            :1;
  } bitfield;
} g5_mss_top_scb_regs_DLL1_CTRL1_TypeDef;

typedef union{                                                         /*!< DLL1_STAT0 register definition*/
  __IO  uint32_t                       DLL1_STAT0;
  struct
  {
    __IO  uint32_t                       reset                :1;
    __IO  uint32_t                       bypass               :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :3;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :1;
    __I   uint32_t                       reserved8            :1;
    __IO  uint32_t                       phase_move_clk       :1;
    __I   uint32_t                       reserved9            :1;
    __I   uint32_t                       reserved10           :2;
    __I   uint32_t                       reserved11           :8;
    __I   uint32_t                       reserved12           :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL1_STAT0_TypeDef;

typedef union{                                                         /*!< DLL1_STAT1 register definition*/
  __I   uint32_t                       DLL1_STAT1;
  struct
  {
    __I   uint32_t                       sro_del4             :7;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :8;
    __I   uint32_t                       sro_alu_cnt          :9;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :2;
    __I   uint32_t                       reserved5            :2;
    __I   uint32_t                       reserved6            :2;
  } bitfield;
} g5_mss_top_scb_regs_DLL1_STAT1_TypeDef;

typedef union{                                                         /*!< DLL1_STAT2 register definition*/
  __I   uint32_t                       DLL1_STAT2;
  struct
  {
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       sro_lock             :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :1;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :9;
    __I   uint32_t                       reserved8            :8;
    __I   uint32_t                       reserved9            :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL1_STAT2_TypeDef;

typedef union{                                                         /*!< DLL1_TEST register definition*/
  __IO  uint32_t                       DLL1_TEST;
  struct
  {
    __IO  uint32_t                       cfm_enable           :1;
    __IO  uint32_t                       cfm_select           :1;
    __IO  uint32_t                       ref_select           :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} g5_mss_top_scb_regs_DLL1_TEST_TypeDef;

typedef union{                                                         /*!< DLL2_CTRL0 register definition*/
  __IO  uint32_t                       DLL2_CTRL0;
  struct
  {
    __IO  uint32_t                       phase_p              :2;
    __IO  uint32_t                       phase_s              :2;
    __IO  uint32_t                       sel_p                :2;
    __IO  uint32_t                       sel_s                :2;
    __IO  uint32_t                       ref_sel              :1;
    __IO  uint32_t                       fb_sel               :1;
    __IO  uint32_t                       div_sel              :1;
    __I   uint32_t                       reserved             :3;
    __IO  uint32_t                       alu_upd              :2;
    __I   uint32_t                       reserved2            :3;
    __IO  uint32_t                       lock_frc             :1;
    __IO  uint32_t                       lock_flt             :2;
    __I   uint32_t                       reserved3            :2;
    __IO  uint32_t                       lock_high            :4;
    __IO  uint32_t                       lock_low             :4;
  } bitfield;
} g5_mss_top_scb_regs_DLL2_CTRL0_TypeDef;

typedef union{                                                         /*!< DLL2_CTRL1 register definition*/
  __IO  uint32_t                       DLL2_CTRL1;
  struct
  {
    __IO  uint32_t                       set_alu              :8;
    __IO  uint32_t                       adj_del4             :7;
    __IO  uint32_t                       test_s               :1;
    __I   uint32_t                       reserved             :7;
    __IO  uint32_t                       test_ring            :1;
    __IO  uint32_t                       init_code            :6;
    __IO  uint32_t                       relock_fast          :1;
    __I   uint32_t                       reserved2            :1;
  } bitfield;
} g5_mss_top_scb_regs_DLL2_CTRL1_TypeDef;

typedef union{                                                         /*!< DLL2_STAT0 register definition*/
  __IO  uint32_t                       DLL2_STAT0;
  struct
  {
    __IO  uint32_t                       reset                :1;
    __IO  uint32_t                       bypass               :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :3;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :1;
    __I   uint32_t                       reserved8            :1;
    __IO  uint32_t                       phase_move_clk       :1;
    __I   uint32_t                       reserved9            :1;
    __I   uint32_t                       reserved10           :2;
    __I   uint32_t                       reserved11           :8;
    __I   uint32_t                       reserved12           :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL2_STAT0_TypeDef;

typedef union{                                                         /*!< DLL2_STAT1 register definition*/
  __I   uint32_t                       DLL2_STAT1;
  struct
  {
    __I   uint32_t                       sro_del4             :7;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :8;
    __I   uint32_t                       sro_alu_cnt          :9;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :2;
    __I   uint32_t                       reserved5            :2;
    __I   uint32_t                       reserved6            :2;
  } bitfield;
} g5_mss_top_scb_regs_DLL2_STAT1_TypeDef;

typedef union{                                                         /*!< DLL2_STAT2 register definition*/
  __I   uint32_t                       DLL2_STAT2;
  struct
  {
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       sro_lock             :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :1;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :9;
    __I   uint32_t                       reserved8            :8;
    __I   uint32_t                       reserved9            :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL2_STAT2_TypeDef;

typedef union{                                                         /*!< DLL2_TEST register definition*/
  __IO  uint32_t                       DLL2_TEST;
  struct
  {
    __IO  uint32_t                       cfm_enable           :1;
    __IO  uint32_t                       cfm_select           :1;
    __IO  uint32_t                       ref_select           :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} g5_mss_top_scb_regs_DLL2_TEST_TypeDef;

typedef union{                                                         /*!< DLL3_CTRL0 register definition*/
  __IO  uint32_t                       DLL3_CTRL0;
  struct
  {
    __IO  uint32_t                       phase_p              :2;
    __IO  uint32_t                       phase_s              :2;
    __IO  uint32_t                       sel_p                :2;
    __IO  uint32_t                       sel_s                :2;
    __IO  uint32_t                       ref_sel              :1;
    __IO  uint32_t                       fb_sel               :1;
    __IO  uint32_t                       div_sel              :1;
    __I   uint32_t                       reserved             :3;
    __IO  uint32_t                       alu_upd              :2;
    __I   uint32_t                       reserved2            :3;
    __IO  uint32_t                       lock_frc             :1;
    __IO  uint32_t                       lock_flt             :2;
    __I   uint32_t                       reserved3            :2;
    __IO  uint32_t                       lock_high            :4;
    __IO  uint32_t                       lock_low             :4;
  } bitfield;
} g5_mss_top_scb_regs_DLL3_CTRL0_TypeDef;

typedef union{                                                         /*!< DLL3_CTRL1 register definition*/
  __IO  uint32_t                       DLL3_CTRL1;
  struct
  {
    __IO  uint32_t                       set_alu              :8;
    __IO  uint32_t                       adj_del4             :7;
    __IO  uint32_t                       test_s               :1;
    __I   uint32_t                       reserved             :7;
    __IO  uint32_t                       test_ring            :1;
    __IO  uint32_t                       init_code            :6;
    __IO  uint32_t                       relock_fast          :1;
    __I   uint32_t                       reserved2            :1;
  } bitfield;
} g5_mss_top_scb_regs_DLL3_CTRL1_TypeDef;

typedef union{                                                         /*!< DLL3_STAT0 register definition*/
  __IO  uint32_t                       DLL3_STAT0;
  struct
  {
    __IO  uint32_t                       reset                :1;
    __IO  uint32_t                       bypass               :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :3;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :1;
    __I   uint32_t                       reserved8            :1;
    __IO  uint32_t                       phase_move_clk       :1;
    __I   uint32_t                       reserved9            :1;
    __I   uint32_t                       reserved10           :2;
    __I   uint32_t                       reserved11           :8;
    __I   uint32_t                       reserved12           :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL3_STAT0_TypeDef;

typedef union{                                                         /*!< DLL3_STAT1 register definition*/
  __I   uint32_t                       DLL3_STAT1;
  struct
  {
    __I   uint32_t                       sro_del4             :7;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :8;
    __I   uint32_t                       sro_alu_cnt          :9;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :2;
    __I   uint32_t                       reserved5            :2;
    __I   uint32_t                       reserved6            :2;
  } bitfield;
} g5_mss_top_scb_regs_DLL3_STAT1_TypeDef;

typedef union{                                                         /*!< DLL3_STAT2 register definition*/
  __I   uint32_t                       DLL3_STAT2;
  struct
  {
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved2            :1;
    __I   uint32_t                       sro_lock             :1;
    __I   uint32_t                       reserved3            :1;
    __I   uint32_t                       reserved4            :1;
    __I   uint32_t                       reserved5            :1;
    __I   uint32_t                       reserved6            :1;
    __I   uint32_t                       reserved7            :9;
    __I   uint32_t                       reserved8            :8;
    __I   uint32_t                       reserved9            :8;
  } bitfield;
} g5_mss_top_scb_regs_DLL3_STAT2_TypeDef;

typedef union{                                                         /*!< DLL3_TEST register definition*/
  __IO  uint32_t                       DLL3_TEST;
  struct
  {
    __IO  uint32_t                       cfm_enable           :1;
    __IO  uint32_t                       cfm_select           :1;
    __IO  uint32_t                       ref_select           :1;
    __I   uint32_t                       reserved             :1;
    __I   uint32_t                       reserved_01          :28;
  } bitfield;
} g5_mss_top_scb_regs_DLL3_TEST_TypeDef;

typedef union{                                                         /*!< MSSIO_VB2_CFG register definition*/
  __IO  uint32_t                       MSSIO_VB2_CFG;
  struct
  {
    __IO  uint32_t                       dpc_io_cfg_ibufmd_0  :1;
    __IO  uint32_t                       dpc_io_cfg_ibufmd_1  :1;
    __IO  uint32_t                       dpc_io_cfg_ibufmd_2  :1;
    __IO  uint32_t                       dpc_io_cfg_drv_0     :1;
    __IO  uint32_t                       dpc_io_cfg_drv_1     :1;
    __IO  uint32_t                       dpc_io_cfg_drv_2     :1;
    __IO  uint32_t                       dpc_io_cfg_drv_3     :1;
    __IO  uint32_t                       dpc_io_cfg_clamp     :1;
    __IO  uint32_t                       dpc_io_cfg_enhyst    :1;
    __IO  uint32_t                       dpc_io_cfg_lockdn_en :1;
    __IO  uint32_t                       dpc_io_cfg_wpd       :1;
    __IO  uint32_t                       dpc_io_cfg_wpu       :1;
    __IO  uint32_t                       dpc_io_cfg_atp_en    :1;
    __IO  uint32_t                       dpc_io_cfg_lp_persist_en :1;
    __IO  uint32_t                       dpc_io_cfg_lp_bypass_en :1;
    __I   uint32_t                       reserved_01          :17;
  } bitfield;
} g5_mss_top_scb_regs_MSSIO_VB2_CFG_TypeDef;

typedef union{                                                         /*!< MSSIO_VB4_CFG register definition*/
  __IO  uint32_t                       MSSIO_VB4_CFG;
  struct
  {
    __IO  uint32_t                       dpc_io_cfg_ibufmd_0  :1;
    __IO  uint32_t                       dpc_io_cfg_ibufmd_1  :1;
    __IO  uint32_t                       dpc_io_cfg_ibufmd_2  :1;
    __IO  uint32_t                       dpc_io_cfg_drv_0     :1;
    __IO  uint32_t                       dpc_io_cfg_drv_1     :1;
    __IO  uint32_t                       dpc_io_cfg_drv_2     :1;
    __IO  uint32_t                       dpc_io_cfg_drv_3     :1;
    __IO  uint32_t                       dpc_io_cfg_clamp     :1;
    __IO  uint32_t                       dpc_io_cfg_enhyst    :1;
    __IO  uint32_t                       dpc_io_cfg_lockdn_en :1;
    __IO  uint32_t                       dpc_io_cfg_wpd       :1;
    __IO  uint32_t                       dpc_io_cfg_wpu       :1;
    __IO  uint32_t                       dpc_io_cfg_atp_en    :1;
    __IO  uint32_t                       dpc_io_cfg_lp_persist_en :1;
    __IO  uint32_t                       dpc_io_cfg_lp_bypass_en :1;
    __I   uint32_t                       reserved_01          :17;
  } bitfield;
} g5_mss_top_scb_regs_MSSIO_VB4_CFG_TypeDef;

/*------------ g5_mss_top_scb_regs definition -----------*/
typedef struct
{
  __IO  g5_mss_top_scb_regs_SOFT_RESET_TypeDef SOFT_RESET;                                         /*!< Offset: 0x0  */
  __I   uint32_t                       UNUSED_SPACE0[3];                                   /*!< Offset: 0x4 */
  __IO  g5_mss_top_scb_regs_AXI_WSETUP_TypeDef AXI_WSETUP;                                         /*!< Offset: 0x10  */
  __IO  g5_mss_top_scb_regs_AXI_WADDR_TypeDef AXI_WADDR;                                          /*!< Offset: 0x14  */
  __IO  g5_mss_top_scb_regs_AXI_WDATA_TypeDef AXI_WDATA;                                          /*!< Offset: 0x18  */
  __IO  g5_mss_top_scb_regs_AXI_RSETUP_TypeDef AXI_RSETUP;                                         /*!< Offset: 0x1c  */
  __IO  g5_mss_top_scb_regs_AXI_RADDR_TypeDef AXI_RADDR;                                          /*!< Offset: 0x20  */
  __IO  g5_mss_top_scb_regs_AXI_RDATA_TypeDef AXI_RDATA;                                          /*!< Offset: 0x24  */
  __IO  g5_mss_top_scb_regs_AXI_STATUS_TypeDef AXI_STATUS;                                         /*!< Offset: 0x28  */
  __IO  g5_mss_top_scb_regs_AXI_CONTROL_TypeDef AXI_CONTROL;                                        /*!< Offset: 0x2c  */
  __IO  g5_mss_top_scb_regs_REDUNDANCY_TypeDef REDUNDANCY;                                         /*!< Offset: 0x30  */
  __I   uint32_t                       UNUSED_SPACE1[7];                                   /*!< Offset: 0x34 */
  __IO  g5_mss_top_scb_regs_BIST_CONFIG_TypeDef BIST_CONFIG;                                        /*!< Offset: 0x50  */
  __IO  g5_mss_top_scb_regs_BIST_DATA_TypeDef BIST_DATA;                                          /*!< Offset: 0x54  */
  __IO  g5_mss_top_scb_regs_BIST_COMMAND_TypeDef BIST_COMMAND;                                       /*!< Offset: 0x58  */
  __I   uint32_t                       UNUSED_SPACE2[41];                                  /*!< Offset: 0x5c */
  __IO  g5_mss_top_scb_regs_MSS_RESET_CR_TypeDef MSS_RESET_CR;                                       /*!< Offset: 0x100  */
  __IO  g5_mss_top_scb_regs_MSS_STATUS_TypeDef MSS_STATUS;                                         /*!< Offset: 0x104  */
  __IO  g5_mss_top_scb_regs_BOOT_ADDR0_TypeDef BOOT_ADDR0;                                         /*!< Offset: 0x108  */
  __IO  g5_mss_top_scb_regs_BOOT_ADDR1_TypeDef BOOT_ADDR1;                                         /*!< Offset: 0x10c  */
  __IO  g5_mss_top_scb_regs_BOOT_ADDR2_TypeDef BOOT_ADDR2;                                         /*!< Offset: 0x110  */
  __IO  g5_mss_top_scb_regs_BOOT_ADDR3_TypeDef BOOT_ADDR3;                                         /*!< Offset: 0x114  */
  __IO  g5_mss_top_scb_regs_BOOT_ADDR4_TypeDef BOOT_ADDR4;                                         /*!< Offset: 0x118  */
  __I   uint32_t                       UNUSED_SPACE3;                                      /*!< Offset: 0x11c */
  __IO  g5_mss_top_scb_regs_BOOT_ROM0_TypeDef BOOT_ROM0;                                          /*!< Offset: 0x120  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM1_TypeDef BOOT_ROM1;                                          /*!< Offset: 0x124  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM2_TypeDef BOOT_ROM2;                                          /*!< Offset: 0x128  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM3_TypeDef BOOT_ROM3;                                          /*!< Offset: 0x12c  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM4_TypeDef BOOT_ROM4;                                          /*!< Offset: 0x130  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM5_TypeDef BOOT_ROM5;                                          /*!< Offset: 0x134  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM6_TypeDef BOOT_ROM6;                                          /*!< Offset: 0x138  */
  __IO  g5_mss_top_scb_regs_BOOT_ROM7_TypeDef BOOT_ROM7;                                          /*!< Offset: 0x13c  */
  __I   uint32_t                       UNUSED_SPACE4[16];                                  /*!< Offset: 0x140 */
  __IO  g5_mss_top_scb_regs_FLASH_FREEZE_TypeDef FLASH_FREEZE;                                       /*!< Offset: 0x180  */
  __IO  g5_mss_top_scb_regs_G5CIO_TypeDef G5CIO;                                              /*!< Offset: 0x184  */
  __IO  g5_mss_top_scb_regs_DEVICE_ID_TypeDef DEVICE_ID;                                          /*!< Offset: 0x188  */
  __IO  g5_mss_top_scb_regs_MESSAGE_INT_TypeDef MESSAGE_INT;                                        /*!< Offset: 0x18c  */
  __IO  g5_mss_top_scb_regs_MESSAGE_TypeDef MESSAGE;                                            /*!< Offset: 0x190  */
  __IO  g5_mss_top_scb_regs_DEVRST_INT_TypeDef DEVRST_INT;                                         /*!< Offset: 0x194  */
  __IO  g5_mss_top_scb_regs_SCB_INTERRUPT_TypeDef SCB_INTERRUPT;                                      /*!< Offset: 0x198  */
  __IO  g5_mss_top_scb_regs_MSS_INTERRUPT_TypeDef MSS_INTERRUPT;                                      /*!< Offset: 0x19c  */
  __IO  g5_mss_top_scb_regs_DEVICE_CONFIG_CR_TypeDef DEVICE_CONFIG_CR;                                   /*!< Offset: 0x1a0  */
  __IO  g5_mss_top_scb_regs_ATHENA_CR_TypeDef ATHENA_CR;                                          /*!< Offset: 0x1a4  */
  __IO  g5_mss_top_scb_regs_ENVM_CR_TypeDef ENVM_CR;                                            /*!< Offset: 0x1a8  */
  __IO  g5_mss_top_scb_regs_ENVM_POWER_CR_TypeDef ENVM_POWER_CR;                                      /*!< Offset: 0x1ac  */
  __IO  g5_mss_top_scb_regs_RAM_SHUTDOWN_CR_TypeDef RAM_SHUTDOWN_CR;                                    /*!< Offset: 0x1b0  */
  __IO  g5_mss_top_scb_regs_RAM_MARGIN_CR_TypeDef RAM_MARGIN_CR;                                      /*!< Offset: 0x1b4  */
  __IO  g5_mss_top_scb_regs_TRACE_CR_TypeDef TRACE_CR;                                           /*!< Offset: 0x1b8  */
  __IO  g5_mss_top_scb_regs_MSSIO_CONTROL_CR_TypeDef MSSIO_CONTROL_CR;                                   /*!< Offset: 0x1bc  */
  __I   g5_mss_top_scb_regs_MSS_IO_LOCKDOWN_CR_TypeDef MSS_IO_LOCKDOWN_CR;                                 /*!< Offset: 0x1c0  */
  __IO  g5_mss_top_scb_regs_MSSIO_BANK2_CFG_CR_TypeDef MSSIO_BANK2_CFG_CR;                                 /*!< Offset: 0x1c4  */
  __IO  g5_mss_top_scb_regs_MSSIO_BANK4_CFG_CR_TypeDef MSSIO_BANK4_CFG_CR;                                 /*!< Offset: 0x1c8  */
  __I   uint32_t                       UNUSED_SPACE5[13];                                  /*!< Offset: 0x1cc */
  __IO  g5_mss_top_scb_regs_DLL0_CTRL0_TypeDef DLL0_CTRL0;                                         /*!< Offset: 0x200  */
  __IO  g5_mss_top_scb_regs_DLL0_CTRL1_TypeDef DLL0_CTRL1;                                         /*!< Offset: 0x204  */
  __IO  g5_mss_top_scb_regs_DLL0_STAT0_TypeDef DLL0_STAT0;                                         /*!< Offset: 0x208  */
  __I   g5_mss_top_scb_regs_DLL0_STAT1_TypeDef DLL0_STAT1;                                         /*!< Offset: 0x20c  */
  __I   g5_mss_top_scb_regs_DLL0_STAT2_TypeDef DLL0_STAT2;                                         /*!< Offset: 0x210  */
  __IO  g5_mss_top_scb_regs_DLL0_TEST_TypeDef DLL0_TEST;                                          /*!< Offset: 0x214  */
  __I   uint32_t                       UNUSED_SPACE6[2];                                   /*!< Offset: 0x218 */
  __IO  g5_mss_top_scb_regs_DLL1_CTRL0_TypeDef DLL1_CTRL0;                                         /*!< Offset: 0x220  */
  __IO  g5_mss_top_scb_regs_DLL1_CTRL1_TypeDef DLL1_CTRL1;                                         /*!< Offset: 0x224  */
  __IO  g5_mss_top_scb_regs_DLL1_STAT0_TypeDef DLL1_STAT0;                                         /*!< Offset: 0x228  */
  __I   g5_mss_top_scb_regs_DLL1_STAT1_TypeDef DLL1_STAT1;                                         /*!< Offset: 0x22c  */
  __I   g5_mss_top_scb_regs_DLL1_STAT2_TypeDef DLL1_STAT2;                                         /*!< Offset: 0x230  */
  __IO  g5_mss_top_scb_regs_DLL1_TEST_TypeDef DLL1_TEST;                                          /*!< Offset: 0x234  */
  __I   uint32_t                       UNUSED_SPACE7[2];                                   /*!< Offset: 0x238 */
  __IO  g5_mss_top_scb_regs_DLL2_CTRL0_TypeDef DLL2_CTRL0;                                         /*!< Offset: 0x240  */
  __IO  g5_mss_top_scb_regs_DLL2_CTRL1_TypeDef DLL2_CTRL1;                                         /*!< Offset: 0x244  */
  __IO  g5_mss_top_scb_regs_DLL2_STAT0_TypeDef DLL2_STAT0;                                         /*!< Offset: 0x248  */
  __I   g5_mss_top_scb_regs_DLL2_STAT1_TypeDef DLL2_STAT1;                                         /*!< Offset: 0x24c  */
  __I   g5_mss_top_scb_regs_DLL2_STAT2_TypeDef DLL2_STAT2;                                         /*!< Offset: 0x250  */
  __IO  g5_mss_top_scb_regs_DLL2_TEST_TypeDef DLL2_TEST;                                          /*!< Offset: 0x254  */
  __I   uint32_t                       UNUSED_SPACE8[2];                                   /*!< Offset: 0x258 */
  __IO  g5_mss_top_scb_regs_DLL3_CTRL0_TypeDef DLL3_CTRL0;                                         /*!< Offset: 0x260  */
  __IO  g5_mss_top_scb_regs_DLL3_CTRL1_TypeDef DLL3_CTRL1;                                         /*!< Offset: 0x264  */
  __IO  g5_mss_top_scb_regs_DLL3_STAT0_TypeDef DLL3_STAT0;                                         /*!< Offset: 0x268  */
  __I   g5_mss_top_scb_regs_DLL3_STAT1_TypeDef DLL3_STAT1;                                         /*!< Offset: 0x26c  */
  __I   g5_mss_top_scb_regs_DLL3_STAT2_TypeDef DLL3_STAT2;                                         /*!< Offset: 0x270  */
  __IO  g5_mss_top_scb_regs_DLL3_TEST_TypeDef DLL3_TEST;                                          /*!< Offset: 0x274  */
  __IO  g5_mss_top_scb_regs_MSSIO_VB2_CFG_TypeDef MSSIO_VB2_CFG;                                      /*!< Offset: 0x278  */
  __IO  g5_mss_top_scb_regs_MSSIO_VB4_CFG_TypeDef MSSIO_VB4_CFG;                                      /*!< Offset: 0x27c  */
} g5_mss_top_scb_regs_TypeDef;


#define CFG_DDR_SGMII_PHY_BASE         (0x20007000)         /*!< ( CFG_DDR_SGMII_PHY ) Base Address */
#define DDRCFG_BASE                    (0x20080000)         /*!< ( DDRCFG ) Base Address */

#define SYSREGSCB_BASE                 (0x20003000)         /*!< ( SYSREGSCB ) Base Address */
#define IOSCBCFG_BASE                  (0x37080000)         /*!< ( IOSCBCFG ) Base Address */

extern CFG_DDR_SGMII_PHY_TypeDef       * const CFG_DDR_SGMII_PHY   ;
extern DDR_CSR_APB_TypeDef             * const DDRCFG              ;
extern IOSCBCFG_TypeDef                * const SCBCFG_REGS         ;
extern g5_mss_top_scb_regs_TypeDef     * const SCB_REGS            ;

#ifdef __cplusplus
}
#endif

#endif /* MSS_DDR_REGS_H_ */
