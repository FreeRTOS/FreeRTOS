/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_ddrc.h
 * @author Microchip-FPGA Embedded Systems Solutions
 *
 *
 * Note 1: This file should not be edited. If you need to modify a parameter
 * without going through regenerating using the MSS Configurator Libero flow 
 * or editing the associated xml file
 * the following method is recommended: 

 * 1. edit the following file 
 * boards/your_board/platform_config/mpfs_hal_config/mss_sw_config.h

 * 2. define the value you want to override there.
 * (Note: There is a commented example in the platform directory)

 * Note 2: The definition in mss_sw_config.h takes precedence, as
 * mss_sw_config.h is included prior to the generated header files located in
 * boards/your_board/fpga_design_config
 *
 */

#ifndef HW_DDRC_H_
#define HW_DDRC_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_CFG_MANUAL_ADDRESS_MAP)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_MANUAL_ADDRESS_MAP    0x00000000UL
    /* CFG_MANUAL_ADDRESS_MAP            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_CHIPADDR_MAP)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_CHIPADDR_MAP    0x0000001DUL
    /* CFG_CHIPADDR_MAP                  [0:32]  RW value= 0x00001D */
#endif
#if !defined (LIBERO_SETTING_CFG_CIDADDR_MAP)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_CIDADDR_MAP    0x00000000UL
    /* CFG_CIDADDR_MAP                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MB_AUTOPCH_COL_BIT_POS_LOW)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_MB_AUTOPCH_COL_BIT_POS_LOW    0x00000004UL
    /* CFG_MB_AUTOPCH_COL_BIT_POS_LOW    [0:32]  RW value= 0x00000004 */
#endif
#if !defined (LIBERO_SETTING_CFG_MB_AUTOPCH_COL_BIT_POS_HIGH)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_MB_AUTOPCH_COL_BIT_POS_HIGH    0x0000000AUL
    /* CFG_MB_AUTOPCH_COL_BIT_POS_HIGH        [0:32]  RW value= 0x0000000A */
#endif
#if !defined (LIBERO_SETTING_CFG_BANKADDR_MAP_0)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_BANKADDR_MAP_0    0x0000C2CAUL
    /* CFG_BANKADDR_MAP_0                [0:32]  RW value= 0x00C2CA */
#endif
#if !defined (LIBERO_SETTING_CFG_BANKADDR_MAP_1)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_BANKADDR_MAP_1    0x00000000UL
    /* CFG_BANKADDR_MAP_1                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ROWADDR_MAP_0)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_ROWADDR_MAP_0    0x9140F38DUL
    /* CFG_ROWADDR_MAP_0                 [0:32]  RW value= 0x9140F38D */
#endif
#if !defined (LIBERO_SETTING_CFG_ROWADDR_MAP_1)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_ROWADDR_MAP_1    0x75955134UL
    /* CFG_ROWADDR_MAP_1                 [0:32]  RW value= 0x75955134 */
#endif
#if !defined (LIBERO_SETTING_CFG_ROWADDR_MAP_2)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_ROWADDR_MAP_2    0x71B69961UL
    /* CFG_ROWADDR_MAP_2                 [0:32]  RW value= 0x71B69961 */
#endif
#if !defined (LIBERO_SETTING_CFG_ROWADDR_MAP_3)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_ROWADDR_MAP_3    0x00000000UL
    /* CFG_ROWADDR_MAP_3                 [0:32]  RW value= 0x000 */
#endif
#if !defined (LIBERO_SETTING_CFG_COLADDR_MAP_0)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_COLADDR_MAP_0    0x440C2040UL
    /* CFG_COLADDR_MAP_0                 [0:32]  RW value= 0x440C2040 */
#endif
#if !defined (LIBERO_SETTING_CFG_COLADDR_MAP_1)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_COLADDR_MAP_1    0x02481C61UL
    /* CFG_COLADDR_MAP_1                 [0:32]  RW value= 0x02481C61 */
#endif
#if !defined (LIBERO_SETTING_CFG_COLADDR_MAP_2)
/*IP Blk = ADDR_MAP Access=RW */
#define LIBERO_SETTING_CFG_COLADDR_MAP_2    0x00000000UL
    /* CFG_COLADDR_MAP_2                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_VRCG_ENABLE)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_VRCG_ENABLE    0x00000140UL
    /* CFG_VRCG_ENABLE                   [0:32]  RW value= 0x00000140 */
#endif
#if !defined (LIBERO_SETTING_CFG_VRCG_DISABLE)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_VRCG_DISABLE    0x000000A0UL
    /* CFG_VRCG_DISABLE                  [0:32]  RW value= 0x000000A0 */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_LATENCY_SET)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_LATENCY_SET    0x00000000UL
    /* CFG_WRITE_LATENCY_SET             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_THERMAL_OFFSET)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_THERMAL_OFFSET    0x00000000UL
    /* CFG_THERMAL_OFFSET                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_SOC_ODT)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_SOC_ODT    0x00000006UL
    /* CFG_SOC_ODT                       [0:32]  RW value= 0x6 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODTE_CK)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_ODTE_CK    0x00000000UL
    /* CFG_ODTE_CK                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODTE_CS)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_ODTE_CS    0x00000000UL
    /* CFG_ODTE_CS                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODTD_CA)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_ODTD_CA    0x00000000UL
    /* CFG_ODTD_CA                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_LPDDR4_FSP_OP)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_LPDDR4_FSP_OP    0x00000001UL
    /* CFG_LPDDR4_FSP_OP                 [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_GENERATE_REFRESH_ON_SRX)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_GENERATE_REFRESH_ON_SRX    0x00000001UL
    /* CFG_GENERATE_REFRESH_ON_SRX       [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_CFG_DBI_CL)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_DBI_CL    0x00000016UL
    /* CFG_DBI_CL                        [0:32]  RW value= 0x00000016 */
#endif
#if !defined (LIBERO_SETTING_CFG_NON_DBI_CL)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_CFG_NON_DBI_CL    0x00000016UL
    /* CFG_NON_DBI_CL                    [0:32]  RW value= 0x00000016 */
#endif
#if !defined (LIBERO_SETTING_INIT_FORCE_WRITE_DATA_0)
/*IP Blk = MC_BASE3 Access=RW */
#define LIBERO_SETTING_INIT_FORCE_WRITE_DATA_0    0x00000000UL
    /* INIT_FORCE_WRITE_DATA_0           [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_CRC)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_CRC    0x00000000UL
    /* CFG_WRITE_CRC                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MPR_READ_FORMAT)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_MPR_READ_FORMAT    0x00000000UL
    /* CFG_MPR_READ_FORMAT               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_WR_CMD_LAT_CRC_DM)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WR_CMD_LAT_CRC_DM    0x00000000UL
    /* CFG_WR_CMD_LAT_CRC_DM             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_FINE_GRAN_REF_MODE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_FINE_GRAN_REF_MODE    0x00000000UL
    /* CFG_FINE_GRAN_REF_MODE            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TEMP_SENSOR_READOUT)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_TEMP_SENSOR_READOUT    0x00000000UL
    /* CFG_TEMP_SENSOR_READOUT           [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_PER_DRAM_ADDR_EN)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_PER_DRAM_ADDR_EN    0x00000000UL
    /* CFG_PER_DRAM_ADDR_EN              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_GEARDOWN_MODE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_GEARDOWN_MODE    0x00000000UL
    /* CFG_GEARDOWN_MODE                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_WR_PREAMBLE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WR_PREAMBLE    0x00000001UL
    /* CFG_WR_PREAMBLE                   [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_RD_PREAMBLE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RD_PREAMBLE    0x00000000UL
    /* CFG_RD_PREAMBLE                   [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_RD_PREAMB_TRN_MODE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RD_PREAMB_TRN_MODE    0x00000000UL
    /* CFG_RD_PREAMB_TRN_MODE            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_SR_ABORT)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_SR_ABORT    0x00000000UL
    /* CFG_SR_ABORT                      [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_CS_TO_CMDADDR_LATENCY)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CS_TO_CMDADDR_LATENCY    0x00000000UL
    /* CFG_CS_TO_CMDADDR_LATENCY         [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_INT_VREF_MON)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_INT_VREF_MON    0x00000000UL
    /* CFG_INT_VREF_MON                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TEMP_CTRL_REF_MODE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_TEMP_CTRL_REF_MODE    0x00000000UL
    /* CFG_TEMP_CTRL_REF_MODE            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TEMP_CTRL_REF_RANGE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_TEMP_CTRL_REF_RANGE    0x00000000UL
    /* CFG_TEMP_CTRL_REF_RANGE           [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MAX_PWR_DOWN_MODE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_MAX_PWR_DOWN_MODE    0x00000000UL
    /* CFG_MAX_PWR_DOWN_MODE             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_READ_DBI)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_READ_DBI    0x00000000UL
    /* CFG_READ_DBI                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_DBI)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_DBI    0x00000000UL
    /* CFG_WRITE_DBI                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DATA_MASK)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_DATA_MASK    0x00000001UL
    /* CFG_DATA_MASK                     [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_CA_PARITY_PERSIST_ERR)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CA_PARITY_PERSIST_ERR    0x00000000UL
    /* CFG_CA_PARITY_PERSIST_ERR         [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_RTT_PARK)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RTT_PARK    0x00000000UL
    /* CFG_RTT_PARK                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_INBUF_4_PD)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_ODT_INBUF_4_PD    0x00000000UL
    /* CFG_ODT_INBUF_4_PD                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CA_PARITY_ERR_STATUS)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CA_PARITY_ERR_STATUS    0x00000000UL
    /* CFG_CA_PARITY_ERR_STATUS          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CRC_ERROR_CLEAR)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CRC_ERROR_CLEAR    0x00000000UL
    /* CFG_CRC_ERROR_CLEAR               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CA_PARITY_LATENCY)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CA_PARITY_LATENCY    0x00000000UL
    /* CFG_CA_PARITY_LATENCY             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CCD_S)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CCD_S    0x00000005UL
    /* CFG_CCD_S                         [0:32]  RW value= 0x00000005 */
#endif
#if !defined (LIBERO_SETTING_CFG_CCD_L)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_CCD_L    0x00000006UL
    /* CFG_CCD_L                         [0:32]  RW value= 0x00000006 */
#endif
#if !defined (LIBERO_SETTING_CFG_VREFDQ_TRN_ENABLE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_VREFDQ_TRN_ENABLE    0x00000000UL
    /* CFG_VREFDQ_TRN_ENABLE             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_VREFDQ_TRN_RANGE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_VREFDQ_TRN_RANGE    0x00000000UL
    /* CFG_VREFDQ_TRN_RANGE              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_VREFDQ_TRN_VALUE)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_VREFDQ_TRN_VALUE    0x00000000UL
    /* CFG_VREFDQ_TRN_VALUE              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_RRD_S)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RRD_S    0x00000004UL
    /* CFG_RRD_S                         [0:32]  RW value= 0x00000004 */
#endif
#if !defined (LIBERO_SETTING_CFG_RRD_L)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RRD_L    0x00000003UL
    /* CFG_RRD_L                         [0:32]  RW value= 0x00000003 */
#endif
#if !defined (LIBERO_SETTING_CFG_WTR_S)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WTR_S    0x00000003UL
    /* CFG_WTR_S                         [0:32]  RW value= 0x00000003 */
#endif
#if !defined (LIBERO_SETTING_CFG_WTR_L)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WTR_L    0x00000003UL
    /* CFG_WTR_L                         [0:32]  RW value= 0x00000003 */
#endif
#if !defined (LIBERO_SETTING_CFG_WTR_S_CRC_DM)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WTR_S_CRC_DM    0x00000003UL
    /* CFG_WTR_S_CRC_DM                  [0:32]  RW value= 0x00000003 */
#endif
#if !defined (LIBERO_SETTING_CFG_WTR_L_CRC_DM)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WTR_L_CRC_DM    0x00000003UL
    /* CFG_WTR_L_CRC_DM                  [0:32]  RW value= 0x00000003 */
#endif
#if !defined (LIBERO_SETTING_CFG_WR_CRC_DM)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_WR_CRC_DM    0x00000006UL
    /* CFG_WR_CRC_DM                     [0:32]  RW value= 0x00000006 */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RFC1    0x00000036UL
    /* CFG_RFC1                          [0:32]  RW value= 0x00000036 */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC2)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RFC2    0x00000036UL
    /* CFG_RFC2                          [0:32]  RW value= 0x00000036 */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC4)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RFC4    0x00000036UL
    /* CFG_RFC4                          [0:32]  RW value= 0x00000036 */
#endif
#if !defined (LIBERO_SETTING_CFG_NIBBLE_DEVICES)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_NIBBLE_DEVICES    0x00000000UL
    /* CFG_NIBBLE_DEVICES                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS0_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS0_0    0x81881881UL
    /* CFG_BIT_MAP_INDEX_CS0_0           [0:32]  RW value= 0x81881881 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS0_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS0_1    0x00008818UL
    /* CFG_BIT_MAP_INDEX_CS0_1           [0:32]  RW value= 0x00008818 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS1_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS1_0    0xA92A92A9UL
    /* CFG_BIT_MAP_INDEX_CS1_0           [0:32]  RW value= 0xa92a92a9 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS1_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS1_1    0x00002A92UL
    /* CFG_BIT_MAP_INDEX_CS1_1           [0:32]  RW value= 0x00002a92 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS2_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS2_0    0xC28C28C2UL
    /* CFG_BIT_MAP_INDEX_CS2_0           [0:32]  RW value= 0xc28c28c2 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS2_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS2_1    0x00008C28UL
    /* CFG_BIT_MAP_INDEX_CS2_1           [0:32]  RW value= 0x00008c28 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS3_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS3_0    0xEA2EA2EAUL
    /* CFG_BIT_MAP_INDEX_CS3_0           [0:32]  RW value= 0xea2ea2ea */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS3_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS3_1    0x00002EA2UL
    /* CFG_BIT_MAP_INDEX_CS3_1           [0:32]  RW value= 0x00002ea2 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS4_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS4_0    0x03903903UL
    /* CFG_BIT_MAP_INDEX_CS4_0           [0:32]  RW value= 0x03903903 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS4_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS4_1    0x00009039UL
    /* CFG_BIT_MAP_INDEX_CS4_1           [0:32]  RW value= 0x00009039 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS5_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS5_0    0x2B32B32BUL
    /* CFG_BIT_MAP_INDEX_CS5_0           [0:32]  RW value= 0x2b32b32b */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS5_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS5_1    0x000032B3UL
    /* CFG_BIT_MAP_INDEX_CS5_1           [0:32]  RW value= 0x000032b3 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS6_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS6_0    0x44944944UL
    /* CFG_BIT_MAP_INDEX_CS6_0           [0:32]  RW value= 0x44944944 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS6_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS6_1    0x00009449UL
    /* CFG_BIT_MAP_INDEX_CS6_1           [0:32]  RW value= 0x00009449 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS7_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS7_0    0x6C36C36CUL
    /* CFG_BIT_MAP_INDEX_CS7_0           [0:32]  RW value= 0x6c36c36c */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS7_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS7_1    0x000036C3UL
    /* CFG_BIT_MAP_INDEX_CS7_1           [0:32]  RW value= 0x000036c3 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS8_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS8_0    0x85985985UL
    /* CFG_BIT_MAP_INDEX_CS8_0           [0:32]  RW value= 0x85985985 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS8_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS8_1    0x00009859UL
    /* CFG_BIT_MAP_INDEX_CS8_1           [0:32]  RW value= 0x00009859 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS9_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS9_0    0xAD3AD3ADUL
    /* CFG_BIT_MAP_INDEX_CS9_0           [0:32]  RW value= 0xad3ad3ad */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS9_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS9_1    0x00003AD3UL
    /* CFG_BIT_MAP_INDEX_CS9_1           [0:32]  RW value= 0x00003ad3 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS10_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS10_0    0xC69C69C6UL
    /* CFG_BIT_MAP_INDEX_CS10_0          [0:32]  RW value= 0xc69c69c6 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS10_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS10_1    0x00009C69UL
    /* CFG_BIT_MAP_INDEX_CS10_1          [0:32]  RW value= 0x00009c69 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS11_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS11_0    0xEE3EE3EEUL
    /* CFG_BIT_MAP_INDEX_CS11_0          [0:32]  RW value= 0xee3ee3ee */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS11_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS11_1    0x00003EE3UL
    /* CFG_BIT_MAP_INDEX_CS11_1          [0:32]  RW value= 0x00003ee3 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS12_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS12_0    0x07A07A07UL
    /* CFG_BIT_MAP_INDEX_CS12_0          [0:32]  RW value= 0x07a07a07 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS12_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS12_1    0x0000A07AUL
    /* CFG_BIT_MAP_INDEX_CS12_1          [0:32]  RW value= 0x0000a07a */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS13_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS13_0    0x2F42F42FUL
    /* CFG_BIT_MAP_INDEX_CS13_0          [0:32]  RW value= 0x2f42f42f */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS13_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS13_1    0x000042F4UL
    /* CFG_BIT_MAP_INDEX_CS13_1          [0:32]  RW value= 0x000042f4 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS14_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS14_0    0x48A48A48UL
    /* CFG_BIT_MAP_INDEX_CS14_0          [0:32]  RW value= 0x48a48a48 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS14_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS14_1    0x0000A48AUL
    /* CFG_BIT_MAP_INDEX_CS14_1          [0:32]  RW value= 0x0000a48a */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS15_0)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS15_0    0x70470470UL
    /* CFG_BIT_MAP_INDEX_CS15_0          [0:32]  RW value= 0x70470470 */
#endif
#if !defined (LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS15_1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS15_1    0x00004704UL
    /* CFG_BIT_MAP_INDEX_CS15_1          [0:32]  RW value= 0x00004704 */
#endif
#if !defined (LIBERO_SETTING_CFG_NUM_LOGICAL_RANKS_PER_3DS)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_NUM_LOGICAL_RANKS_PER_3DS    0x00000000UL
    /* CFG_NUM_LOGICAL_RANKS_PER_3DS     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC_DLR1)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RFC_DLR1    0x00000048UL
    /* CFG_RFC_DLR1                      [0:32]  RW value= 0x00000048 */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC_DLR2)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RFC_DLR2    0x0000002CUL
    /* CFG_RFC_DLR2                      [0:32]  RW value= 0x0000002C */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC_DLR4)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RFC_DLR4    0x00000020UL
    /* CFG_RFC_DLR4                      [0:32]  RW value= 0x00000020 */
#endif
#if !defined (LIBERO_SETTING_CFG_RRD_DLR)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_RRD_DLR    0x00000004UL
    /* CFG_RRD_DLR                       [0:32]  RW value= 0x00000004 */
#endif
#if !defined (LIBERO_SETTING_CFG_FAW_DLR)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_FAW_DLR    0x00000010UL
    /* CFG_FAW_DLR                       [0:32]  RW value= 0x00000010 */
#endif
#if !defined (LIBERO_SETTING_CFG_ADVANCE_ACTIVATE_READY)
/*IP Blk = MC_BASE1 Access=RW */
#define LIBERO_SETTING_CFG_ADVANCE_ACTIVATE_READY    0x00000000UL
    /* CFG_ADVANCE_ACTIVATE_READY        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CTRLR_SOFT_RESET_N)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CTRLR_SOFT_RESET_N    0x00000001UL
    /* CTRLR_SOFT_RESET_N                [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_LOOKAHEAD_PCH)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_LOOKAHEAD_PCH    0x00000000UL
    /* CFG_LOOKAHEAD_PCH                 [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_LOOKAHEAD_ACT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_LOOKAHEAD_ACT    0x00000000UL
    /* CFG_LOOKAHEAD_ACT                 [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_INIT_AUTOINIT_DISABLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_AUTOINIT_DISABLE    0x00000000UL
    /* INIT_AUTOINIT_DISABLE             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_FORCE_RESET)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_FORCE_RESET    0x00000000UL
    /* INIT_FORCE_RESET                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_GEARDOWN_EN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_GEARDOWN_EN    0x00000000UL
    /* INIT_GEARDOWN_EN                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_DISABLE_CKE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_DISABLE_CKE    0x00000000UL
    /* INIT_DISABLE_CKE                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_CS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_CS    0x00000000UL
    /* INIT_CS                           [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_PRECHARGE_ALL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_PRECHARGE_ALL    0x00000000UL
    /* INIT_PRECHARGE_ALL                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_REFRESH)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_REFRESH    0x00000000UL
    /* INIT_REFRESH                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_ZQ_CAL_REQ)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_ZQ_CAL_REQ    0x00000000UL
    /* INIT_ZQ_CAL_REQ                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_BL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_BL    0x00000000UL
    /* CFG_BL                            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CTRLR_INIT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CTRLR_INIT    0x00000000UL
    /* CTRLR_INIT                        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AUTO_REF_EN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_AUTO_REF_EN    0x00000001UL
    /* CFG_AUTO_REF_EN                   [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_RAS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RAS    0x00000022UL
    /* CFG_RAS                           [0:32]  RW value= 0x22 */
#endif
#if !defined (LIBERO_SETTING_CFG_RCD)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RCD    0x0000000FUL
    /* CFG_RCD                           [0:32]  RW value= 0xF */
#endif
#if !defined (LIBERO_SETTING_CFG_RRD)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RRD    0x00000008UL
    /* CFG_RRD                           [0:32]  RW value= 0x8 */
#endif
#if !defined (LIBERO_SETTING_CFG_RP)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RP    0x00000011UL
    /* CFG_RP                            [0:32]  RW value= 0x11 */
#endif
#if !defined (LIBERO_SETTING_CFG_RC)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RC    0x00000033UL
    /* CFG_RC                            [0:32]  RW value= 0x33 */
#endif
#if !defined (LIBERO_SETTING_CFG_FAW)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_FAW    0x00000020UL
    /* CFG_FAW                           [0:32]  RW value= 0x20 */
#endif
#if !defined (LIBERO_SETTING_CFG_RFC)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RFC    0x00000130UL
    /* CFG_RFC                           [0:32]  RW value= 0x130 */
#endif
#if !defined (LIBERO_SETTING_CFG_RTP)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RTP    0x00000008UL
    /* CFG_RTP                           [0:32]  RW value= 0x8 */
#endif
#if !defined (LIBERO_SETTING_CFG_WR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WR    0x00000010UL
    /* CFG_WR                            [0:32]  RW value= 0x10 */
#endif
#if !defined (LIBERO_SETTING_CFG_WTR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WTR    0x00000008UL
    /* CFG_WTR                           [0:32]  RW value= 0x8 */
#endif
#if !defined (LIBERO_SETTING_CFG_PASR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_PASR    0x00000000UL
    /* CFG_PASR                          [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_XP)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_XP    0x00000006UL
    /* CFG_XP                            [0:32]  RW value= 0x6 */
#endif
#if !defined (LIBERO_SETTING_CFG_XSR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_XSR    0x0000001FUL
    /* CFG_XSR                           [0:32]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_CFG_CL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CL    0x00000005UL
    /* CFG_CL                            [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_CFG_READ_TO_WRITE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_READ_TO_WRITE    0x0000000FUL
    /* CFG_READ_TO_WRITE                 [0:32]  RW value= 0xF */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_TO_WRITE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_TO_WRITE    0x0000000FUL
    /* CFG_WRITE_TO_WRITE                [0:32]  RW value= 0xF */
#endif
#if !defined (LIBERO_SETTING_CFG_READ_TO_READ)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_READ_TO_READ    0x0000000FUL
    /* CFG_READ_TO_READ                  [0:32]  RW value= 0xF */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_TO_READ)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_TO_READ    0x0000001FUL
    /* CFG_WRITE_TO_READ                 [0:32]  RW value= 0x1F */
#endif
#if !defined (LIBERO_SETTING_CFG_READ_TO_WRITE_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_READ_TO_WRITE_ODT    0x00000001UL
    /* CFG_READ_TO_WRITE_ODT             [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_TO_WRITE_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_TO_WRITE_ODT    0x00000000UL
    /* CFG_WRITE_TO_WRITE_ODT            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_READ_TO_READ_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_READ_TO_READ_ODT    0x00000001UL
    /* CFG_READ_TO_READ_ODT              [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_WRITE_TO_READ_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WRITE_TO_READ_ODT    0x00000001UL
    /* CFG_WRITE_TO_READ_ODT             [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_MIN_READ_IDLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MIN_READ_IDLE    0x00000007UL
    /* CFG_MIN_READ_IDLE                 [0:32]  RW value= 0x7 */
#endif
#if !defined (LIBERO_SETTING_CFG_MRD)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MRD    0x0000000CUL
    /* CFG_MRD                           [0:32]  RW value= 0xC */
#endif
#if !defined (LIBERO_SETTING_CFG_BT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_BT    0x00000000UL
    /* CFG_BT                            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_DS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DS    0x00000006UL
    /* CFG_DS                            [0:32]  RW value= 0x6 */
#endif
#if !defined (LIBERO_SETTING_CFG_QOFF)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_QOFF    0x00000000UL
    /* CFG_QOFF                          [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_RTT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RTT    0x00000002UL
    /* CFG_RTT                           [0:32]  RW value= 0x2 */
#endif
#if !defined (LIBERO_SETTING_CFG_DLL_DISABLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DLL_DISABLE    0x00000000UL
    /* CFG_DLL_DISABLE                   [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_REF_PER)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_REF_PER    0x00000C34UL
    /* CFG_REF_PER                       [0:32]  RW value= 0xC34 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARTUP_DELAY)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_STARTUP_DELAY    0x00027100UL
    /* CFG_STARTUP_DELAY                 [0:32]  RW value= 0x27100 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_COLBITS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MEM_COLBITS    0x0000000AUL
    /* CFG_MEM_COLBITS                   [0:32]  RW value= 0xA */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_ROWBITS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MEM_ROWBITS    0x00000010UL
    /* CFG_MEM_ROWBITS                   [0:32]  RW value= 0x10 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_BANKBITS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MEM_BANKBITS    0x00000003UL
    /* CFG_MEM_BANKBITS                  [0:32]  RW value= 0x3 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS0)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS0    0x00000000UL
    /* CFG_ODT_RD_MAP_CS0                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS1)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS1    0x00000000UL
    /* CFG_ODT_RD_MAP_CS1                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS2)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS2    0x00000000UL
    /* CFG_ODT_RD_MAP_CS2                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS3)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS3    0x00000000UL
    /* CFG_ODT_RD_MAP_CS3                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS4)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS4    0x00000000UL
    /* CFG_ODT_RD_MAP_CS4                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS5)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS5    0x00000000UL
    /* CFG_ODT_RD_MAP_CS5                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS6)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS6    0x00000000UL
    /* CFG_ODT_RD_MAP_CS6                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_MAP_CS7)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_MAP_CS7    0x00000000UL
    /* CFG_ODT_RD_MAP_CS7                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS0)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS0    0x00000000UL
    /* CFG_ODT_WR_MAP_CS0                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS1)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS1    0x00000000UL
    /* CFG_ODT_WR_MAP_CS1                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS2)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS2    0x00000000UL
    /* CFG_ODT_WR_MAP_CS2                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS3)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS3    0x00000000UL
    /* CFG_ODT_WR_MAP_CS3                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS4)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS4    0x00000000UL
    /* CFG_ODT_WR_MAP_CS4                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS5)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS5    0x00000000UL
    /* CFG_ODT_WR_MAP_CS5                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS6)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS6    0x00000000UL
    /* CFG_ODT_WR_MAP_CS6                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_MAP_CS7)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_MAP_CS7    0x00000000UL
    /* CFG_ODT_WR_MAP_CS7                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_TURN_ON)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_TURN_ON    0x00000000UL
    /* CFG_ODT_RD_TURN_ON                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_TURN_ON)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_TURN_ON    0x00000000UL
    /* CFG_ODT_WR_TURN_ON                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_RD_TURN_OFF)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_RD_TURN_OFF    0x00000000UL
    /* CFG_ODT_RD_TURN_OFF               [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_WR_TURN_OFF)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_WR_TURN_OFF    0x00000000UL
    /* CFG_ODT_WR_TURN_OFF               [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_EMR3)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_EMR3    0x00000000UL
    /* CFG_EMR3                          [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_TWO_T)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_TWO_T    0x00000000UL
    /* CFG_TWO_T                         [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_TWO_T_SEL_CYCLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_TWO_T_SEL_CYCLE    0x00000001UL
    /* CFG_TWO_T_SEL_CYCLE               [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_REGDIMM)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_REGDIMM    0x00000000UL
    /* CFG_REGDIMM                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_MOD)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MOD    0x0000000CUL
    /* CFG_MOD                           [0:32]  RW value= 0xC */
#endif
#if !defined (LIBERO_SETTING_CFG_XS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_XS    0x00000005UL
    /* CFG_XS                            [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_CFG_XSDLL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_XSDLL    0x00000200UL
    /* CFG_XSDLL                         [0:32]  RW value= 0x00000200 */
#endif
#if !defined (LIBERO_SETTING_CFG_XPR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_XPR    0x00000005UL
    /* CFG_XPR                           [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_CFG_AL_MODE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_AL_MODE    0x00000000UL
    /* CFG_AL_MODE                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_CWL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CWL    0x00000005UL
    /* CFG_CWL                           [0:32]  RW value= 0x5 */
#endif
#if !defined (LIBERO_SETTING_CFG_BL_MODE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_BL_MODE    0x00000000UL
    /* CFG_BL_MODE                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_TDQS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_TDQS    0x00000000UL
    /* CFG_TDQS                          [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_RTT_WR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RTT_WR    0x00000000UL
    /* CFG_RTT_WR                        [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_LP_ASR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_LP_ASR    0x00000000UL
    /* CFG_LP_ASR                        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AUTO_SR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_AUTO_SR    0x00000000UL
    /* CFG_AUTO_SR                       [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_SRT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_SRT    0x00000000UL
    /* CFG_SRT                           [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ADDR_MIRROR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ADDR_MIRROR    0x00000000UL
    /* CFG_ADDR_MIRROR                   [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQ_CAL_TYPE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQ_CAL_TYPE    0x00000001UL
    /* CFG_ZQ_CAL_TYPE                   [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQ_CAL_PER)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQ_CAL_PER    0x00027100UL
    /* CFG_ZQ_CAL_PER                    [0:32]  RW value= 0x27100 */
#endif
#if !defined (LIBERO_SETTING_CFG_AUTO_ZQ_CAL_EN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_AUTO_ZQ_CAL_EN    0x00000000UL
    /* CFG_AUTO_ZQ_CAL_EN                [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEMORY_TYPE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MEMORY_TYPE    0x00000400UL
    /* CFG_MEMORY_TYPE                   [0:32]  RW value= 0x400 */
#endif
#if !defined (LIBERO_SETTING_CFG_ONLY_SRANK_CMDS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ONLY_SRANK_CMDS    0x00000000UL
    /* CFG_ONLY_SRANK_CMDS               [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_NUM_RANKS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_NUM_RANKS    0x00000001UL
    /* CFG_NUM_RANKS                     [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_QUAD_RANK)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_QUAD_RANK    0x00000000UL
    /* CFG_QUAD_RANK                     [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_EARLY_RANK_TO_WR_START)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_EARLY_RANK_TO_WR_START    0x00000000UL
    /* CFG_EARLY_RANK_TO_WR_START        [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_EARLY_RANK_TO_RD_START)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_EARLY_RANK_TO_RD_START    0x00000000UL
    /* CFG_EARLY_RANK_TO_RD_START        [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_PASR_BANK)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_PASR_BANK    0x00000000UL
    /* CFG_PASR_BANK                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_PASR_SEG)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_PASR_SEG    0x00000000UL
    /* CFG_PASR_SEG                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_MRR_MODE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_MRR_MODE    0x00000000UL
    /* INIT_MRR_MODE                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_MR_W_REQ)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_MR_W_REQ    0x00000000UL
    /* INIT_MR_W_REQ                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_MR_ADDR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_MR_ADDR    0x00000000UL
    /* INIT_MR_ADDR                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_MR_WR_DATA)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_MR_WR_DATA    0x00000000UL
    /* INIT_MR_WR_DATA                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_MR_WR_MASK)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_MR_WR_MASK    0x00000000UL
    /* INIT_MR_WR_MASK                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_NOP)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_NOP    0x00000000UL
    /* INIT_NOP                          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_INIT_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_INIT_DURATION    0x00000640UL
    /* CFG_INIT_DURATION                 [0:32]  RW value= 0x640 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQINIT_CAL_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQINIT_CAL_DURATION    0x00000000UL
    /* CFG_ZQINIT_CAL_DURATION           [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQ_CAL_L_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQ_CAL_L_DURATION    0x00000000UL
    /* CFG_ZQ_CAL_L_DURATION             [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQ_CAL_S_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQ_CAL_S_DURATION    0x00000000UL
    /* CFG_ZQ_CAL_S_DURATION             [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQ_CAL_R_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQ_CAL_R_DURATION    0x00000028UL
    /* CFG_ZQ_CAL_R_DURATION             [0:32]  RW value= 0x28 */
#endif
#if !defined (LIBERO_SETTING_CFG_MRR)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MRR    0x00000008UL
    /* CFG_MRR                           [0:32]  RW value= 0x8 */
#endif
#if !defined (LIBERO_SETTING_CFG_MRW)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MRW    0x0000000AUL
    /* CFG_MRW                           [0:32]  RW value= 0xA */
#endif
#if !defined (LIBERO_SETTING_CFG_ODT_POWERDOWN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ODT_POWERDOWN    0x00000000UL
    /* CFG_ODT_POWERDOWN                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_WL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WL    0x00000008UL
    /* CFG_WL                            [0:32]  RW value= 0x8 */
#endif
#if !defined (LIBERO_SETTING_CFG_RL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RL    0x0000000EUL
    /* CFG_RL                            [0:32]  RW value= 0xE */
#endif
#if !defined (LIBERO_SETTING_CFG_CAL_READ_PERIOD)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CAL_READ_PERIOD    0x00000000UL
    /* CFG_CAL_READ_PERIOD               [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_NUM_CAL_READS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_NUM_CAL_READS    0x00000001UL
    /* CFG_NUM_CAL_READS                 [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_INIT_SELF_REFRESH)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_SELF_REFRESH    0x00000000UL
    /* INIT_SELF_REFRESH                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_POWER_DOWN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_POWER_DOWN    0x00000000UL
    /* INIT_POWER_DOWN                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_FORCE_WRITE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_FORCE_WRITE    0x00000000UL
    /* INIT_FORCE_WRITE                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_FORCE_WRITE_CS)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_FORCE_WRITE_CS    0x00000000UL
    /* INIT_FORCE_WRITE_CS               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_INIT_DISABLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_INIT_DISABLE    0x00000000UL
    /* CFG_CTRLR_INIT_DISABLE            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_INIT_RDIMM_COMPLETE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_RDIMM_COMPLETE    0x00000000UL
    /* INIT_RDIMM_COMPLETE               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_RDIMM_LAT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RDIMM_LAT    0x00000000UL
    /* CFG_RDIMM_LAT                     [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_RDIMM_BSIDE_INVERT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RDIMM_BSIDE_INVERT    0x00000001UL
    /* CFG_RDIMM_BSIDE_INVERT            [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_CFG_LRDIMM)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_LRDIMM    0x00000000UL
    /* CFG_LRDIMM                        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_MEMORY_RESET_MASK)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_MEMORY_RESET_MASK    0x00000000UL
    /* INIT_MEMORY_RESET_MASK            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_RD_PREAMB_TOGGLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RD_PREAMB_TOGGLE    0x00000000UL
    /* CFG_RD_PREAMB_TOGGLE              [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_RD_POSTAMBLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RD_POSTAMBLE    0x00000000UL
    /* CFG_RD_POSTAMBLE                  [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_PU_CAL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_PU_CAL    0x00000001UL
    /* CFG_PU_CAL                        [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_DQ_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DQ_ODT    0x00000002UL
    /* CFG_DQ_ODT                        [0:32]  RW value= 0x2 */
#endif
#if !defined (LIBERO_SETTING_CFG_CA_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CA_ODT    0x00000004UL
    /* CFG_CA_ODT                        [0:32]  RW value= 0x4 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQLATCH_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQLATCH_DURATION    0x00000018UL
    /* CFG_ZQLATCH_DURATION              [0:32]  RW value= 0x18 */
#endif
#if !defined (LIBERO_SETTING_INIT_CAL_SELECT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_CAL_SELECT    0x00000000UL
    /* INIT_CAL_SELECT                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_CAL_L_R_REQ)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_CAL_L_R_REQ    0x00000000UL
    /* INIT_CAL_L_R_REQ                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_CAL_L_B_SIZE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_CAL_L_B_SIZE    0x00000000UL
    /* INIT_CAL_L_B_SIZE                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_RWFIFO)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_RWFIFO    0x00000000UL
    /* INIT_RWFIFO                       [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_RD_DQCAL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_RD_DQCAL    0x00000000UL
    /* INIT_RD_DQCAL                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_START_DQSOSC)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_START_DQSOSC    0x00000000UL
    /* INIT_START_DQSOSC                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_STOP_DQSOSC)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_STOP_DQSOSC    0x00000000UL
    /* INIT_STOP_DQSOSC                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_ZQ_CAL_START)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_ZQ_CAL_START    0x00000000UL
    /* INIT_ZQ_CAL_START                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_WR_POSTAMBLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_WR_POSTAMBLE    0x00000000UL
    /* CFG_WR_POSTAMBLE                  [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_INIT_CAL_L_ADDR_0)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_CAL_L_ADDR_0    0x00000000UL
    /* INIT_CAL_L_ADDR_0                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_CAL_L_ADDR_1)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_CAL_L_ADDR_1    0x00000000UL
    /* INIT_CAL_L_ADDR_1                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLUPD_TRIG)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLUPD_TRIG    0x00000000UL
    /* CFG_CTRLUPD_TRIG                  [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLUPD_START_DELAY)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLUPD_START_DELAY    0x00000000UL
    /* CFG_CTRLUPD_START_DELAY           [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_T_CTRLUPD_MAX)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DFI_T_CTRLUPD_MAX    0x00000000UL
    /* CFG_DFI_T_CTRLUPD_MAX             [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_BUSY_SEL)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_BUSY_SEL    0x00000000UL
    /* CFG_CTRLR_BUSY_SEL                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_BUSY_VALUE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_BUSY_VALUE    0x00000000UL
    /* CFG_CTRLR_BUSY_VALUE              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_BUSY_TURN_OFF_DELAY)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_BUSY_TURN_OFF_DELAY    0x00000000UL
    /* CFG_CTRLR_BUSY_TURN_OFF_DELAY     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW    0x00000000UL
    /* CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_BUSY_RESTART_HOLDOFF)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_BUSY_RESTART_HOLDOFF    0x00000000UL
    /* CFG_CTRLR_BUSY_RESTART_HOLDOFF    [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_PARITY_RDIMM_DELAY)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_PARITY_RDIMM_DELAY    0x00000000UL
    /* CFG_PARITY_RDIMM_DELAY            [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_CTRLR_BUSY_ENABLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CTRLR_BUSY_ENABLE    0x00000000UL
    /* CFG_CTRLR_BUSY_ENABLE             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ASYNC_ODT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ASYNC_ODT    0x00000000UL
    /* CFG_ASYNC_ODT                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ZQ_CAL_DURATION)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_ZQ_CAL_DURATION    0x00000320UL
    /* CFG_ZQ_CAL_DURATION               [0:32]  RW value= 0x320 */
#endif
#if !defined (LIBERO_SETTING_CFG_MRRI)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MRRI    0x00000012UL
    /* CFG_MRRI                          [0:32]  RW value= 0x12 */
#endif
#if !defined (LIBERO_SETTING_INIT_ODT_FORCE_EN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_ODT_FORCE_EN    0x00000000UL
    /* INIT_ODT_FORCE_EN                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_ODT_FORCE_RANK)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_ODT_FORCE_RANK    0x00000000UL
    /* INIT_ODT_FORCE_RANK               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_PHYUPD_ACK_DELAY)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_PHYUPD_ACK_DELAY    0x00000000UL
    /* CFG_PHYUPD_ACK_DELAY              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MIRROR_X16_BG0_BG1)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_MIRROR_X16_BG0_BG1    0x00000000UL
    /* CFG_MIRROR_X16_BG0_BG1            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_PDA_MR_W_REQ)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_PDA_MR_W_REQ    0x00000000UL
    /* INIT_PDA_MR_W_REQ                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_PDA_NIBBLE_SELECT)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_INIT_PDA_NIBBLE_SELECT    0x00000000UL
    /* INIT_PDA_NIBBLE_SELECT            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH    0x00000000UL
    /* CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_CKSRE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CKSRE    0x00000008UL
    /* CFG_CKSRE                         [0:32]  RW value= 0x00000008 */
#endif
#if !defined (LIBERO_SETTING_CFG_CKSRX)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_CKSRX    0x0000000BUL
    /* CFG_CKSRX                         [0:32]  RW value= 0x0000000b */
#endif
#if !defined (LIBERO_SETTING_CFG_RCD_STAB)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_RCD_STAB    0x00000000UL
    /* CFG_RCD_STAB                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_T_CTRL_DELAY)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DFI_T_CTRL_DELAY    0x00000000UL
    /* CFG_DFI_T_CTRL_DELAY              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_T_DRAM_CLK_ENABLE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_DFI_T_DRAM_CLK_ENABLE    0x00000000UL
    /* CFG_DFI_T_DRAM_CLK_ENABLE         [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_IDLE_TIME_TO_SELF_REFRESH)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_IDLE_TIME_TO_SELF_REFRESH    0x00000000UL
    /* CFG_IDLE_TIME_TO_SELF_REFRESH     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_IDLE_TIME_TO_POWER_DOWN)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_IDLE_TIME_TO_POWER_DOWN    0x00000000UL
    /* CFG_IDLE_TIME_TO_POWER_DOWN       [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_BURST_RW_REFRESH_HOLDOFF)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_BURST_RW_REFRESH_HOLDOFF    0x00000000UL
    /* CFG_BURST_RW_REFRESH_HOLDOFF      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_BG_INTERLEAVE)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_BG_INTERLEAVE    0x00000001UL
    /* CFG_BG_INTERLEAVE                 [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_CFG_REFRESH_DURING_PHY_TRAINING)
/*IP Blk = MC_BASE2 Access=RW */
#define LIBERO_SETTING_CFG_REFRESH_DURING_PHY_TRAINING    0x00000000UL
    /* CFG_REFRESH_DURING_PHY_TRAINING        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P0)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P0    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P0             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P1)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P1    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P1             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P2)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P2    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P2             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P3)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P3    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P3             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P4)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P4    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P4             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P5)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P5    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P5             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P6)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P6    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P6             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_STARVE_TIMEOUT_P7)
/*IP Blk = MPFE Access=RW */
#define LIBERO_SETTING_CFG_STARVE_TIMEOUT_P7    0x00000000UL
    /* CFG_STARVE_TIMEOUT_P7             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_REORDER_EN)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_REORDER_EN    0x00000001UL
    /* CFG_REORDER_EN                    [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_CFG_REORDER_QUEUE_EN)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_REORDER_QUEUE_EN    0x00000001UL
    /* CFG_REORDER_QUEUE_EN              [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_CFG_INTRAPORT_REORDER_EN)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_INTRAPORT_REORDER_EN    0x00000000UL
    /* CFG_INTRAPORT_REORDER_EN          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MAINTAIN_COHERENCY)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_MAINTAIN_COHERENCY    0x00000001UL
    /* CFG_MAINTAIN_COHERENCY            [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_CFG_Q_AGE_LIMIT)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_Q_AGE_LIMIT    0x000000FFUL
    /* CFG_Q_AGE_LIMIT                   [0:32]  RW value= 0x000000FF */
#endif
#if !defined (LIBERO_SETTING_CFG_RO_CLOSED_PAGE_POLICY)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_RO_CLOSED_PAGE_POLICY    0x00000000UL
    /* CFG_RO_CLOSED_PAGE_POLICY         [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_REORDER_RW_ONLY)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_REORDER_RW_ONLY    0x00000000UL
    /* CFG_REORDER_RW_ONLY               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_RO_PRIORITY_EN)
/*IP Blk = REORDER Access=RW */
#define LIBERO_SETTING_CFG_RO_PRIORITY_EN    0x00000000UL
    /* CFG_RO_PRIORITY_EN                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DM_EN)
/*IP Blk = RMW Access=RW */
#define LIBERO_SETTING_CFG_DM_EN    0x00000001UL
    /* CFG_DM_EN                         [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_RMW_EN)
/*IP Blk = RMW Access=RW */
#define LIBERO_SETTING_CFG_RMW_EN    0x00000000UL
    /* CFG_RMW_EN                        [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ECC_CORRECTION_EN)
/*IP Blk = ECC Access=RW */
#define LIBERO_SETTING_CFG_ECC_CORRECTION_EN    0x00000000UL
    /* CFG_ECC_CORRECTION_EN             [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ECC_BYPASS)
/*IP Blk = ECC Access=RW */
#define LIBERO_SETTING_CFG_ECC_BYPASS    0x00000000UL
    /* CFG_ECC_BYPASS                    [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_WRITE_DATA_1B_ECC_ERROR_GEN)
/*IP Blk = ECC Access=RW */
#define LIBERO_SETTING_INIT_WRITE_DATA_1B_ECC_ERROR_GEN    0x00000000UL
    /* INIT_WRITE_DATA_1B_ECC_ERROR_GEN        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_WRITE_DATA_2B_ECC_ERROR_GEN)
/*IP Blk = ECC Access=RW */
#define LIBERO_SETTING_INIT_WRITE_DATA_2B_ECC_ERROR_GEN    0x00000000UL
    /* INIT_WRITE_DATA_2B_ECC_ERROR_GEN        [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ECC_1BIT_INT_THRESH)
/*IP Blk = ECC Access=RW */
#define LIBERO_SETTING_CFG_ECC_1BIT_INT_THRESH    0x00000000UL
    /* CFG_ECC_1BIT_INT_THRESH           [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_READ_CAPTURE_ADDR)
/*IP Blk = READ_CAPT Access=RW */
#define LIBERO_SETTING_INIT_READ_CAPTURE_ADDR    0x00000000UL
    /* INIT_READ_CAPTURE_ADDR            [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ERROR_GROUP_SEL)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_ERROR_GROUP_SEL    0x00000000UL
    /* CFG_ERROR_GROUP_SEL               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DATA_SEL)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_DATA_SEL    0x00000000UL
    /* CFG_DATA_SEL                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_MODE)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_MODE    0x00000000UL
    /* CFG_TRIG_MODE                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_POST_TRIG_CYCS)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_POST_TRIG_CYCS    0x00000000UL
    /* CFG_POST_TRIG_CYCS                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_MASK)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_MASK    0x00000000UL
    /* CFG_TRIG_MASK                     [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_EN_MASK)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_EN_MASK    0x00000000UL
    /* CFG_EN_MASK                       [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_MTC_ACQ_ADDR)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_MTC_ACQ_ADDR    0x00000000UL
    /* MTC_ACQ_ADDR                      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_MT_ADDR_0)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_MT_ADDR_0    0x00000000UL
    /* CFG_TRIG_MT_ADDR_0                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_MT_ADDR_1)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_MT_ADDR_1    0x00000000UL
    /* CFG_TRIG_MT_ADDR_1                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_ERR_MASK_0)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_ERR_MASK_0    0x00000000UL
    /* CFG_TRIG_ERR_MASK_0               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_ERR_MASK_1)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_ERR_MASK_1    0x00000000UL
    /* CFG_TRIG_ERR_MASK_1               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_ERR_MASK_2)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_ERR_MASK_2    0x00000000UL
    /* CFG_TRIG_ERR_MASK_2               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_ERR_MASK_3)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_ERR_MASK_3    0x00000000UL
    /* CFG_TRIG_ERR_MASK_3               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_TRIG_ERR_MASK_4)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_TRIG_ERR_MASK_4    0x00000000UL
    /* CFG_TRIG_ERR_MASK_4               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_MTC_ACQ_WR_DATA_0)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_MTC_ACQ_WR_DATA_0    0x00000000UL
    /* MTC_ACQ_WR_DATA_0                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_MTC_ACQ_WR_DATA_1)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_MTC_ACQ_WR_DATA_1    0x00000000UL
    /* MTC_ACQ_WR_DATA_1                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_MTC_ACQ_WR_DATA_2)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_MTC_ACQ_WR_DATA_2    0x00000000UL
    /* MTC_ACQ_WR_DATA_2                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_PRE_TRIG_CYCS)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_PRE_TRIG_CYCS    0x00000000UL
    /* CFG_PRE_TRIG_CYCS                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DATA_SEL_FIRST_ERROR)
/*IP Blk = MTA Access=RW */
#define LIBERO_SETTING_CFG_DATA_SEL_FIRST_ERROR    0x00000000UL
    /* CFG_DATA_SEL_FIRST_ERROR          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DQ_WIDTH)
/*IP Blk = DYN_WIDTH_ADJ Access=RW */
#define LIBERO_SETTING_CFG_DQ_WIDTH    0x00000000UL
    /* CFG_DQ_WIDTH                      [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_ACTIVE_DQ_SEL)
/*IP Blk = DYN_WIDTH_ADJ Access=RW */
#define LIBERO_SETTING_CFG_ACTIVE_DQ_SEL    0x00000000UL
    /* CFG_ACTIVE_DQ_SEL                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_CA_PARITY_ERROR_GEN_REQ)
/*IP Blk = CA_PAR_ERR Access=RW */
#define LIBERO_SETTING_INIT_CA_PARITY_ERROR_GEN_REQ    0x00000000UL
    /* INIT_CA_PARITY_ERROR_GEN_REQ      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_CA_PARITY_ERROR_GEN_CMD)
/*IP Blk = CA_PAR_ERR Access=RW */
#define LIBERO_SETTING_INIT_CA_PARITY_ERROR_GEN_CMD    0x00000000UL
    /* INIT_CA_PARITY_ERROR_GEN_CMD      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_T_RDDATA_EN)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_T_RDDATA_EN    0x00000015UL
    /* CFG_DFI_T_RDDATA_EN               [0:32]  RW value= 0x15 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_T_PHY_RDLAT)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_T_PHY_RDLAT    0x00000006UL
    /* CFG_DFI_T_PHY_RDLAT               [0:32]  RW value= 0x6 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_T_PHY_WRLAT)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_T_PHY_WRLAT    0x00000003UL
    /* CFG_DFI_T_PHY_WRLAT               [0:32]  RW value= 0x3 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_PHYUPD_EN)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_PHYUPD_EN    0x00000001UL
    /* CFG_DFI_PHYUPD_EN                 [0:32]  RW value= 0x00000001 */
#endif
#if !defined (LIBERO_SETTING_INIT_DFI_LP_DATA_REQ)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_INIT_DFI_LP_DATA_REQ    0x00000000UL
    /* INIT_DFI_LP_DATA_REQ              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_DFI_LP_CTRL_REQ)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_INIT_DFI_LP_CTRL_REQ    0x00000000UL
    /* INIT_DFI_LP_CTRL_REQ              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_DFI_LP_WAKEUP)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_INIT_DFI_LP_WAKEUP    0x00000000UL
    /* INIT_DFI_LP_WAKEUP                [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_INIT_DFI_DRAM_CLK_DISABLE)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_INIT_DFI_DRAM_CLK_DISABLE    0x00000000UL
    /* INIT_DFI_DRAM_CLK_DISABLE         [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_DATA_BYTE_DISABLE)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_DATA_BYTE_DISABLE    0x00000000UL
    /* CFG_DFI_DATA_BYTE_DISABLE         [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_LVL_SEL)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_LVL_SEL    0x00000000UL
    /* CFG_DFI_LVL_SEL                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_LVL_PERIODIC)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_LVL_PERIODIC    0x00000000UL
    /* CFG_DFI_LVL_PERIODIC              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_DFI_LVL_PATTERN)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_CFG_DFI_LVL_PATTERN    0x00000000UL
    /* CFG_DFI_LVL_PATTERN               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_DFI_INIT_START)
/*IP Blk = DFI Access=RW */
#define LIBERO_SETTING_PHY_DFI_INIT_START    0x00000001UL
    /* PHY_DFI_INIT_START                [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI1_0)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI1_0    0x00000000UL
    /* CFG_AXI_START_ADDRESS_AXI1_0      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI1_1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI1_1    0x00000000UL
    /* CFG_AXI_START_ADDRESS_AXI1_1      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI2_0)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI2_0    0x00000000UL
    /* CFG_AXI_START_ADDRESS_AXI2_0      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI2_1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI2_1    0x00000000UL
    /* CFG_AXI_START_ADDRESS_AXI2_1      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI1_0)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI1_0    0x7FFFFFFFUL
    /* CFG_AXI_END_ADDRESS_AXI1_0        [0:32]  RW value= 0x7FFFFFFF */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI1_1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI1_1    0x00000000UL
    /* CFG_AXI_END_ADDRESS_AXI1_1        [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI2_0)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI2_0    0x7FFFFFFFUL
    /* CFG_AXI_END_ADDRESS_AXI2_0        [0:32]  RW value= 0x7FFFFFFF */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI2_1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI2_1    0x00000000UL
    /* CFG_AXI_END_ADDRESS_AXI2_1        [0:32]  RW value= 0x0 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI1_0)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI1_0    0x00000000UL
    /* CFG_MEM_START_ADDRESS_AXI1_0      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI1_1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI1_1    0x00000000UL
    /* CFG_MEM_START_ADDRESS_AXI1_1      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI2_0)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI2_0    0x00000000UL
    /* CFG_MEM_START_ADDRESS_AXI2_0      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI2_1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI2_1    0x00000000UL
    /* CFG_MEM_START_ADDRESS_AXI2_1      [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ENABLE_BUS_HOLD_AXI1)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_ENABLE_BUS_HOLD_AXI1    0x00000000UL
    /* CFG_ENABLE_BUS_HOLD_AXI1          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_ENABLE_BUS_HOLD_AXI2)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_ENABLE_BUS_HOLD_AXI2    0x00000000UL
    /* CFG_ENABLE_BUS_HOLD_AXI2          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_CFG_AXI_AUTO_PCH)
/*IP Blk = AXI_IF Access=RW */
#define LIBERO_SETTING_CFG_AXI_AUTO_PCH    0x00000000UL
    /* CFG_AXI_AUTO_PCH                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_RESET_CONTROL)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_RESET_CONTROL    0x00008001UL
    /* PHY_RESET_CONTROL                 [0:32]  RW value= 0x8001 */
#endif
#if !defined (LIBERO_SETTING_PHY_PC_RANK)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_PC_RANK    0x00000001UL
    /* PHY_PC_RANK                       [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_PHY_RANKS_TO_TRAIN)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_RANKS_TO_TRAIN    0x00000001UL
    /* PHY_RANKS_TO_TRAIN                [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_PHY_WRITE_REQUEST)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_WRITE_REQUEST    0x00000000UL
    /* PHY_WRITE_REQUEST                 [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_READ_REQUEST)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_READ_REQUEST    0x00000000UL
    /* PHY_READ_REQUEST                  [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_WRITE_LEVEL_DELAY)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_WRITE_LEVEL_DELAY    0x00000000UL
    /* PHY_WRITE_LEVEL_DELAY             [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_GATE_TRAIN_DELAY)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_GATE_TRAIN_DELAY    0x0000003FUL
    /* PHY_GATE_TRAIN_DELAY              [0:32]  RW value= 0x3F */
#endif
#if !defined (LIBERO_SETTING_PHY_EYE_TRAIN_DELAY)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_EYE_TRAIN_DELAY    0x0000003FUL
    /* PHY_EYE_TRAIN_DELAY               [0:32]  RW value= 0x3F */
#endif
#if !defined (LIBERO_SETTING_PHY_EYE_PAT)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_EYE_PAT    0x00000000UL
    /* PHY_EYE_PAT                       [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_START_RECAL)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_START_RECAL    0x00000000UL
    /* PHY_START_RECAL                   [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_CLR_DFI_LVL_PERIODIC)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_CLR_DFI_LVL_PERIODIC    0x00000000UL
    /* PHY_CLR_DFI_LVL_PERIODIC          [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_TRAIN_STEP_ENABLE)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_TRAIN_STEP_ENABLE    0x00000018UL
    /* PHY_TRAIN_STEP_ENABLE             [0:32]  RW value= 0x18 */
#endif
#if !defined (LIBERO_SETTING_PHY_LPDDR_DQ_CAL_PAT)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_LPDDR_DQ_CAL_PAT    0x00000000UL
    /* PHY_LPDDR_DQ_CAL_PAT              [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_INDPNDT_TRAINING)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_INDPNDT_TRAINING    0x00000001UL
    /* PHY_INDPNDT_TRAINING              [0:32]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_PHY_ENCODED_QUAD_CS)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_ENCODED_QUAD_CS    0x00000000UL
    /* PHY_ENCODED_QUAD_CS               [0:32]  RW value= 0x00000000 */
#endif
#if !defined (LIBERO_SETTING_PHY_HALF_CLK_DLY_ENABLE)
/*IP Blk = csr_custom Access=RW */
#define LIBERO_SETTING_PHY_HALF_CLK_DLY_ENABLE    0x00000000UL
    /* PHY_HALF_CLK_DLY_ENABLE           [0:32]  RW value= 0x00000000 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_DDRC_H_ */

