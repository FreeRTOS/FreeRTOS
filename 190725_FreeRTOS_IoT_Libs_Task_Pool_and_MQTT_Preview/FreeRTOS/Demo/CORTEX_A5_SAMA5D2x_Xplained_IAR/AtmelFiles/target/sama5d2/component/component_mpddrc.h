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

#ifndef _SAMA5D2_MPDDRC_COMPONENT_
#define _SAMA5D2_MPDDRC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR AHB Multi-port DDR-SDRAM Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_MPDDRC AHB Multi-port DDR-SDRAM Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Mpddrc hardware registers */
typedef struct {
  __IO uint32_t MPDDRC_MR;              /**< \brief (Mpddrc Offset: 0x00) MPDDRC Mode Register */
  __IO uint32_t MPDDRC_RTR;             /**< \brief (Mpddrc Offset: 0x04) MPDDRC Refresh Timer Register */
  __IO uint32_t MPDDRC_CR;              /**< \brief (Mpddrc Offset: 0x08) MPDDRC Configuration Register */
  __IO uint32_t MPDDRC_TPR0;            /**< \brief (Mpddrc Offset: 0x0C) MPDDRC Timing Parameter 0 Register */
  __IO uint32_t MPDDRC_TPR1;            /**< \brief (Mpddrc Offset: 0x10) MPDDRC Timing Parameter 1 Register */
  __IO uint32_t MPDDRC_TPR2;            /**< \brief (Mpddrc Offset: 0x14) MPDDRC Timing Parameter 2 Register */
  __I  uint32_t Reserved1[1];
  __IO uint32_t MPDDRC_LPR;             /**< \brief (Mpddrc Offset: 0x1C) MPDDRC Low-power Register */
  __IO uint32_t MPDDRC_MD;              /**< \brief (Mpddrc Offset: 0x20) MPDDRC Memory Device Register */
  __I  uint32_t Reserved2[1];
  __IO uint32_t MPDDRC_LPDDR23_LPR;     /**< \brief (Mpddrc Offset: 0x28) MPDDRC LPDDR2-LPDDR3 Low-power Register */
  __IO uint32_t MPDDRC_LPDDR23_CAL_MR4; /**< \brief (Mpddrc Offset: 0x2C) MPDDRC LPDDR2-LPDDR3 Calibration and MR4 Register */
  __IO uint32_t MPDDRC_LPDDR23_TIM_CAL; /**< \brief (Mpddrc Offset: 0x30) MPDDRC LPDDR2-LPDDR3 Timing Calibration Register */
  __IO uint32_t MPDDRC_IO_CALIBR;       /**< \brief (Mpddrc Offset: 0x34) MPDDRC IO Calibration */
  __IO uint32_t MPDDRC_OCMS;            /**< \brief (Mpddrc Offset: 0x38) MPDDRC OCMS Register */
  __O  uint32_t MPDDRC_OCMS_KEY1;       /**< \brief (Mpddrc Offset: 0x3C) MPDDRC OCMS KEY1 Register */
  __O  uint32_t MPDDRC_OCMS_KEY2;       /**< \brief (Mpddrc Offset: 0x40) MPDDRC OCMS KEY2 Register */
  __IO uint32_t MPDDRC_CONF_ARBITER;    /**< \brief (Mpddrc Offset: 0x44) MPDDRC Configuration Arbiter Register */
  __IO uint32_t MPDDRC_TIMEOUT;         /**< \brief (Mpddrc Offset: 0x48) MPDDRC Time-out Port 0/1/2/3 Register */
  __IO uint32_t MPDDRC_REQ_PORT_0123;   /**< \brief (Mpddrc Offset: 0x4C) MPDDRC Request Port 0/1/2/3 Register */
  __IO uint32_t MPDDRC_REQ_PORT_4567;   /**< \brief (Mpddrc Offset: 0x50) MPDDRC Request Port 4/5/6/7 Register */
  __I  uint32_t MPDDRC_BDW_PORT_0123;   /**< \brief (Mpddrc Offset: 0x54) MPDDRC Bandwidth Port 0/1/2/3 Register */
  __I  uint32_t MPDDRC_BDW_PORT_4567;   /**< \brief (Mpddrc Offset: 0x58) MPDDRC Bandwidth Port 4/5/6/7 Register */
  __IO uint32_t MPDDRC_RD_DATA_PATH;    /**< \brief (Mpddrc Offset: 0x5C) MPDDRC Read Datapath Register */
  __IO uint32_t MPDDRC_MCFGR;           /**< \brief (Mpddrc Offset: 0x60) MPDDRC Monitor Configuration */
  __IO uint32_t MPDDRC_MADDR0;          /**< \brief (Mpddrc Offset: 0x64) MPDDRC Monitor Address High/Low port 0 */
  __IO uint32_t MPDDRC_MADDR1;          /**< \brief (Mpddrc Offset: 0x68) MPDDRC Monitor Address High/Low port 1 */
  __IO uint32_t MPDDRC_MADDR2;          /**< \brief (Mpddrc Offset: 0x6C) MPDDRC Monitor Address High/Low port 2 */
  __IO uint32_t MPDDRC_MADDR3;          /**< \brief (Mpddrc Offset: 0x70) MPDDRC Monitor Address High/Low port 3 */
  __IO uint32_t MPDDRC_MADDR4;          /**< \brief (Mpddrc Offset: 0x74) MPDDRC Monitor Address High/Low port 4 */
  __IO uint32_t MPDDRC_MADDR5;          /**< \brief (Mpddrc Offset: 0x78) MPDDRC Monitor Address High/Low port 5 */
  __IO uint32_t MPDDRC_MADDR6;          /**< \brief (Mpddrc Offset: 0x7C) MPDDRC Monitor Address High/Low port 6 */
  __IO uint32_t MPDDRC_MADDR7;          /**< \brief (Mpddrc Offset: 0x80) MPDDRC Monitor Address High/Low port 7 */
  __I  uint32_t MPDDRC_MINFO0;          /**< \brief (Mpddrc Offset: 0x84) MPDDRC Monitor Information port 0 */
  __I  uint32_t MPDDRC_MINFO1;          /**< \brief (Mpddrc Offset: 0x88) MPDDRC Monitor Information port 1 */
  __I  uint32_t MPDDRC_MINFO2;          /**< \brief (Mpddrc Offset: 0x8C) MPDDRC Monitor Information port 2 */
  __I  uint32_t MPDDRC_MINFO3;          /**< \brief (Mpddrc Offset: 0x90) MPDDRC Monitor Information port 3 */
  __I  uint32_t MPDDRC_MINFO4;          /**< \brief (Mpddrc Offset: 0x94) MPDDRC Monitor Information port 4 */
  __I  uint32_t MPDDRC_MINFO5;          /**< \brief (Mpddrc Offset: 0x98) MPDDRC Monitor Information port 5 */
  __I  uint32_t MPDDRC_MINFO6;          /**< \brief (Mpddrc Offset: 0x9C) MPDDRC Monitor Information port 6 */
  __I  uint32_t MPDDRC_MINFO7;          /**< \brief (Mpddrc Offset: 0xA0) MPDDRC Monitor Information port 7 */
  __I  uint32_t Reserved3[16];
  __IO uint32_t MPDDRC_WPMR;            /**< \brief (Mpddrc Offset: 0xE4) MPDDRC Write Protection Mode Register */
  __I  uint32_t MPDDRC_WPSR;            /**< \brief (Mpddrc Offset: 0xE8) MPDDRC Write Protection Status Register */
  __I  uint32_t Reserved4[4];
  __I  uint32_t MPDDRC_VERSION;         /**< \brief (Mpddrc Offset: 0xFC) MPDDRC Version Register */
  __IO uint32_t MPDDRC_DLL_OS;          /**< \brief (Mpddrc Offset: 0x100) MPDDRC DLL Offset Selection Register */
  __IO uint32_t MPDDRC_DLL_MAO;         /**< \brief (Mpddrc Offset: 0x104) MPDDRC DLL MASTER Offset Register */
  __IO uint32_t MPDDRC_DLL_SO0;         /**< \brief (Mpddrc Offset: 0x108) MPDDRC DLL SLAVE Offset 0 Register */
  __IO uint32_t MPDDRC_DLL_SO1;         /**< \brief (Mpddrc Offset: 0x10C) MPDDRC DLL SLAVE Offset 1 Register */
  __IO uint32_t MPDDRC_DLL_WRO;         /**< \brief (Mpddrc Offset: 0x110) MPDDRC DLL CLKWR Offset Register */
  __IO uint32_t MPDDRC_DLL_ADO;         /**< \brief (Mpddrc Offset: 0x114) MPDDRC DLL CLKAD Offset Register */
  __I  uint32_t MPDDRC_DLL_SM[4];       /**< \brief (Mpddrc Offset: 0x118) MPDDRC DLL Status MASTER0 Register */
  __I  uint32_t MPDDRC_DLL_SSL[8];      /**< \brief (Mpddrc Offset: 0x128) MPDDRC DLL Status SLAVE0 Register */
  __I  uint32_t MPDDRC_DLL_SWR[4];      /**< \brief (Mpddrc Offset: 0x148) MPDDRC DLL Status CLKWR0 Register */
  __I  uint32_t MPDDRC_DLL_SAD;         /**< \brief (Mpddrc Offset: 0x158) MPDDRC DLL Status CLKAD Register */
} Mpddrc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- MPDDRC_MR : (MPDDRC Offset: 0x00) MPDDRC Mode Register -------- */
#define MPDDRC_MR_MODE_Pos 0
#define MPDDRC_MR_MODE_Msk (0x7u << MPDDRC_MR_MODE_Pos) /**< \brief (MPDDRC_MR) MPDDRC Command Mode */
#define MPDDRC_MR_MODE(value) ((MPDDRC_MR_MODE_Msk & ((value) << MPDDRC_MR_MODE_Pos)))
#define   MPDDRC_MR_MODE_NORMAL_CMD (0x0u << 0) /**< \brief (MPDDRC_MR) Normal Mode. Any access to the MPDDRC is decoded normally. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_NOP_CMD (0x1u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues a NOP command when the DDR-SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_PRCGALL_CMD (0x2u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues the All Banks Precharge command when the DDR-SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the SDRAM. */
#define   MPDDRC_MR_MODE_LMR_CMD (0x3u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues a Load Mode Register command when the DDR-SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_RFSH_CMD (0x4u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an Auto-Refresh command when the DDR-SDRAM device is accessed regardless of the cycle. Previously, an All Banks Precharge command must be issued. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_EXT_LMR_CMD (0x5u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an Extended Load Mode Register command when the SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the DDR-SDRAM. The write in the DDR-SDRAM must be done in the appropriate bank. */
#define   MPDDRC_MR_MODE_DEEP_CALIB_MD (0x6u << 0) /**< \brief (MPDDRC_MR) Deep Power mode: Access to Deep Power-down modeCalibration command: to calibrate RTT and RON values for the Process Voltage Temperature (PVT) (DDR3-SDRAM device) */
#define   MPDDRC_MR_MODE_LPDDR2_LPDDR3_CMD (0x7u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an LPDDR2/LPDDR3 Mode Register command when the device is accessed regardless of the cycle. To activate this mode, the Mode Register command must be followed by a write to the low-power DDR2-SDRAM or to the low-power DDR3-SDRAM. */
#define MPDDRC_MR_DAI (0x1u << 4) /**< \brief (MPDDRC_MR) Device Auto-Initialization Status */
#define   MPDDRC_MR_DAI_DAI_COMPLETE (0x0u << 4) /**< \brief (MPDDRC_MR) DAI complete */
#define   MPDDRC_MR_DAI_DAI_IN_PROGESSS (0x1u << 4) /**< \brief (MPDDRC_MR) DAI still in progress */
#define MPDDRC_MR_MRS_Pos 8
#define MPDDRC_MR_MRS_Msk (0xffu << MPDDRC_MR_MRS_Pos) /**< \brief (MPDDRC_MR) Mode Register Select LPDDR2/LPDDR3 */
#define MPDDRC_MR_MRS(value) ((MPDDRC_MR_MRS_Msk & ((value) << MPDDRC_MR_MRS_Pos)))
/* -------- MPDDRC_RTR : (MPDDRC Offset: 0x04) MPDDRC Refresh Timer Register -------- */
#define MPDDRC_RTR_COUNT_Pos 0
#define MPDDRC_RTR_COUNT_Msk (0xfffu << MPDDRC_RTR_COUNT_Pos) /**< \brief (MPDDRC_RTR) MPDDRC Refresh Timer Count */
#define MPDDRC_RTR_COUNT(value) ((MPDDRC_RTR_COUNT_Msk & ((value) << MPDDRC_RTR_COUNT_Pos)))
#define MPDDRC_RTR_ADJ_REF (0x1u << 16) /**< \brief (MPDDRC_RTR) Adjust Refresh Rate */
#define MPDDRC_RTR_REF_PB (0x1u << 17) /**< \brief (MPDDRC_RTR) Refresh Per Bank */
#define MPDDRC_RTR_MR4_VALUE_Pos 20
#define MPDDRC_RTR_MR4_VALUE_Msk (0x7u << MPDDRC_RTR_MR4_VALUE_Pos) /**< \brief (MPDDRC_RTR) Content of MR4 Register */
#define MPDDRC_RTR_MR4_VALUE(value) ((MPDDRC_RTR_MR4_VALUE_Msk & ((value) << MPDDRC_RTR_MR4_VALUE_Pos)))
/* -------- MPDDRC_CR : (MPDDRC Offset: 0x08) MPDDRC Configuration Register -------- */
#define MPDDRC_CR_NC_Pos 0
#define MPDDRC_CR_NC_Msk (0x3u << MPDDRC_CR_NC_Pos) /**< \brief (MPDDRC_CR) Number of Column Bits */
#define MPDDRC_CR_NC(value) ((MPDDRC_CR_NC_Msk & ((value) << MPDDRC_CR_NC_Pos)))
#define   MPDDRC_CR_NC_DDR9_MDDR8_COL_BITS (0x0u << 0) /**< \brief (MPDDRC_CR) 9 bits for DDR, 8-bit for low-power DDR1-SDRAM */
#define   MPDDRC_CR_NC_10_COL_BITS (0x1u << 0) /**< \brief (MPDDRC_CR) 10 bits for DDR, 9-bit for low-power DDR1-SDRAM */
#define   MPDDRC_CR_NC_DDR11_MDDR10_COL_BITS (0x2u << 0) /**< \brief (MPDDRC_CR) 11 bits for DDR, 10-bit for low-power DDR1-SDRAM */
#define   MPDDRC_CR_NC_DDR12_MDDR11_COL_BITS (0x3u << 0) /**< \brief (MPDDRC_CR) 12 bits for DDR, 11-bit for low-power DDR1-SDRAM */
#define MPDDRC_CR_NR_Pos 2
#define MPDDRC_CR_NR_Msk (0x3u << MPDDRC_CR_NR_Pos) /**< \brief (MPDDRC_CR) Number of Row Bits */
#define MPDDRC_CR_NR(value) ((MPDDRC_CR_NR_Msk & ((value) << MPDDRC_CR_NR_Pos)))
#define   MPDDRC_CR_NR_11_ROW_BITS (0x0u << 2) /**< \brief (MPDDRC_CR) 11 bits to define the row number, up to 2048 rows */
#define   MPDDRC_CR_NR_12_ROW_BITS (0x1u << 2) /**< \brief (MPDDRC_CR) 12 bits to define the row number, up to 4096 rows */
#define   MPDDRC_CR_NR_13_ROW_BITS (0x2u << 2) /**< \brief (MPDDRC_CR) 13 bits to define the row number, up to 8192 rows */
#define   MPDDRC_CR_NR_14_ROW_BITS (0x3u << 2) /**< \brief (MPDDRC_CR) 14 bits to define the row number, up to 16384 rows */
#define MPDDRC_CR_CAS_Pos 4
#define MPDDRC_CR_CAS_Msk (0x7u << MPDDRC_CR_CAS_Pos) /**< \brief (MPDDRC_CR) CAS Latency */
#define MPDDRC_CR_CAS(value) ((MPDDRC_CR_CAS_Msk & ((value) << MPDDRC_CR_CAS_Pos)))
#define   MPDDRC_CR_CAS_DDR_CAS2 (0x2u << 4) /**< \brief (MPDDRC_CR) LPDDR1 CAS Latency 2 */
#define   MPDDRC_CR_CAS_DDR_CAS3 (0x3u << 4) /**< \brief (MPDDRC_CR) LPDDR3/DDR2/LPDDR2/LPDDR1 CAS Latency 3 */
#define   MPDDRC_CR_CAS_DDR_CAS5 (0x5u << 4) /**< \brief (MPDDRC_CR) DDR3 CAS Latency 5 */
#define   MPDDRC_CR_CAS_DDR_CAS6 (0x6u << 4) /**< \brief (MPDDRC_CR) DDR3LPDDR3 CAS Latency 6 */
#define MPDDRC_CR_DLL (0x1u << 7) /**< \brief (MPDDRC_CR) Reset DLL */
#define   MPDDRC_CR_DLL_RESET_DISABLED (0x0u << 7) /**< \brief (MPDDRC_CR) Disable DLL reset */
#define   MPDDRC_CR_DLL_RESET_ENABLED (0x1u << 7) /**< \brief (MPDDRC_CR) Enable DLL reset */
#define MPDDRC_CR_DIC_DS (0x1u << 8) /**< \brief (MPDDRC_CR) Output Driver Impedance Control (Drive Strength) */
#define   MPDDRC_CR_DIC_DS_DDR2_NORMALSTRENGTH_DDR3_RZQ6 (0x0u << 8) /**< \brief (MPDDRC_CR) Normal driver strength (DDR2) - RZQ/6 (40 [NOM], DDR3) */
#define   MPDDRC_CR_DIC_DS_DDR2_WEAKSTRENGTH_DDR3_RZQ7 (0x1u << 8) /**< \brief (MPDDRC_CR) Weak driver strength (DDR2) - RZQ/7 (34 [NOM], DDR3) */
#define MPDDRC_CR_DIS_DLL (0x1u << 9) /**< \brief (MPDDRC_CR) DISABLE DLL */
#define MPDDRC_CR_ZQ_Pos 10
#define MPDDRC_CR_ZQ_Msk (0x3u << MPDDRC_CR_ZQ_Pos) /**< \brief (MPDDRC_CR) ZQ Calibration */
#define MPDDRC_CR_ZQ(value) ((MPDDRC_CR_ZQ_Msk & ((value) << MPDDRC_CR_ZQ_Pos)))
#define   MPDDRC_CR_ZQ_INIT (0x0u << 10) /**< \brief (MPDDRC_CR) Calibration command after initialization */
#define   MPDDRC_CR_ZQ_LONG (0x1u << 10) /**< \brief (MPDDRC_CR) Long calibration */
#define   MPDDRC_CR_ZQ_SHORT (0x2u << 10) /**< \brief (MPDDRC_CR) Short calibration */
#define   MPDDRC_CR_ZQ_RESET (0x3u << 10) /**< \brief (MPDDRC_CR) ZQ Reset */
#define MPDDRC_CR_OCD_Pos 12
#define MPDDRC_CR_OCD_Msk (0x7u << MPDDRC_CR_OCD_Pos) /**< \brief (MPDDRC_CR) Off-chip Driver */
#define MPDDRC_CR_OCD(value) ((MPDDRC_CR_OCD_Msk & ((value) << MPDDRC_CR_OCD_Pos)))
#define   MPDDRC_CR_OCD_DDR2_EXITCALIB (0x0u << 12) /**< \brief (MPDDRC_CR) Exit from OCD Calibration mode and maintain settings */
#define   MPDDRC_CR_OCD_DDR2_DEFAULT_CALIB (0x7u << 12) /**< \brief (MPDDRC_CR) OCD calibration default */
#define MPDDRC_CR_DQMS (0x1u << 16) /**< \brief (MPDDRC_CR) Mask Data is Shared */
#define   MPDDRC_CR_DQMS_NOT_SHARED (0x0u << 16) /**< \brief (MPDDRC_CR) DQM is not shared with another controller */
#define   MPDDRC_CR_DQMS_SHARED (0x1u << 16) /**< \brief (MPDDRC_CR) DQM is shared with another controller */
#define MPDDRC_CR_ENRDM (0x1u << 17) /**< \brief (MPDDRC_CR) Enable Read Measure */
#define   MPDDRC_CR_ENRDM_OFF (0x0u << 17) /**< \brief (MPDDRC_CR) DQS/DDR_DATA phase error correction is disabled */
#define   MPDDRC_CR_ENRDM_ON (0x1u << 17) /**< \brief (MPDDRC_CR) DQS/DDR_DATA phase error correction is enabled */
#define MPDDRC_CR_LC_LPDDR1 (0x1u << 19) /**< \brief (MPDDRC_CR) Low-cost Low-power DDR1 */
#define   MPDDRC_CR_LC_LPDDR1_NOT_2_BANKS (0x0u << 19) /**< \brief (MPDDRC_CR) Any type of memory devices except of low cost, low density Low Power DDR1. */
#define   MPDDRC_CR_LC_LPDDR1_2_BANKS_LPDDR1 (0x1u << 19) /**< \brief (MPDDRC_CR) Low-cost and low-density low-power DDR1. These devices have a density of 32 Mbits and are organized as two internal banks. To use this feature, the user has to define the type of memory and the data bus width (see Section 8.8 "MPDDRC Memory Device Register").The 16-bit memory device is organized as 2 banks, 9 columns and 11 rows.The 32-bit memory device is organized as 2 banks, 8 columns and 11 rows.It is impossible to use two 16-bit memory devices (2 x 32 Mbits) for creating one 32-bit memory device (64 Mbits). In this case, it is recommended to use one 32-bit memory device which embeds four internal banks. */
#define MPDDRC_CR_NB (0x1u << 20) /**< \brief (MPDDRC_CR) Number of Banks */
#define   MPDDRC_CR_NB_4_BANKS (0x0u << 20) /**< \brief (MPDDRC_CR) 4-bank memory devices */
#define   MPDDRC_CR_NB_8_BANKS (0x1u << 20) /**< \brief (MPDDRC_CR) 8 banks. Only possible when using the DDR2-SDRAM and low-power DDR2-SDRAM and DDR3-SDRAM and low-power DDR3-SDRAM devices. */
#define MPDDRC_CR_NDQS (0x1u << 21) /**< \brief (MPDDRC_CR) Not DQS */
#define   MPDDRC_CR_NDQS_ENABLED (0x0u << 21) /**< \brief (MPDDRC_CR) Not DQS is enabled */
#define   MPDDRC_CR_NDQS_DISABLED (0x1u << 21) /**< \brief (MPDDRC_CR) Not DQS is disabled */
#define MPDDRC_CR_DECOD (0x1u << 22) /**< \brief (MPDDRC_CR) Type of Decoding */
#define   MPDDRC_CR_DECOD_SEQUENTIAL (0x0u << 22) /**< \brief (MPDDRC_CR) Method for address mapping where banks alternate at each last DDR-SDRAM page of the current bank. */
#define   MPDDRC_CR_DECOD_INTERLEAVED (0x1u << 22) /**< \brief (MPDDRC_CR) Method for address mapping where banks alternate at each SDRAM end page of the current bank. */
#define MPDDRC_CR_UNAL (0x1u << 23) /**< \brief (MPDDRC_CR) Support Unaligned Access */
#define   MPDDRC_CR_UNAL_UNSUPPORTED (0x0u << 23) /**< \brief (MPDDRC_CR) Unaligned access is not supported. */
#define   MPDDRC_CR_UNAL_SUPPORTED (0x1u << 23) /**< \brief (MPDDRC_CR) Unaligned access is supported. */
/* -------- MPDDRC_TPR0 : (MPDDRC Offset: 0x0C) MPDDRC Timing Parameter 0 Register -------- */
#define MPDDRC_TPR0_TRAS_Pos 0
#define MPDDRC_TPR0_TRAS_Msk (0xfu << MPDDRC_TPR0_TRAS_Pos) /**< \brief (MPDDRC_TPR0) Active to Precharge Delay */
#define MPDDRC_TPR0_TRAS(value) ((MPDDRC_TPR0_TRAS_Msk & ((value) << MPDDRC_TPR0_TRAS_Pos)))
#define MPDDRC_TPR0_TRCD_Pos 4
#define MPDDRC_TPR0_TRCD_Msk (0xfu << MPDDRC_TPR0_TRCD_Pos) /**< \brief (MPDDRC_TPR0) Row to Column Delay */
#define MPDDRC_TPR0_TRCD(value) ((MPDDRC_TPR0_TRCD_Msk & ((value) << MPDDRC_TPR0_TRCD_Pos)))
#define MPDDRC_TPR0_TWR_Pos 8
#define MPDDRC_TPR0_TWR_Msk (0xfu << MPDDRC_TPR0_TWR_Pos) /**< \brief (MPDDRC_TPR0) Write Recovery Delay */
#define MPDDRC_TPR0_TWR(value) ((MPDDRC_TPR0_TWR_Msk & ((value) << MPDDRC_TPR0_TWR_Pos)))
#define MPDDRC_TPR0_TRC_Pos 12
#define MPDDRC_TPR0_TRC_Msk (0xfu << MPDDRC_TPR0_TRC_Pos) /**< \brief (MPDDRC_TPR0) Row Cycle Delay */
#define MPDDRC_TPR0_TRC(value) ((MPDDRC_TPR0_TRC_Msk & ((value) << MPDDRC_TPR0_TRC_Pos)))
#define MPDDRC_TPR0_TRP_Pos 16
#define MPDDRC_TPR0_TRP_Msk (0xfu << MPDDRC_TPR0_TRP_Pos) /**< \brief (MPDDRC_TPR0) Row Precharge Delay */
#define MPDDRC_TPR0_TRP(value) ((MPDDRC_TPR0_TRP_Msk & ((value) << MPDDRC_TPR0_TRP_Pos)))
#define MPDDRC_TPR0_TRRD_Pos 20
#define MPDDRC_TPR0_TRRD_Msk (0xfu << MPDDRC_TPR0_TRRD_Pos) /**< \brief (MPDDRC_TPR0) Active BankA to Active BankB */
#define MPDDRC_TPR0_TRRD(value) ((MPDDRC_TPR0_TRRD_Msk & ((value) << MPDDRC_TPR0_TRRD_Pos)))
#define MPDDRC_TPR0_TWTR_Pos 24
#define MPDDRC_TPR0_TWTR_Msk (0xfu << MPDDRC_TPR0_TWTR_Pos) /**< \brief (MPDDRC_TPR0) Internal Write to Read Delay */
#define MPDDRC_TPR0_TWTR(value) ((MPDDRC_TPR0_TWTR_Msk & ((value) << MPDDRC_TPR0_TWTR_Pos)))
#define MPDDRC_TPR0_TMRD_Pos 28
#define MPDDRC_TPR0_TMRD_Msk (0xfu << MPDDRC_TPR0_TMRD_Pos) /**< \brief (MPDDRC_TPR0) Load Mode Register Command to Activate or Refresh Command */
#define MPDDRC_TPR0_TMRD(value) ((MPDDRC_TPR0_TMRD_Msk & ((value) << MPDDRC_TPR0_TMRD_Pos)))
/* -------- MPDDRC_TPR1 : (MPDDRC Offset: 0x10) MPDDRC Timing Parameter 1 Register -------- */
#define MPDDRC_TPR1_TRFC_Pos 0
#define MPDDRC_TPR1_TRFC_Msk (0x7fu << MPDDRC_TPR1_TRFC_Pos) /**< \brief (MPDDRC_TPR1) Row Cycle Delay */
#define MPDDRC_TPR1_TRFC(value) ((MPDDRC_TPR1_TRFC_Msk & ((value) << MPDDRC_TPR1_TRFC_Pos)))
#define MPDDRC_TPR1_TXSNR_Pos 8
#define MPDDRC_TPR1_TXSNR_Msk (0xffu << MPDDRC_TPR1_TXSNR_Pos) /**< \brief (MPDDRC_TPR1) Exit Self-refresh Delay to Non-Read Command */
#define MPDDRC_TPR1_TXSNR(value) ((MPDDRC_TPR1_TXSNR_Msk & ((value) << MPDDRC_TPR1_TXSNR_Pos)))
#define MPDDRC_TPR1_TXSRD_Pos 16
#define MPDDRC_TPR1_TXSRD_Msk (0xffu << MPDDRC_TPR1_TXSRD_Pos) /**< \brief (MPDDRC_TPR1) Exit Self-refresh Delay to Read Command */
#define MPDDRC_TPR1_TXSRD(value) ((MPDDRC_TPR1_TXSRD_Msk & ((value) << MPDDRC_TPR1_TXSRD_Pos)))
#define MPDDRC_TPR1_TXP_Pos 24
#define MPDDRC_TPR1_TXP_Msk (0xfu << MPDDRC_TPR1_TXP_Pos) /**< \brief (MPDDRC_TPR1) Exit Power-down Delay to First Command */
#define MPDDRC_TPR1_TXP(value) ((MPDDRC_TPR1_TXP_Msk & ((value) << MPDDRC_TPR1_TXP_Pos)))
/* -------- MPDDRC_TPR2 : (MPDDRC Offset: 0x14) MPDDRC Timing Parameter 2 Register -------- */
#define MPDDRC_TPR2_TXARD_Pos 0
#define MPDDRC_TPR2_TXARD_Msk (0xfu << MPDDRC_TPR2_TXARD_Pos) /**< \brief (MPDDRC_TPR2) Exit Active Power Down Delay to Read Command in Mode "Fast Exit" */
#define MPDDRC_TPR2_TXARD(value) ((MPDDRC_TPR2_TXARD_Msk & ((value) << MPDDRC_TPR2_TXARD_Pos)))
#define MPDDRC_TPR2_TXARDS_Pos 4
#define MPDDRC_TPR2_TXARDS_Msk (0xfu << MPDDRC_TPR2_TXARDS_Pos) /**< \brief (MPDDRC_TPR2) Exit Active Power Down Delay to Read Command in Mode "Slow Exit" */
#define MPDDRC_TPR2_TXARDS(value) ((MPDDRC_TPR2_TXARDS_Msk & ((value) << MPDDRC_TPR2_TXARDS_Pos)))
#define MPDDRC_TPR2_TRPA_Pos 8
#define MPDDRC_TPR2_TRPA_Msk (0xfu << MPDDRC_TPR2_TRPA_Pos) /**< \brief (MPDDRC_TPR2) Row Precharge All Delay */
#define MPDDRC_TPR2_TRPA(value) ((MPDDRC_TPR2_TRPA_Msk & ((value) << MPDDRC_TPR2_TRPA_Pos)))
#define MPDDRC_TPR2_TRTP_Pos 12
#define MPDDRC_TPR2_TRTP_Msk (0x7u << MPDDRC_TPR2_TRTP_Pos) /**< \brief (MPDDRC_TPR2) Read to Precharge */
#define MPDDRC_TPR2_TRTP(value) ((MPDDRC_TPR2_TRTP_Msk & ((value) << MPDDRC_TPR2_TRTP_Pos)))
#define MPDDRC_TPR2_TFAW_Pos 16
#define MPDDRC_TPR2_TFAW_Msk (0xfu << MPDDRC_TPR2_TFAW_Pos) /**< \brief (MPDDRC_TPR2) Four Active Windows */
#define MPDDRC_TPR2_TFAW(value) ((MPDDRC_TPR2_TFAW_Msk & ((value) << MPDDRC_TPR2_TFAW_Pos)))
/* -------- MPDDRC_LPR : (MPDDRC Offset: 0x1C) MPDDRC Low-power Register -------- */
#define MPDDRC_LPR_LPCB_Pos 0
#define MPDDRC_LPR_LPCB_Msk (0x3u << MPDDRC_LPR_LPCB_Pos) /**< \brief (MPDDRC_LPR) Low-power Command Bit */
#define MPDDRC_LPR_LPCB(value) ((MPDDRC_LPR_LPCB_Msk & ((value) << MPDDRC_LPR_LPCB_Pos)))
#define   MPDDRC_LPR_LPCB_NOLOWPOWER (0x0u << 0) /**< \brief (MPDDRC_LPR) Low-power feature is inhibited. No Power-down, Self-refresh and Deep-power modes are issued to the DDR-SDRAM device. */
#define   MPDDRC_LPR_LPCB_SELFREFRESH (0x1u << 0) /**< \brief (MPDDRC_LPR) The MPDDRC issues a self-refresh command to the DDR-SDRAM device, the clock(s) is/are deactivated and the CKE signal is set low. The DDR-SDRAM device leaves the Self-refresh mode when accessed and reenters it after the access. */
#define   MPDDRC_LPR_LPCB_POWERDOWN (0x2u << 0) /**< \brief (MPDDRC_LPR) The MPDDRC issues a Power-down command to the DDR-SDRAM device after each access, the CKE signal is set low. The DDR-SDRAM device leaves the Power-down mode when accessed and reenters it after the access. */
#define   MPDDRC_LPR_LPCB_DEEPPOWERDOWN (0x3u << 0) /**< \brief (MPDDRC_LPR) The MPDDRC issues a Deep Power-down command to the low-power DDR-SDRAM device. */
#define MPDDRC_LPR_CLK_FR (0x1u << 2) /**< \brief (MPDDRC_LPR) Clock Frozen Command Bit */
#define   MPDDRC_LPR_CLK_FR_DISABLED (0x0u << 2) /**< \brief (MPDDRC_LPR) Clock(s) is/are not frozen. */
#define   MPDDRC_LPR_CLK_FR_ENABLED (0x1u << 2) /**< \brief (MPDDRC_LPR) Clock(s) is/are frozen. */
#define MPDDRC_LPR_LPDDR2_LPDDR3_PWOFF (0x1u << 3) /**< \brief (MPDDRC_LPR) LPDDR2 - LPDDR3 Power Off Bit */
#define   MPDDRC_LPR_LPDDR2_LPDDR3_PWOFF_DISABLED (0x0u << 3) /**< \brief (MPDDRC_LPR) No power-off sequence applied to LPDDR2/LPDDR3. */
#define   MPDDRC_LPR_LPDDR2_LPDDR3_PWOFF_ENABLED (0x1u << 3) /**< \brief (MPDDRC_LPR) A power-off sequence is applied to the LPDDR2/LPDDR3 device. CKE is forced low. */
#define MPDDRC_LPR_PASR_Pos 4
#define MPDDRC_LPR_PASR_Msk (0x7u << MPDDRC_LPR_PASR_Pos) /**< \brief (MPDDRC_LPR) Partial Array Self-refresh */
#define MPDDRC_LPR_PASR(value) ((MPDDRC_LPR_PASR_Msk & ((value) << MPDDRC_LPR_PASR_Pos)))
#define MPDDRC_LPR_DS_Pos 8
#define MPDDRC_LPR_DS_Msk (0x7u << MPDDRC_LPR_DS_Pos) /**< \brief (MPDDRC_LPR) Drive Strength */
#define MPDDRC_LPR_DS(value) ((MPDDRC_LPR_DS_Msk & ((value) << MPDDRC_LPR_DS_Pos)))
#define MPDDRC_LPR_TIMEOUT_Pos 12
#define MPDDRC_LPR_TIMEOUT_Msk (0x3u << MPDDRC_LPR_TIMEOUT_Pos) /**< \brief (MPDDRC_LPR) Time Between Last Transfer and Low-Power Mode */
#define MPDDRC_LPR_TIMEOUT(value) ((MPDDRC_LPR_TIMEOUT_Msk & ((value) << MPDDRC_LPR_TIMEOUT_Pos)))
#define   MPDDRC_LPR_TIMEOUT_NONE (0x0u << 12) /**< \brief (MPDDRC_LPR) SDRAM Low-power mode is activated immediately after the end of the last transfer. */
#define   MPDDRC_LPR_TIMEOUT_DELAY_64_CLK (0x1u << 12) /**< \brief (MPDDRC_LPR) SDRAM Low-power mode is activated 64 clock cycles after the end of the last transfer. */
#define   MPDDRC_LPR_TIMEOUT_DELAY_128_CLK (0x2u << 12) /**< \brief (MPDDRC_LPR) SDRAM Low-power mode is activated 128 clock cycles after the end of the last transfer. */
#define MPDDRC_LPR_APDE (0x1u << 16) /**< \brief (MPDDRC_LPR) Active Power Down Exit Time */
#define   MPDDRC_LPR_APDE_DDR2_FAST_EXIT (0x0u << 16) /**< \brief (MPDDRC_LPR) Fast Exit from Power Down. DDR2-SDRAM and DDR3-SDRAM devices only. */
#define   MPDDRC_LPR_APDE_DDR2_SLOW_EXIT (0x1u << 16) /**< \brief (MPDDRC_LPR) Slow Exit from Power Down. DDR2-SDRAM and DDR3-SDRAM devices only. */
#define MPDDRC_LPR_UPD_MR_Pos 20
#define MPDDRC_LPR_UPD_MR_Msk (0x3u << MPDDRC_LPR_UPD_MR_Pos) /**< \brief (MPDDRC_LPR) Update Load Mode Register and Extended Mode Register */
#define MPDDRC_LPR_UPD_MR(value) ((MPDDRC_LPR_UPD_MR_Msk & ((value) << MPDDRC_LPR_UPD_MR_Pos)))
#define   MPDDRC_LPR_UPD_MR_NO_UPDATE (0x0u << 20) /**< \brief (MPDDRC_LPR) Update of Load Mode and Extended Mode registers is disabled. */
#define   MPDDRC_LPR_UPD_MR_UPDATE_SHAREDBUS (0x1u << 20) /**< \brief (MPDDRC_LPR) MPDDRC shares an external bus. Automatic update is done during a refresh command and a pending read or write access in the SDRAM device. */
#define   MPDDRC_LPR_UPD_MR_UPDATE_NOSHAREDBUS (0x2u << 20) /**< \brief (MPDDRC_LPR) MPDDRC does not share an external bus. Automatic update is done before entering Self-refresh mode. */
#define MPDDRC_LPR_CHG_FRQ (0x1u << 24) /**< \brief (MPDDRC_LPR) Change Clock Frequency During Self-refresh Mode */
#define MPDDRC_LPR_SELF_DONE (0x1u << 25) /**< \brief (MPDDRC_LPR) Self-refresh is done */
/* -------- MPDDRC_MD : (MPDDRC Offset: 0x20) MPDDRC Memory Device Register -------- */
#define MPDDRC_MD_MD_Pos 0
#define MPDDRC_MD_MD_Msk (0x7u << MPDDRC_MD_MD_Pos) /**< \brief (MPDDRC_MD) Memory Device */
#define MPDDRC_MD_MD(value) ((MPDDRC_MD_MD_Msk & ((value) << MPDDRC_MD_MD_Pos)))
#define   MPDDRC_MD_MD_LPDDR_SDRAM (0x3u << 0) /**< \brief (MPDDRC_MD) Low-power DDR1-SDRAM */
#define   MPDDRC_MD_MD_DDR3_SDRAM (0x4u << 0) /**< \brief (MPDDRC_MD) DDR3-SDRAM */
#define   MPDDRC_MD_MD_LPDDR3_SDRAM (0x5u << 0) /**< \brief (MPDDRC_MD) Low-power DDR3-SDRAM */
#define   MPDDRC_MD_MD_DDR2_SDRAM (0x6u << 0) /**< \brief (MPDDRC_MD) DDR2-SDRAM */
#define   MPDDRC_MD_MD_LPDDR2_SDRAM (0x7u << 0) /**< \brief (MPDDRC_MD) Low-power DDR2-SDRAM */
#define MPDDRC_MD_DBW (0x1u << 4) /**< \brief (MPDDRC_MD) Data Bus Width */
#define   MPDDRC_MD_DBW_DBW_32_BITS (0x0u << 4) /**< \brief (MPDDRC_MD) Data bus width is 32 bits */
#define   MPDDRC_MD_DBW_DBW_16_BITS (0x1u << 4) /**< \brief (MPDDRC_MD) Data bus width is 16 bits. */
#define MPDDRC_MD_WL (0x1u << 5) /**< \brief (MPDDRC_MD) Write Latency */
#define   MPDDRC_MD_WL_WL_SETA (0x0u << 5) /**< \brief (MPDDRC_MD) Write Latency Set A */
#define   MPDDRC_MD_WL_WL_SETB (0x1u << 5) /**< \brief (MPDDRC_MD) Write Latency Set B */
#define MPDDRC_MD_RL3 (0x1u << 6) /**< \brief (MPDDRC_MD) Read Latency 3 Option Support */
#define   MPDDRC_MD_RL3_RL3_SUPPORT (0x0u << 6) /**< \brief (MPDDRC_MD) Read latency of 3 is supported */
#define   MPDDRC_MD_RL3_RL3_NOT_SUPPORTED (0x1u << 6) /**< \brief (MPDDRC_MD) Read latency 0f 3 is not supported */
#define MPDDRC_MD_MANU_ID_Pos 8
#define MPDDRC_MD_MANU_ID_Msk (0xffu << MPDDRC_MD_MANU_ID_Pos) /**< \brief (MPDDRC_MD) Manufacturer Identification */
#define MPDDRC_MD_MANU_ID(value) ((MPDDRC_MD_MANU_ID_Msk & ((value) << MPDDRC_MD_MANU_ID_Pos)))
#define MPDDRC_MD_REV_ID_Pos 16
#define MPDDRC_MD_REV_ID_Msk (0xffu << MPDDRC_MD_REV_ID_Pos) /**< \brief (MPDDRC_MD) Revision Identification */
#define MPDDRC_MD_REV_ID(value) ((MPDDRC_MD_REV_ID_Msk & ((value) << MPDDRC_MD_REV_ID_Pos)))
#define MPDDRC_MD_TYPE_Pos 24
#define MPDDRC_MD_TYPE_Msk (0x3u << MPDDRC_MD_TYPE_Pos) /**< \brief (MPDDRC_MD) DRAM Architecture */
#define MPDDRC_MD_TYPE(value) ((MPDDRC_MD_TYPE_Msk & ((value) << MPDDRC_MD_TYPE_Pos)))
#define   MPDDRC_MD_TYPE_S4_SDRAM (0x0u << 24) /**< \brief (MPDDRC_MD) 4n prefetch architecture */
#define   MPDDRC_MD_TYPE_S2_SDRAM (0x1u << 24) /**< \brief (MPDDRC_MD) 2n prefetch architecture */
#define   MPDDRC_MD_TYPE_NVM (0x2u << 24) /**< \brief (MPDDRC_MD) Non-volatile device */
#define   MPDDRC_MD_TYPE_S8_SDRAM (0x3u << 24) /**< \brief (MPDDRC_MD) 8n prefetch architecture */
#define MPDDRC_MD_DENSITY_Pos 26
#define MPDDRC_MD_DENSITY_Msk (0xfu << MPDDRC_MD_DENSITY_Pos) /**< \brief (MPDDRC_MD) Density of Memory */
#define MPDDRC_MD_DENSITY(value) ((MPDDRC_MD_DENSITY_Msk & ((value) << MPDDRC_MD_DENSITY_Pos)))
#define   MPDDRC_MD_DENSITY_DENSITY_64MBITS (0x0u << 26) /**< \brief (MPDDRC_MD) The device density is 64 Mbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_128MBITS (0x1u << 26) /**< \brief (MPDDRC_MD) The device density is 128 Mbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_256MBITS (0x2u << 26) /**< \brief (MPDDRC_MD) The device density is 256 Mbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_512MBITS (0x3u << 26) /**< \brief (MPDDRC_MD) The device density is 512 Mbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_1GBITS (0x4u << 26) /**< \brief (MPDDRC_MD) The device density is 1 Gbit. */
#define   MPDDRC_MD_DENSITY_DENSITY_2GBITS (0x5u << 26) /**< \brief (MPDDRC_MD) The device density is 2 Gbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_4GBITS (0x6u << 26) /**< \brief (MPDDRC_MD) The device density is 4 Gbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_8GBITS (0x7u << 26) /**< \brief (MPDDRC_MD) The device density is 8 Gbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_16GBITS (0x8u << 26) /**< \brief (MPDDRC_MD) The device density is 16 Gbits. */
#define   MPDDRC_MD_DENSITY_DENSITY_32GBITS (0x9u << 26) /**< \brief (MPDDRC_MD) The device density is 32 Gbits. */
#define MPDDRC_MD_IO_WIDTH_Pos 30
#define MPDDRC_MD_IO_WIDTH_Msk (0x3u << MPDDRC_MD_IO_WIDTH_Pos) /**< \brief (MPDDRC_MD) Width of Memory */
#define MPDDRC_MD_IO_WIDTH(value) ((MPDDRC_MD_IO_WIDTH_Msk & ((value) << MPDDRC_MD_IO_WIDTH_Pos)))
#define   MPDDRC_MD_IO_WIDTH_WIDTH_32 (0x0u << 30) /**< \brief (MPDDRC_MD) The data bus width is 32 bits. */
#define   MPDDRC_MD_IO_WIDTH_WIDTH_16 (0x1u << 30) /**< \brief (MPDDRC_MD) The data bus width is 16 bits. */
#define   MPDDRC_MD_IO_WIDTH_WIDTH_8 (0x2u << 30) /**< \brief (MPDDRC_MD) The data bus width is 8 bits. */
#define   MPDDRC_MD_IO_WIDTH_NOT_USED (0x3u << 30) /**< \brief (MPDDRC_MD) - */
/* -------- MPDDRC_LPDDR23_LPR : (MPDDRC Offset: 0x28) MPDDRC LPDDR2-LPDDR3 Low-power Register -------- */
#define MPDDRC_LPDDR23_LPR_BK_MASK_PASR_Pos 0
#define MPDDRC_LPDDR23_LPR_BK_MASK_PASR_Msk (0xffu << MPDDRC_LPDDR23_LPR_BK_MASK_PASR_Pos) /**< \brief (MPDDRC_LPDDR23_LPR) Bank Mask Bit/PASR */
#define MPDDRC_LPDDR23_LPR_BK_MASK_PASR(value) ((MPDDRC_LPDDR23_LPR_BK_MASK_PASR_Msk & ((value) << MPDDRC_LPDDR23_LPR_BK_MASK_PASR_Pos)))
#define MPDDRC_LPDDR23_LPR_SEG_MASK_Pos 8
#define MPDDRC_LPDDR23_LPR_SEG_MASK_Msk (0xffffu << MPDDRC_LPDDR23_LPR_SEG_MASK_Pos) /**< \brief (MPDDRC_LPDDR23_LPR) Segment Mask Bit */
#define MPDDRC_LPDDR23_LPR_SEG_MASK(value) ((MPDDRC_LPDDR23_LPR_SEG_MASK_Msk & ((value) << MPDDRC_LPDDR23_LPR_SEG_MASK_Pos)))
#define MPDDRC_LPDDR23_LPR_DS_Pos 24
#define MPDDRC_LPDDR23_LPR_DS_Msk (0xfu << MPDDRC_LPDDR23_LPR_DS_Pos) /**< \brief (MPDDRC_LPDDR23_LPR) Drive Strength */
#define MPDDRC_LPDDR23_LPR_DS(value) ((MPDDRC_LPDDR23_LPR_DS_Msk & ((value) << MPDDRC_LPDDR23_LPR_DS_Pos)))
/* -------- MPDDRC_LPDDR23_CAL_MR4 : (MPDDRC Offset: 0x2C) MPDDRC LPDDR2-LPDDR3 Calibration and MR4 Register -------- */
#define MPDDRC_LPDDR23_CAL_MR4_COUNT_CAL_Pos 0
#define MPDDRC_LPDDR23_CAL_MR4_COUNT_CAL_Msk (0xffffu << MPDDRC_LPDDR23_CAL_MR4_COUNT_CAL_Pos) /**< \brief (MPDDRC_LPDDR23_CAL_MR4) LPDDR2 and LPDDR3 Calibration Timer Count */
#define MPDDRC_LPDDR23_CAL_MR4_COUNT_CAL(value) ((MPDDRC_LPDDR23_CAL_MR4_COUNT_CAL_Msk & ((value) << MPDDRC_LPDDR23_CAL_MR4_COUNT_CAL_Pos)))
#define MPDDRC_LPDDR23_CAL_MR4_MR4_READ_Pos 16
#define MPDDRC_LPDDR23_CAL_MR4_MR4_READ_Msk (0xffffu << MPDDRC_LPDDR23_CAL_MR4_MR4_READ_Pos) /**< \brief (MPDDRC_LPDDR23_CAL_MR4) Mode Register 4 Read Interval */
#define MPDDRC_LPDDR23_CAL_MR4_MR4_READ(value) ((MPDDRC_LPDDR23_CAL_MR4_MR4_READ_Msk & ((value) << MPDDRC_LPDDR23_CAL_MR4_MR4_READ_Pos)))
/* -------- MPDDRC_LPDDR23_TIM_CAL : (MPDDRC Offset: 0x30) MPDDRC LPDDR2-LPDDR3 Timing Calibration Register -------- */
#define MPDDRC_LPDDR23_TIM_CAL_ZQCS_Pos 0
#define MPDDRC_LPDDR23_TIM_CAL_ZQCS_Msk (0xffu << MPDDRC_LPDDR23_TIM_CAL_ZQCS_Pos) /**< \brief (MPDDRC_LPDDR23_TIM_CAL) ZQ Calibration Short */
#define MPDDRC_LPDDR23_TIM_CAL_ZQCS(value) ((MPDDRC_LPDDR23_TIM_CAL_ZQCS_Msk & ((value) << MPDDRC_LPDDR23_TIM_CAL_ZQCS_Pos)))
#define MPDDRC_LPDDR23_TIM_CAL_RZQI_Pos 16
#define MPDDRC_LPDDR23_TIM_CAL_RZQI_Msk (0x3u << MPDDRC_LPDDR23_TIM_CAL_RZQI_Pos) /**< \brief (MPDDRC_LPDDR23_TIM_CAL) Built-in Self-Test for RZQ Information */
#define MPDDRC_LPDDR23_TIM_CAL_RZQI(value) ((MPDDRC_LPDDR23_TIM_CAL_RZQI_Msk & ((value) << MPDDRC_LPDDR23_TIM_CAL_RZQI_Pos)))
#define   MPDDRC_LPDDR23_TIM_CAL_RZQI_RZQ_NOT_SUPPORTED (0x0u << 16) /**< \brief (MPDDRC_LPDDR23_TIM_CAL) RZQ self test not supported */
#define   MPDDRC_LPDDR23_TIM_CAL_RZQI_ZQ_VDDCA_FLOAT (0x1u << 16) /**< \brief (MPDDRC_LPDDR23_TIM_CAL) The ZQ pin can be connected to VDDCA or left floating. */
#define   MPDDRC_LPDDR23_TIM_CAL_RZQI_ZQ_SHORTED_GROUND (0x2u << 16) /**< \brief (MPDDRC_LPDDR23_TIM_CAL) The ZQ pin can be shorted to ground. */
#define   MPDDRC_LPDDR23_TIM_CAL_RZQI_ZQ_SELF_TEST_OK (0x3u << 16) /**< \brief (MPDDRC_LPDDR23_TIM_CAL) ZQ pin self test complete; no error condition detected */
/* -------- MPDDRC_IO_CALIBR : (MPDDRC Offset: 0x34) MPDDRC IO Calibration -------- */
#define MPDDRC_IO_CALIBR_RDIV_Pos 0
#define MPDDRC_IO_CALIBR_RDIV_Msk (0x7u << MPDDRC_IO_CALIBR_RDIV_Pos) /**< \brief (MPDDRC_IO_CALIBR) Resistor Divider, Output Driver Impedance */
#define MPDDRC_IO_CALIBR_RDIV(value) ((MPDDRC_IO_CALIBR_RDIV_Msk & ((value) << MPDDRC_IO_CALIBR_RDIV_Pos)))
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_34 (0x1u << 0) /**< \brief (MPDDRC_IO_CALIBR) LP-DDR2 serial impedance line = 34.3 ohms,DDR2/LP-DDR1 serial impedance line: Not applicable */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_40_RZQ_38_RZQ_37_RZQ_35 (0x2u << 0) /**< \brief (MPDDRC_IO_CALIBR) LP-DDR2 serial impedance line = 40 ohms,LP-DDR3 serial impedance line = 38 ohms,DDR3 serial impedance line = 37 ohms,DDR2/LP-DDR1 serial impedance line = 35 ohms */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_48_RZQ_46_RZQ_44_RZQ_43 (0x3u << 0) /**< \brief (MPDDRC_IO_CALIBR) LP-DDR2 serial impedance line = 48 ohms,LP-DDR3 serial impedance line = 46 ohms,DDR3 serial impedance line = 44 ohms,DDR2/LP-DDR1 serial impedance line = 43 ohms */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_60 (0x4u << 0) /**< \brief (MPDDRC_IO_CALIBR) LP-DDR2 serial impedance line = 60 ohms,LP-DDR3 serial impedance line = 57 ohms,DDR3 serial impedance line = 55 ohms,DDR2/LP-DDR1 serial impedance line = 52 ohms */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_80_RZQ_77_RZQ_73_RZQ_70 (0x6u << 0) /**< \brief (MPDDRC_IO_CALIBR) LP-DDR2 serial impedance line = 80 ohms,LP-DDR3 serial impedance line = 77 ohms,DDR3 serial impedance line = 73 ohms,DDR2/LP-DDR1 serial impedance line = 70 ohms */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_120_RZQ_115_RZQ_110_RZQ_105 (0x7u << 0) /**< \brief (MPDDRC_IO_CALIBR) LP-DDR2 serial impedance line = 120 ohms,LP-DDR3 serial impedance line = 115 ohms,DDR3 serial impedance line = 110 ohms,DDR2/LP-DDR1 serial impedance line = 105 ohms */
#define MPDDRC_IO_CALIBR_EN_CALIB (0x1u << 4) /**< \brief (MPDDRC_IO_CALIBR) Enable Calibration */
#define   MPDDRC_IO_CALIBR_EN_CALIB_DISABLE_CALIBRATION (0x0u << 4) /**< \brief (MPDDRC_IO_CALIBR) Calibration is disabled. */
#define   MPDDRC_IO_CALIBR_EN_CALIB_ENABLE_CALIBRATION (0x1u << 4) /**< \brief (MPDDRC_IO_CALIBR) Calibration is enabled. */
#define MPDDRC_IO_CALIBR_TZQIO_Pos 8
#define MPDDRC_IO_CALIBR_TZQIO_Msk (0x7fu << MPDDRC_IO_CALIBR_TZQIO_Pos) /**< \brief (MPDDRC_IO_CALIBR) IO Calibration */
#define MPDDRC_IO_CALIBR_TZQIO(value) ((MPDDRC_IO_CALIBR_TZQIO_Msk & ((value) << MPDDRC_IO_CALIBR_TZQIO_Pos)))
#define MPDDRC_IO_CALIBR_CALCODEP_Pos 16
#define MPDDRC_IO_CALIBR_CALCODEP_Msk (0xfu << MPDDRC_IO_CALIBR_CALCODEP_Pos) /**< \brief (MPDDRC_IO_CALIBR) Number of Transistor P */
#define MPDDRC_IO_CALIBR_CALCODEP(value) ((MPDDRC_IO_CALIBR_CALCODEP_Msk & ((value) << MPDDRC_IO_CALIBR_CALCODEP_Pos)))
#define MPDDRC_IO_CALIBR_CALCODEN_Pos 20
#define MPDDRC_IO_CALIBR_CALCODEN_Msk (0xfu << MPDDRC_IO_CALIBR_CALCODEN_Pos) /**< \brief (MPDDRC_IO_CALIBR) Number of Transistor N */
#define MPDDRC_IO_CALIBR_CALCODEN(value) ((MPDDRC_IO_CALIBR_CALCODEN_Msk & ((value) << MPDDRC_IO_CALIBR_CALCODEN_Pos)))
/* -------- MPDDRC_OCMS : (MPDDRC Offset: 0x38) MPDDRC OCMS Register -------- */
#define MPDDRC_OCMS_SCR_EN (0x1u << 0) /**< \brief (MPDDRC_OCMS) Scrambling Enable */
/* -------- MPDDRC_OCMS_KEY1 : (MPDDRC Offset: 0x3C) MPDDRC OCMS KEY1 Register -------- */
#define MPDDRC_OCMS_KEY1_KEY1_Pos 0
#define MPDDRC_OCMS_KEY1_KEY1_Msk (0xffffffffu << MPDDRC_OCMS_KEY1_KEY1_Pos) /**< \brief (MPDDRC_OCMS_KEY1) Off-chip Memory Scrambling (OCMS) Key Part 1 */
#define MPDDRC_OCMS_KEY1_KEY1(value) ((MPDDRC_OCMS_KEY1_KEY1_Msk & ((value) << MPDDRC_OCMS_KEY1_KEY1_Pos)))
/* -------- MPDDRC_OCMS_KEY2 : (MPDDRC Offset: 0x40) MPDDRC OCMS KEY2 Register -------- */
#define MPDDRC_OCMS_KEY2_KEY2_Pos 0
#define MPDDRC_OCMS_KEY2_KEY2_Msk (0xffffffffu << MPDDRC_OCMS_KEY2_KEY2_Pos) /**< \brief (MPDDRC_OCMS_KEY2) Off-chip Memory Scrambling (OCMS) Key Part 2 */
#define MPDDRC_OCMS_KEY2_KEY2(value) ((MPDDRC_OCMS_KEY2_KEY2_Msk & ((value) << MPDDRC_OCMS_KEY2_KEY2_Pos)))
/* -------- MPDDRC_CONF_ARBITER : (MPDDRC Offset: 0x44) MPDDRC Configuration Arbiter Register -------- */
#define MPDDRC_CONF_ARBITER_ARB_Pos 0
#define MPDDRC_CONF_ARBITER_ARB_Msk (0x3u << MPDDRC_CONF_ARBITER_ARB_Pos) /**< \brief (MPDDRC_CONF_ARBITER) Type of Arbitration */
#define MPDDRC_CONF_ARBITER_ARB(value) ((MPDDRC_CONF_ARBITER_ARB_Msk & ((value) << MPDDRC_CONF_ARBITER_ARB_Pos)))
#define   MPDDRC_CONF_ARBITER_ARB_ROUND (0x0u << 0) /**< \brief (MPDDRC_CONF_ARBITER) Round Robin */
#define   MPDDRC_CONF_ARBITER_ARB_NB_REQUEST (0x1u << 0) /**< \brief (MPDDRC_CONF_ARBITER) Request Policy */
#define   MPDDRC_CONF_ARBITER_ARB_BANDWIDTH (0x2u << 0) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth Policy */
#define MPDDRC_CONF_ARBITER_BDW_MAX_CUR (0x1u << 3) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth Max or Current */
#define MPDDRC_CONF_ARBITER_RQ_WD_P0 (0x1u << 8) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P1 (0x1u << 9) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P2 (0x1u << 10) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P3 (0x1u << 11) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P4 (0x1u << 12) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P5 (0x1u << 13) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P6 (0x1u << 14) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_RQ_WD_P7 (0x1u << 15) /**< \brief (MPDDRC_CONF_ARBITER) Request or Word from Port X */
#define MPDDRC_CONF_ARBITER_MA_PR_P0 (0x1u << 16) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P1 (0x1u << 17) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P2 (0x1u << 18) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P3 (0x1u << 19) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P4 (0x1u << 20) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P5 (0x1u << 21) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P6 (0x1u << 22) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_MA_PR_P7 (0x1u << 23) /**< \brief (MPDDRC_CONF_ARBITER) Master or Software Provide Information */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P0 (0x1u << 24) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P1 (0x1u << 25) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P2 (0x1u << 26) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P3 (0x1u << 27) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P4 (0x1u << 28) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P5 (0x1u << 29) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P6 (0x1u << 30) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
#define MPDDRC_CONF_ARBITER_BDW_BURST_P7 (0x1u << 31) /**< \brief (MPDDRC_CONF_ARBITER) Bandwidth is Reached or Bandwidth and Current Burst Access is Ended on port X */
/* -------- MPDDRC_TIMEOUT : (MPDDRC Offset: 0x48) MPDDRC Time-out Port 0/1/2/3 Register -------- */
#define MPDDRC_TIMEOUT_TIMEOUT_P0_Pos 0
#define MPDDRC_TIMEOUT_TIMEOUT_P0_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P0_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P0(value) ((MPDDRC_TIMEOUT_TIMEOUT_P0_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P0_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P1_Pos 4
#define MPDDRC_TIMEOUT_TIMEOUT_P1_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P1_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P1(value) ((MPDDRC_TIMEOUT_TIMEOUT_P1_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P1_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P2_Pos 8
#define MPDDRC_TIMEOUT_TIMEOUT_P2_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P2_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P2(value) ((MPDDRC_TIMEOUT_TIMEOUT_P2_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P2_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P3_Pos 12
#define MPDDRC_TIMEOUT_TIMEOUT_P3_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P3_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P3(value) ((MPDDRC_TIMEOUT_TIMEOUT_P3_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P3_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P4_Pos 16
#define MPDDRC_TIMEOUT_TIMEOUT_P4_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P4_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P4(value) ((MPDDRC_TIMEOUT_TIMEOUT_P4_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P4_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P5_Pos 20
#define MPDDRC_TIMEOUT_TIMEOUT_P5_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P5_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P5(value) ((MPDDRC_TIMEOUT_TIMEOUT_P5_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P5_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P6_Pos 24
#define MPDDRC_TIMEOUT_TIMEOUT_P6_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P6_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P6(value) ((MPDDRC_TIMEOUT_TIMEOUT_P6_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P6_Pos)))
#define MPDDRC_TIMEOUT_TIMEOUT_P7_Pos 28
#define MPDDRC_TIMEOUT_TIMEOUT_P7_Msk (0xfu << MPDDRC_TIMEOUT_TIMEOUT_P7_Pos) /**< \brief (MPDDRC_TIMEOUT) Time-out for Ports 0, 1, 2, 3, 4, 5, 6 and 7 */
#define MPDDRC_TIMEOUT_TIMEOUT_P7(value) ((MPDDRC_TIMEOUT_TIMEOUT_P7_Msk & ((value) << MPDDRC_TIMEOUT_TIMEOUT_P7_Pos)))
/* -------- MPDDRC_REQ_PORT_0123 : (MPDDRC Offset: 0x4C) MPDDRC Request Port 0/1/2/3 Register -------- */
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P0_Pos 0
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P0_Msk (0xffu << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P0_Pos) /**< \brief (MPDDRC_REQ_PORT_0123) Number of Requests, Number of Words or Bandwidth Allocation from Port 0-1-2-3 */
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P0(value) ((MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P0_Msk & ((value) << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P0_Pos)))
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P1_Pos 8
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P1_Msk (0xffu << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P1_Pos) /**< \brief (MPDDRC_REQ_PORT_0123) Number of Requests, Number of Words or Bandwidth Allocation from Port 0-1-2-3 */
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P1(value) ((MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P1_Msk & ((value) << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P1_Pos)))
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P2_Pos 16
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P2_Msk (0xffu << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P2_Pos) /**< \brief (MPDDRC_REQ_PORT_0123) Number of Requests, Number of Words or Bandwidth Allocation from Port 0-1-2-3 */
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P2(value) ((MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P2_Msk & ((value) << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P2_Pos)))
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P3_Pos 24
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P3_Msk (0xffu << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P3_Pos) /**< \brief (MPDDRC_REQ_PORT_0123) Number of Requests, Number of Words or Bandwidth Allocation from Port 0-1-2-3 */
#define MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P3(value) ((MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P3_Msk & ((value) << MPDDRC_REQ_PORT_0123_NRQ_NWD_BDW_P3_Pos)))
/* -------- MPDDRC_REQ_PORT_4567 : (MPDDRC Offset: 0x50) MPDDRC Request Port 4/5/6/7 Register -------- */
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P4_Pos 0
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P4_Msk (0xffu << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P4_Pos) /**< \brief (MPDDRC_REQ_PORT_4567) Number of Requests, Number of Words or Bandwidth allocation from port 4-5-6-7 */
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P4(value) ((MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P4_Msk & ((value) << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P4_Pos)))
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P5_Pos 8
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P5_Msk (0xffu << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P5_Pos) /**< \brief (MPDDRC_REQ_PORT_4567) Number of Requests, Number of Words or Bandwidth allocation from port 4-5-6-7 */
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P5(value) ((MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P5_Msk & ((value) << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P5_Pos)))
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P6_Pos 16
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P6_Msk (0xffu << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P6_Pos) /**< \brief (MPDDRC_REQ_PORT_4567) Number of Requests, Number of Words or Bandwidth allocation from port 4-5-6-7 */
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P6(value) ((MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P6_Msk & ((value) << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P6_Pos)))
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P7_Pos 24
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P7_Msk (0xffu << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P7_Pos) /**< \brief (MPDDRC_REQ_PORT_4567) Number of Requests, Number of Words or Bandwidth allocation from port 4-5-6-7 */
#define MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P7(value) ((MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P7_Msk & ((value) << MPDDRC_REQ_PORT_4567_NRQ_NWD_BDW_P7_Pos)))
/* -------- MPDDRC_BDW_PORT_0123 : (MPDDRC Offset: 0x54) MPDDRC Bandwidth Port 0/1/2/3 Register -------- */
#define MPDDRC_BDW_PORT_0123_BDW_P0_Pos 0
#define MPDDRC_BDW_PORT_0123_BDW_P0_Msk (0x7fu << MPDDRC_BDW_PORT_0123_BDW_P0_Pos) /**< \brief (MPDDRC_BDW_PORT_0123) Current/Maximum Bandwidth from Port 0-1-2-3 */
#define MPDDRC_BDW_PORT_0123_BDW_P1_Pos 8
#define MPDDRC_BDW_PORT_0123_BDW_P1_Msk (0x7fu << MPDDRC_BDW_PORT_0123_BDW_P1_Pos) /**< \brief (MPDDRC_BDW_PORT_0123) Current/Maximum Bandwidth from Port 0-1-2-3 */
#define MPDDRC_BDW_PORT_0123_BDW_P2_Pos 16
#define MPDDRC_BDW_PORT_0123_BDW_P2_Msk (0x7fu << MPDDRC_BDW_PORT_0123_BDW_P2_Pos) /**< \brief (MPDDRC_BDW_PORT_0123) Current/Maximum Bandwidth from Port 0-1-2-3 */
#define MPDDRC_BDW_PORT_0123_BDW_P3_Pos 24
#define MPDDRC_BDW_PORT_0123_BDW_P3_Msk (0x7fu << MPDDRC_BDW_PORT_0123_BDW_P3_Pos) /**< \brief (MPDDRC_BDW_PORT_0123) Current/Maximum Bandwidth from Port 0-1-2-3 */
/* -------- MPDDRC_BDW_PORT_4567 : (MPDDRC Offset: 0x58) MPDDRC Bandwidth Port 4/5/6/7 Register -------- */
#define MPDDRC_BDW_PORT_4567_BDW_P4_Pos 0
#define MPDDRC_BDW_PORT_4567_BDW_P4_Msk (0x7fu << MPDDRC_BDW_PORT_4567_BDW_P4_Pos) /**< \brief (MPDDRC_BDW_PORT_4567) Current/Maximum Bandwidth from Port 4-5-6-7 */
#define MPDDRC_BDW_PORT_4567_BDW_P5_Pos 8
#define MPDDRC_BDW_PORT_4567_BDW_P5_Msk (0x7fu << MPDDRC_BDW_PORT_4567_BDW_P5_Pos) /**< \brief (MPDDRC_BDW_PORT_4567) Current/Maximum Bandwidth from Port 4-5-6-7 */
#define MPDDRC_BDW_PORT_4567_BDW_P6_Pos 16
#define MPDDRC_BDW_PORT_4567_BDW_P6_Msk (0x7fu << MPDDRC_BDW_PORT_4567_BDW_P6_Pos) /**< \brief (MPDDRC_BDW_PORT_4567) Current/Maximum Bandwidth from Port 4-5-6-7 */
#define MPDDRC_BDW_PORT_4567_BDW_P7_Pos 24
#define MPDDRC_BDW_PORT_4567_BDW_P7_Msk (0x7fu << MPDDRC_BDW_PORT_4567_BDW_P7_Pos) /**< \brief (MPDDRC_BDW_PORT_4567) Current/Maximum Bandwidth from Port 4-5-6-7 */
/* -------- MPDDRC_RD_DATA_PATH : (MPDDRC Offset: 0x5C) MPDDRC Read Datapath Register -------- */
#define MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_Pos 0
#define MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_Msk (0x3u << MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_Pos) /**< \brief (MPDDRC_RD_DATA_PATH) Shift Sampling Point of Data */
#define MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING(value) ((MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_Msk & ((value) << MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_Pos)))
#define   MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_NO_SHIFT (0x0u << 0) /**< \brief (MPDDRC_RD_DATA_PATH) Initial sampling point. */
#define   MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_SHIFT_ONE_CYCLE (0x1u << 0) /**< \brief (MPDDRC_RD_DATA_PATH) Sampling point is shifted by one cycle. */
#define   MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_SHIFT_TWO_CYCLES (0x2u << 0) /**< \brief (MPDDRC_RD_DATA_PATH) Sampling point is shifted by two cycles. */
#define   MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_SHIFT_THREE_CYCLES (0x3u << 0) /**< \brief (MPDDRC_RD_DATA_PATH) Sampling point is shifted by three cycles, unique for LPDDR2 and DDR3 and LPDDR3.Not applicable for DDR2 and LPDDR1 devices. */
/* -------- MPDDRC_MCFGR : (MPDDRC Offset: 0x60) MPDDRC Monitor Configuration -------- */
#define MPDDRC_MCFGR_EN_MONI (0x1u << 0) /**< \brief (MPDDRC_MCFGR) Enable Monitor */
#define MPDDRC_MCFGR_SOFT_RESET (0x1u << 1) /**< \brief (MPDDRC_MCFGR) Soft Reset */
#define MPDDRC_MCFGR_RUN (0x1u << 4) /**< \brief (MPDDRC_MCFGR) Control Monitor */
#define MPDDRC_MCFGR_READ_WRITE_Pos 8
#define MPDDRC_MCFGR_READ_WRITE_Msk (0x3u << MPDDRC_MCFGR_READ_WRITE_Pos) /**< \brief (MPDDRC_MCFGR) Read/Write Access */
#define MPDDRC_MCFGR_READ_WRITE(value) ((MPDDRC_MCFGR_READ_WRITE_Msk & ((value) << MPDDRC_MCFGR_READ_WRITE_Pos)))
#define   MPDDRC_MCFGR_READ_WRITE_TRIG_RD_WR (0x0u << 8) /**< \brief (MPDDRC_MCFGR) Read and Write accesses are triggered. */
#define   MPDDRC_MCFGR_READ_WRITE_TRIG_WR (0x1u << 8) /**< \brief (MPDDRC_MCFGR) Only Write accesses are triggered. */
#define   MPDDRC_MCFGR_READ_WRITE_TRIG_RD (0x2u << 8) /**< \brief (MPDDRC_MCFGR) Only Read accesses are triggered. */
#define MPDDRC_MCFGR_REFR_CALIB (0x1u << 10) /**< \brief (MPDDRC_MCFGR) Refresh Calibration */
#define MPDDRC_MCFGR_INFO_Pos 11
#define MPDDRC_MCFGR_INFO_Msk (0x3u << MPDDRC_MCFGR_INFO_Pos) /**< \brief (MPDDRC_MCFGR) Information Type */
#define MPDDRC_MCFGR_INFO(value) ((MPDDRC_MCFGR_INFO_Msk & ((value) << MPDDRC_MCFGR_INFO_Pos)))
#define   MPDDRC_MCFGR_INFO_MAX_WAIT (0x0u << 11) /**< \brief (MPDDRC_MCFGR) Information concerning the transfer with the longest waiting time */
#define   MPDDRC_MCFGR_INFO_NB_TRANSFERS (0x1u << 11) /**< \brief (MPDDRC_MCFGR) Number of transfers on the port */
#define   MPDDRC_MCFGR_INFO_TOTAL_LATENCY (0x2u << 11) /**< \brief (MPDDRC_MCFGR) Total latency on the port */
/* -------- MPDDRC_MADDR0 : (MPDDRC Offset: 0x64) MPDDRC Monitor Address High/Low port 0 -------- */
#define MPDDRC_MADDR0_ADDR_LOW_PORT0_Pos 0
#define MPDDRC_MADDR0_ADDR_LOW_PORT0_Msk (0xffffu << MPDDRC_MADDR0_ADDR_LOW_PORT0_Pos) /**< \brief (MPDDRC_MADDR0) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR0_ADDR_LOW_PORT0(value) ((MPDDRC_MADDR0_ADDR_LOW_PORT0_Msk & ((value) << MPDDRC_MADDR0_ADDR_LOW_PORT0_Pos)))
#define MPDDRC_MADDR0_ADDR_HIGH_PORT0_Pos 16
#define MPDDRC_MADDR0_ADDR_HIGH_PORT0_Msk (0xffffu << MPDDRC_MADDR0_ADDR_HIGH_PORT0_Pos) /**< \brief (MPDDRC_MADDR0) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR0_ADDR_HIGH_PORT0(value) ((MPDDRC_MADDR0_ADDR_HIGH_PORT0_Msk & ((value) << MPDDRC_MADDR0_ADDR_HIGH_PORT0_Pos)))
/* -------- MPDDRC_MADDR1 : (MPDDRC Offset: 0x68) MPDDRC Monitor Address High/Low port 1 -------- */
#define MPDDRC_MADDR1_ADDR_LOW_PORT1_Pos 0
#define MPDDRC_MADDR1_ADDR_LOW_PORT1_Msk (0xffffu << MPDDRC_MADDR1_ADDR_LOW_PORT1_Pos) /**< \brief (MPDDRC_MADDR1) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR1_ADDR_LOW_PORT1(value) ((MPDDRC_MADDR1_ADDR_LOW_PORT1_Msk & ((value) << MPDDRC_MADDR1_ADDR_LOW_PORT1_Pos)))
#define MPDDRC_MADDR1_ADDR_HIGH_PORT1_Pos 16
#define MPDDRC_MADDR1_ADDR_HIGH_PORT1_Msk (0xffffu << MPDDRC_MADDR1_ADDR_HIGH_PORT1_Pos) /**< \brief (MPDDRC_MADDR1) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR1_ADDR_HIGH_PORT1(value) ((MPDDRC_MADDR1_ADDR_HIGH_PORT1_Msk & ((value) << MPDDRC_MADDR1_ADDR_HIGH_PORT1_Pos)))
/* -------- MPDDRC_MADDR2 : (MPDDRC Offset: 0x6C) MPDDRC Monitor Address High/Low port 2 -------- */
#define MPDDRC_MADDR2_ADDR_LOW_PORT2_Pos 0
#define MPDDRC_MADDR2_ADDR_LOW_PORT2_Msk (0xffffu << MPDDRC_MADDR2_ADDR_LOW_PORT2_Pos) /**< \brief (MPDDRC_MADDR2) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR2_ADDR_LOW_PORT2(value) ((MPDDRC_MADDR2_ADDR_LOW_PORT2_Msk & ((value) << MPDDRC_MADDR2_ADDR_LOW_PORT2_Pos)))
#define MPDDRC_MADDR2_ADDR_HIGH_PORT2_Pos 16
#define MPDDRC_MADDR2_ADDR_HIGH_PORT2_Msk (0xffffu << MPDDRC_MADDR2_ADDR_HIGH_PORT2_Pos) /**< \brief (MPDDRC_MADDR2) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR2_ADDR_HIGH_PORT2(value) ((MPDDRC_MADDR2_ADDR_HIGH_PORT2_Msk & ((value) << MPDDRC_MADDR2_ADDR_HIGH_PORT2_Pos)))
/* -------- MPDDRC_MADDR3 : (MPDDRC Offset: 0x70) MPDDRC Monitor Address High/Low port 3 -------- */
#define MPDDRC_MADDR3_ADDR_LOW_PORT3_Pos 0
#define MPDDRC_MADDR3_ADDR_LOW_PORT3_Msk (0xffffu << MPDDRC_MADDR3_ADDR_LOW_PORT3_Pos) /**< \brief (MPDDRC_MADDR3) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR3_ADDR_LOW_PORT3(value) ((MPDDRC_MADDR3_ADDR_LOW_PORT3_Msk & ((value) << MPDDRC_MADDR3_ADDR_LOW_PORT3_Pos)))
#define MPDDRC_MADDR3_ADDR_HIGH_PORT3_Pos 16
#define MPDDRC_MADDR3_ADDR_HIGH_PORT3_Msk (0xffffu << MPDDRC_MADDR3_ADDR_HIGH_PORT3_Pos) /**< \brief (MPDDRC_MADDR3) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR3_ADDR_HIGH_PORT3(value) ((MPDDRC_MADDR3_ADDR_HIGH_PORT3_Msk & ((value) << MPDDRC_MADDR3_ADDR_HIGH_PORT3_Pos)))
/* -------- MPDDRC_MADDR4 : (MPDDRC Offset: 0x74) MPDDRC Monitor Address High/Low port 4 -------- */
#define MPDDRC_MADDR4_ADDR_LOW_PORT4_Pos 0
#define MPDDRC_MADDR4_ADDR_LOW_PORT4_Msk (0xffffu << MPDDRC_MADDR4_ADDR_LOW_PORT4_Pos) /**< \brief (MPDDRC_MADDR4) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR4_ADDR_LOW_PORT4(value) ((MPDDRC_MADDR4_ADDR_LOW_PORT4_Msk & ((value) << MPDDRC_MADDR4_ADDR_LOW_PORT4_Pos)))
#define MPDDRC_MADDR4_ADDR_HIGH_PORT4_Pos 16
#define MPDDRC_MADDR4_ADDR_HIGH_PORT4_Msk (0xffffu << MPDDRC_MADDR4_ADDR_HIGH_PORT4_Pos) /**< \brief (MPDDRC_MADDR4) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR4_ADDR_HIGH_PORT4(value) ((MPDDRC_MADDR4_ADDR_HIGH_PORT4_Msk & ((value) << MPDDRC_MADDR4_ADDR_HIGH_PORT4_Pos)))
/* -------- MPDDRC_MADDR5 : (MPDDRC Offset: 0x78) MPDDRC Monitor Address High/Low port 5 -------- */
#define MPDDRC_MADDR5_ADDR_LOW_PORT5_Pos 0
#define MPDDRC_MADDR5_ADDR_LOW_PORT5_Msk (0xffffu << MPDDRC_MADDR5_ADDR_LOW_PORT5_Pos) /**< \brief (MPDDRC_MADDR5) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR5_ADDR_LOW_PORT5(value) ((MPDDRC_MADDR5_ADDR_LOW_PORT5_Msk & ((value) << MPDDRC_MADDR5_ADDR_LOW_PORT5_Pos)))
#define MPDDRC_MADDR5_ADDR_HIGH_PORT5_Pos 16
#define MPDDRC_MADDR5_ADDR_HIGH_PORT5_Msk (0xffffu << MPDDRC_MADDR5_ADDR_HIGH_PORT5_Pos) /**< \brief (MPDDRC_MADDR5) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR5_ADDR_HIGH_PORT5(value) ((MPDDRC_MADDR5_ADDR_HIGH_PORT5_Msk & ((value) << MPDDRC_MADDR5_ADDR_HIGH_PORT5_Pos)))
/* -------- MPDDRC_MADDR6 : (MPDDRC Offset: 0x7C) MPDDRC Monitor Address High/Low port 6 -------- */
#define MPDDRC_MADDR6_ADDR_LOW_PORT6_Pos 0
#define MPDDRC_MADDR6_ADDR_LOW_PORT6_Msk (0xffffu << MPDDRC_MADDR6_ADDR_LOW_PORT6_Pos) /**< \brief (MPDDRC_MADDR6) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR6_ADDR_LOW_PORT6(value) ((MPDDRC_MADDR6_ADDR_LOW_PORT6_Msk & ((value) << MPDDRC_MADDR6_ADDR_LOW_PORT6_Pos)))
#define MPDDRC_MADDR6_ADDR_HIGH_PORT6_Pos 16
#define MPDDRC_MADDR6_ADDR_HIGH_PORT6_Msk (0xffffu << MPDDRC_MADDR6_ADDR_HIGH_PORT6_Pos) /**< \brief (MPDDRC_MADDR6) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR6_ADDR_HIGH_PORT6(value) ((MPDDRC_MADDR6_ADDR_HIGH_PORT6_Msk & ((value) << MPDDRC_MADDR6_ADDR_HIGH_PORT6_Pos)))
/* -------- MPDDRC_MADDR7 : (MPDDRC Offset: 0x80) MPDDRC Monitor Address High/Low port 7 -------- */
#define MPDDRC_MADDR7_ADDR_LOW_PORT7_Pos 0
#define MPDDRC_MADDR7_ADDR_LOW_PORT7_Msk (0xffffu << MPDDRC_MADDR7_ADDR_LOW_PORT7_Pos) /**< \brief (MPDDRC_MADDR7) Address Low on Port x [x =0..7] */
#define MPDDRC_MADDR7_ADDR_LOW_PORT7(value) ((MPDDRC_MADDR7_ADDR_LOW_PORT7_Msk & ((value) << MPDDRC_MADDR7_ADDR_LOW_PORT7_Pos)))
#define MPDDRC_MADDR7_ADDR_HIGH_PORT7_Pos 16
#define MPDDRC_MADDR7_ADDR_HIGH_PORT7_Msk (0xffffu << MPDDRC_MADDR7_ADDR_HIGH_PORT7_Pos) /**< \brief (MPDDRC_MADDR7) Address High on Port x [x =0..7] */
#define MPDDRC_MADDR7_ADDR_HIGH_PORT7(value) ((MPDDRC_MADDR7_ADDR_HIGH_PORT7_Msk & ((value) << MPDDRC_MADDR7_ADDR_HIGH_PORT7_Pos)))
/* -------- MPDDRC_MINFO0 : (MPDDRC Offset: 0x84) MPDDRC Monitor Information port 0 -------- */
#define MPDDRC_MINFO0_MAX_PORT0_WAITING_Pos 0
#define MPDDRC_MINFO0_MAX_PORT0_WAITING_Msk (0xffffu << MPDDRC_MINFO0_MAX_PORT0_WAITING_Pos) /**< \brief (MPDDRC_MINFO0) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO0_BURST_Pos 16
#define MPDDRC_MINFO0_BURST_Msk (0x7u << MPDDRC_MINFO0_BURST_Pos) /**< \brief (MPDDRC_MINFO0) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO0_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO0) Single transfer */
#define   MPDDRC_MINFO0_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO0) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO0_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO0) 4-beat wrapping burst */
#define   MPDDRC_MINFO0_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO0) 4-beat incrementing burst */
#define   MPDDRC_MINFO0_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO0) 8-beat wrapping burst */
#define   MPDDRC_MINFO0_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO0) 8-beat incrementing burst */
#define   MPDDRC_MINFO0_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO0) 16-beat wrapping burst */
#define   MPDDRC_MINFO0_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO0) 16-beat incrementing burst */
#define MPDDRC_MINFO0_SIZE_Pos 20
#define MPDDRC_MINFO0_SIZE_Msk (0x7u << MPDDRC_MINFO0_SIZE_Pos) /**< \brief (MPDDRC_MINFO0) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO0_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO0) Byte transfer */
#define   MPDDRC_MINFO0_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO0) Halfword transfer */
#define   MPDDRC_MINFO0_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO0) Word transfer */
#define   MPDDRC_MINFO0_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO0) Dword transfer */
#define MPDDRC_MINFO0_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO0) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO0_P0_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO0_P0_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO0_P0_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO0) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO0_P0_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO0_P0_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO0_P0_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO0) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO1 : (MPDDRC Offset: 0x88) MPDDRC Monitor Information port 1 -------- */
#define MPDDRC_MINFO1_MAX_PORT1_WAITING_Pos 0
#define MPDDRC_MINFO1_MAX_PORT1_WAITING_Msk (0xffffu << MPDDRC_MINFO1_MAX_PORT1_WAITING_Pos) /**< \brief (MPDDRC_MINFO1) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO1_BURST_Pos 16
#define MPDDRC_MINFO1_BURST_Msk (0x7u << MPDDRC_MINFO1_BURST_Pos) /**< \brief (MPDDRC_MINFO1) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO1_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO1) Single transfer */
#define   MPDDRC_MINFO1_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO1) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO1_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO1) 4-beat wrapping burst */
#define   MPDDRC_MINFO1_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO1) 4-beat incrementing burst */
#define   MPDDRC_MINFO1_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO1) 8-beat wrapping burst */
#define   MPDDRC_MINFO1_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO1) 8-beat incrementing burst */
#define   MPDDRC_MINFO1_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO1) 16-beat wrapping burst */
#define   MPDDRC_MINFO1_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO1) 16-beat incrementing burst */
#define MPDDRC_MINFO1_SIZE_Pos 20
#define MPDDRC_MINFO1_SIZE_Msk (0x7u << MPDDRC_MINFO1_SIZE_Pos) /**< \brief (MPDDRC_MINFO1) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO1_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO1) Byte transfer */
#define   MPDDRC_MINFO1_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO1) Halfword transfer */
#define   MPDDRC_MINFO1_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO1) Word transfer */
#define   MPDDRC_MINFO1_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO1) Dword transfer */
#define MPDDRC_MINFO1_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO1) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO1_P1_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO1_P1_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO1_P1_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO1) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO1_P1_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO1_P1_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO1_P1_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO1) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO2 : (MPDDRC Offset: 0x8C) MPDDRC Monitor Information port 2 -------- */
#define MPDDRC_MINFO2_MAX_PORT2_WAITING_Pos 0
#define MPDDRC_MINFO2_MAX_PORT2_WAITING_Msk (0xffffu << MPDDRC_MINFO2_MAX_PORT2_WAITING_Pos) /**< \brief (MPDDRC_MINFO2) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO2_BURST_Pos 16
#define MPDDRC_MINFO2_BURST_Msk (0x7u << MPDDRC_MINFO2_BURST_Pos) /**< \brief (MPDDRC_MINFO2) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO2_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO2) Single transfer */
#define   MPDDRC_MINFO2_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO2) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO2_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO2) 4-beat wrapping burst */
#define   MPDDRC_MINFO2_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO2) 4-beat incrementing burst */
#define   MPDDRC_MINFO2_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO2) 8-beat wrapping burst */
#define   MPDDRC_MINFO2_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO2) 8-beat incrementing burst */
#define   MPDDRC_MINFO2_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO2) 16-beat wrapping burst */
#define   MPDDRC_MINFO2_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO2) 16-beat incrementing burst */
#define MPDDRC_MINFO2_SIZE_Pos 20
#define MPDDRC_MINFO2_SIZE_Msk (0x7u << MPDDRC_MINFO2_SIZE_Pos) /**< \brief (MPDDRC_MINFO2) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO2_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO2) Byte transfer */
#define   MPDDRC_MINFO2_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO2) Halfword transfer */
#define   MPDDRC_MINFO2_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO2) Word transfer */
#define   MPDDRC_MINFO2_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO2) Dword transfer */
#define MPDDRC_MINFO2_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO2) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO2_P2_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO2_P2_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO2_P2_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO2) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO2_P2_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO2_P2_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO2_P2_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO2) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO3 : (MPDDRC Offset: 0x90) MPDDRC Monitor Information port 3 -------- */
#define MPDDRC_MINFO3_MAX_PORT3_WAITING_Pos 0
#define MPDDRC_MINFO3_MAX_PORT3_WAITING_Msk (0xffffu << MPDDRC_MINFO3_MAX_PORT3_WAITING_Pos) /**< \brief (MPDDRC_MINFO3) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO3_BURST_Pos 16
#define MPDDRC_MINFO3_BURST_Msk (0x7u << MPDDRC_MINFO3_BURST_Pos) /**< \brief (MPDDRC_MINFO3) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO3_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO3) Single transfer */
#define   MPDDRC_MINFO3_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO3) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO3_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO3) 4-beat wrapping burst */
#define   MPDDRC_MINFO3_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO3) 4-beat incrementing burst */
#define   MPDDRC_MINFO3_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO3) 8-beat wrapping burst */
#define   MPDDRC_MINFO3_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO3) 8-beat incrementing burst */
#define   MPDDRC_MINFO3_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO3) 16-beat wrapping burst */
#define   MPDDRC_MINFO3_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO3) 16-beat incrementing burst */
#define MPDDRC_MINFO3_SIZE_Pos 20
#define MPDDRC_MINFO3_SIZE_Msk (0x7u << MPDDRC_MINFO3_SIZE_Pos) /**< \brief (MPDDRC_MINFO3) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO3_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO3) Byte transfer */
#define   MPDDRC_MINFO3_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO3) Halfword transfer */
#define   MPDDRC_MINFO3_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO3) Word transfer */
#define   MPDDRC_MINFO3_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO3) Dword transfer */
#define MPDDRC_MINFO3_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO3) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO3_P3_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO3_P3_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO3_P3_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO3) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO3_P3_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO3_P3_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO3_P3_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO3) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO4 : (MPDDRC Offset: 0x94) MPDDRC Monitor Information port 4 -------- */
#define MPDDRC_MINFO4_MAX_PORT4_WAITING_Pos 0
#define MPDDRC_MINFO4_MAX_PORT4_WAITING_Msk (0xffffu << MPDDRC_MINFO4_MAX_PORT4_WAITING_Pos) /**< \brief (MPDDRC_MINFO4) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO4_BURST_Pos 16
#define MPDDRC_MINFO4_BURST_Msk (0x7u << MPDDRC_MINFO4_BURST_Pos) /**< \brief (MPDDRC_MINFO4) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO4_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO4) Single transfer */
#define   MPDDRC_MINFO4_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO4) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO4_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO4) 4-beat wrapping burst */
#define   MPDDRC_MINFO4_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO4) 4-beat incrementing burst */
#define   MPDDRC_MINFO4_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO4) 8-beat wrapping burst */
#define   MPDDRC_MINFO4_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO4) 8-beat incrementing burst */
#define   MPDDRC_MINFO4_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO4) 16-beat wrapping burst */
#define   MPDDRC_MINFO4_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO4) 16-beat incrementing burst */
#define MPDDRC_MINFO4_SIZE_Pos 20
#define MPDDRC_MINFO4_SIZE_Msk (0x7u << MPDDRC_MINFO4_SIZE_Pos) /**< \brief (MPDDRC_MINFO4) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO4_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO4) Byte transfer */
#define   MPDDRC_MINFO4_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO4) Halfword transfer */
#define   MPDDRC_MINFO4_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO4) Word transfer */
#define   MPDDRC_MINFO4_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO4) Dword transfer */
#define MPDDRC_MINFO4_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO4) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO4_P4_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO4_P4_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO4_P4_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO4) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO4_P4_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO4_P4_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO4_P4_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO4) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO5 : (MPDDRC Offset: 0x98) MPDDRC Monitor Information port 5 -------- */
#define MPDDRC_MINFO5_MAX_PORT5_WAITING_Pos 0
#define MPDDRC_MINFO5_MAX_PORT5_WAITING_Msk (0xffffu << MPDDRC_MINFO5_MAX_PORT5_WAITING_Pos) /**< \brief (MPDDRC_MINFO5) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO5_BURST_Pos 16
#define MPDDRC_MINFO5_BURST_Msk (0x7u << MPDDRC_MINFO5_BURST_Pos) /**< \brief (MPDDRC_MINFO5) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO5_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO5) Single transfer */
#define   MPDDRC_MINFO5_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO5) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO5_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO5) 4-beat wrapping burst */
#define   MPDDRC_MINFO5_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO5) 4-beat incrementing burst */
#define   MPDDRC_MINFO5_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO5) 8-beat wrapping burst */
#define   MPDDRC_MINFO5_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO5) 8-beat incrementing burst */
#define   MPDDRC_MINFO5_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO5) 16-beat wrapping burst */
#define   MPDDRC_MINFO5_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO5) 16-beat incrementing burst */
#define MPDDRC_MINFO5_SIZE_Pos 20
#define MPDDRC_MINFO5_SIZE_Msk (0x7u << MPDDRC_MINFO5_SIZE_Pos) /**< \brief (MPDDRC_MINFO5) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO5_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO5) Byte transfer */
#define   MPDDRC_MINFO5_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO5) Halfword transfer */
#define   MPDDRC_MINFO5_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO5) Word transfer */
#define   MPDDRC_MINFO5_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO5) Dword transfer */
#define MPDDRC_MINFO5_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO5) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO5_P5_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO5_P5_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO5_P5_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO5) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO5_P5_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO5_P5_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO5_P5_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO5) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO6 : (MPDDRC Offset: 0x9C) MPDDRC Monitor Information port 6 -------- */
#define MPDDRC_MINFO6_MAX_PORT6_WAITING_Pos 0
#define MPDDRC_MINFO6_MAX_PORT6_WAITING_Msk (0xffffu << MPDDRC_MINFO6_MAX_PORT6_WAITING_Pos) /**< \brief (MPDDRC_MINFO6) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO6_BURST_Pos 16
#define MPDDRC_MINFO6_BURST_Msk (0x7u << MPDDRC_MINFO6_BURST_Pos) /**< \brief (MPDDRC_MINFO6) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO6_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO6) Single transfer */
#define   MPDDRC_MINFO6_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO6) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO6_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO6) 4-beat wrapping burst */
#define   MPDDRC_MINFO6_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO6) 4-beat incrementing burst */
#define   MPDDRC_MINFO6_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO6) 8-beat wrapping burst */
#define   MPDDRC_MINFO6_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO6) 8-beat incrementing burst */
#define   MPDDRC_MINFO6_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO6) 16-beat wrapping burst */
#define   MPDDRC_MINFO6_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO6) 16-beat incrementing burst */
#define MPDDRC_MINFO6_SIZE_Pos 20
#define MPDDRC_MINFO6_SIZE_Msk (0x7u << MPDDRC_MINFO6_SIZE_Pos) /**< \brief (MPDDRC_MINFO6) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO6_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO6) Byte transfer */
#define   MPDDRC_MINFO6_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO6) Halfword transfer */
#define   MPDDRC_MINFO6_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO6) Word transfer */
#define   MPDDRC_MINFO6_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO6) Dword transfer */
#define MPDDRC_MINFO6_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO6) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO6_P6_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO6_P6_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO6_P6_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO6) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO6_P6_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO6_P6_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO6_P6_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO6) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_MINFO7 : (MPDDRC Offset: 0xA0) MPDDRC Monitor Information port 7 -------- */
#define MPDDRC_MINFO7_MAX_PORT7_WAITING_Pos 0
#define MPDDRC_MINFO7_MAX_PORT7_WAITING_Msk (0xffffu << MPDDRC_MINFO7_MAX_PORT7_WAITING_Pos) /**< \brief (MPDDRC_MINFO7) Address High on Port x [x =0..7] */
#define MPDDRC_MINFO7_BURST_Pos 16
#define MPDDRC_MINFO7_BURST_Msk (0x7u << MPDDRC_MINFO7_BURST_Pos) /**< \brief (MPDDRC_MINFO7) Type of Burst on Port x [x =0..7] */
#define   MPDDRC_MINFO7_BURST_SINGLE (0x0u << 16) /**< \brief (MPDDRC_MINFO7) Single transfer */
#define   MPDDRC_MINFO7_BURST_INCR (0x1u << 16) /**< \brief (MPDDRC_MINFO7) Incrementing burst of unspecified length */
#define   MPDDRC_MINFO7_BURST_WRAP4 (0x2u << 16) /**< \brief (MPDDRC_MINFO7) 4-beat wrapping burst */
#define   MPDDRC_MINFO7_BURST_INCR4 (0x3u << 16) /**< \brief (MPDDRC_MINFO7) 4-beat incrementing burst */
#define   MPDDRC_MINFO7_BURST_WRAP8 (0x4u << 16) /**< \brief (MPDDRC_MINFO7) 8-beat wrapping burst */
#define   MPDDRC_MINFO7_BURST_INCR8 (0x5u << 16) /**< \brief (MPDDRC_MINFO7) 8-beat incrementing burst */
#define   MPDDRC_MINFO7_BURST_WRAP16 (0x6u << 16) /**< \brief (MPDDRC_MINFO7) 16-beat wrapping burst */
#define   MPDDRC_MINFO7_BURST_INCR16 (0x7u << 16) /**< \brief (MPDDRC_MINFO7) 16-beat incrementing burst */
#define MPDDRC_MINFO7_SIZE_Pos 20
#define MPDDRC_MINFO7_SIZE_Msk (0x7u << MPDDRC_MINFO7_SIZE_Pos) /**< \brief (MPDDRC_MINFO7) Transfer Size on Port x [x =0..7] */
#define   MPDDRC_MINFO7_SIZE_8BITS (0x0u << 20) /**< \brief (MPDDRC_MINFO7) Byte transfer */
#define   MPDDRC_MINFO7_SIZE_16BITS (0x1u << 20) /**< \brief (MPDDRC_MINFO7) Halfword transfer */
#define   MPDDRC_MINFO7_SIZE_32BITS (0x2u << 20) /**< \brief (MPDDRC_MINFO7) Word transfer */
#define   MPDDRC_MINFO7_SIZE_64BITS (0x3u << 20) /**< \brief (MPDDRC_MINFO7) Dword transfer */
#define MPDDRC_MINFO7_READ_WRITE (0x1u << 24) /**< \brief (MPDDRC_MINFO7) Read or Write Access on Port x [x =0..7] */
#define MPDDRC_MINFO7_P7_NB_TRANSFERS_Pos 0
#define MPDDRC_MINFO7_P7_NB_TRANSFERS_Msk (0xffffffffu << MPDDRC_MINFO7_P7_NB_TRANSFERS_Pos) /**< \brief (MPDDRC_MINFO7) Number of Transfers on Port x [x =0..7] */
#define MPDDRC_MINFO7_P7_TOTAL_LATENCY_Pos 0
#define MPDDRC_MINFO7_P7_TOTAL_LATENCY_Msk (0xffffffffu << MPDDRC_MINFO7_P7_TOTAL_LATENCY_Pos) /**< \brief (MPDDRC_MINFO7) Total Latency on Port x [x =0..7] */
/* -------- MPDDRC_WPMR : (MPDDRC Offset: 0xE4) MPDDRC Write Protection Mode Register -------- */
#define MPDDRC_WPMR_WPEN (0x1u << 0) /**< \brief (MPDDRC_WPMR) Write Protection Enable */
#define MPDDRC_WPMR_WPKEY_Pos 8
#define MPDDRC_WPMR_WPKEY_Msk (0xffffffu << MPDDRC_WPMR_WPKEY_Pos) /**< \brief (MPDDRC_WPMR) Write Protection Key */
#define MPDDRC_WPMR_WPKEY(value) ((MPDDRC_WPMR_WPKEY_Msk & ((value) << MPDDRC_WPMR_WPKEY_Pos)))
#define   MPDDRC_WPMR_WPKEY_PASSWD (0x444452u << 8) /**< \brief (MPDDRC_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- MPDDRC_WPSR : (MPDDRC Offset: 0xE8) MPDDRC Write Protection Status Register -------- */
#define MPDDRC_WPSR_WPVS (0x1u << 0) /**< \brief (MPDDRC_WPSR) Write Protection Enable */
#define MPDDRC_WPSR_WPVSRC_Pos 8
#define MPDDRC_WPSR_WPVSRC_Msk (0xffffu << MPDDRC_WPSR_WPVSRC_Pos) /**< \brief (MPDDRC_WPSR) Write Protection Violation Source */
/* -------- MPDDRC_VERSION : (MPDDRC Offset: 0xFC) MPDDRC Version Register -------- */
#define MPDDRC_VERSION_VERSION_Pos 0
#define MPDDRC_VERSION_VERSION_Msk (0xffffu << MPDDRC_VERSION_VERSION_Pos) /**< \brief (MPDDRC_VERSION) Version of the Hardware Module */
#define MPDDRC_VERSION_MFN_Pos 16
#define MPDDRC_VERSION_MFN_Msk (0xfu << MPDDRC_VERSION_MFN_Pos) /**< \brief (MPDDRC_VERSION) Metal Fix Number */
/* -------- MPDDRC_DLL_OS : (MPDDRC Offset: 0x100) MPDDRC DLL Offset Selection Register -------- */
#define MPDDRC_DLL_OS_SELOFF (0x1u << 0) /**< \brief (MPDDRC_DLL_OS) Offset Selection */
/* -------- MPDDRC_DLL_MAO : (MPDDRC Offset: 0x104) MPDDRC DLL MASTER Offset Register -------- */
#define MPDDRC_DLL_MAO_MAOFF_Pos 0
#define MPDDRC_DLL_MAO_MAOFF_Msk (0xffu << MPDDRC_DLL_MAO_MAOFF_Pos) /**< \brief (MPDDRC_DLL_MAO) Master Delay Line Offset */
#define MPDDRC_DLL_MAO_MAOFF(value) ((MPDDRC_DLL_MAO_MAOFF_Msk & ((value) << MPDDRC_DLL_MAO_MAOFF_Pos)))
/* -------- MPDDRC_DLL_SO0 : (MPDDRC Offset: 0x108) MPDDRC DLL SLAVE Offset 0 Register -------- */
#define MPDDRC_DLL_SO0_S0OFF_Pos 0
#define MPDDRC_DLL_SO0_S0OFF_Msk (0xffu << MPDDRC_DLL_SO0_S0OFF_Pos) /**< \brief (MPDDRC_DLL_SO0) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO0_S0OFF(value) ((MPDDRC_DLL_SO0_S0OFF_Msk & ((value) << MPDDRC_DLL_SO0_S0OFF_Pos)))
#define MPDDRC_DLL_SO0_S1OFF_Pos 8
#define MPDDRC_DLL_SO0_S1OFF_Msk (0xffu << MPDDRC_DLL_SO0_S1OFF_Pos) /**< \brief (MPDDRC_DLL_SO0) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO0_S1OFF(value) ((MPDDRC_DLL_SO0_S1OFF_Msk & ((value) << MPDDRC_DLL_SO0_S1OFF_Pos)))
#define MPDDRC_DLL_SO0_S2OFF_Pos 16
#define MPDDRC_DLL_SO0_S2OFF_Msk (0xffu << MPDDRC_DLL_SO0_S2OFF_Pos) /**< \brief (MPDDRC_DLL_SO0) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO0_S2OFF(value) ((MPDDRC_DLL_SO0_S2OFF_Msk & ((value) << MPDDRC_DLL_SO0_S2OFF_Pos)))
#define MPDDRC_DLL_SO0_S3OFF_Pos 24
#define MPDDRC_DLL_SO0_S3OFF_Msk (0xffu << MPDDRC_DLL_SO0_S3OFF_Pos) /**< \brief (MPDDRC_DLL_SO0) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO0_S3OFF(value) ((MPDDRC_DLL_SO0_S3OFF_Msk & ((value) << MPDDRC_DLL_SO0_S3OFF_Pos)))
/* -------- MPDDRC_DLL_SO1 : (MPDDRC Offset: 0x10C) MPDDRC DLL SLAVE Offset 1 Register -------- */
#define MPDDRC_DLL_SO1_S4OFF_Pos 0
#define MPDDRC_DLL_SO1_S4OFF_Msk (0xffu << MPDDRC_DLL_SO1_S4OFF_Pos) /**< \brief (MPDDRC_DLL_SO1) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO1_S4OFF(value) ((MPDDRC_DLL_SO1_S4OFF_Msk & ((value) << MPDDRC_DLL_SO1_S4OFF_Pos)))
#define MPDDRC_DLL_SO1_S5OFF_Pos 8
#define MPDDRC_DLL_SO1_S5OFF_Msk (0xffu << MPDDRC_DLL_SO1_S5OFF_Pos) /**< \brief (MPDDRC_DLL_SO1) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO1_S5OFF(value) ((MPDDRC_DLL_SO1_S5OFF_Msk & ((value) << MPDDRC_DLL_SO1_S5OFF_Pos)))
#define MPDDRC_DLL_SO1_S6OFF_Pos 16
#define MPDDRC_DLL_SO1_S6OFF_Msk (0xffu << MPDDRC_DLL_SO1_S6OFF_Pos) /**< \brief (MPDDRC_DLL_SO1) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO1_S6OFF(value) ((MPDDRC_DLL_SO1_S6OFF_Msk & ((value) << MPDDRC_DLL_SO1_S6OFF_Pos)))
#define MPDDRC_DLL_SO1_S7OFF_Pos 24
#define MPDDRC_DLL_SO1_S7OFF_Msk (0xffu << MPDDRC_DLL_SO1_S7OFF_Pos) /**< \brief (MPDDRC_DLL_SO1) SLAVEx Delay Line Offset */
#define MPDDRC_DLL_SO1_S7OFF(value) ((MPDDRC_DLL_SO1_S7OFF_Msk & ((value) << MPDDRC_DLL_SO1_S7OFF_Pos)))
/* -------- MPDDRC_DLL_WRO : (MPDDRC Offset: 0x110) MPDDRC DLL CLKWR Offset Register -------- */
#define MPDDRC_DLL_WRO_WR0OFF_Pos 0
#define MPDDRC_DLL_WRO_WR0OFF_Msk (0xffu << MPDDRC_DLL_WRO_WR0OFF_Pos) /**< \brief (MPDDRC_DLL_WRO) CLKWRx Delay Line Offset */
#define MPDDRC_DLL_WRO_WR0OFF(value) ((MPDDRC_DLL_WRO_WR0OFF_Msk & ((value) << MPDDRC_DLL_WRO_WR0OFF_Pos)))
#define MPDDRC_DLL_WRO_WR1OFF_Pos 8
#define MPDDRC_DLL_WRO_WR1OFF_Msk (0xffu << MPDDRC_DLL_WRO_WR1OFF_Pos) /**< \brief (MPDDRC_DLL_WRO) CLKWRx Delay Line Offset */
#define MPDDRC_DLL_WRO_WR1OFF(value) ((MPDDRC_DLL_WRO_WR1OFF_Msk & ((value) << MPDDRC_DLL_WRO_WR1OFF_Pos)))
#define MPDDRC_DLL_WRO_WR2OFF_Pos 16
#define MPDDRC_DLL_WRO_WR2OFF_Msk (0xffu << MPDDRC_DLL_WRO_WR2OFF_Pos) /**< \brief (MPDDRC_DLL_WRO) CLKWRx Delay Line Offset */
#define MPDDRC_DLL_WRO_WR2OFF(value) ((MPDDRC_DLL_WRO_WR2OFF_Msk & ((value) << MPDDRC_DLL_WRO_WR2OFF_Pos)))
#define MPDDRC_DLL_WRO_WR3OFF_Pos 24
#define MPDDRC_DLL_WRO_WR3OFF_Msk (0xffu << MPDDRC_DLL_WRO_WR3OFF_Pos) /**< \brief (MPDDRC_DLL_WRO) CLKWRx Delay Line Offset */
#define MPDDRC_DLL_WRO_WR3OFF(value) ((MPDDRC_DLL_WRO_WR3OFF_Msk & ((value) << MPDDRC_DLL_WRO_WR3OFF_Pos)))
/* -------- MPDDRC_DLL_ADO : (MPDDRC Offset: 0x114) MPDDRC DLL CLKAD Offset Register -------- */
#define MPDDRC_DLL_ADO_ADOFF_Pos 0
#define MPDDRC_DLL_ADO_ADOFF_Msk (0xffu << MPDDRC_DLL_ADO_ADOFF_Pos) /**< \brief (MPDDRC_DLL_ADO) CLKAD Delay Line Offset */
#define MPDDRC_DLL_ADO_ADOFF(value) ((MPDDRC_DLL_ADO_ADOFF_Msk & ((value) << MPDDRC_DLL_ADO_ADOFF_Pos)))
/* -------- MPDDRC_DLL_SM[4] : (MPDDRC Offset: 0x118) MPDDRC DLL Status MASTER0 Register -------- */
#define MPDDRC_DLL_SM_MDINC (0x1u << 0) /**< \brief (MPDDRC_DLL_SM[4]) MASTERx Delay Increment */
#define MPDDRC_DLL_SM_MDDEC (0x1u << 1) /**< \brief (MPDDRC_DLL_SM[4]) MASTERx Delay Decrement */
#define MPDDRC_DLL_SM_MDOVF (0x1u << 2) /**< \brief (MPDDRC_DLL_SM[4]) MASTERx Delay Overflow Flag */
#define MPDDRC_DLL_SM_MDLVAL_Pos 8
#define MPDDRC_DLL_SM_MDLVAL_Msk (0xffu << MPDDRC_DLL_SM_MDLVAL_Pos) /**< \brief (MPDDRC_DLL_SM[4]) MASTERx Delay Lock Value */
#define MPDDRC_DLL_SM_MDCNT_Pos 20
#define MPDDRC_DLL_SM_MDCNT_Msk (0xffu << MPDDRC_DLL_SM_MDCNT_Pos) /**< \brief (MPDDRC_DLL_SM[4]) MASTERx Delay Counter Value */
/* -------- MPDDRC_DLL_SSL[8] : (MPDDRC Offset: 0x128) MPDDRC DLL Status SLAVE0 Register -------- */
#define MPDDRC_DLL_SSL_SDCOVF (0x1u << 0) /**< \brief (MPDDRC_DLL_SSL[8]) SLAVEx Delay Correction Overflow Flag */
#define MPDDRC_DLL_SSL_SDCUDF (0x1u << 1) /**< \brief (MPDDRC_DLL_SSL[8]) SLAVEx Delay Correction Underflow Flag */
#define MPDDRC_DLL_SSL_SDERF (0x1u << 2) /**< \brief (MPDDRC_DLL_SSL[8]) SLAVEx Delay Correction Error Flag */
#define MPDDRC_DLL_SSL_SDCNT_Pos 8
#define MPDDRC_DLL_SSL_SDCNT_Msk (0xffu << MPDDRC_DLL_SSL_SDCNT_Pos) /**< \brief (MPDDRC_DLL_SSL[8]) SLAVEx Delay Counter Value */
#define MPDDRC_DLL_SSL_SDCVAL_Pos 20
#define MPDDRC_DLL_SSL_SDCVAL_Msk (0xffu << MPDDRC_DLL_SSL_SDCVAL_Pos) /**< \brief (MPDDRC_DLL_SSL[8]) SLAVEx Delay Correction Value */
/* -------- MPDDRC_DLL_SWR[4] : (MPDDRC Offset: 0x148) MPDDRC DLL Status CLKWR0 Register -------- */
#define MPDDRC_DLL_SWR_WRDCNT_Pos 0
#define MPDDRC_DLL_SWR_WRDCNT_Msk (0xffu << MPDDRC_DLL_SWR_WRDCNT_Pos) /**< \brief (MPDDRC_DLL_SWR[4]) CLKWRx Delay Counter Value */
/* -------- MPDDRC_DLL_SAD : (MPDDRC Offset: 0x158) MPDDRC DLL Status CLKAD Register -------- */
#define MPDDRC_DLL_SAD_ADDCNT_Pos 0
#define MPDDRC_DLL_SAD_ADDCNT_Msk (0xffu << MPDDRC_DLL_SAD_ADDCNT_Pos) /**< \brief (MPDDRC_DLL_SAD) CLKAD Delay Counter Value */

/*@}*/


#endif /* _SAMA5D2_MPDDRC_COMPONENT_ */
