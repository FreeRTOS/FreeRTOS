/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _SAMA5_MPDDRC_COMPONENT_
#define _SAMA5_MPDDRC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR AHB Multi-port DDR-SDRAM Controller */
/* ============================================================================= */
/** \addtogroup SAMA5_MPDDRC AHB Multi-port DDR-SDRAM Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Mpddrc hardware registers */
typedef struct {
  RwReg MPDDRC_MR;             /**< \brief (Mpddrc Offset: 0x00) MPDDRC Mode Register */
  RwReg MPDDRC_RTR;            /**< \brief (Mpddrc Offset: 0x04) MPDDRC Refresh Timer Register */
  RwReg MPDDRC_CR;             /**< \brief (Mpddrc Offset: 0x08) MPDDRC Configuration Register */
  RwReg MPDDRC_TPR0;           /**< \brief (Mpddrc Offset: 0x0C) MPDDRC Timing Parameter 0 Register */
  RwReg MPDDRC_TPR1;           /**< \brief (Mpddrc Offset: 0x10) MPDDRC Timing Parameter 1 Register */
  RwReg MPDDRC_TPR2;           /**< \brief (Mpddrc Offset: 0x14) MPDDRC Timing Parameter 2 Register */
  RoReg Reserved1[1];
  RwReg MPDDRC_LPR;            /**< \brief (Mpddrc Offset: 0x1C) MPDDRC Low-power Register */
  RwReg MPDDRC_MD;             /**< \brief (Mpddrc Offset: 0x20) MPDDRC Memory Device Register */
  RoReg Reserved2[1];
  RwReg MPDDRC_LPDDR2_LPR;     /**< \brief (Mpddrc Offset: 0x28) MPDDRC LPDDR2 Low-power Register */
  RwReg MPDDRC_LPDDR2_CAL_MR4; /**< \brief (Mpddrc Offset: 0x2C) MPDDRC LPDDR2 Calibration and MR4 Register */
  RwReg MPDDRC_LPDDR2_TIM_CAL; /**< \brief (Mpddrc Offset: 0x30) MPDDRC LPDDR2 Timing Calibration Register */
  RwReg MPDDRC_IO_CALIBR;      /**< \brief (Mpddrc Offset: 0x34) MPDDRC IO Calibration */
  RwReg MPDDRC_OCMS;           /**< \brief (Mpddrc Offset: 0x38) MPDDRC OCMS Register */
  WoReg MPDDRC_OCMS_KEY1;      /**< \brief (Mpddrc Offset: 0x3C) MPDDRC OCMS KEY1 Register */
  WoReg MPDDRC_OCMS_KEY2;      /**< \brief (Mpddrc Offset: 0x40) MPDDRC OCMS KEY2 Register */
  RoReg Reserved3[12];
  RwReg MPDDRC_DLL_MOR;        /**< \brief (Mpddrc Offset: 0x74) MPDDRC DLL Master Offset Register */
  RwReg MPDDRC_DLL_SOR;        /**< \brief (Mpddrc Offset: 0x78) MPDDRC DLL Slave Offset Register */
  RoReg MPDDRC_DLL_MSR;        /**< \brief (Mpddrc Offset: 0x7C) MPDDRC DLL Master Status Register */
  RoReg MPDDRC_DLL_SxSR[4];    /**< \brief (Mpddrc Offset: 0x80) MPDDRC DLL Slave 0 Status Register */
  RoReg Reserved4[21];
  RwReg MPDDRC_WPCR;           /**< \brief (Mpddrc Offset: 0xE4) MPDDRC Write Protect Control Register */
  RoReg MPDDRC_WPSR;           /**< \brief (Mpddrc Offset: 0xE8) MPDDRC Write Protect Status Register */
} Mpddrc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- MPDDRC_MR : (MPDDRC Offset: 0x00) MPDDRC Mode Register -------- */
#define MPDDRC_MR_MODE_Pos 0
#define MPDDRC_MR_MODE_Msk (0x7u << MPDDRC_MR_MODE_Pos) /**< \brief (MPDDRC_MR) MPDDRC Command Mode */
#define   MPDDRC_MR_MODE_NORMAL_CMD (0x0u << 0) /**< \brief (MPDDRC_MR) Normal Mode. Any access to the MPDDRC will be decoded normally. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_NOP_CMD (0x1u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an NOP command when the DDR-SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_PRCGALL_CMD (0x2u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an "All Banks Precharge" command when the DDR-SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the SDRAM. */
#define   MPDDRC_MR_MODE_LMR_CMD (0x3u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues a "Load Mode Register" command when the DDR-SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_RFSH_CMD (0x4u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an "Auto-Refresh" Command when the DDR-SDRAM device is accessed regardless of the cycle. Previously, an "All Banks Precharge" command must be issued. To activate this mode, the command must be followed by a write to the DDR-SDRAM. */
#define   MPDDRC_MR_MODE_EXT_LMR_CMD (0x5u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an "Extended Load Mode Register" command when the SDRAM device is accessed regardless of the cycle. To activate this mode, the command must be followed by a write to the DDR-SDRAM. The write in the DDR-SDRAM must be done in the appropriate bank. */
#define   MPDDRC_MR_MODE_DEEP_CMD (0x6u << 0) /**< \brief (MPDDRC_MR) Deep power mode: Access to deep power-down mode */
#define   MPDDRC_MR_MODE_LPDDR2_CMD (0x7u << 0) /**< \brief (MPDDRC_MR) The MPDDRC issues an "LPDDR2 Mode Register" command when the Low-power DDR2-SDRAM device is accessed regardless of the cycle. To activate this mode, the "Mode Register" command must be followed by a write to the Low-power DDR2-SDRAM. */
#define MPDDRC_MR_MRS_Pos 8
#define MPDDRC_MR_MRS_Msk (0xffu << MPDDRC_MR_MRS_Pos) /**< \brief (MPDDRC_MR) Mode Register Select LPDDR2 */
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
#define MPDDRC_CR_NC_Msk (0x3u << MPDDRC_CR_NC_Pos) /**< \brief (MPDDRC_CR) Number of Column Bits. */
#define   MPDDRC_CR_NC_9 (0x0u << 0) /**< \brief (MPDDRC_CR) 9 DDR column bits */
#define   MPDDRC_CR_NC_10 (0x1u << 0) /**< \brief (MPDDRC_CR) 10 DDR column bits */
#define   MPDDRC_CR_NC_11 (0x2u << 0) /**< \brief (MPDDRC_CR) 11 DDR column bits */
#define   MPDDRC_CR_NC_12 (0x3u << 0) /**< \brief (MPDDRC_CR) 12 DDR column bits */
#define MPDDRC_CR_NR_Pos 2
#define MPDDRC_CR_NR_Msk (0x3u << MPDDRC_CR_NR_Pos) /**< \brief (MPDDRC_CR) Number of Row Bits */
#define   MPDDRC_CR_NR_11 (0x0u << 2) /**< \brief (MPDDRC_CR) 11 row bits */
#define   MPDDRC_CR_NR_12 (0x1u << 2) /**< \brief (MPDDRC_CR) 12 row bits */
#define   MPDDRC_CR_NR_13 (0x2u << 2) /**< \brief (MPDDRC_CR) 13 row bits */
#define   MPDDRC_CR_NR_14 (0x3u << 2) /**< \brief (MPDDRC_CR) 14 row bits */
#define MPDDRC_CR_CAS_Pos 4
#define MPDDRC_CR_CAS_Msk (0x7u << MPDDRC_CR_CAS_Pos) /**< \brief (MPDDRC_CR) CAS Latency */
#define   MPDDRC_CR_CAS_3_DDR2 (0x3u << 4) /**< \brief (MPDDRC_CR) DDR2 CAS Latency 3 */
#define   MPDDRC_CR_CAS_3_LPDDR2 (0x3u << 4) /**< \brief (MPDDRC_CR) LPDDR2 CAS Latency 3 */
#define   MPDDRC_CR_CAS_4_DDR2 (0x4u << 4) /**< \brief (MPDDRC_CR) DDR2 CAS Latency 4 */
#define   MPDDRC_CR_CAS_4_LPDDR2 (0x4u << 4) /**< \brief (MPDDRC_CR) LPDDR2 CAS Latency 4 */
#define   MPDDRC_CR_CAS_5_DDR2 (0x5u << 4) /**< \brief (MPDDRC_CR) DDR2 CAS Latency 5 */
#define   MPDDRC_CR_CAS_5_LPDDR2 (0x5u << 4) /**< \brief (MPDDRC_CR) LPDDR2 CAS Latency 5 */
#define   MPDDRC_CR_CAS_6_DDR2 (0x6u << 4) /**< \brief (MPDDRC_CR) DDR2 CAS Latency 6 */
#define MPDDRC_CR_DLL (0x1u << 7) /**< \brief (MPDDRC_CR) Reset DLL */
#define   MPDDRC_CR_DLL_RESET_DISABLED (0x0u << 7) /**< \brief (MPDDRC_CR) Disable DLL reset. */
#define   MPDDRC_CR_DLL_RESET_ENABLED (0x1u << 7) /**< \brief (MPDDRC_CR) Enable DLL reset. */
#define MPDDRC_CR_DIC_DS (0x1u << 8) /**< \brief (MPDDRC_CR) Output Driver Impedance Control (Drive Strength) */
#define MPDDRC_CR_DIS_DLL (0x1u << 9) /**< \brief (MPDDRC_CR) DISABLE DLL */
#define MPDDRC_CR_ZQ_Pos 10
#define MPDDRC_CR_ZQ_Msk (0x3u << MPDDRC_CR_ZQ_Pos) /**< \brief (MPDDRC_CR) ZQ Calibration */
#define   MPDDRC_CR_ZQ_INIT (0x0u << 10) /**< \brief (MPDDRC_CR) Calibration command after initialization */
#define   MPDDRC_CR_ZQ_LONG (0x1u << 10) /**< \brief (MPDDRC_CR) Long calibration */
#define   MPDDRC_CR_ZQ_SHORT (0x2u << 10) /**< \brief (MPDDRC_CR) Short calibration */
#define   MPDDRC_CR_ZQ_RESET (0x3u << 10) /**< \brief (MPDDRC_CR) ZQ Reset */
#define MPDDRC_CR_OCD_Pos 12
#define MPDDRC_CR_OCD_Msk (0x7u << MPDDRC_CR_OCD_Pos) /**< \brief (MPDDRC_CR) Off-chip Driver */
#define MPDDRC_CR_OCD(value) ((MPDDRC_CR_OCD_Msk & ((value) << MPDDRC_CR_OCD_Pos)))
#define MPDDRC_CR_DQMS (0x1u << 16) /**< \brief (MPDDRC_CR) Mask Data is Shared */
#define   MPDDRC_CR_DQMS_NOT_SHARED (0x0u << 16) /**< \brief (MPDDRC_CR) DQM is not shared with another controller. */
#define   MPDDRC_CR_DQMS_SHARED (0x1u << 16) /**< \brief (MPDDRC_CR) DQM is shared with another controller. */
#define MPDDRC_CR_ENRDM (0x1u << 17) /**< \brief (MPDDRC_CR) Enable Read Measure */
#define   MPDDRC_CR_ENRDM_OFF (0x0u << 17) /**< \brief (MPDDRC_CR) DQS/DDR_DATA phase error correction is disabled. */
#define   MPDDRC_CR_ENRDM_ON (0x1u << 17) /**< \brief (MPDDRC_CR) DQS/DDR_DATA phase error correction is enabled. */
#define MPDDRC_CR_NB (0x1u << 20) /**< \brief (MPDDRC_CR) Number of Banks. */
#define   MPDDRC_CR_NB_4 (0x0u << 20) /**< \brief (MPDDRC_CR) 4 banks */
#define   MPDDRC_CR_NB_8 (0x1u << 20) /**< \brief (MPDDRC_CR) 8 banks */
#define MPDDRC_CR_NDQS (0x1u << 21) /**< \brief (MPDDRC_CR) Not DQS: */
#define   MPDDRC_CR_NDQS_ENABLED (0x0u << 21) /**< \brief (MPDDRC_CR) Not DQS is enabled. */
#define   MPDDRC_CR_NDQS_DISABLED (0x1u << 21) /**< \brief (MPDDRC_CR) Not DQS is disabled. */
#define MPDDRC_CR_DECOD (0x1u << 22) /**< \brief (MPDDRC_CR) Type of Decoding */
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
#define MPDDRC_TPR1_TRFC_Msk (0x1fu << MPDDRC_TPR1_TRFC_Pos) /**< \brief (MPDDRC_TPR1) Row Cycle Delay */
#define MPDDRC_TPR1_TRFC(value) ((MPDDRC_TPR1_TRFC_Msk & ((value) << MPDDRC_TPR1_TRFC_Pos)))
#define MPDDRC_TPR1_TXSNR_Pos 8
#define MPDDRC_TPR1_TXSNR_Msk (0xffu << MPDDRC_TPR1_TXSNR_Pos) /**< \brief (MPDDRC_TPR1) Exit Self Refresh Delay to Non Read Command */
#define MPDDRC_TPR1_TXSNR(value) ((MPDDRC_TPR1_TXSNR_Msk & ((value) << MPDDRC_TPR1_TXSNR_Pos)))
#define MPDDRC_TPR1_TXSRD_Pos 16
#define MPDDRC_TPR1_TXSRD_Msk (0xffu << MPDDRC_TPR1_TXSRD_Pos) /**< \brief (MPDDRC_TPR1) Exit Self Refresh Delay to Read Command */
#define MPDDRC_TPR1_TXSRD(value) ((MPDDRC_TPR1_TXSRD_Msk & ((value) << MPDDRC_TPR1_TXSRD_Pos)))
#define MPDDRC_TPR1_TXP_Pos 24
#define MPDDRC_TPR1_TXP_Msk (0xfu << MPDDRC_TPR1_TXP_Pos) /**< \brief (MPDDRC_TPR1) Exit Power-down Delay to First Command */
#define MPDDRC_TPR1_TXP(value) ((MPDDRC_TPR1_TXP_Msk & ((value) << MPDDRC_TPR1_TXP_Pos)))
/* -------- MPDDRC_TPR2 : (MPDDRC Offset: 0x14) MPDDRC Timing Parameter 2 Register -------- */
#define MPDDRC_TPR2_TXARD_Pos 0
#define MPDDRC_TPR2_TXARD_Msk (0xfu << MPDDRC_TPR2_TXARD_Pos) /**< \brief (MPDDRC_TPR2) Exit Active Power Down Delay to Read Command in Mode "Fast Exit". */
#define MPDDRC_TPR2_TXARD(value) ((MPDDRC_TPR2_TXARD_Msk & ((value) << MPDDRC_TPR2_TXARD_Pos)))
#define MPDDRC_TPR2_TXARDS_Pos 4
#define MPDDRC_TPR2_TXARDS_Msk (0xfu << MPDDRC_TPR2_TXARDS_Pos) /**< \brief (MPDDRC_TPR2) Exit Active Power Down Delay to Read Command in Mode "Slow Exit". */
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
#define   MPDDRC_LPR_LPCB_DISABLED (0x0u << 0) /**< \brief (MPDDRC_LPR) Low-power Feature is inhibited. No power-down, self refresh and deep-power modes are issued to the DDR-SDRAM device. */
#define   MPDDRC_LPR_LPCB_SELFREFRESH (0x1u << 0) /**< \brief (MPDDRC_LPR) The MPDDRC issues a Self Refresh command to the DDR-SDRAM device, the clock(s) is/are de-activated and the CKE signal is set low. The DDR-SDRAM device leaves the self refresh mode when accessed and reenters it after the access. */
#define   MPDDRC_LPR_LPCB_POWERDOWN (0x2u << 0) /**< \brief (MPDDRC_LPR) The MPDDRC issues a Power-down Command to the DDR-SDRAM device after each access, the CKE signal is set low. The DDR-SDRAM device leaves the power-down mode when accessed and reenters it after the access. */
#define   MPDDRC_LPR_LPCB_DEEP_PWD (0x3u << 0) /**< \brief (MPDDRC_LPR) The MPDDRC issues a Deep Power-down command to the Low-power DDR-SDRAM device. */
#define MPDDRC_LPR_CLK_FR (0x1u << 2) /**< \brief (MPDDRC_LPR) Clock Frozen Command Bit */
#define   MPDDRC_LPR_CLK_FR_DISABLED (0x0u << 2) /**< \brief (MPDDRC_LPR) Clock(s) is/are not frozen. */
#define   MPDDRC_LPR_CLK_FR_ENABLED (0x1u << 2) /**< \brief (MPDDRC_LPR) Clock(s) is/are frozen. */
#define MPDDRC_LPR_LPDDR2_PWOFF (0x1u << 3) /**< \brief (MPDDRC_LPR) LPDDR2 Power Off Bit */
#define   MPDDRC_LPR_LPDDR2_PWOFF_DISABLED (0x0u << 3) /**< \brief (MPDDRC_LPR) No power off sequence applied to LPDDR2. */
#define   MPDDRC_LPR_LPDDR2_PWOFF_ENABLED (0x1u << 3) /**< \brief (MPDDRC_LPR) A power off sequence is applied to the LPDDR2 device. CKE is forced low. */
#define MPDDRC_LPR_PASR_Pos 4
#define MPDDRC_LPR_PASR_Msk (0x7u << MPDDRC_LPR_PASR_Pos) /**< \brief (MPDDRC_LPR) Partial Array Self Refresh */
#define MPDDRC_LPR_PASR(value) ((MPDDRC_LPR_PASR_Msk & ((value) << MPDDRC_LPR_PASR_Pos)))
#define MPDDRC_LPR_DS_Pos 8
#define MPDDRC_LPR_DS_Msk (0x7u << MPDDRC_LPR_DS_Pos) /**< \brief (MPDDRC_LPR) Drive Strength */
#define MPDDRC_LPR_DS(value) ((MPDDRC_LPR_DS_Msk & ((value) << MPDDRC_LPR_DS_Pos)))
#define MPDDRC_LPR_TIMEOUT_Pos 12
#define MPDDRC_LPR_TIMEOUT_Msk (0x3u << MPDDRC_LPR_TIMEOUT_Pos) /**< \brief (MPDDRC_LPR) Enter Low-power Mode */
#define   MPDDRC_LPR_TIMEOUT_0 (0x0u << 12) /**< \brief (MPDDRC_LPR) The SDRAM controller activates the SDRAM low-power mode immediately after the end of the last transfer. */
#define   MPDDRC_LPR_TIMEOUT_64 (0x1u << 12) /**< \brief (MPDDRC_LPR) The SDRAM controller activates the SDRAM low-power mode 64 clock cycles after the end of the last transfer. */
#define   MPDDRC_LPR_TIMEOUT_128 (0x2u << 12) /**< \brief (MPDDRC_LPR) The SDRAM controller activates the SDRAM low-power mode 128 clock cycles after the end of the last transfer. */
#define MPDDRC_LPR_APDE (0x1u << 16) /**< \brief (MPDDRC_LPR) Active Power Down Exit Time */
#define   MPDDRC_LPR_APDE_FAST (0x0u << 16) /**< \brief (MPDDRC_LPR) Fast Exit. */
#define   MPDDRC_LPR_APDE_SLOW (0x1u << 16) /**< \brief (MPDDRC_LPR) Low Exit. */
#define MPDDRC_LPR_UPD_MR_Pos 20
#define MPDDRC_LPR_UPD_MR_Msk (0x3u << MPDDRC_LPR_UPD_MR_Pos) /**< \brief (MPDDRC_LPR) Update Load Mode Register and Extended Mode Register */
#define MPDDRC_LPR_UPD_MR(value) ((MPDDRC_LPR_UPD_MR_Msk & ((value) << MPDDRC_LPR_UPD_MR_Pos)))
/* -------- MPDDRC_MD : (MPDDRC Offset: 0x20) MPDDRC Memory Device Register -------- */
#define MPDDRC_MD_MD_Pos 0
#define MPDDRC_MD_MD_Msk (0x7u << MPDDRC_MD_MD_Pos) /**< \brief (MPDDRC_MD) Memory Device */
#define   MPDDRC_MD_MD_LPDDR_SDRAM (0x3u << 0) /**< \brief (MPDDRC_MD) Low-power DDR1-SDRAM */
#define   MPDDRC_MD_MD_DDR2_SDRAM (0x6u << 0) /**< \brief (MPDDRC_MD) DDR2-SDRAM */
#define   MPDDRC_MD_MD_LPDDR2_SDRAM (0x7u << 0) /**< \brief (MPDDRC_MD) Low-Power DDR2-SDRAM */
#define MPDDRC_MD_DBW (0x1u << 4) /**< \brief (MPDDRC_MD) Data Bus Width */
#define   MPDDRC_MD_DBW_32_BITS (0x0u << 4) /**< \brief (MPDDRC_MD) Data bus width is 32 bits. */
#define   MPDDRC_MD_DBW_16_BITS (0x1u << 4) /**< \brief (MPDDRC_MD) Data bus width is 16 bits. */
/* -------- MPDDRC_LPDDR2_LPR : (MPDDRC Offset: 0x28) MPDDRC LPDDR2 Low-power Register -------- */
#define MPDDRC_LPDDR2_LPR_BK_MASK_Pos 0
#define MPDDRC_LPDDR2_LPR_BK_MASK_Msk (0xffu << MPDDRC_LPDDR2_LPR_BK_MASK_Pos) /**< \brief (MPDDRC_LPDDR2_LPR)  */
#define MPDDRC_LPDDR2_LPR_BK_MASK(value) ((MPDDRC_LPDDR2_LPR_BK_MASK_Msk & ((value) << MPDDRC_LPDDR2_LPR_BK_MASK_Pos)))
#define MPDDRC_LPDDR2_LPR_SEG_MASK_Pos 8
#define MPDDRC_LPDDR2_LPR_SEG_MASK_Msk (0xffffu << MPDDRC_LPDDR2_LPR_SEG_MASK_Pos) /**< \brief (MPDDRC_LPDDR2_LPR) Segment Mask Bit */
#define MPDDRC_LPDDR2_LPR_SEG_MASK(value) ((MPDDRC_LPDDR2_LPR_SEG_MASK_Msk & ((value) << MPDDRC_LPDDR2_LPR_SEG_MASK_Pos)))
#define MPDDRC_LPDDR2_LPR_DS_Pos 24
#define MPDDRC_LPDDR2_LPR_DS_Msk (0xfu << MPDDRC_LPDDR2_LPR_DS_Pos) /**< \brief (MPDDRC_LPDDR2_LPR) Drive strength */
#define MPDDRC_LPDDR2_LPR_DS(value) ((MPDDRC_LPDDR2_LPR_DS_Msk & ((value) << MPDDRC_LPDDR2_LPR_DS_Pos)))
/* -------- MPDDRC_LPDDR2_CAL_MR4 : (MPDDRC Offset: 0x2C) MPDDRC LPDDR2 Calibration and MR4 Register -------- */
#define MPDDRC_LPDDR2_CAL_MR4_COUNT_CAL_Pos 0
#define MPDDRC_LPDDR2_CAL_MR4_COUNT_CAL_Msk (0xffffu << MPDDRC_LPDDR2_CAL_MR4_COUNT_CAL_Pos) /**< \brief (MPDDRC_LPDDR2_CAL_MR4) LPDDR2 Calibration Timer Count */
#define MPDDRC_LPDDR2_CAL_MR4_COUNT_CAL(value) ((MPDDRC_LPDDR2_CAL_MR4_COUNT_CAL_Msk & ((value) << MPDDRC_LPDDR2_CAL_MR4_COUNT_CAL_Pos)))
#define MPDDRC_LPDDR2_CAL_MR4_MR4_READ_Pos 16
#define MPDDRC_LPDDR2_CAL_MR4_MR4_READ_Msk (0xffffu << MPDDRC_LPDDR2_CAL_MR4_MR4_READ_Pos) /**< \brief (MPDDRC_LPDDR2_CAL_MR4) Mode Register 4 Read Interval */
#define MPDDRC_LPDDR2_CAL_MR4_MR4_READ(value) ((MPDDRC_LPDDR2_CAL_MR4_MR4_READ_Msk & ((value) << MPDDRC_LPDDR2_CAL_MR4_MR4_READ_Pos)))
/* -------- MPDDRC_LPDDR2_TIM_CAL : (MPDDRC Offset: 0x30) MPDDRC LPDDR2 Timing Calibration Register -------- */
#define MPDDRC_LPDDR2_TIM_CAL_ZQCS_Pos 0
#define MPDDRC_LPDDR2_TIM_CAL_ZQCS_Msk (0xffu << MPDDRC_LPDDR2_TIM_CAL_ZQCS_Pos) /**< \brief (MPDDRC_LPDDR2_TIM_CAL) ZQ Calibration Short */
#define MPDDRC_LPDDR2_TIM_CAL_ZQCS(value) ((MPDDRC_LPDDR2_TIM_CAL_ZQCS_Msk & ((value) << MPDDRC_LPDDR2_TIM_CAL_ZQCS_Pos)))
/* -------- MPDDRC_IO_CALIBR : (MPDDRC Offset: 0x34) MPDDRC IO Calibration -------- */
#define MPDDRC_IO_CALIBR_RDIV_Pos 0
#define MPDDRC_IO_CALIBR_RDIV_Msk (0x7u << MPDDRC_IO_CALIBR_RDIV_Pos) /**< \brief (MPDDRC_IO_CALIBR) Resistor Divider, output driver impedance */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_34 (0x1u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 34,3 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_40 (0x2u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 40 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_333 (0x2u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 33,3 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_48 (0x3u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ =48 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_60 (0x4u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ =60 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_50 (0x4u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ =50 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_80 (0x6u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 80 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_667 (0x6u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 66,7 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_120 (0x7u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 120 Ohm */
#define   MPDDRC_IO_CALIBR_RDIV_RZQ_100 (0x7u << 0) /**< \brief (MPDDRC_IO_CALIBR) RZQ = 100 Ohm */
#define MPDDRC_IO_CALIBR_TZQIO_Pos 8
#define MPDDRC_IO_CALIBR_TZQIO_Msk (0x7u << MPDDRC_IO_CALIBR_TZQIO_Pos) /**< \brief (MPDDRC_IO_CALIBR) IO Calibration */
#define MPDDRC_IO_CALIBR_TZQIO(value) ((MPDDRC_IO_CALIBR_TZQIO_Msk & ((value) << MPDDRC_IO_CALIBR_TZQIO_Pos)))
#define MPDDRC_IO_CALIBR_CALCODEP_Pos 16
#define MPDDRC_IO_CALIBR_CALCODEP_Msk (0xfu << MPDDRC_IO_CALIBR_CALCODEP_Pos) /**< \brief (MPDDRC_IO_CALIBR) Number of Transistor P */
#define MPDDRC_IO_CALIBR_CALCODEP(value) ((MPDDRC_IO_CALIBR_CALCODEP_Msk & ((value) << MPDDRC_IO_CALIBR_CALCODEP_Pos)))
#define MPDDRC_IO_CALIBR_CALCODEN_Pos 20
#define MPDDRC_IO_CALIBR_CALCODEN_Msk (0xfu << MPDDRC_IO_CALIBR_CALCODEN_Pos) /**< \brief (MPDDRC_IO_CALIBR) Number of Transistor N */
#define MPDDRC_IO_CALIBR_CALCODEN(value) ((MPDDRC_IO_CALIBR_CALCODEN_Msk & ((value) << MPDDRC_IO_CALIBR_CALCODEN_Pos)))
/* -------- MPDDRC_OCMS : (MPDDRC Offset: 0x38) MPDDRC OCMS Register -------- */
#define MPDDRC_OCMS_SCR_EN (0x1u << 0) /**< \brief (MPDDRC_OCMS) Scrambling enable */
/* -------- MPDDRC_OCMS_KEY1 : (MPDDRC Offset: 0x3C) MPDDRC OCMS KEY1 Register -------- */
#define MPDDRC_OCMS_KEY1_KEY1_Pos 0
#define MPDDRC_OCMS_KEY1_KEY1_Msk (0xffffffffu << MPDDRC_OCMS_KEY1_KEY1_Pos) /**< \brief (MPDDRC_OCMS_KEY1) Off Chip Memory Scrambling (OCMS) Key Part 1 */
#define MPDDRC_OCMS_KEY1_KEY1(value) ((MPDDRC_OCMS_KEY1_KEY1_Msk & ((value) << MPDDRC_OCMS_KEY1_KEY1_Pos)))
/* -------- MPDDRC_OCMS_KEY2 : (MPDDRC Offset: 0x40) MPDDRC OCMS KEY2 Register -------- */
#define MPDDRC_OCMS_KEY2_KEY2_Pos 0
#define MPDDRC_OCMS_KEY2_KEY2_Msk (0xffffffffu << MPDDRC_OCMS_KEY2_KEY2_Pos) /**< \brief (MPDDRC_OCMS_KEY2) Off Chip Memory Scrambling (OCMS) Key Part 2 */
#define MPDDRC_OCMS_KEY2_KEY2(value) ((MPDDRC_OCMS_KEY2_KEY2_Msk & ((value) << MPDDRC_OCMS_KEY2_KEY2_Pos)))
/* -------- MPDDRC_DLL_MOR : (MPDDRC Offset: 0x74) MPDDRC DLL Master Offset Register -------- */
#define MPDDRC_DLL_MOR_MOFF_Pos 0
#define MPDDRC_DLL_MOR_MOFF_Msk (0xfu << MPDDRC_DLL_MOR_MOFF_Pos) /**< \brief (MPDDRC_DLL_MOR) DLL Master Delay Line Offset */
#define MPDDRC_DLL_MOR_MOFF(value) ((MPDDRC_DLL_MOR_MOFF_Msk & ((value) << MPDDRC_DLL_MOR_MOFF_Pos)))
#define MPDDRC_DLL_MOR_CLK90OFF_Pos 8
#define MPDDRC_DLL_MOR_CLK90OFF_Msk (0x1fu << MPDDRC_DLL_MOR_CLK90OFF_Pos) /**< \brief (MPDDRC_DLL_MOR) DLL CLK90 Delay Line Offset */
#define MPDDRC_DLL_MOR_CLK90OFF(value) ((MPDDRC_DLL_MOR_CLK90OFF_Msk & ((value) << MPDDRC_DLL_MOR_CLK90OFF_Pos)))
#define MPDDRC_DLL_MOR_SELOFF (0x1u << 16) /**< \brief (MPDDRC_DLL_MOR) DLL Offset Selection */
/* -------- MPDDRC_DLL_SOR : (MPDDRC Offset: 0x78) MPDDRC DLL Slave Offset Register -------- */
#define MPDDRC_DLL_SOR_S0OFF_Pos 0
#define MPDDRC_DLL_SOR_S0OFF_Msk (0x1fu << MPDDRC_DLL_SOR_S0OFF_Pos) /**< \brief (MPDDRC_DLL_SOR) DLL Slave 0 Delay Line Offset ([x=0..3]) */
#define MPDDRC_DLL_SOR_S0OFF(value) ((MPDDRC_DLL_SOR_S0OFF_Msk & ((value) << MPDDRC_DLL_SOR_S0OFF_Pos)))
#define MPDDRC_DLL_SOR_S1OFF_Pos 8
#define MPDDRC_DLL_SOR_S1OFF_Msk (0x1fu << MPDDRC_DLL_SOR_S1OFF_Pos) /**< \brief (MPDDRC_DLL_SOR) DLL Slave 1 Delay Line Offset ([x=0..3]) */
#define MPDDRC_DLL_SOR_S1OFF(value) ((MPDDRC_DLL_SOR_S1OFF_Msk & ((value) << MPDDRC_DLL_SOR_S1OFF_Pos)))
#define MPDDRC_DLL_SOR_S2OFF_Pos 16
#define MPDDRC_DLL_SOR_S2OFF_Msk (0x1fu << MPDDRC_DLL_SOR_S2OFF_Pos) /**< \brief (MPDDRC_DLL_SOR) DLL Slave 2 Delay Line Offset ([x=0..3]) */
#define MPDDRC_DLL_SOR_S2OFF(value) ((MPDDRC_DLL_SOR_S2OFF_Msk & ((value) << MPDDRC_DLL_SOR_S2OFF_Pos)))
#define MPDDRC_DLL_SOR_S3OFF_Pos 24
#define MPDDRC_DLL_SOR_S3OFF_Msk (0x1fu << MPDDRC_DLL_SOR_S3OFF_Pos) /**< \brief (MPDDRC_DLL_SOR) DLL Slave 3 Delay Line Offset ([x=0..3]) */
#define MPDDRC_DLL_SOR_S3OFF(value) ((MPDDRC_DLL_SOR_S3OFF_Msk & ((value) << MPDDRC_DLL_SOR_S3OFF_Pos)))
/* -------- MPDDRC_DLL_MSR : (MPDDRC Offset: 0x7C) MPDDRC DLL Master Status Register -------- */
#define MPDDRC_DLL_MSR_MDINC (0x1u << 0) /**< \brief (MPDDRC_DLL_MSR) DLL Master Delay Increment */
#define MPDDRC_DLL_MSR_MDDEC (0x1u << 1) /**< \brief (MPDDRC_DLL_MSR) DLL Master Delay Decrement */
#define MPDDRC_DLL_MSR_MDOVF (0x1u << 2) /**< \brief (MPDDRC_DLL_MSR) DLL Master Delay Overflow Flag */
#define MPDDRC_DLL_MSR_MDVAL_Pos 8
#define MPDDRC_DLL_MSR_MDVAL_Msk (0xffu << MPDDRC_DLL_MSR_MDVAL_Pos) /**< \brief (MPDDRC_DLL_MSR) DLL Master Delay Value */
/* -------- MPDDRC_DLL_S0SR : (MPDDRC Offset: 0x80) MPDDRC DLL Slave 0 Status Register -------- */
#define MPDDRC_DLL_S0SR_SDCOVF (0x1u << 0) /**< \brief (MPDDRC_DLL_S0SR) DLL Slave x Delay Correction Overflow Flag */
#define MPDDRC_DLL_S0SR_SDCUDF (0x1u << 1) /**< \brief (MPDDRC_DLL_S0SR) DLL Slave x Delay Correction Underflow Flag */
#define MPDDRC_DLL_S0SR_SDERF (0x1u << 2) /**< \brief (MPDDRC_DLL_S0SR) DLL Slave x Delay Correction Error Flag */
#define MPDDRC_DLL_S0SR_SDVAL_Pos 8
#define MPDDRC_DLL_S0SR_SDVAL_Msk (0xffu << MPDDRC_DLL_S0SR_SDVAL_Pos) /**< \brief (MPDDRC_DLL_S0SR) DLL Slave x Delay Value */
#define MPDDRC_DLL_S0SR_SDCVAL_Pos 16
#define MPDDRC_DLL_S0SR_SDCVAL_Msk (0xffu << MPDDRC_DLL_S0SR_SDCVAL_Pos) /**< \brief (MPDDRC_DLL_S0SR) DLL Slave x Delay Correction Value */
/* -------- MPDDRC_DLL_S1SR : (MPDDRC Offset: 0x84) MPDDRC DLL Slave 1 Status Register -------- */
#define MPDDRC_DLL_S1SR_SDCOVF (0x1u << 0) /**< \brief (MPDDRC_DLL_S1SR) DLL Slave x Delay Correction Overflow Flag */
#define MPDDRC_DLL_S1SR_SDCUDF (0x1u << 1) /**< \brief (MPDDRC_DLL_S1SR) DLL Slave x Delay Correction Underflow Flag */
#define MPDDRC_DLL_S1SR_SDERF (0x1u << 2) /**< \brief (MPDDRC_DLL_S1SR) DLL Slave x Delay Correction Error Flag */
#define MPDDRC_DLL_S1SR_SDVAL_Pos 8
#define MPDDRC_DLL_S1SR_SDVAL_Msk (0xffu << MPDDRC_DLL_S1SR_SDVAL_Pos) /**< \brief (MPDDRC_DLL_S1SR) DLL Slave x Delay Value */
#define MPDDRC_DLL_S1SR_SDCVAL_Pos 16
#define MPDDRC_DLL_S1SR_SDCVAL_Msk (0xffu << MPDDRC_DLL_S1SR_SDCVAL_Pos) /**< \brief (MPDDRC_DLL_S1SR) DLL Slave x Delay Correction Value */
/* -------- MPDDRC_DLL_S2SR : (MPDDRC Offset: 0x88) MPDDRC DLL Slave 2 Status Register -------- */
#define MPDDRC_DLL_S2SR_SDCOVF (0x1u << 0) /**< \brief (MPDDRC_DLL_S2SR) DLL Slave x Delay Correction Overflow Flag */
#define MPDDRC_DLL_S2SR_SDCUDF (0x1u << 1) /**< \brief (MPDDRC_DLL_S2SR) DLL Slave x Delay Correction Underflow Flag */
#define MPDDRC_DLL_S2SR_SDERF (0x1u << 2) /**< \brief (MPDDRC_DLL_S2SR) DLL Slave x Delay Correction Error Flag */
#define MPDDRC_DLL_S2SR_SDVAL_Pos 8
#define MPDDRC_DLL_S2SR_SDVAL_Msk (0xffu << MPDDRC_DLL_S2SR_SDVAL_Pos) /**< \brief (MPDDRC_DLL_S2SR) DLL Slave x Delay Value */
#define MPDDRC_DLL_S2SR_SDCVAL_Pos 16
#define MPDDRC_DLL_S2SR_SDCVAL_Msk (0xffu << MPDDRC_DLL_S2SR_SDCVAL_Pos) /**< \brief (MPDDRC_DLL_S2SR) DLL Slave x Delay Correction Value */
/* -------- MPDDRC_DLL_S3SR : (MPDDRC Offset: 0x8C) MPDDRC DLL Slave 3 Status Register -------- */
#define MPDDRC_DLL_S3SR_SDCOVF (0x1u << 0) /**< \brief (MPDDRC_DLL_S3SR) DLL Slave x Delay Correction Overflow Flag */
#define MPDDRC_DLL_S3SR_SDCUDF (0x1u << 1) /**< \brief (MPDDRC_DLL_S3SR) DLL Slave x Delay Correction Underflow Flag */
#define MPDDRC_DLL_S3SR_SDERF (0x1u << 2) /**< \brief (MPDDRC_DLL_S3SR) DLL Slave x Delay Correction Error Flag */
#define MPDDRC_DLL_S3SR_SDVAL_Pos 8
#define MPDDRC_DLL_S3SR_SDVAL_Msk (0xffu << MPDDRC_DLL_S3SR_SDVAL_Pos) /**< \brief (MPDDRC_DLL_S3SR) DLL Slave x Delay Value */
#define MPDDRC_DLL_S3SR_SDCVAL_Pos 16
#define MPDDRC_DLL_S3SR_SDCVAL_Msk (0xffu << MPDDRC_DLL_S3SR_SDCVAL_Pos) /**< \brief (MPDDRC_DLL_S3SR) DLL Slave x Delay Correction Value */
/* -------- MPDDRC_WPCR : (MPDDRC Offset: 0xE4) MPDDRC Write Protect Control Register -------- */
#define MPDDRC_WPCR_WPEN (0x1u << 0) /**< \brief (MPDDRC_WPCR) Write Protection Enable */
#define MPDDRC_WPCR_WPKEY_Pos 8
#define MPDDRC_WPCR_WPKEY_Msk (0xffffffu << MPDDRC_WPCR_WPKEY_Pos) /**< \brief (MPDDRC_WPCR) Write Protection KEY */
#define MPDDRC_WPCR_WPKEY(value) ((MPDDRC_WPCR_WPKEY_Msk & ((value) << MPDDRC_WPCR_WPKEY_Pos)))
/* -------- MPDDRC_WPSR : (MPDDRC Offset: 0xE8) MPDDRC Write Protect Status Register -------- */
#define MPDDRC_WPSR_WPVS (0x1u << 0) /**< \brief (MPDDRC_WPSR) Write Protection Enable */
#define MPDDRC_WPSR_WPVSRC_Pos 8
#define MPDDRC_WPSR_WPVSRC_Msk (0xffffu << MPDDRC_WPSR_WPVSRC_Pos) /**< \brief (MPDDRC_WPSR) Write Protection Violation Source */

/*@}*/


#endif /* _SAMA5_MPDDRC_COMPONENT_ */
