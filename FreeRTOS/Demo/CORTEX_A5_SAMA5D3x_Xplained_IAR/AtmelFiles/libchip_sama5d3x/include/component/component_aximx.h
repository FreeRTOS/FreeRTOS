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

#ifndef _SAMA5_AXIMX_COMPONENT_
#define _SAMA5_AXIMX_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR AXI MATRIX */
/* ============================================================================= */
/** \addtogroup SAMA5_AXIMX AXI MATRIX */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Aximx hardware registers */
typedef struct {
  WoReg AXIMX_REMAP;               /**< \brief (Aximx Offset: 0x00) Remap Register */
  RoReg Reserved1[2035];
  RoReg AXIMX_PERIPH_ID4;          /**< \brief (Aximx Offset: 0x1FD0) Peripheral ID Register 4 */
  RoReg AXIMX_PERIPH_ID5;          /**< \brief (Aximx Offset: 0x1FD4) Peripheral ID Register 5 */
  RoReg AXIMX_PERIPH_ID6;          /**< \brief (Aximx Offset: 0x1FD8) Peripheral ID Register 6 */
  RoReg AXIMX_PERIPH_ID7;          /**< \brief (Aximx Offset: 0x1FDC) Peripheral ID Register 7 */
  RoReg AXIMX_PERIPH_ID0;          /**< \brief (Aximx Offset: 0x1FE0) Peripheral ID Register 0 */
  RoReg AXIMX_PERIPH_ID1;          /**< \brief (Aximx Offset: 0x1FE4) Peripheral ID Register 1 */
  RoReg AXIMX_PERIPH_ID2;          /**< \brief (Aximx Offset: 0x1FE8) Peripheral ID Register 2 */
  RoReg AXIMX_PERIPH_ID3;          /**< \brief (Aximx Offset: 0x1FEC) Peripheral ID Register 3 */
  RoReg AXIMX_COMP_ID[4];          /**< \brief (Aximx Offset: 0x1FF0) Component ID Register */
  RoReg Reserved2[3074];
  RwReg AXIMX_AMIB3_FN_MOD_BM_ISS; /**< \brief (Aximx Offset: 0x5008) AMIB3 Bus Matrix Functionality Modification Register */
  RoReg Reserved3[6];
  RwReg AXIMX_AMIB3_FN_MOD2;       /**< \brief (Aximx Offset: 0x5024) AMIB3 Bypass Merge */
  RoReg Reserved4[62518];
  RwReg AXIMX_ASIB0_READ_QOS;      /**< \brief (Aximx Offset: 0x42100) ASIB0 Read Channel QoS Register */
  RwReg AXIMX_ASIB0_WRITE_QOS;     /**< \brief (Aximx Offset: 0x42104) ASIB0 Write Channel QoS Register */
  RoReg Reserved5[968];
  RwReg AXIMX_ASIB1_FN_MOD_AHB;    /**< \brief (Aximx Offset: 0x43028) ASIB1 AHB Functionality Modification Register */
  RoReg Reserved6[53];
  RwReg AXIMX_ASIB1_READ_QOS;      /**< \brief (Aximx Offset: 0x43100) ASIB1 Read Channel QoS Register */
  RwReg AXIMX_ASIB1_WRITE_QOS;     /**< \brief (Aximx Offset: 0x43104) ASIB1 Write Channel QoS Register */
  RwReg AXIMX_ASIB1_FN_MOD;        /**< \brief (Aximx Offset: 0x43108) ASIB1 Issuing Functionality Modification Register */
} Aximx;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- AXIMX_REMAP : (AXIMX Offset: 0x00) Remap Register -------- */
#define AXIMX_REMAP_REMAP0 (0x1u << 0) /**< \brief (AXIMX_REMAP) Remap State 0 */
#define AXIMX_REMAP_REMAP1 (0x1u << 1) /**< \brief (AXIMX_REMAP) Remap State 1 */
/* -------- AXIMX_PERIPH_ID4 : (AXIMX Offset: 0x1FD0) Peripheral ID Register 4 -------- */
#define AXIMX_PERIPH_ID4_ID_Pos 0
#define AXIMX_PERIPH_ID4_ID_Msk (0xffu << AXIMX_PERIPH_ID4_ID_Pos) /**< \brief (AXIMX_PERIPH_ID4) Peripheral ID */
#define   AXIMX_PERIPH_ID4_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID4) Part Number */
#define   AXIMX_PERIPH_ID4_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID4) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID4_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID4) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID4_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID4) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID5 : (AXIMX Offset: 0x1FD4) Peripheral ID Register 5 -------- */
#define AXIMX_PERIPH_ID5_ID_Pos 0
#define AXIMX_PERIPH_ID5_ID_Msk (0xffu << AXIMX_PERIPH_ID5_ID_Pos) /**< \brief (AXIMX_PERIPH_ID5) Peripheral ID */
#define   AXIMX_PERIPH_ID5_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID5) Part Number */
#define   AXIMX_PERIPH_ID5_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID5) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID5_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID5) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID5_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID5) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID6 : (AXIMX Offset: 0x1FD8) Peripheral ID Register 6 -------- */
#define AXIMX_PERIPH_ID6_ID_Pos 0
#define AXIMX_PERIPH_ID6_ID_Msk (0xffu << AXIMX_PERIPH_ID6_ID_Pos) /**< \brief (AXIMX_PERIPH_ID6) Peripheral ID */
#define   AXIMX_PERIPH_ID6_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID6) Part Number */
#define   AXIMX_PERIPH_ID6_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID6) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID6_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID6) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID6_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID6) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID7 : (AXIMX Offset: 0x1FDC) Peripheral ID Register 7 -------- */
#define AXIMX_PERIPH_ID7_ID_Pos 0
#define AXIMX_PERIPH_ID7_ID_Msk (0xffu << AXIMX_PERIPH_ID7_ID_Pos) /**< \brief (AXIMX_PERIPH_ID7) Peripheral ID */
#define   AXIMX_PERIPH_ID7_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID7) Part Number */
#define   AXIMX_PERIPH_ID7_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID7) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID7_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID7) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID7_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID7) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID0 : (AXIMX Offset: 0x1FE0) Peripheral ID Register 0 -------- */
#define AXIMX_PERIPH_ID0_ID_Pos 0
#define AXIMX_PERIPH_ID0_ID_Msk (0xffu << AXIMX_PERIPH_ID0_ID_Pos) /**< \brief (AXIMX_PERIPH_ID0) Peripheral ID */
#define   AXIMX_PERIPH_ID0_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID0) Part Number */
#define   AXIMX_PERIPH_ID0_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID0) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID0_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID0) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID0_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID0) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID1 : (AXIMX Offset: 0x1FE4) Peripheral ID Register 1 -------- */
#define AXIMX_PERIPH_ID1_ID_Pos 0
#define AXIMX_PERIPH_ID1_ID_Msk (0xffu << AXIMX_PERIPH_ID1_ID_Pos) /**< \brief (AXIMX_PERIPH_ID1) Peripheral ID */
#define   AXIMX_PERIPH_ID1_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID1) Part Number */
#define   AXIMX_PERIPH_ID1_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID1) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID1_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID1) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID1_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID1) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID2 : (AXIMX Offset: 0x1FE8) Peripheral ID Register 2 -------- */
#define AXIMX_PERIPH_ID2_ID_Pos 0
#define AXIMX_PERIPH_ID2_ID_Msk (0xffu << AXIMX_PERIPH_ID2_ID_Pos) /**< \brief (AXIMX_PERIPH_ID2) Peripheral ID */
#define   AXIMX_PERIPH_ID2_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID2) Part Number */
#define   AXIMX_PERIPH_ID2_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID2) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID2_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID2) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID2_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID2) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_PERIPH_ID3 : (AXIMX Offset: 0x1FEC) Peripheral ID Register 3 -------- */
#define AXIMX_PERIPH_ID3_ID_Pos 0
#define AXIMX_PERIPH_ID3_ID_Msk (0xffu << AXIMX_PERIPH_ID3_ID_Pos) /**< \brief (AXIMX_PERIPH_ID3) Peripheral ID */
#define   AXIMX_PERIPH_ID3_ID_ID0 (0x1u << 0) /**< \brief (AXIMX_PERIPH_ID3) Part Number */
#define   AXIMX_PERIPH_ID3_ID_ID4 (0x4u << 0) /**< \brief (AXIMX_PERIPH_ID3) 4KB count, JEP106 continuation code */
#define   AXIMX_PERIPH_ID3_ID_ID1 (0xB3u << 0) /**< \brief (AXIMX_PERIPH_ID3) JEP106[3:0, part number[11:8] */
#define   AXIMX_PERIPH_ID3_ID_ID2 (0xB6u << 0) /**< \brief (AXIMX_PERIPH_ID3) Revision, JEP106 code flag, JEP106[6:4] */
/* -------- AXIMX_COMP_ID[4] : (AXIMX Offset: 0x1FF0) Component ID Register -------- */
#define AXIMX_COMP_ID_ID_Pos 0
#define AXIMX_COMP_ID_ID_Msk (0xffu << AXIMX_COMP_ID_ID_Pos) /**< \brief (AXIMX_COMP_ID[4]) Component ID */
/* -------- AXIMX_AMIB3_FN_MOD_BM_ISS : (AXIMX Offset: 0x5008) AMIB3 Bus Matrix Functionality Modification Register -------- */
#define AXIMX_AMIB3_FN_MOD_BM_ISS_RD_ISS (0x1u << 0) /**< \brief (AXIMX_AMIB3_FN_MOD_BM_ISS) Read Issuing */
#define AXIMX_AMIB3_FN_MOD_BM_ISS_WR_ISS (0x1u << 1) /**< \brief (AXIMX_AMIB3_FN_MOD_BM_ISS) Write Issuing */
/* -------- AXIMX_AMIB3_FN_MOD2 : (AXIMX Offset: 0x5024) AMIB3 Bypass Merge -------- */
#define AXIMX_AMIB3_FN_MOD2_BP_MRG (0x1u << 0) /**< \brief (AXIMX_AMIB3_FN_MOD2) Bypass Merge */
/* -------- AXIMX_ASIB0_READ_QOS : (AXIMX Offset: 0x42100) ASIB0 Read Channel QoS Register -------- */
#define AXIMX_ASIB0_READ_QOS_RD_QOS_Pos 0
#define AXIMX_ASIB0_READ_QOS_RD_QOS_Msk (0xfu << AXIMX_ASIB0_READ_QOS_RD_QOS_Pos) /**< \brief (AXIMX_ASIB0_READ_QOS) Read QoS */
#define AXIMX_ASIB0_READ_QOS_RD_QOS(value) ((AXIMX_ASIB0_READ_QOS_RD_QOS_Msk & ((value) << AXIMX_ASIB0_READ_QOS_RD_QOS_Pos)))
/* -------- AXIMX_ASIB0_WRITE_QOS : (AXIMX Offset: 0x42104) ASIB0 Write Channel QoS Register -------- */
#define AXIMX_ASIB0_WRITE_QOS_WR_QOS_Pos 0
#define AXIMX_ASIB0_WRITE_QOS_WR_QOS_Msk (0xfu << AXIMX_ASIB0_WRITE_QOS_WR_QOS_Pos) /**< \brief (AXIMX_ASIB0_WRITE_QOS) Write QoS */
#define AXIMX_ASIB0_WRITE_QOS_WR_QOS(value) ((AXIMX_ASIB0_WRITE_QOS_WR_QOS_Msk & ((value) << AXIMX_ASIB0_WRITE_QOS_WR_QOS_Pos)))
/* -------- AXIMX_ASIB1_FN_MOD_AHB : (AXIMX Offset: 0x43028) ASIB1 AHB Functionality Modification Register -------- */
#define AXIMX_ASIB1_FN_MOD_AHB_RD_INCR_OVR (0x1u << 0) /**< \brief (AXIMX_ASIB1_FN_MOD_AHB) Read INCR Override */
#define AXIMX_ASIB1_FN_MOD_AHB_WR_INCR_OVR (0x1u << 1) /**< \brief (AXIMX_ASIB1_FN_MOD_AHB) Write INCR override */
#define AXIMX_ASIB1_FN_MOD_AHB_LOCK_OVR (0x1u << 2) /**< \brief (AXIMX_ASIB1_FN_MOD_AHB) Lock Override */
/* -------- AXIMX_ASIB1_READ_QOS : (AXIMX Offset: 0x43100) ASIB1 Read Channel QoS Register -------- */
#define AXIMX_ASIB1_READ_QOS_RD_QOS_Pos 0
#define AXIMX_ASIB1_READ_QOS_RD_QOS_Msk (0xfu << AXIMX_ASIB1_READ_QOS_RD_QOS_Pos) /**< \brief (AXIMX_ASIB1_READ_QOS) Read QoS */
#define AXIMX_ASIB1_READ_QOS_RD_QOS(value) ((AXIMX_ASIB1_READ_QOS_RD_QOS_Msk & ((value) << AXIMX_ASIB1_READ_QOS_RD_QOS_Pos)))
/* -------- AXIMX_ASIB1_WRITE_QOS : (AXIMX Offset: 0x43104) ASIB1 Write Channel QoS Register -------- */
#define AXIMX_ASIB1_WRITE_QOS_WR_QOS_Pos 0
#define AXIMX_ASIB1_WRITE_QOS_WR_QOS_Msk (0xfu << AXIMX_ASIB1_WRITE_QOS_WR_QOS_Pos) /**< \brief (AXIMX_ASIB1_WRITE_QOS) Write QoS */
#define AXIMX_ASIB1_WRITE_QOS_WR_QOS(value) ((AXIMX_ASIB1_WRITE_QOS_WR_QOS_Msk & ((value) << AXIMX_ASIB1_WRITE_QOS_WR_QOS_Pos)))
/* -------- AXIMX_ASIB1_FN_MOD : (AXIMX Offset: 0x43108) ASIB1 Issuing Functionality Modification Register -------- */
#define AXIMX_ASIB1_FN_MOD_RD_ISS (0x1u << 0) /**< \brief (AXIMX_ASIB1_FN_MOD) Read Issuing */
#define AXIMX_ASIB1_FN_MOD_WR_ISS (0x1u << 1) /**< \brief (AXIMX_ASIB1_FN_MOD) Write Issuing */

/*@}*/


#endif /* _SAMA5_AXIMX_COMPONENT_ */
