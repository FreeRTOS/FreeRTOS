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

#ifndef _SAMA5D2_L2CC_COMPONENT_
#define _SAMA5D2_L2CC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR L2 Cache Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_L2CC L2 Cache Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief L2cc hardware registers */
typedef struct {
  __I  uint32_t L2CC_IDR;        /**< \brief (L2cc Offset: 0x000) Cache ID Register */
  __I  uint32_t L2CC_TYPR;       /**< \brief (L2cc Offset: 0x004) Cache Type Register */
  __I  uint32_t Reserved1[62];
  __IO uint32_t L2CC_CR;         /**< \brief (L2cc Offset: 0x100) Control Register */
  __IO uint32_t L2CC_ACR;        /**< \brief (L2cc Offset: 0x104) Auxiliary Control Register */
  __IO uint32_t L2CC_TRCR;       /**< \brief (L2cc Offset: 0x108) Tag RAM Control Register */
  __IO uint32_t L2CC_DRCR;       /**< \brief (L2cc Offset: 0x10C) Data RAM Control Register */
  __I  uint32_t Reserved2[60];
  __IO uint32_t L2CC_ECR;        /**< \brief (L2cc Offset: 0x200) Event Counter Control Register */
  __IO uint32_t L2CC_ECFGR1;     /**< \brief (L2cc Offset: 0x204) Event Counter 1 Configuration Register */
  __IO uint32_t L2CC_ECFGR0;     /**< \brief (L2cc Offset: 0x208) Event Counter 0 Configuration Register */
  __IO uint32_t L2CC_EVR1;       /**< \brief (L2cc Offset: 0x20C) Event Counter 1 Value Register */
  __IO uint32_t L2CC_EVR0;       /**< \brief (L2cc Offset: 0x210) Event Counter 0 Value Register */
  __IO uint32_t L2CC_IMR;        /**< \brief (L2cc Offset: 0x214) Interrupt Mask Register */
  __I  uint32_t L2CC_MISR;       /**< \brief (L2cc Offset: 0x218) Masked Interrupt Status Register */
  __I  uint32_t L2CC_RISR;       /**< \brief (L2cc Offset: 0x21C) Raw Interrupt Status Register */
  __IO uint32_t L2CC_ICR;        /**< \brief (L2cc Offset: 0x220) Interrupt Clear Register */
  __I  uint32_t Reserved3[323];
  __IO uint32_t L2CC_CSR;        /**< \brief (L2cc Offset: 0x730) Cache Synchronization Register */
  __I  uint32_t Reserved4[15];
  __IO uint32_t L2CC_IPALR;      /**< \brief (L2cc Offset: 0x770) Invalidate Physical Address Line Register */
  __I  uint32_t Reserved5[2];
  __IO uint32_t L2CC_IWR;        /**< \brief (L2cc Offset: 0x77C) Invalidate Way Register */
  __I  uint32_t Reserved6[12];
  __IO uint32_t L2CC_CPALR;      /**< \brief (L2cc Offset: 0x7B0) Clean Physical Address Line Register */
  __I  uint32_t Reserved7[1];
  __IO uint32_t L2CC_CIR;        /**< \brief (L2cc Offset: 0x7B8) Clean Index Register */
  __IO uint32_t L2CC_CWR;        /**< \brief (L2cc Offset: 0x7BC) Clean Way Register */
  __I  uint32_t Reserved8[12];
  __IO uint32_t L2CC_CIPALR;     /**< \brief (L2cc Offset: 0x7F0) Clean Invalidate Physical Address Line Register */
  __I  uint32_t Reserved9[1];
  __IO uint32_t L2CC_CIIR;       /**< \brief (L2cc Offset: 0x7F8) Clean Invalidate Index Register */
  __IO uint32_t L2CC_CIWR;       /**< \brief (L2cc Offset: 0x7FC) Clean Invalidate Way Register */
  __I  uint32_t Reserved10[64];
  __IO uint32_t L2CC_DLKR;       /**< \brief (L2cc Offset: 0x900) Data Lockdown Register */
  __IO uint32_t L2CC_ILKR;       /**< \brief (L2cc Offset: 0x904) Instruction Lockdown Register */
  __I  uint32_t Reserved11[398];
  __IO uint32_t L2CC_DCR;        /**< \brief (L2cc Offset: 0xF40) Debug Control Register */
  __I  uint32_t Reserved12[7];
  __IO uint32_t L2CC_PCR;        /**< \brief (L2cc Offset: 0xF60) Prefetch Control Register */
  __I  uint32_t Reserved13[7];
  __IO uint32_t L2CC_POWCR;      /**< \brief (L2cc Offset: 0xF80) Power Control Register */
} L2cc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- L2CC_IDR : (L2CC Offset: 0x000) Cache ID Register -------- */
#define L2CC_IDR_ID_Pos 0
#define L2CC_IDR_ID_Msk (0xffffffffu << L2CC_IDR_ID_Pos) /**< \brief (L2CC_IDR) Cache Controller ID */
/* -------- L2CC_TYPR : (L2CC Offset: 0x004) Cache Type Register -------- */
#define L2CC_TYPR_IL2ASS (0x1u << 6) /**< \brief (L2CC_TYPR) Instruction L2 Cache Associativity */
#define L2CC_TYPR_IL2WSIZE_Pos 8
#define L2CC_TYPR_IL2WSIZE_Msk (0x7u << L2CC_TYPR_IL2WSIZE_Pos) /**< \brief (L2CC_TYPR) Instruction L2 Cache Way Size */
#define L2CC_TYPR_DL2ASS (0x1u << 18) /**< \brief (L2CC_TYPR) Data L2 Cache Associativity */
#define L2CC_TYPR_DL2WSIZE_Pos 20
#define L2CC_TYPR_DL2WSIZE_Msk (0x7u << L2CC_TYPR_DL2WSIZE_Pos) /**< \brief (L2CC_TYPR) Data L2 Cache Way Size */
/* -------- L2CC_CR : (L2CC Offset: 0x100) Control Register -------- */
#define L2CC_CR_L2CEN (0x1u << 0) /**< \brief (L2CC_CR) L2 Cache Enable */
/* -------- L2CC_ACR : (L2CC Offset: 0x104) Auxiliary Control Register -------- */
#define L2CC_ACR_HPSO (0x1u << 10) /**< \brief (L2CC_ACR) High Priority for SO and Dev Reads Enable */
#define L2CC_ACR_SBDLE (0x1u << 11) /**< \brief (L2CC_ACR) Store Buffer Device Limitation Enable */
#define L2CC_ACR_EXCC (0x1u << 12) /**< \brief (L2CC_ACR) Exclusive Cache Configuration */
#define L2CC_ACR_SAIE (0x1u << 13) /**< \brief (L2CC_ACR) Shared Attribute Invalidate Enable */
#define L2CC_ACR_ASS (0x1u << 16) /**< \brief (L2CC_ACR) Associativity */
#define L2CC_ACR_WAYSIZE_Pos 17
#define L2CC_ACR_WAYSIZE_Msk (0x7u << L2CC_ACR_WAYSIZE_Pos) /**< \brief (L2CC_ACR) Way Size */
#define L2CC_ACR_WAYSIZE(value) ((L2CC_ACR_WAYSIZE_Msk & ((value) << L2CC_ACR_WAYSIZE_Pos)))
#define   L2CC_ACR_WAYSIZE_16KB_WAY (0x1u << 17) /**< \brief (L2CC_ACR) 16-Kbyte way set associative */
#define L2CC_ACR_EMBEN (0x1u << 20) /**< \brief (L2CC_ACR) Event Monitor Bus Enable */
#define L2CC_ACR_PEN (0x1u << 21) /**< \brief (L2CC_ACR) Parity Enable */
#define L2CC_ACR_SAOEN (0x1u << 22) /**< \brief (L2CC_ACR) Shared Attribute Override Enable */
#define L2CC_ACR_FWA_Pos 23
#define L2CC_ACR_FWA_Msk (0x3u << L2CC_ACR_FWA_Pos) /**< \brief (L2CC_ACR) Force Write Allocate */
#define L2CC_ACR_FWA(value) ((L2CC_ACR_FWA_Msk & ((value) << L2CC_ACR_FWA_Pos)))
#define L2CC_ACR_CRPOL (0x1u << 25) /**< \brief (L2CC_ACR) Cache Replacement Policy */
#define L2CC_ACR_NSLEN (0x1u << 26) /**< \brief (L2CC_ACR) Non-Secure Lockdown Enable */
#define L2CC_ACR_NSIAC (0x1u << 27) /**< \brief (L2CC_ACR) Non-Secure Interrupt Access Control */
#define L2CC_ACR_DPEN (0x1u << 28) /**< \brief (L2CC_ACR) Data Prefetch Enable */
#define L2CC_ACR_IPEN (0x1u << 29) /**< \brief (L2CC_ACR) Instruction Prefetch Enable */
/* -------- L2CC_TRCR : (L2CC Offset: 0x108) Tag RAM Control Register -------- */
#define L2CC_TRCR_TSETLAT_Pos 0
#define L2CC_TRCR_TSETLAT_Msk (0x7u << L2CC_TRCR_TSETLAT_Pos) /**< \brief (L2CC_TRCR) Setup Latency */
#define L2CC_TRCR_TSETLAT(value) ((L2CC_TRCR_TSETLAT_Msk & ((value) << L2CC_TRCR_TSETLAT_Pos)))
#define L2CC_TRCR_TRDLAT_Pos 4
#define L2CC_TRCR_TRDLAT_Msk (0x7u << L2CC_TRCR_TRDLAT_Pos) /**< \brief (L2CC_TRCR) Read Access Latency */
#define L2CC_TRCR_TRDLAT(value) ((L2CC_TRCR_TRDLAT_Msk & ((value) << L2CC_TRCR_TRDLAT_Pos)))
#define L2CC_TRCR_TWRLAT_Pos 8
#define L2CC_TRCR_TWRLAT_Msk (0x7u << L2CC_TRCR_TWRLAT_Pos) /**< \brief (L2CC_TRCR) Write Access Latency */
#define L2CC_TRCR_TWRLAT(value) ((L2CC_TRCR_TWRLAT_Msk & ((value) << L2CC_TRCR_TWRLAT_Pos)))
/* -------- L2CC_DRCR : (L2CC Offset: 0x10C) Data RAM Control Register -------- */
#define L2CC_DRCR_DSETLAT_Pos 0
#define L2CC_DRCR_DSETLAT_Msk (0x7u << L2CC_DRCR_DSETLAT_Pos) /**< \brief (L2CC_DRCR) Setup Latency */
#define L2CC_DRCR_DSETLAT(value) ((L2CC_DRCR_DSETLAT_Msk & ((value) << L2CC_DRCR_DSETLAT_Pos)))
#define L2CC_DRCR_DRDLAT_Pos 4
#define L2CC_DRCR_DRDLAT_Msk (0x7u << L2CC_DRCR_DRDLAT_Pos) /**< \brief (L2CC_DRCR) Read Access Latency */
#define L2CC_DRCR_DRDLAT(value) ((L2CC_DRCR_DRDLAT_Msk & ((value) << L2CC_DRCR_DRDLAT_Pos)))
#define L2CC_DRCR_DWRLAT_Pos 8
#define L2CC_DRCR_DWRLAT_Msk (0x7u << L2CC_DRCR_DWRLAT_Pos) /**< \brief (L2CC_DRCR) Write Access Latency */
#define L2CC_DRCR_DWRLAT(value) ((L2CC_DRCR_DWRLAT_Msk & ((value) << L2CC_DRCR_DWRLAT_Pos)))
/* -------- L2CC_ECR : (L2CC Offset: 0x200) Event Counter Control Register -------- */
#define L2CC_ECR_EVCEN (0x1u << 0) /**< \brief (L2CC_ECR) Event Counter Enable */
#define L2CC_ECR_EVC0RST (0x1u << 1) /**< \brief (L2CC_ECR) Event Counter 0 Reset */
#define L2CC_ECR_EVC1RST (0x1u << 2) /**< \brief (L2CC_ECR) Event Counter 1 Reset */
/* -------- L2CC_ECFGR1 : (L2CC Offset: 0x204) Event Counter 1 Configuration Register -------- */
#define L2CC_ECFGR1_EIGEN_Pos 0
#define L2CC_ECFGR1_EIGEN_Msk (0x3u << L2CC_ECFGR1_EIGEN_Pos) /**< \brief (L2CC_ECFGR1) Event Counter Interrupt Generation */
#define L2CC_ECFGR1_EIGEN(value) ((L2CC_ECFGR1_EIGEN_Msk & ((value) << L2CC_ECFGR1_EIGEN_Pos)))
#define   L2CC_ECFGR1_EIGEN_INT_DIS (0x0u << 0) /**< \brief (L2CC_ECFGR1) Disables (default) */
#define   L2CC_ECFGR1_EIGEN_INT_EN_INCR (0x1u << 0) /**< \brief (L2CC_ECFGR1) Enables with Increment condition */
#define   L2CC_ECFGR1_EIGEN_INT_EN_OVER (0x2u << 0) /**< \brief (L2CC_ECFGR1) Enables with Overflow condition */
#define   L2CC_ECFGR1_EIGEN_INT_GEN_DIS (0x3u << 0) /**< \brief (L2CC_ECFGR1) Disables Interrupt generation */
#define L2CC_ECFGR1_ESRC_Pos 2
#define L2CC_ECFGR1_ESRC_Msk (0xfu << L2CC_ECFGR1_ESRC_Pos) /**< \brief (L2CC_ECFGR1) Event Counter Source */
#define L2CC_ECFGR1_ESRC(value) ((L2CC_ECFGR1_ESRC_Msk & ((value) << L2CC_ECFGR1_ESRC_Pos)))
#define   L2CC_ECFGR1_ESRC_CNT_DIS (0x0u << 2) /**< \brief (L2CC_ECFGR1) Counter Disabled */
#define   L2CC_ECFGR1_ESRC_SRC_CO (0x1u << 2) /**< \brief (L2CC_ECFGR1) Source is CO */
#define   L2CC_ECFGR1_ESRC_SRC_DRHIT (0x2u << 2) /**< \brief (L2CC_ECFGR1) Source is DRHIT */
#define   L2CC_ECFGR1_ESRC_SRC_DRREQ (0x3u << 2) /**< \brief (L2CC_ECFGR1) Source is DRREQ */
#define   L2CC_ECFGR1_ESRC_SRC_DWHIT (0x4u << 2) /**< \brief (L2CC_ECFGR1) Source is DWHIT */
#define   L2CC_ECFGR1_ESRC_SRC_DWREQ (0x5u << 2) /**< \brief (L2CC_ECFGR1) Source is DWREQ */
#define   L2CC_ECFGR1_ESRC_SRC_DWTREQ (0x6u << 2) /**< \brief (L2CC_ECFGR1) Source is DWTREQ */
#define   L2CC_ECFGR1_ESRC_SRC_IRHIT (0x7u << 2) /**< \brief (L2CC_ECFGR1) Source is IRHIT */
#define   L2CC_ECFGR1_ESRC_SRC_IRREQ (0x8u << 2) /**< \brief (L2CC_ECFGR1) Source is IRREQ */
#define   L2CC_ECFGR1_ESRC_SRC_WA (0x9u << 2) /**< \brief (L2CC_ECFGR1) Source is WA */
#define   L2CC_ECFGR1_ESRC_SRC_IPFALLOC (0xAu << 2) /**< \brief (L2CC_ECFGR1) Source is IPFALLOC */
#define   L2CC_ECFGR1_ESRC_SRC_EPFHIT (0xBu << 2) /**< \brief (L2CC_ECFGR1) Source is EPFHIT */
#define   L2CC_ECFGR1_ESRC_SRC_EPFALLOC (0xCu << 2) /**< \brief (L2CC_ECFGR1) Source is EPFALLOC */
#define   L2CC_ECFGR1_ESRC_SRC_SRRCVD (0xDu << 2) /**< \brief (L2CC_ECFGR1) Source is SRRCVD */
#define   L2CC_ECFGR1_ESRC_SRC_SRCONF (0xEu << 2) /**< \brief (L2CC_ECFGR1) Source is SRCONF */
#define   L2CC_ECFGR1_ESRC_SRC_EPFRCVD (0xFu << 2) /**< \brief (L2CC_ECFGR1) Source is EPFRCVD */
/* -------- L2CC_ECFGR0 : (L2CC Offset: 0x208) Event Counter 0 Configuration Register -------- */
#define L2CC_ECFGR0_EIGEN_Pos 0
#define L2CC_ECFGR0_EIGEN_Msk (0x3u << L2CC_ECFGR0_EIGEN_Pos) /**< \brief (L2CC_ECFGR0) Event Counter Interrupt Generation */
#define L2CC_ECFGR0_EIGEN(value) ((L2CC_ECFGR0_EIGEN_Msk & ((value) << L2CC_ECFGR0_EIGEN_Pos)))
#define   L2CC_ECFGR0_EIGEN_INT_DIS (0x0u << 0) /**< \brief (L2CC_ECFGR0) Disables (default) */
#define   L2CC_ECFGR0_EIGEN_INT_EN_INCR (0x1u << 0) /**< \brief (L2CC_ECFGR0) Enables with Increment condition */
#define   L2CC_ECFGR0_EIGEN_INT_EN_OVER (0x2u << 0) /**< \brief (L2CC_ECFGR0) Enables with Overflow condition */
#define   L2CC_ECFGR0_EIGEN_INT_GEN_DIS (0x3u << 0) /**< \brief (L2CC_ECFGR0) Disables Interrupt generation */
#define L2CC_ECFGR0_ESRC_Pos 2
#define L2CC_ECFGR0_ESRC_Msk (0xfu << L2CC_ECFGR0_ESRC_Pos) /**< \brief (L2CC_ECFGR0) Event Counter Source */
#define L2CC_ECFGR0_ESRC(value) ((L2CC_ECFGR0_ESRC_Msk & ((value) << L2CC_ECFGR0_ESRC_Pos)))
#define   L2CC_ECFGR0_ESRC_CNT_DIS (0x0u << 2) /**< \brief (L2CC_ECFGR0) Counter Disabled */
#define   L2CC_ECFGR0_ESRC_SRC_CO (0x1u << 2) /**< \brief (L2CC_ECFGR0) Source is CO */
#define   L2CC_ECFGR0_ESRC_SRC_DRHIT (0x2u << 2) /**< \brief (L2CC_ECFGR0) Source is DRHIT */
#define   L2CC_ECFGR0_ESRC_SRC_DRREQ (0x3u << 2) /**< \brief (L2CC_ECFGR0) Source is DRREQ */
#define   L2CC_ECFGR0_ESRC_SRC_DWHIT (0x4u << 2) /**< \brief (L2CC_ECFGR0) Source is DWHIT */
#define   L2CC_ECFGR0_ESRC_SRC_DWREQ (0x5u << 2) /**< \brief (L2CC_ECFGR0) Source is DWREQ */
#define   L2CC_ECFGR0_ESRC_SRC_DWTREQ (0x6u << 2) /**< \brief (L2CC_ECFGR0) Source is DWTREQ */
#define   L2CC_ECFGR0_ESRC_SRC_IRHIT (0x7u << 2) /**< \brief (L2CC_ECFGR0) Source is IRHIT */
#define   L2CC_ECFGR0_ESRC_SRC_IRREQ (0x8u << 2) /**< \brief (L2CC_ECFGR0) Source is IRREQ */
#define   L2CC_ECFGR0_ESRC_SRC_WA (0x9u << 2) /**< \brief (L2CC_ECFGR0) Source is WA */
#define   L2CC_ECFGR0_ESRC_SRC_IPFALLOC (0xAu << 2) /**< \brief (L2CC_ECFGR0) Source is IPFALLOC */
#define   L2CC_ECFGR0_ESRC_SRC_EPFHIT (0xBu << 2) /**< \brief (L2CC_ECFGR0) Source is EPFHIT */
#define   L2CC_ECFGR0_ESRC_SRC_EPFALLOC (0xCu << 2) /**< \brief (L2CC_ECFGR0) Source is EPFALLOC */
#define   L2CC_ECFGR0_ESRC_SRC_SRRCVD (0xDu << 2) /**< \brief (L2CC_ECFGR0) Source is SRRCVD */
#define   L2CC_ECFGR0_ESRC_SRC_SRCONF (0xEu << 2) /**< \brief (L2CC_ECFGR0) Source is SRCONF */
#define   L2CC_ECFGR0_ESRC_SRC_EPFRCVD (0xFu << 2) /**< \brief (L2CC_ECFGR0) Source is EPFRCVD */
/* -------- L2CC_EVR1 : (L2CC Offset: 0x20C) Event Counter 1 Value Register -------- */
#define L2CC_EVR1_VALUE_Pos 0
#define L2CC_EVR1_VALUE_Msk (0xffffffffu << L2CC_EVR1_VALUE_Pos) /**< \brief (L2CC_EVR1) Event Counter Value */
#define L2CC_EVR1_VALUE(value) ((L2CC_EVR1_VALUE_Msk & ((value) << L2CC_EVR1_VALUE_Pos)))
/* -------- L2CC_EVR0 : (L2CC Offset: 0x210) Event Counter 0 Value Register -------- */
#define L2CC_EVR0_VALUE_Pos 0
#define L2CC_EVR0_VALUE_Msk (0xffffffffu << L2CC_EVR0_VALUE_Pos) /**< \brief (L2CC_EVR0) Event Counter Value */
#define L2CC_EVR0_VALUE(value) ((L2CC_EVR0_VALUE_Msk & ((value) << L2CC_EVR0_VALUE_Pos)))
/* -------- L2CC_IMR : (L2CC Offset: 0x214) Interrupt Mask Register -------- */
#define L2CC_IMR_ECNTR (0x1u << 0) /**< \brief (L2CC_IMR) Event Counter 1/0 Overflow Increment */
#define L2CC_IMR_PARRT (0x1u << 1) /**< \brief (L2CC_IMR) Parity Error on L2 Tag RAM, Read */
#define L2CC_IMR_PARRD (0x1u << 2) /**< \brief (L2CC_IMR) Parity Error on L2 Data RAM, Read */
#define L2CC_IMR_ERRWT (0x1u << 3) /**< \brief (L2CC_IMR) Error on L2 Tag RAM, Write */
#define L2CC_IMR_ERRWD (0x1u << 4) /**< \brief (L2CC_IMR) Error on L2 Data RAM, Write */
#define L2CC_IMR_ERRRT (0x1u << 5) /**< \brief (L2CC_IMR) Error on L2 Tag RAM, Read */
#define L2CC_IMR_ERRRD (0x1u << 6) /**< \brief (L2CC_IMR) Error on L2 Data RAM, Read */
#define L2CC_IMR_SLVERR (0x1u << 7) /**< \brief (L2CC_IMR) SLVERR from L3 Memory */
#define L2CC_IMR_DECERR (0x1u << 8) /**< \brief (L2CC_IMR) DECERR from L3 Memory */
/* -------- L2CC_MISR : (L2CC Offset: 0x218) Masked Interrupt Status Register -------- */
#define L2CC_MISR_ECNTR (0x1u << 0) /**< \brief (L2CC_MISR) Event Counter 1/0 Overflow Increment */
#define L2CC_MISR_PARRT (0x1u << 1) /**< \brief (L2CC_MISR) Parity Error on L2 Tag RAM, Read */
#define L2CC_MISR_PARRD (0x1u << 2) /**< \brief (L2CC_MISR) Parity Error on L2 Data RAM, Read */
#define L2CC_MISR_ERRWT (0x1u << 3) /**< \brief (L2CC_MISR) Error on L2 Tag RAM, Write */
#define L2CC_MISR_ERRWD (0x1u << 4) /**< \brief (L2CC_MISR) Error on L2 Data RAM, Write */
#define L2CC_MISR_ERRRT (0x1u << 5) /**< \brief (L2CC_MISR) Error on L2 Tag RAM, Read */
#define L2CC_MISR_ERRRD (0x1u << 6) /**< \brief (L2CC_MISR) Error on L2 Data RAM, Read */
#define L2CC_MISR_SLVERR (0x1u << 7) /**< \brief (L2CC_MISR) SLVERR from L3 memory */
#define L2CC_MISR_DECERR (0x1u << 8) /**< \brief (L2CC_MISR) DECERR from L3 memory */
/* -------- L2CC_RISR : (L2CC Offset: 0x21C) Raw Interrupt Status Register -------- */
#define L2CC_RISR_ECNTR (0x1u << 0) /**< \brief (L2CC_RISR) Event Counter 1/0 Overflow Increment */
#define L2CC_RISR_PARRT (0x1u << 1) /**< \brief (L2CC_RISR) Parity Error on L2 Tag RAM, Read */
#define L2CC_RISR_PARRD (0x1u << 2) /**< \brief (L2CC_RISR) Parity Error on L2 Data RAM, Read */
#define L2CC_RISR_ERRWT (0x1u << 3) /**< \brief (L2CC_RISR) Error on L2 Tag RAM, Write */
#define L2CC_RISR_ERRWD (0x1u << 4) /**< \brief (L2CC_RISR) Error on L2 Data RAM, Write */
#define L2CC_RISR_ERRRT (0x1u << 5) /**< \brief (L2CC_RISR) Error on L2 Tag RAM, Read */
#define L2CC_RISR_ERRRD (0x1u << 6) /**< \brief (L2CC_RISR) Error on L2 Data RAM, Read */
#define L2CC_RISR_SLVERR (0x1u << 7) /**< \brief (L2CC_RISR) SLVERR from L3 memory */
#define L2CC_RISR_DECERR (0x1u << 8) /**< \brief (L2CC_RISR) DECERR from L3 memory */
/* -------- L2CC_ICR : (L2CC Offset: 0x220) Interrupt Clear Register -------- */
#define L2CC_ICR_ECNTR (0x1u << 0) /**< \brief (L2CC_ICR) Event Counter 1/0 Overflow Increment */
#define L2CC_ICR_PARRT (0x1u << 1) /**< \brief (L2CC_ICR) Parity Error on L2 Tag RAM, Read */
#define L2CC_ICR_PARRD (0x1u << 2) /**< \brief (L2CC_ICR) Parity Error on L2 Data RAM, Read */
#define L2CC_ICR_ERRWT (0x1u << 3) /**< \brief (L2CC_ICR) Error on L2 Tag RAM, Write */
#define L2CC_ICR_ERRWD (0x1u << 4) /**< \brief (L2CC_ICR) Error on L2 Data RAM, Write */
#define L2CC_ICR_ERRRT (0x1u << 5) /**< \brief (L2CC_ICR) Error on L2 Tag RAM, Read */
#define L2CC_ICR_ERRRD (0x1u << 6) /**< \brief (L2CC_ICR) Error on L2 Data RAM, Read */
#define L2CC_ICR_SLVERR (0x1u << 7) /**< \brief (L2CC_ICR) SLVERR from L3 memory */
#define L2CC_ICR_DECERR (0x1u << 8) /**< \brief (L2CC_ICR) DECERR from L3 memory */
/* -------- L2CC_CSR : (L2CC Offset: 0x730) Cache Synchronization Register -------- */
#define L2CC_CSR_C (0x1u << 0) /**< \brief (L2CC_CSR) Cache Synchronization Status */
/* -------- L2CC_IPALR : (L2CC Offset: 0x770) Invalidate Physical Address Line Register -------- */
#define L2CC_IPALR_C (0x1u << 0) /**< \brief (L2CC_IPALR) Cache Synchronization Status */
#define L2CC_IPALR_IDX_Pos 5
#define L2CC_IPALR_IDX_Msk (0x1ffu << L2CC_IPALR_IDX_Pos) /**< \brief (L2CC_IPALR) Index Number */
#define L2CC_IPALR_IDX(value) ((L2CC_IPALR_IDX_Msk & ((value) << L2CC_IPALR_IDX_Pos)))
#define L2CC_IPALR_TAG_Pos 14
#define L2CC_IPALR_TAG_Msk (0x3ffffu << L2CC_IPALR_TAG_Pos) /**< \brief (L2CC_IPALR) Tag Number */
#define L2CC_IPALR_TAG(value) ((L2CC_IPALR_TAG_Msk & ((value) << L2CC_IPALR_TAG_Pos)))
/* -------- L2CC_IWR : (L2CC Offset: 0x77C) Invalidate Way Register -------- */
#define L2CC_IWR_WAY0 (0x1u << 0) /**< \brief (L2CC_IWR) Invalidate Way Number 0 */
#define L2CC_IWR_WAY1 (0x1u << 1) /**< \brief (L2CC_IWR) Invalidate Way Number 1 */
#define L2CC_IWR_WAY2 (0x1u << 2) /**< \brief (L2CC_IWR) Invalidate Way Number 2 */
#define L2CC_IWR_WAY3 (0x1u << 3) /**< \brief (L2CC_IWR) Invalidate Way Number 3 */
#define L2CC_IWR_WAY4 (0x1u << 4) /**< \brief (L2CC_IWR) Invalidate Way Number 4 */
#define L2CC_IWR_WAY5 (0x1u << 5) /**< \brief (L2CC_IWR) Invalidate Way Number 5 */
#define L2CC_IWR_WAY6 (0x1u << 6) /**< \brief (L2CC_IWR) Invalidate Way Number 6 */
#define L2CC_IWR_WAY7 (0x1u << 7) /**< \brief (L2CC_IWR) Invalidate Way Number 7 */
/* -------- L2CC_CPALR : (L2CC Offset: 0x7B0) Clean Physical Address Line Register -------- */
#define L2CC_CPALR_C (0x1u << 0) /**< \brief (L2CC_CPALR) Cache Synchronization Status */
#define L2CC_CPALR_IDX_Pos 5
#define L2CC_CPALR_IDX_Msk (0x1ffu << L2CC_CPALR_IDX_Pos) /**< \brief (L2CC_CPALR) Index number */
#define L2CC_CPALR_IDX(value) ((L2CC_CPALR_IDX_Msk & ((value) << L2CC_CPALR_IDX_Pos)))
#define L2CC_CPALR_TAG_Pos 14
#define L2CC_CPALR_TAG_Msk (0x3ffffu << L2CC_CPALR_TAG_Pos) /**< \brief (L2CC_CPALR) Tag number */
#define L2CC_CPALR_TAG(value) ((L2CC_CPALR_TAG_Msk & ((value) << L2CC_CPALR_TAG_Pos)))
/* -------- L2CC_CIR : (L2CC Offset: 0x7B8) Clean Index Register -------- */
#define L2CC_CIR_C (0x1u << 0) /**< \brief (L2CC_CIR) Cache Synchronization Status */
#define L2CC_CIR_IDX_Pos 5
#define L2CC_CIR_IDX_Msk (0x1ffu << L2CC_CIR_IDX_Pos) /**< \brief (L2CC_CIR) Index number */
#define L2CC_CIR_IDX(value) ((L2CC_CIR_IDX_Msk & ((value) << L2CC_CIR_IDX_Pos)))
#define L2CC_CIR_WAY_Pos 28
#define L2CC_CIR_WAY_Msk (0x7u << L2CC_CIR_WAY_Pos) /**< \brief (L2CC_CIR) Way number */
#define L2CC_CIR_WAY(value) ((L2CC_CIR_WAY_Msk & ((value) << L2CC_CIR_WAY_Pos)))
/* -------- L2CC_CWR : (L2CC Offset: 0x7BC) Clean Way Register -------- */
#define L2CC_CWR_WAY0 (0x1u << 0) /**< \brief (L2CC_CWR) Clean Way Number 0 */
#define L2CC_CWR_WAY1 (0x1u << 1) /**< \brief (L2CC_CWR) Clean Way Number 1 */
#define L2CC_CWR_WAY2 (0x1u << 2) /**< \brief (L2CC_CWR) Clean Way Number 2 */
#define L2CC_CWR_WAY3 (0x1u << 3) /**< \brief (L2CC_CWR) Clean Way Number 3 */
#define L2CC_CWR_WAY4 (0x1u << 4) /**< \brief (L2CC_CWR) Clean Way Number 4 */
#define L2CC_CWR_WAY5 (0x1u << 5) /**< \brief (L2CC_CWR) Clean Way Number 5 */
#define L2CC_CWR_WAY6 (0x1u << 6) /**< \brief (L2CC_CWR) Clean Way Number 6 */
#define L2CC_CWR_WAY7 (0x1u << 7) /**< \brief (L2CC_CWR) Clean Way Number 7 */
/* -------- L2CC_CIPALR : (L2CC Offset: 0x7F0) Clean Invalidate Physical Address Line Register -------- */
#define L2CC_CIPALR_C (0x1u << 0) /**< \brief (L2CC_CIPALR) Cache Synchronization Status */
#define L2CC_CIPALR_IDX_Pos 5
#define L2CC_CIPALR_IDX_Msk (0x1ffu << L2CC_CIPALR_IDX_Pos) /**< \brief (L2CC_CIPALR) Index Number */
#define L2CC_CIPALR_IDX(value) ((L2CC_CIPALR_IDX_Msk & ((value) << L2CC_CIPALR_IDX_Pos)))
#define L2CC_CIPALR_TAG_Pos 14
#define L2CC_CIPALR_TAG_Msk (0x3ffffu << L2CC_CIPALR_TAG_Pos) /**< \brief (L2CC_CIPALR) Tag Number */
#define L2CC_CIPALR_TAG(value) ((L2CC_CIPALR_TAG_Msk & ((value) << L2CC_CIPALR_TAG_Pos)))
/* -------- L2CC_CIIR : (L2CC Offset: 0x7F8) Clean Invalidate Index Register -------- */
#define L2CC_CIIR_C (0x1u << 0) /**< \brief (L2CC_CIIR) Cache Synchronization Status */
#define L2CC_CIIR_IDX_Pos 5
#define L2CC_CIIR_IDX_Msk (0x1ffu << L2CC_CIIR_IDX_Pos) /**< \brief (L2CC_CIIR) Index Number */
#define L2CC_CIIR_IDX(value) ((L2CC_CIIR_IDX_Msk & ((value) << L2CC_CIIR_IDX_Pos)))
#define L2CC_CIIR_WAY_Pos 28
#define L2CC_CIIR_WAY_Msk (0x7u << L2CC_CIIR_WAY_Pos) /**< \brief (L2CC_CIIR) Way Number */
#define L2CC_CIIR_WAY(value) ((L2CC_CIIR_WAY_Msk & ((value) << L2CC_CIIR_WAY_Pos)))
/* -------- L2CC_CIWR : (L2CC Offset: 0x7FC) Clean Invalidate Way Register -------- */
#define L2CC_CIWR_WAY0 (0x1u << 0) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 0 */
#define L2CC_CIWR_WAY1 (0x1u << 1) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 1 */
#define L2CC_CIWR_WAY2 (0x1u << 2) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 2 */
#define L2CC_CIWR_WAY3 (0x1u << 3) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 3 */
#define L2CC_CIWR_WAY4 (0x1u << 4) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 4 */
#define L2CC_CIWR_WAY5 (0x1u << 5) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 5 */
#define L2CC_CIWR_WAY6 (0x1u << 6) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 6 */
#define L2CC_CIWR_WAY7 (0x1u << 7) /**< \brief (L2CC_CIWR) Clean Invalidate Way Number 7 */
/* -------- L2CC_DLKR : (L2CC Offset: 0x900) Data Lockdown Register -------- */
#define L2CC_DLKR_DLK0 (0x1u << 0) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 0 */
#define L2CC_DLKR_DLK1 (0x1u << 1) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 1 */
#define L2CC_DLKR_DLK2 (0x1u << 2) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 2 */
#define L2CC_DLKR_DLK3 (0x1u << 3) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 3 */
#define L2CC_DLKR_DLK4 (0x1u << 4) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 4 */
#define L2CC_DLKR_DLK5 (0x1u << 5) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 5 */
#define L2CC_DLKR_DLK6 (0x1u << 6) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 6 */
#define L2CC_DLKR_DLK7 (0x1u << 7) /**< \brief (L2CC_DLKR) Data Lockdown in Way Number 7 */
/* -------- L2CC_ILKR : (L2CC Offset: 0x904) Instruction Lockdown Register -------- */
#define L2CC_ILKR_ILK0 (0x1u << 0) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 0 */
#define L2CC_ILKR_ILK1 (0x1u << 1) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 1 */
#define L2CC_ILKR_ILK2 (0x1u << 2) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 2 */
#define L2CC_ILKR_ILK3 (0x1u << 3) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 3 */
#define L2CC_ILKR_ILK4 (0x1u << 4) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 4 */
#define L2CC_ILKR_ILK5 (0x1u << 5) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 5 */
#define L2CC_ILKR_ILK6 (0x1u << 6) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 6 */
#define L2CC_ILKR_ILK7 (0x1u << 7) /**< \brief (L2CC_ILKR) Instruction Lockdown in Way Number 7 */
/* -------- L2CC_DCR : (L2CC Offset: 0xF40) Debug Control Register -------- */
#define L2CC_DCR_DCL (0x1u << 0) /**< \brief (L2CC_DCR) Disable Cache Linefill */
#define L2CC_DCR_DWB (0x1u << 1) /**< \brief (L2CC_DCR) Disable Write-back, Force Write-through */
#define L2CC_DCR_SPNIDEN (0x1u << 2) /**< \brief (L2CC_DCR) SPNIDEN Value */
/* -------- L2CC_PCR : (L2CC Offset: 0xF60) Prefetch Control Register -------- */
#define L2CC_PCR_OFFSET_Pos 0
#define L2CC_PCR_OFFSET_Msk (0x1fu << L2CC_PCR_OFFSET_Pos) /**< \brief (L2CC_PCR) Prefetch Offset */
#define L2CC_PCR_OFFSET(value) ((L2CC_PCR_OFFSET_Msk & ((value) << L2CC_PCR_OFFSET_Pos)))
#define L2CC_PCR_NSIDEN (0x1u << 21) /**< \brief (L2CC_PCR) Not Same ID on Exclusive Sequence Enable */
#define L2CC_PCR_IDLEN (0x1u << 23) /**< \brief (L2CC_PCR) INCR Double Linefill Enable */
#define L2CC_PCR_PDEN (0x1u << 24) /**< \brief (L2CC_PCR) Prefetch Drop Enable */
#define L2CC_PCR_DLFWRDIS (0x1u << 27) /**< \brief (L2CC_PCR) Double Linefill on WRAP Read Disable */
#define L2CC_PCR_DATPEN (0x1u << 28) /**< \brief (L2CC_PCR) Data Prefetch Enable */
#define L2CC_PCR_INSPEN (0x1u << 29) /**< \brief (L2CC_PCR) Instruction Prefetch Enable */
#define L2CC_PCR_DLEN (0x1u << 30) /**< \brief (L2CC_PCR) Double Linefill Enable */
/* -------- L2CC_POWCR : (L2CC Offset: 0xF80) Power Control Register -------- */
#define L2CC_POWCR_STBYEN (0x1u << 0) /**< \brief (L2CC_POWCR) Standby Mode Enable */
#define L2CC_POWCR_DCKGATEN (0x1u << 1) /**< \brief (L2CC_POWCR) Dynamic Clock Gating Enable */

/*@}*/


#endif /* _SAMA5D2_L2CC_COMPONENT_ */
