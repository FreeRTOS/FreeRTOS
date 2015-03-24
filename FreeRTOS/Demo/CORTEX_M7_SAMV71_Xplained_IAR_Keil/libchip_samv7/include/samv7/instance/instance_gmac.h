/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2014, Atmel Corporation                                        */
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

#ifndef _SAM_GMAC_INSTANCE_
#define _SAM_GMAC_INSTANCE_

/* ========== Register definition for GMAC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_GMAC_NCR                        (0x40050000U) /**< \brief (GMAC) Network Control Register */
  #define REG_GMAC_NCFGR                      (0x40050004U) /**< \brief (GMAC) Network Configuration Register */
  #define REG_GMAC_NSR                        (0x40050008U) /**< \brief (GMAC) Network Status Register */
  #define REG_GMAC_UR                         (0x4005000CU) /**< \brief (GMAC) User Register */
  #define REG_GMAC_DCFGR                      (0x40050010U) /**< \brief (GMAC) DMA Configuration Register */
  #define REG_GMAC_TSR                        (0x40050014U) /**< \brief (GMAC) Transmit Status Register */
  #define REG_GMAC_RBQB                       (0x40050018U) /**< \brief (GMAC) Receive Buffer Queue Base Address */
  #define REG_GMAC_TBQB                       (0x4005001CU) /**< \brief (GMAC) Transmit Buffer Queue Base Address */
  #define REG_GMAC_RSR                        (0x40050020U) /**< \brief (GMAC) Receive Status Register */
  #define REG_GMAC_ISR                        (0x40050024U) /**< \brief (GMAC) Interrupt Status Register */
  #define REG_GMAC_IER                        (0x40050028U) /**< \brief (GMAC) Interrupt Enable Register */
  #define REG_GMAC_IDR                        (0x4005002CU) /**< \brief (GMAC) Interrupt Disable Register */
  #define REG_GMAC_IMR                        (0x40050030U) /**< \brief (GMAC) Interrupt Mask Register */
  #define REG_GMAC_MAN                        (0x40050034U) /**< \brief (GMAC) PHY Maintenance Register */
  #define REG_GMAC_RPQ                        (0x40050038U) /**< \brief (GMAC) Received Pause Quantum Register */
  #define REG_GMAC_TPQ                        (0x4005003CU) /**< \brief (GMAC) Transmit Pause Quantum Register */
  #define REG_GMAC_HRB                        (0x40050080U) /**< \brief (GMAC) Hash Register Bottom [31:0] */
  #define REG_GMAC_HRT                        (0x40050084U) /**< \brief (GMAC) Hash Register Top [63:32] */
  #define REG_GMAC_SAB1                       (0x40050088U) /**< \brief (GMAC) Specific Address 1 Bottom [31:0] Register */
  #define REG_GMAC_SAT1                       (0x4005008CU) /**< \brief (GMAC) Specific Address 1 Top [47:32] Register */
  #define REG_GMAC_SAB2                       (0x40050090U) /**< \brief (GMAC) Specific Address 2 Bottom [31:0] Register */
  #define REG_GMAC_SAT2                       (0x40050094U) /**< \brief (GMAC) Specific Address 2 Top [47:32] Register */
  #define REG_GMAC_SAB3                       (0x40050098U) /**< \brief (GMAC) Specific Address 3 Bottom [31:0] Register */
  #define REG_GMAC_SAT3                       (0x4005009CU) /**< \brief (GMAC) Specific Address 3 Top [47:32] Register */
  #define REG_GMAC_SAB4                       (0x400500A0U) /**< \brief (GMAC) Specific Address 4 Bottom [31:0] Register */
  #define REG_GMAC_SAT4                       (0x400500A4U) /**< \brief (GMAC) Specific Address 4 Top [47:32] Register */
  #define REG_GMAC_TIDM                       (0x400500A8U) /**< \brief (GMAC) Type ID Match 1 Register */
  #define REG_GMAC_WOL                        (0x400500B8U) /**< \brief (GMAC) Wake on LAN Register */
  #define REG_GMAC_IPGS                       (0x400500BCU) /**< \brief (GMAC) IPG Stretch Register */
  #define REG_GMAC_SVLAN                      (0x400500C0U) /**< \brief (GMAC) Stacked VLAN Register */
  #define REG_GMAC_TPFCP                      (0x400500C4U) /**< \brief (GMAC) Transmit PFC Pause Register */
  #define REG_GMAC_SAMB1                      (0x400500C8U) /**< \brief (GMAC) Specific Address 1 Mask Bottom [31:0] Register */
  #define REG_GMAC_SAMT1                      (0x400500CCU) /**< \brief (GMAC) Specific Address 1 Mask Top [47:32] Register */
  #define REG_GMAC_MID                        (0x400500FCU) /**< \brief (GMAC) Module ID Register */
  #define REG_GMAC_OTLO                       (0x40050100U) /**< \brief (GMAC) Octets Transmitted [31:0] Register */
  #define REG_GMAC_OTHI                       (0x40050104U) /**< \brief (GMAC) Octets Transmitted [47:32] Register */
  #define REG_GMAC_FT                         (0x40050108U) /**< \brief (GMAC) Frames Transmitted Register */
  #define REG_GMAC_BCFT                       (0x4005010CU) /**< \brief (GMAC) Broadcast Frames Transmitted Register */
  #define REG_GMAC_MFT                        (0x40050110U) /**< \brief (GMAC) Multicast Frames Transmitted Register */
  #define REG_GMAC_PFT                        (0x40050114U) /**< \brief (GMAC) Pause Frames Transmitted Register */
  #define REG_GMAC_BFT64                      (0x40050118U) /**< \brief (GMAC) 64 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT127                    (0x4005011CU) /**< \brief (GMAC) 65 to 127 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT255                    (0x40050120U) /**< \brief (GMAC) 128 to 255 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT511                    (0x40050124U) /**< \brief (GMAC) 256 to 511 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT1023                   (0x40050128U) /**< \brief (GMAC) 512 to 1023 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT1518                   (0x4005012CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Transmitted Register */
  #define REG_GMAC_GTBFT1518                  (0x40050130U) /**< \brief (GMAC) Greater Than 1518 Byte Frames Transmitted Register */
  #define REG_GMAC_TUR                        (0x40050134U) /**< \brief (GMAC) Transmit Under Runs Register */
  #define REG_GMAC_SCF                        (0x40050138U) /**< \brief (GMAC) Single Collision Frames Register */
  #define REG_GMAC_MCF                        (0x4005013CU) /**< \brief (GMAC) Multiple Collision Frames Register */
  #define REG_GMAC_EC                         (0x40050140U) /**< \brief (GMAC) Excessive Collisions Register */
  #define REG_GMAC_LC                         (0x40050144U) /**< \brief (GMAC) Late Collisions Register */
  #define REG_GMAC_DTF                        (0x40050148U) /**< \brief (GMAC) Deferred Transmission Frames Register */
  #define REG_GMAC_CSE                        (0x4005014CU) /**< \brief (GMAC) Carrier Sense Errors Register */
  #define REG_GMAC_ORLO                       (0x40050150U) /**< \brief (GMAC) Octets Received [31:0] Received */
  #define REG_GMAC_ORHI                       (0x40050154U) /**< \brief (GMAC) Octets Received [47:32] Received */
  #define REG_GMAC_FR                         (0x40050158U) /**< \brief (GMAC) Frames Received Register */
  #define REG_GMAC_BCFR                       (0x4005015CU) /**< \brief (GMAC) Broadcast Frames Received Register */
  #define REG_GMAC_MFR                        (0x40050160U) /**< \brief (GMAC) Multicast Frames Received Register */
  #define REG_GMAC_PFR                        (0x40050164U) /**< \brief (GMAC) Pause Frames Received Register */
  #define REG_GMAC_BFR64                      (0x40050168U) /**< \brief (GMAC) 64 Byte Frames Received Register */
  #define REG_GMAC_TBFR127                    (0x4005016CU) /**< \brief (GMAC) 65 to 127 Byte Frames Received Register */
  #define REG_GMAC_TBFR255                    (0x40050170U) /**< \brief (GMAC) 128 to 255 Byte Frames Received Register */
  #define REG_GMAC_TBFR511                    (0x40050174U) /**< \brief (GMAC) 256 to 511Byte Frames Received Register */
  #define REG_GMAC_TBFR1023                   (0x40050178U) /**< \brief (GMAC) 512 to 1023 Byte Frames Received Register */
  #define REG_GMAC_TBFR1518                   (0x4005017CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Received Register */
  #define REG_GMAC_TMXBFR                     (0x40050180U) /**< \brief (GMAC) 1519 to Maximum Byte Frames Received Register */
  #define REG_GMAC_UFR                        (0x40050184U) /**< \brief (GMAC) Undersize Frames Received Register */
  #define REG_GMAC_OFR                        (0x40050188U) /**< \brief (GMAC) Oversize Frames Received Register */
  #define REG_GMAC_JR                         (0x4005018CU) /**< \brief (GMAC) Jabbers Received Register */
  #define REG_GMAC_FCSE                       (0x40050190U) /**< \brief (GMAC) Frame Check Sequence Errors Register */
  #define REG_GMAC_LFFE                       (0x40050194U) /**< \brief (GMAC) Length Field Frame Errors Register */
  #define REG_GMAC_RSE                        (0x40050198U) /**< \brief (GMAC) Receive Symbol Errors Register */
  #define REG_GMAC_AE                         (0x4005019CU) /**< \brief (GMAC) Alignment Errors Register */
  #define REG_GMAC_RRE                        (0x400501A0U) /**< \brief (GMAC) Receive Resource Errors Register */
  #define REG_GMAC_ROE                        (0x400501A4U) /**< \brief (GMAC) Receive Overrun Register */
  #define REG_GMAC_IHCE                       (0x400501A8U) /**< \brief (GMAC) IP Header Checksum Errors Register */
  #define REG_GMAC_TCE                        (0x400501ACU) /**< \brief (GMAC) TCP Checksum Errors Register */
  #define REG_GMAC_UCE                        (0x400501B0U) /**< \brief (GMAC) UDP Checksum Errors Register */
  #define REG_GMAC_TSSS                       (0x400501C8U) /**< \brief (GMAC) 1588 Timer Sync Strobe Seconds Register */
  #define REG_GMAC_TSSN                       (0x400501CCU) /**< \brief (GMAC) 1588 Timer Sync Strobe Nanoseconds Register */
  #define REG_GMAC_TS                         (0x400501D0U) /**< \brief (GMAC) 1588 Timer Seconds Register */
  #define REG_GMAC_TN                         (0x400501D4U) /**< \brief (GMAC) 1588 Timer Nanoseconds Register */
  #define REG_GMAC_TA                         (0x400501D8U) /**< \brief (GMAC) 1588 Timer Adjust Register */
  #define REG_GMAC_TI                         (0x400501DCU) /**< \brief (GMAC) 1588 Timer Increment Register */
  #define REG_GMAC_EFTS                       (0x400501E0U) /**< \brief (GMAC) PTP Event Frame Transmitted Seconds */
  #define REG_GMAC_EFTN                       (0x400501E4U) /**< \brief (GMAC) PTP Event Frame Transmitted Nanoseconds */
  #define REG_GMAC_EFRS                       (0x400501E8U) /**< \brief (GMAC) PTP Event Frame Received Seconds */
  #define REG_GMAC_EFRN                       (0x400501ECU) /**< \brief (GMAC) PTP Event Frame Received Nanoseconds */
  #define REG_GMAC_PEFTS                      (0x400501F0U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Seconds */
  #define REG_GMAC_PEFTN                      (0x400501F4U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Nanoseconds */
  #define REG_GMAC_PEFRS                      (0x400501F8U) /**< \brief (GMAC) PTP Peer Event Frame Received Seconds */
  #define REG_GMAC_PEFRN                      (0x400501FCU) /**< \brief (GMAC) PTP Peer Event Frame Received Nanoseconds */
  #define REG_GMAC_ISRPQ                      (0x40050400U) /**< \brief (GMAC) Interrupt Status Register Priority Queue */
  #define REG_GMAC_TBQBAPQ                    (0x40050440U) /**< \brief (GMAC) Transmit Buffer Queue Base Address Priority Queue */
  #define REG_GMAC_RBQBAPQ                    (0x40050480U) /**< \brief (GMAC) Receive Buffer Queue Base Address Priority Queue */
  #define REG_GMAC_RBSRPQ                     (0x400504A0U) /**< \brief (GMAC) Receive Buffer Size Register Priority Queue */
  #define REG_GMAC_ST1RPQ                     (0x40050500U) /**< \brief (GMAC) Screening Type 1 Register Priority Queue */
  #define REG_GMAC_ST2RPQ                     (0x40050540U) /**< \brief (GMAC) Screening Type 2 Register Priority Queue */
  #define REG_GMAC_IERPQ                      (0x40050600U) /**< \brief (GMAC) Interrupt Enable Register Priority Queue */
  #define REG_GMAC_IDRPQ                      (0x40050620U) /**< \brief (GMAC) Interrupt Disable Register Priority Queue */
  #define REG_GMAC_IMRPQ                      (0x40050640U) /**< \brief (GMAC) Interrupt Mask Register Priority Queue */
#else
  #define REG_GMAC_NCR       (*(__IO uint32_t*)0x40050000U) /**< \brief (GMAC) Network Control Register */
  #define REG_GMAC_NCFGR     (*(__IO uint32_t*)0x40050004U) /**< \brief (GMAC) Network Configuration Register */
  #define REG_GMAC_NSR       (*(__I  uint32_t*)0x40050008U) /**< \brief (GMAC) Network Status Register */
  #define REG_GMAC_UR        (*(__IO uint32_t*)0x4005000CU) /**< \brief (GMAC) User Register */
  #define REG_GMAC_DCFGR     (*(__IO uint32_t*)0x40050010U) /**< \brief (GMAC) DMA Configuration Register */
  #define REG_GMAC_TSR       (*(__IO uint32_t*)0x40050014U) /**< \brief (GMAC) Transmit Status Register */
  #define REG_GMAC_RBQB      (*(__IO uint32_t*)0x40050018U) /**< \brief (GMAC) Receive Buffer Queue Base Address */
  #define REG_GMAC_TBQB      (*(__IO uint32_t*)0x4005001CU) /**< \brief (GMAC) Transmit Buffer Queue Base Address */
  #define REG_GMAC_RSR       (*(__IO uint32_t*)0x40050020U) /**< \brief (GMAC) Receive Status Register */
  #define REG_GMAC_ISR       (*(__I  uint32_t*)0x40050024U) /**< \brief (GMAC) Interrupt Status Register */
  #define REG_GMAC_IER       (*(__O  uint32_t*)0x40050028U) /**< \brief (GMAC) Interrupt Enable Register */
  #define REG_GMAC_IDR       (*(__O  uint32_t*)0x4005002CU) /**< \brief (GMAC) Interrupt Disable Register */
  #define REG_GMAC_IMR       (*(__I  uint32_t*)0x40050030U) /**< \brief (GMAC) Interrupt Mask Register */
  #define REG_GMAC_MAN       (*(__IO uint32_t*)0x40050034U) /**< \brief (GMAC) PHY Maintenance Register */
  #define REG_GMAC_RPQ       (*(__I  uint32_t*)0x40050038U) /**< \brief (GMAC) Received Pause Quantum Register */
  #define REG_GMAC_TPQ       (*(__IO uint32_t*)0x4005003CU) /**< \brief (GMAC) Transmit Pause Quantum Register */
  #define REG_GMAC_HRB       (*(__IO uint32_t*)0x40050080U) /**< \brief (GMAC) Hash Register Bottom [31:0] */
  #define REG_GMAC_HRT       (*(__IO uint32_t*)0x40050084U) /**< \brief (GMAC) Hash Register Top [63:32] */
  #define REG_GMAC_SAB1      (*(__IO uint32_t*)0x40050088U) /**< \brief (GMAC) Specific Address 1 Bottom [31:0] Register */
  #define REG_GMAC_SAT1      (*(__IO uint32_t*)0x4005008CU) /**< \brief (GMAC) Specific Address 1 Top [47:32] Register */
  #define REG_GMAC_SAB2      (*(__IO uint32_t*)0x40050090U) /**< \brief (GMAC) Specific Address 2 Bottom [31:0] Register */
  #define REG_GMAC_SAT2      (*(__IO uint32_t*)0x40050094U) /**< \brief (GMAC) Specific Address 2 Top [47:32] Register */
  #define REG_GMAC_SAB3      (*(__IO uint32_t*)0x40050098U) /**< \brief (GMAC) Specific Address 3 Bottom [31:0] Register */
  #define REG_GMAC_SAT3      (*(__IO uint32_t*)0x4005009CU) /**< \brief (GMAC) Specific Address 3 Top [47:32] Register */
  #define REG_GMAC_SAB4      (*(__IO uint32_t*)0x400500A0U) /**< \brief (GMAC) Specific Address 4 Bottom [31:0] Register */
  #define REG_GMAC_SAT4      (*(__IO uint32_t*)0x400500A4U) /**< \brief (GMAC) Specific Address 4 Top [47:32] Register */
  #define REG_GMAC_TIDM      (*(__IO uint32_t*)0x400500A8U) /**< \brief (GMAC) Type ID Match 1 Register */
  #define REG_GMAC_WOL       (*(__IO uint32_t*)0x400500B8U) /**< \brief (GMAC) Wake on LAN Register */
  #define REG_GMAC_IPGS      (*(__IO uint32_t*)0x400500BCU) /**< \brief (GMAC) IPG Stretch Register */
  #define REG_GMAC_SVLAN     (*(__IO uint32_t*)0x400500C0U) /**< \brief (GMAC) Stacked VLAN Register */
  #define REG_GMAC_TPFCP     (*(__IO uint32_t*)0x400500C4U) /**< \brief (GMAC) Transmit PFC Pause Register */
  #define REG_GMAC_SAMB1     (*(__IO uint32_t*)0x400500C8U) /**< \brief (GMAC) Specific Address 1 Mask Bottom [31:0] Register */
  #define REG_GMAC_SAMT1     (*(__IO uint32_t*)0x400500CCU) /**< \brief (GMAC) Specific Address 1 Mask Top [47:32] Register */
  #define REG_GMAC_MID       (*(__I  uint32_t*)0x400500FCU) /**< \brief (GMAC) Module ID Register */
  #define REG_GMAC_OTLO      (*(__I  uint32_t*)0x40050100U) /**< \brief (GMAC) Octets Transmitted [31:0] Register */
  #define REG_GMAC_OTHI      (*(__I  uint32_t*)0x40050104U) /**< \brief (GMAC) Octets Transmitted [47:32] Register */
  #define REG_GMAC_FT        (*(__I  uint32_t*)0x40050108U) /**< \brief (GMAC) Frames Transmitted Register */
  #define REG_GMAC_BCFT      (*(__I  uint32_t*)0x4005010CU) /**< \brief (GMAC) Broadcast Frames Transmitted Register */
  #define REG_GMAC_MFT       (*(__I  uint32_t*)0x40050110U) /**< \brief (GMAC) Multicast Frames Transmitted Register */
  #define REG_GMAC_PFT       (*(__I  uint32_t*)0x40050114U) /**< \brief (GMAC) Pause Frames Transmitted Register */
  #define REG_GMAC_BFT64     (*(__I  uint32_t*)0x40050118U) /**< \brief (GMAC) 64 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT127   (*(__I  uint32_t*)0x4005011CU) /**< \brief (GMAC) 65 to 127 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT255   (*(__I  uint32_t*)0x40050120U) /**< \brief (GMAC) 128 to 255 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT511   (*(__I  uint32_t*)0x40050124U) /**< \brief (GMAC) 256 to 511 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT1023  (*(__I  uint32_t*)0x40050128U) /**< \brief (GMAC) 512 to 1023 Byte Frames Transmitted Register */
  #define REG_GMAC_TBFT1518  (*(__I  uint32_t*)0x4005012CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Transmitted Register */
  #define REG_GMAC_GTBFT1518 (*(__I  uint32_t*)0x40050130U) /**< \brief (GMAC) Greater Than 1518 Byte Frames Transmitted Register */
  #define REG_GMAC_TUR       (*(__I  uint32_t*)0x40050134U) /**< \brief (GMAC) Transmit Under Runs Register */
  #define REG_GMAC_SCF       (*(__I  uint32_t*)0x40050138U) /**< \brief (GMAC) Single Collision Frames Register */
  #define REG_GMAC_MCF       (*(__I  uint32_t*)0x4005013CU) /**< \brief (GMAC) Multiple Collision Frames Register */
  #define REG_GMAC_EC        (*(__I  uint32_t*)0x40050140U) /**< \brief (GMAC) Excessive Collisions Register */
  #define REG_GMAC_LC        (*(__I  uint32_t*)0x40050144U) /**< \brief (GMAC) Late Collisions Register */
  #define REG_GMAC_DTF       (*(__I  uint32_t*)0x40050148U) /**< \brief (GMAC) Deferred Transmission Frames Register */
  #define REG_GMAC_CSE       (*(__I  uint32_t*)0x4005014CU) /**< \brief (GMAC) Carrier Sense Errors Register */
  #define REG_GMAC_ORLO      (*(__I  uint32_t*)0x40050150U) /**< \brief (GMAC) Octets Received [31:0] Received */
  #define REG_GMAC_ORHI      (*(__I  uint32_t*)0x40050154U) /**< \brief (GMAC) Octets Received [47:32] Received */
  #define REG_GMAC_FR        (*(__I  uint32_t*)0x40050158U) /**< \brief (GMAC) Frames Received Register */
  #define REG_GMAC_BCFR      (*(__I  uint32_t*)0x4005015CU) /**< \brief (GMAC) Broadcast Frames Received Register */
  #define REG_GMAC_MFR       (*(__I  uint32_t*)0x40050160U) /**< \brief (GMAC) Multicast Frames Received Register */
  #define REG_GMAC_PFR       (*(__I  uint32_t*)0x40050164U) /**< \brief (GMAC) Pause Frames Received Register */
  #define REG_GMAC_BFR64     (*(__I  uint32_t*)0x40050168U) /**< \brief (GMAC) 64 Byte Frames Received Register */
  #define REG_GMAC_TBFR127   (*(__I  uint32_t*)0x4005016CU) /**< \brief (GMAC) 65 to 127 Byte Frames Received Register */
  #define REG_GMAC_TBFR255   (*(__I  uint32_t*)0x40050170U) /**< \brief (GMAC) 128 to 255 Byte Frames Received Register */
  #define REG_GMAC_TBFR511   (*(__I  uint32_t*)0x40050174U) /**< \brief (GMAC) 256 to 511Byte Frames Received Register */
  #define REG_GMAC_TBFR1023  (*(__I  uint32_t*)0x40050178U) /**< \brief (GMAC) 512 to 1023 Byte Frames Received Register */
  #define REG_GMAC_TBFR1518  (*(__I  uint32_t*)0x4005017CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Received Register */
  #define REG_GMAC_TMXBFR    (*(__I  uint32_t*)0x40050180U) /**< \brief (GMAC) 1519 to Maximum Byte Frames Received Register */
  #define REG_GMAC_UFR       (*(__I  uint32_t*)0x40050184U) /**< \brief (GMAC) Undersize Frames Received Register */
  #define REG_GMAC_OFR       (*(__I  uint32_t*)0x40050188U) /**< \brief (GMAC) Oversize Frames Received Register */
  #define REG_GMAC_JR        (*(__I  uint32_t*)0x4005018CU) /**< \brief (GMAC) Jabbers Received Register */
  #define REG_GMAC_FCSE      (*(__I  uint32_t*)0x40050190U) /**< \brief (GMAC) Frame Check Sequence Errors Register */
  #define REG_GMAC_LFFE      (*(__I  uint32_t*)0x40050194U) /**< \brief (GMAC) Length Field Frame Errors Register */
  #define REG_GMAC_RSE       (*(__I  uint32_t*)0x40050198U) /**< \brief (GMAC) Receive Symbol Errors Register */
  #define REG_GMAC_AE        (*(__I  uint32_t*)0x4005019CU) /**< \brief (GMAC) Alignment Errors Register */
  #define REG_GMAC_RRE       (*(__I  uint32_t*)0x400501A0U) /**< \brief (GMAC) Receive Resource Errors Register */
  #define REG_GMAC_ROE       (*(__I  uint32_t*)0x400501A4U) /**< \brief (GMAC) Receive Overrun Register */
  #define REG_GMAC_IHCE      (*(__I  uint32_t*)0x400501A8U) /**< \brief (GMAC) IP Header Checksum Errors Register */
  #define REG_GMAC_TCE       (*(__I  uint32_t*)0x400501ACU) /**< \brief (GMAC) TCP Checksum Errors Register */
  #define REG_GMAC_UCE       (*(__I  uint32_t*)0x400501B0U) /**< \brief (GMAC) UDP Checksum Errors Register */
  #define REG_GMAC_TSSS      (*(__IO uint32_t*)0x400501C8U) /**< \brief (GMAC) 1588 Timer Sync Strobe Seconds Register */
  #define REG_GMAC_TSSN      (*(__IO uint32_t*)0x400501CCU) /**< \brief (GMAC) 1588 Timer Sync Strobe Nanoseconds Register */
  #define REG_GMAC_TS        (*(__IO uint32_t*)0x400501D0U) /**< \brief (GMAC) 1588 Timer Seconds Register */
  #define REG_GMAC_TN        (*(__IO uint32_t*)0x400501D4U) /**< \brief (GMAC) 1588 Timer Nanoseconds Register */
  #define REG_GMAC_TA        (*(__O  uint32_t*)0x400501D8U) /**< \brief (GMAC) 1588 Timer Adjust Register */
  #define REG_GMAC_TI        (*(__IO uint32_t*)0x400501DCU) /**< \brief (GMAC) 1588 Timer Increment Register */
  #define REG_GMAC_EFTS      (*(__I  uint32_t*)0x400501E0U) /**< \brief (GMAC) PTP Event Frame Transmitted Seconds */
  #define REG_GMAC_EFTN      (*(__I  uint32_t*)0x400501E4U) /**< \brief (GMAC) PTP Event Frame Transmitted Nanoseconds */
  #define REG_GMAC_EFRS      (*(__I  uint32_t*)0x400501E8U) /**< \brief (GMAC) PTP Event Frame Received Seconds */
  #define REG_GMAC_EFRN      (*(__I  uint32_t*)0x400501ECU) /**< \brief (GMAC) PTP Event Frame Received Nanoseconds */
  #define REG_GMAC_PEFTS     (*(__I  uint32_t*)0x400501F0U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Seconds */
  #define REG_GMAC_PEFTN     (*(__I  uint32_t*)0x400501F4U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Nanoseconds */
  #define REG_GMAC_PEFRS     (*(__I  uint32_t*)0x400501F8U) /**< \brief (GMAC) PTP Peer Event Frame Received Seconds */
  #define REG_GMAC_PEFRN     (*(__I  uint32_t*)0x400501FCU) /**< \brief (GMAC) PTP Peer Event Frame Received Nanoseconds */
  #define REG_GMAC_ISRPQ     (*(__I  uint32_t*)0x40050400U) /**< \brief (GMAC) Interrupt Status Register Priority Queue */
  #define REG_GMAC_TBQBAPQ   (*(__IO uint32_t*)0x40050440U) /**< \brief (GMAC) Transmit Buffer Queue Base Address Priority Queue */
  #define REG_GMAC_RBQBAPQ   (*(__IO uint32_t*)0x40050480U) /**< \brief (GMAC) Receive Buffer Queue Base Address Priority Queue */
  #define REG_GMAC_RBSRPQ    (*(__IO uint32_t*)0x400504A0U) /**< \brief (GMAC) Receive Buffer Size Register Priority Queue */
  #define REG_GMAC_ST1RPQ    (*(__IO uint32_t*)0x40050500U) /**< \brief (GMAC) Screening Type 1 Register Priority Queue */
  #define REG_GMAC_ST2RPQ    (*(__IO uint32_t*)0x40050540U) /**< \brief (GMAC) Screening Type 2 Register Priority Queue */
  #define REG_GMAC_IERPQ     (*(__O  uint32_t*)0x40050600U) /**< \brief (GMAC) Interrupt Enable Register Priority Queue */
  #define REG_GMAC_IDRPQ     (*(__O  uint32_t*)0x40050620U) /**< \brief (GMAC) Interrupt Disable Register Priority Queue */
  #define REG_GMAC_IMRPQ     (*(__IO uint32_t*)0x40050640U) /**< \brief (GMAC) Interrupt Mask Register Priority Queue */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAM_GMAC_INSTANCE_ */
