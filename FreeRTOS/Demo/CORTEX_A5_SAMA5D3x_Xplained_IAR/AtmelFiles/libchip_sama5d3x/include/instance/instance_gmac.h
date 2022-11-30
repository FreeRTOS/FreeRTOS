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

#ifndef _SAMA5_GMAC_INSTANCE_
#define _SAMA5_GMAC_INSTANCE_

/* ========== Register definition for GMAC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_GMAC_NCR                 (0xF0028000U) /**< \brief (GMAC) Network Control Register */
#define REG_GMAC_NCFGR               (0xF0028004U) /**< \brief (GMAC) Network Configuration Register */
#define REG_GMAC_NSR                 (0xF0028008U) /**< \brief (GMAC) Network Status Register */
#define REG_GMAC_UR                  (0xF002800CU) /**< \brief (GMAC) User Register */
#define REG_GMAC_DCFGR               (0xF0028010U) /**< \brief (GMAC) DMA Configuration Register */
#define REG_GMAC_TSR                 (0xF0028014U) /**< \brief (GMAC) Transmit Status Register */
#define REG_GMAC_RBQB                (0xF0028018U) /**< \brief (GMAC) Receive Buffer Queue Base Address */
#define REG_GMAC_TBQB                (0xF002801CU) /**< \brief (GMAC) Transmit Buffer Queue Base Address */
#define REG_GMAC_RSR                 (0xF0028020U) /**< \brief (GMAC) Receive Status Register */
#define REG_GMAC_ISR                 (0xF0028024U) /**< \brief (GMAC) Interrupt Status Register */
#define REG_GMAC_IER                 (0xF0028028U) /**< \brief (GMAC) Interrupt Enable Register */
#define REG_GMAC_IDR                 (0xF002802CU) /**< \brief (GMAC) Interrupt Disable Register */
#define REG_GMAC_IMR                 (0xF0028030U) /**< \brief (GMAC) Interrupt Mask Register */
#define REG_GMAC_MAN                 (0xF0028034U) /**< \brief (GMAC) PHY Maintenance Register */
#define REG_GMAC_RPQ                 (0xF0028038U) /**< \brief (GMAC) Received Pause Quantum Register */
#define REG_GMAC_TPQ                 (0xF002803CU) /**< \brief (GMAC) Transmit Pause Quantum Register */
#define REG_GMAC_TPSF                (0xF0028040U) /**< \brief (GMAC) TX Partial Store and Forward Register */
#define REG_GMAC_RPSF                (0xF0028044U) /**< \brief (GMAC) RX Partial Store and Forward Register */
#define REG_GMAC_HRB                 (0xF0028080U) /**< \brief (GMAC) Hash Register Bottom [31:0] */
#define REG_GMAC_HRT                 (0xF0028084U) /**< \brief (GMAC) Hash Register Top [63:32] */
#define REG_GMAC_SAB1                (0xF0028088U) /**< \brief (GMAC) Specific Address 1 Bottom [31:0] Register */
#define REG_GMAC_SAT1                (0xF002808CU) /**< \brief (GMAC) Specific Address 1 Top [47:32] Register */
#define REG_GMAC_SAB2                (0xF0028090U) /**< \brief (GMAC) Specific Address 2 Bottom [31:0] Register */
#define REG_GMAC_SAT2                (0xF0028094U) /**< \brief (GMAC) Specific Address 2 Top [47:32] Register */
#define REG_GMAC_SAB3                (0xF0028098U) /**< \brief (GMAC) Specific Address 3 Bottom [31:0] Register */
#define REG_GMAC_SAT3                (0xF002809CU) /**< \brief (GMAC) Specific Address 3 Top [47:32] Register */
#define REG_GMAC_SAB4                (0xF00280A0U) /**< \brief (GMAC) Specific Address 4 Bottom [31:0] Register */
#define REG_GMAC_SAT4                (0xF00280A4U) /**< \brief (GMAC) Specific Address 4 Top [47:32] Register */
#define REG_GMAC_TIDM                (0xF00280A8U) /**< \brief (GMAC) Type ID Match 1 Register */
#define REG_GMAC_WOL                 (0xF00280B8U) /**< \brief (GMAC) Wake on LAN Register */
#define REG_GMAC_IPGS                (0xF00280BCU) /**< \brief (GMAC) IPG Stretch Register */
#define REG_GMAC_SVLAN               (0xF00280C0U) /**< \brief (GMAC) Stacked VLAN Register */
#define REG_GMAC_TPFCP               (0xF00280C4U) /**< \brief (GMAC) Transmit PFC Pause Register */
#define REG_GMAC_SAMB1               (0xF00280C8U) /**< \brief (GMAC) Specific Address 1 Mask Bottom [31:0] Register */
#define REG_GMAC_SAMT1               (0xF00280CCU) /**< \brief (GMAC) Specific Address 1 Mask Top [47:32] Register */
#define REG_GMAC_OTLO                (0xF0028100U) /**< \brief (GMAC) Octets Transmitted [31:0] Register */
#define REG_GMAC_OTHI                (0xF0028104U) /**< \brief (GMAC) Octets Transmitted [47:32] Register */
#define REG_GMAC_FT                  (0xF0028108U) /**< \brief (GMAC) Frames Transmitted Register */
#define REG_GMAC_BCFT                (0xF002810CU) /**< \brief (GMAC) Broadcast Frames Transmitted Register */
#define REG_GMAC_MFT                 (0xF0028110U) /**< \brief (GMAC) Multicast Frames Transmitted Register */
#define REG_GMAC_PFT                 (0xF0028114U) /**< \brief (GMAC) Pause Frames Transmitted Register */
#define REG_GMAC_BFT64               (0xF0028118U) /**< \brief (GMAC) 64 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT127             (0xF002811CU) /**< \brief (GMAC) 65 to 127 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT255             (0xF0028120U) /**< \brief (GMAC) 128 to 255 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT511             (0xF0028124U) /**< \brief (GMAC) 256 to 511 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT1023            (0xF0028128U) /**< \brief (GMAC) 512 to 1023 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT1518            (0xF002812CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Transmitted Register */
#define REG_GMAC_GTBFT1518           (0xF0028130U) /**< \brief (GMAC) Greater Than 1518 Byte Frames Transmitted Register */
#define REG_GMAC_TUR                 (0xF0028134U) /**< \brief (GMAC) Transmit Under Runs Register */
#define REG_GMAC_SCF                 (0xF0028138U) /**< \brief (GMAC) Single Collision Frames Register */
#define REG_GMAC_MCF                 (0xF002813CU) /**< \brief (GMAC) Multiple Collision Frames Register */
#define REG_GMAC_EC                  (0xF0028140U) /**< \brief (GMAC) Excessive Collisions Register */
#define REG_GMAC_LC                  (0xF0028144U) /**< \brief (GMAC) Late Collisions Register */
#define REG_GMAC_DTF                 (0xF0028148U) /**< \brief (GMAC) Deferred Transmission Frames Register */
#define REG_GMAC_CSE                 (0xF002814CU) /**< \brief (GMAC) Carrier Sense Errors Register */
#define REG_GMAC_ORLO                (0xF0028150U) /**< \brief (GMAC) Octets Received [31:0] Received */
#define REG_GMAC_ORHI                (0xF0028154U) /**< \brief (GMAC) Octets Received [47:32] Received */
#define REG_GMAC_FR                  (0xF0028158U) /**< \brief (GMAC) Frames Received Register */
#define REG_GMAC_BCFR                (0xF002815CU) /**< \brief (GMAC) Broadcast Frames Received Register */
#define REG_GMAC_MFR                 (0xF0028160U) /**< \brief (GMAC) Multicast Frames Received Register */
#define REG_GMAC_PFR                 (0xF0028164U) /**< \brief (GMAC) Pause Frames Received Register */
#define REG_GMAC_BFR64               (0xF0028168U) /**< \brief (GMAC) 64 Byte Frames Received Register */
#define REG_GMAC_TBFR127             (0xF002816CU) /**< \brief (GMAC) 65 to 127 Byte Frames Received Register */
#define REG_GMAC_TBFR255             (0xF0028170U) /**< \brief (GMAC) 128 to 255 Byte Frames Received Register */
#define REG_GMAC_TBFR511             (0xF0028174U) /**< \brief (GMAC) 256 to 511Byte Frames Received Register */
#define REG_GMAC_TBFR1023            (0xF0028178U) /**< \brief (GMAC) 512 to 1023 Byte Frames Received Register */
#define REG_GMAC_TBFR1518            (0xF002817CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Received Register */
#define REG_GMAC_TMXBFR              (0xF0028180U) /**< \brief (GMAC) 1519 to Maximum Byte Frames Received Register */
#define REG_GMAC_UFR                 (0xF0028184U) /**< \brief (GMAC) Undersize Frames Received Register */
#define REG_GMAC_OFR                 (0xF0028188U) /**< \brief (GMAC) Oversize Frames Received Register */
#define REG_GMAC_JR                  (0xF002818CU) /**< \brief (GMAC) Jabbers Received Register */
#define REG_GMAC_FCSE                (0xF0028190U) /**< \brief (GMAC) Frame Check Sequence Errors Register */
#define REG_GMAC_LFFE                (0xF0028194U) /**< \brief (GMAC) Length Field Frame Errors Register */
#define REG_GMAC_RSE                 (0xF0028198U) /**< \brief (GMAC) Receive Symbol Errors Register */
#define REG_GMAC_AE                  (0xF002819CU) /**< \brief (GMAC) Alignment Errors Register */
#define REG_GMAC_RRE                 (0xF00281A0U) /**< \brief (GMAC) Receive Resource Errors Register */
#define REG_GMAC_ROE                 (0xF00281A4U) /**< \brief (GMAC) Receive Overrun Register */
#define REG_GMAC_IHCE                (0xF00281A8U) /**< \brief (GMAC) IP Header Checksum Errors Register */
#define REG_GMAC_TCE                 (0xF00281ACU) /**< \brief (GMAC) TCP Checksum Errors Register */
#define REG_GMAC_UCE                 (0xF00281B0U) /**< \brief (GMAC) UDP Checksum Errors Register */
#define REG_GMAC_TSSS                (0xF00281C8U) /**< \brief (GMAC) 1588 Timer Sync Strobe Seconds Register */
#define REG_GMAC_TSSN                (0xF00281CCU) /**< \brief (GMAC) 1588 Timer Sync Strobe Nanoseconds Register */
#define REG_GMAC_TS                  (0xF00281D0U) /**< \brief (GMAC) 1588 Timer Seconds Register */
#define REG_GMAC_TN                  (0xF00281D4U) /**< \brief (GMAC) 1588 Timer Nanoseconds Register */
#define REG_GMAC_TA                  (0xF00281D8U) /**< \brief (GMAC) 1588 Timer Adjust Register */
#define REG_GMAC_TI                  (0xF00281DCU) /**< \brief (GMAC) 1588 Timer Increment Register */
#define REG_GMAC_EFTS                (0xF00281E0U) /**< \brief (GMAC) PTP Event Frame Transmitted Seconds */
#define REG_GMAC_EFTN                (0xF00281E4U) /**< \brief (GMAC) PTP Event Frame Transmitted Nanoseconds */
#define REG_GMAC_EFRS                (0xF00281E8U) /**< \brief (GMAC) PTP Event Frame Received Seconds */
#define REG_GMAC_EFRN                (0xF00281ECU) /**< \brief (GMAC) PTP Event Frame Received Nanoseconds */
#define REG_GMAC_PEFTS               (0xF00281F0U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Seconds */
#define REG_GMAC_PEFTN               (0xF00281F4U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Nanoseconds */
#define REG_GMAC_PEFRS               (0xF00281F8U) /**< \brief (GMAC) PTP Peer Event Frame Received Seconds */
#define REG_GMAC_PEFRN               (0xF00281FCU) /**< \brief (GMAC) PTP Peer Event Frame Received Nanoseconds */
#define REG_GMAC_ISRPQ               (0xF0028400U) /**< \brief (GMAC) Interrupt Status Register Priority Queue */
#define REG_GMAC_TBQBAPQ             (0xF0028440U) /**< \brief (GMAC) Transmit Buffer Queue Base Address Priority Queue */
#define REG_GMAC_RBQBAPQ             (0xF0028480U) /**< \brief (GMAC) Receive Buffer Queue Base Address Priority Queue */
#define REG_GMAC_RBSRPQ              (0xF00284A0U) /**< \brief (GMAC) Receive Buffer Size Register Priority Queue */
#define REG_GMAC_ST1RPQ              (0xF0028500U) /**< \brief (GMAC) Screening Type1 Register Priority Queue */
#define REG_GMAC_ST2RPQ              (0xF0028540U) /**< \brief (GMAC) Screening Type2 Register Priority Queue */
#define REG_GMAC_IERPQ               (0xF0028600U) /**< \brief (GMAC) Interrupt Enable Register Priority Queue */
#define REG_GMAC_IDRPQ               (0xF0028620U) /**< \brief (GMAC) Interrupt Disable Register Priority Queue */
#define REG_GMAC_IMRPQ               (0xF0028640U) /**< \brief (GMAC) Interrupt Mask Register Priority Queue */
#else
#define REG_GMAC_NCR        (*(RwReg*)0xF0028000U) /**< \brief (GMAC) Network Control Register */
#define REG_GMAC_NCFGR      (*(RwReg*)0xF0028004U) /**< \brief (GMAC) Network Configuration Register */
#define REG_GMAC_NSR        (*(RoReg*)0xF0028008U) /**< \brief (GMAC) Network Status Register */
#define REG_GMAC_UR         (*(RwReg*)0xF002800CU) /**< \brief (GMAC) User Register */
#define REG_GMAC_DCFGR      (*(RwReg*)0xF0028010U) /**< \brief (GMAC) DMA Configuration Register */
#define REG_GMAC_TSR        (*(RwReg*)0xF0028014U) /**< \brief (GMAC) Transmit Status Register */
#define REG_GMAC_RBQB       (*(RwReg*)0xF0028018U) /**< \brief (GMAC) Receive Buffer Queue Base Address */
#define REG_GMAC_TBQB       (*(RwReg*)0xF002801CU) /**< \brief (GMAC) Transmit Buffer Queue Base Address */
#define REG_GMAC_RSR        (*(RwReg*)0xF0028020U) /**< \brief (GMAC) Receive Status Register */
#define REG_GMAC_ISR        (*(RoReg*)0xF0028024U) /**< \brief (GMAC) Interrupt Status Register */
#define REG_GMAC_IER        (*(WoReg*)0xF0028028U) /**< \brief (GMAC) Interrupt Enable Register */
#define REG_GMAC_IDR        (*(WoReg*)0xF002802CU) /**< \brief (GMAC) Interrupt Disable Register */
#define REG_GMAC_IMR        (*(RoReg*)0xF0028030U) /**< \brief (GMAC) Interrupt Mask Register */
#define REG_GMAC_MAN        (*(RwReg*)0xF0028034U) /**< \brief (GMAC) PHY Maintenance Register */
#define REG_GMAC_RPQ        (*(RoReg*)0xF0028038U) /**< \brief (GMAC) Received Pause Quantum Register */
#define REG_GMAC_TPQ        (*(RwReg*)0xF002803CU) /**< \brief (GMAC) Transmit Pause Quantum Register */
#define REG_GMAC_TPSF       (*(RwReg*)0xF0028040U) /**< \brief (GMAC) TX Partial Store and Forward Register */
#define REG_GMAC_RPSF       (*(RwReg*)0xF0028044U) /**< \brief (GMAC) RX Partial Store and Forward Register */
#define REG_GMAC_HRB        (*(RwReg*)0xF0028080U) /**< \brief (GMAC) Hash Register Bottom [31:0] */
#define REG_GMAC_HRT        (*(RwReg*)0xF0028084U) /**< \brief (GMAC) Hash Register Top [63:32] */
#define REG_GMAC_SAB1       (*(RwReg*)0xF0028088U) /**< \brief (GMAC) Specific Address 1 Bottom [31:0] Register */
#define REG_GMAC_SAT1       (*(RwReg*)0xF002808CU) /**< \brief (GMAC) Specific Address 1 Top [47:32] Register */
#define REG_GMAC_SAB2       (*(RwReg*)0xF0028090U) /**< \brief (GMAC) Specific Address 2 Bottom [31:0] Register */
#define REG_GMAC_SAT2       (*(RwReg*)0xF0028094U) /**< \brief (GMAC) Specific Address 2 Top [47:32] Register */
#define REG_GMAC_SAB3       (*(RwReg*)0xF0028098U) /**< \brief (GMAC) Specific Address 3 Bottom [31:0] Register */
#define REG_GMAC_SAT3       (*(RwReg*)0xF002809CU) /**< \brief (GMAC) Specific Address 3 Top [47:32] Register */
#define REG_GMAC_SAB4       (*(RwReg*)0xF00280A0U) /**< \brief (GMAC) Specific Address 4 Bottom [31:0] Register */
#define REG_GMAC_SAT4       (*(RwReg*)0xF00280A4U) /**< \brief (GMAC) Specific Address 4 Top [47:32] Register */
#define REG_GMAC_TIDM       (*(RwReg*)0xF00280A8U) /**< \brief (GMAC) Type ID Match 1 Register */
#define REG_GMAC_WOL        (*(RwReg*)0xF00280B8U) /**< \brief (GMAC) Wake on LAN Register */
#define REG_GMAC_IPGS       (*(RwReg*)0xF00280BCU) /**< \brief (GMAC) IPG Stretch Register */
#define REG_GMAC_SVLAN      (*(RwReg*)0xF00280C0U) /**< \brief (GMAC) Stacked VLAN Register */
#define REG_GMAC_TPFCP      (*(RwReg*)0xF00280C4U) /**< \brief (GMAC) Transmit PFC Pause Register */
#define REG_GMAC_SAMB1      (*(RwReg*)0xF00280C8U) /**< \brief (GMAC) Specific Address 1 Mask Bottom [31:0] Register */
#define REG_GMAC_SAMT1      (*(RwReg*)0xF00280CCU) /**< \brief (GMAC) Specific Address 1 Mask Top [47:32] Register */
#define REG_GMAC_OTLO       (*(RoReg*)0xF0028100U) /**< \brief (GMAC) Octets Transmitted [31:0] Register */
#define REG_GMAC_OTHI       (*(RoReg*)0xF0028104U) /**< \brief (GMAC) Octets Transmitted [47:32] Register */
#define REG_GMAC_FT         (*(RoReg*)0xF0028108U) /**< \brief (GMAC) Frames Transmitted Register */
#define REG_GMAC_BCFT       (*(RoReg*)0xF002810CU) /**< \brief (GMAC) Broadcast Frames Transmitted Register */
#define REG_GMAC_MFT        (*(RoReg*)0xF0028110U) /**< \brief (GMAC) Multicast Frames Transmitted Register */
#define REG_GMAC_PFT        (*(RoReg*)0xF0028114U) /**< \brief (GMAC) Pause Frames Transmitted Register */
#define REG_GMAC_BFT64      (*(RoReg*)0xF0028118U) /**< \brief (GMAC) 64 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT127    (*(RoReg*)0xF002811CU) /**< \brief (GMAC) 65 to 127 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT255    (*(RoReg*)0xF0028120U) /**< \brief (GMAC) 128 to 255 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT511    (*(RoReg*)0xF0028124U) /**< \brief (GMAC) 256 to 511 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT1023   (*(RoReg*)0xF0028128U) /**< \brief (GMAC) 512 to 1023 Byte Frames Transmitted Register */
#define REG_GMAC_TBFT1518   (*(RoReg*)0xF002812CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Transmitted Register */
#define REG_GMAC_GTBFT1518  (*(RoReg*)0xF0028130U) /**< \brief (GMAC) Greater Than 1518 Byte Frames Transmitted Register */
#define REG_GMAC_TUR        (*(RoReg*)0xF0028134U) /**< \brief (GMAC) Transmit Under Runs Register */
#define REG_GMAC_SCF        (*(RoReg*)0xF0028138U) /**< \brief (GMAC) Single Collision Frames Register */
#define REG_GMAC_MCF        (*(RoReg*)0xF002813CU) /**< \brief (GMAC) Multiple Collision Frames Register */
#define REG_GMAC_EC         (*(RoReg*)0xF0028140U) /**< \brief (GMAC) Excessive Collisions Register */
#define REG_GMAC_LC         (*(RoReg*)0xF0028144U) /**< \brief (GMAC) Late Collisions Register */
#define REG_GMAC_DTF        (*(RoReg*)0xF0028148U) /**< \brief (GMAC) Deferred Transmission Frames Register */
#define REG_GMAC_CSE        (*(RoReg*)0xF002814CU) /**< \brief (GMAC) Carrier Sense Errors Register */
#define REG_GMAC_ORLO       (*(RoReg*)0xF0028150U) /**< \brief (GMAC) Octets Received [31:0] Received */
#define REG_GMAC_ORHI       (*(RoReg*)0xF0028154U) /**< \brief (GMAC) Octets Received [47:32] Received */
#define REG_GMAC_FR         (*(RoReg*)0xF0028158U) /**< \brief (GMAC) Frames Received Register */
#define REG_GMAC_BCFR       (*(RoReg*)0xF002815CU) /**< \brief (GMAC) Broadcast Frames Received Register */
#define REG_GMAC_MFR        (*(RoReg*)0xF0028160U) /**< \brief (GMAC) Multicast Frames Received Register */
#define REG_GMAC_PFR        (*(RoReg*)0xF0028164U) /**< \brief (GMAC) Pause Frames Received Register */
#define REG_GMAC_BFR64      (*(RoReg*)0xF0028168U) /**< \brief (GMAC) 64 Byte Frames Received Register */
#define REG_GMAC_TBFR127    (*(RoReg*)0xF002816CU) /**< \brief (GMAC) 65 to 127 Byte Frames Received Register */
#define REG_GMAC_TBFR255    (*(RoReg*)0xF0028170U) /**< \brief (GMAC) 128 to 255 Byte Frames Received Register */
#define REG_GMAC_TBFR511    (*(RoReg*)0xF0028174U) /**< \brief (GMAC) 256 to 511Byte Frames Received Register */
#define REG_GMAC_TBFR1023   (*(RoReg*)0xF0028178U) /**< \brief (GMAC) 512 to 1023 Byte Frames Received Register */
#define REG_GMAC_TBFR1518   (*(RoReg*)0xF002817CU) /**< \brief (GMAC) 1024 to 1518 Byte Frames Received Register */
#define REG_GMAC_TMXBFR     (*(RoReg*)0xF0028180U) /**< \brief (GMAC) 1519 to Maximum Byte Frames Received Register */
#define REG_GMAC_UFR        (*(RoReg*)0xF0028184U) /**< \brief (GMAC) Undersize Frames Received Register */
#define REG_GMAC_OFR        (*(RoReg*)0xF0028188U) /**< \brief (GMAC) Oversize Frames Received Register */
#define REG_GMAC_JR         (*(RoReg*)0xF002818CU) /**< \brief (GMAC) Jabbers Received Register */
#define REG_GMAC_FCSE       (*(RoReg*)0xF0028190U) /**< \brief (GMAC) Frame Check Sequence Errors Register */
#define REG_GMAC_LFFE       (*(RoReg*)0xF0028194U) /**< \brief (GMAC) Length Field Frame Errors Register */
#define REG_GMAC_RSE        (*(RoReg*)0xF0028198U) /**< \brief (GMAC) Receive Symbol Errors Register */
#define REG_GMAC_AE         (*(RoReg*)0xF002819CU) /**< \brief (GMAC) Alignment Errors Register */
#define REG_GMAC_RRE        (*(RoReg*)0xF00281A0U) /**< \brief (GMAC) Receive Resource Errors Register */
#define REG_GMAC_ROE        (*(RoReg*)0xF00281A4U) /**< \brief (GMAC) Receive Overrun Register */
#define REG_GMAC_IHCE       (*(RoReg*)0xF00281A8U) /**< \brief (GMAC) IP Header Checksum Errors Register */
#define REG_GMAC_TCE        (*(RoReg*)0xF00281ACU) /**< \brief (GMAC) TCP Checksum Errors Register */
#define REG_GMAC_UCE        (*(RoReg*)0xF00281B0U) /**< \brief (GMAC) UDP Checksum Errors Register */
#define REG_GMAC_TSSS       (*(RwReg*)0xF00281C8U) /**< \brief (GMAC) 1588 Timer Sync Strobe Seconds Register */
#define REG_GMAC_TSSN       (*(RwReg*)0xF00281CCU) /**< \brief (GMAC) 1588 Timer Sync Strobe Nanoseconds Register */
#define REG_GMAC_TS         (*(RwReg*)0xF00281D0U) /**< \brief (GMAC) 1588 Timer Seconds Register */
#define REG_GMAC_TN         (*(RwReg*)0xF00281D4U) /**< \brief (GMAC) 1588 Timer Nanoseconds Register */
#define REG_GMAC_TA         (*(WoReg*)0xF00281D8U) /**< \brief (GMAC) 1588 Timer Adjust Register */
#define REG_GMAC_TI         (*(RwReg*)0xF00281DCU) /**< \brief (GMAC) 1588 Timer Increment Register */
#define REG_GMAC_EFTS       (*(RoReg*)0xF00281E0U) /**< \brief (GMAC) PTP Event Frame Transmitted Seconds */
#define REG_GMAC_EFTN       (*(RoReg*)0xF00281E4U) /**< \brief (GMAC) PTP Event Frame Transmitted Nanoseconds */
#define REG_GMAC_EFRS       (*(RoReg*)0xF00281E8U) /**< \brief (GMAC) PTP Event Frame Received Seconds */
#define REG_GMAC_EFRN       (*(RoReg*)0xF00281ECU) /**< \brief (GMAC) PTP Event Frame Received Nanoseconds */
#define REG_GMAC_PEFTS      (*(RoReg*)0xF00281F0U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Seconds */
#define REG_GMAC_PEFTN      (*(RoReg*)0xF00281F4U) /**< \brief (GMAC) PTP Peer Event Frame Transmitted Nanoseconds */
#define REG_GMAC_PEFRS      (*(RoReg*)0xF00281F8U) /**< \brief (GMAC) PTP Peer Event Frame Received Seconds */
#define REG_GMAC_PEFRN      (*(RoReg*)0xF00281FCU) /**< \brief (GMAC) PTP Peer Event Frame Received Nanoseconds */
#define REG_GMAC_ISRPQ      (*(RoReg*)0xF0028400U) /**< \brief (GMAC) Interrupt Status Register Priority Queue */
#define REG_GMAC_TBQBAPQ    (*(RwReg*)0xF0028440U) /**< \brief (GMAC) Transmit Buffer Queue Base Address Priority Queue */
#define REG_GMAC_RBQBAPQ    (*(RwReg*)0xF0028480U) /**< \brief (GMAC) Receive Buffer Queue Base Address Priority Queue */
#define REG_GMAC_RBSRPQ     (*(RwReg*)0xF00284A0U) /**< \brief (GMAC) Receive Buffer Size Register Priority Queue */
#define REG_GMAC_ST1RPQ     (*(RwReg*)0xF0028500U) /**< \brief (GMAC) Screening Type1 Register Priority Queue */
#define REG_GMAC_ST2RPQ     (*(RwReg*)0xF0028540U) /**< \brief (GMAC) Screening Type2 Register Priority Queue */
#define REG_GMAC_IERPQ      (*(WoReg*)0xF0028600U) /**< \brief (GMAC) Interrupt Enable Register Priority Queue */
#define REG_GMAC_IDRPQ      (*(WoReg*)0xF0028620U) /**< \brief (GMAC) Interrupt Disable Register Priority Queue */
#define REG_GMAC_IMRPQ      (*(RwReg*)0xF0028640U) /**< \brief (GMAC) Interrupt Mask Register Priority Queue */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_GMAC_INSTANCE_ */
