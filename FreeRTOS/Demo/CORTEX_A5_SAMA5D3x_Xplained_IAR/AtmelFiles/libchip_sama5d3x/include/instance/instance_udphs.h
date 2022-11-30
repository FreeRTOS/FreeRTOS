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

#ifndef _SAMA5_UDPHS_INSTANCE_
#define _SAMA5_UDPHS_INSTANCE_

/* ========== Register definition for UDPHS peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
#define REG_UDPHS_CTRL                 (0xF8030000U) /**< \brief (UDPHS) UDPHS Control Register */
#define REG_UDPHS_FNUM                 (0xF8030004U) /**< \brief (UDPHS) UDPHS Frame Number Register */
#define REG_UDPHS_IEN                  (0xF8030010U) /**< \brief (UDPHS) UDPHS Interrupt Enable Register */
#define REG_UDPHS_INTSTA               (0xF8030014U) /**< \brief (UDPHS) UDPHS Interrupt Status Register */
#define REG_UDPHS_CLRINT               (0xF8030018U) /**< \brief (UDPHS) UDPHS Clear Interrupt Register */
#define REG_UDPHS_EPTRST               (0xF803001CU) /**< \brief (UDPHS) UDPHS Endpoints Reset Register */
#define REG_UDPHS_TST                  (0xF80300E0U) /**< \brief (UDPHS) UDPHS Test Register */
#define REG_UDPHS_IPNAME1              (0xF80300F0U) /**< \brief (UDPHS) UDPHS Name1 Register */
#define REG_UDPHS_IPNAME2              (0xF80300F4U) /**< \brief (UDPHS) UDPHS Name2 Register */
#define REG_UDPHS_IPFEATURES           (0xF80300F8U) /**< \brief (UDPHS) UDPHS Features Register */
#define REG_UDPHS_EPTCFG0              (0xF8030100U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 0) */
#define REG_UDPHS_EPTCTLENB0           (0xF8030104U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 0) */
#define REG_UDPHS_EPTCTLDIS0           (0xF8030108U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 0) */
#define REG_UDPHS_EPTCTL0              (0xF803010CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 0) */
#define REG_UDPHS_EPTSETSTA0           (0xF8030114U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 0) */
#define REG_UDPHS_EPTCLRSTA0           (0xF8030118U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 0) */
#define REG_UDPHS_EPTSTA0              (0xF803011CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 0) */
#define REG_UDPHS_EPTCFG1              (0xF8030120U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 1) */
#define REG_UDPHS_EPTCTLENB1           (0xF8030124U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 1) */
#define REG_UDPHS_EPTCTLDIS1           (0xF8030128U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 1) */
#define REG_UDPHS_EPTCTL1              (0xF803012CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 1) */
#define REG_UDPHS_EPTSETSTA1           (0xF8030134U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 1) */
#define REG_UDPHS_EPTCLRSTA1           (0xF8030138U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 1) */
#define REG_UDPHS_EPTSTA1              (0xF803013CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 1) */
#define REG_UDPHS_EPTCFG2              (0xF8030140U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 2) */
#define REG_UDPHS_EPTCTLENB2           (0xF8030144U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 2) */
#define REG_UDPHS_EPTCTLDIS2           (0xF8030148U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 2) */
#define REG_UDPHS_EPTCTL2              (0xF803014CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 2) */
#define REG_UDPHS_EPTSETSTA2           (0xF8030154U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 2) */
#define REG_UDPHS_EPTCLRSTA2           (0xF8030158U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 2) */
#define REG_UDPHS_EPTSTA2              (0xF803015CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 2) */
#define REG_UDPHS_EPTCFG3              (0xF8030160U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 3) */
#define REG_UDPHS_EPTCTLENB3           (0xF8030164U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 3) */
#define REG_UDPHS_EPTCTLDIS3           (0xF8030168U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 3) */
#define REG_UDPHS_EPTCTL3              (0xF803016CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 3) */
#define REG_UDPHS_EPTSETSTA3           (0xF8030174U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 3) */
#define REG_UDPHS_EPTCLRSTA3           (0xF8030178U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 3) */
#define REG_UDPHS_EPTSTA3              (0xF803017CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 3) */
#define REG_UDPHS_EPTCFG4              (0xF8030180U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 4) */
#define REG_UDPHS_EPTCTLENB4           (0xF8030184U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 4) */
#define REG_UDPHS_EPTCTLDIS4           (0xF8030188U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 4) */
#define REG_UDPHS_EPTCTL4              (0xF803018CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 4) */
#define REG_UDPHS_EPTSETSTA4           (0xF8030194U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 4) */
#define REG_UDPHS_EPTCLRSTA4           (0xF8030198U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 4) */
#define REG_UDPHS_EPTSTA4              (0xF803019CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 4) */
#define REG_UDPHS_EPTCFG5              (0xF80301A0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 5) */
#define REG_UDPHS_EPTCTLENB5           (0xF80301A4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 5) */
#define REG_UDPHS_EPTCTLDIS5           (0xF80301A8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 5) */
#define REG_UDPHS_EPTCTL5              (0xF80301ACU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 5) */
#define REG_UDPHS_EPTSETSTA5           (0xF80301B4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 5) */
#define REG_UDPHS_EPTCLRSTA5           (0xF80301B8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 5) */
#define REG_UDPHS_EPTSTA5              (0xF80301BCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 5) */
#define REG_UDPHS_EPTCFG6              (0xF80301C0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 6) */
#define REG_UDPHS_EPTCTLENB6           (0xF80301C4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 6) */
#define REG_UDPHS_EPTCTLDIS6           (0xF80301C8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 6) */
#define REG_UDPHS_EPTCTL6              (0xF80301CCU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 6) */
#define REG_UDPHS_EPTSETSTA6           (0xF80301D4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 6) */
#define REG_UDPHS_EPTCLRSTA6           (0xF80301D8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 6) */
#define REG_UDPHS_EPTSTA6              (0xF80301DCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 6) */
#define REG_UDPHS_EPTCFG7              (0xF80301E0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 7) */
#define REG_UDPHS_EPTCTLENB7           (0xF80301E4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 7) */
#define REG_UDPHS_EPTCTLDIS7           (0xF80301E8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 7) */
#define REG_UDPHS_EPTCTL7              (0xF80301ECU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 7) */
#define REG_UDPHS_EPTSETSTA7           (0xF80301F4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 7) */
#define REG_UDPHS_EPTCLRSTA7           (0xF80301F8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 7) */
#define REG_UDPHS_EPTSTA7              (0xF80301FCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 7) */
#define REG_UDPHS_EPTCFG8              (0xF8030200U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 8) */
#define REG_UDPHS_EPTCTLENB8           (0xF8030204U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 8) */
#define REG_UDPHS_EPTCTLDIS8           (0xF8030208U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 8) */
#define REG_UDPHS_EPTCTL8              (0xF803020CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 8) */
#define REG_UDPHS_EPTSETSTA8           (0xF8030214U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 8) */
#define REG_UDPHS_EPTCLRSTA8           (0xF8030218U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 8) */
#define REG_UDPHS_EPTSTA8              (0xF803021CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 8) */
#define REG_UDPHS_EPTCFG9              (0xF8030220U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 9) */
#define REG_UDPHS_EPTCTLENB9           (0xF8030224U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 9) */
#define REG_UDPHS_EPTCTLDIS9           (0xF8030228U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 9) */
#define REG_UDPHS_EPTCTL9              (0xF803022CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 9) */
#define REG_UDPHS_EPTSETSTA9           (0xF8030234U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 9) */
#define REG_UDPHS_EPTCLRSTA9           (0xF8030238U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 9) */
#define REG_UDPHS_EPTSTA9              (0xF803023CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 9) */
#define REG_UDPHS_EPTCFG10             (0xF8030240U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 10) */
#define REG_UDPHS_EPTCTLENB10          (0xF8030244U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 10) */
#define REG_UDPHS_EPTCTLDIS10          (0xF8030248U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 10) */
#define REG_UDPHS_EPTCTL10             (0xF803024CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 10) */
#define REG_UDPHS_EPTSETSTA10          (0xF8030254U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 10) */
#define REG_UDPHS_EPTCLRSTA10          (0xF8030258U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 10) */
#define REG_UDPHS_EPTSTA10             (0xF803025CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 10) */
#define REG_UDPHS_EPTCFG11             (0xF8030260U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 11) */
#define REG_UDPHS_EPTCTLENB11          (0xF8030264U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 11) */
#define REG_UDPHS_EPTCTLDIS11          (0xF8030268U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 11) */
#define REG_UDPHS_EPTCTL11             (0xF803026CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 11) */
#define REG_UDPHS_EPTSETSTA11          (0xF8030274U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 11) */
#define REG_UDPHS_EPTCLRSTA11          (0xF8030278U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 11) */
#define REG_UDPHS_EPTSTA11             (0xF803027CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 11) */
#define REG_UDPHS_EPTCFG12             (0xF8030280U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 12) */
#define REG_UDPHS_EPTCTLENB12          (0xF8030284U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 12) */
#define REG_UDPHS_EPTCTLDIS12          (0xF8030288U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 12) */
#define REG_UDPHS_EPTCTL12             (0xF803028CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 12) */
#define REG_UDPHS_EPTSETSTA12          (0xF8030294U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 12) */
#define REG_UDPHS_EPTCLRSTA12          (0xF8030298U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 12) */
#define REG_UDPHS_EPTSTA12             (0xF803029CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 12) */
#define REG_UDPHS_EPTCFG13             (0xF80302A0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 13) */
#define REG_UDPHS_EPTCTLENB13          (0xF80302A4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 13) */
#define REG_UDPHS_EPTCTLDIS13          (0xF80302A8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 13) */
#define REG_UDPHS_EPTCTL13             (0xF80302ACU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 13) */
#define REG_UDPHS_EPTSETSTA13          (0xF80302B4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 13) */
#define REG_UDPHS_EPTCLRSTA13          (0xF80302B8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 13) */
#define REG_UDPHS_EPTSTA13             (0xF80302BCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 13) */
#define REG_UDPHS_EPTCFG14             (0xF80302C0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 14) */
#define REG_UDPHS_EPTCTLENB14          (0xF80302C4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 14) */
#define REG_UDPHS_EPTCTLDIS14          (0xF80302C8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 14) */
#define REG_UDPHS_EPTCTL14             (0xF80302CCU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 14) */
#define REG_UDPHS_EPTSETSTA14          (0xF80302D4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 14) */
#define REG_UDPHS_EPTCLRSTA14          (0xF80302D8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 14) */
#define REG_UDPHS_EPTSTA14             (0xF80302DCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 14) */
#define REG_UDPHS_EPTCFG15             (0xF80302E0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 15) */
#define REG_UDPHS_EPTCTLENB15          (0xF80302E4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 15) */
#define REG_UDPHS_EPTCTLDIS15          (0xF80302E8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 15) */
#define REG_UDPHS_EPTCTL15             (0xF80302ECU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 15) */
#define REG_UDPHS_EPTSETSTA15          (0xF80302F4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 15) */
#define REG_UDPHS_EPTCLRSTA15          (0xF80302F8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 15) */
#define REG_UDPHS_EPTSTA15             (0xF80302FCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 15) */
#define REG_UDPHS_DMANXTDSC0           (0xF8030300U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 0) */
#define REG_UDPHS_DMAADDRESS0          (0xF8030304U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 0) */
#define REG_UDPHS_DMACONTROL0          (0xF8030308U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 0) */
#define REG_UDPHS_DMASTATUS0           (0xF803030CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 0) */
#define REG_UDPHS_DMANXTDSC1           (0xF8030310U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 1) */
#define REG_UDPHS_DMAADDRESS1          (0xF8030314U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 1) */
#define REG_UDPHS_DMACONTROL1          (0xF8030318U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 1) */
#define REG_UDPHS_DMASTATUS1           (0xF803031CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 1) */
#define REG_UDPHS_DMANXTDSC2           (0xF8030320U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 2) */
#define REG_UDPHS_DMAADDRESS2          (0xF8030324U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 2) */
#define REG_UDPHS_DMACONTROL2          (0xF8030328U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 2) */
#define REG_UDPHS_DMASTATUS2           (0xF803032CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 2) */
#define REG_UDPHS_DMANXTDSC3           (0xF8030330U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 3) */
#define REG_UDPHS_DMAADDRESS3          (0xF8030334U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 3) */
#define REG_UDPHS_DMACONTROL3          (0xF8030338U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 3) */
#define REG_UDPHS_DMASTATUS3           (0xF803033CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 3) */
#define REG_UDPHS_DMANXTDSC4           (0xF8030340U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 4) */
#define REG_UDPHS_DMAADDRESS4          (0xF8030344U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 4) */
#define REG_UDPHS_DMACONTROL4          (0xF8030348U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 4) */
#define REG_UDPHS_DMASTATUS4           (0xF803034CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 4) */
#define REG_UDPHS_DMANXTDSC5           (0xF8030350U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 5) */
#define REG_UDPHS_DMAADDRESS5          (0xF8030354U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 5) */
#define REG_UDPHS_DMACONTROL5          (0xF8030358U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 5) */
#define REG_UDPHS_DMASTATUS5           (0xF803035CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 5) */
#define REG_UDPHS_DMANXTDSC6           (0xF8030360U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 6) */
#define REG_UDPHS_DMAADDRESS6          (0xF8030364U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 6) */
#define REG_UDPHS_DMACONTROL6          (0xF8030368U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 6) */
#define REG_UDPHS_DMASTATUS6           (0xF803036CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 6) */
#else
#define REG_UDPHS_CTRL        (*(RwReg*)0xF8030000U) /**< \brief (UDPHS) UDPHS Control Register */
#define REG_UDPHS_FNUM        (*(RoReg*)0xF8030004U) /**< \brief (UDPHS) UDPHS Frame Number Register */
#define REG_UDPHS_IEN         (*(RwReg*)0xF8030010U) /**< \brief (UDPHS) UDPHS Interrupt Enable Register */
#define REG_UDPHS_INTSTA      (*(RoReg*)0xF8030014U) /**< \brief (UDPHS) UDPHS Interrupt Status Register */
#define REG_UDPHS_CLRINT      (*(WoReg*)0xF8030018U) /**< \brief (UDPHS) UDPHS Clear Interrupt Register */
#define REG_UDPHS_EPTRST      (*(WoReg*)0xF803001CU) /**< \brief (UDPHS) UDPHS Endpoints Reset Register */
#define REG_UDPHS_TST         (*(RwReg*)0xF80300E0U) /**< \brief (UDPHS) UDPHS Test Register */
#define REG_UDPHS_IPNAME1     (*(RoReg*)0xF80300F0U) /**< \brief (UDPHS) UDPHS Name1 Register */
#define REG_UDPHS_IPNAME2     (*(RoReg*)0xF80300F4U) /**< \brief (UDPHS) UDPHS Name2 Register */
#define REG_UDPHS_IPFEATURES  (*(RoReg*)0xF80300F8U) /**< \brief (UDPHS) UDPHS Features Register */
#define REG_UDPHS_EPTCFG0     (*(RwReg*)0xF8030100U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 0) */
#define REG_UDPHS_EPTCTLENB0  (*(WoReg*)0xF8030104U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 0) */
#define REG_UDPHS_EPTCTLDIS0  (*(WoReg*)0xF8030108U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 0) */
#define REG_UDPHS_EPTCTL0     (*(RoReg*)0xF803010CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 0) */
#define REG_UDPHS_EPTSETSTA0  (*(WoReg*)0xF8030114U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 0) */
#define REG_UDPHS_EPTCLRSTA0  (*(WoReg*)0xF8030118U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 0) */
#define REG_UDPHS_EPTSTA0     (*(RoReg*)0xF803011CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 0) */
#define REG_UDPHS_EPTCFG1     (*(RwReg*)0xF8030120U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 1) */
#define REG_UDPHS_EPTCTLENB1  (*(WoReg*)0xF8030124U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 1) */
#define REG_UDPHS_EPTCTLDIS1  (*(WoReg*)0xF8030128U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 1) */
#define REG_UDPHS_EPTCTL1     (*(RoReg*)0xF803012CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 1) */
#define REG_UDPHS_EPTSETSTA1  (*(WoReg*)0xF8030134U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 1) */
#define REG_UDPHS_EPTCLRSTA1  (*(WoReg*)0xF8030138U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 1) */
#define REG_UDPHS_EPTSTA1     (*(RoReg*)0xF803013CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 1) */
#define REG_UDPHS_EPTCFG2     (*(RwReg*)0xF8030140U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 2) */
#define REG_UDPHS_EPTCTLENB2  (*(WoReg*)0xF8030144U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 2) */
#define REG_UDPHS_EPTCTLDIS2  (*(WoReg*)0xF8030148U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 2) */
#define REG_UDPHS_EPTCTL2     (*(RoReg*)0xF803014CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 2) */
#define REG_UDPHS_EPTSETSTA2  (*(WoReg*)0xF8030154U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 2) */
#define REG_UDPHS_EPTCLRSTA2  (*(WoReg*)0xF8030158U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 2) */
#define REG_UDPHS_EPTSTA2     (*(RoReg*)0xF803015CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 2) */
#define REG_UDPHS_EPTCFG3     (*(RwReg*)0xF8030160U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 3) */
#define REG_UDPHS_EPTCTLENB3  (*(WoReg*)0xF8030164U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 3) */
#define REG_UDPHS_EPTCTLDIS3  (*(WoReg*)0xF8030168U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 3) */
#define REG_UDPHS_EPTCTL3     (*(RoReg*)0xF803016CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 3) */
#define REG_UDPHS_EPTSETSTA3  (*(WoReg*)0xF8030174U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 3) */
#define REG_UDPHS_EPTCLRSTA3  (*(WoReg*)0xF8030178U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 3) */
#define REG_UDPHS_EPTSTA3     (*(RoReg*)0xF803017CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 3) */
#define REG_UDPHS_EPTCFG4     (*(RwReg*)0xF8030180U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 4) */
#define REG_UDPHS_EPTCTLENB4  (*(WoReg*)0xF8030184U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 4) */
#define REG_UDPHS_EPTCTLDIS4  (*(WoReg*)0xF8030188U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 4) */
#define REG_UDPHS_EPTCTL4     (*(RoReg*)0xF803018CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 4) */
#define REG_UDPHS_EPTSETSTA4  (*(WoReg*)0xF8030194U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 4) */
#define REG_UDPHS_EPTCLRSTA4  (*(WoReg*)0xF8030198U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 4) */
#define REG_UDPHS_EPTSTA4     (*(RoReg*)0xF803019CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 4) */
#define REG_UDPHS_EPTCFG5     (*(RwReg*)0xF80301A0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 5) */
#define REG_UDPHS_EPTCTLENB5  (*(WoReg*)0xF80301A4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 5) */
#define REG_UDPHS_EPTCTLDIS5  (*(WoReg*)0xF80301A8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 5) */
#define REG_UDPHS_EPTCTL5     (*(RoReg*)0xF80301ACU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 5) */
#define REG_UDPHS_EPTSETSTA5  (*(WoReg*)0xF80301B4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 5) */
#define REG_UDPHS_EPTCLRSTA5  (*(WoReg*)0xF80301B8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 5) */
#define REG_UDPHS_EPTSTA5     (*(RoReg*)0xF80301BCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 5) */
#define REG_UDPHS_EPTCFG6     (*(RwReg*)0xF80301C0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 6) */
#define REG_UDPHS_EPTCTLENB6  (*(WoReg*)0xF80301C4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 6) */
#define REG_UDPHS_EPTCTLDIS6  (*(WoReg*)0xF80301C8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 6) */
#define REG_UDPHS_EPTCTL6     (*(RoReg*)0xF80301CCU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 6) */
#define REG_UDPHS_EPTSETSTA6  (*(WoReg*)0xF80301D4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 6) */
#define REG_UDPHS_EPTCLRSTA6  (*(WoReg*)0xF80301D8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 6) */
#define REG_UDPHS_EPTSTA6     (*(RoReg*)0xF80301DCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 6) */
#define REG_UDPHS_EPTCFG7     (*(RwReg*)0xF80301E0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 7) */
#define REG_UDPHS_EPTCTLENB7  (*(WoReg*)0xF80301E4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 7) */
#define REG_UDPHS_EPTCTLDIS7  (*(WoReg*)0xF80301E8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 7) */
#define REG_UDPHS_EPTCTL7     (*(RoReg*)0xF80301ECU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 7) */
#define REG_UDPHS_EPTSETSTA7  (*(WoReg*)0xF80301F4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 7) */
#define REG_UDPHS_EPTCLRSTA7  (*(WoReg*)0xF80301F8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 7) */
#define REG_UDPHS_EPTSTA7     (*(RoReg*)0xF80301FCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 7) */
#define REG_UDPHS_EPTCFG8     (*(RwReg*)0xF8030200U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 8) */
#define REG_UDPHS_EPTCTLENB8  (*(WoReg*)0xF8030204U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 8) */
#define REG_UDPHS_EPTCTLDIS8  (*(WoReg*)0xF8030208U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 8) */
#define REG_UDPHS_EPTCTL8     (*(RoReg*)0xF803020CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 8) */
#define REG_UDPHS_EPTSETSTA8  (*(WoReg*)0xF8030214U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 8) */
#define REG_UDPHS_EPTCLRSTA8  (*(WoReg*)0xF8030218U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 8) */
#define REG_UDPHS_EPTSTA8     (*(RoReg*)0xF803021CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 8) */
#define REG_UDPHS_EPTCFG9     (*(RwReg*)0xF8030220U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 9) */
#define REG_UDPHS_EPTCTLENB9  (*(WoReg*)0xF8030224U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 9) */
#define REG_UDPHS_EPTCTLDIS9  (*(WoReg*)0xF8030228U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 9) */
#define REG_UDPHS_EPTCTL9     (*(RoReg*)0xF803022CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 9) */
#define REG_UDPHS_EPTSETSTA9  (*(WoReg*)0xF8030234U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 9) */
#define REG_UDPHS_EPTCLRSTA9  (*(WoReg*)0xF8030238U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 9) */
#define REG_UDPHS_EPTSTA9     (*(RoReg*)0xF803023CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 9) */
#define REG_UDPHS_EPTCFG10    (*(RwReg*)0xF8030240U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 10) */
#define REG_UDPHS_EPTCTLENB10 (*(WoReg*)0xF8030244U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 10) */
#define REG_UDPHS_EPTCTLDIS10 (*(WoReg*)0xF8030248U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 10) */
#define REG_UDPHS_EPTCTL10    (*(RoReg*)0xF803024CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 10) */
#define REG_UDPHS_EPTSETSTA10 (*(WoReg*)0xF8030254U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 10) */
#define REG_UDPHS_EPTCLRSTA10 (*(WoReg*)0xF8030258U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 10) */
#define REG_UDPHS_EPTSTA10    (*(RoReg*)0xF803025CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 10) */
#define REG_UDPHS_EPTCFG11    (*(RwReg*)0xF8030260U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 11) */
#define REG_UDPHS_EPTCTLENB11 (*(WoReg*)0xF8030264U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 11) */
#define REG_UDPHS_EPTCTLDIS11 (*(WoReg*)0xF8030268U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 11) */
#define REG_UDPHS_EPTCTL11    (*(RoReg*)0xF803026CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 11) */
#define REG_UDPHS_EPTSETSTA11 (*(WoReg*)0xF8030274U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 11) */
#define REG_UDPHS_EPTCLRSTA11 (*(WoReg*)0xF8030278U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 11) */
#define REG_UDPHS_EPTSTA11    (*(RoReg*)0xF803027CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 11) */
#define REG_UDPHS_EPTCFG12    (*(RwReg*)0xF8030280U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 12) */
#define REG_UDPHS_EPTCTLENB12 (*(WoReg*)0xF8030284U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 12) */
#define REG_UDPHS_EPTCTLDIS12 (*(WoReg*)0xF8030288U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 12) */
#define REG_UDPHS_EPTCTL12    (*(RoReg*)0xF803028CU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 12) */
#define REG_UDPHS_EPTSETSTA12 (*(WoReg*)0xF8030294U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 12) */
#define REG_UDPHS_EPTCLRSTA12 (*(WoReg*)0xF8030298U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 12) */
#define REG_UDPHS_EPTSTA12    (*(RoReg*)0xF803029CU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 12) */
#define REG_UDPHS_EPTCFG13    (*(RwReg*)0xF80302A0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 13) */
#define REG_UDPHS_EPTCTLENB13 (*(WoReg*)0xF80302A4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 13) */
#define REG_UDPHS_EPTCTLDIS13 (*(WoReg*)0xF80302A8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 13) */
#define REG_UDPHS_EPTCTL13    (*(RoReg*)0xF80302ACU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 13) */
#define REG_UDPHS_EPTSETSTA13 (*(WoReg*)0xF80302B4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 13) */
#define REG_UDPHS_EPTCLRSTA13 (*(WoReg*)0xF80302B8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 13) */
#define REG_UDPHS_EPTSTA13    (*(RoReg*)0xF80302BCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 13) */
#define REG_UDPHS_EPTCFG14    (*(RwReg*)0xF80302C0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 14) */
#define REG_UDPHS_EPTCTLENB14 (*(WoReg*)0xF80302C4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 14) */
#define REG_UDPHS_EPTCTLDIS14 (*(WoReg*)0xF80302C8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 14) */
#define REG_UDPHS_EPTCTL14    (*(RoReg*)0xF80302CCU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 14) */
#define REG_UDPHS_EPTSETSTA14 (*(WoReg*)0xF80302D4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 14) */
#define REG_UDPHS_EPTCLRSTA14 (*(WoReg*)0xF80302D8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 14) */
#define REG_UDPHS_EPTSTA14    (*(RoReg*)0xF80302DCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 14) */
#define REG_UDPHS_EPTCFG15    (*(RwReg*)0xF80302E0U) /**< \brief (UDPHS) UDPHS Endpoint Configuration Register (endpoint = 15) */
#define REG_UDPHS_EPTCTLENB15 (*(WoReg*)0xF80302E4U) /**< \brief (UDPHS) UDPHS Endpoint Control Enable Register (endpoint = 15) */
#define REG_UDPHS_EPTCTLDIS15 (*(WoReg*)0xF80302E8U) /**< \brief (UDPHS) UDPHS Endpoint Control Disable Register (endpoint = 15) */
#define REG_UDPHS_EPTCTL15    (*(RoReg*)0xF80302ECU) /**< \brief (UDPHS) UDPHS Endpoint Control Register (endpoint = 15) */
#define REG_UDPHS_EPTSETSTA15 (*(WoReg*)0xF80302F4U) /**< \brief (UDPHS) UDPHS Endpoint Set Status Register (endpoint = 15) */
#define REG_UDPHS_EPTCLRSTA15 (*(WoReg*)0xF80302F8U) /**< \brief (UDPHS) UDPHS Endpoint Clear Status Register (endpoint = 15) */
#define REG_UDPHS_EPTSTA15    (*(RoReg*)0xF80302FCU) /**< \brief (UDPHS) UDPHS Endpoint Status Register (endpoint = 15) */
#define REG_UDPHS_DMANXTDSC0  (*(RwReg*)0xF8030300U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 0) */
#define REG_UDPHS_DMAADDRESS0 (*(RwReg*)0xF8030304U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 0) */
#define REG_UDPHS_DMACONTROL0 (*(RwReg*)0xF8030308U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 0) */
#define REG_UDPHS_DMASTATUS0  (*(RwReg*)0xF803030CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 0) */
#define REG_UDPHS_DMANXTDSC1  (*(RwReg*)0xF8030310U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 1) */
#define REG_UDPHS_DMAADDRESS1 (*(RwReg*)0xF8030314U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 1) */
#define REG_UDPHS_DMACONTROL1 (*(RwReg*)0xF8030318U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 1) */
#define REG_UDPHS_DMASTATUS1  (*(RwReg*)0xF803031CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 1) */
#define REG_UDPHS_DMANXTDSC2  (*(RwReg*)0xF8030320U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 2) */
#define REG_UDPHS_DMAADDRESS2 (*(RwReg*)0xF8030324U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 2) */
#define REG_UDPHS_DMACONTROL2 (*(RwReg*)0xF8030328U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 2) */
#define REG_UDPHS_DMASTATUS2  (*(RwReg*)0xF803032CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 2) */
#define REG_UDPHS_DMANXTDSC3  (*(RwReg*)0xF8030330U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 3) */
#define REG_UDPHS_DMAADDRESS3 (*(RwReg*)0xF8030334U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 3) */
#define REG_UDPHS_DMACONTROL3 (*(RwReg*)0xF8030338U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 3) */
#define REG_UDPHS_DMASTATUS3  (*(RwReg*)0xF803033CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 3) */
#define REG_UDPHS_DMANXTDSC4  (*(RwReg*)0xF8030340U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 4) */
#define REG_UDPHS_DMAADDRESS4 (*(RwReg*)0xF8030344U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 4) */
#define REG_UDPHS_DMACONTROL4 (*(RwReg*)0xF8030348U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 4) */
#define REG_UDPHS_DMASTATUS4  (*(RwReg*)0xF803034CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 4) */
#define REG_UDPHS_DMANXTDSC5  (*(RwReg*)0xF8030350U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 5) */
#define REG_UDPHS_DMAADDRESS5 (*(RwReg*)0xF8030354U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 5) */
#define REG_UDPHS_DMACONTROL5 (*(RwReg*)0xF8030358U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 5) */
#define REG_UDPHS_DMASTATUS5  (*(RwReg*)0xF803035CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 5) */
#define REG_UDPHS_DMANXTDSC6  (*(RwReg*)0xF8030360U) /**< \brief (UDPHS) UDPHS DMA Next Descriptor Address Register (channel = 6) */
#define REG_UDPHS_DMAADDRESS6 (*(RwReg*)0xF8030364U) /**< \brief (UDPHS) UDPHS DMA Channel Address Register (channel = 6) */
#define REG_UDPHS_DMACONTROL6 (*(RwReg*)0xF8030368U) /**< \brief (UDPHS) UDPHS DMA Channel Control Register (channel = 6) */
#define REG_UDPHS_DMASTATUS6  (*(RwReg*)0xF803036CU) /**< \brief (UDPHS) UDPHS DMA Channel Status Register (channel = 6) */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMA5_UDPHS_INSTANCE_ */
