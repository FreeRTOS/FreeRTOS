/**
 * \file
 *
 * \brief ASF Patch Header file definitions for SAM4L.
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef SAM4L_PATCH_ASF_H_INCLUDED
#define SAM4L_PATCH_ASF_H_INCLUDED

// These defines are used for sam/drivers/flashcalw implementation.
#define   FLASHCALW_FCMD_CMD_HSEN    (0x10u <<  0)
#define   FLASHCALW_FCMD_CMD_HSDIS   (0x11u <<  0)

// These defines are used to keep compatibility with existing 
// sam/drivers/usart implementation from SAM3/4 products with SAM4L product.
#define US_MR_USART_MODE_HW_HANDSHAKING     US_MR_USART_MODE_HARDWARE
#define US_MR_USART_MODE_IS07816_T_0        US_MR_USART_MODE_ISO7816_T0
#define US_MR_USART_MODE_IS07816_T_1        US_MR_USART_MODE_ISO7816_T1
#define US_MR_NBSTOP_2_BIT                  US_MR_NBSTOP_2
#define US_MR_NBSTOP_1_5_BIT                US_MR_NBSTOP_1_5
#define US_MR_NBSTOP_1_BIT                  US_MR_NBSTOP_1
#define US_MR_CHRL_8_BIT                    US_MR_CHRL_8
#define US_MR_PAR_NO                        US_MR_PAR_NONE
#define US_MR_PAR_MULTIDROP                 US_MR_PAR_MULTI
#define US_IF                               US_IFR
#define US_WPSR_WPVS                        US_WPSR_WPV_1

#if (!defined SCIF_RCOSC_FREQUENCY)
#    define SCIF_RCOSC_FREQUENCY            115200
#endif

// These defines for homogeneity with other SAM header files.
#define CHIP_FREQ_FWS_0                     (18000000UL) /**< \brief Maximum operating frequency when FWS is 0 */
#define CHIP_FREQ_FWS_1                     (36000000UL) /**< \brief Maximum operating frequency when FWS is 1 */
// WARNING NOTE: these are preliminary values.
#define CHIP_FREQ_FLASH_HSEN_FWS_0          (18000000UL) /**< \brief Maximum operating frequency when FWS is 0 and the FLASH HS mode is enabled */
#define CHIP_FREQ_FLASH_HSEN_FWS_1          (36000000UL) /**< \brief Maximum operating frequency when FWS is 1 and the FLASH HS mode is enabled */

// Size of HRAMC1 with 32-bit access
#undef HRAMC1_SIZE
#define HRAMC1_SIZE                         (0x800UL)

// USBC related offsets
#define USBC_UHINT_P0INT_Pos                                   8
#define USBC_UHINTE_P0INTE_Pos                                 8
#define USBC_UPCFG0_PBK_Pos                                    2
#define USBC_UPCFG0_PBK_Msk                     (0x1u << USBC_UPCFG0_PBK_Pos)

// These defines are used to keep compatibility with existing 
// sam/drivers/tc implementation from SAM3/4 products with SAM4L product. 
#define	TC_SMMR                TC_SMC
#define	TC_CMR_LDRA_RISING     TC_CMR_LDRA_POS_EDGE_TIOA
#define	TC_CMR_LDRB_FALLING    TC_CMR_LDRB_NEG_EDGE_TIOA
#define	TC_CMR_ETRGEDG_FALLING TC_CMR_ETRGEDG_NEG_EDGE

// These defines are used to keep compatibility with existing 
// sam/drivers/spi implementation from SAM3/4 products with SAM4L product. 
#define SPI_CSR_BITS_8_BIT     SPI_CSR_BITS_8_BPT

#define SPI_WPSR_WPVS_Pos      SPI_WPSR_SPIWPVS_Pos
#define SPI_WPSR_WPVS_Msk      SPI_WPSR_SPIWPVS_Msk
#define SPI_WPSR_WPVSRC_Pos    SPI_WPSR_SPIWPVSRC_Pos
#define SPI_WPSR_WPVSRC_Msk    SPI_WPSR_SPIWPVSRC_Msk

// These defines are used to keep compatibility with existing 
// sam/drivers/crccu implementation from SAM3/4 products with SAM4L product. 
#define	CRCCU_DMA_EN 	          CRCCU_DMAEN
#define	CRCCU_DMA_DIS             CRCCU_DMADIS
#define	CRCCU_DMA_SR	          CRCCU_DMASR
#define	CRCCU_DMA_IER 	          CRCCU_DMAIER
#define	CRCCU_DMA_IDR             CRCCU_DMAIDR
#define	CRCCU_DMA_IMR	          CRCCU_DMAIMR
#define	CRCCU_DMA_ISR	          CRCCU_DMAISR
#define	CRCCU_DMA_EN_DMAEN 	      CRCCU_DMAEN_DMAEN
#define	CRCCU_DMA_DIS_DMADIS      CRCCU_DMADIS_DMADIS
#define	CRCCU_DMA_SR_DMASR        CRCCU_DMASR_DMASR
#define	CRCCU_DMA_IER_DMAIER      CRCCU_DMAIER_DMAIER
#define	CRCCU_DMA_IDR_DMAIDR      CRCCU_DMAIDR_DMAIDR
#define	CRCCU_DMA_IMR_DMAIMR      CRCCU_DMAIMR_DMAIMR
#define	CRCCU_DMA_ISR_DMAISR      CRCCU_DMAISR_DMAISR
#define	CRCCU_MR_PTYPE_CCITT8023  CRCCU_MR_PTYPE(0)
#define	CRCCU_MR_PTYPE_CASTAGNOLI CRCCU_MR_PTYPE(1)
#define	CRCCU_MR_PTYPE_CCITT16    CRCCU_MR_PTYPE(2)

#endif  // SAM4L_PATCH_ASF_H_INCLUDED
