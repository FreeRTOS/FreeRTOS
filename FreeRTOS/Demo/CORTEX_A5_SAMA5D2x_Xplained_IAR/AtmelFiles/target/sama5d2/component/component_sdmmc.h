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

#ifndef _SAMA5D2_SDMMC_COMPONENT_
#define _SAMA5D2_SDMMC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Secure Digital MultiMedia Card Controller       */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SDMMC Secure Digital MultiMedia Card Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief SDMMC hardware registers */
typedef struct {
  __IO uint32_t SDMMC_SSAR;         /**< \brief (SDMMC Offset: 0x000) SDMA System Address - Argument 2 Register */
  __IO uint16_t SDMMC_BSR;          /**< \brief (SDMMC Offset: 0x004) Block Size Register */
  __IO uint16_t SDMMC_BCR;          /**< \brief (SDMMC Offset: 0x006) Block Count Register */
  __IO uint32_t SDMMC_ARG1R;        /**< \brief (SDMMC Offset: 0x008) Argument 1 Register */
  __IO uint16_t SDMMC_TMR;          /**< \brief (SDMMC Offset: 0x00C) Transfer Mode Register */
  __IO uint16_t SDMMC_CR;           /**< \brief (SDMMC Offset: 0x00E) Command Register */
  __I  uint32_t SDMMC_RR[4];        /**< \brief (SDMMC Offset: 0x010) Response Register */
  __IO uint32_t SDMMC_BDPR;         /**< \brief (SDMMC Offset: 0x020) Buffer Data Port Register */
  __I  uint32_t SDMMC_PSR;          /**< \brief (SDMMC Offset: 0x024) Present State Register */
  __IO uint8_t  SDMMC_HC1R;         /**< \brief (SDMMC Offset: 0x028) Host Control 1 Register */
  __IO uint8_t  SDMMC_PCR;          /**< \brief (SDMMC Offset: 0x029) Power Control Register */
  __IO uint8_t  SDMMC_BGCR;         /**< \brief (SDMMC Offset: 0x02A) Block Gap Control Register */
  __IO uint8_t  SDMMC_WCR;          /**< \brief (SDMMC Offset: 0x02B) Wakeup Control Register */
  __IO uint16_t SDMMC_CCR;          /**< \brief (SDMMC Offset: 0x02C) Clock Control Register */
  __IO uint8_t  SDMMC_TCR;          /**< \brief (SDMMC Offset: 0x02E) Timeout Control Register */
  __IO uint8_t  SDMMC_SRR;          /**< \brief (SDMMC Offset: 0x02F) Software Reset Register */
  __IO uint16_t SDMMC_NISTR;        /**< \brief (SDMMC Offset: 0x030) Normal Interrupt Status Register */
  __IO uint16_t SDMMC_EISTR;        /**< \brief (SDMMC Offset: 0x032) Error Interrupt Status Register */
  __IO uint16_t SDMMC_NISTER;       /**< \brief (SDMMC Offset: 0x034) Normal Interrupt Status Enable Register */
  __IO uint16_t SDMMC_EISTER;       /**< \brief (SDMMC Offset: 0x036) Error Interrupt Status Enable Register */
  __IO uint16_t SDMMC_NISIER;       /**< \brief (SDMMC Offset: 0x038) Normal Interrupt Signal Enable Register */
  __IO uint16_t SDMMC_EISIER;       /**< \brief (SDMMC Offset: 0x03A) Error Interrupt Signal Enable Register */
  __I  uint16_t SDMMC_ACESR;        /**< \brief (SDMMC Offset: 0x03C) Auto CMD Error Status Register */
  __IO uint16_t SDMMC_HC2R;         /**< \brief (SDMMC Offset: 0x03E) Host Control 2 Register */
  __IO uint32_t SDMMC_CA0R;         /**< \brief (SDMMC Offset: 0x040) Capabilities Register */
  __IO uint32_t SDMMC_CA1R;         /**< \brief (SDMMC Offset: 0x044) Capabilities Register */
  __IO uint32_t SDMMC_MCCAR;        /**< \brief (SDMMC Offset: 0x048) Maximum Current Capabilities Register */
  __I  uint32_t SDMMC_RSVD1;        /**< \brief (SDMMC Offset: 0x04C) Reserved */
  __O  uint16_t SDMMC_FERACES;      /**< \brief (SDMMC Offset: 0x050) Force Event Register for Auto CMD Error Status */
  __O  uint16_t SDMMC_FEREIS;       /**< \brief (SDMMC Offset: 0x052) Force Event Register for Error Interrupt Status */
  __I  uint8_t  SDMMC_AESR;         /**< \brief (SDMMC Offset: 0x054) ADMA Error Status Register */
  __I  uint8_t  SDMMC_RSVD2[3];     /**< \brief (SDMMC Offset: 0x055 - 0x57) Reserved */
  __IO uint32_t SDMMC_ASA0R;        /**< \brief (SDMMC Offset: 0x058) ADMA System Address Register */
  __I  uint32_t SDMMC_RSVD3[1];     /**< \brief (SDMMC Offset: 0x05C) Reserved */
  __IO uint16_t SDMMC_PVR[8];       /**< \brief (SDMMC Offset: 0x060) Preset Value Register */
  __I  uint32_t SDMMC_RSVD4[35];    /**< \brief (SDMMC Offset: 0x070 - 0xF8) Reserved */
  __I  uint16_t SDMMC_SISR;         /**< \brief (SDMMC Offset: 0x0FC) Slot Interrupt Status Register */
  __I  uint16_t SDMMC_HCVR;         /**< \brief (SDMMC Offset: 0x0FE) Host Controller Version Register */

  __I  uint32_t SDMMC_RSVD5[64];    /**< \brief (SDMMC Offset: 0x100 - 0x1FC) Reserved */

  __I  uint32_t SDMMC_APSR;         /**< \brief (SDMMC Offset: 0x200) Additionnal Present State Register */
  __IO uint8_t  SDMMC_MC1R;         /**< \brief (SDMMC Offset: 0x204) MMC Control 1 Register */
  __O  uint8_t  SDMMC_MC2R;         /**< \brief (SDMMC Offset: 0x205) MMC Control 2 Register */
  __I  uint8_t  SDMMC_RSVD6[2];     /**< \brief (SDMMC Offset: 0x206 - 0x207) Reserved */
  __IO uint32_t SDMMC_ACR;          /**< \brief (SDMMC Offset: 0x208) AHB Control Register */
  __IO uint32_t SDMMC_CC2R;         /**< \brief (SDMMC Offset: 0x20C) Clock Control 2 Register */
  __IO uint8_t  SDMMC_RTC1R;        /**< \brief (SDMMC Offset: 0x210) Retuning Timer Control 1 Register */
  __O  uint8_t  SDMMC_RTC2R;        /**< \brief (SDMMC Offset: 0x211) Retuning Timer Control 2 Register */
  __I  uint8_t  SDMMC_RSVD7[2];     /**< \brief (SDMMC Offset: 0x212 - 0x213) Reserved */
  __IO uint32_t SDMMC_RTCVR;        /**< \brief (SDMMC Offset: 0x214) Retuning Timer Counter Value Register */
  __IO uint8_t  SDMMC_RTISTER;      /**< \brief (SDMMC Offset: 0x218) Retuning Timer Interrupt Status Enable Register */
  __IO uint8_t  SDMMC_RTISIER;      /**< \brief (SDMMC Offset: 0x219) Retuning Timer Interrupt Signal Enable Register */
  __I  uint8_t  SDMMC_RSVD11[2];    /**< \brief (SDMMC Offset: 0x21A - 0x21B) Reserved */
  __IO uint8_t  SDMMC_RTISTR;       /**< \brief (SDMMC Offset: 0x21C) Retuning Timer Interrupt Status Register */
  __I  uint8_t  SDMMC_RTSSR;        /**< \brief (SDMMC Offset: 0x21D) Retuning Timer Status Slots Register */
  __I  uint8_t  SDMMC_RSVD12[2];    /**< \brief (SDMMC Offset: 0x21E - 0x21F) Reserved */
  __IO uint32_t SDMMC_TUNCR;        /**< \brief (SDMMC Offset: 0x220) Tuning Control Register */
  __I  uint32_t SDMMC_RSVD8[3];     /**< \brief (SDMMC Offset: 0x224 - 0x22C) Reserved */
  __IO uint32_t SDMMC_CACR;         /**< \brief (SDMMC Offset: 0x230) Capabilities Control Register */
  __I  uint32_t SDMMC_RSVD9[3];     /**< \brief (SDMMC Offset: 0x234 - 0x23C) Reserved */
  __IO uint32_t SDMMC_CALCR;        /**< \brief (SDMMC Offset: 0x240) Calibration Control Register */
  __I  uint32_t SDMMC_RSVD10[47];   /**< \brief (SDMMC Offset: 0x244 - 0x2FC) Reserved */
} Sdmmc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* --------  SDMMC_SSAR (SDMMC Offset: 0x000) SDMA System Address - Argument 2 Register */
#define SDMMC_SSAR_ADDR_Pos 0
#define SDMMC_SSAR_ADDR_Msk (0xFFFFFFFFu << SDMMC_SSAR_ADDR_Pos)
#define SDMMC_SSAR_ADDR(value) ((SDMMC_SSAR_ADDR_Msk & ((value) << SDMMC_SSAR_ADDR_Pos)))
#define SDMMC_SSAR_ARG2_Pos 0
#define SDMMC_SSAR_ARG2_Msk (0xFFFFFFFFu << SDMMC_SSAR_ARG2_Pos)
#define SDMMC_SSAR_ARG2(value) ((SDMMC_SSAR_ARG2_Msk & ((value) << SDMMC_SSAR_ARG2_Pos)))
/* --------  SDMMC_BSR (SDMMC Offset: 0x004) Block Size Register */
#define SDMMC_BSR_BLKSIZE_Pos 0
#define SDMMC_BSR_BLKSIZE_Msk (0xFFFu << SDMMC_BSR_BLKSIZE_Pos)
#define SDMMC_BSR_BLKSIZE(value) ((SDMMC_BSR_BLKSIZE_Msk & ((value) << SDMMC_BSR_BLKSIZE_Pos)))
#define SDMMC_BSR_BOUNDARY_Pos 12
#define SDMMC_BSR_BOUNDARY_Msk (0x7u << SDMMC_BSR_BOUNDARY_Pos)
#define SDMMC_BSR_BOUNDARY(value) ((SDMMC_BSR_BOUNDARY_Msk & ((value) << SDMMC_BSR_BOUNDARY_Pos)))
/* --------  SDMMC_BCR (SDMMC Offset: 0x006) Block Count Register */
#define SDMMC_BCR_BLKCNT_Pos 0
#define SDMMC_BCR_BLKCNT_Msk (0xFFFFu << SDMMC_BCR_BLKCNT_Pos)
#define SDMMC_BCR_BLKCNT(value) ((SDMMC_BCR_BLKCNT_Msk & ((value) << SDMMC_BCR_BLKCNT_Pos)))
/* --------  SDMMC_ARG1R (SDMMC Offset: 0x008) Argument 1 Register */
#define SDMMC_ARG1R_ARG1_Pos 0
#define SDMMC_ARG1R_ARG1_Msk (0xFFFFFFFFu << SDMMC_ARG1R_ARG1_Pos)
#define SDMMC_ARG1R_ARG1(value) ((SDMMC_ARG1R_ARG1_Msk & ((value) << SDMMC_ARG1R_ARG1_Pos)))
/* --------  SDMMC_TMR (SDMMC Offset: 0x00C) Transfer Mode Register */
#define SDMMC_TMR_DMAEN (0x1u << 0)
#define SDMMC_TMR_BCEN (0x1u << 1)
#define SDMMC_TMR_ACMDEN_Pos 2
#define SDMMC_TMR_ACMDEN_Msk (0x3u << SDMMC_TMR_ACMDEN_Pos)
#define   SDMMC_TMR_ACMDEN_DIS (0x0u << 2)
#define   SDMMC_TMR_ACMDEN_ACMD12 (0x1u << 2)
#define   SDMMC_TMR_ACMDEN_ACMD23 (0x2u << 2)
#define SDMMC_TMR_DTDSEL (0x1u << 4)
#define   SDMMC_TMR_DTDSEL_WR (0x0u << 4)
#define   SDMMC_TMR_DTDSEL_RD (0x1u << 4)
#define SDMMC_TMR_MSBSEL (0x1u << 5)
/* --------  SDMMC_CR (SDMMC Offset: 0x00E) Command Register */
#define SDMMC_CR_RESPTYP_Pos 0
#define SDMMC_CR_RESPTYP_Msk (0x3u << SDMMC_CR_RESPTYP_Pos)
#define   SDMMC_CR_RESPTYP_NORESP (0x0u << 0)
#define   SDMMC_CR_RESPTYP_RL136 (0x1u << 0)
#define   SDMMC_CR_RESPTYP_RL48 (0x2u << 0)
#define   SDMMC_CR_RESPTYP_RL48BUSY (0x3u << 0)
#define SDMMC_CR_CMDCCEN (0x1u << 3)
#define SDMMC_CR_CMDICEN (0x1u << 4)
#define SDMMC_CR_DPSEL (0x1u << 5)
#define SDMMC_CR_CMDTYP_Pos 6
#define SDMMC_CR_CMDTYP_Msk (0x3u << SDMMC_CR_CMDTYP_Pos)
#define   SDMMC_CR_CMDTYP_NORMAL (0x0u << 6)
#define   SDMMC_CR_CMDTYP_SUSPEND (0x1u << 6)
#define   SDMMC_CR_CMDTYP_RESUME (0x2u << 6)
#define   SDMMC_CR_CMDTYP_ABORT (0x3u << 6)
#define SDMMC_CR_CMDIDX_Pos 8
#define SDMMC_CR_CMDIDX_Msk (0x3F << SDMMC_CR_CMDIDX_Pos)
#define SDMMC_CR_CMDIDX(value) ((SDMMC_CR_CMDIDX_Msk & ((value) << SDMMC_CR_CMDIDX_Pos)))
/* --------  SDMMC_RR[4] (SDMMC Offset: 0x010) Response Register */
#define SDMMC_RR_CMDRESP_Pos 0
#define SDMMC_RR_CMDRESP_Msk (0xFFFFFFFFu << SDMMC_RR_CMDRESP_Pos)
/* --------  SDMMC_BDPR Buffer Data Port Register */
#define SDMMC_BDPR_BUFDATA_Pos 0
#define SDMMC_BDPR_BUFDATA_Msk (0xFFFFFFFFu << SDMMC_BDPR_BUFDATA_Pos)
#define SDMMC_BDPR_BUFDATA(value) ((SDMMC_BDPR_BUFDATA_Msk & ((value) << SDMMC_BDPR_BUFDATA_Pos)))
/* --------  SDMMC_PSR (SDMMC Offset: 0x024) Present State Register */
#define SDMMC_PSR_CMDINHC (0x1u << 0)
#define SDMMC_PSR_CMDINHD (0x1u << 1)
#define SDMMC_PSR_DLACT (0x1u << 2)
#define SDMMC_PSR_RTREQ (0x1u << 3)
#define SDMMC_PSR_WTACT (0x1u << 8)
#define SDMMC_PSR_RTACT (0x1u << 9)
#define SDMMC_PSR_BUFWREN (0x1u << 10)
#define SDMMC_PSR_BUFRDEN (0x1u << 11)
#define SDMMC_PSR_CARDINS (0x1u << 16)
#define SDMMC_PSR_CARDSS (0x1u << 17)
#define SDMMC_PSR_CARDDPL (0x1u << 18)
#define SDMMC_PSR_WRPPL (0x1u << 19)
#define SDMMC_PSR_DATLL_Pos 20
#define SDMMC_PSR_DATLL_Msk (0xFu << SDMMC_PSR_DATLL_Pos)
#define SDMMC_PSR_CMDLL (0x1u << 24)
/* --------  SDMMC_HC1R (SDMMC Offset: 0x028) Host Control 1 Register */
#define SDMMC_HC1R_LEDCTRL (0x1u << 0)
#define SDMMC_HC1R_DW (0x1u << 1)
#define SDMMC_HC1R_HSEN (0x1u << 2)
#define SDMMC_HC1R_DMASEL_Pos 3
#define SDMMC_HC1R_DMASEL_Msk (0x3u << SDMMC_HC1R_DMASEL_Pos)
#define   SDMMC_HC1R_DMASEL_SDMA (0x0u << 3)
#define   SDMMC_HC1R_DMASEL_ADMA32 (0x2u << 3)
#define   SDMMC_HC1R_DMASEL_ADMA64 (0x3u << 3)
#define SDMMC_HC1R_EXTDW (0x1u << 5)
#define SDMMC_HC1R_CARDDTL (0x1u << 6)
#define SDMMC_HC1R_CARDDSSEL (0x1u << 7)
/* --------  SDMMC_PCR (SDMMC Offset: 0x029) Power Control Register */
#define SDMMC_PCR_SDBPWR (0x1u << 0)
#define SDMMC_PCR_SDBVSEL_Pos 1
#define SDMMC_PCR_SDBVSEL_Msk (0x7u << SDMMC_PCR_SDBVSEL_Pos)
#define SDMMC_PCR_SDBVSEL(value) ((SDMMC_PCR_SDBVSEL_Msk & ((value) << SDMMC_PCR_SDBVSEL_Pos)))
/* --------  SDMMC_BGCR (SDMMC Offset: 0x02A) Block Gap Control Register */
#define SDMMC_BGCR_STPBGR (0x1u << 0)
#define SDMMC_BGCR_CONTR (0x1u << 1)
#define SDMMC_BGCR_RWCTRL (0x1u << 2)
#define SDMMC_BGCR_INTBG (0x1u << 3)
/* --------  SDMMC_WCR (SDMMC Offset: 0x02B) Wakeup Control Register */
#define SDMMC_WCR_WKENCINT (0x1u << 0)
#define SDMMC_WCR_WKENCINS (0x1u << 1)
#define SDMMC_WCR_WKENCREM (0x1u << 2)
/* --------  SDMMC_CCR (SDMMC Offset: 0x02C) Clock Control Register */
#define SDMMC_CCR_INTCLKEN (0x1u << 0)
#define SDMMC_CCR_INTCLKS (0x1u << 1)
#define SDMMC_CCR_SDCLKEN (0x1u << 2)
#define SDMMC_CCR_CLKGSEL (0x1u << 5)
#define SDMMC_CCR_USDCLKFSEL_Pos 6
#define SDMMC_CCR_USDCLKFSEL_Msk (0x3u << SDMMC_CCR_USDCLKFSEL_Pos)
#define SDMMC_CCR_USDCLKFSEL(value) ((SDMMC_CCR_USDCLKFSEL_Msk & ((value) << SDMMC_CCR_USDCLKFSEL_Pos)))
#define SDMMC_CCR_SDCLKFSEL_Pos 8
#define SDMMC_CCR_SDCLKFSEL_Msk (0xFFu << SDMMC_CCR_SDCLKFSEL_Pos)
#define SDMMC_CCR_SDCLKFSEL(value) ((SDMMC_CCR_SDCLKFSEL_Msk & ((value) << SDMMC_CCR_SDCLKFSEL_Pos)))
/* --------  SDMMC_TCR (SDMMC Offset: 0x02E) Timeout Control Register */
#define SDMMC_TCR_DTCVAL_Pos 0
#define SDMMC_TCR_DTCVAL_Msk (0xFu << SDMMC_TCR_DTCVAL_Pos)
#define SDMMC_TCR_DTCVAL(value) ((SDMMC_TCR_DTCVAL_Msk & ((value) << SDMMC_TCR_DTCVAL_Pos)))
/* --------  SDMMC_SRR (SDMMC Offset: 0x02F) Software Reset Register */
#define SDMMC_SRR_SWRSTALL (0x1u << 0)
#define SDMMC_SRR_SWRSTCMD (0x1u << 1)
#define SDMMC_SRR_SWRSTDAT (0x1u << 2)
/* --------  SDMMC_NISTR (SDMMC Offset: 0x030) Normal Interrupt Status Register */
#define SDMMC_NISTR_CMDC (0x1u << 0)
#define SDMMC_NISTR_TRFC (0x1u << 1)
#define SDMMC_NISTR_BLKGE (0x1u << 2)
#define SDMMC_NISTR_DMAINT (0x1u << 3)
#define SDMMC_NISTR_BWRRDY (0x1u << 4)
#define SDMMC_NISTR_BRDRDY (0x1u << 5)
#define SDMMC_NISTR_CINS (0x1u << 6)
#define SDMMC_NISTR_CREM (0x1u << 7)
#define SDMMC_NISTR_CINT (0x1u << 8)
#define SDMMC_NISTR_INTA (0x1u << 9)
#define SDMMC_NISTR_INTB (0x1u << 10)
#define SDMMC_NISTR_INTC (0x1u << 11)
#define SDMMC_NISTR_RTEVT (0x1u << 12)
#define SDMMC_NISTR_BOOTAR (0x1u << 14)
#define SDMMC_NISTR_ERRINT (0x1u << 15)
/* --------  SDMMC_EISTR (SDMMC Offset: 0x032) Error Interrupt Status Register */
#define SDMMC_EISTR_CMDTEO (0x1u << 0)
#define SDMMC_EISTR_CMDCRC (0x1u << 1)
#define SDMMC_EISTR_CMDEND (0x1u << 2)
#define SDMMC_EISTR_CMDIDX (0x1u << 3)
#define SDMMC_EISTR_DATTEO (0x1u << 4)
#define SDMMC_EISTR_DATCRC (0x1u << 5)
#define SDMMC_EISTR_DATEND (0x1u << 6)
#define SDMMC_EISTR_CURLIM (0x1u << 7)
#define SDMMC_EISTR_ACMD   (0x1u << 8)
#define SDMMC_EISTR_ADMA   (0x1u << 9)
#define SDMMC_EISTR_TUNING (0x1u << 10)
#define SDMMC_EISTR_BOOTAE (0x1u << 12)
/* --------  SDMMC_NISTER (SDMMC Offset: 0x034) Normal Interrupt Status Enable Register */
#define SDMMC_NISTER_CMDC (0x1u << 0)
#define SDMMC_NISTER_TRFC (0x1u << 1)
#define SDMMC_NISTER_BLKGE (0x1u << 2)
#define SDMMC_NISTER_DMAINT (0x1u << 3)
#define SDMMC_NISTER_BWRRDY (0x1u << 4)
#define SDMMC_NISTER_BRDRDY (0x1u << 5)
#define SDMMC_NISTER_CINS (0x1u << 6)
#define SDMMC_NISTER_CREM (0x1u << 7)
#define SDMMC_NISTER_CINT (0x1u << 8)
#define SDMMC_NISTER_INTA (0x1u << 9)
#define SDMMC_NISTER_INTB (0x1u << 10)
#define SDMMC_NISTER_INTC (0x1u << 11)
#define SDMMC_NISTER_RTEVT (0x1u << 12)
#define SDMMC_NISTER_BOOTAR (0x1u << 14)
/* --------  SDMMC_EISTER (SDMMC Offset: 0x036) Error Interrupt Status Enable Register */
#define SDMMC_EISTER_CMDTEO (0x1u << 0)
#define SDMMC_EISTER_CMDCRC (0x1u << 1)
#define SDMMC_EISTER_CMDEND (0x1u << 2)
#define SDMMC_EISTER_CMDIDX (0x1u << 3)
#define SDMMC_EISTER_DATTEO (0x1u << 4)
#define SDMMC_EISTER_DATCRC (0x1u << 5)
#define SDMMC_EISTER_DATEND (0x1u << 6)
#define SDMMC_EISTER_CURLIM (0x1u << 7)
#define SDMMC_EISTER_ACMD (0x1u << 8)
#define SDMMC_EISTER_ADMA (0x1u << 9)
#define SDMMC_EISTER_TUNING (0x1u << 10)
#define SDMMC_EISTER_BOOTAE (0x1u << 12)
/* --------  SDMMC_NISIER (SDMMC Offset: 0x038) Normal Interrupt Signal Enable Register */
#define SDMMC_NISIER_CMDC (0x1u << 0)
#define SDMMC_NISIER_TRFC (0x1u << 1)
#define SDMMC_NISIER_BLKGE (0x1u << 2)
#define SDMMC_NISIER_DMAINT (0x1u << 3)
#define SDMMC_NISIER_BWRRDY (0x1u << 4)
#define SDMMC_NISIER_BRDRDY (0x1u << 5)
#define SDMMC_NISIER_CINS (0x1u << 6)
#define SDMMC_NISIER_CREM (0x1u << 7)
#define SDMMC_NISIER_CINT (0x1u << 8)
#define SDMMC_NISIER_INTA (0x1u << 9)
#define SDMMC_NISIER_INTB (0x1u << 10)
#define SDMMC_NISIER_INTC (0x1u << 11)
#define SDMMC_NISIER_RTEVT (0x1u << 12)
#define SDMMC_NISIER_BOOTAR (0x1u << 14)
/* --------  SDMMC_EISIER (SDMMC Offset: 0x03A) Error Interrupt Signal Enable Register */
#define SDMMC_EISIER_CMDTEO (0x1u << 0)
#define SDMMC_EISIER_CMDCRC (0x1u << 1)
#define SDMMC_EISIER_CMDEND (0x1u << 2)
#define SDMMC_EISIER_CMDIDX (0x1u << 3)
#define SDMMC_EISIER_DATTEO (0x1u << 4)
#define SDMMC_EISIER_DATCRC (0x1u << 5)
#define SDMMC_EISIER_DATEND (0x1u << 6)
#define SDMMC_EISIER_CURLIM (0x1u << 7)
#define SDMMC_EISIER_ACMD (0x1u << 8)
#define SDMMC_EISIER_ADMA (0x1u << 9)
#define SDMMC_EISIER_TUNING (0x1u << 10)
#define SDMMC_EISIER_BOOTAE (0x1u << 12)
/* --------  SDMMC_ACESR (SDMMC Offset: 0x03C) Auto CMD Error Status Register */
#define SDMMC_ACESR_ACMD12NE (0x1u << 0)
#define SDMMC_ACESR_ACMDTEO (0x1u << 1)
#define SDMMC_ACESR_ACMDCRC (0x1u << 2)
#define SDMMC_ACESR_ACMDEND (0x1u << 3)
#define SDMMC_ACESR_ACMDIDX (0x1u << 4)
#define SDMMC_ACESR_CMDNI (0x1u << 7)
/* --------  SDMMC_HC2R (SDMMC Offset: 0x03E) Host Control 2 Register */
#define SDMMC_HC2R_UHSMS_Pos 0
#define SDMMC_HC2R_UHSMS_Msk (0x7u << SDMMC_HC2R_UHSMS_Pos)
#define   SDMMC_HC2R_UHSMS_SDR12 (0x0u << 0)
#define   SDMMC_HC2R_UHSMS_SDR25 (0x1u << 0)
#define   SDMMC_HC2R_UHSMS_SDR50 (0x2u << 0)
#define   SDMMC_HC2R_UHSMS_SDR104 (0x3u << 0)
#define   SDMMC_HC2R_UHSMS_DDR50 (0x4u << 0)
#define SDMMC_HC2R_VS18EN (0x1u << 3)
#define SDMMC_HC2R_DRVSEL_Pos 4
#define SDMMC_HC2R_DRVSEL_Msk (0x3u << SDMMC_HC2R_DRVSEL_Pos)
#define   SDMMC_HC2R_DRVSEL_TYPEB (0x0u << 4)
#define   SDMMC_HC2R_DRVSEL_TYPEA (0x1u << 4)
#define   SDMMC_HC2R_DRVSEL_TYPEC (0x2u << 4)
#define   SDMMC_HC2R_DRVSEL_TYPED (0x3u << 4)
#define SDMMC_HC2R_EXTUN (0x1u << 6)
#define SDMMC_HC2R_SCLKSEL (0x1u << 7)
#define SDMMC_HC2R_ASINTEN (0x1u << 14)
#define SDMMC_HC2R_PVALEN (0x1u << 15)
/* --------  SDMMC_CA0R (SDMMC Offset: 0x040) Capabilities Register */
#define SDMMC_CA0R_TEOCLKF_Pos 0
#define SDMMC_CA0R_TEOCLKF_Msk (0x3Fu << SDMMC_CA0R_TEOCLKF_Pos)
#define SDMMC_CA0R_TEOCLKF(value) ((SDMMC_CA0R_TEOCLKF_Msk & ((value) << SDMMC_CA0R_TEOCLKF_Pos)))
#define SDMMC_CA0R_TEOCLKU (0x1u << 7)
#define SDMMC_CA0R_BASECLKF_Pos 8
#define SDMMC_CA0R_BASECLKF_Msk (0xFFu << SDMMC_CA0R_BASECLKF_Pos)
#define SDMMC_CA0R_BASECLKF(value) ((SDMMC_CA0R_BASECLKF_Msk & ((value) << SDMMC_CA0R_BASECLKF_Pos)))
#define SDMMC_CA0R_MAXBLKL_Pos 16
#define SDMMC_CA0R_MAXBLKL_Msk (0x3u << SDMMC_CA0R_MAXBLKL_Pos)
#define SDMMC_CA0R_MAXBLKL(value) ((SDMMC_CA0R_MAXBLKL_Msk & ((value) << SDMMC_CA0R_MAXBLKL_Pos)))
#define SDMMC_CA0R_ED8SUP (0x1u << 18)
#define SDMMC_CA0R_ADMA2SUP (0x1u << 19)
#define SDMMC_CA0R_HSSUP (0x1u << 21)
#define SDMMC_CA0R_SDMASUP (0x1u << 22)
#define SDMMC_CA0R_SRSUP (0x1u << 23)
#define SDMMC_CA0R_V33VSUP (0x1u << 24)
#define SDMMC_CA0R_V30VSUP (0x1u << 25)
#define SDMMC_CA0R_V18VSUP (0x1u << 26)
#define SDMMC_CA0R_SB64SUP (0x1u << 28)
#define SDMMC_CA0R_ASINTSUP (0x1u << 29)
#define SDMMC_CA0R_SLTYPE_Pos 30
#define SDMMC_CA0R_SLTYPE_Msk (0x3u << SDMMC_CA0R_SLTYPE_Pos)
#define   SDMMC_CA0R_SLTYPE_REMOVABLECARD (0x0u << 30)
#define   SDMMC_CA0R_SLTYPE_EMBEDDED (0x1u << 30)
#define   SDMMC_CA0R_SLTYPE_SHAREDBUS (0x2u << 30)
/* --------  SDMMC_CA1R (SDMMC Offset: 0x044) Capabilities Register */
#define SDMMC_CA1R_SDR50SUP (0x1u << 0)
#define SDMMC_CA1R_SDR104SUP (0x1u << 1)
#define SDMMC_CA1R_DDR50SUP (0x1u << 2)
#define SDMMC_CA1R_DRVASUP (0x1u << 4)
#define SDMMC_CA1R_DRVCSUP (0x1u << 5)
#define SDMMC_CA1R_DRVDSUP (0x1u << 6)
#define SDMMC_CA1R_TCNTRT_Pos 8
#define SDMMC_CA1R_TCNTRT_Msk (0xFu << SDMMC_CA1R_TCNTRT_Pos)
#define SDMMC_CA1R_TSDR50 (0x1u << 13)
#define SDMMC_CA1R_RTMOD_Pos 14
#define SDMMC_CA1R_RTMOD_Msk (0x3u << SDMMC_CA1R_RTMOD_Pos)
#define   SDMMC_CA1R_RTMOD_MODE1 (0x0u << 14)
#define   SDMMC_CA1R_RTMOD_MODE2 (0x1u << 14)
#define   SDMMC_CA1R_RTMOD_MODE3 (0x2u << 14)
#define SDMMC_CA1R_CLKMULT_Pos 16
#define SDMMC_CA1R_CLKMULT_Msk (0xFFu << SDMMC_CA1R_CLKMULT_Pos)
/* --------  SDMMC_MCCAR (SDMMC Offset: 0x048) Maximum Current Capabilities Register */
#define SDMMC_MCCAR_MAXCUR33V_Pos 0
#define SDMMC_MCCAR_MAXCUR33V_Msk (0xFFu << SDMMC_MCCAR_MAXCUR33V_Pos)
#define SDMMC_MCCAR_MAXCUR30V_Pos 8
#define SDMMC_MCCAR_MAXCUR30V_Msk (0xFFu << SDMMC_MCCAR_MAXCUR30V_Pos)
#define SDMMC_MCCAR_MAXCUR18V_Pos 16
#define SDMMC_MCCAR_MAXCUR18V_Msk (0xFFu << SDMMC_MCCAR_MAXCUR18V_Pos)
/* --------  SDMMC_FERACES (SDMMC Offset: 0x050) Force Event Register for Auto CMD Error Status */
#define SDMMC_FERACES_ACMD12NE (0x1u << 0)
#define SDMMC_FERACES_ACMDTEO (0x1u << 1)
#define SDMMC_FERACES_ACMDCRC (0x1u << 2)
#define SDMMC_FERACES_ACMDEND (0x1u << 3)
#define SDMMC_FERACES_ACMDIDX (0x1u << 4)
#define SDMMC_FERACES_CMDNI (0x1u << 7)
/* --------  SDMMC_FEREIS (SDMMC Offset: 0x052) Force Event Register for Error Interrupt Status */
#define SDMMC_FEREIS_CMDTEO (0x1u << 0)
#define SDMMC_FEREIS_CMDCRC (0x1u << 1)
#define SDMMC_FEREIS_CMDEND (0x1u << 2)
#define SDMMC_FEREIS_CMDIDX (0x1u << 3)
#define SDMMC_FEREIS_DATTEO (0x1u << 4)
#define SDMMC_FEREIS_DATCRC (0x1u << 5)
#define SDMMC_FEREIS_DATEND (0x1u << 6)
#define SDMMC_FEREIS_CURLIM (0x1u << 7)
#define SDMMC_FEREIS_ACMD (0x1u << 8)
#define SDMMC_FEREIS_ADMA (0x1u << 9)
/* --------  SDMMC_AESR (SDMMC Offset: 0x054) ADMA Error Status Register */
#define SDMMC_AESR_ERRST_Pos 0
#define SDMMC_AESR_ERRST_Msk (0x3u << SDMMC_AESR_ERRST_Pos)
#define   SDMMC_AESR_ERRST_STOP (0x0u << 0)
#define   SDMMC_AESR_ERRST_FDS (0x1u << 0)
#define   SDMMC_AESR_ERRST_TFR (0x3u << 0)
#define SDMMC_AESR_LMIS (0x1u << 2)
/* --------  SDMMC_ASA0R (SDMMC Offset: 0x058) ADMA System Address Register */
#define SDMMC_ASA0R_ADMASA_Pos 0
#define SDMMC_ASA0R_ADMASA_Msk (0xFFFFFFFFu << SDMMC_ASA0R_ADMASA_Pos)
#define SDMMC_ASA0R_ADMASA(value) ((SDMMC_ASA0R_ADMASA_Msk & ((value) << SDMMC_ASA0R_ADMASA_Pos)))
/* --------  SDMMC_PVR[8] (SDMMC Offset: 0x060) Preset Value Register */
#define SDMMC_PVR_SDCLKFSEL_Pos 0
#define SDMMC_PVR_SDCLKFSEL_Msk (0x3FFu << SDMMC_PVR_SDCLKFSEL_Pos)
#define SDMMC_PVR_SDCLKFSEL(value) ((SDMMC_PVR_SDCLKFSEL_Msk & ((value) << SDMMC_PVR_SDCLKFSEL_Pos)))
#define SDMMC_PVR_CLKGSEL (0x1u << 10)
#define SDMMC_PVR_DRVSEL_Pos 14
#define SDMMC_PVR_DRVSEL_Msk (0x3u << SDMMC_PVR_DRVSEL_Pos)
#define SDMMC_PVR_DRVSEL(value) ((SDMMC_PVR_DRVSEL_Msk & ((value) << SDMMC_PVR_DRVSEL_Pos)))
/* --------  SDMMC_SISR (SDMMC Offset: 0x0FC) Slot Interrupt Status Register */
#define SDMMC_SISR_INTSSL_Pos 0
#define SDMMC_SISR_INTSSL_Msk (0xFFu << SDMMC_SISR_INTSIGSLOT_Pos)
/* --------  SDMMC_HCVR (SDMMC Offset: 0x0FE) Host Controller Version Register */
#define SDMMC_HCVR_SVER_Pos 0
#define SDMMC_HCVR_SVER_Msk (0xFFu << SDMMC_HCVR_SVER_Pos)
#define SDMMC_HCVR_VVER_Pos 8
#define SDMMC_HCVR_VVER_Msk (0xFFu << SDMMC_HCVR_VVER_Pos)
/* --------  SDMMC_APSR (SDMMC Offset: 0x200) Additionnal Present State Register */
#define SDMMC_APSR_HDATLL_Pos 0
#define SDMMC_APSR_HDATLL_Msk (0xFu << SDMMC_APSR_HDATLL_Pos)
/* --------  SDMMC_MC1R (SDMMC Offset: 0x204) MMC Control 1 Register */
#define SDMMC_MC1R_CMDTYP_Pos 0
#define SDMMC_MC1R_CMDTYP_Msk (0x3u << SDMMC_MC1R_CMDTYP_Pos)
#define   SDMMC_MC1R_CMDTYP_NORMAL (0x0u << 0)
#define   SDMMC_MC1R_CMDTYP_WAITIRQ (0x1u << 0)
#define   SDMMC_MC1R_CMDTYP_STREAM (0x2u << 0)
#define   SDMMC_MC1R_CMDTYP_BOOT (0x3u << 0)
#define SDMMC_MC1R_DDR (0x1u << 3)
#define SDMMC_MC1R_OPD (0x1u << 4)
#define SDMMC_MC1R_BOOTA (0x1u << 5)
#define SDMMC_MC1R_RSTN (0x1u << 6)
#define SDMMC_MC1R_FCD (0x1u << 7)
/* --------  SDMMC_MC2R (SDMMC Offset: 0x205) MMC Control 2 Register */
#define SDMMC_MC2R_SRESP (0x1u << 0)
#define SDMMC_MC2R_ABOOT (0x1u << 1)
/* --------  SDMMC_ACR (SDMMC Offset: 0x208) AHB Control Register */
#define SDMMC_ACR_BMAX_Pos 0
#define SDMMC_ACR_BMAX_Msk (0x3u << SDMMC_ACR_BMAX_Pos)
#define   SDMMC_ACR_BMAX_INCR16 (0x0u << 0)
#define   SDMMC_ACR_BMAX_INCR8 (0x1u << 0)
#define   SDMMC_ACR_BMAX_INCR4 (0x2u << 0)
#define   SDMMC_ACR_BMAX_SINGLE (0x3u << 0)
#define SDMMC_ACR_HNBRDIS (0x1u << 4)
#define SDMMC_ACR_B1KBDIS (0x1u << 5)
/* --------  SDMMC_CC2R (SDMMC Offset: 0x20C) Clock Control 2 Register */
#define SDMMC_CC2R_FSDCLKD (0x1u << 0)
/* --------  SDMMC_RTC1R (SDMMC Offset: 0x210) Retuning Timer Control 1 Register */
#define SDMMC_RTC1R_TMREN (0x1u << 0)
/* --------  SDMMC_RTC2R (SDMMC Offset: 0x211) Retuning Timer Control 2 Register */
#define SDMMC_RTC2R_RLD (0x1u << 0)
/* --------  SDMMC_RTCVR (SDMMC Offset: 0x214) Retuning Timer Counter Value Register */
#define SDMMC_RTCVR_TCVAL_Pos 0
#define SDMMC_RTCVR_TCVAL_Msk (0xFu << SDMMC_RTCVR_TCVAL_Pos)
#define SDMMC_RTCVR_TCVAL(value) ((SDMMC_RTCVR_TCVAL_Msk & ((value) << SDMMC_RTCVR_TCVAL_Pos)))
/* --------  SDMMC_RTISTER (SDMMC Offset: 0x218) Retuning Timer Interrupt Status Enable Register */
#define SDMMC_RTISTER_TEVT (0x1u << 0)
/* --------  SDMMC_RTISIER (SDMMC Offset: 0x219) Retuning Timer Interrupt Signal Enable Register */
#define SDMMC_RTISIER_TEVT (0x1u << 0)
/* --------  SDMMC_RTISTR (SDMMC Offset: 0x21C) Retuning Timer Interrupt Status Register */
#define SDMMC_RTISTR_TEVT (0x1u << 0)
/* --------  SDMMC_RTSSR (SDMMC Offset: 0x21D) Retuning Timer Status Slots Register */
#define SDMMC_RTSSR_TEVTSLOT (0x1u << 0)
/* --------  SDMMC_TUNCR (SDMMC Offset: 0x220) Tuning Control Register */
#define SDMMC_TUNCR_SMPLPT (0x1u << 0)
/* --------  SDMMC_CACR (SDMMC Offset: 0x230) Capabilities Control Register */
#define SDMMC_CACR_CAPWREN (0x1u << 0)
#define SDMMC_CACR_KEY_Pos 8
#define SDMMC_CACR_KEY_Msk (0xFFu << SDMMC_CACR_KEY_Pos)
#define SDMMC_CACR_KEY(value) ((SDMMC_CACR_KEY_Msk & ((value) << SDMMC_CACR_KEY_Pos)))
/* --------  SDMMC_CALCR (SDMMC Offset: 0x240) Calibration Control Register */
#define SDMMC_CALCR_EN (0x1u << 0)
#define SDMMC_CALCR_ALWYSON (0x1u << 4)
#define SDMMC_CALCR_TUNDIS (0x1u << 5)
#define SDMMC_CALCR_CNTVAL_Pos 8
#define SDMMC_CALCR_CNTVAL_Msk (0xFFu << SDMMC_CALCR_CNTVAL_Pos)
#define SDMMC_CALCR_CNTVAL(value) ((SDMMC_CALCR_CNTVAL_Msk & ((value) << SDMMC_CALCR_CNTVAL_Pos)))
#define SDMMC_CALCR_CALN_Pos 16
#define SDMMC_CALCR_CALN_Msk (0xFu << SDMMC_CALCR_CALN_Pos)
#define SDMMC_CALCR_CALP_Pos 24
#define SDMMC_CALCR_CALP_Msk (0xFu << SDMMC_CALCR_CALP_Pos)
/* --------  SDMMC Descriptor Table for Advanced DMA 2 as pointed by SDMMC_ASA0R */
#define SDMMC_DMADL_SIZE (2u) /**< \brief Size of a Descriptor Line in the ADMA2 Descriptor Table, in words */
#define SDMMC_DMADL_TRAN_LEN_MIN (1u) /**< \brief Minimum data length per ADMA2 Descriptor Line, in bytes */
#define SDMMC_DMADL_TRAN_LEN_MAX (65536ul) /**< \brief Maximum data length per ADMA2 Descriptor Line, in bytes */
/* --------  SDMMC_DMADL[0] (Descriptor Line Offset: 0x0) ADMA2 Descriptor Line */
#define SDMMC_DMA0DL_ATTR_VALID (0x1u << 0)
#define SDMMC_DMA0DL_ATTR_END (0x1u << 1)
#define SDMMC_DMA0DL_ATTR_INT (0x1u << 2)
#define SDMMC_DMA0DL_ATTR_ACT_Pos 4
#define SDMMC_DMA0DL_ATTR_ACT_Msk (0x3u << SDMMC_DMA0DL_ATTR_ACT_Pos)
#define   SDMMC_DMA0DL_ATTR_ACT_NOP (0x0u << 4)
#define   SDMMC_DMA0DL_ATTR_ACT_TRAN (0x2u << 4)
#define   SDMMC_DMA0DL_ATTR_ACT_LINK (0x3u << 4)
#define SDMMC_DMA0DL_LEN_Pos 16
#define SDMMC_DMA0DL_LEN_Msk (0xFFFFu << SDMMC_DMA0DL_LEN_Pos)
#define   SDMMC_DMA0DL_LEN_MAX (0x0u << 16)
#define SDMMC_DMA0DL_LEN(value) ((SDMMC_DMA0DL_LEN_Msk & ((value) << SDMMC_DMA0DL_LEN_Pos)))
/* --------  SDMMC_DMADL[1] (Descriptor Line Offset: 0x4) ADMA2 Descriptor Line */
#define SDMMC_DMA1DL_ADDR_Pos 0
#define SDMMC_DMA1DL_ADDR_Msk (0xFFFFFFFFu << SDMMC_DMA1DL_ADDR_Pos)
#define SDMMC_DMA1DL_ADDR(value) ((SDMMC_DMA1DL_ADDR_Msk & ((value) << SDMMC_DMA1DL_ADDR_Pos)))

/*@}*/

#endif /* _SAMA5D2_SDMMC_COMPONENT_ */
