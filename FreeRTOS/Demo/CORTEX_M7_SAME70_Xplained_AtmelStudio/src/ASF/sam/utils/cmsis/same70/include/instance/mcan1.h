/**
 * \file
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef _SAME70_MCAN1_INSTANCE_
#define _SAME70_MCAN1_INSTANCE_

/* ========== Register definition for MCAN1 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_MCAN1_CUST                    (0x40034008U) /**< \brief (MCAN1) Customer Register */
  #define REG_MCAN1_FBTP                    (0x4003400CU) /**< \brief (MCAN1) Fast Bit Timing and Prescaler Register */
  #define REG_MCAN1_TEST                    (0x40034010U) /**< \brief (MCAN1) Test Register */
  #define REG_MCAN1_RWD                     (0x40034014U) /**< \brief (MCAN1) RAM Watchdog Register */
  #define REG_MCAN1_CCCR                    (0x40034018U) /**< \brief (MCAN1) CC Control Register */
  #define REG_MCAN1_BTP                     (0x4003401CU) /**< \brief (MCAN1) Bit Timing and Prescaler Register */
  #define REG_MCAN1_TSCC                    (0x40034020U) /**< \brief (MCAN1) Timestamp Counter Configuration Register */
  #define REG_MCAN1_TSCV                    (0x40034024U) /**< \brief (MCAN1) Timestamp Counter Value Register */
  #define REG_MCAN1_TOCC                    (0x40034028U) /**< \brief (MCAN1) Timeout Counter Configuration Register */
  #define REG_MCAN1_TOCV                    (0x4003402CU) /**< \brief (MCAN1) Timeout Counter Value Register */
  #define REG_MCAN1_ECR                     (0x40034040U) /**< \brief (MCAN1) Error Counter Register */
  #define REG_MCAN1_PSR                     (0x40034044U) /**< \brief (MCAN1) Protocol Status Register */
  #define REG_MCAN1_IR                      (0x40034050U) /**< \brief (MCAN1) Interrupt Register */
  #define REG_MCAN1_IE                      (0x40034054U) /**< \brief (MCAN1) Interrupt Enable Register */
  #define REG_MCAN1_ILS                     (0x40034058U) /**< \brief (MCAN1) Interrupt Line Select Register */
  #define REG_MCAN1_ILE                     (0x4003405CU) /**< \brief (MCAN1) Interrupt Line Enable Register */
  #define REG_MCAN1_GFC                     (0x40034080U) /**< \brief (MCAN1) Global Filter Configuration Register */
  #define REG_MCAN1_SIDFC                   (0x40034084U) /**< \brief (MCAN1) Standard ID Filter Configuration Register */
  #define REG_MCAN1_XIDFC                   (0x40034088U) /**< \brief (MCAN1) Extended ID Filter Configuration Register */
  #define REG_MCAN1_XIDAM                   (0x40034090U) /**< \brief (MCAN1) Extended ID AND Mask Register */
  #define REG_MCAN1_HPMS                    (0x40034094U) /**< \brief (MCAN1) High Priority Message Status Register */
  #define REG_MCAN1_NDAT1                   (0x40034098U) /**< \brief (MCAN1) New Data 1 Register */
  #define REG_MCAN1_NDAT2                   (0x4003409CU) /**< \brief (MCAN1) New Data 2 Register */
  #define REG_MCAN1_RXF0C                   (0x400340A0U) /**< \brief (MCAN1) Receive FIFO 0 Configuration Register */
  #define REG_MCAN1_RXF0S                   (0x400340A4U) /**< \brief (MCAN1) Receive FIFO 0 Status Register */
  #define REG_MCAN1_RXF0A                   (0x400340A8U) /**< \brief (MCAN1) Receive FIFO 0 Acknowledge Register */
  #define REG_MCAN1_RXBC                    (0x400340ACU) /**< \brief (MCAN1) Receive Rx Buffer Configuration Register */
  #define REG_MCAN1_RXF1C                   (0x400340B0U) /**< \brief (MCAN1) Receive FIFO 1 Configuration Register */
  #define REG_MCAN1_RXF1S                   (0x400340B4U) /**< \brief (MCAN1) Receive FIFO 1 Status Register */
  #define REG_MCAN1_RXF1A                   (0x400340B8U) /**< \brief (MCAN1) Receive FIFO 1 Acknowledge Register */
  #define REG_MCAN1_RXESC                   (0x400340BCU) /**< \brief (MCAN1) Receive Buffer / FIFO Element Size Configuration Register */
  #define REG_MCAN1_TXBC                    (0x400340C0U) /**< \brief (MCAN1) Transmit Buffer Configuration Register */
  #define REG_MCAN1_TXFQS                   (0x400340C4U) /**< \brief (MCAN1) Transmit FIFO/Queue Status Register */
  #define REG_MCAN1_TXESC                   (0x400340C8U) /**< \brief (MCAN1) Transmit Buffer Element Size Configuration Register */
  #define REG_MCAN1_TXBRP                   (0x400340CCU) /**< \brief (MCAN1) Transmit Buffer Request Pending Register */
  #define REG_MCAN1_TXBAR                   (0x400340D0U) /**< \brief (MCAN1) Transmit Buffer Add Request Register */
  #define REG_MCAN1_TXBCR                   (0x400340D4U) /**< \brief (MCAN1) Transmit Buffer Cancellation Request Register */
  #define REG_MCAN1_TXBTO                   (0x400340D8U) /**< \brief (MCAN1) Transmit Buffer Transmission Occurred Register */
  #define REG_MCAN1_TXBCF                   (0x400340DCU) /**< \brief (MCAN1) Transmit Buffer Cancellation Finished Register */
  #define REG_MCAN1_TXBTIE                  (0x400340E0U) /**< \brief (MCAN1) Transmit Buffer Transmission Interrupt Enable Register */
  #define REG_MCAN1_TXBCIE                  (0x400340E4U) /**< \brief (MCAN1) Transmit Buffer Cancellation Finished Interrupt Enable Register */
  #define REG_MCAN1_TXEFC                   (0x400340F0U) /**< \brief (MCAN1) Transmit Event FIFO Configuration Register */
  #define REG_MCAN1_TXEFS                   (0x400340F4U) /**< \brief (MCAN1) Transmit Event FIFO Status Register */
  #define REG_MCAN1_TXEFA                   (0x400340F8U) /**< \brief (MCAN1) Transmit Event FIFO Acknowledge Register */
#else
  #define REG_MCAN1_CUST   (*(__IO uint32_t*)0x40034008U) /**< \brief (MCAN1) Customer Register */
  #define REG_MCAN1_FBTP   (*(__IO uint32_t*)0x4003400CU) /**< \brief (MCAN1) Fast Bit Timing and Prescaler Register */
  #define REG_MCAN1_TEST   (*(__IO uint32_t*)0x40034010U) /**< \brief (MCAN1) Test Register */
  #define REG_MCAN1_RWD    (*(__IO uint32_t*)0x40034014U) /**< \brief (MCAN1) RAM Watchdog Register */
  #define REG_MCAN1_CCCR   (*(__IO uint32_t*)0x40034018U) /**< \brief (MCAN1) CC Control Register */
  #define REG_MCAN1_BTP    (*(__IO uint32_t*)0x4003401CU) /**< \brief (MCAN1) Bit Timing and Prescaler Register */
  #define REG_MCAN1_TSCC   (*(__IO uint32_t*)0x40034020U) /**< \brief (MCAN1) Timestamp Counter Configuration Register */
  #define REG_MCAN1_TSCV   (*(__IO uint32_t*)0x40034024U) /**< \brief (MCAN1) Timestamp Counter Value Register */
  #define REG_MCAN1_TOCC   (*(__IO uint32_t*)0x40034028U) /**< \brief (MCAN1) Timeout Counter Configuration Register */
  #define REG_MCAN1_TOCV   (*(__IO uint32_t*)0x4003402CU) /**< \brief (MCAN1) Timeout Counter Value Register */
  #define REG_MCAN1_ECR    (*(__I  uint32_t*)0x40034040U) /**< \brief (MCAN1) Error Counter Register */
  #define REG_MCAN1_PSR    (*(__I  uint32_t*)0x40034044U) /**< \brief (MCAN1) Protocol Status Register */
  #define REG_MCAN1_IR     (*(__IO uint32_t*)0x40034050U) /**< \brief (MCAN1) Interrupt Register */
  #define REG_MCAN1_IE     (*(__IO uint32_t*)0x40034054U) /**< \brief (MCAN1) Interrupt Enable Register */
  #define REG_MCAN1_ILS    (*(__IO uint32_t*)0x40034058U) /**< \brief (MCAN1) Interrupt Line Select Register */
  #define REG_MCAN1_ILE    (*(__IO uint32_t*)0x4003405CU) /**< \brief (MCAN1) Interrupt Line Enable Register */
  #define REG_MCAN1_GFC    (*(__IO uint32_t*)0x40034080U) /**< \brief (MCAN1) Global Filter Configuration Register */
  #define REG_MCAN1_SIDFC  (*(__IO uint32_t*)0x40034084U) /**< \brief (MCAN1) Standard ID Filter Configuration Register */
  #define REG_MCAN1_XIDFC  (*(__IO uint32_t*)0x40034088U) /**< \brief (MCAN1) Extended ID Filter Configuration Register */
  #define REG_MCAN1_XIDAM  (*(__IO uint32_t*)0x40034090U) /**< \brief (MCAN1) Extended ID AND Mask Register */
  #define REG_MCAN1_HPMS   (*(__I  uint32_t*)0x40034094U) /**< \brief (MCAN1) High Priority Message Status Register */
  #define REG_MCAN1_NDAT1  (*(__IO uint32_t*)0x40034098U) /**< \brief (MCAN1) New Data 1 Register */
  #define REG_MCAN1_NDAT2  (*(__IO uint32_t*)0x4003409CU) /**< \brief (MCAN1) New Data 2 Register */
  #define REG_MCAN1_RXF0C  (*(__IO uint32_t*)0x400340A0U) /**< \brief (MCAN1) Receive FIFO 0 Configuration Register */
  #define REG_MCAN1_RXF0S  (*(__I  uint32_t*)0x400340A4U) /**< \brief (MCAN1) Receive FIFO 0 Status Register */
  #define REG_MCAN1_RXF0A  (*(__IO uint32_t*)0x400340A8U) /**< \brief (MCAN1) Receive FIFO 0 Acknowledge Register */
  #define REG_MCAN1_RXBC   (*(__IO uint32_t*)0x400340ACU) /**< \brief (MCAN1) Receive Rx Buffer Configuration Register */
  #define REG_MCAN1_RXF1C  (*(__IO uint32_t*)0x400340B0U) /**< \brief (MCAN1) Receive FIFO 1 Configuration Register */
  #define REG_MCAN1_RXF1S  (*(__I  uint32_t*)0x400340B4U) /**< \brief (MCAN1) Receive FIFO 1 Status Register */
  #define REG_MCAN1_RXF1A  (*(__IO uint32_t*)0x400340B8U) /**< \brief (MCAN1) Receive FIFO 1 Acknowledge Register */
  #define REG_MCAN1_RXESC  (*(__IO uint32_t*)0x400340BCU) /**< \brief (MCAN1) Receive Buffer / FIFO Element Size Configuration Register */
  #define REG_MCAN1_TXBC   (*(__IO uint32_t*)0x400340C0U) /**< \brief (MCAN1) Transmit Buffer Configuration Register */
  #define REG_MCAN1_TXFQS  (*(__I  uint32_t*)0x400340C4U) /**< \brief (MCAN1) Transmit FIFO/Queue Status Register */
  #define REG_MCAN1_TXESC  (*(__IO uint32_t*)0x400340C8U) /**< \brief (MCAN1) Transmit Buffer Element Size Configuration Register */
  #define REG_MCAN1_TXBRP  (*(__I  uint32_t*)0x400340CCU) /**< \brief (MCAN1) Transmit Buffer Request Pending Register */
  #define REG_MCAN1_TXBAR  (*(__IO uint32_t*)0x400340D0U) /**< \brief (MCAN1) Transmit Buffer Add Request Register */
  #define REG_MCAN1_TXBCR  (*(__IO uint32_t*)0x400340D4U) /**< \brief (MCAN1) Transmit Buffer Cancellation Request Register */
  #define REG_MCAN1_TXBTO  (*(__I  uint32_t*)0x400340D8U) /**< \brief (MCAN1) Transmit Buffer Transmission Occurred Register */
  #define REG_MCAN1_TXBCF  (*(__I  uint32_t*)0x400340DCU) /**< \brief (MCAN1) Transmit Buffer Cancellation Finished Register */
  #define REG_MCAN1_TXBTIE (*(__IO uint32_t*)0x400340E0U) /**< \brief (MCAN1) Transmit Buffer Transmission Interrupt Enable Register */
  #define REG_MCAN1_TXBCIE (*(__IO uint32_t*)0x400340E4U) /**< \brief (MCAN1) Transmit Buffer Cancellation Finished Interrupt Enable Register */
  #define REG_MCAN1_TXEFC  (*(__IO uint32_t*)0x400340F0U) /**< \brief (MCAN1) Transmit Event FIFO Configuration Register */
  #define REG_MCAN1_TXEFS  (*(__I  uint32_t*)0x400340F4U) /**< \brief (MCAN1) Transmit Event FIFO Status Register */
  #define REG_MCAN1_TXEFA  (*(__IO uint32_t*)0x400340F8U) /**< \brief (MCAN1) Transmit Event FIFO Acknowledge Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_MCAN1_INSTANCE_ */
