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

#ifndef _SAME70_MCAN0_INSTANCE_
#define _SAME70_MCAN0_INSTANCE_

/* ========== Register definition for MCAN0 peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_MCAN0_CUST                    (0x40030008U) /**< \brief (MCAN0) Customer Register */
  #define REG_MCAN0_FBTP                    (0x4003000CU) /**< \brief (MCAN0) Fast Bit Timing and Prescaler Register */
  #define REG_MCAN0_TEST                    (0x40030010U) /**< \brief (MCAN0) Test Register */
  #define REG_MCAN0_RWD                     (0x40030014U) /**< \brief (MCAN0) RAM Watchdog Register */
  #define REG_MCAN0_CCCR                    (0x40030018U) /**< \brief (MCAN0) CC Control Register */
  #define REG_MCAN0_BTP                     (0x4003001CU) /**< \brief (MCAN0) Bit Timing and Prescaler Register */
  #define REG_MCAN0_TSCC                    (0x40030020U) /**< \brief (MCAN0) Timestamp Counter Configuration Register */
  #define REG_MCAN0_TSCV                    (0x40030024U) /**< \brief (MCAN0) Timestamp Counter Value Register */
  #define REG_MCAN0_TOCC                    (0x40030028U) /**< \brief (MCAN0) Timeout Counter Configuration Register */
  #define REG_MCAN0_TOCV                    (0x4003002CU) /**< \brief (MCAN0) Timeout Counter Value Register */
  #define REG_MCAN0_ECR                     (0x40030040U) /**< \brief (MCAN0) Error Counter Register */
  #define REG_MCAN0_PSR                     (0x40030044U) /**< \brief (MCAN0) Protocol Status Register */
  #define REG_MCAN0_IR                      (0x40030050U) /**< \brief (MCAN0) Interrupt Register */
  #define REG_MCAN0_IE                      (0x40030054U) /**< \brief (MCAN0) Interrupt Enable Register */
  #define REG_MCAN0_ILS                     (0x40030058U) /**< \brief (MCAN0) Interrupt Line Select Register */
  #define REG_MCAN0_ILE                     (0x4003005CU) /**< \brief (MCAN0) Interrupt Line Enable Register */
  #define REG_MCAN0_GFC                     (0x40030080U) /**< \brief (MCAN0) Global Filter Configuration Register */
  #define REG_MCAN0_SIDFC                   (0x40030084U) /**< \brief (MCAN0) Standard ID Filter Configuration Register */
  #define REG_MCAN0_XIDFC                   (0x40030088U) /**< \brief (MCAN0) Extended ID Filter Configuration Register */
  #define REG_MCAN0_XIDAM                   (0x40030090U) /**< \brief (MCAN0) Extended ID AND Mask Register */
  #define REG_MCAN0_HPMS                    (0x40030094U) /**< \brief (MCAN0) High Priority Message Status Register */
  #define REG_MCAN0_NDAT1                   (0x40030098U) /**< \brief (MCAN0) New Data 1 Register */
  #define REG_MCAN0_NDAT2                   (0x4003009CU) /**< \brief (MCAN0) New Data 2 Register */
  #define REG_MCAN0_RXF0C                   (0x400300A0U) /**< \brief (MCAN0) Receive FIFO 0 Configuration Register */
  #define REG_MCAN0_RXF0S                   (0x400300A4U) /**< \brief (MCAN0) Receive FIFO 0 Status Register */
  #define REG_MCAN0_RXF0A                   (0x400300A8U) /**< \brief (MCAN0) Receive FIFO 0 Acknowledge Register */
  #define REG_MCAN0_RXBC                    (0x400300ACU) /**< \brief (MCAN0) Receive Rx Buffer Configuration Register */
  #define REG_MCAN0_RXF1C                   (0x400300B0U) /**< \brief (MCAN0) Receive FIFO 1 Configuration Register */
  #define REG_MCAN0_RXF1S                   (0x400300B4U) /**< \brief (MCAN0) Receive FIFO 1 Status Register */
  #define REG_MCAN0_RXF1A                   (0x400300B8U) /**< \brief (MCAN0) Receive FIFO 1 Acknowledge Register */
  #define REG_MCAN0_RXESC                   (0x400300BCU) /**< \brief (MCAN0) Receive Buffer / FIFO Element Size Configuration Register */
  #define REG_MCAN0_TXBC                    (0x400300C0U) /**< \brief (MCAN0) Transmit Buffer Configuration Register */
  #define REG_MCAN0_TXFQS                   (0x400300C4U) /**< \brief (MCAN0) Transmit FIFO/Queue Status Register */
  #define REG_MCAN0_TXESC                   (0x400300C8U) /**< \brief (MCAN0) Transmit Buffer Element Size Configuration Register */
  #define REG_MCAN0_TXBRP                   (0x400300CCU) /**< \brief (MCAN0) Transmit Buffer Request Pending Register */
  #define REG_MCAN0_TXBAR                   (0x400300D0U) /**< \brief (MCAN0) Transmit Buffer Add Request Register */
  #define REG_MCAN0_TXBCR                   (0x400300D4U) /**< \brief (MCAN0) Transmit Buffer Cancellation Request Register */
  #define REG_MCAN0_TXBTO                   (0x400300D8U) /**< \brief (MCAN0) Transmit Buffer Transmission Occurred Register */
  #define REG_MCAN0_TXBCF                   (0x400300DCU) /**< \brief (MCAN0) Transmit Buffer Cancellation Finished Register */
  #define REG_MCAN0_TXBTIE                  (0x400300E0U) /**< \brief (MCAN0) Transmit Buffer Transmission Interrupt Enable Register */
  #define REG_MCAN0_TXBCIE                  (0x400300E4U) /**< \brief (MCAN0) Transmit Buffer Cancellation Finished Interrupt Enable Register */
  #define REG_MCAN0_TXEFC                   (0x400300F0U) /**< \brief (MCAN0) Transmit Event FIFO Configuration Register */
  #define REG_MCAN0_TXEFS                   (0x400300F4U) /**< \brief (MCAN0) Transmit Event FIFO Status Register */
  #define REG_MCAN0_TXEFA                   (0x400300F8U) /**< \brief (MCAN0) Transmit Event FIFO Acknowledge Register */
#else
  #define REG_MCAN0_CUST   (*(__IO uint32_t*)0x40030008U) /**< \brief (MCAN0) Customer Register */
  #define REG_MCAN0_FBTP   (*(__IO uint32_t*)0x4003000CU) /**< \brief (MCAN0) Fast Bit Timing and Prescaler Register */
  #define REG_MCAN0_TEST   (*(__IO uint32_t*)0x40030010U) /**< \brief (MCAN0) Test Register */
  #define REG_MCAN0_RWD    (*(__IO uint32_t*)0x40030014U) /**< \brief (MCAN0) RAM Watchdog Register */
  #define REG_MCAN0_CCCR   (*(__IO uint32_t*)0x40030018U) /**< \brief (MCAN0) CC Control Register */
  #define REG_MCAN0_BTP    (*(__IO uint32_t*)0x4003001CU) /**< \brief (MCAN0) Bit Timing and Prescaler Register */
  #define REG_MCAN0_TSCC   (*(__IO uint32_t*)0x40030020U) /**< \brief (MCAN0) Timestamp Counter Configuration Register */
  #define REG_MCAN0_TSCV   (*(__IO uint32_t*)0x40030024U) /**< \brief (MCAN0) Timestamp Counter Value Register */
  #define REG_MCAN0_TOCC   (*(__IO uint32_t*)0x40030028U) /**< \brief (MCAN0) Timeout Counter Configuration Register */
  #define REG_MCAN0_TOCV   (*(__IO uint32_t*)0x4003002CU) /**< \brief (MCAN0) Timeout Counter Value Register */
  #define REG_MCAN0_ECR    (*(__I  uint32_t*)0x40030040U) /**< \brief (MCAN0) Error Counter Register */
  #define REG_MCAN0_PSR    (*(__I  uint32_t*)0x40030044U) /**< \brief (MCAN0) Protocol Status Register */
  #define REG_MCAN0_IR     (*(__IO uint32_t*)0x40030050U) /**< \brief (MCAN0) Interrupt Register */
  #define REG_MCAN0_IE     (*(__IO uint32_t*)0x40030054U) /**< \brief (MCAN0) Interrupt Enable Register */
  #define REG_MCAN0_ILS    (*(__IO uint32_t*)0x40030058U) /**< \brief (MCAN0) Interrupt Line Select Register */
  #define REG_MCAN0_ILE    (*(__IO uint32_t*)0x4003005CU) /**< \brief (MCAN0) Interrupt Line Enable Register */
  #define REG_MCAN0_GFC    (*(__IO uint32_t*)0x40030080U) /**< \brief (MCAN0) Global Filter Configuration Register */
  #define REG_MCAN0_SIDFC  (*(__IO uint32_t*)0x40030084U) /**< \brief (MCAN0) Standard ID Filter Configuration Register */
  #define REG_MCAN0_XIDFC  (*(__IO uint32_t*)0x40030088U) /**< \brief (MCAN0) Extended ID Filter Configuration Register */
  #define REG_MCAN0_XIDAM  (*(__IO uint32_t*)0x40030090U) /**< \brief (MCAN0) Extended ID AND Mask Register */
  #define REG_MCAN0_HPMS   (*(__I  uint32_t*)0x40030094U) /**< \brief (MCAN0) High Priority Message Status Register */
  #define REG_MCAN0_NDAT1  (*(__IO uint32_t*)0x40030098U) /**< \brief (MCAN0) New Data 1 Register */
  #define REG_MCAN0_NDAT2  (*(__IO uint32_t*)0x4003009CU) /**< \brief (MCAN0) New Data 2 Register */
  #define REG_MCAN0_RXF0C  (*(__IO uint32_t*)0x400300A0U) /**< \brief (MCAN0) Receive FIFO 0 Configuration Register */
  #define REG_MCAN0_RXF0S  (*(__I  uint32_t*)0x400300A4U) /**< \brief (MCAN0) Receive FIFO 0 Status Register */
  #define REG_MCAN0_RXF0A  (*(__IO uint32_t*)0x400300A8U) /**< \brief (MCAN0) Receive FIFO 0 Acknowledge Register */
  #define REG_MCAN0_RXBC   (*(__IO uint32_t*)0x400300ACU) /**< \brief (MCAN0) Receive Rx Buffer Configuration Register */
  #define REG_MCAN0_RXF1C  (*(__IO uint32_t*)0x400300B0U) /**< \brief (MCAN0) Receive FIFO 1 Configuration Register */
  #define REG_MCAN0_RXF1S  (*(__I  uint32_t*)0x400300B4U) /**< \brief (MCAN0) Receive FIFO 1 Status Register */
  #define REG_MCAN0_RXF1A  (*(__IO uint32_t*)0x400300B8U) /**< \brief (MCAN0) Receive FIFO 1 Acknowledge Register */
  #define REG_MCAN0_RXESC  (*(__IO uint32_t*)0x400300BCU) /**< \brief (MCAN0) Receive Buffer / FIFO Element Size Configuration Register */
  #define REG_MCAN0_TXBC   (*(__IO uint32_t*)0x400300C0U) /**< \brief (MCAN0) Transmit Buffer Configuration Register */
  #define REG_MCAN0_TXFQS  (*(__I  uint32_t*)0x400300C4U) /**< \brief (MCAN0) Transmit FIFO/Queue Status Register */
  #define REG_MCAN0_TXESC  (*(__IO uint32_t*)0x400300C8U) /**< \brief (MCAN0) Transmit Buffer Element Size Configuration Register */
  #define REG_MCAN0_TXBRP  (*(__I  uint32_t*)0x400300CCU) /**< \brief (MCAN0) Transmit Buffer Request Pending Register */
  #define REG_MCAN0_TXBAR  (*(__IO uint32_t*)0x400300D0U) /**< \brief (MCAN0) Transmit Buffer Add Request Register */
  #define REG_MCAN0_TXBCR  (*(__IO uint32_t*)0x400300D4U) /**< \brief (MCAN0) Transmit Buffer Cancellation Request Register */
  #define REG_MCAN0_TXBTO  (*(__I  uint32_t*)0x400300D8U) /**< \brief (MCAN0) Transmit Buffer Transmission Occurred Register */
  #define REG_MCAN0_TXBCF  (*(__I  uint32_t*)0x400300DCU) /**< \brief (MCAN0) Transmit Buffer Cancellation Finished Register */
  #define REG_MCAN0_TXBTIE (*(__IO uint32_t*)0x400300E0U) /**< \brief (MCAN0) Transmit Buffer Transmission Interrupt Enable Register */
  #define REG_MCAN0_TXBCIE (*(__IO uint32_t*)0x400300E4U) /**< \brief (MCAN0) Transmit Buffer Cancellation Finished Interrupt Enable Register */
  #define REG_MCAN0_TXEFC  (*(__IO uint32_t*)0x400300F0U) /**< \brief (MCAN0) Transmit Event FIFO Configuration Register */
  #define REG_MCAN0_TXEFS  (*(__I  uint32_t*)0x400300F4U) /**< \brief (MCAN0) Transmit Event FIFO Status Register */
  #define REG_MCAN0_TXEFA  (*(__IO uint32_t*)0x400300F8U) /**< \brief (MCAN0) Transmit Event FIFO Acknowledge Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAME70_MCAN0_INSTANCE_ */
