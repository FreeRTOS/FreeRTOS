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

#ifndef _SAMA5D2_SFRBU_COMPONENT_
#define _SAMA5D2_SFRBU_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Special Function Registers */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SFRBU Special Function Registers */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sfrbu hardware registers */
typedef struct {
  __IO uint32_t SFRBU_PSWBUCTRL; /**< \brief (Sfrbu Offset: 0x00) Power Switch BU Control Register */
  __IO uint32_t SFRBU_TSRANGECFG;/**< \brief (Sfrbu Offset: 0x04) TS Range Configuration Register */
  __I  uint32_t Reserved1[2];
  __IO uint32_t SFRBU_DDRBUMCR;  /**< \brief (Sfrbu Offset: 0x10) DDR BU Mode Control Register */
  __IO uint32_t SFRBU_RXLPPUCR;  /**< \brief (Sfrbu Offset: 0x14) RXLP Pull-Up Control Register */
} Sfrbu;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

/* -------- SFRBU_DDRBUMCR : (Sfrbu Offset: 0x10) DDR BU Mode Control Register -------- */
/* This bit is used to isolate the DDR Pads from the CPU domain (VCCCORE).
 * It has to be set after enabling the Self-refresh mode on the DDR memory
 * and before doing power-down on VCCCORE
 */
#define SFRBU_DDRBUMCR_BUMEN (0x1<<0) /**< \brief (SFRBU_DDRBUMCR) DDR BU Mode Enable */

/*@}*/

#endif /* _SAMA5D2_SFRBU_COMPONENT_ */
