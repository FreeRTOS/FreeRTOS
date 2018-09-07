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

#ifndef _SAMA5D2_SCKC_COMPONENT_
#define _SAMA5D2_SCKC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Slow Clock Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SCKC Slow Clock Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sckc hardware registers */
typedef struct {
  __IO uint32_t SCKC_CR; /**< \brief (Sckc Offset: 0x0) Slow Clock Controller Configuration Register */
} Sckc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SCKC_CR : (SCKC Offset: 0x0) Slow Clock Controller Configuration Register -------- */
#define SCKC_CR_OSCSEL (0x1u << 3) /**< \brief (SCKC_CR) Slow Clock Selector */
#define   SCKC_CR_OSCSEL_RC (0x0u << 3) /**< \brief (SCKC_CR) Slow clock is the embedded 64 kHz (typical) RC oscillator. */
#define   SCKC_CR_OSCSEL_XTAL (0x1u << 3) /**< \brief (SCKC_CR) Slow clock is the 32.768 kHz crystal oscillator. */

/*@}*/


#endif /* _SAMA5D2_SCKC_COMPONENT_ */
