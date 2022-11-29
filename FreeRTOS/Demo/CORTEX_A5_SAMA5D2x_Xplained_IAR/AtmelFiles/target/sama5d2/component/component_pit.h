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

#ifndef _SAMA5D2_PIT_COMPONENT_
#define _SAMA5D2_PIT_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Periodic Interval Timer */
/* ============================================================================= */
/** \addtogroup SAMA5D2_PIT Periodic Interval Timer */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Pit hardware registers */
typedef struct {
  __IO uint32_t PIT_MR;   /**< \brief (Pit Offset: 0x00) Mode Register */
  __I  uint32_t PIT_SR;   /**< \brief (Pit Offset: 0x04) Status Register */
  __I  uint32_t PIT_PIVR; /**< \brief (Pit Offset: 0x08) Periodic Interval Value Register */
  __I  uint32_t PIT_PIIR; /**< \brief (Pit Offset: 0x0C) Periodic Interval Image Register */
} Pit;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- PIT_MR : (PIT Offset: 0x00) Mode Register -------- */
#define PIT_MR_PIV_Pos 0
#define PIT_MR_PIV_Msk (0xfffffu << PIT_MR_PIV_Pos) /**< \brief (PIT_MR) Periodic Interval Value */
#define PIT_MR_PIV(value) ((PIT_MR_PIV_Msk & ((value) << PIT_MR_PIV_Pos)))
#define PIT_MR_PITEN (0x1u << 24) /**< \brief (PIT_MR) Period Interval Timer Enabled */
#define PIT_MR_PITIEN (0x1u << 25) /**< \brief (PIT_MR) Periodic Interval Timer Interrupt Enable */
/* -------- PIT_SR : (PIT Offset: 0x04) Status Register -------- */
#define PIT_SR_PITS (0x1u << 0) /**< \brief (PIT_SR) Periodic Interval Timer Status */
/* -------- PIT_PIVR : (PIT Offset: 0x08) Periodic Interval Value Register -------- */
#define PIT_PIVR_CPIV_Pos 0
#define PIT_PIVR_CPIV_Msk (0xfffffu << PIT_PIVR_CPIV_Pos) /**< \brief (PIT_PIVR) Current Periodic Interval Value */
#define PIT_PIVR_PICNT_Pos 20
#define PIT_PIVR_PICNT_Msk (0xfffu << PIT_PIVR_PICNT_Pos) /**< \brief (PIT_PIVR) Periodic Interval Counter */
/* -------- PIT_PIIR : (PIT Offset: 0x0C) Periodic Interval Image Register -------- */
#define PIT_PIIR_CPIV_Pos 0
#define PIT_PIIR_CPIV_Msk (0xfffffu << PIT_PIIR_CPIV_Pos) /**< \brief (PIT_PIIR) Current Periodic Interval Value */
#define PIT_PIIR_PICNT_Pos 20
#define PIT_PIIR_PICNT_Msk (0xfffu << PIT_PIIR_PICNT_Pos) /**< \brief (PIT_PIIR) Periodic Interval Counter */

/*@}*/


#endif /* _SAMA5D2_PIT_COMPONENT_ */
