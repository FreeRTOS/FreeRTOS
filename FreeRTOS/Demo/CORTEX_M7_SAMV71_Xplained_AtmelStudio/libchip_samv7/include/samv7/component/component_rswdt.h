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

#ifndef _SAMV71_RSWDT_COMPONENT_
#define _SAMV71_RSWDT_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Reinforced Safety Watchdog Timer */
/* ============================================================================= */
/** \addtogroup SAMV71_RSWDT Reinforced Safety Watchdog Timer */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Rswdt hardware registers */
typedef struct {
  __O  uint32_t RSWDT_CR; /**< \brief (Rswdt Offset: 0x00) Control Register */
  __IO uint32_t RSWDT_MR; /**< \brief (Rswdt Offset: 0x04) Mode Register */
  __I  uint32_t RSWDT_SR; /**< \brief (Rswdt Offset: 0x08) Status Register */
} Rswdt;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- RSWDT_CR : (RSWDT Offset: 0x00) Control Register -------- */
#define RSWDT_CR_WDRSTT (0x1u << 0) /**< \brief (RSWDT_CR) Watchdog Restart */
#define RSWDT_CR_KEY_Pos 24
#define RSWDT_CR_KEY_Msk (0xffu << RSWDT_CR_KEY_Pos) /**< \brief (RSWDT_CR) Password */
#define RSWDT_CR_KEY(value) ((RSWDT_CR_KEY_Msk & ((value) << RSWDT_CR_KEY_Pos)))
#define   RSWDT_CR_KEY_PASSWD (0xC4u << 24) /**< \brief (RSWDT_CR) Writing any other value in this field aborts the write operation. */
/* -------- RSWDT_MR : (RSWDT Offset: 0x04) Mode Register -------- */
#define RSWDT_MR_WDV_Pos 0
#define RSWDT_MR_WDV_Msk (0xfffu << RSWDT_MR_WDV_Pos) /**< \brief (RSWDT_MR) Watchdog Counter Value */
#define RSWDT_MR_WDV(value) ((RSWDT_MR_WDV_Msk & ((value) << RSWDT_MR_WDV_Pos)))
#define RSWDT_MR_WDFIEN (0x1u << 12) /**< \brief (RSWDT_MR) Watchdog Fault Interrupt Enable */
#define RSWDT_MR_WDRSTEN (0x1u << 13) /**< \brief (RSWDT_MR) Watchdog Reset Enable */
#define RSWDT_MR_WDRPROC (0x1u << 14) /**< \brief (RSWDT_MR) Watchdog Reset Processor */
#define RSWDT_MR_WDDIS (0x1u << 15) /**< \brief (RSWDT_MR) Watchdog Disable */
#define RSWDT_MR_ALLONES_Pos 16
#define RSWDT_MR_ALLONES_Msk (0xfffu << RSWDT_MR_ALLONES_Pos) /**< \brief (RSWDT_MR) Must Always Be Written with 0xFFF */
#define RSWDT_MR_ALLONES(value) ((RSWDT_MR_ALLONES_Msk & ((value) << RSWDT_MR_ALLONES_Pos)))
#define RSWDT_MR_WDDBGHLT (0x1u << 28) /**< \brief (RSWDT_MR) Watchdog Debug Halt */
#define RSWDT_MR_WDIDLEHLT (0x1u << 29) /**< \brief (RSWDT_MR) Watchdog Idle Halt */
/* -------- RSWDT_SR : (RSWDT Offset: 0x08) Status Register -------- */
#define RSWDT_SR_WDUNF (0x1u << 0) /**< \brief (RSWDT_SR) Watchdog Underflow */

/*@}*/


#endif /* _SAMV71_RSWDT_COMPONENT_ */
