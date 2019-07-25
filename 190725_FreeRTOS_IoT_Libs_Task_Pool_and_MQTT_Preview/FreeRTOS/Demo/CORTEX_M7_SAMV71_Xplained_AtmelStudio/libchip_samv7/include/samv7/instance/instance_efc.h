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

#ifndef _SAMV71_EFC_INSTANCE_
#define _SAMV71_EFC_INSTANCE_

/* ========== Register definition for EFC peripheral ========== */
#if (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
  #define REG_EFC_FMR                      (0x400E0C00U) /**< \brief (EFC) EEFC Flash Mode Register */
  #define REG_EFC_FCR                      (0x400E0C04U) /**< \brief (EFC) EEFC Flash Command Register */
  #define REG_EFC_FSR                      (0x400E0C08U) /**< \brief (EFC) EEFC Flash Status Register */
  #define REG_EFC_FRR                      (0x400E0C0CU) /**< \brief (EFC) EEFC Flash Result Register */
  #define REG_EFC_VERSION                  (0x400E0C14U) /**< \brief (EFC) EEFC Version Register */
  #define REG_EFC_WPMR                     (0x400E0CE4U) /**< \brief (EFC) Write Protection Mode Register */
#else
  #define REG_EFC_FMR     (*(__IO uint32_t*)0x400E0C00U) /**< \brief (EFC) EEFC Flash Mode Register */
  #define REG_EFC_FCR     (*(__O  uint32_t*)0x400E0C04U) /**< \brief (EFC) EEFC Flash Command Register */
  #define REG_EFC_FSR     (*(__I  uint32_t*)0x400E0C08U) /**< \brief (EFC) EEFC Flash Status Register */
  #define REG_EFC_FRR     (*(__I  uint32_t*)0x400E0C0CU) /**< \brief (EFC) EEFC Flash Result Register */
  #define REG_EFC_VERSION (*(__I  uint32_t*)0x400E0C14U) /**< \brief (EFC) EEFC Version Register */
  #define REG_EFC_WPMR    (*(__IO uint32_t*)0x400E0CE4U) /**< \brief (EFC) Write Protection Mode Register */
#endif /* (defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */

#endif /* _SAMV71_EFC_INSTANCE_ */
