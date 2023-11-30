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

#ifndef _SAMA5D2_MATRIX_COMPONENT_
#define _SAMA5D2_MATRIX_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR AHB Bus Matrix */
/* ============================================================================= */
/** \addtogroup SAMA5D2_MATRIX AHB Bus Matrix */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief MatrixPr hardware registers */
typedef struct {
  __IO uint32_t MATRIX_PRAS; /**< \brief (MatrixPr Offset: 0x0) Priority Register A for Slave 0 */
  __IO uint32_t MATRIX_PRBS; /**< \brief (MatrixPr Offset: 0x4) Priority Register B for Slave 0 */
} MatrixPr;
/** \brief Matrix hardware registers */
#define MATRIXPR_NUMBER 15
typedef struct {
  __IO uint32_t MATRIX_MCFG0;               /**< \brief (Matrix Offset: 0x0000) Master Configuration Register 0 */
  __IO uint32_t MATRIX_MCFG1;               /**< \brief (Matrix Offset: 0x0004) Master Configuration Register 1 */
  __IO uint32_t MATRIX_MCFG2;               /**< \brief (Matrix Offset: 0x0008) Master Configuration Register 2 */
  __IO uint32_t MATRIX_MCFG3;               /**< \brief (Matrix Offset: 0x000C) Master Configuration Register 3 */
  __IO uint32_t MATRIX_MCFG4;               /**< \brief (Matrix Offset: 0x0010) Master Configuration Register 4 */
  __IO uint32_t MATRIX_MCFG5;               /**< \brief (Matrix Offset: 0x0014) Master Configuration Register 5 */
  __IO uint32_t MATRIX_MCFG6;               /**< \brief (Matrix Offset: 0x0018) Master Configuration Register 6 */
  __IO uint32_t MATRIX_MCFG7;               /**< \brief (Matrix Offset: 0x001C) Master Configuration Register 7 */
  __IO uint32_t MATRIX_MCFG8;               /**< \brief (Matrix Offset: 0x0020) Master Configuration Register 8 */
  __IO uint32_t MATRIX_MCFG9;               /**< \brief (Matrix Offset: 0x0024) Master Configuration Register 9 */
  __IO uint32_t MATRIX_MCFG10;              /**< \brief (Matrix Offset: 0x0028) Master Configuration Register 10 */
  __IO uint32_t MATRIX_MCFG11;              /**< \brief (Matrix Offset: 0x002C) Master Configuration Register 11 */
  __I  uint32_t Reserved1[4];
  __IO uint32_t MATRIX_SCFG0;               /**< \brief (Matrix Offset: 0x0040) Slave Configuration Register 0 */
  __IO uint32_t MATRIX_SCFG1;               /**< \brief (Matrix Offset: 0x0044) Slave Configuration Register 1 */
  __IO uint32_t MATRIX_SCFG2;               /**< \brief (Matrix Offset: 0x0048) Slave Configuration Register 2 */
  __IO uint32_t MATRIX_SCFG3;               /**< \brief (Matrix Offset: 0x004C) Slave Configuration Register 3 */
  __IO uint32_t MATRIX_SCFG4;               /**< \brief (Matrix Offset: 0x0050) Slave Configuration Register 4 */
  __IO uint32_t MATRIX_SCFG5;               /**< \brief (Matrix Offset: 0x0054) Slave Configuration Register 5 */
  __IO uint32_t MATRIX_SCFG6;               /**< \brief (Matrix Offset: 0x0058) Slave Configuration Register 6 */
  __IO uint32_t MATRIX_SCFG7;               /**< \brief (Matrix Offset: 0x005C) Slave Configuration Register 7 */
  __IO uint32_t MATRIX_SCFG8;               /**< \brief (Matrix Offset: 0x0060) Slave Configuration Register 8 */
  __IO uint32_t MATRIX_SCFG9;               /**< \brief (Matrix Offset: 0x0064) Slave Configuration Register 9 */
  __IO uint32_t MATRIX_SCFG10;              /**< \brief (Matrix Offset: 0x0068) Slave Configuration Register 10 */
  __IO uint32_t MATRIX_SCFG11;              /**< \brief (Matrix Offset: 0x006C) Slave Configuration Register 11 */
  __IO uint32_t MATRIX_SCFG12;              /**< \brief (Matrix Offset: 0x0070) Slave Configuration Register 12 */
  __IO uint32_t MATRIX_SCFG13;              /**< \brief (Matrix Offset: 0x0074) Slave Configuration Register 13 */
  __IO uint32_t MATRIX_SCFG14;              /**< \brief (Matrix Offset: 0x0078) Slave Configuration Register 14 */
  __I  uint32_t Reserved2[1];
       MatrixPr MATRIX_PR[MATRIXPR_NUMBER]; /**< \brief (Matrix Offset: 0x0080) 0 .. 14 */
  __I  uint32_t Reserved3[22];
  __O  uint32_t MATRIX_MEIER;               /**< \brief (Matrix Offset: 0x0150) Master Error Interrupt Enable Register */
  __O  uint32_t MATRIX_MEIDR;               /**< \brief (Matrix Offset: 0x0154) Master Error Interrupt Disable Register */
  __I  uint32_t MATRIX_MEIMR;               /**< \brief (Matrix Offset: 0x0158) Master Error Interrupt Mask Register */
  __I  uint32_t MATRIX_MESR;                /**< \brief (Matrix Offset: 0x015C) Master Error Status Register */
  __I  uint32_t MATRIX_MEAR0;               /**< \brief (Matrix Offset: 0x0160) Master 0 Error Address Register */
  __I  uint32_t MATRIX_MEAR1;               /**< \brief (Matrix Offset: 0x0164) Master 1 Error Address Register */
  __I  uint32_t MATRIX_MEAR2;               /**< \brief (Matrix Offset: 0x0168) Master 2 Error Address Register */
  __I  uint32_t MATRIX_MEAR3;               /**< \brief (Matrix Offset: 0x016C) Master 3 Error Address Register */
  __I  uint32_t MATRIX_MEAR4;               /**< \brief (Matrix Offset: 0x0170) Master 4 Error Address Register */
  __I  uint32_t MATRIX_MEAR5;               /**< \brief (Matrix Offset: 0x0174) Master 5 Error Address Register */
  __I  uint32_t MATRIX_MEAR6;               /**< \brief (Matrix Offset: 0x0178) Master 6 Error Address Register */
  __I  uint32_t MATRIX_MEAR7;               /**< \brief (Matrix Offset: 0x017C) Master 7 Error Address Register */
  __I  uint32_t MATRIX_MEAR8;               /**< \brief (Matrix Offset: 0x0180) Master 8 Error Address Register */
  __I  uint32_t MATRIX_MEAR9;               /**< \brief (Matrix Offset: 0x0184) Master 9 Error Address Register */
  __I  uint32_t MATRIX_MEAR10;              /**< \brief (Matrix Offset: 0x0188) Master 10 Error Address Register */
  __I  uint32_t MATRIX_MEAR11;              /**< \brief (Matrix Offset: 0x018C) Master 11 Error Address Register */
  __I  uint32_t Reserved4[21];
  __IO uint32_t MATRIX_WPMR;                /**< \brief (Matrix Offset: 0x01E4) Write Protection Mode Register */
  __I  uint32_t MATRIX_WPSR;                /**< \brief (Matrix Offset: 0x01E8) Write Protection Status Register */
  __I  uint32_t Reserved5[4];
  __I  uint32_t MATRIX_VERSION;             /**< \brief (Matrix Offset: 0x01FC) Version Register */
  __IO uint32_t MATRIX_SSR[15];                /**< \brief (Matrix Offset: 0x0200) Security Slave x Register */
  __I  uint32_t Reserved6[1];
  __IO uint32_t MATRIX_SASSR[15];              /**< \brief (Matrix Offset: 0x0240) Security Areas Split Slave x Register */
  __I  uint32_t Reserved7[1];
  __IO uint32_t MATRIX_SRTSR[15];              /**< \brief (Matrix Offset: 0x0284) Security Region Top Slave x Register */
  __I  uint32_t Reserved8[1];
  __IO uint32_t MATRIX_SPSELR[3];           /**< \brief (Matrix Offset: 0x02C0) Security Peripheral Select x Register */
} Matrix;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- MATRIX_MCFG0 : (MATRIX Offset: 0x0000) Master Configuration Register 0 -------- */
#define MATRIX_MCFG0_ULBT_Pos 0
#define MATRIX_MCFG0_ULBT_Msk (0x7u << MATRIX_MCFG0_ULBT_Pos) /**< \brief (MATRIX_MCFG0) Undefined Length Burst Type */
#define MATRIX_MCFG0_ULBT(value) ((MATRIX_MCFG0_ULBT_Msk & ((value) << MATRIX_MCFG0_ULBT_Pos)))
#define   MATRIX_MCFG0_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG0) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG0_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG0) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG0_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG0) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG0_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG0) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG0_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG0) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG0_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG0) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG0_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG0) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG0_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG0) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG1 : (MATRIX Offset: 0x0004) Master Configuration Register 1 -------- */
#define MATRIX_MCFG1_ULBT_Pos 0
#define MATRIX_MCFG1_ULBT_Msk (0x7u << MATRIX_MCFG1_ULBT_Pos) /**< \brief (MATRIX_MCFG1) Undefined Length Burst Type */
#define MATRIX_MCFG1_ULBT(value) ((MATRIX_MCFG1_ULBT_Msk & ((value) << MATRIX_MCFG1_ULBT_Pos)))
#define   MATRIX_MCFG1_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG1) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG1_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG1) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG1_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG1) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG1_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG1) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG1_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG1) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG1_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG1) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG1_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG1) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG1_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG1) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG2 : (MATRIX Offset: 0x0008) Master Configuration Register 2 -------- */
#define MATRIX_MCFG2_ULBT_Pos 0
#define MATRIX_MCFG2_ULBT_Msk (0x7u << MATRIX_MCFG2_ULBT_Pos) /**< \brief (MATRIX_MCFG2) Undefined Length Burst Type */
#define MATRIX_MCFG2_ULBT(value) ((MATRIX_MCFG2_ULBT_Msk & ((value) << MATRIX_MCFG2_ULBT_Pos)))
#define   MATRIX_MCFG2_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG2) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG2_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG2) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG2_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG2) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG2_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG2) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG2_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG2) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG2_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG2) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG2_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG2) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG2_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG2) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG3 : (MATRIX Offset: 0x000C) Master Configuration Register 3 -------- */
#define MATRIX_MCFG3_ULBT_Pos 0
#define MATRIX_MCFG3_ULBT_Msk (0x7u << MATRIX_MCFG3_ULBT_Pos) /**< \brief (MATRIX_MCFG3) Undefined Length Burst Type */
#define MATRIX_MCFG3_ULBT(value) ((MATRIX_MCFG3_ULBT_Msk & ((value) << MATRIX_MCFG3_ULBT_Pos)))
#define   MATRIX_MCFG3_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG3) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG3_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG3) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG3_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG3) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG3_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG3) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG3_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG3) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG3_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG3) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG3_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG3) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG3_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG3) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG4 : (MATRIX Offset: 0x0010) Master Configuration Register 4 -------- */
#define MATRIX_MCFG4_ULBT_Pos 0
#define MATRIX_MCFG4_ULBT_Msk (0x7u << MATRIX_MCFG4_ULBT_Pos) /**< \brief (MATRIX_MCFG4) Undefined Length Burst Type */
#define MATRIX_MCFG4_ULBT(value) ((MATRIX_MCFG4_ULBT_Msk & ((value) << MATRIX_MCFG4_ULBT_Pos)))
#define   MATRIX_MCFG4_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG4) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG4_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG4) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG4_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG4) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG4_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG4) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG4_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG4) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG4_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG4) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG4_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG4) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG4_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG4) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG5 : (MATRIX Offset: 0x0014) Master Configuration Register 5 -------- */
#define MATRIX_MCFG5_ULBT_Pos 0
#define MATRIX_MCFG5_ULBT_Msk (0x7u << MATRIX_MCFG5_ULBT_Pos) /**< \brief (MATRIX_MCFG5) Undefined Length Burst Type */
#define MATRIX_MCFG5_ULBT(value) ((MATRIX_MCFG5_ULBT_Msk & ((value) << MATRIX_MCFG5_ULBT_Pos)))
#define   MATRIX_MCFG5_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG5) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG5_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG5) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG5_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG5) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG5_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG5) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG5_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG5) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG5_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG5) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG5_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG5) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG5_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG5) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG6 : (MATRIX Offset: 0x0018) Master Configuration Register 6 -------- */
#define MATRIX_MCFG6_ULBT_Pos 0
#define MATRIX_MCFG6_ULBT_Msk (0x7u << MATRIX_MCFG6_ULBT_Pos) /**< \brief (MATRIX_MCFG6) Undefined Length Burst Type */
#define MATRIX_MCFG6_ULBT(value) ((MATRIX_MCFG6_ULBT_Msk & ((value) << MATRIX_MCFG6_ULBT_Pos)))
#define   MATRIX_MCFG6_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG6) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG6_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG6) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG6_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG6) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG6_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG6) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG6_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG6) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG6_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG6) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG6_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG6) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG6_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG6) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG7 : (MATRIX Offset: 0x001C) Master Configuration Register 7 -------- */
#define MATRIX_MCFG7_ULBT_Pos 0
#define MATRIX_MCFG7_ULBT_Msk (0x7u << MATRIX_MCFG7_ULBT_Pos) /**< \brief (MATRIX_MCFG7) Undefined Length Burst Type */
#define MATRIX_MCFG7_ULBT(value) ((MATRIX_MCFG7_ULBT_Msk & ((value) << MATRIX_MCFG7_ULBT_Pos)))
#define   MATRIX_MCFG7_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG7) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG7_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG7) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG7_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG7) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG7_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG7) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG7_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG7) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG7_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG7) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG7_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG7) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG7_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG7) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG8 : (MATRIX Offset: 0x0020) Master Configuration Register 8 -------- */
#define MATRIX_MCFG8_ULBT_Pos 0
#define MATRIX_MCFG8_ULBT_Msk (0x7u << MATRIX_MCFG8_ULBT_Pos) /**< \brief (MATRIX_MCFG8) Undefined Length Burst Type */
#define MATRIX_MCFG8_ULBT(value) ((MATRIX_MCFG8_ULBT_Msk & ((value) << MATRIX_MCFG8_ULBT_Pos)))
#define   MATRIX_MCFG8_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG8) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG8_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG8) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG8_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG8) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG8_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG8) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG8_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG8) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG8_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG8) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG8_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG8) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG8_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG8) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_MCFG9 : (MATRIX Offset: 0x0024) Master Configuration Register 9 -------- */
#define MATRIX_MCFG9_ULBT_Pos 0
#define MATRIX_MCFG9_ULBT_Msk (0x7u << MATRIX_MCFG9_ULBT_Pos) /**< \brief (MATRIX_MCFG9) Undefined Length Burst Type */
#define MATRIX_MCFG9_ULBT(value) ((MATRIX_MCFG9_ULBT_Msk & ((value) << MATRIX_MCFG9_ULBT_Pos)))
#define   MATRIX_MCFG9_ULBT_UNLIMITED (0x0u << 0) /**< \brief (MATRIX_MCFG9) Unlimited Length Burst-No predicted end of burst is generated, therefore INCR bursts coming from this master can only be broken if the Slave Slot Cycle Limit is reached. If the Slot Cycle Limit is not reached, the burst is normally completed by the master, at the latest, on the next AHB 1 Kbyte address boundary, allowing up to 256-beat word bursts or 128-beat double-word bursts.This value should not be used in the very particular case of a master capable of performing back-to-back undefined length bursts on a single slave, since this could indefinitely freeze the slave arbitration and thus prevent another master from accessing this slave. */
#define   MATRIX_MCFG9_ULBT_SINGLE (0x1u << 0) /**< \brief (MATRIX_MCFG9) Single Access-The undefined length burst is treated as a succession of single accesses, allowing re-arbitration at each beat of the INCR burst or bursts sequence. */
#define   MATRIX_MCFG9_ULBT_4_BEAT (0x2u << 0) /**< \brief (MATRIX_MCFG9) 4-beat Burst-The undefined length burst or bursts sequence is split into 4-beat bursts or less, allowing re-arbitration every 4 beats. */
#define   MATRIX_MCFG9_ULBT_8_BEAT (0x3u << 0) /**< \brief (MATRIX_MCFG9) 8-beat Burst-The undefined length burst or bursts sequence is split into 8-beat bursts or less, allowing re-arbitration every 8 beats. */
#define   MATRIX_MCFG9_ULBT_16_BEAT (0x4u << 0) /**< \brief (MATRIX_MCFG9) 16-beat Burst-The undefined length burst or bursts sequence is split into 16-beat bursts or less, allowing re-arbitration every 16 beats. */
#define   MATRIX_MCFG9_ULBT_32_BEAT (0x5u << 0) /**< \brief (MATRIX_MCFG9) 32-beat Burst-The undefined length burst or bursts sequence is split into 32-beat bursts or less, allowing re-arbitration every 32 beats. */
#define   MATRIX_MCFG9_ULBT_64_BEAT (0x6u << 0) /**< \brief (MATRIX_MCFG9) 64-beat Burst-The undefined length burst or bursts sequence is split into 64-beat bursts or less, allowing re-arbitration every 64 beats. */
#define   MATRIX_MCFG9_ULBT_128_BEAT (0x7u << 0) /**< \brief (MATRIX_MCFG9) 128-beat Burst-The undefined length burst or bursts sequence is split into 128-beat bursts or less, allowing re-arbitration every 128 beats.Unless duly needed, the ULBT should be left at its default 0 value for power saving. */
/* -------- MATRIX_SCFG0 : (MATRIX Offset: 0x0040) Slave Configuration Register 0 -------- */
#define MATRIX_SCFG0_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG0_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG0_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG0) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG0_SLOT_CYCLE(value) ((MATRIX_SCFG0_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG0_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG0_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG0_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG0_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG0) Default Master Type */
#define MATRIX_SCFG0_DEFMSTR_TYPE(value) ((MATRIX_SCFG0_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG0_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG0_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG0) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG0_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG0) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG0_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG0) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG0_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG0_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG0_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG0) Fixed Default Master */
#define MATRIX_SCFG0_FIXED_DEFMSTR(value) ((MATRIX_SCFG0_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG0_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG1 : (MATRIX Offset: 0x0044) Slave Configuration Register 1 -------- */
#define MATRIX_SCFG1_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG1_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG1_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG1) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG1_SLOT_CYCLE(value) ((MATRIX_SCFG1_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG1_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG1_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG1_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG1_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG1) Default Master Type */
#define MATRIX_SCFG1_DEFMSTR_TYPE(value) ((MATRIX_SCFG1_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG1_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG1_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG1) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG1_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG1) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG1_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG1) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG1_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG1_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG1_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG1) Fixed Default Master */
#define MATRIX_SCFG1_FIXED_DEFMSTR(value) ((MATRIX_SCFG1_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG1_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG2 : (MATRIX Offset: 0x0048) Slave Configuration Register 2 -------- */
#define MATRIX_SCFG2_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG2_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG2_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG2) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG2_SLOT_CYCLE(value) ((MATRIX_SCFG2_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG2_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG2_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG2_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG2_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG2) Default Master Type */
#define MATRIX_SCFG2_DEFMSTR_TYPE(value) ((MATRIX_SCFG2_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG2_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG2_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG2) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG2_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG2) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG2_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG2) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG2_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG2_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG2_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG2) Fixed Default Master */
#define MATRIX_SCFG2_FIXED_DEFMSTR(value) ((MATRIX_SCFG2_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG2_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG3 : (MATRIX Offset: 0x004C) Slave Configuration Register 3 -------- */
#define MATRIX_SCFG3_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG3_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG3_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG3) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG3_SLOT_CYCLE(value) ((MATRIX_SCFG3_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG3_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG3_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG3_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG3_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG3) Default Master Type */
#define MATRIX_SCFG3_DEFMSTR_TYPE(value) ((MATRIX_SCFG3_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG3_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG3_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG3) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG3_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG3) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG3_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG3) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG3_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG3_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG3_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG3) Fixed Default Master */
#define MATRIX_SCFG3_FIXED_DEFMSTR(value) ((MATRIX_SCFG3_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG3_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG4 : (MATRIX Offset: 0x0050) Slave Configuration Register 4 -------- */
#define MATRIX_SCFG4_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG4_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG4_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG4) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG4_SLOT_CYCLE(value) ((MATRIX_SCFG4_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG4_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG4_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG4_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG4_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG4) Default Master Type */
#define MATRIX_SCFG4_DEFMSTR_TYPE(value) ((MATRIX_SCFG4_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG4_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG4_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG4) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG4_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG4) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG4_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG4) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG4_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG4_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG4_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG4) Fixed Default Master */
#define MATRIX_SCFG4_FIXED_DEFMSTR(value) ((MATRIX_SCFG4_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG4_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG5 : (MATRIX Offset: 0x0054) Slave Configuration Register 5 -------- */
#define MATRIX_SCFG5_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG5_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG5_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG5) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG5_SLOT_CYCLE(value) ((MATRIX_SCFG5_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG5_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG5_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG5_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG5_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG5) Default Master Type */
#define MATRIX_SCFG5_DEFMSTR_TYPE(value) ((MATRIX_SCFG5_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG5_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG5_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG5) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG5_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG5) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG5_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG5) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG5_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG5_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG5_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG5) Fixed Default Master */
#define MATRIX_SCFG5_FIXED_DEFMSTR(value) ((MATRIX_SCFG5_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG5_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG6 : (MATRIX Offset: 0x0058) Slave Configuration Register 6 -------- */
#define MATRIX_SCFG6_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG6_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG6_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG6) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG6_SLOT_CYCLE(value) ((MATRIX_SCFG6_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG6_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG6_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG6_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG6_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG6) Default Master Type */
#define MATRIX_SCFG6_DEFMSTR_TYPE(value) ((MATRIX_SCFG6_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG6_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG6_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG6) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG6_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG6) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG6_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG6) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG6_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG6_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG6_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG6) Fixed Default Master */
#define MATRIX_SCFG6_FIXED_DEFMSTR(value) ((MATRIX_SCFG6_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG6_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG7 : (MATRIX Offset: 0x005C) Slave Configuration Register 7 -------- */
#define MATRIX_SCFG7_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG7_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG7_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG7) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG7_SLOT_CYCLE(value) ((MATRIX_SCFG7_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG7_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG7_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG7_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG7_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG7) Default Master Type */
#define MATRIX_SCFG7_DEFMSTR_TYPE(value) ((MATRIX_SCFG7_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG7_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG7_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG7) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG7_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG7) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG7_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG7) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG7_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG7_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG7_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG7) Fixed Default Master */
#define MATRIX_SCFG7_FIXED_DEFMSTR(value) ((MATRIX_SCFG7_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG7_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG8 : (MATRIX Offset: 0x0060) Slave Configuration Register 8 -------- */
#define MATRIX_SCFG8_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG8_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG8_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG8) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG8_SLOT_CYCLE(value) ((MATRIX_SCFG8_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG8_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG8_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG8_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG8_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG8) Default Master Type */
#define MATRIX_SCFG8_DEFMSTR_TYPE(value) ((MATRIX_SCFG8_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG8_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG8_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG8) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG8_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG8) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG8_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG8) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG8_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG8_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG8_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG8) Fixed Default Master */
#define MATRIX_SCFG8_FIXED_DEFMSTR(value) ((MATRIX_SCFG8_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG8_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG9 : (MATRIX Offset: 0x0064) Slave Configuration Register 9 -------- */
#define MATRIX_SCFG9_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG9_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG9_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG9) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG9_SLOT_CYCLE(value) ((MATRIX_SCFG9_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG9_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG9_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG9_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG9_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG9) Default Master Type */
#define MATRIX_SCFG9_DEFMSTR_TYPE(value) ((MATRIX_SCFG9_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG9_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG9_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG9) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG9_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG9) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG9_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG9) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG9_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG9_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG9_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG9) Fixed Default Master */
#define MATRIX_SCFG9_FIXED_DEFMSTR(value) ((MATRIX_SCFG9_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG9_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG10 : (MATRIX Offset: 0x0068) Slave Configuration Register 10 -------- */
#define MATRIX_SCFG10_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG10_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG10_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG10) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG10_SLOT_CYCLE(value) ((MATRIX_SCFG10_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG10_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG10_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG10_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG10_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG10) Default Master Type */
#define MATRIX_SCFG10_DEFMSTR_TYPE(value) ((MATRIX_SCFG10_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG10_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG10_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG10) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG10_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG10) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG10_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG10) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG10_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG10_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG10_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG10) Fixed Default Master */
#define MATRIX_SCFG10_FIXED_DEFMSTR(value) ((MATRIX_SCFG10_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG10_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG11 : (MATRIX Offset: 0x006C) Slave Configuration Register 11 -------- */
#define MATRIX_SCFG11_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG11_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG11_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG11) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG11_SLOT_CYCLE(value) ((MATRIX_SCFG11_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG11_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG11_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG11_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG11_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG11) Default Master Type */
#define MATRIX_SCFG11_DEFMSTR_TYPE(value) ((MATRIX_SCFG11_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG11_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG11_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG11) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG11_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG11) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG11_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG11) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG11_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG11_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG11_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG11) Fixed Default Master */
#define MATRIX_SCFG11_FIXED_DEFMSTR(value) ((MATRIX_SCFG11_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG11_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_SCFG12 : (MATRIX Offset: 0x0070) Slave Configuration Register 12 -------- */
#define MATRIX_SCFG12_SLOT_CYCLE_Pos 0
#define MATRIX_SCFG12_SLOT_CYCLE_Msk (0x1ffu << MATRIX_SCFG12_SLOT_CYCLE_Pos) /**< \brief (MATRIX_SCFG12) Maximum Bus Grant Duration for Masters */
#define MATRIX_SCFG12_SLOT_CYCLE(value) ((MATRIX_SCFG12_SLOT_CYCLE_Msk & ((value) << MATRIX_SCFG12_SLOT_CYCLE_Pos)))
#define MATRIX_SCFG12_DEFMSTR_TYPE_Pos 16
#define MATRIX_SCFG12_DEFMSTR_TYPE_Msk (0x3u << MATRIX_SCFG12_DEFMSTR_TYPE_Pos) /**< \brief (MATRIX_SCFG12) Default Master Type */
#define MATRIX_SCFG12_DEFMSTR_TYPE(value) ((MATRIX_SCFG12_DEFMSTR_TYPE_Msk & ((value) << MATRIX_SCFG12_DEFMSTR_TYPE_Pos)))
#define   MATRIX_SCFG12_DEFMSTR_TYPE_NONE (0x0u << 16) /**< \brief (MATRIX_SCFG12) No Default Master-At the end of the current slave access, if no other master request is pending, the slave is disconnected from all masters.This results in a one clock cycle latency for the first access of a burst transfer or for a single access. */
#define   MATRIX_SCFG12_DEFMSTR_TYPE_LAST (0x1u << 16) /**< \brief (MATRIX_SCFG12) Last Default Master-At the end of the current slave access, if no other master request is pending, the slave stays connected to the last master having accessed it.This results in not having one clock cycle latency when the last master tries to access the slave again. */
#define   MATRIX_SCFG12_DEFMSTR_TYPE_FIXED (0x2u << 16) /**< \brief (MATRIX_SCFG12) Fixed Default Master-At the end of the current slave access, if no other master request is pending, the slave connects to the fixed master the number that has been written in the FIXED_DEFMSTR field.This results in not having one clock cycle latency when the fixed master tries to access the slave again. */
#define MATRIX_SCFG12_FIXED_DEFMSTR_Pos 18
#define MATRIX_SCFG12_FIXED_DEFMSTR_Msk (0xfu << MATRIX_SCFG12_FIXED_DEFMSTR_Pos) /**< \brief (MATRIX_SCFG12) Fixed Default Master */
#define MATRIX_SCFG12_FIXED_DEFMSTR(value) ((MATRIX_SCFG12_FIXED_DEFMSTR_Msk & ((value) << MATRIX_SCFG12_FIXED_DEFMSTR_Pos)))
/* -------- MATRIX_PRAS : (MATRIX Offset: N/A) Priority Register A for Slave 0 -------- */
#define MATRIX_PRAS_M0PR_Pos 0
#define MATRIX_PRAS_M0PR_Msk (0x3u << MATRIX_PRAS_M0PR_Pos) /**< \brief (MATRIX_PRAS) Master 0 Priority */
#define MATRIX_PRAS_M0PR(value) ((MATRIX_PRAS_M0PR_Msk & ((value) << MATRIX_PRAS_M0PR_Pos)))
#define MATRIX_PRAS_M1PR_Pos 4
#define MATRIX_PRAS_M1PR_Msk (0x3u << MATRIX_PRAS_M1PR_Pos) /**< \brief (MATRIX_PRAS) Master 1 Priority */
#define MATRIX_PRAS_M1PR(value) ((MATRIX_PRAS_M1PR_Msk & ((value) << MATRIX_PRAS_M1PR_Pos)))
#define MATRIX_PRAS_M2PR_Pos 8
#define MATRIX_PRAS_M2PR_Msk (0x3u << MATRIX_PRAS_M2PR_Pos) /**< \brief (MATRIX_PRAS) Master 2 Priority */
#define MATRIX_PRAS_M2PR(value) ((MATRIX_PRAS_M2PR_Msk & ((value) << MATRIX_PRAS_M2PR_Pos)))
#define MATRIX_PRAS_M3PR_Pos 12
#define MATRIX_PRAS_M3PR_Msk (0x3u << MATRIX_PRAS_M3PR_Pos) /**< \brief (MATRIX_PRAS) Master 3 Priority */
#define MATRIX_PRAS_M3PR(value) ((MATRIX_PRAS_M3PR_Msk & ((value) << MATRIX_PRAS_M3PR_Pos)))
#define MATRIX_PRAS_M4PR_Pos 16
#define MATRIX_PRAS_M4PR_Msk (0x3u << MATRIX_PRAS_M4PR_Pos) /**< \brief (MATRIX_PRAS) Master 4 Priority */
#define MATRIX_PRAS_M4PR(value) ((MATRIX_PRAS_M4PR_Msk & ((value) << MATRIX_PRAS_M4PR_Pos)))
#define MATRIX_PRAS_M5PR_Pos 20
#define MATRIX_PRAS_M5PR_Msk (0x3u << MATRIX_PRAS_M5PR_Pos) /**< \brief (MATRIX_PRAS) Master 5 Priority */
#define MATRIX_PRAS_M5PR(value) ((MATRIX_PRAS_M5PR_Msk & ((value) << MATRIX_PRAS_M5PR_Pos)))
#define MATRIX_PRAS_M6PR_Pos 24
#define MATRIX_PRAS_M6PR_Msk (0x3u << MATRIX_PRAS_M6PR_Pos) /**< \brief (MATRIX_PRAS) Master 6 Priority */
#define MATRIX_PRAS_M6PR(value) ((MATRIX_PRAS_M6PR_Msk & ((value) << MATRIX_PRAS_M6PR_Pos)))
#define MATRIX_PRAS_M7PR_Pos 28
#define MATRIX_PRAS_M7PR_Msk (0x3u << MATRIX_PRAS_M7PR_Pos) /**< \brief (MATRIX_PRAS) Master 7 Priority */
#define MATRIX_PRAS_M7PR(value) ((MATRIX_PRAS_M7PR_Msk & ((value) << MATRIX_PRAS_M7PR_Pos)))
/* -------- MATRIX_PRBS : (MATRIX Offset: N/A) Priority Register B for Slave 0 -------- */
#define MATRIX_PRBS_M8PR_Pos 0
#define MATRIX_PRBS_M8PR_Msk (0x3u << MATRIX_PRBS_M8PR_Pos) /**< \brief (MATRIX_PRBS) Master 8 Priority */
#define MATRIX_PRBS_M8PR(value) ((MATRIX_PRBS_M8PR_Msk & ((value) << MATRIX_PRBS_M8PR_Pos)))
#define MATRIX_PRBS_M9PR_Pos 4
#define MATRIX_PRBS_M9PR_Msk (0x3u << MATRIX_PRBS_M9PR_Pos) /**< \brief (MATRIX_PRBS) Master 9 Priority */
#define MATRIX_PRBS_M9PR(value) ((MATRIX_PRBS_M9PR_Msk & ((value) << MATRIX_PRBS_M9PR_Pos)))
#define MATRIX_PRBS_M10PR_Pos 8
#define MATRIX_PRBS_M10PR_Msk (0x3u << MATRIX_PRBS_M10PR_Pos) /**< \brief (MATRIX_PRBS) Master 10 Priority */
#define MATRIX_PRBS_M10PR(value) ((MATRIX_PRBS_M10PR_Msk & ((value) << MATRIX_PRBS_M10PR_Pos)))
#define MATRIX_PRBS_M11PR_Pos 12
#define MATRIX_PRBS_M11PR_Msk (0x3u << MATRIX_PRBS_M11PR_Pos) /**< \brief (MATRIX_PRBS) Master 11 Priority */
#define MATRIX_PRBS_M11PR(value) ((MATRIX_PRBS_M11PR_Msk & ((value) << MATRIX_PRBS_M11PR_Pos)))
/* -------- MATRIX_MEIER : (MATRIX Offset: 0x0150) Master Error Interrupt Enable Register -------- */
#define MATRIX_MEIER_MERR0 (0x1u << 0) /**< \brief (MATRIX_MEIER) Master 0 Access Error */
#define MATRIX_MEIER_MERR1 (0x1u << 1) /**< \brief (MATRIX_MEIER) Master 1 Access Error */
#define MATRIX_MEIER_MERR2 (0x1u << 2) /**< \brief (MATRIX_MEIER) Master 2 Access Error */
#define MATRIX_MEIER_MERR3 (0x1u << 3) /**< \brief (MATRIX_MEIER) Master 3 Access Error */
#define MATRIX_MEIER_MERR4 (0x1u << 4) /**< \brief (MATRIX_MEIER) Master 4 Access Error */
#define MATRIX_MEIER_MERR5 (0x1u << 5) /**< \brief (MATRIX_MEIER) Master 5 Access Error */
#define MATRIX_MEIER_MERR6 (0x1u << 6) /**< \brief (MATRIX_MEIER) Master 6 Access Error */
#define MATRIX_MEIER_MERR7 (0x1u << 7) /**< \brief (MATRIX_MEIER) Master 7 Access Error */
#define MATRIX_MEIER_MERR8 (0x1u << 8) /**< \brief (MATRIX_MEIER) Master 8 Access Error */
#define MATRIX_MEIER_MERR9 (0x1u << 9) /**< \brief (MATRIX_MEIER) Master 9 Access Error */
#define MATRIX_MEIER_MERR10 (0x1u << 10) /**< \brief (MATRIX_MEIER) Master 10 Access Error */
#define MATRIX_MEIER_MERR11 (0x1u << 11) /**< \brief (MATRIX_MEIER) Master 11 Access Error */
/* -------- MATRIX_MEIDR : (MATRIX Offset: 0x0154) Master Error Interrupt Disable Register -------- */
#define MATRIX_MEIDR_MERR0 (0x1u << 0) /**< \brief (MATRIX_MEIDR) Master 0 Access Error */
#define MATRIX_MEIDR_MERR1 (0x1u << 1) /**< \brief (MATRIX_MEIDR) Master 1 Access Error */
#define MATRIX_MEIDR_MERR2 (0x1u << 2) /**< \brief (MATRIX_MEIDR) Master 2 Access Error */
#define MATRIX_MEIDR_MERR3 (0x1u << 3) /**< \brief (MATRIX_MEIDR) Master 3 Access Error */
#define MATRIX_MEIDR_MERR4 (0x1u << 4) /**< \brief (MATRIX_MEIDR) Master 4 Access Error */
#define MATRIX_MEIDR_MERR5 (0x1u << 5) /**< \brief (MATRIX_MEIDR) Master 5 Access Error */
#define MATRIX_MEIDR_MERR6 (0x1u << 6) /**< \brief (MATRIX_MEIDR) Master 6 Access Error */
#define MATRIX_MEIDR_MERR7 (0x1u << 7) /**< \brief (MATRIX_MEIDR) Master 7 Access Error */
#define MATRIX_MEIDR_MERR8 (0x1u << 8) /**< \brief (MATRIX_MEIDR) Master 8 Access Error */
#define MATRIX_MEIDR_MERR9 (0x1u << 9) /**< \brief (MATRIX_MEIDR) Master 9 Access Error */
#define MATRIX_MEIDR_MERR10 (0x1u << 10) /**< \brief (MATRIX_MEIDR) Master 10 Access Error */
#define MATRIX_MEIDR_MERR11 (0x1u << 11) /**< \brief (MATRIX_MEIDR) Master 11 Access Error */
/* -------- MATRIX_MEIMR : (MATRIX Offset: 0x0158) Master Error Interrupt Mask Register -------- */
#define MATRIX_MEIMR_MERR0 (0x1u << 0) /**< \brief (MATRIX_MEIMR) Master 0 Access Error */
#define MATRIX_MEIMR_MERR1 (0x1u << 1) /**< \brief (MATRIX_MEIMR) Master 1 Access Error */
#define MATRIX_MEIMR_MERR2 (0x1u << 2) /**< \brief (MATRIX_MEIMR) Master 2 Access Error */
#define MATRIX_MEIMR_MERR3 (0x1u << 3) /**< \brief (MATRIX_MEIMR) Master 3 Access Error */
#define MATRIX_MEIMR_MERR4 (0x1u << 4) /**< \brief (MATRIX_MEIMR) Master 4 Access Error */
#define MATRIX_MEIMR_MERR5 (0x1u << 5) /**< \brief (MATRIX_MEIMR) Master 5 Access Error */
#define MATRIX_MEIMR_MERR6 (0x1u << 6) /**< \brief (MATRIX_MEIMR) Master 6 Access Error */
#define MATRIX_MEIMR_MERR7 (0x1u << 7) /**< \brief (MATRIX_MEIMR) Master 7 Access Error */
#define MATRIX_MEIMR_MERR8 (0x1u << 8) /**< \brief (MATRIX_MEIMR) Master 8 Access Error */
#define MATRIX_MEIMR_MERR9 (0x1u << 9) /**< \brief (MATRIX_MEIMR) Master 9 Access Error */
#define MATRIX_MEIMR_MERR10 (0x1u << 10) /**< \brief (MATRIX_MEIMR) Master 10 Access Error */
#define MATRIX_MEIMR_MERR11 (0x1u << 11) /**< \brief (MATRIX_MEIMR) Master 11 Access Error */
/* -------- MATRIX_MESR : (MATRIX Offset: 0x015C) Master Error Status Register -------- */
#define MATRIX_MESR_MERR0 (0x1u << 0) /**< \brief (MATRIX_MESR) Master 0 Access Error */
#define MATRIX_MESR_MERR1 (0x1u << 1) /**< \brief (MATRIX_MESR) Master 1 Access Error */
#define MATRIX_MESR_MERR2 (0x1u << 2) /**< \brief (MATRIX_MESR) Master 2 Access Error */
#define MATRIX_MESR_MERR3 (0x1u << 3) /**< \brief (MATRIX_MESR) Master 3 Access Error */
#define MATRIX_MESR_MERR4 (0x1u << 4) /**< \brief (MATRIX_MESR) Master 4 Access Error */
#define MATRIX_MESR_MERR5 (0x1u << 5) /**< \brief (MATRIX_MESR) Master 5 Access Error */
#define MATRIX_MESR_MERR6 (0x1u << 6) /**< \brief (MATRIX_MESR) Master 6 Access Error */
#define MATRIX_MESR_MERR7 (0x1u << 7) /**< \brief (MATRIX_MESR) Master 7 Access Error */
#define MATRIX_MESR_MERR8 (0x1u << 8) /**< \brief (MATRIX_MESR) Master 8 Access Error */
#define MATRIX_MESR_MERR9 (0x1u << 9) /**< \brief (MATRIX_MESR) Master 9 Access Error */
#define MATRIX_MESR_MERR10 (0x1u << 10) /**< \brief (MATRIX_MESR) Master 10 Access Error */
#define MATRIX_MESR_MERR11 (0x1u << 11) /**< \brief (MATRIX_MESR) Master 11 Access Error */
/* -------- MATRIX_MEAR0 : (MATRIX Offset: 0x0160) Master 0 Error Address Register -------- */
#define MATRIX_MEAR0_ERRADD_Pos 0
#define MATRIX_MEAR0_ERRADD_Msk (0xffffffffu << MATRIX_MEAR0_ERRADD_Pos) /**< \brief (MATRIX_MEAR0) Master Error Address */
/* -------- MATRIX_MEAR1 : (MATRIX Offset: 0x0164) Master 1 Error Address Register -------- */
#define MATRIX_MEAR1_ERRADD_Pos 0
#define MATRIX_MEAR1_ERRADD_Msk (0xffffffffu << MATRIX_MEAR1_ERRADD_Pos) /**< \brief (MATRIX_MEAR1) Master Error Address */
/* -------- MATRIX_MEAR2 : (MATRIX Offset: 0x0168) Master 2 Error Address Register -------- */
#define MATRIX_MEAR2_ERRADD_Pos 0
#define MATRIX_MEAR2_ERRADD_Msk (0xffffffffu << MATRIX_MEAR2_ERRADD_Pos) /**< \brief (MATRIX_MEAR2) Master Error Address */
/* -------- MATRIX_MEAR3 : (MATRIX Offset: 0x016C) Master 3 Error Address Register -------- */
#define MATRIX_MEAR3_ERRADD_Pos 0
#define MATRIX_MEAR3_ERRADD_Msk (0xffffffffu << MATRIX_MEAR3_ERRADD_Pos) /**< \brief (MATRIX_MEAR3) Master Error Address */
/* -------- MATRIX_MEAR4 : (MATRIX Offset: 0x0170) Master 4 Error Address Register -------- */
#define MATRIX_MEAR4_ERRADD_Pos 0
#define MATRIX_MEAR4_ERRADD_Msk (0xffffffffu << MATRIX_MEAR4_ERRADD_Pos) /**< \brief (MATRIX_MEAR4) Master Error Address */
/* -------- MATRIX_MEAR5 : (MATRIX Offset: 0x0174) Master 5 Error Address Register -------- */
#define MATRIX_MEAR5_ERRADD_Pos 0
#define MATRIX_MEAR5_ERRADD_Msk (0xffffffffu << MATRIX_MEAR5_ERRADD_Pos) /**< \brief (MATRIX_MEAR5) Master Error Address */
/* -------- MATRIX_MEAR6 : (MATRIX Offset: 0x0178) Master 6 Error Address Register -------- */
#define MATRIX_MEAR6_ERRADD_Pos 0
#define MATRIX_MEAR6_ERRADD_Msk (0xffffffffu << MATRIX_MEAR6_ERRADD_Pos) /**< \brief (MATRIX_MEAR6) Master Error Address */
/* -------- MATRIX_MEAR7 : (MATRIX Offset: 0x017C) Master 7 Error Address Register -------- */
#define MATRIX_MEAR7_ERRADD_Pos 0
#define MATRIX_MEAR7_ERRADD_Msk (0xffffffffu << MATRIX_MEAR7_ERRADD_Pos) /**< \brief (MATRIX_MEAR7) Master Error Address */
/* -------- MATRIX_MEAR8 : (MATRIX Offset: 0x0180) Master 8 Error Address Register -------- */
#define MATRIX_MEAR8_ERRADD_Pos 0
#define MATRIX_MEAR8_ERRADD_Msk (0xffffffffu << MATRIX_MEAR8_ERRADD_Pos) /**< \brief (MATRIX_MEAR8) Master Error Address */
/* -------- MATRIX_MEAR9 : (MATRIX Offset: 0x0184) Master 9 Error Address Register -------- */
#define MATRIX_MEAR9_ERRADD_Pos 0
#define MATRIX_MEAR9_ERRADD_Msk (0xffffffffu << MATRIX_MEAR9_ERRADD_Pos) /**< \brief (MATRIX_MEAR9) Master Error Address */
/* -------- MATRIX_WPMR : (MATRIX Offset: 0x01E4) Write Protection Mode Register -------- */
#define MATRIX_WPMR_WPEN (0x1u << 0) /**< \brief (MATRIX_WPMR) Write Protection Enable */
#define MATRIX_WPMR_WPKEY_Pos 8
#define MATRIX_WPMR_WPKEY_Msk (0xffffffu << MATRIX_WPMR_WPKEY_Pos) /**< \brief (MATRIX_WPMR) Write Protection Key (Write-only) */
#define MATRIX_WPMR_WPKEY(value) ((MATRIX_WPMR_WPKEY_Msk & ((value) << MATRIX_WPMR_WPKEY_Pos)))
#define   MATRIX_WPMR_WPKEY_PASSWD (0x4D4154u << 8) /**< \brief (MATRIX_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit.Always reads as 0. */
/* -------- MATRIX_WPSR : (MATRIX Offset: 0x01E8) Write Protection Status Register -------- */
#define MATRIX_WPSR_WPVS (0x1u << 0) /**< \brief (MATRIX_WPSR) Write Protection Violation Status */
#define MATRIX_WPSR_WPVSRC_Pos 8
#define MATRIX_WPSR_WPVSRC_Msk (0xffffu << MATRIX_WPSR_WPVSRC_Pos) /**< \brief (MATRIX_WPSR) Write Protection Violation Source */
/* -------- MATRIX_VERSION : (MATRIX Offset: 0x01FC) Version Register -------- */
#define MATRIX_VERSION_VERSION_Pos 0
#define MATRIX_VERSION_VERSION_Msk (0xfffu << MATRIX_VERSION_VERSION_Pos) /**< \brief (MATRIX_VERSION) Version of the Hardware Module */
#define MATRIX_VERSION_MFN_Pos 16
#define MATRIX_VERSION_MFN_Msk (0x7u << MATRIX_VERSION_MFN_Pos) /**< \brief (MATRIX_VERSION) Metal Fix Number */
/* -------- MATRIX_SSR0 : (MATRIX Offset: 0x0200) Security Slave 0 Register -------- */
#define MATRIX_SSR0_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR0) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR0_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR0) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR0_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR0) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR1 : (MATRIX Offset: 0x0204) Security Slave 1 Register -------- */
#define MATRIX_SSR1_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR1) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR1_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR1) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR1_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR1) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR2 : (MATRIX Offset: 0x0208) Security Slave 2 Register -------- */
#define MATRIX_SSR2_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR2) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR2_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR2) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR2_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR2) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR3 : (MATRIX Offset: 0x020C) Security Slave 3 Register -------- */
#define MATRIX_SSR3_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR3) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR3_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR3) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR3_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR3) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR4 : (MATRIX Offset: 0x0210) Security Slave 4 Register -------- */
#define MATRIX_SSR4_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR4) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR4_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR4) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR4_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR4) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR5 : (MATRIX Offset: 0x0214) Security Slave 5 Register -------- */
#define MATRIX_SSR5_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR5) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR5_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR5) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR5_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR5) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR6 : (MATRIX Offset: 0x0218) Security Slave 6 Register -------- */
#define MATRIX_SSR6_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR6) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR6_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR6) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR6_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR6) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR7 : (MATRIX Offset: 0x021C) Security Slave 7 Register -------- */
#define MATRIX_SSR7_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR7) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR7_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR7) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR7_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR7) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR8 : (MATRIX Offset: 0x0220) Security Slave 8 Register -------- */
#define MATRIX_SSR8_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR8) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR8_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR8) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR8_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR8) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR9 : (MATRIX Offset: 0x0224) Security Slave 9 Register -------- */
#define MATRIX_SSR9_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR9) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR9_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR9) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR9_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR9) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR10 : (MATRIX Offset: 0x0228) Security Slave 10 Register -------- */
#define MATRIX_SSR10_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR10) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR10_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR10) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR10_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR10) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR11 : (MATRIX Offset: 0x022C) Security Slave 11 Register -------- */
#define MATRIX_SSR11_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR11) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR11_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR11) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR11_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR11) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SSR12 : (MATRIX Offset: 0x0230) Security Slave 12 Register -------- */
#define MATRIX_SSR12_LANSECH0 (0x1u << 0) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH1 (0x1u << 1) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH2 (0x1u << 2) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH3 (0x1u << 3) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH4 (0x1u << 4) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH5 (0x1u << 5) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH6 (0x1u << 6) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_LANSECH7 (0x1u << 7) /**< \brief (MATRIX_SSR12) Low Area Non-secured in HSELx Security Region */
#define MATRIX_SSR12_RDNSECH0 (0x1u << 8) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH1 (0x1u << 9) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH2 (0x1u << 10) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH3 (0x1u << 11) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH4 (0x1u << 12) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH5 (0x1u << 13) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH6 (0x1u << 14) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_RDNSECH7 (0x1u << 15) /**< \brief (MATRIX_SSR12) Read Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH0 (0x1u << 16) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH1 (0x1u << 17) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH2 (0x1u << 18) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH3 (0x1u << 19) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH4 (0x1u << 20) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH5 (0x1u << 21) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH6 (0x1u << 22) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
#define MATRIX_SSR12_WRNSECH7 (0x1u << 23) /**< \brief (MATRIX_SSR12) Write Non-secured for HSELx Security Region */
/* -------- MATRIX_SASSR0 : (MATRIX Offset: 0x0240) Security Areas Split Slave 0 Register -------- */
#define MATRIX_SASSR0_SASPLIT0_Pos 0
#define MATRIX_SASSR0_SASPLIT0_Msk (0xfu << MATRIX_SASSR0_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT0(value) ((MATRIX_SASSR0_SASPLIT0_Msk & ((value) << MATRIX_SASSR0_SASPLIT0_Pos)))
#define MATRIX_SASSR0_SASPLIT1_Pos 4
#define MATRIX_SASSR0_SASPLIT1_Msk (0xfu << MATRIX_SASSR0_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT1(value) ((MATRIX_SASSR0_SASPLIT1_Msk & ((value) << MATRIX_SASSR0_SASPLIT1_Pos)))
#define MATRIX_SASSR0_SASPLIT2_Pos 8
#define MATRIX_SASSR0_SASPLIT2_Msk (0xfu << MATRIX_SASSR0_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT2(value) ((MATRIX_SASSR0_SASPLIT2_Msk & ((value) << MATRIX_SASSR0_SASPLIT2_Pos)))
#define MATRIX_SASSR0_SASPLIT3_Pos 12
#define MATRIX_SASSR0_SASPLIT3_Msk (0xfu << MATRIX_SASSR0_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT3(value) ((MATRIX_SASSR0_SASPLIT3_Msk & ((value) << MATRIX_SASSR0_SASPLIT3_Pos)))
#define MATRIX_SASSR0_SASPLIT4_Pos 16
#define MATRIX_SASSR0_SASPLIT4_Msk (0xfu << MATRIX_SASSR0_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT4(value) ((MATRIX_SASSR0_SASPLIT4_Msk & ((value) << MATRIX_SASSR0_SASPLIT4_Pos)))
#define MATRIX_SASSR0_SASPLIT5_Pos 20
#define MATRIX_SASSR0_SASPLIT5_Msk (0xfu << MATRIX_SASSR0_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT5(value) ((MATRIX_SASSR0_SASPLIT5_Msk & ((value) << MATRIX_SASSR0_SASPLIT5_Pos)))
#define MATRIX_SASSR0_SASPLIT6_Pos 24
#define MATRIX_SASSR0_SASPLIT6_Msk (0xfu << MATRIX_SASSR0_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT6(value) ((MATRIX_SASSR0_SASPLIT6_Msk & ((value) << MATRIX_SASSR0_SASPLIT6_Pos)))
#define MATRIX_SASSR0_SASPLIT7_Pos 28
#define MATRIX_SASSR0_SASPLIT7_Msk (0xfu << MATRIX_SASSR0_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR0) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR0_SASPLIT7(value) ((MATRIX_SASSR0_SASPLIT7_Msk & ((value) << MATRIX_SASSR0_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR1 : (MATRIX Offset: 0x0244) Security Areas Split Slave 1 Register -------- */
#define MATRIX_SASSR1_SASPLIT0_Pos 0
#define MATRIX_SASSR1_SASPLIT0_Msk (0xfu << MATRIX_SASSR1_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT0(value) ((MATRIX_SASSR1_SASPLIT0_Msk & ((value) << MATRIX_SASSR1_SASPLIT0_Pos)))
#define MATRIX_SASSR1_SASPLIT1_Pos 4
#define MATRIX_SASSR1_SASPLIT1_Msk (0xfu << MATRIX_SASSR1_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT1(value) ((MATRIX_SASSR1_SASPLIT1_Msk & ((value) << MATRIX_SASSR1_SASPLIT1_Pos)))
#define MATRIX_SASSR1_SASPLIT2_Pos 8
#define MATRIX_SASSR1_SASPLIT2_Msk (0xfu << MATRIX_SASSR1_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT2(value) ((MATRIX_SASSR1_SASPLIT2_Msk & ((value) << MATRIX_SASSR1_SASPLIT2_Pos)))
#define MATRIX_SASSR1_SASPLIT3_Pos 12
#define MATRIX_SASSR1_SASPLIT3_Msk (0xfu << MATRIX_SASSR1_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT3(value) ((MATRIX_SASSR1_SASPLIT3_Msk & ((value) << MATRIX_SASSR1_SASPLIT3_Pos)))
#define MATRIX_SASSR1_SASPLIT4_Pos 16
#define MATRIX_SASSR1_SASPLIT4_Msk (0xfu << MATRIX_SASSR1_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT4(value) ((MATRIX_SASSR1_SASPLIT4_Msk & ((value) << MATRIX_SASSR1_SASPLIT4_Pos)))
#define MATRIX_SASSR1_SASPLIT5_Pos 20
#define MATRIX_SASSR1_SASPLIT5_Msk (0xfu << MATRIX_SASSR1_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT5(value) ((MATRIX_SASSR1_SASPLIT5_Msk & ((value) << MATRIX_SASSR1_SASPLIT5_Pos)))
#define MATRIX_SASSR1_SASPLIT6_Pos 24
#define MATRIX_SASSR1_SASPLIT6_Msk (0xfu << MATRIX_SASSR1_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT6(value) ((MATRIX_SASSR1_SASPLIT6_Msk & ((value) << MATRIX_SASSR1_SASPLIT6_Pos)))
#define MATRIX_SASSR1_SASPLIT7_Pos 28
#define MATRIX_SASSR1_SASPLIT7_Msk (0xfu << MATRIX_SASSR1_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR1) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR1_SASPLIT7(value) ((MATRIX_SASSR1_SASPLIT7_Msk & ((value) << MATRIX_SASSR1_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR2 : (MATRIX Offset: 0x0248) Security Areas Split Slave 2 Register -------- */
#define MATRIX_SASSR2_SASPLIT0_Pos 0
#define MATRIX_SASSR2_SASPLIT0_Msk (0xfu << MATRIX_SASSR2_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT0(value) ((MATRIX_SASSR2_SASPLIT0_Msk & ((value) << MATRIX_SASSR2_SASPLIT0_Pos)))
#define MATRIX_SASSR2_SASPLIT1_Pos 4
#define MATRIX_SASSR2_SASPLIT1_Msk (0xfu << MATRIX_SASSR2_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT1(value) ((MATRIX_SASSR2_SASPLIT1_Msk & ((value) << MATRIX_SASSR2_SASPLIT1_Pos)))
#define MATRIX_SASSR2_SASPLIT2_Pos 8
#define MATRIX_SASSR2_SASPLIT2_Msk (0xfu << MATRIX_SASSR2_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT2(value) ((MATRIX_SASSR2_SASPLIT2_Msk & ((value) << MATRIX_SASSR2_SASPLIT2_Pos)))
#define MATRIX_SASSR2_SASPLIT3_Pos 12
#define MATRIX_SASSR2_SASPLIT3_Msk (0xfu << MATRIX_SASSR2_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT3(value) ((MATRIX_SASSR2_SASPLIT3_Msk & ((value) << MATRIX_SASSR2_SASPLIT3_Pos)))
#define MATRIX_SASSR2_SASPLIT4_Pos 16
#define MATRIX_SASSR2_SASPLIT4_Msk (0xfu << MATRIX_SASSR2_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT4(value) ((MATRIX_SASSR2_SASPLIT4_Msk & ((value) << MATRIX_SASSR2_SASPLIT4_Pos)))
#define MATRIX_SASSR2_SASPLIT5_Pos 20
#define MATRIX_SASSR2_SASPLIT5_Msk (0xfu << MATRIX_SASSR2_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT5(value) ((MATRIX_SASSR2_SASPLIT5_Msk & ((value) << MATRIX_SASSR2_SASPLIT5_Pos)))
#define MATRIX_SASSR2_SASPLIT6_Pos 24
#define MATRIX_SASSR2_SASPLIT6_Msk (0xfu << MATRIX_SASSR2_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT6(value) ((MATRIX_SASSR2_SASPLIT6_Msk & ((value) << MATRIX_SASSR2_SASPLIT6_Pos)))
#define MATRIX_SASSR2_SASPLIT7_Pos 28
#define MATRIX_SASSR2_SASPLIT7_Msk (0xfu << MATRIX_SASSR2_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR2) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR2_SASPLIT7(value) ((MATRIX_SASSR2_SASPLIT7_Msk & ((value) << MATRIX_SASSR2_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR3 : (MATRIX Offset: 0x024C) Security Areas Split Slave 3 Register -------- */
#define MATRIX_SASSR3_SASPLIT0_Pos 0
#define MATRIX_SASSR3_SASPLIT0_Msk (0xfu << MATRIX_SASSR3_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT0(value) ((MATRIX_SASSR3_SASPLIT0_Msk & ((value) << MATRIX_SASSR3_SASPLIT0_Pos)))
#define MATRIX_SASSR3_SASPLIT1_Pos 4
#define MATRIX_SASSR3_SASPLIT1_Msk (0xfu << MATRIX_SASSR3_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT1(value) ((MATRIX_SASSR3_SASPLIT1_Msk & ((value) << MATRIX_SASSR3_SASPLIT1_Pos)))
#define MATRIX_SASSR3_SASPLIT2_Pos 8
#define MATRIX_SASSR3_SASPLIT2_Msk (0xfu << MATRIX_SASSR3_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT2(value) ((MATRIX_SASSR3_SASPLIT2_Msk & ((value) << MATRIX_SASSR3_SASPLIT2_Pos)))
#define MATRIX_SASSR3_SASPLIT3_Pos 12
#define MATRIX_SASSR3_SASPLIT3_Msk (0xfu << MATRIX_SASSR3_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT3(value) ((MATRIX_SASSR3_SASPLIT3_Msk & ((value) << MATRIX_SASSR3_SASPLIT3_Pos)))
#define MATRIX_SASSR3_SASPLIT4_Pos 16
#define MATRIX_SASSR3_SASPLIT4_Msk (0xfu << MATRIX_SASSR3_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT4(value) ((MATRIX_SASSR3_SASPLIT4_Msk & ((value) << MATRIX_SASSR3_SASPLIT4_Pos)))
#define MATRIX_SASSR3_SASPLIT5_Pos 20
#define MATRIX_SASSR3_SASPLIT5_Msk (0xfu << MATRIX_SASSR3_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT5(value) ((MATRIX_SASSR3_SASPLIT5_Msk & ((value) << MATRIX_SASSR3_SASPLIT5_Pos)))
#define MATRIX_SASSR3_SASPLIT6_Pos 24
#define MATRIX_SASSR3_SASPLIT6_Msk (0xfu << MATRIX_SASSR3_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT6(value) ((MATRIX_SASSR3_SASPLIT6_Msk & ((value) << MATRIX_SASSR3_SASPLIT6_Pos)))
#define MATRIX_SASSR3_SASPLIT7_Pos 28
#define MATRIX_SASSR3_SASPLIT7_Msk (0xfu << MATRIX_SASSR3_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR3) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR3_SASPLIT7(value) ((MATRIX_SASSR3_SASPLIT7_Msk & ((value) << MATRIX_SASSR3_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR4 : (MATRIX Offset: 0x0250) Security Areas Split Slave 4 Register -------- */
#define MATRIX_SASSR4_SASPLIT0_Pos 0
#define MATRIX_SASSR4_SASPLIT0_Msk (0xfu << MATRIX_SASSR4_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT0(value) ((MATRIX_SASSR4_SASPLIT0_Msk & ((value) << MATRIX_SASSR4_SASPLIT0_Pos)))
#define MATRIX_SASSR4_SASPLIT1_Pos 4
#define MATRIX_SASSR4_SASPLIT1_Msk (0xfu << MATRIX_SASSR4_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT1(value) ((MATRIX_SASSR4_SASPLIT1_Msk & ((value) << MATRIX_SASSR4_SASPLIT1_Pos)))
#define MATRIX_SASSR4_SASPLIT2_Pos 8
#define MATRIX_SASSR4_SASPLIT2_Msk (0xfu << MATRIX_SASSR4_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT2(value) ((MATRIX_SASSR4_SASPLIT2_Msk & ((value) << MATRIX_SASSR4_SASPLIT2_Pos)))
#define MATRIX_SASSR4_SASPLIT3_Pos 12
#define MATRIX_SASSR4_SASPLIT3_Msk (0xfu << MATRIX_SASSR4_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT3(value) ((MATRIX_SASSR4_SASPLIT3_Msk & ((value) << MATRIX_SASSR4_SASPLIT3_Pos)))
#define MATRIX_SASSR4_SASPLIT4_Pos 16
#define MATRIX_SASSR4_SASPLIT4_Msk (0xfu << MATRIX_SASSR4_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT4(value) ((MATRIX_SASSR4_SASPLIT4_Msk & ((value) << MATRIX_SASSR4_SASPLIT4_Pos)))
#define MATRIX_SASSR4_SASPLIT5_Pos 20
#define MATRIX_SASSR4_SASPLIT5_Msk (0xfu << MATRIX_SASSR4_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT5(value) ((MATRIX_SASSR4_SASPLIT5_Msk & ((value) << MATRIX_SASSR4_SASPLIT5_Pos)))
#define MATRIX_SASSR4_SASPLIT6_Pos 24
#define MATRIX_SASSR4_SASPLIT6_Msk (0xfu << MATRIX_SASSR4_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT6(value) ((MATRIX_SASSR4_SASPLIT6_Msk & ((value) << MATRIX_SASSR4_SASPLIT6_Pos)))
#define MATRIX_SASSR4_SASPLIT7_Pos 28
#define MATRIX_SASSR4_SASPLIT7_Msk (0xfu << MATRIX_SASSR4_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR4) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR4_SASPLIT7(value) ((MATRIX_SASSR4_SASPLIT7_Msk & ((value) << MATRIX_SASSR4_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR5 : (MATRIX Offset: 0x0254) Security Areas Split Slave 5 Register -------- */
#define MATRIX_SASSR5_SASPLIT0_Pos 0
#define MATRIX_SASSR5_SASPLIT0_Msk (0xfu << MATRIX_SASSR5_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT0(value) ((MATRIX_SASSR5_SASPLIT0_Msk & ((value) << MATRIX_SASSR5_SASPLIT0_Pos)))
#define MATRIX_SASSR5_SASPLIT1_Pos 4
#define MATRIX_SASSR5_SASPLIT1_Msk (0xfu << MATRIX_SASSR5_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT1(value) ((MATRIX_SASSR5_SASPLIT1_Msk & ((value) << MATRIX_SASSR5_SASPLIT1_Pos)))
#define MATRIX_SASSR5_SASPLIT2_Pos 8
#define MATRIX_SASSR5_SASPLIT2_Msk (0xfu << MATRIX_SASSR5_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT2(value) ((MATRIX_SASSR5_SASPLIT2_Msk & ((value) << MATRIX_SASSR5_SASPLIT2_Pos)))
#define MATRIX_SASSR5_SASPLIT3_Pos 12
#define MATRIX_SASSR5_SASPLIT3_Msk (0xfu << MATRIX_SASSR5_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT3(value) ((MATRIX_SASSR5_SASPLIT3_Msk & ((value) << MATRIX_SASSR5_SASPLIT3_Pos)))
#define MATRIX_SASSR5_SASPLIT4_Pos 16
#define MATRIX_SASSR5_SASPLIT4_Msk (0xfu << MATRIX_SASSR5_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT4(value) ((MATRIX_SASSR5_SASPLIT4_Msk & ((value) << MATRIX_SASSR5_SASPLIT4_Pos)))
#define MATRIX_SASSR5_SASPLIT5_Pos 20
#define MATRIX_SASSR5_SASPLIT5_Msk (0xfu << MATRIX_SASSR5_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT5(value) ((MATRIX_SASSR5_SASPLIT5_Msk & ((value) << MATRIX_SASSR5_SASPLIT5_Pos)))
#define MATRIX_SASSR5_SASPLIT6_Pos 24
#define MATRIX_SASSR5_SASPLIT6_Msk (0xfu << MATRIX_SASSR5_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT6(value) ((MATRIX_SASSR5_SASPLIT6_Msk & ((value) << MATRIX_SASSR5_SASPLIT6_Pos)))
#define MATRIX_SASSR5_SASPLIT7_Pos 28
#define MATRIX_SASSR5_SASPLIT7_Msk (0xfu << MATRIX_SASSR5_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR5) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR5_SASPLIT7(value) ((MATRIX_SASSR5_SASPLIT7_Msk & ((value) << MATRIX_SASSR5_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR6 : (MATRIX Offset: 0x0258) Security Areas Split Slave 6 Register -------- */
#define MATRIX_SASSR6_SASPLIT0_Pos 0
#define MATRIX_SASSR6_SASPLIT0_Msk (0xfu << MATRIX_SASSR6_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT0(value) ((MATRIX_SASSR6_SASPLIT0_Msk & ((value) << MATRIX_SASSR6_SASPLIT0_Pos)))
#define MATRIX_SASSR6_SASPLIT1_Pos 4
#define MATRIX_SASSR6_SASPLIT1_Msk (0xfu << MATRIX_SASSR6_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT1(value) ((MATRIX_SASSR6_SASPLIT1_Msk & ((value) << MATRIX_SASSR6_SASPLIT1_Pos)))
#define MATRIX_SASSR6_SASPLIT2_Pos 8
#define MATRIX_SASSR6_SASPLIT2_Msk (0xfu << MATRIX_SASSR6_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT2(value) ((MATRIX_SASSR6_SASPLIT2_Msk & ((value) << MATRIX_SASSR6_SASPLIT2_Pos)))
#define MATRIX_SASSR6_SASPLIT3_Pos 12
#define MATRIX_SASSR6_SASPLIT3_Msk (0xfu << MATRIX_SASSR6_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT3(value) ((MATRIX_SASSR6_SASPLIT3_Msk & ((value) << MATRIX_SASSR6_SASPLIT3_Pos)))
#define MATRIX_SASSR6_SASPLIT4_Pos 16
#define MATRIX_SASSR6_SASPLIT4_Msk (0xfu << MATRIX_SASSR6_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT4(value) ((MATRIX_SASSR6_SASPLIT4_Msk & ((value) << MATRIX_SASSR6_SASPLIT4_Pos)))
#define MATRIX_SASSR6_SASPLIT5_Pos 20
#define MATRIX_SASSR6_SASPLIT5_Msk (0xfu << MATRIX_SASSR6_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT5(value) ((MATRIX_SASSR6_SASPLIT5_Msk & ((value) << MATRIX_SASSR6_SASPLIT5_Pos)))
#define MATRIX_SASSR6_SASPLIT6_Pos 24
#define MATRIX_SASSR6_SASPLIT6_Msk (0xfu << MATRIX_SASSR6_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT6(value) ((MATRIX_SASSR6_SASPLIT6_Msk & ((value) << MATRIX_SASSR6_SASPLIT6_Pos)))
#define MATRIX_SASSR6_SASPLIT7_Pos 28
#define MATRIX_SASSR6_SASPLIT7_Msk (0xfu << MATRIX_SASSR6_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR6) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR6_SASPLIT7(value) ((MATRIX_SASSR6_SASPLIT7_Msk & ((value) << MATRIX_SASSR6_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR7 : (MATRIX Offset: 0x025C) Security Areas Split Slave 7 Register -------- */
#define MATRIX_SASSR7_SASPLIT0_Pos 0
#define MATRIX_SASSR7_SASPLIT0_Msk (0xfu << MATRIX_SASSR7_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT0(value) ((MATRIX_SASSR7_SASPLIT0_Msk & ((value) << MATRIX_SASSR7_SASPLIT0_Pos)))
#define MATRIX_SASSR7_SASPLIT1_Pos 4
#define MATRIX_SASSR7_SASPLIT1_Msk (0xfu << MATRIX_SASSR7_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT1(value) ((MATRIX_SASSR7_SASPLIT1_Msk & ((value) << MATRIX_SASSR7_SASPLIT1_Pos)))
#define MATRIX_SASSR7_SASPLIT2_Pos 8
#define MATRIX_SASSR7_SASPLIT2_Msk (0xfu << MATRIX_SASSR7_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT2(value) ((MATRIX_SASSR7_SASPLIT2_Msk & ((value) << MATRIX_SASSR7_SASPLIT2_Pos)))
#define MATRIX_SASSR7_SASPLIT3_Pos 12
#define MATRIX_SASSR7_SASPLIT3_Msk (0xfu << MATRIX_SASSR7_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT3(value) ((MATRIX_SASSR7_SASPLIT3_Msk & ((value) << MATRIX_SASSR7_SASPLIT3_Pos)))
#define MATRIX_SASSR7_SASPLIT4_Pos 16
#define MATRIX_SASSR7_SASPLIT4_Msk (0xfu << MATRIX_SASSR7_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT4(value) ((MATRIX_SASSR7_SASPLIT4_Msk & ((value) << MATRIX_SASSR7_SASPLIT4_Pos)))
#define MATRIX_SASSR7_SASPLIT5_Pos 20
#define MATRIX_SASSR7_SASPLIT5_Msk (0xfu << MATRIX_SASSR7_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT5(value) ((MATRIX_SASSR7_SASPLIT5_Msk & ((value) << MATRIX_SASSR7_SASPLIT5_Pos)))
#define MATRIX_SASSR7_SASPLIT6_Pos 24
#define MATRIX_SASSR7_SASPLIT6_Msk (0xfu << MATRIX_SASSR7_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT6(value) ((MATRIX_SASSR7_SASPLIT6_Msk & ((value) << MATRIX_SASSR7_SASPLIT6_Pos)))
#define MATRIX_SASSR7_SASPLIT7_Pos 28
#define MATRIX_SASSR7_SASPLIT7_Msk (0xfu << MATRIX_SASSR7_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR7) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR7_SASPLIT7(value) ((MATRIX_SASSR7_SASPLIT7_Msk & ((value) << MATRIX_SASSR7_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR8 : (MATRIX Offset: 0x0260) Security Areas Split Slave 8 Register -------- */
#define MATRIX_SASSR8_SASPLIT0_Pos 0
#define MATRIX_SASSR8_SASPLIT0_Msk (0xfu << MATRIX_SASSR8_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT0(value) ((MATRIX_SASSR8_SASPLIT0_Msk & ((value) << MATRIX_SASSR8_SASPLIT0_Pos)))
#define MATRIX_SASSR8_SASPLIT1_Pos 4
#define MATRIX_SASSR8_SASPLIT1_Msk (0xfu << MATRIX_SASSR8_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT1(value) ((MATRIX_SASSR8_SASPLIT1_Msk & ((value) << MATRIX_SASSR8_SASPLIT1_Pos)))
#define MATRIX_SASSR8_SASPLIT2_Pos 8
#define MATRIX_SASSR8_SASPLIT2_Msk (0xfu << MATRIX_SASSR8_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT2(value) ((MATRIX_SASSR8_SASPLIT2_Msk & ((value) << MATRIX_SASSR8_SASPLIT2_Pos)))
#define MATRIX_SASSR8_SASPLIT3_Pos 12
#define MATRIX_SASSR8_SASPLIT3_Msk (0xfu << MATRIX_SASSR8_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT3(value) ((MATRIX_SASSR8_SASPLIT3_Msk & ((value) << MATRIX_SASSR8_SASPLIT3_Pos)))
#define MATRIX_SASSR8_SASPLIT4_Pos 16
#define MATRIX_SASSR8_SASPLIT4_Msk (0xfu << MATRIX_SASSR8_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT4(value) ((MATRIX_SASSR8_SASPLIT4_Msk & ((value) << MATRIX_SASSR8_SASPLIT4_Pos)))
#define MATRIX_SASSR8_SASPLIT5_Pos 20
#define MATRIX_SASSR8_SASPLIT5_Msk (0xfu << MATRIX_SASSR8_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT5(value) ((MATRIX_SASSR8_SASPLIT5_Msk & ((value) << MATRIX_SASSR8_SASPLIT5_Pos)))
#define MATRIX_SASSR8_SASPLIT6_Pos 24
#define MATRIX_SASSR8_SASPLIT6_Msk (0xfu << MATRIX_SASSR8_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT6(value) ((MATRIX_SASSR8_SASPLIT6_Msk & ((value) << MATRIX_SASSR8_SASPLIT6_Pos)))
#define MATRIX_SASSR8_SASPLIT7_Pos 28
#define MATRIX_SASSR8_SASPLIT7_Msk (0xfu << MATRIX_SASSR8_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR8) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR8_SASPLIT7(value) ((MATRIX_SASSR8_SASPLIT7_Msk & ((value) << MATRIX_SASSR8_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR9 : (MATRIX Offset: 0x0264) Security Areas Split Slave 9 Register -------- */
#define MATRIX_SASSR9_SASPLIT0_Pos 0
#define MATRIX_SASSR9_SASPLIT0_Msk (0xfu << MATRIX_SASSR9_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT0(value) ((MATRIX_SASSR9_SASPLIT0_Msk & ((value) << MATRIX_SASSR9_SASPLIT0_Pos)))
#define MATRIX_SASSR9_SASPLIT1_Pos 4
#define MATRIX_SASSR9_SASPLIT1_Msk (0xfu << MATRIX_SASSR9_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT1(value) ((MATRIX_SASSR9_SASPLIT1_Msk & ((value) << MATRIX_SASSR9_SASPLIT1_Pos)))
#define MATRIX_SASSR9_SASPLIT2_Pos 8
#define MATRIX_SASSR9_SASPLIT2_Msk (0xfu << MATRIX_SASSR9_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT2(value) ((MATRIX_SASSR9_SASPLIT2_Msk & ((value) << MATRIX_SASSR9_SASPLIT2_Pos)))
#define MATRIX_SASSR9_SASPLIT3_Pos 12
#define MATRIX_SASSR9_SASPLIT3_Msk (0xfu << MATRIX_SASSR9_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT3(value) ((MATRIX_SASSR9_SASPLIT3_Msk & ((value) << MATRIX_SASSR9_SASPLIT3_Pos)))
#define MATRIX_SASSR9_SASPLIT4_Pos 16
#define MATRIX_SASSR9_SASPLIT4_Msk (0xfu << MATRIX_SASSR9_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT4(value) ((MATRIX_SASSR9_SASPLIT4_Msk & ((value) << MATRIX_SASSR9_SASPLIT4_Pos)))
#define MATRIX_SASSR9_SASPLIT5_Pos 20
#define MATRIX_SASSR9_SASPLIT5_Msk (0xfu << MATRIX_SASSR9_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT5(value) ((MATRIX_SASSR9_SASPLIT5_Msk & ((value) << MATRIX_SASSR9_SASPLIT5_Pos)))
#define MATRIX_SASSR9_SASPLIT6_Pos 24
#define MATRIX_SASSR9_SASPLIT6_Msk (0xfu << MATRIX_SASSR9_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT6(value) ((MATRIX_SASSR9_SASPLIT6_Msk & ((value) << MATRIX_SASSR9_SASPLIT6_Pos)))
#define MATRIX_SASSR9_SASPLIT7_Pos 28
#define MATRIX_SASSR9_SASPLIT7_Msk (0xfu << MATRIX_SASSR9_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR9) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR9_SASPLIT7(value) ((MATRIX_SASSR9_SASPLIT7_Msk & ((value) << MATRIX_SASSR9_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR10 : (MATRIX Offset: 0x0268) Security Areas Split Slave 10 Register -------- */
#define MATRIX_SASSR10_SASPLIT0_Pos 0
#define MATRIX_SASSR10_SASPLIT0_Msk (0xfu << MATRIX_SASSR10_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT0(value) ((MATRIX_SASSR10_SASPLIT0_Msk & ((value) << MATRIX_SASSR10_SASPLIT0_Pos)))
#define MATRIX_SASSR10_SASPLIT1_Pos 4
#define MATRIX_SASSR10_SASPLIT1_Msk (0xfu << MATRIX_SASSR10_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT1(value) ((MATRIX_SASSR10_SASPLIT1_Msk & ((value) << MATRIX_SASSR10_SASPLIT1_Pos)))
#define MATRIX_SASSR10_SASPLIT2_Pos 8
#define MATRIX_SASSR10_SASPLIT2_Msk (0xfu << MATRIX_SASSR10_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT2(value) ((MATRIX_SASSR10_SASPLIT2_Msk & ((value) << MATRIX_SASSR10_SASPLIT2_Pos)))
#define MATRIX_SASSR10_SASPLIT3_Pos 12
#define MATRIX_SASSR10_SASPLIT3_Msk (0xfu << MATRIX_SASSR10_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT3(value) ((MATRIX_SASSR10_SASPLIT3_Msk & ((value) << MATRIX_SASSR10_SASPLIT3_Pos)))
#define MATRIX_SASSR10_SASPLIT4_Pos 16
#define MATRIX_SASSR10_SASPLIT4_Msk (0xfu << MATRIX_SASSR10_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT4(value) ((MATRIX_SASSR10_SASPLIT4_Msk & ((value) << MATRIX_SASSR10_SASPLIT4_Pos)))
#define MATRIX_SASSR10_SASPLIT5_Pos 20
#define MATRIX_SASSR10_SASPLIT5_Msk (0xfu << MATRIX_SASSR10_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT5(value) ((MATRIX_SASSR10_SASPLIT5_Msk & ((value) << MATRIX_SASSR10_SASPLIT5_Pos)))
#define MATRIX_SASSR10_SASPLIT6_Pos 24
#define MATRIX_SASSR10_SASPLIT6_Msk (0xfu << MATRIX_SASSR10_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT6(value) ((MATRIX_SASSR10_SASPLIT6_Msk & ((value) << MATRIX_SASSR10_SASPLIT6_Pos)))
#define MATRIX_SASSR10_SASPLIT7_Pos 28
#define MATRIX_SASSR10_SASPLIT7_Msk (0xfu << MATRIX_SASSR10_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR10) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR10_SASPLIT7(value) ((MATRIX_SASSR10_SASPLIT7_Msk & ((value) << MATRIX_SASSR10_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR11 : (MATRIX Offset: 0x026C) Security Areas Split Slave 11 Register -------- */
#define MATRIX_SASSR11_SASPLIT0_Pos 0
#define MATRIX_SASSR11_SASPLIT0_Msk (0xfu << MATRIX_SASSR11_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT0(value) ((MATRIX_SASSR11_SASPLIT0_Msk & ((value) << MATRIX_SASSR11_SASPLIT0_Pos)))
#define MATRIX_SASSR11_SASPLIT1_Pos 4
#define MATRIX_SASSR11_SASPLIT1_Msk (0xfu << MATRIX_SASSR11_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT1(value) ((MATRIX_SASSR11_SASPLIT1_Msk & ((value) << MATRIX_SASSR11_SASPLIT1_Pos)))
#define MATRIX_SASSR11_SASPLIT2_Pos 8
#define MATRIX_SASSR11_SASPLIT2_Msk (0xfu << MATRIX_SASSR11_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT2(value) ((MATRIX_SASSR11_SASPLIT2_Msk & ((value) << MATRIX_SASSR11_SASPLIT2_Pos)))
#define MATRIX_SASSR11_SASPLIT3_Pos 12
#define MATRIX_SASSR11_SASPLIT3_Msk (0xfu << MATRIX_SASSR11_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT3(value) ((MATRIX_SASSR11_SASPLIT3_Msk & ((value) << MATRIX_SASSR11_SASPLIT3_Pos)))
#define MATRIX_SASSR11_SASPLIT4_Pos 16
#define MATRIX_SASSR11_SASPLIT4_Msk (0xfu << MATRIX_SASSR11_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT4(value) ((MATRIX_SASSR11_SASPLIT4_Msk & ((value) << MATRIX_SASSR11_SASPLIT4_Pos)))
#define MATRIX_SASSR11_SASPLIT5_Pos 20
#define MATRIX_SASSR11_SASPLIT5_Msk (0xfu << MATRIX_SASSR11_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT5(value) ((MATRIX_SASSR11_SASPLIT5_Msk & ((value) << MATRIX_SASSR11_SASPLIT5_Pos)))
#define MATRIX_SASSR11_SASPLIT6_Pos 24
#define MATRIX_SASSR11_SASPLIT6_Msk (0xfu << MATRIX_SASSR11_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT6(value) ((MATRIX_SASSR11_SASPLIT6_Msk & ((value) << MATRIX_SASSR11_SASPLIT6_Pos)))
#define MATRIX_SASSR11_SASPLIT7_Pos 28
#define MATRIX_SASSR11_SASPLIT7_Msk (0xfu << MATRIX_SASSR11_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR11) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR11_SASPLIT7(value) ((MATRIX_SASSR11_SASPLIT7_Msk & ((value) << MATRIX_SASSR11_SASPLIT7_Pos)))
/* -------- MATRIX_SASSR12 : (MATRIX Offset: 0x0270) Security Areas Split Slave 12 Register -------- */
#define MATRIX_SASSR12_SASPLIT0_Pos 0
#define MATRIX_SASSR12_SASPLIT0_Msk (0xfu << MATRIX_SASSR12_SASPLIT0_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT0(value) ((MATRIX_SASSR12_SASPLIT0_Msk & ((value) << MATRIX_SASSR12_SASPLIT0_Pos)))
#define MATRIX_SASSR12_SASPLIT1_Pos 4
#define MATRIX_SASSR12_SASPLIT1_Msk (0xfu << MATRIX_SASSR12_SASPLIT1_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT1(value) ((MATRIX_SASSR12_SASPLIT1_Msk & ((value) << MATRIX_SASSR12_SASPLIT1_Pos)))
#define MATRIX_SASSR12_SASPLIT2_Pos 8
#define MATRIX_SASSR12_SASPLIT2_Msk (0xfu << MATRIX_SASSR12_SASPLIT2_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT2(value) ((MATRIX_SASSR12_SASPLIT2_Msk & ((value) << MATRIX_SASSR12_SASPLIT2_Pos)))
#define MATRIX_SASSR12_SASPLIT3_Pos 12
#define MATRIX_SASSR12_SASPLIT3_Msk (0xfu << MATRIX_SASSR12_SASPLIT3_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT3(value) ((MATRIX_SASSR12_SASPLIT3_Msk & ((value) << MATRIX_SASSR12_SASPLIT3_Pos)))
#define MATRIX_SASSR12_SASPLIT4_Pos 16
#define MATRIX_SASSR12_SASPLIT4_Msk (0xfu << MATRIX_SASSR12_SASPLIT4_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT4(value) ((MATRIX_SASSR12_SASPLIT4_Msk & ((value) << MATRIX_SASSR12_SASPLIT4_Pos)))
#define MATRIX_SASSR12_SASPLIT5_Pos 20
#define MATRIX_SASSR12_SASPLIT5_Msk (0xfu << MATRIX_SASSR12_SASPLIT5_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT5(value) ((MATRIX_SASSR12_SASPLIT5_Msk & ((value) << MATRIX_SASSR12_SASPLIT5_Pos)))
#define MATRIX_SASSR12_SASPLIT6_Pos 24
#define MATRIX_SASSR12_SASPLIT6_Msk (0xfu << MATRIX_SASSR12_SASPLIT6_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT6(value) ((MATRIX_SASSR12_SASPLIT6_Msk & ((value) << MATRIX_SASSR12_SASPLIT6_Pos)))
#define MATRIX_SASSR12_SASPLIT7_Pos 28
#define MATRIX_SASSR12_SASPLIT7_Msk (0xfu << MATRIX_SASSR12_SASPLIT7_Pos) /**< \brief (MATRIX_SASSR12) Security Areas Split for HSELx Security Region */
#define MATRIX_SASSR12_SASPLIT7(value) ((MATRIX_SASSR12_SASPLIT7_Msk & ((value) << MATRIX_SASSR12_SASPLIT7_Pos)))
/* -------- MATRIX_SRTSR1 : (MATRIX Offset: 0x0284) Security Region Top Slave 1 Register -------- */
#define MATRIX_SRTSR1_SRTOP0_Pos 0
#define MATRIX_SRTSR1_SRTOP0_Msk (0xfu << MATRIX_SRTSR1_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP0(value) ((MATRIX_SRTSR1_SRTOP0_Msk & ((value) << MATRIX_SRTSR1_SRTOP0_Pos)))
#define MATRIX_SRTSR1_SRTOP1_Pos 4
#define MATRIX_SRTSR1_SRTOP1_Msk (0xfu << MATRIX_SRTSR1_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP1(value) ((MATRIX_SRTSR1_SRTOP1_Msk & ((value) << MATRIX_SRTSR1_SRTOP1_Pos)))
#define MATRIX_SRTSR1_SRTOP2_Pos 8
#define MATRIX_SRTSR1_SRTOP2_Msk (0xfu << MATRIX_SRTSR1_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP2(value) ((MATRIX_SRTSR1_SRTOP2_Msk & ((value) << MATRIX_SRTSR1_SRTOP2_Pos)))
#define MATRIX_SRTSR1_SRTOP3_Pos 12
#define MATRIX_SRTSR1_SRTOP3_Msk (0xfu << MATRIX_SRTSR1_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP3(value) ((MATRIX_SRTSR1_SRTOP3_Msk & ((value) << MATRIX_SRTSR1_SRTOP3_Pos)))
#define MATRIX_SRTSR1_SRTOP4_Pos 16
#define MATRIX_SRTSR1_SRTOP4_Msk (0xfu << MATRIX_SRTSR1_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP4(value) ((MATRIX_SRTSR1_SRTOP4_Msk & ((value) << MATRIX_SRTSR1_SRTOP4_Pos)))
#define MATRIX_SRTSR1_SRTOP5_Pos 20
#define MATRIX_SRTSR1_SRTOP5_Msk (0xfu << MATRIX_SRTSR1_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP5(value) ((MATRIX_SRTSR1_SRTOP5_Msk & ((value) << MATRIX_SRTSR1_SRTOP5_Pos)))
#define MATRIX_SRTSR1_SRTOP6_Pos 24
#define MATRIX_SRTSR1_SRTOP6_Msk (0xfu << MATRIX_SRTSR1_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP6(value) ((MATRIX_SRTSR1_SRTOP6_Msk & ((value) << MATRIX_SRTSR1_SRTOP6_Pos)))
#define MATRIX_SRTSR1_SRTOP7_Pos 28
#define MATRIX_SRTSR1_SRTOP7_Msk (0xfu << MATRIX_SRTSR1_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR1) HSELx Security Region Top */
#define MATRIX_SRTSR1_SRTOP7(value) ((MATRIX_SRTSR1_SRTOP7_Msk & ((value) << MATRIX_SRTSR1_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR2 : (MATRIX Offset: 0x0288) Security Region Top Slave 2 Register -------- */
#define MATRIX_SRTSR2_SRTOP0_Pos 0
#define MATRIX_SRTSR2_SRTOP0_Msk (0xfu << MATRIX_SRTSR2_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP0(value) ((MATRIX_SRTSR2_SRTOP0_Msk & ((value) << MATRIX_SRTSR2_SRTOP0_Pos)))
#define MATRIX_SRTSR2_SRTOP1_Pos 4
#define MATRIX_SRTSR2_SRTOP1_Msk (0xfu << MATRIX_SRTSR2_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP1(value) ((MATRIX_SRTSR2_SRTOP1_Msk & ((value) << MATRIX_SRTSR2_SRTOP1_Pos)))
#define MATRIX_SRTSR2_SRTOP2_Pos 8
#define MATRIX_SRTSR2_SRTOP2_Msk (0xfu << MATRIX_SRTSR2_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP2(value) ((MATRIX_SRTSR2_SRTOP2_Msk & ((value) << MATRIX_SRTSR2_SRTOP2_Pos)))
#define MATRIX_SRTSR2_SRTOP3_Pos 12
#define MATRIX_SRTSR2_SRTOP3_Msk (0xfu << MATRIX_SRTSR2_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP3(value) ((MATRIX_SRTSR2_SRTOP3_Msk & ((value) << MATRIX_SRTSR2_SRTOP3_Pos)))
#define MATRIX_SRTSR2_SRTOP4_Pos 16
#define MATRIX_SRTSR2_SRTOP4_Msk (0xfu << MATRIX_SRTSR2_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP4(value) ((MATRIX_SRTSR2_SRTOP4_Msk & ((value) << MATRIX_SRTSR2_SRTOP4_Pos)))
#define MATRIX_SRTSR2_SRTOP5_Pos 20
#define MATRIX_SRTSR2_SRTOP5_Msk (0xfu << MATRIX_SRTSR2_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP5(value) ((MATRIX_SRTSR2_SRTOP5_Msk & ((value) << MATRIX_SRTSR2_SRTOP5_Pos)))
#define MATRIX_SRTSR2_SRTOP6_Pos 24
#define MATRIX_SRTSR2_SRTOP6_Msk (0xfu << MATRIX_SRTSR2_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP6(value) ((MATRIX_SRTSR2_SRTOP6_Msk & ((value) << MATRIX_SRTSR2_SRTOP6_Pos)))
#define MATRIX_SRTSR2_SRTOP7_Pos 28
#define MATRIX_SRTSR2_SRTOP7_Msk (0xfu << MATRIX_SRTSR2_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR2) HSELx Security Region Top */
#define MATRIX_SRTSR2_SRTOP7(value) ((MATRIX_SRTSR2_SRTOP7_Msk & ((value) << MATRIX_SRTSR2_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR3 : (MATRIX Offset: 0x028C) Security Region Top Slave 3 Register -------- */
#define MATRIX_SRTSR3_SRTOP0_Pos 0
#define MATRIX_SRTSR3_SRTOP0_Msk (0xfu << MATRIX_SRTSR3_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP0(value) ((MATRIX_SRTSR3_SRTOP0_Msk & ((value) << MATRIX_SRTSR3_SRTOP0_Pos)))
#define MATRIX_SRTSR3_SRTOP1_Pos 4
#define MATRIX_SRTSR3_SRTOP1_Msk (0xfu << MATRIX_SRTSR3_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP1(value) ((MATRIX_SRTSR3_SRTOP1_Msk & ((value) << MATRIX_SRTSR3_SRTOP1_Pos)))
#define MATRIX_SRTSR3_SRTOP2_Pos 8
#define MATRIX_SRTSR3_SRTOP2_Msk (0xfu << MATRIX_SRTSR3_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP2(value) ((MATRIX_SRTSR3_SRTOP2_Msk & ((value) << MATRIX_SRTSR3_SRTOP2_Pos)))
#define MATRIX_SRTSR3_SRTOP3_Pos 12
#define MATRIX_SRTSR3_SRTOP3_Msk (0xfu << MATRIX_SRTSR3_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP3(value) ((MATRIX_SRTSR3_SRTOP3_Msk & ((value) << MATRIX_SRTSR3_SRTOP3_Pos)))
#define MATRIX_SRTSR3_SRTOP4_Pos 16
#define MATRIX_SRTSR3_SRTOP4_Msk (0xfu << MATRIX_SRTSR3_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP4(value) ((MATRIX_SRTSR3_SRTOP4_Msk & ((value) << MATRIX_SRTSR3_SRTOP4_Pos)))
#define MATRIX_SRTSR3_SRTOP5_Pos 20
#define MATRIX_SRTSR3_SRTOP5_Msk (0xfu << MATRIX_SRTSR3_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP5(value) ((MATRIX_SRTSR3_SRTOP5_Msk & ((value) << MATRIX_SRTSR3_SRTOP5_Pos)))
#define MATRIX_SRTSR3_SRTOP6_Pos 24
#define MATRIX_SRTSR3_SRTOP6_Msk (0xfu << MATRIX_SRTSR3_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP6(value) ((MATRIX_SRTSR3_SRTOP6_Msk & ((value) << MATRIX_SRTSR3_SRTOP6_Pos)))
#define MATRIX_SRTSR3_SRTOP7_Pos 28
#define MATRIX_SRTSR3_SRTOP7_Msk (0xfu << MATRIX_SRTSR3_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR3) HSELx Security Region Top */
#define MATRIX_SRTSR3_SRTOP7(value) ((MATRIX_SRTSR3_SRTOP7_Msk & ((value) << MATRIX_SRTSR3_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR4 : (MATRIX Offset: 0x0290) Security Region Top Slave 4 Register -------- */
#define MATRIX_SRTSR4_SRTOP0_Pos 0
#define MATRIX_SRTSR4_SRTOP0_Msk (0xfu << MATRIX_SRTSR4_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP0(value) ((MATRIX_SRTSR4_SRTOP0_Msk & ((value) << MATRIX_SRTSR4_SRTOP0_Pos)))
#define MATRIX_SRTSR4_SRTOP1_Pos 4
#define MATRIX_SRTSR4_SRTOP1_Msk (0xfu << MATRIX_SRTSR4_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP1(value) ((MATRIX_SRTSR4_SRTOP1_Msk & ((value) << MATRIX_SRTSR4_SRTOP1_Pos)))
#define MATRIX_SRTSR4_SRTOP2_Pos 8
#define MATRIX_SRTSR4_SRTOP2_Msk (0xfu << MATRIX_SRTSR4_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP2(value) ((MATRIX_SRTSR4_SRTOP2_Msk & ((value) << MATRIX_SRTSR4_SRTOP2_Pos)))
#define MATRIX_SRTSR4_SRTOP3_Pos 12
#define MATRIX_SRTSR4_SRTOP3_Msk (0xfu << MATRIX_SRTSR4_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP3(value) ((MATRIX_SRTSR4_SRTOP3_Msk & ((value) << MATRIX_SRTSR4_SRTOP3_Pos)))
#define MATRIX_SRTSR4_SRTOP4_Pos 16
#define MATRIX_SRTSR4_SRTOP4_Msk (0xfu << MATRIX_SRTSR4_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP4(value) ((MATRIX_SRTSR4_SRTOP4_Msk & ((value) << MATRIX_SRTSR4_SRTOP4_Pos)))
#define MATRIX_SRTSR4_SRTOP5_Pos 20
#define MATRIX_SRTSR4_SRTOP5_Msk (0xfu << MATRIX_SRTSR4_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP5(value) ((MATRIX_SRTSR4_SRTOP5_Msk & ((value) << MATRIX_SRTSR4_SRTOP5_Pos)))
#define MATRIX_SRTSR4_SRTOP6_Pos 24
#define MATRIX_SRTSR4_SRTOP6_Msk (0xfu << MATRIX_SRTSR4_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP6(value) ((MATRIX_SRTSR4_SRTOP6_Msk & ((value) << MATRIX_SRTSR4_SRTOP6_Pos)))
#define MATRIX_SRTSR4_SRTOP7_Pos 28
#define MATRIX_SRTSR4_SRTOP7_Msk (0xfu << MATRIX_SRTSR4_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR4) HSELx Security Region Top */
#define MATRIX_SRTSR4_SRTOP7(value) ((MATRIX_SRTSR4_SRTOP7_Msk & ((value) << MATRIX_SRTSR4_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR5 : (MATRIX Offset: 0x0294) Security Region Top Slave 5 Register -------- */
#define MATRIX_SRTSR5_SRTOP0_Pos 0
#define MATRIX_SRTSR5_SRTOP0_Msk (0xfu << MATRIX_SRTSR5_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP0(value) ((MATRIX_SRTSR5_SRTOP0_Msk & ((value) << MATRIX_SRTSR5_SRTOP0_Pos)))
#define MATRIX_SRTSR5_SRTOP1_Pos 4
#define MATRIX_SRTSR5_SRTOP1_Msk (0xfu << MATRIX_SRTSR5_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP1(value) ((MATRIX_SRTSR5_SRTOP1_Msk & ((value) << MATRIX_SRTSR5_SRTOP1_Pos)))
#define MATRIX_SRTSR5_SRTOP2_Pos 8
#define MATRIX_SRTSR5_SRTOP2_Msk (0xfu << MATRIX_SRTSR5_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP2(value) ((MATRIX_SRTSR5_SRTOP2_Msk & ((value) << MATRIX_SRTSR5_SRTOP2_Pos)))
#define MATRIX_SRTSR5_SRTOP3_Pos 12
#define MATRIX_SRTSR5_SRTOP3_Msk (0xfu << MATRIX_SRTSR5_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP3(value) ((MATRIX_SRTSR5_SRTOP3_Msk & ((value) << MATRIX_SRTSR5_SRTOP3_Pos)))
#define MATRIX_SRTSR5_SRTOP4_Pos 16
#define MATRIX_SRTSR5_SRTOP4_Msk (0xfu << MATRIX_SRTSR5_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP4(value) ((MATRIX_SRTSR5_SRTOP4_Msk & ((value) << MATRIX_SRTSR5_SRTOP4_Pos)))
#define MATRIX_SRTSR5_SRTOP5_Pos 20
#define MATRIX_SRTSR5_SRTOP5_Msk (0xfu << MATRIX_SRTSR5_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP5(value) ((MATRIX_SRTSR5_SRTOP5_Msk & ((value) << MATRIX_SRTSR5_SRTOP5_Pos)))
#define MATRIX_SRTSR5_SRTOP6_Pos 24
#define MATRIX_SRTSR5_SRTOP6_Msk (0xfu << MATRIX_SRTSR5_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP6(value) ((MATRIX_SRTSR5_SRTOP6_Msk & ((value) << MATRIX_SRTSR5_SRTOP6_Pos)))
#define MATRIX_SRTSR5_SRTOP7_Pos 28
#define MATRIX_SRTSR5_SRTOP7_Msk (0xfu << MATRIX_SRTSR5_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR5) HSELx Security Region Top */
#define MATRIX_SRTSR5_SRTOP7(value) ((MATRIX_SRTSR5_SRTOP7_Msk & ((value) << MATRIX_SRTSR5_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR6 : (MATRIX Offset: 0x0298) Security Region Top Slave 6 Register -------- */
#define MATRIX_SRTSR6_SRTOP0_Pos 0
#define MATRIX_SRTSR6_SRTOP0_Msk (0xfu << MATRIX_SRTSR6_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP0(value) ((MATRIX_SRTSR6_SRTOP0_Msk & ((value) << MATRIX_SRTSR6_SRTOP0_Pos)))
#define MATRIX_SRTSR6_SRTOP1_Pos 4
#define MATRIX_SRTSR6_SRTOP1_Msk (0xfu << MATRIX_SRTSR6_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP1(value) ((MATRIX_SRTSR6_SRTOP1_Msk & ((value) << MATRIX_SRTSR6_SRTOP1_Pos)))
#define MATRIX_SRTSR6_SRTOP2_Pos 8
#define MATRIX_SRTSR6_SRTOP2_Msk (0xfu << MATRIX_SRTSR6_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP2(value) ((MATRIX_SRTSR6_SRTOP2_Msk & ((value) << MATRIX_SRTSR6_SRTOP2_Pos)))
#define MATRIX_SRTSR6_SRTOP3_Pos 12
#define MATRIX_SRTSR6_SRTOP3_Msk (0xfu << MATRIX_SRTSR6_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP3(value) ((MATRIX_SRTSR6_SRTOP3_Msk & ((value) << MATRIX_SRTSR6_SRTOP3_Pos)))
#define MATRIX_SRTSR6_SRTOP4_Pos 16
#define MATRIX_SRTSR6_SRTOP4_Msk (0xfu << MATRIX_SRTSR6_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP4(value) ((MATRIX_SRTSR6_SRTOP4_Msk & ((value) << MATRIX_SRTSR6_SRTOP4_Pos)))
#define MATRIX_SRTSR6_SRTOP5_Pos 20
#define MATRIX_SRTSR6_SRTOP5_Msk (0xfu << MATRIX_SRTSR6_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP5(value) ((MATRIX_SRTSR6_SRTOP5_Msk & ((value) << MATRIX_SRTSR6_SRTOP5_Pos)))
#define MATRIX_SRTSR6_SRTOP6_Pos 24
#define MATRIX_SRTSR6_SRTOP6_Msk (0xfu << MATRIX_SRTSR6_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP6(value) ((MATRIX_SRTSR6_SRTOP6_Msk & ((value) << MATRIX_SRTSR6_SRTOP6_Pos)))
#define MATRIX_SRTSR6_SRTOP7_Pos 28
#define MATRIX_SRTSR6_SRTOP7_Msk (0xfu << MATRIX_SRTSR6_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR6) HSELx Security Region Top */
#define MATRIX_SRTSR6_SRTOP7(value) ((MATRIX_SRTSR6_SRTOP7_Msk & ((value) << MATRIX_SRTSR6_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR7 : (MATRIX Offset: 0x029C) Security Region Top Slave 7 Register -------- */
#define MATRIX_SRTSR7_SRTOP0_Pos 0
#define MATRIX_SRTSR7_SRTOP0_Msk (0xfu << MATRIX_SRTSR7_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP0(value) ((MATRIX_SRTSR7_SRTOP0_Msk & ((value) << MATRIX_SRTSR7_SRTOP0_Pos)))
#define MATRIX_SRTSR7_SRTOP1_Pos 4
#define MATRIX_SRTSR7_SRTOP1_Msk (0xfu << MATRIX_SRTSR7_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP1(value) ((MATRIX_SRTSR7_SRTOP1_Msk & ((value) << MATRIX_SRTSR7_SRTOP1_Pos)))
#define MATRIX_SRTSR7_SRTOP2_Pos 8
#define MATRIX_SRTSR7_SRTOP2_Msk (0xfu << MATRIX_SRTSR7_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP2(value) ((MATRIX_SRTSR7_SRTOP2_Msk & ((value) << MATRIX_SRTSR7_SRTOP2_Pos)))
#define MATRIX_SRTSR7_SRTOP3_Pos 12
#define MATRIX_SRTSR7_SRTOP3_Msk (0xfu << MATRIX_SRTSR7_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP3(value) ((MATRIX_SRTSR7_SRTOP3_Msk & ((value) << MATRIX_SRTSR7_SRTOP3_Pos)))
#define MATRIX_SRTSR7_SRTOP4_Pos 16
#define MATRIX_SRTSR7_SRTOP4_Msk (0xfu << MATRIX_SRTSR7_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP4(value) ((MATRIX_SRTSR7_SRTOP4_Msk & ((value) << MATRIX_SRTSR7_SRTOP4_Pos)))
#define MATRIX_SRTSR7_SRTOP5_Pos 20
#define MATRIX_SRTSR7_SRTOP5_Msk (0xfu << MATRIX_SRTSR7_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP5(value) ((MATRIX_SRTSR7_SRTOP5_Msk & ((value) << MATRIX_SRTSR7_SRTOP5_Pos)))
#define MATRIX_SRTSR7_SRTOP6_Pos 24
#define MATRIX_SRTSR7_SRTOP6_Msk (0xfu << MATRIX_SRTSR7_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP6(value) ((MATRIX_SRTSR7_SRTOP6_Msk & ((value) << MATRIX_SRTSR7_SRTOP6_Pos)))
#define MATRIX_SRTSR7_SRTOP7_Pos 28
#define MATRIX_SRTSR7_SRTOP7_Msk (0xfu << MATRIX_SRTSR7_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR7) HSELx Security Region Top */
#define MATRIX_SRTSR7_SRTOP7(value) ((MATRIX_SRTSR7_SRTOP7_Msk & ((value) << MATRIX_SRTSR7_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR8 : (MATRIX Offset: 0x02A0) Security Region Top Slave 8 Register -------- */
#define MATRIX_SRTSR8_SRTOP0_Pos 0
#define MATRIX_SRTSR8_SRTOP0_Msk (0xfu << MATRIX_SRTSR8_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP0(value) ((MATRIX_SRTSR8_SRTOP0_Msk & ((value) << MATRIX_SRTSR8_SRTOP0_Pos)))
#define MATRIX_SRTSR8_SRTOP1_Pos 4
#define MATRIX_SRTSR8_SRTOP1_Msk (0xfu << MATRIX_SRTSR8_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP1(value) ((MATRIX_SRTSR8_SRTOP1_Msk & ((value) << MATRIX_SRTSR8_SRTOP1_Pos)))
#define MATRIX_SRTSR8_SRTOP2_Pos 8
#define MATRIX_SRTSR8_SRTOP2_Msk (0xfu << MATRIX_SRTSR8_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP2(value) ((MATRIX_SRTSR8_SRTOP2_Msk & ((value) << MATRIX_SRTSR8_SRTOP2_Pos)))
#define MATRIX_SRTSR8_SRTOP3_Pos 12
#define MATRIX_SRTSR8_SRTOP3_Msk (0xfu << MATRIX_SRTSR8_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP3(value) ((MATRIX_SRTSR8_SRTOP3_Msk & ((value) << MATRIX_SRTSR8_SRTOP3_Pos)))
#define MATRIX_SRTSR8_SRTOP4_Pos 16
#define MATRIX_SRTSR8_SRTOP4_Msk (0xfu << MATRIX_SRTSR8_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP4(value) ((MATRIX_SRTSR8_SRTOP4_Msk & ((value) << MATRIX_SRTSR8_SRTOP4_Pos)))
#define MATRIX_SRTSR8_SRTOP5_Pos 20
#define MATRIX_SRTSR8_SRTOP5_Msk (0xfu << MATRIX_SRTSR8_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP5(value) ((MATRIX_SRTSR8_SRTOP5_Msk & ((value) << MATRIX_SRTSR8_SRTOP5_Pos)))
#define MATRIX_SRTSR8_SRTOP6_Pos 24
#define MATRIX_SRTSR8_SRTOP6_Msk (0xfu << MATRIX_SRTSR8_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP6(value) ((MATRIX_SRTSR8_SRTOP6_Msk & ((value) << MATRIX_SRTSR8_SRTOP6_Pos)))
#define MATRIX_SRTSR8_SRTOP7_Pos 28
#define MATRIX_SRTSR8_SRTOP7_Msk (0xfu << MATRIX_SRTSR8_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR8) HSELx Security Region Top */
#define MATRIX_SRTSR8_SRTOP7(value) ((MATRIX_SRTSR8_SRTOP7_Msk & ((value) << MATRIX_SRTSR8_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR9 : (MATRIX Offset: 0x02A4) Security Region Top Slave 9 Register -------- */
#define MATRIX_SRTSR9_SRTOP0_Pos 0
#define MATRIX_SRTSR9_SRTOP0_Msk (0xfu << MATRIX_SRTSR9_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP0(value) ((MATRIX_SRTSR9_SRTOP0_Msk & ((value) << MATRIX_SRTSR9_SRTOP0_Pos)))
#define MATRIX_SRTSR9_SRTOP1_Pos 4
#define MATRIX_SRTSR9_SRTOP1_Msk (0xfu << MATRIX_SRTSR9_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP1(value) ((MATRIX_SRTSR9_SRTOP1_Msk & ((value) << MATRIX_SRTSR9_SRTOP1_Pos)))
#define MATRIX_SRTSR9_SRTOP2_Pos 8
#define MATRIX_SRTSR9_SRTOP2_Msk (0xfu << MATRIX_SRTSR9_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP2(value) ((MATRIX_SRTSR9_SRTOP2_Msk & ((value) << MATRIX_SRTSR9_SRTOP2_Pos)))
#define MATRIX_SRTSR9_SRTOP3_Pos 12
#define MATRIX_SRTSR9_SRTOP3_Msk (0xfu << MATRIX_SRTSR9_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP3(value) ((MATRIX_SRTSR9_SRTOP3_Msk & ((value) << MATRIX_SRTSR9_SRTOP3_Pos)))
#define MATRIX_SRTSR9_SRTOP4_Pos 16
#define MATRIX_SRTSR9_SRTOP4_Msk (0xfu << MATRIX_SRTSR9_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP4(value) ((MATRIX_SRTSR9_SRTOP4_Msk & ((value) << MATRIX_SRTSR9_SRTOP4_Pos)))
#define MATRIX_SRTSR9_SRTOP5_Pos 20
#define MATRIX_SRTSR9_SRTOP5_Msk (0xfu << MATRIX_SRTSR9_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP5(value) ((MATRIX_SRTSR9_SRTOP5_Msk & ((value) << MATRIX_SRTSR9_SRTOP5_Pos)))
#define MATRIX_SRTSR9_SRTOP6_Pos 24
#define MATRIX_SRTSR9_SRTOP6_Msk (0xfu << MATRIX_SRTSR9_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP6(value) ((MATRIX_SRTSR9_SRTOP6_Msk & ((value) << MATRIX_SRTSR9_SRTOP6_Pos)))
#define MATRIX_SRTSR9_SRTOP7_Pos 28
#define MATRIX_SRTSR9_SRTOP7_Msk (0xfu << MATRIX_SRTSR9_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR9) HSELx Security Region Top */
#define MATRIX_SRTSR9_SRTOP7(value) ((MATRIX_SRTSR9_SRTOP7_Msk & ((value) << MATRIX_SRTSR9_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR10 : (MATRIX Offset: 0x02A8) Security Region Top Slave 10 Register -------- */
#define MATRIX_SRTSR10_SRTOP0_Pos 0
#define MATRIX_SRTSR10_SRTOP0_Msk (0xfu << MATRIX_SRTSR10_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP0(value) ((MATRIX_SRTSR10_SRTOP0_Msk & ((value) << MATRIX_SRTSR10_SRTOP0_Pos)))
#define MATRIX_SRTSR10_SRTOP1_Pos 4
#define MATRIX_SRTSR10_SRTOP1_Msk (0xfu << MATRIX_SRTSR10_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP1(value) ((MATRIX_SRTSR10_SRTOP1_Msk & ((value) << MATRIX_SRTSR10_SRTOP1_Pos)))
#define MATRIX_SRTSR10_SRTOP2_Pos 8
#define MATRIX_SRTSR10_SRTOP2_Msk (0xfu << MATRIX_SRTSR10_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP2(value) ((MATRIX_SRTSR10_SRTOP2_Msk & ((value) << MATRIX_SRTSR10_SRTOP2_Pos)))
#define MATRIX_SRTSR10_SRTOP3_Pos 12
#define MATRIX_SRTSR10_SRTOP3_Msk (0xfu << MATRIX_SRTSR10_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP3(value) ((MATRIX_SRTSR10_SRTOP3_Msk & ((value) << MATRIX_SRTSR10_SRTOP3_Pos)))
#define MATRIX_SRTSR10_SRTOP4_Pos 16
#define MATRIX_SRTSR10_SRTOP4_Msk (0xfu << MATRIX_SRTSR10_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP4(value) ((MATRIX_SRTSR10_SRTOP4_Msk & ((value) << MATRIX_SRTSR10_SRTOP4_Pos)))
#define MATRIX_SRTSR10_SRTOP5_Pos 20
#define MATRIX_SRTSR10_SRTOP5_Msk (0xfu << MATRIX_SRTSR10_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP5(value) ((MATRIX_SRTSR10_SRTOP5_Msk & ((value) << MATRIX_SRTSR10_SRTOP5_Pos)))
#define MATRIX_SRTSR10_SRTOP6_Pos 24
#define MATRIX_SRTSR10_SRTOP6_Msk (0xfu << MATRIX_SRTSR10_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP6(value) ((MATRIX_SRTSR10_SRTOP6_Msk & ((value) << MATRIX_SRTSR10_SRTOP6_Pos)))
#define MATRIX_SRTSR10_SRTOP7_Pos 28
#define MATRIX_SRTSR10_SRTOP7_Msk (0xfu << MATRIX_SRTSR10_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR10) HSELx Security Region Top */
#define MATRIX_SRTSR10_SRTOP7(value) ((MATRIX_SRTSR10_SRTOP7_Msk & ((value) << MATRIX_SRTSR10_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR11 : (MATRIX Offset: 0x02AC) Security Region Top Slave 11 Register -------- */
#define MATRIX_SRTSR11_SRTOP0_Pos 0
#define MATRIX_SRTSR11_SRTOP0_Msk (0xfu << MATRIX_SRTSR11_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP0(value) ((MATRIX_SRTSR11_SRTOP0_Msk & ((value) << MATRIX_SRTSR11_SRTOP0_Pos)))
#define MATRIX_SRTSR11_SRTOP1_Pos 4
#define MATRIX_SRTSR11_SRTOP1_Msk (0xfu << MATRIX_SRTSR11_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP1(value) ((MATRIX_SRTSR11_SRTOP1_Msk & ((value) << MATRIX_SRTSR11_SRTOP1_Pos)))
#define MATRIX_SRTSR11_SRTOP2_Pos 8
#define MATRIX_SRTSR11_SRTOP2_Msk (0xfu << MATRIX_SRTSR11_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP2(value) ((MATRIX_SRTSR11_SRTOP2_Msk & ((value) << MATRIX_SRTSR11_SRTOP2_Pos)))
#define MATRIX_SRTSR11_SRTOP3_Pos 12
#define MATRIX_SRTSR11_SRTOP3_Msk (0xfu << MATRIX_SRTSR11_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP3(value) ((MATRIX_SRTSR11_SRTOP3_Msk & ((value) << MATRIX_SRTSR11_SRTOP3_Pos)))
#define MATRIX_SRTSR11_SRTOP4_Pos 16
#define MATRIX_SRTSR11_SRTOP4_Msk (0xfu << MATRIX_SRTSR11_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP4(value) ((MATRIX_SRTSR11_SRTOP4_Msk & ((value) << MATRIX_SRTSR11_SRTOP4_Pos)))
#define MATRIX_SRTSR11_SRTOP5_Pos 20
#define MATRIX_SRTSR11_SRTOP5_Msk (0xfu << MATRIX_SRTSR11_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP5(value) ((MATRIX_SRTSR11_SRTOP5_Msk & ((value) << MATRIX_SRTSR11_SRTOP5_Pos)))
#define MATRIX_SRTSR11_SRTOP6_Pos 24
#define MATRIX_SRTSR11_SRTOP6_Msk (0xfu << MATRIX_SRTSR11_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP6(value) ((MATRIX_SRTSR11_SRTOP6_Msk & ((value) << MATRIX_SRTSR11_SRTOP6_Pos)))
#define MATRIX_SRTSR11_SRTOP7_Pos 28
#define MATRIX_SRTSR11_SRTOP7_Msk (0xfu << MATRIX_SRTSR11_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR11) HSELx Security Region Top */
#define MATRIX_SRTSR11_SRTOP7(value) ((MATRIX_SRTSR11_SRTOP7_Msk & ((value) << MATRIX_SRTSR11_SRTOP7_Pos)))
/* -------- MATRIX_SRTSR12 : (MATRIX Offset: 0x02B0) Security Region Top Slave 12 Register -------- */
#define MATRIX_SRTSR12_SRTOP0_Pos 0
#define MATRIX_SRTSR12_SRTOP0_Msk (0xfu << MATRIX_SRTSR12_SRTOP0_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP0(value) ((MATRIX_SRTSR12_SRTOP0_Msk & ((value) << MATRIX_SRTSR12_SRTOP0_Pos)))
#define MATRIX_SRTSR12_SRTOP1_Pos 4
#define MATRIX_SRTSR12_SRTOP1_Msk (0xfu << MATRIX_SRTSR12_SRTOP1_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP1(value) ((MATRIX_SRTSR12_SRTOP1_Msk & ((value) << MATRIX_SRTSR12_SRTOP1_Pos)))
#define MATRIX_SRTSR12_SRTOP2_Pos 8
#define MATRIX_SRTSR12_SRTOP2_Msk (0xfu << MATRIX_SRTSR12_SRTOP2_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP2(value) ((MATRIX_SRTSR12_SRTOP2_Msk & ((value) << MATRIX_SRTSR12_SRTOP2_Pos)))
#define MATRIX_SRTSR12_SRTOP3_Pos 12
#define MATRIX_SRTSR12_SRTOP3_Msk (0xfu << MATRIX_SRTSR12_SRTOP3_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP3(value) ((MATRIX_SRTSR12_SRTOP3_Msk & ((value) << MATRIX_SRTSR12_SRTOP3_Pos)))
#define MATRIX_SRTSR12_SRTOP4_Pos 16
#define MATRIX_SRTSR12_SRTOP4_Msk (0xfu << MATRIX_SRTSR12_SRTOP4_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP4(value) ((MATRIX_SRTSR12_SRTOP4_Msk & ((value) << MATRIX_SRTSR12_SRTOP4_Pos)))
#define MATRIX_SRTSR12_SRTOP5_Pos 20
#define MATRIX_SRTSR12_SRTOP5_Msk (0xfu << MATRIX_SRTSR12_SRTOP5_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP5(value) ((MATRIX_SRTSR12_SRTOP5_Msk & ((value) << MATRIX_SRTSR12_SRTOP5_Pos)))
#define MATRIX_SRTSR12_SRTOP6_Pos 24
#define MATRIX_SRTSR12_SRTOP6_Msk (0xfu << MATRIX_SRTSR12_SRTOP6_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP6(value) ((MATRIX_SRTSR12_SRTOP6_Msk & ((value) << MATRIX_SRTSR12_SRTOP6_Pos)))
#define MATRIX_SRTSR12_SRTOP7_Pos 28
#define MATRIX_SRTSR12_SRTOP7_Msk (0xfu << MATRIX_SRTSR12_SRTOP7_Pos) /**< \brief (MATRIX_SRTSR12) HSELx Security Region Top */
#define MATRIX_SRTSR12_SRTOP7(value) ((MATRIX_SRTSR12_SRTOP7_Msk & ((value) << MATRIX_SRTSR12_SRTOP7_Pos)))
/* -------- MATRIX_SPSELR[3] : (MATRIX Offset: 0x02C0) Security Peripheral Select 1 Register -------- */
#define MATRIX_SPSELR_NSECP0 (0x1u << 0) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP1 (0x1u << 1) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP2 (0x1u << 2) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP3 (0x1u << 3) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP4 (0x1u << 4) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP5 (0x1u << 5) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP6 (0x1u << 6) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP7 (0x1u << 7) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP8 (0x1u << 8) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP9 (0x1u << 9) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP10 (0x1u << 10) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP11 (0x1u << 11) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP12 (0x1u << 12) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP13 (0x1u << 13) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP14 (0x1u << 14) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP15 (0x1u << 15) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP16 (0x1u << 16) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP17 (0x1u << 17) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP18 (0x1u << 18) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP19 (0x1u << 19) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP20 (0x1u << 20) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP21 (0x1u << 21) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP22 (0x1u << 22) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP23 (0x1u << 23) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP24 (0x1u << 24) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP25 (0x1u << 25) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP26 (0x1u << 26) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP27 (0x1u << 27) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP28 (0x1u << 28) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP29 (0x1u << 29) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP30 (0x1u << 30) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */
#define MATRIX_SPSELR_NSECP31 (0x1u << 31) /**< \brief (MATRIX_SPSELR[3]) Non-secured Peripheral */

/*@}*/


#endif /* _SAMA5D2_MATRIX_COMPONENT_ */
