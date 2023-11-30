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

#ifndef _SAMA5D2_PIO_COMPONENT_
#define _SAMA5D2_PIO_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Parallel Input/Output Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_PIO Parallel Input/Output Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief PioIo_group hardware registers */
typedef struct {
  __IO uint32_t PIO_MSKR;     /**< \brief (PioIo_group Offset: 0x0) PIO Mask Register */
  __IO uint32_t PIO_CFGR;     /**< \brief (PioIo_group Offset: 0x4) PIO Configuration Register */
  __I  uint32_t PIO_PDSR;     /**< \brief (PioIo_group Offset: 0x8) PIO Pin Data Status Register */
  __I  uint32_t PIO_LOCKSR;   /**< \brief (PioIo_group Offset: 0xC) PIO Lock Status Register */
  __O  uint32_t PIO_SODR;     /**< \brief (PioIo_group Offset: 0x10) PIO Set Output Data Register */
  __O  uint32_t PIO_CODR;     /**< \brief (PioIo_group Offset: 0x14) PIO Clear Output Data Register */
  __IO uint32_t PIO_ODSR;     /**< \brief (PioIo_group Offset: 0x18) PIO Output Data Status Register */
  __I  uint32_t Reserved1[1];
  __O  uint32_t PIO_IER;      /**< \brief (PioIo_group Offset: 0x20) PIO Interrupt Enable Register */
  __O  uint32_t PIO_IDR;      /**< \brief (PioIo_group Offset: 0x24) PIO Interrupt Disable Register */
  __I  uint32_t PIO_IMR;      /**< \brief (PioIo_group Offset: 0x28) PIO Interrupt Mask Register */
  __I  uint32_t PIO_ISR;      /**< \brief (PioIo_group Offset: 0x2C) PIO Interrupt Status Register */
  __I  uint32_t Reserved2[3];
  __O  uint32_t PIO_IOFR;     /**< \brief (PioIo_group Offset: 0x3C) PIO I/O Freeze Register */
} PioIo_group;
/** \brief PioPio_ hardware registers */
typedef struct {
  __IO uint32_t S_PIO_MSKR;   /**< \brief (PioPio_ Offset: 0x0) Secure PIO Mask Register */
  __IO uint32_t S_PIO_CFGR;   /**< \brief (PioPio_ Offset: 0x4) Secure PIO Configuration Register */
  __I  uint32_t S_PIO_PDSR;   /**< \brief (PioPio_ Offset: 0x8) Secure PIO Pin Data Status Register */
  __I  uint32_t S_PIO_LOCKSR; /**< \brief (PioPio_ Offset: 0xC) Secure PIO Lock Status Register */
  __O  uint32_t S_PIO_SODR;   /**< \brief (PioPio_ Offset: 0x10) Secure PIO Set Output Data Register */
  __O  uint32_t S_PIO_CODR;   /**< \brief (PioPio_ Offset: 0x14) Secure PIO Clear Output Data Register */
  __IO uint32_t S_PIO_ODSR;   /**< \brief (PioPio_ Offset: 0x18) Secure PIO Output Data Status Register */
  __I  uint32_t Reserved3[1];
  __O  uint32_t S_PIO_IER;    /**< \brief (PioPio_ Offset: 0x20) Secure PIO Interrupt Enable Register */
  __O  uint32_t S_PIO_IDR;    /**< \brief (PioPio_ Offset: 0x24) Secure PIO Interrupt Disable Register */
  __I  uint32_t S_PIO_IMR;    /**< \brief (PioPio_ Offset: 0x28) Secure PIO Interrupt Mask Register */
  __I  uint32_t S_PIO_ISR;    /**< \brief (PioPio_ Offset: 0x2C) Secure PIO Interrupt Status Register */
  __O  uint32_t S_PIO_SIONR;  /**< \brief (PioPio_ Offset: 0x30) Secure PIO Set I/O Non-Secure Register */
  __O  uint32_t S_PIO_SIOSR;  /**< \brief (PioPio_ Offset: 0x34) Secure PIO Set I/O Secure Register */
  __I  uint32_t S_PIO_IOSSR;  /**< \brief (PioPio_ Offset: 0x38) Secure PIO I/O Security Status Register */
  __O  uint32_t S_PIO_IOFR;   /**< \brief (PioPio_ Offset: 0x3C) Secure PIO I/O Freeze Register */
} PioPio_;
/** \brief Pio hardware registers */
#define PIOIO_GROUP_NUMBER 4
#define PIOPIO__NUMBER 4
typedef struct {
       PioIo_group PIO_IO_GROUP[PIOIO_GROUP_NUMBER]; /**< \brief (Pio Offset: 0x0) io_group = 0 .. 3 */
  __I  uint32_t    Reserved1[312];
  __IO uint32_t    PIO_WPMR;                         /**< \brief (Pio Offset: 0x5E0) PIO Write Protection Mode Register */
  __I  uint32_t    PIO_WPSR;                         /**< \brief (Pio Offset: 0x5E4) PIO Write Protection Status Register */
  __I  uint32_t    Reserved2[5];
  __I  uint32_t    PIO_VERSION;                      /**< \brief (Pio Offset: 0x5FC) Version Register */
  __I  uint32_t    Reserved3[640];
       PioPio_     PIO_PIO_[PIOPIO__NUMBER];         /**< \brief (Pio Offset: 0x1000) io_group = 0 .. 3 */
  __I  uint32_t    Reserved4[256];
  __IO uint32_t    S_PIO_SCDR;                       /**< \brief (Pio Offset: 0x1500) Secure PIO Slow Clock Divider Debouncing Register */
  __I  uint32_t    Reserved5[55];
  __IO uint32_t    S_PIO_WPMR;                       /**< \brief (Pio Offset: 0x15E0) Secure PIO Write Protection Mode Register */
  __I  uint32_t    S_PIO_WPSR;                       /**< \brief (Pio Offset: 0x15E4) Secure PIO Write Protection Status Register */
} Pio;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- PIO_MSKR : (PIO Offset: N/A) PIO Mask Register -------- */
#define PIO_MSKR_MSK0 (0x1u << 0) /**< \brief (PIO_MSKR) PIO Line 0 Mask */
#define   PIO_MSKR_MSK0_DISABLED (0x0u << 0) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK0_ENABLED (0x1u << 0) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK1 (0x1u << 1) /**< \brief (PIO_MSKR) PIO Line 1 Mask */
#define   PIO_MSKR_MSK1_DISABLED (0x0u << 1) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK1_ENABLED (0x1u << 1) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK2 (0x1u << 2) /**< \brief (PIO_MSKR) PIO Line 2 Mask */
#define   PIO_MSKR_MSK2_DISABLED (0x0u << 2) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK2_ENABLED (0x1u << 2) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK3 (0x1u << 3) /**< \brief (PIO_MSKR) PIO Line 3 Mask */
#define   PIO_MSKR_MSK3_DISABLED (0x0u << 3) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK3_ENABLED (0x1u << 3) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK4 (0x1u << 4) /**< \brief (PIO_MSKR) PIO Line 4 Mask */
#define   PIO_MSKR_MSK4_DISABLED (0x0u << 4) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK4_ENABLED (0x1u << 4) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK5 (0x1u << 5) /**< \brief (PIO_MSKR) PIO Line 5 Mask */
#define   PIO_MSKR_MSK5_DISABLED (0x0u << 5) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK5_ENABLED (0x1u << 5) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK6 (0x1u << 6) /**< \brief (PIO_MSKR) PIO Line 6 Mask */
#define   PIO_MSKR_MSK6_DISABLED (0x0u << 6) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK6_ENABLED (0x1u << 6) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK7 (0x1u << 7) /**< \brief (PIO_MSKR) PIO Line 7 Mask */
#define   PIO_MSKR_MSK7_DISABLED (0x0u << 7) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK7_ENABLED (0x1u << 7) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK8 (0x1u << 8) /**< \brief (PIO_MSKR) PIO Line 8 Mask */
#define   PIO_MSKR_MSK8_DISABLED (0x0u << 8) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK8_ENABLED (0x1u << 8) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK9 (0x1u << 9) /**< \brief (PIO_MSKR) PIO Line 9 Mask */
#define   PIO_MSKR_MSK9_DISABLED (0x0u << 9) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK9_ENABLED (0x1u << 9) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK10 (0x1u << 10) /**< \brief (PIO_MSKR) PIO Line 10 Mask */
#define   PIO_MSKR_MSK10_DISABLED (0x0u << 10) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK10_ENABLED (0x1u << 10) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK11 (0x1u << 11) /**< \brief (PIO_MSKR) PIO Line 11 Mask */
#define   PIO_MSKR_MSK11_DISABLED (0x0u << 11) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK11_ENABLED (0x1u << 11) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK12 (0x1u << 12) /**< \brief (PIO_MSKR) PIO Line 12 Mask */
#define   PIO_MSKR_MSK12_DISABLED (0x0u << 12) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK12_ENABLED (0x1u << 12) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK13 (0x1u << 13) /**< \brief (PIO_MSKR) PIO Line 13 Mask */
#define   PIO_MSKR_MSK13_DISABLED (0x0u << 13) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK13_ENABLED (0x1u << 13) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK14 (0x1u << 14) /**< \brief (PIO_MSKR) PIO Line 14 Mask */
#define   PIO_MSKR_MSK14_DISABLED (0x0u << 14) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK14_ENABLED (0x1u << 14) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK15 (0x1u << 15) /**< \brief (PIO_MSKR) PIO Line 15 Mask */
#define   PIO_MSKR_MSK15_DISABLED (0x0u << 15) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK15_ENABLED (0x1u << 15) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK16 (0x1u << 16) /**< \brief (PIO_MSKR) PIO Line 16 Mask */
#define   PIO_MSKR_MSK16_DISABLED (0x0u << 16) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK16_ENABLED (0x1u << 16) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK17 (0x1u << 17) /**< \brief (PIO_MSKR) PIO Line 17 Mask */
#define   PIO_MSKR_MSK17_DISABLED (0x0u << 17) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK17_ENABLED (0x1u << 17) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK18 (0x1u << 18) /**< \brief (PIO_MSKR) PIO Line 18 Mask */
#define   PIO_MSKR_MSK18_DISABLED (0x0u << 18) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK18_ENABLED (0x1u << 18) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK19 (0x1u << 19) /**< \brief (PIO_MSKR) PIO Line 19 Mask */
#define   PIO_MSKR_MSK19_DISABLED (0x0u << 19) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK19_ENABLED (0x1u << 19) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK20 (0x1u << 20) /**< \brief (PIO_MSKR) PIO Line 20 Mask */
#define   PIO_MSKR_MSK20_DISABLED (0x0u << 20) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK20_ENABLED (0x1u << 20) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK21 (0x1u << 21) /**< \brief (PIO_MSKR) PIO Line 21 Mask */
#define   PIO_MSKR_MSK21_DISABLED (0x0u << 21) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK21_ENABLED (0x1u << 21) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK22 (0x1u << 22) /**< \brief (PIO_MSKR) PIO Line 22 Mask */
#define   PIO_MSKR_MSK22_DISABLED (0x0u << 22) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK22_ENABLED (0x1u << 22) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK23 (0x1u << 23) /**< \brief (PIO_MSKR) PIO Line 23 Mask */
#define   PIO_MSKR_MSK23_DISABLED (0x0u << 23) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK23_ENABLED (0x1u << 23) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK24 (0x1u << 24) /**< \brief (PIO_MSKR) PIO Line 24 Mask */
#define   PIO_MSKR_MSK24_DISABLED (0x0u << 24) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK24_ENABLED (0x1u << 24) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK25 (0x1u << 25) /**< \brief (PIO_MSKR) PIO Line 25 Mask */
#define   PIO_MSKR_MSK25_DISABLED (0x0u << 25) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK25_ENABLED (0x1u << 25) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK26 (0x1u << 26) /**< \brief (PIO_MSKR) PIO Line 26 Mask */
#define   PIO_MSKR_MSK26_DISABLED (0x0u << 26) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK26_ENABLED (0x1u << 26) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK27 (0x1u << 27) /**< \brief (PIO_MSKR) PIO Line 27 Mask */
#define   PIO_MSKR_MSK27_DISABLED (0x0u << 27) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK27_ENABLED (0x1u << 27) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK28 (0x1u << 28) /**< \brief (PIO_MSKR) PIO Line 28 Mask */
#define   PIO_MSKR_MSK28_DISABLED (0x0u << 28) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK28_ENABLED (0x1u << 28) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK29 (0x1u << 29) /**< \brief (PIO_MSKR) PIO Line 29 Mask */
#define   PIO_MSKR_MSK29_DISABLED (0x0u << 29) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK29_ENABLED (0x1u << 29) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK30 (0x1u << 30) /**< \brief (PIO_MSKR) PIO Line 30 Mask */
#define   PIO_MSKR_MSK30_DISABLED (0x0u << 30) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK30_ENABLED (0x1u << 30) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
#define PIO_MSKR_MSK31 (0x1u << 31) /**< \brief (PIO_MSKR) PIO Line 31 Mask */
#define   PIO_MSKR_MSK31_DISABLED (0x0u << 31) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   PIO_MSKR_MSK31_ENABLED (0x1u << 31) /**< \brief (PIO_MSKR) Writing the PIO_CFGRx, PIO_ODSRx or PIO_IOFRx updates the corresponding I/O line configuration. */
/* -------- PIO_CFGR : (PIO Offset: N/A) PIO Configuration Register -------- */
#define PIO_CFGR_FUNC_Pos 0
#define PIO_CFGR_FUNC_Msk (0x7u << PIO_CFGR_FUNC_Pos) /**< \brief (PIO_CFGR) I/O Line Function */
#define PIO_CFGR_FUNC(value) ((PIO_CFGR_FUNC_Msk & ((value) << PIO_CFGR_FUNC_Pos)))
#define   PIO_CFGR_FUNC_GPIO (0x0u << 0) /**< \brief (PIO_CFGR) Select the PIO mode for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_A (0x1u << 0) /**< \brief (PIO_CFGR) Select the peripheral A for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_B (0x2u << 0) /**< \brief (PIO_CFGR) Select the peripheral B for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_C (0x3u << 0) /**< \brief (PIO_CFGR) Select the peripheral C for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_D (0x4u << 0) /**< \brief (PIO_CFGR) Select the peripheral D for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_E (0x5u << 0) /**< \brief (PIO_CFGR) Select the peripheral E for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_F (0x6u << 0) /**< \brief (PIO_CFGR) Select the peripheral F for the selected I/O lines. */
#define   PIO_CFGR_FUNC_PERIPH_G (0x7u << 0) /**< \brief (PIO_CFGR) Select the peripheral G for the selected I/O lines. */
#define PIO_CFGR_DIR (0x1u << 8) /**< \brief (PIO_CFGR) Direction */
#define   PIO_CFGR_DIR_INPUT (0x0u << 8) /**< \brief (PIO_CFGR) The selected I/O lines are pure inputs. */
#define   PIO_CFGR_DIR_OUTPUT (0x1u << 8) /**< \brief (PIO_CFGR) The selected I/O lines are enabled in output. */
#define PIO_CFGR_PUEN (0x1u << 9) /**< \brief (PIO_CFGR) Pull-Up Enable */
#define   PIO_CFGR_PUEN_DISABLED (0x0u << 9) /**< \brief (PIO_CFGR) Pull-Up is disabled for the selected I/O lines. */
#define   PIO_CFGR_PUEN_ENABLED (0x1u << 9) /**< \brief (PIO_CFGR) Pull-Up is enabled for the selected I/O lines. */
#define PIO_CFGR_PDEN (0x1u << 10) /**< \brief (PIO_CFGR) Pull-Down Enable */
#define   PIO_CFGR_PDEN_DISABLED (0x0u << 10) /**< \brief (PIO_CFGR) Pull-Down is disabled for the selected I/O lines. */
#define   PIO_CFGR_PDEN_ENABLED (0x1u << 10) /**< \brief (PIO_CFGR) Pull-Down is enabled for the selected I/O lines only if PUEN is 0(1). */
#define PIO_CFGR_IFEN (0x1u << 12) /**< \brief (PIO_CFGR) Input Filter Enable */
#define   PIO_CFGR_IFEN_DISABLED (0x0u << 12) /**< \brief (PIO_CFGR) The input filter is disabled for the selected I/O lines. */
#define   PIO_CFGR_IFEN_ENABLED (0x1u << 12) /**< \brief (PIO_CFGR) The input filter is enabled for the selected I/O lines. */
#define PIO_CFGR_IFSCEN (0x1u << 13) /**< \brief (PIO_CFGR) Input Filter Slow Clock Enable */
#define   PIO_CFGR_IFSCEN_DISABLED (0x0u << 13) /**< \brief (PIO_CFGR) The glitch filter is able to filter glitches with a duration < tmck/2 for the selected I/O lines. */
#define   PIO_CFGR_IFSCEN_ENABLED (0x1u << 13) /**< \brief (PIO_CFGR) The debouncing filter is able to filter pulses with a duration < tdiv_slck/2 for the selected I/O lines. */
#define PIO_CFGR_OPD (0x1u << 14) /**< \brief (PIO_CFGR) Open-Drain */
#define   PIO_CFGR_OPD_DISABLED (0x0u << 14) /**< \brief (PIO_CFGR) The open-drain is disabled for the selected I/O lines. I/O lines are driven at high- and low-level. */
#define   PIO_CFGR_OPD_ENABLED (0x1u << 14) /**< \brief (PIO_CFGR) The open-drain is enabled for the selected I/O lines. I/O lines are driven at low-level only. */
#define PIO_CFGR_SCHMITT (0x1u << 15) /**< \brief (PIO_CFGR) Schmitt Trigger */
#define   PIO_CFGR_SCHMITT_ENABLED (0x0u << 15) /**< \brief (PIO_CFGR) Schmitt trigger is enabled for the selected I/O lines. */
#define   PIO_CFGR_SCHMITT_DISABLED (0x1u << 15) /**< \brief (PIO_CFGR) Schmitt trigger is disabled for the selected I/O lines. */
#define PIO_CFGR_DRVSTR_Pos 16
#define PIO_CFGR_DRVSTR_Msk (0x3u << PIO_CFGR_DRVSTR_Pos) /**< \brief (PIO_CFGR) Drive Strength */
#define PIO_CFGR_DRVSTR(value) ((PIO_CFGR_DRVSTR_Msk & ((value) << PIO_CFGR_DRVSTR_Pos)))
#define   PIO_CFGR_DRVSTR_LO (0x0u << 16) /**< \brief (PIO_CFGR) Low drive */
#define   PIO_CFGR_DRVSTR_ME (0x2u << 16) /**< \brief (PIO_CFGR) Medium drive */
#define   PIO_CFGR_DRVSTR_HI (0x3u << 16) /**< \brief (PIO_CFGR) High drive */
#define PIO_CFGR_EVTSEL_Pos 24
#define PIO_CFGR_EVTSEL_Msk (0x7u << PIO_CFGR_EVTSEL_Pos) /**< \brief (PIO_CFGR) Event Selection */
#define PIO_CFGR_EVTSEL(value) ((PIO_CFGR_EVTSEL_Msk & ((value) << PIO_CFGR_EVTSEL_Pos)))
#define   PIO_CFGR_EVTSEL_FALLING (0x0u << 24) /**< \brief (PIO_CFGR) Event detection on input falling edge */
#define   PIO_CFGR_EVTSEL_RISING (0x1u << 24) /**< \brief (PIO_CFGR) Event detection on input rising edge */
#define   PIO_CFGR_EVTSEL_BOTH (0x2u << 24) /**< \brief (PIO_CFGR) Event detection on input both edge */
#define   PIO_CFGR_EVTSEL_LOW (0x3u << 24) /**< \brief (PIO_CFGR) Event detection on low level input */
#define   PIO_CFGR_EVTSEL_HIGH (0x4u << 24) /**< \brief (PIO_CFGR) Event detection on high level input */
#define PIO_CFGR_PCFS (0x1u << 29) /**< \brief (PIO_CFGR) Physical Configuration Freeze Status */
#define   PIO_CFGR_PCFS_NOT_FROZEN (0x0u << 29) /**< \brief (PIO_CFGR) The fields are not frozen and can be written for this I/O line. */
#define   PIO_CFGR_PCFS_FROZEN (0x1u << 29) /**< \brief (PIO_CFGR) The fields are frozen and can not be written for this I/O line. Only a hardware reset can release these fields. */
#define PIO_CFGR_ICFS (0x1u << 30) /**< \brief (PIO_CFGR) Interrupt Configuration Freeze Status */
#define   PIO_CFGR_ICFS_NOT_FROZEN (0x0u << 30) /**< \brief (PIO_CFGR) The fields are not frozen and can be written for this I/O line. */
#define   PIO_CFGR_ICFS_FROZEN (0x1u << 30) /**< \brief (PIO_CFGR) The fields are frozen and can not be written for this I/O line. Only a hardware reset can release these fields. */
/* -------- PIO_PDSR : (PIO Offset: N/A) PIO Pin Data Status Register -------- */
#define PIO_PDSR_P0 (0x1u << 0) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P1 (0x1u << 1) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P2 (0x1u << 2) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P3 (0x1u << 3) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P4 (0x1u << 4) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P5 (0x1u << 5) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P6 (0x1u << 6) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P7 (0x1u << 7) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P8 (0x1u << 8) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P9 (0x1u << 9) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P10 (0x1u << 10) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P11 (0x1u << 11) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P12 (0x1u << 12) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P13 (0x1u << 13) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P14 (0x1u << 14) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P15 (0x1u << 15) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P16 (0x1u << 16) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P17 (0x1u << 17) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P18 (0x1u << 18) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P19 (0x1u << 19) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P20 (0x1u << 20) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P21 (0x1u << 21) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P22 (0x1u << 22) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P23 (0x1u << 23) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P24 (0x1u << 24) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P25 (0x1u << 25) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P26 (0x1u << 26) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P27 (0x1u << 27) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P28 (0x1u << 28) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P29 (0x1u << 29) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P30 (0x1u << 30) /**< \brief (PIO_PDSR) Input Data Status */
#define PIO_PDSR_P31 (0x1u << 31) /**< \brief (PIO_PDSR) Input Data Status */
/* -------- PIO_LOCKSR : (PIO Offset: N/A) PIO Lock Status Register -------- */
#define PIO_LOCKSR_P0 (0x1u << 0) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P1 (0x1u << 1) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P2 (0x1u << 2) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P3 (0x1u << 3) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P4 (0x1u << 4) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P5 (0x1u << 5) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P6 (0x1u << 6) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P7 (0x1u << 7) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P8 (0x1u << 8) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P9 (0x1u << 9) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P10 (0x1u << 10) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P11 (0x1u << 11) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P12 (0x1u << 12) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P13 (0x1u << 13) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P14 (0x1u << 14) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P15 (0x1u << 15) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P16 (0x1u << 16) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P17 (0x1u << 17) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P18 (0x1u << 18) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P19 (0x1u << 19) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P20 (0x1u << 20) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P21 (0x1u << 21) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P22 (0x1u << 22) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P23 (0x1u << 23) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P24 (0x1u << 24) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P25 (0x1u << 25) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P26 (0x1u << 26) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P27 (0x1u << 27) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P28 (0x1u << 28) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P29 (0x1u << 29) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P30 (0x1u << 30) /**< \brief (PIO_LOCKSR) Lock Status */
#define PIO_LOCKSR_P31 (0x1u << 31) /**< \brief (PIO_LOCKSR) Lock Status */
/* -------- PIO_SODR : (PIO Offset: N/A) PIO Set Output Data Register -------- */
#define PIO_SODR_P0 (0x1u << 0) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P1 (0x1u << 1) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P2 (0x1u << 2) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P3 (0x1u << 3) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P4 (0x1u << 4) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P5 (0x1u << 5) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P6 (0x1u << 6) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P7 (0x1u << 7) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P8 (0x1u << 8) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P9 (0x1u << 9) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P10 (0x1u << 10) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P11 (0x1u << 11) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P12 (0x1u << 12) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P13 (0x1u << 13) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P14 (0x1u << 14) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P15 (0x1u << 15) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P16 (0x1u << 16) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P17 (0x1u << 17) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P18 (0x1u << 18) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P19 (0x1u << 19) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P20 (0x1u << 20) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P21 (0x1u << 21) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P22 (0x1u << 22) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P23 (0x1u << 23) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P24 (0x1u << 24) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P25 (0x1u << 25) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P26 (0x1u << 26) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P27 (0x1u << 27) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P28 (0x1u << 28) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P29 (0x1u << 29) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P30 (0x1u << 30) /**< \brief (PIO_SODR) Set Output Data */
#define PIO_SODR_P31 (0x1u << 31) /**< \brief (PIO_SODR) Set Output Data */
/* -------- PIO_CODR : (PIO Offset: N/A) PIO Clear Output Data Register -------- */
#define PIO_CODR_P0 (0x1u << 0) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P1 (0x1u << 1) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P2 (0x1u << 2) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P3 (0x1u << 3) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P4 (0x1u << 4) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P5 (0x1u << 5) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P6 (0x1u << 6) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P7 (0x1u << 7) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P8 (0x1u << 8) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P9 (0x1u << 9) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P10 (0x1u << 10) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P11 (0x1u << 11) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P12 (0x1u << 12) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P13 (0x1u << 13) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P14 (0x1u << 14) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P15 (0x1u << 15) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P16 (0x1u << 16) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P17 (0x1u << 17) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P18 (0x1u << 18) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P19 (0x1u << 19) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P20 (0x1u << 20) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P21 (0x1u << 21) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P22 (0x1u << 22) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P23 (0x1u << 23) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P24 (0x1u << 24) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P25 (0x1u << 25) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P26 (0x1u << 26) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P27 (0x1u << 27) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P28 (0x1u << 28) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P29 (0x1u << 29) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P30 (0x1u << 30) /**< \brief (PIO_CODR) Clear Output Data */
#define PIO_CODR_P31 (0x1u << 31) /**< \brief (PIO_CODR) Clear Output Data */
/* -------- PIO_ODSR : (PIO Offset: N/A) PIO Output Data Status Register -------- */
#define PIO_ODSR_P0 (0x1u << 0) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P1 (0x1u << 1) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P2 (0x1u << 2) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P3 (0x1u << 3) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P4 (0x1u << 4) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P5 (0x1u << 5) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P6 (0x1u << 6) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P7 (0x1u << 7) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P8 (0x1u << 8) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P9 (0x1u << 9) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P10 (0x1u << 10) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P11 (0x1u << 11) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P12 (0x1u << 12) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P13 (0x1u << 13) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P14 (0x1u << 14) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P15 (0x1u << 15) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P16 (0x1u << 16) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P17 (0x1u << 17) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P18 (0x1u << 18) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P19 (0x1u << 19) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P20 (0x1u << 20) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P21 (0x1u << 21) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P22 (0x1u << 22) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P23 (0x1u << 23) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P24 (0x1u << 24) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P25 (0x1u << 25) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P26 (0x1u << 26) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P27 (0x1u << 27) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P28 (0x1u << 28) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P29 (0x1u << 29) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P30 (0x1u << 30) /**< \brief (PIO_ODSR) Output Data Status */
#define PIO_ODSR_P31 (0x1u << 31) /**< \brief (PIO_ODSR) Output Data Status */
/* -------- PIO_IER : (PIO Offset: N/A) PIO Interrupt Enable Register -------- */
#define PIO_IER_P0 (0x1u << 0) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P1 (0x1u << 1) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P2 (0x1u << 2) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P3 (0x1u << 3) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P4 (0x1u << 4) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P5 (0x1u << 5) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P6 (0x1u << 6) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P7 (0x1u << 7) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P8 (0x1u << 8) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P9 (0x1u << 9) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P10 (0x1u << 10) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P11 (0x1u << 11) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P12 (0x1u << 12) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P13 (0x1u << 13) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P14 (0x1u << 14) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P15 (0x1u << 15) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P16 (0x1u << 16) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P17 (0x1u << 17) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P18 (0x1u << 18) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P19 (0x1u << 19) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P20 (0x1u << 20) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P21 (0x1u << 21) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P22 (0x1u << 22) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P23 (0x1u << 23) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P24 (0x1u << 24) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P25 (0x1u << 25) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P26 (0x1u << 26) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P27 (0x1u << 27) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P28 (0x1u << 28) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P29 (0x1u << 29) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P30 (0x1u << 30) /**< \brief (PIO_IER) Input Change Interrupt Enable */
#define PIO_IER_P31 (0x1u << 31) /**< \brief (PIO_IER) Input Change Interrupt Enable */
/* -------- PIO_IDR : (PIO Offset: N/A) PIO Interrupt Disable Register -------- */
#define PIO_IDR_P0 (0x1u << 0) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P1 (0x1u << 1) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P2 (0x1u << 2) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P3 (0x1u << 3) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P4 (0x1u << 4) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P5 (0x1u << 5) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P6 (0x1u << 6) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P7 (0x1u << 7) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P8 (0x1u << 8) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P9 (0x1u << 9) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P10 (0x1u << 10) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P11 (0x1u << 11) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P12 (0x1u << 12) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P13 (0x1u << 13) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P14 (0x1u << 14) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P15 (0x1u << 15) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P16 (0x1u << 16) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P17 (0x1u << 17) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P18 (0x1u << 18) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P19 (0x1u << 19) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P20 (0x1u << 20) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P21 (0x1u << 21) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P22 (0x1u << 22) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P23 (0x1u << 23) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P24 (0x1u << 24) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P25 (0x1u << 25) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P26 (0x1u << 26) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P27 (0x1u << 27) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P28 (0x1u << 28) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P29 (0x1u << 29) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P30 (0x1u << 30) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
#define PIO_IDR_P31 (0x1u << 31) /**< \brief (PIO_IDR) Input Change Interrupt Disable */
/* -------- PIO_IMR : (PIO Offset: N/A) PIO Interrupt Mask Register -------- */
#define PIO_IMR_P0 (0x1u << 0) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P1 (0x1u << 1) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P2 (0x1u << 2) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P3 (0x1u << 3) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P4 (0x1u << 4) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P5 (0x1u << 5) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P6 (0x1u << 6) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P7 (0x1u << 7) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P8 (0x1u << 8) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P9 (0x1u << 9) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P10 (0x1u << 10) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P11 (0x1u << 11) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P12 (0x1u << 12) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P13 (0x1u << 13) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P14 (0x1u << 14) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P15 (0x1u << 15) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P16 (0x1u << 16) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P17 (0x1u << 17) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P18 (0x1u << 18) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P19 (0x1u << 19) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P20 (0x1u << 20) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P21 (0x1u << 21) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P22 (0x1u << 22) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P23 (0x1u << 23) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P24 (0x1u << 24) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P25 (0x1u << 25) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P26 (0x1u << 26) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P27 (0x1u << 27) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P28 (0x1u << 28) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P29 (0x1u << 29) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P30 (0x1u << 30) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
#define PIO_IMR_P31 (0x1u << 31) /**< \brief (PIO_IMR) Input Change Interrupt Mask */
/* -------- PIO_ISR : (PIO Offset: N/A) PIO Interrupt Status Register -------- */
#define PIO_ISR_P0 (0x1u << 0) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P1 (0x1u << 1) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P2 (0x1u << 2) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P3 (0x1u << 3) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P4 (0x1u << 4) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P5 (0x1u << 5) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P6 (0x1u << 6) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P7 (0x1u << 7) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P8 (0x1u << 8) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P9 (0x1u << 9) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P10 (0x1u << 10) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P11 (0x1u << 11) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P12 (0x1u << 12) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P13 (0x1u << 13) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P14 (0x1u << 14) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P15 (0x1u << 15) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P16 (0x1u << 16) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P17 (0x1u << 17) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P18 (0x1u << 18) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P19 (0x1u << 19) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P20 (0x1u << 20) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P21 (0x1u << 21) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P22 (0x1u << 22) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P23 (0x1u << 23) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P24 (0x1u << 24) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P25 (0x1u << 25) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P26 (0x1u << 26) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P27 (0x1u << 27) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P28 (0x1u << 28) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P29 (0x1u << 29) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P30 (0x1u << 30) /**< \brief (PIO_ISR) Input Change Interrupt Status */
#define PIO_ISR_P31 (0x1u << 31) /**< \brief (PIO_ISR) Input Change Interrupt Status */
/* -------- PIO_IOFR : (PIO Offset: N/A) PIO I/O Freeze Register -------- */
#define PIO_IOFR_FPHY (0x1u << 0) /**< \brief (PIO_IOFR) Freeze Physical Configuration */
#define PIO_IOFR_FINT (0x1u << 1) /**< \brief (PIO_IOFR) Freeze Interrupt Configuration */
#define PIO_IOFR_FRZKEY_Pos 8
#define PIO_IOFR_FRZKEY_Msk (0xffffffu << PIO_IOFR_FRZKEY_Pos) /**< \brief (PIO_IOFR) Freeze Key */
#define PIO_IOFR_FRZKEY(value) ((PIO_IOFR_FRZKEY_Msk & ((value) << PIO_IOFR_FRZKEY_Pos)))
#define   PIO_IOFR_FRZKEY_PASSWD (0x494F46u << 8) /**< \brief (PIO_IOFR) Writing any other value in this field aborts the write operation of the WPEN bit. */
/* -------- PIO_WPMR : (PIO Offset: 0x5E0) PIO Write Protection Mode Register -------- */
#define PIO_WPMR_WPEN (0x1u << 0) /**< \brief (PIO_WPMR) Write Protection Enable */
#define PIO_WPMR_WPKEY_Pos 8
#define PIO_WPMR_WPKEY_Msk (0xffffffu << PIO_WPMR_WPKEY_Pos) /**< \brief (PIO_WPMR) Write Protection Key */
#define PIO_WPMR_WPKEY(value) ((PIO_WPMR_WPKEY_Msk & ((value) << PIO_WPMR_WPKEY_Pos)))
#define   PIO_WPMR_WPKEY_PASSWD (0x50494Fu << 8) /**< \brief (PIO_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit. Always reads as 0. */
/* -------- PIO_WPSR : (PIO Offset: 0x5E4) PIO Write Protection Status Register -------- */
#define PIO_WPSR_WPVS (0x1u << 0) /**< \brief (PIO_WPSR) Write Protection Violation Status */
#define PIO_WPSR_WPVSRC_Pos 8
#define PIO_WPSR_WPVSRC_Msk (0xffffu << PIO_WPSR_WPVSRC_Pos) /**< \brief (PIO_WPSR) Write Protection Violation Source */
/* -------- PIO_VERSION : (PIO Offset: 0x5FC) Version Register -------- */
#define PIO_VERSION_VERSION_Pos 0
#define PIO_VERSION_VERSION_Msk (0xfffu << PIO_VERSION_VERSION_Pos) /**< \brief (PIO_VERSION) Hardware Module Version */
#define PIO_VERSION_MFN_Pos 16
#define PIO_VERSION_MFN_Msk (0x7u << PIO_VERSION_MFN_Pos) /**< \brief (PIO_VERSION) Metal Fix Number */
/* -------- S_PIO_MSKR : (PIO Offset: N/A) Secure PIO Mask Register -------- */
#define S_PIO_MSKR_MSK0 (0x1u << 0) /**< \brief (S_PIO_MSKR) PIO Line 0 Mask */
#define   S_PIO_MSKR_MSK0_DISABLED (0x0u << 0) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK0_ENABLED (0x1u << 0) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK1 (0x1u << 1) /**< \brief (S_PIO_MSKR) PIO Line 1 Mask */
#define   S_PIO_MSKR_MSK1_DISABLED (0x0u << 1) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK1_ENABLED (0x1u << 1) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK2 (0x1u << 2) /**< \brief (S_PIO_MSKR) PIO Line 2 Mask */
#define   S_PIO_MSKR_MSK2_DISABLED (0x0u << 2) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK2_ENABLED (0x1u << 2) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK3 (0x1u << 3) /**< \brief (S_PIO_MSKR) PIO Line 3 Mask */
#define   S_PIO_MSKR_MSK3_DISABLED (0x0u << 3) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK3_ENABLED (0x1u << 3) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK4 (0x1u << 4) /**< \brief (S_PIO_MSKR) PIO Line 4 Mask */
#define   S_PIO_MSKR_MSK4_DISABLED (0x0u << 4) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK4_ENABLED (0x1u << 4) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK5 (0x1u << 5) /**< \brief (S_PIO_MSKR) PIO Line 5 Mask */
#define   S_PIO_MSKR_MSK5_DISABLED (0x0u << 5) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK5_ENABLED (0x1u << 5) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK6 (0x1u << 6) /**< \brief (S_PIO_MSKR) PIO Line 6 Mask */
#define   S_PIO_MSKR_MSK6_DISABLED (0x0u << 6) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK6_ENABLED (0x1u << 6) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK7 (0x1u << 7) /**< \brief (S_PIO_MSKR) PIO Line 7 Mask */
#define   S_PIO_MSKR_MSK7_DISABLED (0x0u << 7) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK7_ENABLED (0x1u << 7) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK8 (0x1u << 8) /**< \brief (S_PIO_MSKR) PIO Line 8 Mask */
#define   S_PIO_MSKR_MSK8_DISABLED (0x0u << 8) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK8_ENABLED (0x1u << 8) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK9 (0x1u << 9) /**< \brief (S_PIO_MSKR) PIO Line 9 Mask */
#define   S_PIO_MSKR_MSK9_DISABLED (0x0u << 9) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK9_ENABLED (0x1u << 9) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK10 (0x1u << 10) /**< \brief (S_PIO_MSKR) PIO Line 10 Mask */
#define   S_PIO_MSKR_MSK10_DISABLED (0x0u << 10) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK10_ENABLED (0x1u << 10) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK11 (0x1u << 11) /**< \brief (S_PIO_MSKR) PIO Line 11 Mask */
#define   S_PIO_MSKR_MSK11_DISABLED (0x0u << 11) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK11_ENABLED (0x1u << 11) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK12 (0x1u << 12) /**< \brief (S_PIO_MSKR) PIO Line 12 Mask */
#define   S_PIO_MSKR_MSK12_DISABLED (0x0u << 12) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK12_ENABLED (0x1u << 12) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK13 (0x1u << 13) /**< \brief (S_PIO_MSKR) PIO Line 13 Mask */
#define   S_PIO_MSKR_MSK13_DISABLED (0x0u << 13) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK13_ENABLED (0x1u << 13) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK14 (0x1u << 14) /**< \brief (S_PIO_MSKR) PIO Line 14 Mask */
#define   S_PIO_MSKR_MSK14_DISABLED (0x0u << 14) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK14_ENABLED (0x1u << 14) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK15 (0x1u << 15) /**< \brief (S_PIO_MSKR) PIO Line 15 Mask */
#define   S_PIO_MSKR_MSK15_DISABLED (0x0u << 15) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK15_ENABLED (0x1u << 15) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK16 (0x1u << 16) /**< \brief (S_PIO_MSKR) PIO Line 16 Mask */
#define   S_PIO_MSKR_MSK16_DISABLED (0x0u << 16) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK16_ENABLED (0x1u << 16) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK17 (0x1u << 17) /**< \brief (S_PIO_MSKR) PIO Line 17 Mask */
#define   S_PIO_MSKR_MSK17_DISABLED (0x0u << 17) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK17_ENABLED (0x1u << 17) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK18 (0x1u << 18) /**< \brief (S_PIO_MSKR) PIO Line 18 Mask */
#define   S_PIO_MSKR_MSK18_DISABLED (0x0u << 18) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK18_ENABLED (0x1u << 18) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK19 (0x1u << 19) /**< \brief (S_PIO_MSKR) PIO Line 19 Mask */
#define   S_PIO_MSKR_MSK19_DISABLED (0x0u << 19) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK19_ENABLED (0x1u << 19) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK20 (0x1u << 20) /**< \brief (S_PIO_MSKR) PIO Line 20 Mask */
#define   S_PIO_MSKR_MSK20_DISABLED (0x0u << 20) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK20_ENABLED (0x1u << 20) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK21 (0x1u << 21) /**< \brief (S_PIO_MSKR) PIO Line 21 Mask */
#define   S_PIO_MSKR_MSK21_DISABLED (0x0u << 21) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK21_ENABLED (0x1u << 21) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK22 (0x1u << 22) /**< \brief (S_PIO_MSKR) PIO Line 22 Mask */
#define   S_PIO_MSKR_MSK22_DISABLED (0x0u << 22) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK22_ENABLED (0x1u << 22) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK23 (0x1u << 23) /**< \brief (S_PIO_MSKR) PIO Line 23 Mask */
#define   S_PIO_MSKR_MSK23_DISABLED (0x0u << 23) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK23_ENABLED (0x1u << 23) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK24 (0x1u << 24) /**< \brief (S_PIO_MSKR) PIO Line 24 Mask */
#define   S_PIO_MSKR_MSK24_DISABLED (0x0u << 24) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK24_ENABLED (0x1u << 24) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK25 (0x1u << 25) /**< \brief (S_PIO_MSKR) PIO Line 25 Mask */
#define   S_PIO_MSKR_MSK25_DISABLED (0x0u << 25) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK25_ENABLED (0x1u << 25) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK26 (0x1u << 26) /**< \brief (S_PIO_MSKR) PIO Line 26 Mask */
#define   S_PIO_MSKR_MSK26_DISABLED (0x0u << 26) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK26_ENABLED (0x1u << 26) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK27 (0x1u << 27) /**< \brief (S_PIO_MSKR) PIO Line 27 Mask */
#define   S_PIO_MSKR_MSK27_DISABLED (0x0u << 27) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK27_ENABLED (0x1u << 27) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK28 (0x1u << 28) /**< \brief (S_PIO_MSKR) PIO Line 28 Mask */
#define   S_PIO_MSKR_MSK28_DISABLED (0x0u << 28) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK28_ENABLED (0x1u << 28) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK29 (0x1u << 29) /**< \brief (S_PIO_MSKR) PIO Line 29 Mask */
#define   S_PIO_MSKR_MSK29_DISABLED (0x0u << 29) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK29_ENABLED (0x1u << 29) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK30 (0x1u << 30) /**< \brief (S_PIO_MSKR) PIO Line 30 Mask */
#define   S_PIO_MSKR_MSK30_DISABLED (0x0u << 30) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK30_ENABLED (0x1u << 30) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
#define S_PIO_MSKR_MSK31 (0x1u << 31) /**< \brief (S_PIO_MSKR) PIO Line 31 Mask */
#define   S_PIO_MSKR_MSK31_DISABLED (0x0u << 31) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRx does not affect the corresponding I/O line configuration. */
#define   S_PIO_MSKR_MSK31_ENABLED (0x1u << 31) /**< \brief (S_PIO_MSKR) Writing the S_PIO_CFGRx, S_PIO_ODSRx or S_PIO_IOFRX updates the corresponding I/O line configuration. */
/* -------- S_PIO_CFGR : (PIO Offset: N/A) Secure PIO Configuration Register -------- */
#define S_PIO_CFGR_FUNC_Pos 0
#define S_PIO_CFGR_FUNC_Msk (0x7u << S_PIO_CFGR_FUNC_Pos) /**< \brief (S_PIO_CFGR) I/O Line Function */
#define S_PIO_CFGR_FUNC(value) ((S_PIO_CFGR_FUNC_Msk & ((value) << S_PIO_CFGR_FUNC_Pos)))
#define   S_PIO_CFGR_FUNC_GPIO (0x0u << 0) /**< \brief (S_PIO_CFGR) Select the PIO mode for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_A (0x1u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral A for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_B (0x2u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral B for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_C (0x3u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral C for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_D (0x4u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral D for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_E (0x5u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral E for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_F (0x6u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral F for the selected I/O lines. */
#define   S_PIO_CFGR_FUNC_PERIPH_G (0x7u << 0) /**< \brief (S_PIO_CFGR) Select the peripheral G for the selected I/O lines. */
#define S_PIO_CFGR_DIR (0x1u << 8) /**< \brief (S_PIO_CFGR) Direction */
#define   S_PIO_CFGR_DIR_INPUT (0x0u << 8) /**< \brief (S_PIO_CFGR) The selected I/O lines are pure inputs. */
#define   S_PIO_CFGR_DIR_OUTPUT (0x1u << 8) /**< \brief (S_PIO_CFGR) The selected I/O lines are enabled in output. */
#define S_PIO_CFGR_PUEN (0x1u << 9) /**< \brief (S_PIO_CFGR) Pull-Up Enable */
#define   S_PIO_CFGR_PUEN_DISABLED (0x0u << 9) /**< \brief (S_PIO_CFGR) Pull-Up is disabled for the selected I/O lines. */
#define   S_PIO_CFGR_PUEN_ENABLED (0x1u << 9) /**< \brief (S_PIO_CFGR) Pull-Up is enabled for the selected I/O lines. */
#define S_PIO_CFGR_PDEN (0x1u << 10) /**< \brief (S_PIO_CFGR) Pull-Down Enable */
#define   S_PIO_CFGR_PDEN_DISABLED (0x0u << 10) /**< \brief (S_PIO_CFGR) Pull-Down is disabled for the selected I/O lines. */
#define   S_PIO_CFGR_PDEN_ENABLED (0x1u << 10) /**< \brief (S_PIO_CFGR) Pull-Down is enabled for the selected I/O lines only if PUEN is 0(1). */
#define S_PIO_CFGR_IFEN (0x1u << 12) /**< \brief (S_PIO_CFGR) Input Filter Enable */
#define   S_PIO_CFGR_IFEN_DISABLED (0x0u << 12) /**< \brief (S_PIO_CFGR) The input filter is disabled for the selected I/O lines. */
#define   S_PIO_CFGR_IFEN_ENABLED (0x1u << 12) /**< \brief (S_PIO_CFGR) The input filter is enabled for the selected I/O lines. */
#define S_PIO_CFGR_IFSCEN (0x1u << 13) /**< \brief (S_PIO_CFGR) Input Filter Slow Clock Enable */
#define S_PIO_CFGR_OPD (0x1u << 14) /**< \brief (S_PIO_CFGR) Open-Drain */
#define   S_PIO_CFGR_OPD_DISABLED (0x0u << 14) /**< \brief (S_PIO_CFGR) The open-drain is disabled for the selected I/O lines. I/O lines are driven at high- and low-level. */
#define   S_PIO_CFGR_OPD_ENABLED (0x1u << 14) /**< \brief (S_PIO_CFGR) The open-drain is enabled for the selected I/O lines. I/O lines are driven at low-level only. */
#define S_PIO_CFGR_SCHMITT (0x1u << 15) /**< \brief (S_PIO_CFGR) Schmitt Trigger */
#define   S_PIO_CFGR_SCHMITT_ENABLED (0x0u << 15) /**< \brief (S_PIO_CFGR) Schmitt trigger is enabled for the selected I/O lines. */
#define   S_PIO_CFGR_SCHMITT_DISABLED (0x1u << 15) /**< \brief (S_PIO_CFGR) Schmitt trigger is disabled for the selected I/O lines. */
#define S_PIO_CFGR_DRVSTR_Pos 16
#define S_PIO_CFGR_DRVSTR_Msk (0x3u << S_PIO_CFGR_DRVSTR_Pos) /**< \brief (S_PIO_CFGR)  */
#define S_PIO_CFGR_DRVSTR(value) ((S_PIO_CFGR_DRVSTR_Msk & ((value) << S_PIO_CFGR_DRVSTR_Pos)))
#define S_PIO_CFGR_EVTSEL_Pos 24
#define S_PIO_CFGR_EVTSEL_Msk (0x7u << S_PIO_CFGR_EVTSEL_Pos) /**< \brief (S_PIO_CFGR) Event Selection */
#define S_PIO_CFGR_EVTSEL(value) ((S_PIO_CFGR_EVTSEL_Msk & ((value) << S_PIO_CFGR_EVTSEL_Pos)))
#define   S_PIO_CFGR_EVTSEL_FALLING (0x0u << 24) /**< \brief (S_PIO_CFGR) Event detection on input falling edge */
#define   S_PIO_CFGR_EVTSEL_RISING (0x1u << 24) /**< \brief (S_PIO_CFGR) Event detection on input rising edge */
#define   S_PIO_CFGR_EVTSEL_BOTH (0x2u << 24) /**< \brief (S_PIO_CFGR) Event detection on input both edge */
#define   S_PIO_CFGR_EVTSEL_LOW (0x3u << 24) /**< \brief (S_PIO_CFGR) Event detection on low level input */
#define   S_PIO_CFGR_EVTSEL_HIGH (0x4u << 24) /**< \brief (S_PIO_CFGR) Event detection on high level input */
#define S_PIO_CFGR_PCFS (0x1u << 29) /**< \brief (S_PIO_CFGR) Physical Configuration Freeze Status */
#define   S_PIO_CFGR_PCFS_NOT_FROZEN (0x0u << 29) /**< \brief (S_PIO_CFGR) The fields are not frozen and can be written for this I/O line. */
#define   S_PIO_CFGR_PCFS_FROZEN (0x1u << 29) /**< \brief (S_PIO_CFGR) The fields are frozen and can not be written for this I/O line. Only a hardware reset can release these fields. */
#define S_PIO_CFGR_ICFS (0x1u << 30) /**< \brief (S_PIO_CFGR) Interrupt Configuration Freeze Status */
#define   S_PIO_CFGR_ICFS_NOT_FROZEN (0x0u << 30) /**< \brief (S_PIO_CFGR) The fields are not frozen and can be written for this I/O line. */
#define   S_PIO_CFGR_ICFS_FROZEN (0x1u << 30) /**< \brief (S_PIO_CFGR) The fields are frozen and can not be written for this I/O line. Only a hardware reset can release these fields. */
/* -------- S_PIO_PDSR : (PIO Offset: N/A) Secure PIO Pin Data Status Register -------- */
#define S_PIO_PDSR_P0 (0x1u << 0) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P1 (0x1u << 1) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P2 (0x1u << 2) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P3 (0x1u << 3) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P4 (0x1u << 4) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P5 (0x1u << 5) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P6 (0x1u << 6) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P7 (0x1u << 7) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P8 (0x1u << 8) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P9 (0x1u << 9) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P10 (0x1u << 10) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P11 (0x1u << 11) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P12 (0x1u << 12) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P13 (0x1u << 13) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P14 (0x1u << 14) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P15 (0x1u << 15) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P16 (0x1u << 16) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P17 (0x1u << 17) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P18 (0x1u << 18) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P19 (0x1u << 19) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P20 (0x1u << 20) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P21 (0x1u << 21) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P22 (0x1u << 22) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P23 (0x1u << 23) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P24 (0x1u << 24) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P25 (0x1u << 25) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P26 (0x1u << 26) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P27 (0x1u << 27) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P28 (0x1u << 28) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P29 (0x1u << 29) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P30 (0x1u << 30) /**< \brief (S_PIO_PDSR) Input Data Status */
#define S_PIO_PDSR_P31 (0x1u << 31) /**< \brief (S_PIO_PDSR) Input Data Status */
/* -------- S_PIO_SODR : (PIO Offset: N/A) Secure PIO Set Output Data Register -------- */
#define S_PIO_SODR_P0 (0x1u << 0) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P1 (0x1u << 1) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P2 (0x1u << 2) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P3 (0x1u << 3) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P4 (0x1u << 4) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P5 (0x1u << 5) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P6 (0x1u << 6) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P7 (0x1u << 7) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P8 (0x1u << 8) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P9 (0x1u << 9) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P10 (0x1u << 10) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P11 (0x1u << 11) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P12 (0x1u << 12) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P13 (0x1u << 13) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P14 (0x1u << 14) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P15 (0x1u << 15) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P16 (0x1u << 16) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P17 (0x1u << 17) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P18 (0x1u << 18) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P19 (0x1u << 19) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P20 (0x1u << 20) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P21 (0x1u << 21) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P22 (0x1u << 22) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P23 (0x1u << 23) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P24 (0x1u << 24) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P25 (0x1u << 25) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P26 (0x1u << 26) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P27 (0x1u << 27) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P28 (0x1u << 28) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P29 (0x1u << 29) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P30 (0x1u << 30) /**< \brief (S_PIO_SODR) Set Output Data */
#define S_PIO_SODR_P31 (0x1u << 31) /**< \brief (S_PIO_SODR) Set Output Data */
/* -------- S_PIO_CODR : (PIO Offset: N/A) Secure PIO Clear Output Data Register -------- */
#define S_PIO_CODR_P0 (0x1u << 0) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P1 (0x1u << 1) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P2 (0x1u << 2) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P3 (0x1u << 3) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P4 (0x1u << 4) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P5 (0x1u << 5) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P6 (0x1u << 6) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P7 (0x1u << 7) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P8 (0x1u << 8) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P9 (0x1u << 9) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P10 (0x1u << 10) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P11 (0x1u << 11) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P12 (0x1u << 12) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P13 (0x1u << 13) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P14 (0x1u << 14) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P15 (0x1u << 15) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P16 (0x1u << 16) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P17 (0x1u << 17) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P18 (0x1u << 18) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P19 (0x1u << 19) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P20 (0x1u << 20) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P21 (0x1u << 21) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P22 (0x1u << 22) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P23 (0x1u << 23) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P24 (0x1u << 24) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P25 (0x1u << 25) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P26 (0x1u << 26) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P27 (0x1u << 27) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P28 (0x1u << 28) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P29 (0x1u << 29) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P30 (0x1u << 30) /**< \brief (S_PIO_CODR) Clear Output Data */
#define S_PIO_CODR_P31 (0x1u << 31) /**< \brief (S_PIO_CODR) Clear Output Data */
/* -------- S_PIO_ODSR : (PIO Offset: N/A) Secure PIO Output Data Status Register -------- */
#define S_PIO_ODSR_P0 (0x1u << 0) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P1 (0x1u << 1) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P2 (0x1u << 2) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P3 (0x1u << 3) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P4 (0x1u << 4) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P5 (0x1u << 5) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P6 (0x1u << 6) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P7 (0x1u << 7) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P8 (0x1u << 8) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P9 (0x1u << 9) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P10 (0x1u << 10) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P11 (0x1u << 11) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P12 (0x1u << 12) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P13 (0x1u << 13) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P14 (0x1u << 14) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P15 (0x1u << 15) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P16 (0x1u << 16) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P17 (0x1u << 17) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P18 (0x1u << 18) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P19 (0x1u << 19) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P20 (0x1u << 20) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P21 (0x1u << 21) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P22 (0x1u << 22) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P23 (0x1u << 23) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P24 (0x1u << 24) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P25 (0x1u << 25) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P26 (0x1u << 26) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P27 (0x1u << 27) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P28 (0x1u << 28) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P29 (0x1u << 29) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P30 (0x1u << 30) /**< \brief (S_PIO_ODSR) Output Data Status */
#define S_PIO_ODSR_P31 (0x1u << 31) /**< \brief (S_PIO_ODSR) Output Data Status */
/* -------- S_PIO_IER : (PIO Offset: N/A) Secure PIO Interrupt Enable Register -------- */
#define S_PIO_IER_P0 (0x1u << 0) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P1 (0x1u << 1) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P2 (0x1u << 2) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P3 (0x1u << 3) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P4 (0x1u << 4) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P5 (0x1u << 5) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P6 (0x1u << 6) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P7 (0x1u << 7) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P8 (0x1u << 8) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P9 (0x1u << 9) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P10 (0x1u << 10) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P11 (0x1u << 11) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P12 (0x1u << 12) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P13 (0x1u << 13) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P14 (0x1u << 14) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P15 (0x1u << 15) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P16 (0x1u << 16) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P17 (0x1u << 17) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P18 (0x1u << 18) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P19 (0x1u << 19) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P20 (0x1u << 20) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P21 (0x1u << 21) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P22 (0x1u << 22) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P23 (0x1u << 23) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P24 (0x1u << 24) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P25 (0x1u << 25) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P26 (0x1u << 26) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P27 (0x1u << 27) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P28 (0x1u << 28) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P29 (0x1u << 29) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P30 (0x1u << 30) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
#define S_PIO_IER_P31 (0x1u << 31) /**< \brief (S_PIO_IER) Input Change Interrupt Enable */
/* -------- S_PIO_IDR : (PIO Offset: N/A) Secure PIO Interrupt Disable Register -------- */
#define S_PIO_IDR_P0 (0x1u << 0) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P1 (0x1u << 1) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P2 (0x1u << 2) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P3 (0x1u << 3) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P4 (0x1u << 4) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P5 (0x1u << 5) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P6 (0x1u << 6) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P7 (0x1u << 7) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P8 (0x1u << 8) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P9 (0x1u << 9) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P10 (0x1u << 10) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P11 (0x1u << 11) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P12 (0x1u << 12) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P13 (0x1u << 13) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P14 (0x1u << 14) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P15 (0x1u << 15) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P16 (0x1u << 16) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P17 (0x1u << 17) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P18 (0x1u << 18) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P19 (0x1u << 19) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P20 (0x1u << 20) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P21 (0x1u << 21) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P22 (0x1u << 22) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P23 (0x1u << 23) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P24 (0x1u << 24) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P25 (0x1u << 25) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P26 (0x1u << 26) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P27 (0x1u << 27) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P28 (0x1u << 28) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P29 (0x1u << 29) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P30 (0x1u << 30) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
#define S_PIO_IDR_P31 (0x1u << 31) /**< \brief (S_PIO_IDR) Input Change Interrupt Disable */
/* -------- S_PIO_IMR : (PIO Offset: N/A) Secure PIO Interrupt Mask Register -------- */
#define S_PIO_IMR_P0 (0x1u << 0) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P1 (0x1u << 1) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P2 (0x1u << 2) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P3 (0x1u << 3) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P4 (0x1u << 4) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P5 (0x1u << 5) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P6 (0x1u << 6) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P7 (0x1u << 7) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P8 (0x1u << 8) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P9 (0x1u << 9) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P10 (0x1u << 10) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P11 (0x1u << 11) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P12 (0x1u << 12) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P13 (0x1u << 13) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P14 (0x1u << 14) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P15 (0x1u << 15) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P16 (0x1u << 16) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P17 (0x1u << 17) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P18 (0x1u << 18) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P19 (0x1u << 19) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P20 (0x1u << 20) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P21 (0x1u << 21) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P22 (0x1u << 22) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P23 (0x1u << 23) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P24 (0x1u << 24) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P25 (0x1u << 25) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P26 (0x1u << 26) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P27 (0x1u << 27) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P28 (0x1u << 28) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P29 (0x1u << 29) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P30 (0x1u << 30) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
#define S_PIO_IMR_P31 (0x1u << 31) /**< \brief (S_PIO_IMR) Input Change Interrupt Mask */
/* -------- S_PIO_ISR : (PIO Offset: N/A) Secure PIO Interrupt Status Register -------- */
#define S_PIO_ISR_P0 (0x1u << 0) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P1 (0x1u << 1) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P2 (0x1u << 2) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P3 (0x1u << 3) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P4 (0x1u << 4) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P5 (0x1u << 5) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P6 (0x1u << 6) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P7 (0x1u << 7) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P8 (0x1u << 8) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P9 (0x1u << 9) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P10 (0x1u << 10) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P11 (0x1u << 11) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P12 (0x1u << 12) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P13 (0x1u << 13) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P14 (0x1u << 14) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P15 (0x1u << 15) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P16 (0x1u << 16) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P17 (0x1u << 17) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P18 (0x1u << 18) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P19 (0x1u << 19) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P20 (0x1u << 20) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P21 (0x1u << 21) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P22 (0x1u << 22) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P23 (0x1u << 23) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P24 (0x1u << 24) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P25 (0x1u << 25) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P26 (0x1u << 26) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P27 (0x1u << 27) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P28 (0x1u << 28) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P29 (0x1u << 29) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P30 (0x1u << 30) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
#define S_PIO_ISR_P31 (0x1u << 31) /**< \brief (S_PIO_ISR) Input Change Interrupt Status */
/* -------- S_PIO_SIONR : (PIO Offset: N/A) Secure PIO Set I/O Non-Secure Register -------- */
#define S_PIO_SIONR_P0 (0x1u << 0) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P1 (0x1u << 1) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P2 (0x1u << 2) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P3 (0x1u << 3) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P4 (0x1u << 4) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P5 (0x1u << 5) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P6 (0x1u << 6) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P7 (0x1u << 7) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P8 (0x1u << 8) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P9 (0x1u << 9) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P10 (0x1u << 10) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P11 (0x1u << 11) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P12 (0x1u << 12) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P13 (0x1u << 13) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P14 (0x1u << 14) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P15 (0x1u << 15) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P16 (0x1u << 16) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P17 (0x1u << 17) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P18 (0x1u << 18) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P19 (0x1u << 19) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P20 (0x1u << 20) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P21 (0x1u << 21) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P22 (0x1u << 22) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P23 (0x1u << 23) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P24 (0x1u << 24) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P25 (0x1u << 25) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P26 (0x1u << 26) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P27 (0x1u << 27) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P28 (0x1u << 28) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P29 (0x1u << 29) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P30 (0x1u << 30) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
#define S_PIO_SIONR_P31 (0x1u << 31) /**< \brief (S_PIO_SIONR) Set I/O Non-Secure */
/* -------- S_PIO_SIOSR : (PIO Offset: N/A) Secure PIO Set I/O Secure Register -------- */
#define S_PIO_SIOSR_P0 (0x1u << 0) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P1 (0x1u << 1) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P2 (0x1u << 2) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P3 (0x1u << 3) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P4 (0x1u << 4) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P5 (0x1u << 5) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P6 (0x1u << 6) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P7 (0x1u << 7) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P8 (0x1u << 8) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P9 (0x1u << 9) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P10 (0x1u << 10) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P11 (0x1u << 11) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P12 (0x1u << 12) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P13 (0x1u << 13) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P14 (0x1u << 14) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P15 (0x1u << 15) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P16 (0x1u << 16) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P17 (0x1u << 17) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P18 (0x1u << 18) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P19 (0x1u << 19) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P20 (0x1u << 20) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P21 (0x1u << 21) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P22 (0x1u << 22) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P23 (0x1u << 23) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P24 (0x1u << 24) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P25 (0x1u << 25) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P26 (0x1u << 26) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P27 (0x1u << 27) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P28 (0x1u << 28) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P29 (0x1u << 29) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P30 (0x1u << 30) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
#define S_PIO_SIOSR_P31 (0x1u << 31) /**< \brief (S_PIO_SIOSR) Set I/O Secure */
/* -------- S_PIO_IOSSR : (PIO Offset: N/A) Secure PIO I/O Security Status Register -------- */
#define S_PIO_IOSSR_P0 (0x1u << 0) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P0_SECURE (0x0u << 0) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P0_NON_SECURE (0x1u << 0) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P1 (0x1u << 1) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P1_SECURE (0x0u << 1) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P1_NON_SECURE (0x1u << 1) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P2 (0x1u << 2) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P2_SECURE (0x0u << 2) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P2_NON_SECURE (0x1u << 2) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P3 (0x1u << 3) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P3_SECURE (0x0u << 3) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P3_NON_SECURE (0x1u << 3) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P4 (0x1u << 4) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P4_SECURE (0x0u << 4) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P4_NON_SECURE (0x1u << 4) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P5 (0x1u << 5) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P5_SECURE (0x0u << 5) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P5_NON_SECURE (0x1u << 5) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P6 (0x1u << 6) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P6_SECURE (0x0u << 6) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P6_NON_SECURE (0x1u << 6) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P7 (0x1u << 7) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P7_SECURE (0x0u << 7) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P7_NON_SECURE (0x1u << 7) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P8 (0x1u << 8) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P8_SECURE (0x0u << 8) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P8_NON_SECURE (0x1u << 8) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P9 (0x1u << 9) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P9_SECURE (0x0u << 9) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P9_NON_SECURE (0x1u << 9) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P10 (0x1u << 10) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P10_SECURE (0x0u << 10) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P10_NON_SECURE (0x1u << 10) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P11 (0x1u << 11) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P11_SECURE (0x0u << 11) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P11_NON_SECURE (0x1u << 11) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P12 (0x1u << 12) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P12_SECURE (0x0u << 12) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P12_NON_SECURE (0x1u << 12) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P13 (0x1u << 13) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P13_SECURE (0x0u << 13) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P13_NON_SECURE (0x1u << 13) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P14 (0x1u << 14) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P14_SECURE (0x0u << 14) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P14_NON_SECURE (0x1u << 14) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P15 (0x1u << 15) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P15_SECURE (0x0u << 15) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P15_NON_SECURE (0x1u << 15) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P16 (0x1u << 16) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P16_SECURE (0x0u << 16) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P16_NON_SECURE (0x1u << 16) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P17 (0x1u << 17) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P17_SECURE (0x0u << 17) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P17_NON_SECURE (0x1u << 17) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P18 (0x1u << 18) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P18_SECURE (0x0u << 18) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P18_NON_SECURE (0x1u << 18) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P19 (0x1u << 19) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P19_SECURE (0x0u << 19) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P19_NON_SECURE (0x1u << 19) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P20 (0x1u << 20) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P20_SECURE (0x0u << 20) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P20_NON_SECURE (0x1u << 20) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P21 (0x1u << 21) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P21_SECURE (0x0u << 21) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P21_NON_SECURE (0x1u << 21) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P22 (0x1u << 22) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P22_SECURE (0x0u << 22) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P22_NON_SECURE (0x1u << 22) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P23 (0x1u << 23) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P23_SECURE (0x0u << 23) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P23_NON_SECURE (0x1u << 23) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P24 (0x1u << 24) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P24_SECURE (0x0u << 24) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P24_NON_SECURE (0x1u << 24) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P25 (0x1u << 25) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P25_SECURE (0x0u << 25) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P25_NON_SECURE (0x1u << 25) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P26 (0x1u << 26) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P26_SECURE (0x0u << 26) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P26_NON_SECURE (0x1u << 26) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P27 (0x1u << 27) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P27_SECURE (0x0u << 27) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P27_NON_SECURE (0x1u << 27) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P28 (0x1u << 28) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P28_SECURE (0x0u << 28) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P28_NON_SECURE (0x1u << 28) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P29 (0x1u << 29) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P29_SECURE (0x0u << 29) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P29_NON_SECURE (0x1u << 29) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P30 (0x1u << 30) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P30_SECURE (0x0u << 30) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P30_NON_SECURE (0x1u << 30) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
#define S_PIO_IOSSR_P31 (0x1u << 31) /**< \brief (S_PIO_IOSSR) I/O Security Status */
#define   S_PIO_IOSSR_P31_SECURE (0x0u << 31) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Secure mode. */
#define   S_PIO_IOSSR_P31_NON_SECURE (0x1u << 31) /**< \brief (S_PIO_IOSSR) The I/O line of the I/O group x is in Non-Secure mode. */
/* -------- S_PIO_IOFR : (PIO Offset: N/A) Secure PIO I/O Freeze Register -------- */
#define S_PIO_IOFR_FPHY (0x1u << 0) /**< \brief (S_PIO_IOFR) Freeze Physical Configuration */
#define S_PIO_IOFR_FINT (0x1u << 1) /**< \brief (S_PIO_IOFR) Freeze Interrupt Configuration */
#define S_PIO_IOFR_FRZKEY_Pos 8
#define S_PIO_IOFR_FRZKEY_Msk (0xffffffu << S_PIO_IOFR_FRZKEY_Pos) /**< \brief (S_PIO_IOFR) Freeze Key */
#define S_PIO_IOFR_FRZKEY(value) ((S_PIO_IOFR_FRZKEY_Msk & ((value) << S_PIO_IOFR_FRZKEY_Pos)))
#define   S_PIO_IOFR_FRZKEY_PASSWD (0x494F46u << 8) /**< \brief (S_PIO_IOFR) Writing any other value in this field aborts the write operation of the WPEN bit. */
/* -------- S_PIO_SCDR : (PIO Offset: 0x1500) Secure PIO Slow Clock Divider Debouncing Register -------- */
#define S_PIO_SCDR_DIV_Pos 0
#define S_PIO_SCDR_DIV_Msk (0x3fffu << S_PIO_SCDR_DIV_Pos) /**< \brief (S_PIO_SCDR) Slow Clock Divider Selection for Debouncing */
#define S_PIO_SCDR_DIV(value) ((S_PIO_SCDR_DIV_Msk & ((value) << S_PIO_SCDR_DIV_Pos)))
/* -------- S_PIO_WPMR : (PIO Offset: 0x15E0) Secure PIO Write Protection Mode Register -------- */
#define S_PIO_WPMR_WPEN (0x1u << 0) /**< \brief (S_PIO_WPMR) Write Protection Enable */
#define S_PIO_WPMR_WPKEY_Pos 8
#define S_PIO_WPMR_WPKEY_Msk (0xffffffu << S_PIO_WPMR_WPKEY_Pos) /**< \brief (S_PIO_WPMR) Write Protection Key */
#define S_PIO_WPMR_WPKEY(value) ((S_PIO_WPMR_WPKEY_Msk & ((value) << S_PIO_WPMR_WPKEY_Pos)))
#define   S_PIO_WPMR_WPKEY_PASSWD (0x50494Fu << 8) /**< \brief (S_PIO_WPMR) Writing any other value in this field aborts the write operation of the WPEN bit. Always reads as 0. */
/* -------- S_PIO_WPSR : (PIO Offset: 0x15E4) Secure PIO Write Protection Status Register -------- */
#define S_PIO_WPSR_WPVS (0x1u << 0) /**< \brief (S_PIO_WPSR) Write Protection Violation Status */
#define S_PIO_WPSR_WPVSRC_Pos 8
#define S_PIO_WPSR_WPVSRC_Msk (0xffffu << S_PIO_WPSR_WPVSRC_Pos) /**< \brief (S_PIO_WPSR) Write Protection Violation Source */

/*@}*/


#endif /* _SAMA5D2_PIO_COMPONENT_ */
