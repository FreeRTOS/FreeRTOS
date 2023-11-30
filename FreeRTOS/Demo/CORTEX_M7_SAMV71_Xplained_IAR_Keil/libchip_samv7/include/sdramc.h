/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation

 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */
/**
 *  \file
 *
 *  Definitions and function prototype for SDRAMC.
 */

// ----------------------------------------------------------------------------------------------------------
// SDRAM
// ----------------------------------------------------------------------------------------------------------
/**  SDRAMC Configuration */
#define EBI_SDRAMC_ADDR (0x70000000u)

/**  SDRAM bus width */
#define BOARD_SDRAM_BUSWIDTH    16


typedef struct _SSdramc_config
{
  uint32_t dwColumnBits ;                     // Number of Column Bits
  uint32_t dwRowBits ;                        // Number of Row Bits
  uint32_t dwBanks ;                          // Number of Banks
  uint32_t dwCAS ;                            // CAS Latency
  uint32_t dwDataBusWidth ;                   // Data Bus Width
  uint32_t dwWriteRecoveryDelay ;             // Write Recovery Delay
  uint32_t dwRowCycleDelay_RowRefreshCycle ;  // Row Cycle Delay and Row Refresh Cycle
  uint32_t dwRowPrechargeDelay ;              // Row Precharge Delay
  uint32_t dwRowColumnDelay ;                 // Row to Column Delay
  uint32_t dwActivePrechargeDelay ;           // Active to Precharge Delay
  uint32_t dwExitSelfRefreshActiveDelay ;     // Exit Self Refresh to Active Delay
  uint32_t dwBK1 ;                            // bk1 addr

} SSdramc_config ;

typedef struct _SSdramc_Memory
{
  SSdramc_config cfg ;

} SSdramc_Memory ;

extern void SDRAMC_Configure( SSdramc_Memory* pMemory, uint32_t dwClockFrequency ) ;
