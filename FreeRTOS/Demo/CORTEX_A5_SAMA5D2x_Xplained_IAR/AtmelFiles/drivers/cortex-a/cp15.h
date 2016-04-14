/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
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

#ifndef _CP15_H
#define _CP15_H

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define CP15_L4_BIT 15		// Determines if the T bit is set when load instructions
// change the PC:
// 0 = loads to PC set the T bit
// 1 = loads to PC do not set T bit

#define CP15_RR_BIT 14		// RR bit Replacement strategy for Icache and Dcache:
// 0 = Random replacement
// 1 = Round-robin replacement.

#define CP15_V_BIT  13		// V bit Location of exception vectors:
// 0 = Normal exception vectors selected address range = 0x0000 0000 to 0x0000 001C
// 1 = High exception vect selected, address range = 0xFFFF 0000 to 0xFFFF 001C

#define CP15_I_BIT  12		// I bit Icache enable/disable:
// 0 = Icache disabled
// 1 = Icache enabled

#define CP15_R_BIT   9		// R bit ROM protection

#define CP15_S_BIT   8		// S bit System protection

#define CP15_B_BIT   7		// B bit Endianness:
// 0 = Little-endian operation
// 1 = Big-endian operation.

#define CP15_C_BIT   2		// C bit Dcache enable/disable:
// 0 = cache disabled
// 1 = cache enabled

#define CP15_A_BIT   1		// A bit Alignment fault enable/disable:
// 0 = Data address alignment fault checking disabled
// 1 = Data address alignment fault checking enabled

#define CP15_M_BIT   0		// M bit MMU enable/disable: 0 = disabled 1 = enabled.
// 0 = disabled
// 1 = enabled

/** No access Any access generates a domain fault. */
#define CP15_DOMAIN_NO_ACCESS      0x00
/** Client Accesses are checked against the access permission bits in the section or page descriptor. */
#define CP15_DOMAIN_CLIENT_ACCESS  0x01
/** Manager Accesses are not checked against the access permission bits so a permission fault cannot be generated. */
#define CP15_DOMAIN_MANAGER_ACCESS 0x03

#define CP15_ICache             1
#define CP15_DCache             0

#define CP15_PMCNTENSET_ENABLE  31
#define CP15_PMCR_DIVIDER       3
#define CP15_PMCR_RESET         2
#define CP15_PMCR_ENABLE        0

/*------------------------------------------------------------------------------ */
/*         Exported functions */
/*------------------------------------------------------------------------------ */

/**
 * \brief Read the Main ID Register (MIDR).
 * \return register contents
 */
extern unsigned int cp15_read_id(void);

/**
 * \brief Read the System Control Register (SCTLR).
 * \return register contents
 */
extern unsigned int cp15_read_control(void);

/**
 * \brief Indicate CPU that L2 is in exclusive caching mode.
 */
extern void cp15_exclusive_cache(void);

/**
 * \brief Allow data to reside in the L1 and L2 caches at the same time.
 */
extern void cp15_non_exclusive_cache(void);

/**
 * \brief Instruction Synchronization Barrier operation.
 */
extern void cp15_isb(void);

/**
 * \brief Data Synchronization Barrier operation.
 */
extern void cp15_dsb(void);

/**
 * \brief Data Memory Barrier operation.
 */
extern void cp15_dmb(void);

/**
 * \brief Invalidate unified Translation Lookaside Buffer.
 */
extern void cp15_invalidate_tlb(void);

/**
 * \brief Select the data cache as the one to later retrieve architecture
 *      information about.
 */
extern void cp15_select_dcache(void);

/**
 * \brief Select the instruction cache as the one to later retrieve architecture
 *      information about.
 */
extern void cp15_select_icache(void);

/**
 * \brief Modify the System Control Register (SCTLR).
 *      This register specifies the configuration used to enable and disable the
 *      caches and MMU.
 *      It is recommended that you access this register using a read-modify-
 *      write sequence.
 * \param value new value for SCTLR
 */
extern void cp15_write_control(unsigned int value);

/**
 * \brief ARMv7A architecture supports two translation tables.
 *      Configure translation table base (TTB) control register 0.
 * \param value address of our page table base
 */
extern void cp15_write_ttb(unsigned int value);

/**
 * \brief Modify the Domain Access Control Register (DACR).
 * \param value new value for DACR
 */
extern void cp15_write_domain_access_control(unsigned int value);

/**
 * \brief Invalidate I cache predictor array to point of unification Inner
 *      Shareable.
 */
extern void cp15_invalid_icache_inner_sharable(void);

/**
 * \brief Invalidate entire branch predictor array Inner Shareable
 */
extern void cp15_invalid_btb_inner_sharable(void);

/**
 * \brief Invalidate all instruction caches to point of unification.
 *      Also flush branch target cache.
 */
extern void cp15_invalid_icache(void);

/**
 * \brief Invalidate instruction caches by virtual address to point of
 *      unification.
 */
extern void cp15_invalid_icache_by_mva(void);

/**
 * \brief Invalidate entire branch predictor array.
 */
extern void cp15_invalid_btb(void);

/**
 * \brief Invalidate branch predictor array entry by modified virtual address.
 * \param addr virtual address
 */
extern void cp15_invalid_btb_by_mva(uint32_t addr);

/**
 * \brief Invalidate entire data cache by set/way.
 *      Should be called further to cp15_select_dcache(), not
 *      cp15_select_icache().
 */
extern void cp15_invalid_dcache_by_set_way(void);

/**
 * \brief Clean entire data cache by set/way.
 *      Should be called further to cp15_select_dcache(), not
 *      cp15_select_icache().
 */
extern void cp15_clean_dcache_by_set_way(void);

/**
 * \brief Clean and invalidate entire data cache by set/way
 *      Should be called further to cp15_select_dcache(), not
 *      cp15_select_icache().
 */
extern void cp15_clean_invalid_dcache_by_set_way(void);

/**
 * \brief Invalidate data cache by virtual address to point of coherency.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_invalid_dcache_by_mva(uint32_t start, uint32_t end);

/**
 * \brief Clean data cache by modified virtual address to point of coherency.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_clean_dcache_by_mva(uint32_t start, uint32_t end);

/**
 * \brief Clean and invalidate data cache by virtual address to point of
 *      coherency.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_clean_invalid_dcache_by_mva(uint32_t start, uint32_t end);

/**
 * \brief Clean unified cache by modified virtual address to point of
 *      unification.
 */
extern void cp15_clean_dcache_umva(void);

/**
 * \brief Ensure that the I and D caches are coherent within the specified
 *      region. This is typically used when code has been written to
 *      a memory region, and will be executed.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_coherent_dcache_for_dma(uint32_t start, uint32_t end);

/**
 * \brief Invalidate the data cache within the specified region; we will
 *      be performing a DMA operation in this region and we want to purge the
 *      cache of old data. Cache data will be discarded, not flushed.
 *      The specified region should be aligned on cache lines. Otherwise mind
 *      the data loss that may occur in the collateral part of start/end lines,
 *      since cache data won't be flushed.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_invalidate_dcache_for_dma(uint32_t start, uint32_t end);

/**
 * \brief Clean the data cache within the specified region.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_clean_dcache_for_dma(uint32_t start, uint32_t end);

/**
 * \brief Flush, i.e. clean and invalidate, the data cache within the specified
 *      region.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
extern void cp15_flush_dcache_for_dma(uint32_t start, uint32_t end);

/*------------------------------------------------------------------------------ */
/*         Exported functions  from CP15.c                                       */
/*------------------------------------------------------------------------------ */

/** MMU (Status/Enable/Disable) */
extern unsigned int cp15_is_mmu_enabled(void);
extern void cp15_enable_mmu(void);
extern void cp15_disable_mmu(void);

/** I cache (Status/Enable/Disable) */
extern unsigned int cp15_is_icached_enabled(void);
extern void cp15_enable_icache(void);
extern void cp15_disable_icache(void);

/** D cache (Status/Enable/Disable) */
extern unsigned int cp15_is_dcache_enabled(void);
extern void cp15_enable_dcache(void);
extern void cp15_disable_dcache(void);

extern void cp15_dcache_clean(void);
extern void cp15_dcache_invalidate(void);
extern void cp15_icache_invalidate(void);
extern void cp15_dcache_flush(void);
extern void cp15_invalid_dcache_by_va(uint32_t S_Add, uint32_t E_Add);
extern void cp15_clean_dcache_by_va(uint32_t S_Add, uint32_t E_Add);
extern void cp15_flush_dcache_by_va(uint32_t S_Add, uint32_t E_Add);

#endif				// #ifndef _CP15_H
