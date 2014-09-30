/******************************************************************************
 *
 * Copyright 2013 Altera Corporation. All Rights Reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 * 
 * 3. The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 * 
 ******************************************************************************/

#include "alt_cache.h"
#include "alt_interrupt_common.h"
#include "alt_mmu.h"
#include "socal/alt_sysmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"
#include <stdio.h>
#include <inttypes.h>

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf  printf

/////

#ifndef MIN
#define MIN(a, b) ((a) > (b) ? (b) : (a))
#endif

/////

// System Level API here

ALT_STATUS_CODE alt_cache_system_enable(void)
{
    alt_cache_l1_enable_all();

    alt_cache_l2_init();
    alt_cache_l2_prefetch_enable();
    alt_cache_l2_parity_enable();
    alt_cache_l2_enable();

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_system_disable(void)
{
    alt_cache_l2_disable();
    alt_cache_l2_parity_disable();
    alt_cache_l2_prefetch_disable();
    alt_cache_l2_uninit();

    alt_cache_l1_disable_all();

    return ALT_E_SUCCESS;
}

#define ALT_CPU_PAR_FS_VALUE_GET(par) ((par >> 1) & 0x3f)
#define ALT_CPU_PAR_SS_SET_MSK 0x00000002
#define ALT_CPU_PAR_F_SET_MSK  0x00000001

static inline uintptr_t alt_mmu_va_to_pa(void * va, uint32_t * seglength, uint32_t * dfsr)
{
#if ALT_CACHE_SUPPORT_NON_FLAT_VIRTUAL_MEMORY

    uintptr_t pa = 0;

    // ATS1CPR [Address Translate Stage 1 Current state PL1 Read]; See ARMv7-A,R, section B4.2.4.
    // ISB
    // Read the PAR
#ifdef __ARMCC_VERSION
    __asm("mcr p15, 0, va, c7, c8, 0");
    __asm("isb");
    __asm("mrc p15, 0, pa, c7, c4, 0");
#else
    __asm("mcr p15, 0, %0, c7, c8, 0" : : "r" (va));
    __asm("isb");
    __asm("mrc p15, 0, %0, c7, c4, 0" : "=r" (pa));
#endif

    if (pa & ALT_CPU_PAR_F_SET_MSK)
    {
        // If the F bit (fault) is set, then report the error.

        // Extract the PAR::FS field value.
        uint32_t fs = ALT_CPU_PAR_FS_VALUE_GET(pa);

        // Translate PAR::FS[5:0] (field value) or PAR[6:1] => DFSR[12,10,3:0] to report error.
        *dfsr = ((fs & 0x20) << 7) | // bit 12
                ((fs & 0x10) << 6) | // bit 10
                ((fs & 0x0f) << 0);  // bit 3:0

        dprintf("DEBUG[cache][va->pa]: Fault detected. DFSR = 0x%" PRIx32 ".\n", dfsr);
    }
    else if (pa & ALT_CPU_PAR_SS_SET_MSK)
    {
        // If the page is a supersection, PAR contains PA[31:24]. VA contains PA[23:0].

        uint32_t offset = (uintptr_t)va & (ALT_MMU_SUPERSECTION_SIZE - 1);
        pa &= ~(ALT_MMU_SUPERSECTION_SIZE - 1);
        pa |= offset;

        dprintf("DEBUG[cache][va->pa]: pa[SS] = 0x%x; offset = 0x%" PRIx32 ".\n",
                pa & ~(ALT_MMU_SUPERSECTION_SIZE - 1),
                offset);

        *seglength = ALT_MMU_SUPERSECTION_SIZE - offset;
        *dfsr      = 0;
    }
    else
    {
        // If the page is not a supersection, PAR contains PA[31:12]. VA contains PA[11:0].

        uint32_t offset = (uintptr_t)va & (ALT_MMU_SMALL_PAGE_SIZE - 1);
        pa &= ~(ALT_MMU_SMALL_PAGE_SIZE - 1);
        pa |= offset;

        dprintf("DEBUG[cache][va->pa]: pa[page] = 0x%x; offset = 0x%" PRIx32 ".\n",
                pa & ~(ALT_MMU_SMALL_PAGE_SIZE - 1),
                offset);

        *seglength = ALT_MMU_SMALL_PAGE_SIZE - offset;
        *dfsr      = 0;
    }

    return pa;

#else

    *seglength = 0xffffffff - (uintptr_t)va + 1;
    *dfsr      = 0;
    return (uintptr_t)va;

#endif
}

// Internal functions that expect all inputs to be aligned properly.

static void alt_cache_l1_data_invalidate_helper(void * vaddress, size_t length);
static void alt_cache_l1_data_clean_helper(void * vaddress, size_t length);
static void alt_cache_l1_data_purge_helper(void * vaddress, size_t length);

static ALT_STATUS_CODE alt_cache_l2_invalidate_helper(uintptr_t paddress, size_t length);
static ALT_STATUS_CODE alt_cache_l2_clean_helper(uintptr_t paddress, size_t length);
static ALT_STATUS_CODE alt_cache_l2_purge_helper(uintptr_t paddress, size_t length);

ALT_STATUS_CODE alt_cache_system_invalidate(void * vaddress, size_t length)
{
    // Verify preconditions:
    //  - address and length are on the cache boundaries
    if (((uintptr_t)vaddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    dprintf("DEBUG[cache][sys]: invalidate: vaddr = %p; length = 0x%x.\n", vaddress, length);

    char * va = vaddress;

    while (length)
    {
        uint32_t  dfsr     = 0;
        uint32_t  seg_size = 0;
        uintptr_t pa       = alt_mmu_va_to_pa(va, &seg_size, &dfsr);
        if (dfsr)
        {
            return ALT_E_ERROR;
        }

        seg_size = MIN(length, seg_size);

        dprintf("DEBUG[cache][sys]: (loop): va = %p; pa = 0x%x; size = 0x%" PRIx32 ".\n", va, pa, seg_size);

        alt_cache_l2_invalidate_helper(pa, seg_size);
        alt_cache_l2_sync();
        alt_cache_l1_data_invalidate_helper(va, seg_size);
        // __asm("dsb") handled by l1_data_invalidate().

        va     += seg_size;
        length -= seg_size;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_system_clean(void * vaddress, size_t length)
{
    // Verify preconditions:
    //  - address and length are on the cache boundaries
    if (((uintptr_t)vaddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    dprintf("DEBUG[cache][sys]: clean: vaddr = %p; length = 0x%x.\n", vaddress, length);

    char * va = vaddress;

    while (length)
    {
        uint32_t  dfsr     = 0;
        uint32_t  seg_size = 0;
        uintptr_t pa       = alt_mmu_va_to_pa(va, &seg_size, &dfsr);
        if (dfsr)
        {
            return ALT_E_ERROR;
        }

        seg_size = MIN(length, seg_size);

        dprintf("DEBUG[cache][sys]: (loop): va = %p; pa = 0x%x; size = 0x%" PRIx32 ".\n", va, pa, seg_size);

        alt_cache_l1_data_clean_helper(va, seg_size);
        // __asm("dsb") handled by l1_data_clean().
        alt_cache_l2_clean_helper(pa, seg_size);
        alt_cache_l2_sync();

        va     += seg_size;
        length -= seg_size;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_system_purge(void * vaddress, size_t length)
{
    // Verify preconditions:
    //  - address and length are on the cache boundaries
    if (((uintptr_t)vaddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    dprintf("DEBUG[cache][sys]: clean: vaddr = %p; length = 0x%x.\n", vaddress, length);

    char * va = vaddress;

    while (length)
    {
        uint32_t  dfsr     = 0;
        uint32_t  seg_size = 0;
        uintptr_t pa       = alt_mmu_va_to_pa(va, &seg_size, &dfsr);
        if (dfsr)
        {
            return ALT_E_ERROR;
        }

        seg_size = MIN(length, seg_size);

        dprintf("DEBUG[cache][sys]: (loop): va = %p; pa = 0x%x; size = 0x%" PRIx32 ".\n", va, pa, seg_size);

        alt_cache_l1_data_clean_helper(va, seg_size);
        // __asm("dsb") handled by l1_data_clean().
        alt_cache_l2_purge_helper(pa, seg_size);
        alt_cache_l2_sync();
        alt_cache_l1_data_invalidate_helper(va, seg_size);
        // __asm("dsb") handled by l1_data_invalidate().

        va     += seg_size;
        length -= seg_size;
    }

    return ALT_E_SUCCESS;
}

/////

//
// Stand-in SoCAL for ARM CPU registers needed for L1 cache functions.
//

// System Control Register. See Cortex-A9, section 4.3.9.
#define ALT_CPU_SCTLR_TE_SET_MSK   (1 << 30)
#define ALT_CPU_SCTLR_AFE_SET_MSK  (1 << 29)
#define ALT_CPU_SCTLR_TRE_SET_MSK  (1 << 28)
#define ALT_CPU_SCTLR_NMFI_SET_MSK (1 << 27)
#define ALT_CPU_SCTLR_EE_SET_MSK   (1 << 25)
#define ALT_CPU_SCTLR_HA_SET_MSK   (1 << 17)
#define ALT_CPU_SCTLR_RR_SET_MSK   (1 << 14)
#define ALT_CPU_SCTLR_V_SET_MSK    (1 << 13)
#define ALT_CPU_SCTLR_I_SET_MSK    (1 << 12)
#define ALT_CPU_SCTLR_Z_SET_MSK    (1 << 11)
#define ALT_CPU_SCTLR_SW_SET_MSK   (1 << 10)
#define ALT_CPU_SCTLR_C_SET_MSK    (1 <<  2)
#define ALT_CPU_SCTLR_A_SET_MSK    (1 <<  1)
#define ALT_CPU_SCTLR_M_SET_MSK    (1 <<  0)

// Auxiliary Control Register. See Cortex-A9, section 4.3.10.
#define ALT_CPU_ACTLR_PARITYON_SET_MSK           (1 << 9)
#define ALT_CPU_ACTLR_ALLOCINONEWAY_SET_MSK      (1 << 8)
#define ALT_CPU_ACTLR_EXCL_SET_MSK               (1 << 7)
#define ALT_CPU_ACTLR_SMP_SET_MSK                (1 << 6)
#define ALT_CPU_ACTLR_WRITEFULLLINEZEROS_SET_MSK (1 << 3)
#define ALT_CPU_ACTLR_L1PREFETCHEN_SET_MSK       (1 << 2)
#define ALT_CPU_ACTLR_L2PREFETCHEN_SET_MSK       (1 << 1)
#define ALT_CPU_ACTLR_FW_SET_MSK                 (1 << 0)

// Cache Size Selection Register. See Cortex-A9, section 4.3.8.
#define ALT_CPU_ACTLR_LEVEL_SET_MSK (7 << 1)
#define ALT_CPU_ACTLR_IND_SET_MSK   (1 << 0)

// Cache Size Identification Register. See Cortex-A9, section 4.3.5.
#define ALT_CPU_CCSIDR_WT_SET_MSK            (0x1    << 31)
#define ALT_CPU_CCSIDR_WB_SET_MSK            (0x1    << 30)
#define ALT_CPU_CCSIDR_RA_SET_MSK            (0x1    << 29)
#define ALT_CPU_CCSIDR_WA_SET_MSK            (0x1    << 28)
#define ALT_CPU_CCSIDR_NUMSETS_SET_MSK       (0x7fff << 13)
#define ALT_CPU_CCSIDR_ASSOCIATIVITY_SET_MSK (0x3ff  <<  3)
#define ALT_CPU_CCSIDR_LINESIZE_SET_MSK      (0x7    <<  0)

#define ALT_CPU_CCSIDR_NUMSETS_VALUE_GET(value)       (((value) & ALT_CPU_CCSIDR_NUMSETS_SET_MSK)       >> 13)
#define ALT_CPU_CCSIDR_ASSOCIATIVITY_VALUE_GET(value) (((value) & ALT_CPU_CCSIDR_ASSOCIATIVITY_SET_MSK) >>  3)
#define ALT_CPU_CCSIDR_LINESIZE_VALUE_GET(value)      (((value) & ALT_CPU_CCSIDR_LINESIZE_SET_MSK)      >>  0)

/////

static inline __attribute__((always_inline)) uint32_t sctlr_read_helper(void)
{
    uint32_t sctlr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, sctlr, c1, c0, 0");
#else
    __asm("MRC p15, 0, %0,    c1, c0, 0" : "=r" (sctlr));
#endif

    return sctlr;
}

static inline __attribute__((always_inline)) void sctlr_write_helper(uint32_t sctlr)
{
#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, sctlr, c1, c0, 0");
#else
    __asm("MCR p15, 0, %0,    c1, c0, 0" : : "r" (sctlr));
#endif
}

static inline __attribute__((always_inline)) uint32_t actlr_read_helper(void)
{
    uint32_t actlr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, actlr, c1, c0, 1");
#else
    __asm("MRC p15, 0, %0,    c1, c0, 1" : "=r" (actlr));
#endif

    return actlr;
}

static inline __attribute__((always_inline)) void actlr_write_helper(uint32_t actlr)
{
#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, actlr, c1, c0, 1");
#else
    __asm("MCR p15, 0, %0,    c1, c0, 1" : : "r" (actlr));
#endif
}

static void cssidr_decode_helper(bool query_i_cache, uint32_t * log2_L, uint32_t * log2_A, uint32_t * log2_S)
{
    // First query the D cache information using CSSELR to select the data cache
    // See ARM Cortex-A9 TRM, section 4.3.8.

    // Wait for the CSSELR to flush.

    // Then use CSSIDR to get the cache charateristics
    // See ARMv7-A,R, section B4.1.19

    uint32_t csselr;
    uint32_t cssidr;

    if (query_i_cache)
    {
        csselr = ALT_CPU_ACTLR_IND_SET_MSK;
    }
    else
    {
        csselr = 0;
    }

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 2, csselr, c0, c0, 0");
    __asm("ISB");
    __asm("MRC p15, 1, cssidr, c0, c0, 0");
#else
    __asm("MCR p15, 2, %0, c0, c0, 0" : : "r" (csselr));
    __asm("ISB");
    __asm("MRC p15, 1, %0, c0, c0, 0" : "=r" (cssidr));
#endif

    // Extract the associativity, line length, and number of sets.
    int linesize      = ALT_CPU_CCSIDR_LINESIZE_VALUE_GET(cssidr) + 2 + 2; // {log2(line length in words) - 2} + 2 + 2 => (... in bytes)
    int associativity = ALT_CPU_CCSIDR_ASSOCIATIVITY_VALUE_GET(cssidr) + 1;
    int numsets       = ALT_CPU_CCSIDR_NUMSETS_VALUE_GET(cssidr) + 1;

    // Determine the log2 of the associativity and numsets, rounded up
    int L = linesize; // log2(line length in bytes)
    int A = 0;        // log2(associativity) rounded up
    int S = 0;        // log2(number of sets) rounded up

    while ((1 << A) < associativity)
    {
        ++A;
    }

    while ((1 << S) < numsets)
    {
        ++S;
    }

    // Output the parameters
    *log2_L = L;
    *log2_A = A;
    *log2_S = S;
}

/////

ALT_STATUS_CODE alt_cache_l1_enable_all(void)
{
    alt_cache_l1_disable_all();

    // Parity should be turned on before anything else.
    alt_cache_l1_parity_enable();
    alt_cache_l1_instruction_enable();
    alt_cache_l1_data_enable();
    alt_cache_l1_branch_enable();
    alt_cache_l1_prefetch_enable();

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_disable_all(void)
{
    alt_cache_l1_parity_disable();
    alt_cache_l1_instruction_disable();
    alt_cache_l1_data_disable();
    alt_cache_l1_branch_disable();
    alt_cache_l1_prefetch_disable();

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_instruction_enable(void)
{
    // Update SCTLR.I bit (bit 12)
    // See Cortex-A9 TRM, section 4.3.9

    uint32_t sctlr = sctlr_read_helper();
    if ((sctlr & ALT_CPU_SCTLR_I_SET_MSK) == 0)
    {
        alt_cache_l1_instruction_invalidate();

        sctlr |= ALT_CPU_SCTLR_I_SET_MSK;
        sctlr_write_helper(sctlr);     
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_instruction_disable(void)
{
    // Update SCTLR.I bit (bit 12)
    // See Cortex-A9 TRM, section 4.3.9

    uint32_t sctlr = sctlr_read_helper();
    sctlr &= ~ALT_CPU_SCTLR_I_SET_MSK;
    sctlr_write_helper(sctlr);

    return ALT_E_SUCCESS;
}

bool alt_cache_l1_instruction_is_enabled(void)
{
    // Query SCTLR.I bit (bit 12)
    // See Cortex-A9 TRM, section 4.3.9

    uint32_t sctlr = sctlr_read_helper();
    if ( (sctlr & ALT_CPU_SCTLR_I_SET_MSK) != 0 )
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_STATUS_CODE alt_cache_l1_instruction_invalidate(void)
{
    // Issue the ICIALLUIS (Instruction Cache Invalidate ALL to point of
    // Unification Inner Shareable) cache maintenance operation
    // See ARMv7-A,R, section B4.2.1.

    uint32_t dummy = 0;

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, dummy, c7, c1, 0");
#else
    __asm("MCR p15, 0, %0,    c7, c1, 0" : : "r" (dummy));
#endif

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_data_enable(void)
{
    // Update SCTLR.C bit (bit 2)
    // See Cortex-A9 TRM, section 4.3.9

    uint32_t sctlr = sctlr_read_helper();
    if ((sctlr & ALT_CPU_SCTLR_C_SET_MSK) == 0)
    {
        alt_cache_l1_data_invalidate_all();
        
        sctlr |= ALT_CPU_SCTLR_C_SET_MSK;
        sctlr_write_helper(sctlr);
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_data_disable(void)
{
    // Update SCTLR.C bit (bit 2)
    // See Cortex-A9 TRM, section 4.3.9

    uint32_t sctlr = sctlr_read_helper();
    if ((sctlr & ALT_CPU_SCTLR_C_SET_MSK) != 0)
    {
        alt_cache_l1_data_clean_all();

        sctlr &= ~ALT_CPU_SCTLR_C_SET_MSK;

        sctlr_write_helper(sctlr);
    }

    return ALT_E_SUCCESS;
}

bool alt_cache_l1_data_is_enabled(void)
{
    // Query SCTLR.C bit (bit 2)
    // See Cortex-A9 TRM, section 4.3.9

    uint32_t sctlr = sctlr_read_helper();
    if ( (sctlr & ALT_CPU_SCTLR_C_SET_MSK) != 0 )
    {
        return true;
    }
    else
    {
        return false;
    }
}

static void alt_cache_l1_data_invalidate_helper(void * vaddress, size_t length)
{
    // Repeatedly call DCIMVAC (Data Cache Invalidate by Modified Virtual
    // Address to the point of Coherency) and loop for the length of the
    // segment.

    // The DCIMVAC uses the MVA format for the register. This is simply the
    // virtual address of the line to be invalidated.
    // See ARMv7-A,R, section B4.2.1.

    for (uintptr_t va = (uintptr_t)vaddress; va < (uintptr_t)vaddress + length; va += ALT_CACHE_LINE_SIZE)
    {
#ifdef __ARMCC_VERSION
        __asm("MCR p15, 0, va, c7, c6, 1");
#else
        __asm("MCR p15, 0, %0, c7, c6, 1" : : "r" (va));
#endif
    }

    // Ensure all cache maintenance operations complete before returning.
    __asm("dsb");
}

ALT_STATUS_CODE alt_cache_l1_data_invalidate(void * vaddress, size_t length)
{
    // Verify preconditions:
    //  - length is non-zero
    //  - address and length are on the cache boundaries
    if (length == 0)
    {
        return ALT_E_BAD_ARG;
    }
    if (((uintptr_t)vaddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    alt_cache_l1_data_invalidate_helper(vaddress, length);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_data_invalidate_all(void)
{
    // Gather parameters for DCISW (Data Cache Invalidate by Set / Way) data format.
    // See ARMv7-A,R, section B4.2.1

    // Query the log2(line size in bytes), log2(associativity), log2(set count) for the data cache.

    uint32_t L = 0;
    uint32_t A = 0;
    uint32_t S = 0;

    cssidr_decode_helper(false, &L, &A, &S);

    // Repeatedly call DCISW and loop for every cache way and set.

    for (int way = 0; way < (1 << A); ++way)
    {
        for (int set = 0; set < (1 << S); ++set)
        {
            uint32_t way_set_info = 0;
            way_set_info |= way << (32 - A);
            way_set_info |= set << (L);
            // Level is 0 because we're invalidating the L1.

#ifdef __ARMCC_VERSION
            __asm("MCR p15, 0, way_set_info, c7, c6, 2");
#else
            __asm("MCR p15, 0, %0,           c7, c6, 2" : : "r" (way_set_info));
#endif
        }
    }

    // Ensure all cache maintenance operations complete before returning.
    __asm("dsb");

    return ALT_E_SUCCESS;
}

static void alt_cache_l1_data_clean_helper(void * vaddress, size_t length)
{
    // Repeatedly call DCCMVAC (Data Cache Clean by Modified Virtual Address to
    // point of Coherency) and loop for the length of the segment.

    // The DCCMVAC uses the MVA format for the register. This is simply the
    // virtual address of the line to be invalidated.
    // See ARMv7-A,R, section B4.2.1.

    for (uintptr_t va = (uintptr_t)vaddress; va < (uintptr_t)vaddress + length; va += ALT_CACHE_LINE_SIZE)
    {
#ifdef __ARMCC_VERSION
        __asm("MCR p15, 0, va, c7, c10, 1");
#else
        __asm("MCR p15, 0, %0, c7, c10, 1" : : "r" (va));
#endif
    }

    // Ensure all cache maintenance operations complete before returning.
    __asm("dsb");
}

ALT_STATUS_CODE alt_cache_l1_data_clean(void * vaddress, size_t length)
{
    // Verify preconditions:
    //  - length is non-zero
    //  - address and length are on the cache boundaries
    if (length == 0)
    {
        return ALT_E_BAD_ARG;
    }
    if (((uintptr_t)vaddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    alt_cache_l1_data_clean_helper(vaddress, length);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_data_clean_all(void)
{
    // Gather parameters for DCCSW (Data Cache Clean by Set / Way) data format
    // See ARMv7-A,R, section B4.2.1

    // Query the log2(line size in bytes), log2(associativity), log2(set count) for the data cache.

    uint32_t L = 0;
    uint32_t A = 0;
    uint32_t S = 0;

    cssidr_decode_helper(false, &L, &A, &S);

    // Repeatedly call DCCSW and loop for every cache way and set.

    for (int way = 0; way < (1 << A); ++way)
    {
        for (int set = 0; set < (1 << S); ++set)
        {
            uint32_t way_set_info = 0;
            way_set_info |= way << (32 - A);
            way_set_info |= set << (L);
            // Level is 0 because we're invalidating the L1.

#ifdef __ARMCC_VERSION
            __asm("MCR p15, 0, way_set_info, c7, c10, 2");
#else
            __asm("MCR p15, 0, %0,           c7, c10, 2" : : "r" (way_set_info));
#endif
        }
    }

    // Ensure all cache maintenance operations complete before returning.
    __asm("dsb");

    return ALT_E_SUCCESS;
}

static void alt_cache_l1_data_purge_helper(void * vaddress, size_t length)
{
    // Repeatedly call DCCIMVAC (Data Cache Clean and Invalidate by Modified
    // Virtual Address to point of Coherency) and loop for the length of the
    // segment.

    // The DCCIMVAC uses the MVA format for the register. This is simply the
    // virtual address of the line to be invalidated.
    // See ARMv7-A,R, section B4.2.1.

    for (uintptr_t va = (uintptr_t)vaddress; va < (uintptr_t)vaddress + length; va += ALT_CACHE_LINE_SIZE)
    {
#ifdef __ARMCC_VERSION
        __asm("MCR p15, 0, va, c7, c14, 1");
#else
        __asm("MCR p15, 0, %0, c7, c14, 1" : : "r" (va));
#endif
    }

    // Ensure all cache maintenance operations complete before returning.
    __asm("dsb");
}

ALT_STATUS_CODE alt_cache_l1_data_purge(void * vaddress, size_t length)
{
    // Verify preconditions:
    //  - length is non-zero
    //  - address and length are on the cache boundaries
    if (length == 0)
    {
        return ALT_E_BAD_ARG;
    }
    if (((uintptr_t)vaddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    alt_cache_l1_data_purge_helper(vaddress, length);

    return ALT_E_SUCCESS;

}

ALT_STATUS_CODE alt_cache_l1_data_purge_all(void)
{
    // Gather parameters for DCCISW (Data Cache Clean and Invalidate by Set / Way) data format
    // See ARMv7-A,R, section B4.2.1

    // Query the log2(line size in bytes), log2(associativity), log2(set count) for the data cache.

    uint32_t L = 0;
    uint32_t A = 0;
    uint32_t S = 0;

    cssidr_decode_helper(false, &L, &A, &S);

    // Repeatedly call DCCISW and loop for every cache way and set.

    for (int way = 0; way < (1 << A); ++way)
    {
        for (int set = 0; set < (1 << S); ++set)
        {
            uint32_t way_set_info = 0;
            way_set_info |= way << (32 - A);
            way_set_info |= set << (L);
            // Level is 0 because we're invalidating the L1.

#ifdef __ARMCC_VERSION
            __asm("MCR p15, 0, way_set_info, c7, c14, 2");
#else
            __asm("MCR p15, 0, %0,           c7, c14, 2" : : "r" (way_set_info));
#endif
        }
    }

    // Ensure all cache maintenance operations complete before returning.
    __asm("dsb");

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_parity_enable(void)
{
    uint32_t actlr = actlr_read_helper();
    if ((actlr & ALT_CPU_ACTLR_PARITYON_SET_MSK) == 0)
    {
        // Determine which caches which will be affected by parity being enabled
        // are currently enabled.
        bool dcache_en = alt_cache_l1_data_is_enabled();
        bool icache_en = alt_cache_l1_instruction_is_enabled();
        bool branch_en = alt_cache_l1_branch_is_enabled();

        // For those caches, disable them temporarily
        if (icache_en == true)
        {
            alt_cache_l1_instruction_disable();
        }
        if (dcache_en == true)
        {
            alt_cache_l1_data_disable();
        }
        if (branch_en == true)
        {
            alt_cache_l1_branch_disable();
        }

        // Turn on parity in the L1.
        actlr |= ALT_CPU_ACTLR_PARITYON_SET_MSK;
        actlr_write_helper(actlr);

        // Now enable them again.
        if (icache_en == true)
        {
            alt_cache_l1_instruction_enable();
        }
        if (dcache_en == true)
        {
            alt_cache_l1_data_enable();
        }
        if (branch_en == true)
        {
            alt_cache_l1_branch_enable();
        }
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_parity_disable(void)
{
    uint32_t actlr = actlr_read_helper();
    actlr &= ~ALT_CPU_ACTLR_PARITYON_SET_MSK;
    actlr_write_helper(actlr);

    return ALT_E_SUCCESS;
}

bool alt_cache_l1_parity_is_enabled(void)
{
    uint32_t actlr = actlr_read_helper();
    if ((actlr & ALT_CPU_ACTLR_PARITYON_SET_MSK) != 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_STATUS_CODE alt_cache_l1_branch_enable(void)
{
    alt_cache_l1_branch_invalidate();

    uint32_t sctlr = sctlr_read_helper();
    sctlr |= ALT_CPU_SCTLR_Z_SET_MSK;
    sctlr_write_helper(sctlr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_branch_disable(void)
{
    uint32_t sctlr = sctlr_read_helper();
    sctlr &= ~ALT_CPU_SCTLR_Z_SET_MSK;
    sctlr_write_helper(sctlr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_branch_invalidate(void)
{
    // Issue BPIALLIS (Branch Predictor Invalidate ALL, Inner Shareable).

    uint32_t dummy = 0;

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, dummy, c7, c1, 6");
#else
    __asm("MCR p15, 0, %0,    c7, c1, 6" : : "r" (dummy));
#endif

    // Ensure all branch predictor maintenance operations complete before returning.
    __asm("dsb");

    return ALT_E_SUCCESS;
}

bool alt_cache_l1_branch_is_enabled(void)
{
    uint32_t sctlr = sctlr_read_helper();
    if ((sctlr & ALT_CPU_SCTLR_Z_SET_MSK) != 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_STATUS_CODE alt_cache_l1_prefetch_enable(void)
{
    uint32_t actlr = actlr_read_helper();
    actlr |= ALT_CPU_ACTLR_L1PREFETCHEN_SET_MSK;
    actlr_write_helper(actlr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l1_prefetch_disable(void)
{
    uint32_t actlr = actlr_read_helper();
    actlr &= ~ALT_CPU_ACTLR_L1PREFETCHEN_SET_MSK;
    actlr_write_helper(actlr);

    return ALT_E_SUCCESS;
}

bool alt_cache_l1_prefetch_is_enabled(void)
{
    uint32_t actlr = actlr_read_helper();
    if ((actlr & ALT_CPU_ACTLR_L1PREFETCHEN_SET_MSK) != 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}

/////

//
// Stand-in SoCAL for MPU L2 registers.
//
// All offsets are from ALT_MPUL2_OFST.
//

#define ALT_MPUL2_CACHE_ID_OFST             0x000
#define ALT_MPUL2_CACHE_TYPE_OFST           0x004
#define ALT_MPUL2_CONTROL_OFST              0x100
#define ALT_MPUL2_AUX_CONTROL_OFST          0x104
#define ALT_MPUL2_TAG_RAM_CONTROL_OFST      0x108
#define ALT_MPUL2_DATA_RAM_CONTROL_OFST     0x10c
#define ALT_MPUL2_EV_COUNTER_CTRL_OFST      0x200
#define ALT_MPUL2_EV_COUNTER1_CFG_OFST      0x204
#define ALT_MPUL2_EV_COUNTER0_CFG_OFST      0x208
#define ALT_MPUL2_EV_COUNTER1_OFST          0x20c
#define ALT_MPUL2_EV_COUNTER0_OFST          0x210
#define ALT_MPUL2_INT_MASK_OFST             0x214
#define ALT_MPUL2_INT_MASK_STATUS_OFST      0x218
#define ALT_MPUL2_INT_RAW_STATUS_OFST       0x21c
#define ALT_MPUL2_INT_CLEAR_OFST            0x220
#define ALT_MPUL2_CACHE_SYNC_OFST           0x730
#define ALT_MPUL2_INV_PA_OFST               0x770
#define ALT_MPUL2_INV_WAY_OFST              0x77c
#define ALT_MPUL2_CLEAN_PA_OFST             0x7b0
#define ALT_MPUL2_CLEAN_INDEX_OFST          0x7b8
#define ALT_MPUL2_CLEAN_WAY_OFST            0x7bc
#define ALT_MPUL2_CLEAN_INV_PA_OFST         0x7f0
#define ALT_MPUL2_CLEAN_INV_INDEX_OFST      0x7f8
#define ALT_MPUL2_CLEAN_INV_WAY_OFST        0x7fc
#define ALT_MPUL2_D_LOCKDOWN0_OFST          0x900
#define ALT_MPUL2_I_LOCKDOWN0_OFST          0x904
#define ALT_MPUL2_D_LOCKDOWN1_OFST          0x908
#define ALT_MPUL2_I_LOCKDOWN1_OFST          0x90c
#define ALT_MPUL2_D_LOCKDOWN2_OFST          0x910
#define ALT_MPUL2_I_LOCKDOWN2_OFST          0x914
#define ALT_MPUL2_D_LOCKDOWN3_OFST          0x918
#define ALT_MPUL2_I_LOCKDOWN3_OFST          0x91c
#define ALT_MPUL2_D_LOCKDOWN4_OFST          0x920
#define ALT_MPUL2_I_LOCKDOWN4_OFST          0x924
#define ALT_MPUL2_D_LOCKDOWN5_OFST          0x928
#define ALT_MPUL2_I_LOCKDOWN5_OFST          0x92c
#define ALT_MPUL2_D_LOCKDOWN6_OFST          0x930
#define ALT_MPUL2_I_LOCKDOWN6_OFST          0x934
#define ALT_MPUL2_D_LOCKDOWN7_OFST          0x938
#define ALT_MPUL2_I_LOCKDOWN7_OFST          0x93c
#define ALT_MPUL2_D_LOCKDOWNx_OFST(x)       (0x900 + ((x) * 0x8))
#define ALT_MPUL2_I_LOCKDOWNx_OFST(x)       (0x904 + ((x) * 0x8))
#define ALT_MPUL2_LOCK_LINE_EN_OFST         0x950
#define ALT_MPUL2_UNLOCK_WAY_OFST           0x954
#define ALT_MPUL2_ADDR_FILTERING_START_OFST 0xc00
#define ALT_MPUL2_ADDR_FILTERING_END_OFST   0xc04
#define ALT_MPUL2_DEBUG_CTRL_OFST           0xf40
#define ALT_MPUL2_PREFETCH_CTRL_OFST        0xf60
#define ALT_MPUL2_POWER_CTRL_OFST           0xf80

#define ALT_MPUL2_CACHE_ID_ADDR             ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CACHE_ID_OFST))
#define ALT_MPUL2_CACHE_TYPE_ADDR           ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CACHE_TYPE_OFST))
#define ALT_MPUL2_CONTROL_ADDR              ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CONTROL_OFST))
#define ALT_MPUL2_AUX_CONTROL_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_AUX_CONTROL_OFST))
#define ALT_MPUL2_TAG_RAM_CONTROL_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_TAG_RAM_CONTROL_OFST))
#define ALT_MPUL2_DATA_RAM_CONTROL_ADDR     ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_DATA_RAM_CONTROL_OFST))
#define ALT_MPUL2_EV_COUNTER_CTRL_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_EV_COUNTER_CTRL_OFST))
#define ALT_MPUL2_EV_COUNTER1_CFG_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_EV_COUNTER1_CFG_OFST))
#define ALT_MPUL2_EV_COUNTER0_CFG_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_EV_COUNTER0_CFG_OFST))
#define ALT_MPUL2_EV_COUNTER1_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_EV_COUNTER1_OFST))
#define ALT_MPUL2_EV_COUNTER0_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_EV_COUNTER0_OFST))
#define ALT_MPUL2_INT_MASK_ADDR             ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_INT_MASK_OFST))
#define ALT_MPUL2_INT_MASK_STATUS_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_INT_MASK_STATUS_OFST))
#define ALT_MPUL2_INT_RAW_STATUS_ADDR       ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_INT_RAW_STATUS_OFST))
#define ALT_MPUL2_INT_CLEAR_ADDR            ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_INT_CLEAR_OFST))
#define ALT_MPUL2_CACHE_SYNC_ADDR           ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CACHE_SYNC_OFST))
#define ALT_MPUL2_INV_PA_ADDR               ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_INV_PA_OFST))
#define ALT_MPUL2_INV_WAY_ADDR              ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_INV_WAY_OFST))
#define ALT_MPUL2_CLEAN_PA_ADDR             ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CLEAN_PA_OFST))
#define ALT_MPUL2_CLEAN_INDEX_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CLEAN_INDEX_OFST))
#define ALT_MPUL2_CLEAN_WAY_ADDR            ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CLEAN_WAY_OFST))
#define ALT_MPUL2_CLEAN_INV_PA_ADDR         ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CLEAN_INV_PA_OFST))
#define ALT_MPUL2_CLEAN_INV_INDEX_ADDR      ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CLEAN_INV_INDEX_OFST))
#define ALT_MPUL2_CLEAN_INV_WAY_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_CLEAN_INV_WAY_OFST))
#define ALT_MPUL2_D_LOCKDOWN0_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN0_OFST))
#define ALT_MPUL2_I_LOCKDOWN0_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN0_OFST))
#define ALT_MPUL2_D_LOCKDOWN1_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN1_OFST))
#define ALT_MPUL2_I_LOCKDOWN1_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN1_OFST))
#define ALT_MPUL2_D_LOCKDOWN2_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN2_OFST))
#define ALT_MPUL2_I_LOCKDOWN2_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN2_OFST))
#define ALT_MPUL2_D_LOCKDOWN3_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN3_OFST))
#define ALT_MPUL2_I_LOCKDOWN3_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN3_OFST))
#define ALT_MPUL2_D_LOCKDOWN4_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN4_OFST))
#define ALT_MPUL2_I_LOCKDOWN4_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN4_OFST))
#define ALT_MPUL2_D_LOCKDOWN5_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN5_OFST))
#define ALT_MPUL2_I_LOCKDOWN5_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN5_OFST))
#define ALT_MPUL2_D_LOCKDOWN6_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN6_OFST))
#define ALT_MPUL2_I_LOCKDOWN6_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN6_OFST))
#define ALT_MPUL2_D_LOCKDOWN7_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWN7_OFST))
#define ALT_MPUL2_I_LOCKDOWN7_ADDR          ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWN7_OFST))
#define ALT_MPUL2_D_LOCKDOWNx_ADDR(x)       ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_D_LOCKDOWNx_OFST(x)))
#define ALT_MPUL2_I_LOCKDOWNx_ADDR(x)       ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_I_LOCKDOWNx_OFST(x)))
#define ALT_MPUL2_LOCK_LINE_EN_ADDR         ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_LOCK_LINE_EN_OFST))
#define ALT_MPUL2_UNLOCK_WAY_ADDR           ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_UNLOCK_WAY_OFST))
#define ALT_MPUL2_ADDR_FILTERING_START_ADDR ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_ADDR_FILTERING_START_OFST))
#define ALT_MPUL2_ADDR_FILTERING_END_ADDR   ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_ADDR_FILTERING_END_OFST))
#define ALT_MPUL2_DEBUG_CTRL_ADDR           ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_DEBUG_CTRL_OFST))
#define ALT_MPUL2_PREFETCH_CTRL_ADDR        ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_PREFETCH_CTRL_OFST))
#define ALT_MPUL2_POWER_CTRL_ADDR           ALT_CAST(void *, (ALT_CAST(char *, ALT_MPUL2_ADDR) + ALT_MPUL2_POWER_CTRL_OFST))

#define ALT_MPUL2_CONTROL_EN_SET_MSK (1 << 0)

#define ALT_MPUL2_AUX_CONTROL_PARITY_EN_SET_MSK         (1 << 21)
#define ALT_MPUL2_AUX_CONTROL_WAYSIZE_SET_MSK           (7 << 17)
#define ALT_MPUL2_AUX_CONTROL_ASSOCIATIVITY_SET_MSK     (1 << 16)
#define ALT_MPUL2_AUX_CONTROL_WAYSIZE_VALUE_GET(value)  (((value) >> 17) & 0x7)
#define ALT_MPUL2_AUX_CONTROL_FULLLINEOFZERO_EN_SET_MSK (1 << 0)

#define ALT_MPUL2_TAG_RAM_CONTROL_WRITE_LATENCY_VALUE_GET(value) (((value) >> 8) & 0x7)
#define ALT_MPUL2_TAG_RAM_CONTROL_WRITE_LATENCY_VALUE_SET(value) (((value) & 0x7) << 8)
#define ALT_MPUL2_TAG_RAM_CONTROL_READ_LATENCY_VALUE_GET(value)  (((value) >> 4) & 0x7)
#define ALT_MPUL2_TAG_RAM_CONTROL_READ_LATENCY_VALUE_SET(value)  (((value) & 0x7) << 4)
#define ALT_MPUL2_TAG_RAM_CONTROL_SETUP_LATENCY_VALUE_GET(value) (((value) >> 0) & 0x7)
#define ALT_MPUL2_TAG_RAM_CONTROL_SETUP_LATENCY_VALUE_SET(value) (((value) & 0x7) << 0)

#define ALT_MPUL2_DATA_RAM_CONTROL_WRITE_LATENCY_VALUE_GET(value) (((value) >> 8) & 0x7)
#define ALT_MPUL2_DATA_RAM_CONTROL_WRITE_LATENCY_VALUE_SET(value) (((value) & 0x7) << 8)
#define ALT_MPUL2_DATA_RAM_CONTROL_READ_LATENCY_VALUE_GET(value)  (((value) >> 4) & 0x7)
#define ALT_MPUL2_DATA_RAM_CONTROL_READ_LATENCY_VALUE_SET(value)  (((value) & 0x7) << 4)
#define ALT_MPUL2_DATA_RAM_CONTROL_SETUP_LATENCY_VALUE_GET(value) (((value) >> 0) & 0x7)
#define ALT_MPUL2_DATA_RAM_CONTROL_SETUP_LATENCY_VALUE_SET(value) (((value) & 0x7) << 0)

#define ALT_MPUL2_PREFETCH_CTRL_I_PF_EN_SET_MSK (1 << 29)
#define ALT_MPUL2_PREFETCH_CTRL_D_PF_EN_SET_MSK (1 << 28)

/////

#define ALT_CACHE_L2_INTERRUPT_ALL (ALT_CACHE_L2_INTERRUPT_DECERR | \
                                    ALT_CACHE_L2_INTERRUPT_SLVERR | \
                                    ALT_CACHE_L2_INTERRUPT_ERRRD |  \
                                    ALT_CACHE_L2_INTERRUPT_ERRRT |  \
                                    ALT_CACHE_L2_INTERRUPT_ERRWD |  \
                                    ALT_CACHE_L2_INTERRUPT_ERRWT |  \
                                    ALT_CACHE_L2_INTERRUPT_PARRD |  \
                                    ALT_CACHE_L2_INTERRUPT_PARRT |  \
                                    ALT_CACHE_L2_INTERRUPT_ECNTR)

/////

static uint32_t alt_cache_l2_waymask = 0x0000ffff;

ALT_STATUS_CODE alt_cache_l2_init(void)
{
    // Query the cache characteristics

    uint32_t auxctrl = alt_read_word(ALT_MPUL2_AUX_CONTROL_ADDR);

    if (auxctrl & ALT_MPUL2_AUX_CONTROL_ASSOCIATIVITY_SET_MSK)
    {
        alt_cache_l2_waymask = 0x0000ffff;
    }
    else
    {
        alt_cache_l2_waymask = 0x000000ff;
    }

    /////

    // Initialize the L2CC using instructions from L2C-310, section 3.1.1.

    // Write global configuration:
    //  - Associativity, way size
    //  - Latencies for RAM accesses
    //  - Allocation policy
    //  - Prefetch and power capability
    // (Not needed as the associated lines are by default set to the instantiation parameters)

    // Invalidate by way all cache entries
    // (Not needed as it will be invalidated when L2 is enabled)

    alt_write_word(ALT_MPUL2_TAG_RAM_CONTROL_ADDR,
                     ALT_MPUL2_TAG_RAM_CONTROL_WRITE_LATENCY_VALUE_SET(0)
                   | ALT_MPUL2_TAG_RAM_CONTROL_READ_LATENCY_VALUE_SET(0)
                   | ALT_MPUL2_TAG_RAM_CONTROL_SETUP_LATENCY_VALUE_SET(0));

    alt_write_word(ALT_MPUL2_DATA_RAM_CONTROL_ADDR,
                     ALT_MPUL2_DATA_RAM_CONTROL_WRITE_LATENCY_VALUE_SET(0)
                   | ALT_MPUL2_DATA_RAM_CONTROL_READ_LATENCY_VALUE_SET(1)
                   | ALT_MPUL2_DATA_RAM_CONTROL_SETUP_LATENCY_VALUE_SET(0));

    // Clear interrupts just in case.
    alt_cache_l2_int_status_clear(ALT_CACHE_L2_INTERRUPT_ALL);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_uninit(void)
{
    return ALT_E_SUCCESS;
}

#define ALT_MPUL2_PREFETCH_CTRL_PF_EN_SET_MSK \
    (ALT_MPUL2_PREFETCH_CTRL_I_PF_EN_SET_MSK | ALT_MPUL2_PREFETCH_CTRL_D_PF_EN_SET_MSK)

ALT_STATUS_CODE alt_cache_l2_prefetch_enable(void)
{
    // Use the Prefetch Control Register instead of Aux Control. This is
    // because the Prefetch Control can be changed while the L2 is enabled.
    // For more information, see L2C-310, section 3.3.14.

    alt_setbits_word(ALT_MPUL2_PREFETCH_CTRL_ADDR, ALT_MPUL2_PREFETCH_CTRL_PF_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_prefetch_disable(void)
{
    // Use the Prefetch Control Register instead of Aux Control. This is
    // because the Prefetch Control can be changed while the L2 is enabled.
    // For more information, see L2C-310, section 3.3.14.

    alt_clrbits_word(ALT_MPUL2_PREFETCH_CTRL_ADDR, ALT_MPUL2_PREFETCH_CTRL_PF_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

bool alt_cache_l2_prefetch_is_enabled(void)
{
    // Query the Prefetch Control Register.
    // For more information, see L2C-310, section 3.3.14.

    uint32_t pfctrl = alt_read_word(ALT_MPUL2_PREFETCH_CTRL_ADDR);

    if ((pfctrl & ALT_MPUL2_PREFETCH_CTRL_PF_EN_SET_MSK) == ALT_MPUL2_PREFETCH_CTRL_PF_EN_SET_MSK)
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_STATUS_CODE alt_cache_l2_parity_enable(void)
{
    bool l2_enabled = alt_cache_l2_is_enabled();

    if (l2_enabled)
    {
        alt_cache_l2_disable();
    }

    alt_setbits_word(ALT_MPUL2_AUX_CONTROL_ADDR, ALT_MPUL2_AUX_CONTROL_PARITY_EN_SET_MSK);

    if (l2_enabled)
    {
        alt_cache_l2_enable();
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_parity_disable(void)
{
    alt_clrbits_word(ALT_MPUL2_AUX_CONTROL_ADDR, ALT_MPUL2_AUX_CONTROL_PARITY_EN_SET_MSK);
    return ALT_E_SUCCESS;
}

bool alt_cache_l2_parity_is_enabled(void)
{
    uint32_t auxctrl = alt_read_word(ALT_MPUL2_AUX_CONTROL_ADDR);
    if ((auxctrl & ALT_MPUL2_AUX_CONTROL_PARITY_EN_SET_MSK) == ALT_MPUL2_AUX_CONTROL_PARITY_EN_SET_MSK)
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_STATUS_CODE alt_cache_l2_enable(void)
{
    if (!alt_cache_l2_is_enabled())
    {
        alt_cache_l2_invalidate_all();
        alt_write_word(ALT_MPUL2_CONTROL_ADDR, ALT_MPUL2_CONTROL_EN_SET_MSK);
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_disable(void)
{
    if (alt_cache_l2_is_enabled())
    {
        alt_cache_l2_purge_all();
        alt_write_word(ALT_MPUL2_CONTROL_ADDR, 0);
    }

    return ALT_E_SUCCESS;
}

bool alt_cache_l2_is_enabled(void)
{
    uint32_t ctrl = alt_read_word(ALT_MPUL2_CONTROL_ADDR);
    if ((ctrl & ALT_MPUL2_CONTROL_EN_SET_MSK) != 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
// Common cache maintenance operation register formats
//

#define ALT_MPUL2_COMMON_PA_TAG_SET_MSK   (0xfffff << 12)
#define ALT_MPUL2_COMMON_PA_INDEX_SET_MSK (0x7f    << 5)
#define ALT_MPUL2_COMMON_PA_C_SET_MSK     (0x1     << 0)

#define ALT_MPUL2_COMMON_INDEXWAY_WAY_SET_MSK   (0xf  << 28)
#define ALT_MPUL2_COMMON_INDEXWAY_INDEX_SET_MSK (0x7f << 5)
#define ALT_MPUL2_COMMON_INDEXWAY_C_SET_MSK     (0x1  << 0)

#define ALT_MPUL2_COMMON_SYNC_C_SET_MSK (1 << 0)

#define ALT_MPUL2_COMMON_WAY_WAY_SET_MSK (0xffff << 0)

/////

// Timeouts for various L2 cache maintenance operations.
// The ranges of the operations can be determined by enabling debug printing.
#define ALT_CACHE_L2_SYNC_TIMEOUT             128

#define ALT_CACHE_L2_INVALIDATE_ALL_TIMEOUT   4096
#define ALT_CACHE_L2_CLEAN_ALL_TIMEOUT        65536
#define ALT_CACHE_L2_PURGE_ALL_TIMEOUT        65536

#define ALT_CACHE_L2_INVALIDATE_ADDR_TIMEOUT  128
#define ALT_CACHE_L2_CLEAN_ADDR_TIMEOUT       128
#define ALT_CACHE_L2_PURGE_ADDR_TIMEOUT       128

ALT_STATUS_CODE alt_cache_l2_sync(void)
{
    // Issue cache sync command, then wait for it to complete by polling the same register.
    // For more information, see L2C-310, section 3.3.10.

    alt_write_word(ALT_MPUL2_CACHE_SYNC_ADDR, 0);

    int i = 0;

    while (alt_read_word(ALT_MPUL2_CACHE_SYNC_ADDR))
    {
        // Atomic operation still in progress.

        if (i == ALT_CACHE_L2_SYNC_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Sync time = %d.\n", i);

    return ALT_E_SUCCESS;
}

static ALT_STATUS_CODE alt_cache_l2_invalidate_helper(uintptr_t paddress, size_t length)
{
    int i   = 0;
    int seg = 0;

    // For each stride: Issue invalidate line by PA command, then wait for it
    // to complete by polling the same register.
    // For more information, see L2C-310, section 3.3.10.

    for (uintptr_t pa = paddress; pa < paddress + length; pa += ALT_CACHE_LINE_SIZE)
    {
        alt_write_word(ALT_MPUL2_INV_PA_ADDR, pa);

        ++seg;
    }

    while (alt_read_word(ALT_MPUL2_INV_PA_ADDR))
    {
        // Atomic operation still in progress.

        if (i == ALT_CACHE_L2_INVALIDATE_ADDR_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Invalidate PA time = %d for %d segment(s)\n", i, seg);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_invalidate(void * paddress, size_t length)
{
    // Verify preconditions:
    //  - length is non-zero
    //  - address and length are on the cache boundaries
    if (length == 0)
    {
        return ALT_E_BAD_ARG;
    }
    if (((uintptr_t)paddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    return alt_cache_l2_invalidate_helper((uintptr_t)paddress, length);
}

ALT_STATUS_CODE alt_cache_l2_invalidate_all(void)
{
    // Invalidate by way, all ways.
    // For more information, see L2C-310, section 3.3.10.

    alt_write_word(ALT_MPUL2_INV_WAY_ADDR, alt_cache_l2_waymask);

    int i = 0;

    while (alt_read_word(ALT_MPUL2_INV_WAY_ADDR))
    {
        // Background operation still in progress.

        if (i == ALT_CACHE_L2_INVALIDATE_ALL_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Invalidate All time = %d.\n", i);

    return ALT_E_SUCCESS;
}

static ALT_STATUS_CODE alt_cache_l2_clean_helper(uintptr_t paddress, size_t length)
{
    int i   = 0;
    int seg = 0;

    // For each stride: Issue clean line by PA command, then wait for it to
    // complete by polling the same register.
    // For more information, see L2C-310, section 3.3.10.

    for (uintptr_t pa = paddress; pa < paddress + length; pa += ALT_CACHE_LINE_SIZE)
    {
        alt_write_word(ALT_MPUL2_CLEAN_PA_ADDR, pa);

        ++seg;
    }

    while (alt_read_word(ALT_MPUL2_CLEAN_PA_ADDR) & ALT_MPUL2_COMMON_PA_C_SET_MSK)
    {
        // Atomic operation still in progress.

        if (i == ALT_CACHE_L2_CLEAN_ADDR_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Clean PA time = %d for %d segment(s)\n", i, seg);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_clean(void * paddress, size_t length)
{
    // Verify preconditions:
    //  - length is non-zero
    //  - address and length are on the cache boundaries
    if (length == 0)
    {
        return ALT_E_BAD_ARG;
    }
    if (((uintptr_t)paddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    return alt_cache_l2_clean_helper((uintptr_t)paddress, length);
}

ALT_STATUS_CODE alt_cache_l2_clean_all(void)
{
    // Clean by way, all ways.
    // For more information, see L2C-310, section 3.3.10.

    alt_write_word(ALT_MPUL2_CLEAN_WAY_ADDR, alt_cache_l2_waymask);

    int i = 0;

    while (alt_read_word(ALT_MPUL2_CLEAN_WAY_ADDR))
    {
        // Background operation still in progress.

        if (i == ALT_CACHE_L2_CLEAN_ALL_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Invalidate All time = %d.\n", i);

    return ALT_E_SUCCESS;
}

static ALT_STATUS_CODE alt_cache_l2_purge_helper(uintptr_t paddress, size_t length)
{
    int i   = 0;
    int seg = 0;

    // For each stride: Issue clean and invalidate line by PA command, then
    // wait for it to complete by polling the same register.
    // For more information, see L2C-310, section 3.3.10.

    for (uintptr_t pa = paddress; pa < paddress + length; pa += ALT_CACHE_LINE_SIZE)
    {
        alt_write_word(ALT_MPUL2_CLEAN_INV_PA_ADDR, pa);

        ++seg;
    }

    while (alt_read_word(ALT_MPUL2_CLEAN_INV_PA_ADDR) & ALT_MPUL2_COMMON_PA_C_SET_MSK)
    {
        // Atomic operation still in progress.

        if (i == ALT_CACHE_L2_PURGE_ADDR_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Purge PA time = %d for %d segment(s)\n", i, seg);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_purge(void * paddress, size_t length)
{
    // Verify preconditions:
    //  - length is non-zero
    //  - address and length are on the cache boundaries
    if (length == 0)
    {
        return ALT_E_BAD_ARG;
    }
    if (((uintptr_t)paddress & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }
    if ((length & (ALT_CACHE_LINE_SIZE - 1)) != 0)
    {
        return ALT_E_BAD_ARG;
    }

    return alt_cache_l2_purge_helper((uintptr_t)paddress, length);
}

ALT_STATUS_CODE alt_cache_l2_purge_all(void)
{
    // Clean and invalidate by way, all ways.
    // For more information, see L2C-310, section 3.3.10.

    alt_write_word(ALT_MPUL2_CLEAN_INV_WAY_ADDR, alt_cache_l2_waymask);

    int i = 0;

    while (alt_read_word(ALT_MPUL2_CLEAN_INV_WAY_ADDR))
    {
        // Background operation still in progress.

        if (i == ALT_CACHE_L2_PURGE_ALL_TIMEOUT)
        {
            return ALT_E_TMO;
        }
        ++i;
    }

    dprintf("DEBUG[cache][l2]: L2 Purge All time = %d.\n", i);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_int_enable(uint32_t interrupt)
{
    // Validate the interrupt mask
    if ((interrupt & ALT_CACHE_L2_INTERRUPT_ALL) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_MPUL2_INT_MASK_ADDR, interrupt);
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_cache_l2_int_disable(uint32_t interrupt)
{
    // Validate the interrupt mask
    if ((interrupt & ALT_CACHE_L2_INTERRUPT_ALL) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    alt_clrbits_word(ALT_MPUL2_INT_MASK_ADDR, interrupt);
    return ALT_E_SUCCESS;
}

uint32_t alt_cache_l2_int_status_get(void)
{
    return alt_read_word(ALT_MPUL2_INT_MASK_STATUS_ADDR);
}

ALT_STATUS_CODE alt_cache_l2_int_status_clear(uint32_t interrupt)
{
    // Validate the interrupt mask
    if ((interrupt & ALT_CACHE_L2_INTERRUPT_ALL) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    alt_write_word(ALT_MPUL2_INT_CLEAR_ADDR, interrupt);
    return ALT_E_SUCCESS;
}

/////

__attribute__((weak)) ALT_STATUS_CODE alt_int_dist_pending_clear(ALT_INT_INTERRUPT_t int_id)
{
    return ALT_E_SUCCESS;
}

inline static uint32_t get_current_cpu_num(void)
{
    uint32_t affinity;

    // Use the MPIDR. This is only available at PL1 or higher.
    // See ARMv7, section B4.1.106.

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, affinity, c0, c0, 5");
#else
    __asm("MRC p15, 0,       %0, c0, c0, 5" : "=r" (affinity));
#endif

    return affinity & 0xFF;
}

ALT_STATUS_CODE alt_cache_l2_ecc_start(void * block, size_t size)
{
    uint32_t way_size = (8 * 1024) << ALT_MPUL2_AUX_CONTROL_WAYSIZE_VALUE_GET(alt_read_word(ALT_MPUL2_AUX_CONTROL_ADDR));

    // Add 32 KiB to the scrubbing size to account for effects of the L1 on scrubbing.
    uint32_t scrub_way_size = way_size + (32 * 1024);

    if (size < scrub_way_size)
    {
        return ALT_E_ERROR;
    }

    if (alt_cache_l2_is_enabled() == false)
    {
        return ALT_E_ERROR;
    }

    /////

    bool l1_icache   = false;
    bool l1_prefetch = false;
    bool l2_prefetch = false;

    if (alt_cache_l1_instruction_is_enabled() == true)
    {
        l1_icache = true;
        alt_cache_l1_instruction_disable();
    }

    if (alt_cache_l1_prefetch_is_enabled() == true)
    {
        l1_prefetch = true;
        alt_cache_l1_prefetch_disable();
    }

    if (alt_cache_l2_prefetch_is_enabled() == true)
    {
        l2_prefetch = true;
        alt_cache_l2_prefetch_disable();
    }

    // inline'ed alt_cache_l2_disable(); // This will invalidate all L2 entries
    alt_cache_l2_purge_all();
    alt_write_word(ALT_MPUL2_CONTROL_ADDR, 0);

    // Enable "Full line of zero" feature of the L2C.
    // See L2C-310, section 2.5.5, "Full line of zero write".
    alt_setbits_word(ALT_MPUL2_AUX_CONTROL_ADDR, ALT_MPUL2_AUX_CONTROL_FULLLINEOFZERO_EN_SET_MSK);

    // ECC should be enabled before L2 is enabled. (NPP MPU, section 4.3, item 1)
    alt_write_word(ALT_SYSMGR_ECC_L2_ADDR, ALT_SYSMGR_ECC_L2_EN_SET_MSK);

    // inline'ed alt_cache_l2_enable();
    // No need to invalidate all; the previous L2 disable should have purged everything.
    alt_write_word(ALT_MPUL2_CONTROL_ADDR, ALT_MPUL2_CONTROL_EN_SET_MSK);

    // Enable "Full line of zero" feature of the A9.
    // See Cortex-A9 TRM, section 4.3.10.
    actlr_write_helper(actlr_read_helper() | ALT_CPU_ACTLR_WRITEFULLLINEZEROS_SET_MSK);

    /////

    uint32_t cpu_affinity = get_current_cpu_num();

    // Loop through all ways for the lock by master configuration.
    int way_count = (alt_cache_l2_waymask == 0x0000ffff) ? 16 : 8;

    for (int way_lock = 0; way_lock < way_count; ++way_lock)
    {
        // Lock the current way for Data and Instruction.
        alt_write_word(ALT_MPUL2_D_LOCKDOWNx_ADDR(cpu_affinity), ~(1 << way_lock) & alt_cache_l2_waymask);
        alt_write_word(ALT_MPUL2_I_LOCKDOWNx_ADDR(cpu_affinity), ~(1 << way_lock) & alt_cache_l2_waymask);

        // Invalidate All. This will ensure that scrubbing RAM contents does not exist in a different way.
        alt_cache_l2_invalidate_all();

        // Loop through all words in the block
        register uint32_t * block2 = block;
        for (register int i = 0; i < (scrub_way_size / sizeof(*block2)); i++)
        {
            *block2 = 0;
            ++block2;
        }

        // Don't put the DSB inside the loop. It will disallow the [full line of zero] optimization.
        __asm("dsb");
    }

    // Unlock the way lock by master for the current CPU.
    alt_write_word(ALT_MPUL2_D_LOCKDOWNx_ADDR(cpu_affinity), 0);
    alt_write_word(ALT_MPUL2_I_LOCKDOWNx_ADDR(cpu_affinity), 0);

    if (l1_icache)
    {
        alt_cache_l1_instruction_enable();
    }

    if (l1_prefetch)
    {
        alt_cache_l1_prefetch_enable();
    }

    if (l2_prefetch)
    {
        alt_cache_l2_prefetch_enable();
    }

    alt_int_dist_pending_clear(ALT_INT_INTERRUPT_L2_ECC_BYTE_WR_IRQ);
    alt_int_dist_pending_clear(ALT_INT_INTERRUPT_L2_ECC_CORRECTED_IRQ);
    alt_int_dist_pending_clear(ALT_INT_INTERRUPT_L2_ECC_UNCORRECTED_IRQ);

    return ALT_E_SUCCESS;
}
