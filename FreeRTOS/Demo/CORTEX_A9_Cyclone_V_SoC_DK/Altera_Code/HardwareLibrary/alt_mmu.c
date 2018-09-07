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

#include "alt_mmu.h"
#include <string.h>
#include <stdio.h>

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, ##__VA_ARGS__)

/////

// Generates the bitmask given the MSB and LSB of a register field.
// NOTE: This is problematic for the BITMASK(31, 0) case.
#define BITMASK(msb, lsb) (((1 << ((msb) - (lsb) + 1)) - 1) << (lsb))
// Calculates the array count statically
#define ARRAY_COUNT(array) (sizeof(array) / sizeof(array[0]))
// Minimum
#define MIN(a, b) ((a) < (b) ? (a) : (b))
// Index into the pagetable given the virtual address. This is bits va[19:12] >> 12.
#define ALT_MMU_PAGE_TABLE_INDEX(va) (((uintptr_t)(va) >> 12) & 0xff)

/////

// This is the number of 1 MiB sections in the TTB1 table.
#define ALT_MMU_TTB1_SECTION_COUNT 4096

/////

// System Control Register
#define ALT_CPU_SCTLR_C_SET_MSK (1 << 2)
#define ALT_CPU_SCTLR_M_SET_MSK (1 << 0)

#define ALT_CPU_CONTEXTIDR_PROCID_SET_MSK (0xffffff << 8)
#define ALT_CPU_CONTEXTIDR_ASID_SET_MSK   (0x0000ff << 0)

// Translation Table Base Register 0 (Process Specific; Changes on context switch)

// (31 to 14 - (TTBCR.N))
#define ALT_CPU_TTBR0_TTB0BASEADDR_SET_MSK(ttbcr_n) BITMASK(31, 14 - (ttbcr_n))
#define ALT_CPU_TTBR0_IRGN_0_SET_MSK (1 << 6)
#define ALT_CPU_TTBR0_NOS_SET_MSK (1 << 5)
#define ALT_CPU_TTBR0_RGN_SET_MSK (3 << 3)
#define ALT_CPU_TTBR0_IMP_SET_MSK (1 << 2)
#define ALT_CPU_TTBR0_S_SET_MSK (1 << 1)
#define ALT_CPU_TTBR0_IRGN_1_SET_MSK (1 << 0)

#define ALT_CPU_TTBR0_RGN_NC  (0 << 3) // RGN[1:0] = 00
#define ALT_CPU_TTBR0_RGN_WBA (1 << 3) // RGN[1:0] = 01
#define ALT_CPU_TTBR0_RGN_WT  (2 << 3) // RGN[1:0] = 10
#define ALT_CPU_TTBR0_RGN_WB  (3 << 3) // RGN[1:0] = 11

// NOTE: IRGN bits are reversed. TTBR0[6] is IRGN[0]; TTBR[0] is IRGN[1].
#define ALT_CPU_TTBR0_IRGN_NC   (0 << 0 | 0 << 6) // IRGN[1:0] = 00
#define ALT_CPU_TTBR0_IRGN_WBA  (0 << 0 | 1 << 6) // IRGN[1:0] = 01
#define ALT_CPU_TTBR0_IRGN_WT   (1 << 0 | 0 << 6) // IRGN[1:0] = 10
#define ALT_CPU_TTBR0_IRGN_WB   (1 << 0 | 1 << 6) // IRGN[1:0] = 11

// Translation Table Base Register 1 (OS and IO specific; Static)
#define ALT_CPU_TTBR1_TTB1BASEADDR_SET_MSK (0x3ffffUL << 14)
#define ALT_CPU_TTBR1_IRGN_0_SET_MSK (1 << 6)
#define ALT_CPU_TTBR1_NOS_SET_MSK (1 << 5)
#define ALT_CPU_TTBR1_RGN_SET_MSK (3 << 3)
#define ALT_CPU_TTBR1_IMP_SET_MSK (1 << 2)
#define ALT_CPU_TTBR1_S_SET_MSK (1 << 1)
#define ALT_CPU_TTBR1_IRGN_1_SET_MSK (1 << 0)

// Translation Table Base Control Register
#define ALT_CPU_TTBCR_PD1_SET_MSK (1 << 5)
#define ALT_CPU_TTBCR_PD0_SET_MSK (1 << 4)
#define ALT_CPU_TTBCR_N_SET_MSK   (7 << 0)
#define ALT_CPU_TTBCR_N_VALUE_GET(value) (((value) << 0) & ALT_CPU_TTBCR_N_SET_MSK)

/////

static inline __attribute__((always_inline)) uint32_t sctlr_get_helper(void)
{
    // Read from SCTLR using CP15.
    // See ARMv7-A,R, section B4.1.30.

    uint32_t sctlr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, sctlr, c1, c0, 0");
#else
    __asm("MRC p15, 0, %0,    c1, c0, 0" : "=r" (sctlr));
#endif

    return sctlr;
}

static inline __attribute__((always_inline)) void sctlr_set_helper(uint32_t sctlr)
{
    // Write to SCTLR using CP15.
    // See ARMv7-A,R, section B4.1.30.

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, sctlr, c1, c0, 0");
#else
    __asm("MCR p15, 0, %0,    c1, c0, 0" : : "r" (sctlr));
#endif
}

/*
__attribute__((always_inline)) uint32_t contextidr_get_helper(void)
{
    // Read from CONTEXTIDR using CP15.
    // See ARMv7-A,R, section B4.1.36.

    uint32_t contextidr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, contextidr, c13, c0, 1");
#else
    __asm("MRC p15, 0, %0,         c13, c0, 1" : "=r" (contextidr));
#endif

    return contextidr;
}
*/

static inline __attribute__((always_inline)) void contextidr_set_helper(uint32_t contextidr)
{
    // Write to CONTEXTIDR using CP15.
    // See ARMv7-A,R, section B4.1.36.

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, contextidr, c13, c0, 1");
#else
    __asm("MCR p15, 0, %0,         c13, c0, 1" : : "r" (contextidr));
#endif
}

/*
__attribute__((always_inline)) uint32_t dacr_get_helper(void)
{
    // Read from DACR using CP15.
    // See ARMv7-A,R, section B4.1.43.

    uint32_t dacr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, dacr, c3, c0, 0");
#else
    __asm("MRC p15, 0, %0,   c3, c0, 0" : "=r" (dacr));
#endif

    return dacr;
}
*/

static inline __attribute__((always_inline)) void dacr_set_helper(uint32_t dacr)
{
    // Write to DACR using CP15.
    // See ARMv7-A,R, section B4.1.43.

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, dacr, c3, c0, 0");
#else
    __asm("MCR p15, 0, %0,   c3, c0, 0" : : "r" (dacr));
#endif
}

static inline __attribute__((always_inline)) uint32_t ttbcr_get_helper(void)
{
    // Read from TTBCR using CP15.
    // See ARMv7-A,R, section B4.1.153.

    uint32_t ttbcr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, ttbcr, c2, c0, 2");
#else
    __asm("MRC p15, 0, %0   , c2, c0, 2" : "=r" (ttbcr));
#endif

    return ttbcr;
}

static inline __attribute__((always_inline)) void ttbcr_set_helper(uint32_t ttbcr)
{
    // Write to TTBCR using CP15.
    // See ARMv7-A,R, section B4.1.153.

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, ttbcr, c2, c0, 2");
#else
    __asm("MCR p15, 0, %0,    c2, c0, 2" : : "r" (ttbcr));
#endif
}

static inline __attribute__((always_inline)) uint32_t ttbr0_get_helper(void)
{
    // Read the TTBR0 using CP15.
    // See ARMv7-A,R, section B4.1.154.

    uint32_t ttbr0;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, ttbr0, c2, c0, 0");
#else
    __asm("MRC p15, 0, %0,    c2, c0, 0" : "=r" (ttbr0));
#endif

    return ttbr0;
}

static inline __attribute__((always_inline)) void ttbr0_set_helper(uint32_t ttbr0)
{
    // Write to TTBR0 using CP15.
    // See ARMv7-A,R, section B4.1.154.

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, ttbr0, c2, c0, 0");
#else
    __asm("MCR p15, 0, %0,    c2, c0, 0" : : "r" (ttbr0));
#endif
}

static inline __attribute__((always_inline)) uint32_t ttbr1_get_helper(void)
{
    // Read the TTBR1 using CP15.
    // See ARMv7-A,R, section B4.1.155.

    uint32_t ttbr1;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, ttbr1, c2, c0, 1");
#else
    __asm("MRC p15, 0, %0,    c2, c0, 1" : "=r" (ttbr1));
#endif

    return ttbr1;
}

static inline __attribute__((always_inline)) void ttbr1_set_helper(uint32_t ttbr1)
{
    // Write to TTBR1 using CP15.
    // See ARMv7-A,R, section B4.1.155.

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, ttbr1, c2, c0, 1");
#else
    __asm("MCR p15, 0, %0,    c2, c0, 1" : : "r" (ttbr1));
#endif
}

/////

ALT_STATUS_CODE alt_mmu_init(void)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_uninit(void)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_ttb1_init(uint32_t* ttb1)
{
    uint32_t ttbcr = ttbcr_get_helper();
    uint32_t ttbcr_n = ALT_CPU_TTBCR_N_VALUE_GET(ttbcr);

    // Verify ttb1 buffer alignment.
    if ((uintptr_t)ttb1 & ~ALT_CPU_TTBR0_TTB0BASEADDR_SET_MSK(ttbcr_n))
    {
        // addr must align to 2^(14 - TTBCR.N) bytes.
        return ALT_E_BAD_ARG;
    }

    // The TTB1 size really depends on TTBCR.N value and if it will be used for
    // TTBR0 or TTBR1. The documentation just states that it should be 16 KiB.
    // See ARMv7-A,R, section B3.5.4.

    memset(ttb1, 0, ALT_MMU_TTB1_SIZE);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_ttb1_desc_set(uint32_t* ttb1,
                                      const void* va,
                                      const uint32_t desc)
{
    bool supersection = 0;

    // Validate the [va] parameter alignment based on the entry [desc] is describing.
    //  - Fault, Page Table, or section: 1 MiB.
    //  - Supersection: 16 MiB
    //  - Other: error.

    switch (ALT_MMU_TTB1_TYPE_GET(desc))
    {
    case ALT_MMU_TTB1_TYPE_SET(0x2): // Section or Supersection sans Physical Address Extension
        // Check bit 18, which determines if it is a regular or super variant
        if (desc & (1 << 18))
        {
            // Mark that we are describing a supersection.
            supersection = true;

            // Supersection: Check for 16 MiB alignment
            if ((uintptr_t)va & (ALT_MMU_SUPERSECTION_SIZE - 1))
            {
                return ALT_E_BAD_ARG;
            }
            break;
        }
        else
        {
            // Section, fall through.
        }
    case ALT_MMU_TTB1_TYPE_SET(0x0): // Fault
    case ALT_MMU_TTB1_TYPE_SET(0x1): // Page Table
        // Section, Fault, or Page Table: check for 1 MiB alignment
        if ((uintptr_t)va & (ALT_MMU_SECTION_SIZE - 1))
        {
            return ALT_E_BAD_ARG;
        }
        break;
    case ALT_MMU_TTB1_TYPE_SET(0x3): // Supersection with Physical Address Extension
        // The SoCFPGA does not support PAE.
        return ALT_E_BAD_ARG;
    }

    // The [va] looks good! Add entry into the TTB1.

    // TTB1 is indexed by va[31-N:20]. This function assumes N = 0.
    uint32_t index = (uintptr_t)va >> 20;

    if (supersection == false)
    {
        ttb1[index] = desc;
    }
    else
    {
        // Supersection needs the entry to be repeated 16x.
        for (int i = 0; i < 16; ++i)
        {
            ttb1[index + i] = desc;
        }

    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_ttb2_desc_set(const uint32_t* ttb1,
                                      const void* va,
                                      const uint32_t desc)
{
    bool largepage = false;

    // Validate the [va] parameter alignment based on the entry [desc] is describing.
    //  - Fault, Small Page: 4 KiB
    //  - Large Page: 64 KiB

    switch (ALT_MMU_TTB2_TYPE_GET(desc))
    {
    case ALT_MMU_TTB2_TYPE_SET(0x0): // Fault
    case ALT_MMU_TTB2_TYPE_SET(0x2): // Small Page, XN = 0
    case ALT_MMU_TTB2_TYPE_SET(0x3): // Small Page, XN = 1
        if ((uintptr_t)va & (ALT_MMU_SMALL_PAGE_SIZE - 1))
        {
            return ALT_E_BAD_ARG;
        }
        break;
    case ALT_MMU_TTB2_TYPE_SET(0x1): // Large Page
        if ((uintptr_t)va & (ALT_MMU_LARGE_PAGE_SIZE - 1))
        {
            return ALT_E_BAD_ARG;
        }
        largepage = true;
        break;
    }

    // The [va] looks good! Add entry into TTB1->TTB2.

    // Locate the TTB1 entry
    uint32_t ttb1_desc = ttb1[(uintptr_t)va >> 20];

    // Verify that [ttb1_desc] is a pagetable.
    if (ALT_MMU_TTB1_TYPE_GET(ttb1_desc) != ALT_MMU_TTB1_TYPE_SET(0x1))
    {
        return ALT_E_BAD_ARG;
    }
    
    // Locate TTB2 given [ttb1_desc]
    uint32_t * ttb2 = (uint32_t *)(ttb1_desc & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);

    // TTB2 is indexed by va[19:12].
    uint32_t index = ALT_MMU_PAGE_TABLE_INDEX(va);
    if (largepage == false)
    {
        ttb2[index] = desc;
    }
    else
    {
        // Large page needs the entry to be repeated 16x.
        for (int i = 0; i < 16; ++i)
        {
            ttb2[index + i] = desc;
        }
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_disable(void)
{
    uint32_t sctlr = sctlr_get_helper();
    if (sctlr & ALT_CPU_SCTLR_C_SET_MSK)
    {
        dprintf("WARN[MMU]: Data cache still active.\n");
    }
    sctlr &= ~ALT_CPU_SCTLR_M_SET_MSK;
    sctlr_set_helper(sctlr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_enable(void)
{
    alt_mmu_tlb_invalidate();

    uint32_t sctlr = sctlr_get_helper();
    sctlr |= ALT_CPU_SCTLR_M_SET_MSK;
    sctlr_set_helper(sctlr);

    return ALT_E_SUCCESS;
}

void * alt_mmu_TTBR0_get(void)
{
    uint32_t ttbcr = ttbcr_get_helper();
    uint32_t ttbcr_n = ALT_CPU_TTBCR_N_VALUE_GET(ttbcr);
    uint32_t ttbr0 = ttbr0_get_helper();

    return (void *)(ALT_CPU_TTBR0_TTB0BASEADDR_SET_MSK(ttbcr_n) & ttbr0);
}

ALT_STATUS_CODE alt_mmu_TTBR0_set(const void* addr)
{
    uint32_t ttbcr = ttbcr_get_helper();
    uint32_t ttbcr_n = ALT_CPU_TTBCR_N_VALUE_GET(ttbcr);

    if ((uintptr_t)addr & ~ALT_CPU_TTBR0_TTB0BASEADDR_SET_MSK(ttbcr_n))
    {
        // addr must align to 2^(14 - TTBCR.N) bytes.
        return ALT_E_BAD_ARG;
    }

    // The Translation table must reside in Normal Memory, so pick the most
    // performant attributes.
    uint32_t ttbr0 =   ALT_CPU_TTBR0_RGN_WBA   // Translation table is WBA for outer cacheability
                     | ALT_CPU_TTBR0_IRGN_WBA; // Translation table is WBA for inner cacheability
    ttbr0 &= ~ALT_CPU_TTBR0_TTB0BASEADDR_SET_MSK(ttbcr_n);
    ttbr0 |= (uint32_t)addr;

    ttbr0_set_helper(ttbr0);

    return ALT_E_SUCCESS;
}

void * alt_mmu_TTBR1_get(void)
{
    uint32_t ttbr1 = ttbr1_get_helper();

    return (void *)(ALT_CPU_TTBR1_TTB1BASEADDR_SET_MSK & ttbr1);
}

ALT_STATUS_CODE alt_mmu_TTBR1_set(const void* addr)
{
    if ((uintptr_t)addr & ~ALT_CPU_TTBR1_TTB1BASEADDR_SET_MSK)
    {
        // addr must align to 16 KiB.
        return ALT_E_BAD_ARG;
    }

    uint32_t ttbr1 = ttbr1_get_helper();
    ttbr1 &= ~ALT_CPU_TTBR1_TTB1BASEADDR_SET_MSK;
    ttbr1 |= (uint32_t)addr;

    ttbr1_set_helper(ttbr1);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_TTBCR_set(const bool enable_ttbr0_walk,
                                  const bool enable_ttbr1_walk,
                                  const uint32_t base_addr_width)
{
    uint32_t ttbcr = 0;

    if (!enable_ttbr0_walk)
    {
        ttbcr |= ALT_CPU_TTBCR_PD0_SET_MSK;
    }

    if (!enable_ttbr1_walk)
    {
        ttbcr |= ALT_CPU_TTBCR_PD1_SET_MSK;
    }

    if (base_addr_width > 7)
    {
        return ALT_E_BAD_ARG;
    }

    ttbcr |= base_addr_width;

    ttbcr_set_helper(ttbcr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_DACR_set(const ALT_MMU_DAP_t domain_ap[],
                                 const size_t num_elem)
{
    if (num_elem > 16)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t dacr = 0;

    for (int i = 0; i < num_elem; ++i)
    {
        ALT_MMU_DAP_t ap = domain_ap[i];

        switch (ap)
        {
        case ALT_MMU_DAP_NO_ACCESS:
        case ALT_MMU_DAP_CLIENT:
        case ALT_MMU_DAP_MANAGER:
            dacr |= ap << (i * 2);
            break;
        default:
        case ALT_MMU_DAP_RESERVED:
            return ALT_E_BAD_ARG;
        }
    }

    dacr_set_helper(dacr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_CONTEXTIDR_set(const uint32_t procid, const uint32_t asid)
{
    if (procid > 0x00ffffff)
    {
        return ALT_E_BAD_ARG;
    }

    if (asid > 0xff)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t contextidr = (procid << 8) | (asid << 0);

    contextidr_set_helper(contextidr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_tlb_invalidate(void)
{
    // Issue TLBIALL (TLB Invalidate All)
    // See ARMv7-A,R, section B4.1.135.

    uint32_t dummy = 0;

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, dummy, c8, c3, 0");
#else
    __asm("MCR p15, 0, %0,    c8, c3, 0" : : "r" (dummy));
#endif

    // Ensure all TLB maintenance operations complete before returning.
    __asm("dsb");

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_tlb_invalidate_is(void)
{
    // Issue TLBIALLIS (TLB Invalidate All, Inner Shareable)
    // See ARMv7-A,R, section B4.1.138.

    uint32_t dummy = 0;

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, dummy, c8, c7, 0");
#else
    __asm("MCR p15, 0, %0,    c8, c7, 0" : : "r" (dummy));
#endif

    // Ensure all TLB maintenance operations complete before returning.
    __asm("dsb");

    return ALT_E_SUCCESS;
}

/////

// The #define value for PAGETABLE is designed to make the security check efficient.
#define ALT_VREGION_1MIB         (2)                              /* 2 */
#define ALT_VREGION_PAGETABLE_S  ((int)ALT_MMU_TTB_NS_SECURE)     /* 0 */
#define ALT_VREGION_PAGETABLE_NS ((int)ALT_MMU_TTB_NS_NON_SECURE) /* 1 */

static ALT_STATUS_CODE alt_vregion_mark_pagetable(char * vregion, ALT_MMU_TTB_NS_t security)
{
    if (*vregion == ALT_VREGION_1MIB)
    {
        *vregion = (int)security;
    }
    else if (*vregion != (int)security)
    {
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

static size_t alt_mmu_va_space_storage_required_internal(const ALT_MMU_MEM_REGION_t* mem_regions,
                                                         const size_t num_mem_regions,
                                                         char * vregion)
{
    for (int i = 0; i < ALT_MMU_TTB1_SECTION_COUNT; ++i)
    {
        vregion[i] = ALT_VREGION_1MIB;
    }

    // For each region entry, mark the TTB1 as either fault, section, pagetable.
    // The total space required is the space required for the TTB1 (16 KiB) + pagetables * (1 KiB)

    for (int i = 0; i < num_mem_regions; ++i)
    {
        uintptr_t        va       = (uintptr_t)mem_regions[i].va;
        uintptr_t        pa       = (uintptr_t)mem_regions[i].pa;
        uint32_t         size     = mem_regions[i].size;
        ALT_MMU_TTB_NS_t security = mem_regions[i].security;

        // Verify [va] aligns to 4 KiB
        if (va & (ALT_MMU_SMALL_PAGE_SIZE - 1))
        {
            return 0;
        }

        // Verify [pa] aligns to 4 KiB
        if (pa & (ALT_MMU_SMALL_PAGE_SIZE - 1))
        {
            return 0;
        }

        // Verify [size] aligns to 4 KiB
        if (size & (ALT_MMU_SMALL_PAGE_SIZE - 1))
        {
            return 0;
        }

        // Mark the regions at the start of an unaligned 1 MiB as pagetable.
        // Align the [va] to 1 MiB and subtract that from the [size] left to describe.
        if (va & (ALT_MMU_SECTION_SIZE - 1))
        {
            // Pagetables must be either S or NS. If the pagetable was
            // previously marked as something different, the regions described
            // will not be implementable.
            if (alt_vregion_mark_pagetable(&vregion[va >> 20],
                                           security) != ALT_E_SUCCESS)
            {
                return 0;
            }

            uint32_t segment = MIN(ALT_MMU_SECTION_SIZE - (va & (ALT_MMU_SECTION_SIZE - 1)), size);
            va   += segment;
            pa   += segment;
            size -= segment;
        }

        // Skip each 1 MiB aligned segment of size 1 MiB. These regions require
        // pagetable if the PA is not 1 MiB aligned.

        // [pa] is not used after this point.

        if (pa & (ALT_MMU_SECTION_SIZE - 1))
        {
            // PA is not 1 MiB aligned. Everything must use pagetables.

            while (size >= ALT_MMU_SECTION_SIZE)
            {
                // Pagetables must be either S or NS. If the pagetable was
                // previously marked as something different, the regions described
                // will not be implementable.
                if (alt_vregion_mark_pagetable(&vregion[va >> 20],
                                               security) != ALT_E_SUCCESS)
                {
                    return 0;
                }

                va   += ALT_MMU_SECTION_SIZE;
                // pa   += ALT_MMU_SECTION_SIZE;
                size -= ALT_MMU_SECTION_SIZE;
            }
        }
        else
        {
            // PA is 1 MiB aligned. Sections or supersections can be used.

            while (size >= ALT_MMU_SECTION_SIZE)
            {
                va   += ALT_MMU_SECTION_SIZE;
                // pa   += ALT_MMU_SECTION_SIZE;
                size -= ALT_MMU_SECTION_SIZE;
            }
        }

        // The remainder should be a 1 MiB aligned segment of less than 1 MiB. Mark that region as pagetable.
        if (size)
        {
            // Pagetables must be either S or NS. If the pagetable was
            // previously marked as something different, the regions described
            // will not be implementable.
            if (alt_vregion_mark_pagetable(&vregion[va >> 20],
                                           security) != ALT_E_SUCCESS)
            {
                return 0;
            }
        }
    }

    // Calculate the size as 16 KiB (TTB1) + 1 KiB * (TTB2 or the number of pagetables)
    size_t reqsize = ALT_MMU_TTB1_SIZE;

    for (int i = 0; i < ALT_MMU_TTB1_SECTION_COUNT; ++i)
    {
        if (vregion[i] != ALT_VREGION_1MIB)
        {
            reqsize += ALT_MMU_TTB2_SIZE;
        }
    }

    return reqsize;
}

size_t alt_mmu_va_space_storage_required(const ALT_MMU_MEM_REGION_t* mem_regions,
                                         const size_t num_mem_regions)
{
    char vregion[ALT_MMU_TTB1_SECTION_COUNT];

    return alt_mmu_va_space_storage_required_internal(mem_regions,
                                                      num_mem_regions,
                                                      vregion);
}

/*
static inline uint32_t alt_mmu_va_space_gen_fault(void)
{
    return 0;
}
*/

static inline uint32_t alt_mmu_va_space_gen_pagetable(uintptr_t pagetable,
                                                      const ALT_MMU_MEM_REGION_t * mem)
{
    if (mem->attributes == ALT_MMU_ATTR_FAULT)
    {
        return 0;
    }

    return 
          ALT_MMU_TTB1_TYPE_SET(0x1)
        | ALT_MMU_TTB1_PAGE_TBL_NS_SET(mem->security)
        | ALT_MMU_TTB1_PAGE_TBL_DOMAIN_SET(0)
        | ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_SET(pagetable >> 10);
}

static inline uint32_t alt_mmu_va_space_gen_section(uintptr_t pa,
                                                    const ALT_MMU_MEM_REGION_t * mem)
{
    if (mem->attributes == ALT_MMU_ATTR_FAULT)
    {
        return 0;
    }

    int tex = (mem->attributes >> 4) & 0x7;
    int c   = (mem->attributes >> 1) & 0x1;
    int b   = (mem->attributes >> 0) & 0x1;

    return 
          ALT_MMU_TTB1_TYPE_SET(0x2)
        | ALT_MMU_TTB1_SECTION_B_SET(b)
        | ALT_MMU_TTB1_SECTION_C_SET(c)
        | ALT_MMU_TTB1_SECTION_XN_SET(mem->execute)
        | ALT_MMU_TTB1_SECTION_DOMAIN_SET(0)
        | ALT_MMU_TTB1_SECTION_AP_SET(mem->access)
        | ALT_MMU_TTB1_SECTION_TEX_SET(tex)
        | ALT_MMU_TTB1_SECTION_S_SET(mem->shareable)
        | ALT_MMU_TTB1_SECTION_NG_SET(0)
        | ALT_MMU_TTB1_SECTION_NS_SET(mem->security)
        | ALT_MMU_TTB1_SECTION_BASE_ADDR_SET(pa >> 20);
}

static inline uint32_t alt_mmu_va_space_gen_supersection(uintptr_t pa,
                                                         const ALT_MMU_MEM_REGION_t * mem)
{
    if (mem->attributes == ALT_MMU_ATTR_FAULT)
    {
        return 0;
    }

    int tex = (mem->attributes >> 4) & 0x7;
    int c   = (mem->attributes >> 1) & 0x1;
    int b   = (mem->attributes >> 0) & 0x1;

    return 
          ALT_MMU_TTB1_TYPE_SET(0x2) | (1 << 18) // bit 18 marks section as being super.
        | ALT_MMU_TTB1_SUPERSECTION_B_SET(b)
        | ALT_MMU_TTB1_SUPERSECTION_C_SET(c)
        | ALT_MMU_TTB1_SUPERSECTION_XN_SET(mem->execute)
        | ALT_MMU_TTB1_SUPERSECTION_DOMAIN_SET(0)
        | ALT_MMU_TTB1_SUPERSECTION_AP_SET(mem->access)
        | ALT_MMU_TTB1_SUPERSECTION_TEX_SET(tex)
        | ALT_MMU_TTB1_SUPERSECTION_S_SET(mem->shareable)
        | ALT_MMU_TTB1_SUPERSECTION_NG_SET(0)
        | ALT_MMU_TTB1_SUPERSECTION_NS_SET(mem->security)
        | ALT_MMU_TTB1_SUPERSECTION_BASE_ADDR_SET(pa >> 24);
}

static inline uint32_t alt_mmu_va_space_gen_smallpage(uintptr_t pa,
                                                      const ALT_MMU_MEM_REGION_t * mem)
{
    if (mem->attributes == ALT_MMU_ATTR_FAULT)
    {
        return 0;
    }

    int tex = (mem->attributes >> 4) & 0x7;
    int c   = (mem->attributes >> 1) & 0x1;
    int b   = (mem->attributes >> 0) & 0x1;

    // NS bit (mem->security) is ignored as it is set in TTB1.

    return 
          ALT_MMU_TTB2_TYPE_SET(0x2)
        | ALT_MMU_TTB2_SMALL_PAGE_XN_SET(mem->execute)
        | ALT_MMU_TTB2_SMALL_PAGE_B_SET(b)
        | ALT_MMU_TTB2_SMALL_PAGE_C_SET(c)
        | ALT_MMU_TTB2_SMALL_PAGE_AP_SET(mem->access)
        | ALT_MMU_TTB2_SMALL_PAGE_TEX_SET(tex)
        | ALT_MMU_TTB2_SMALL_PAGE_S_SET(mem->shareable)
        | ALT_MMU_TTB2_SMALL_PAGE_NG_SET(0)
        | ALT_MMU_TTB2_SMALL_PAGE_BASE_ADDR_SET(pa >> 12);
}

static inline uint32_t alt_mmu_va_space_gen_largepage(uintptr_t pa,
                                                      const ALT_MMU_MEM_REGION_t * mem)
{
    if (mem->attributes == ALT_MMU_ATTR_FAULT)
    {
        return 0;
    }

    int tex = (mem->attributes >> 4) & 0x7;
    int c   = (mem->attributes >> 1) & 0x1;
    int b   = (mem->attributes >> 0) & 0x1;

    // NS bit (mem->security) is ignored as it is set in TTB1.

    return
          ALT_MMU_TTB2_TYPE_SET(0x1)
        | ALT_MMU_TTB2_LARGE_PAGE_B_SET(b)
        | ALT_MMU_TTB2_LARGE_PAGE_C_SET(c)
        | ALT_MMU_TTB2_LARGE_PAGE_AP_SET(mem->access)
        | ALT_MMU_TTB2_LARGE_PAGE_S_SET(mem->shareable)
        | ALT_MMU_TTB2_LARGE_PAGE_NG_SET(0)
        | ALT_MMU_TTB2_LARGE_PAGE_TEX_SET(tex)
        | ALT_MMU_TTB2_LARGE_PAGE_XN_SET(mem->execute)
        | ALT_MMU_TTB2_LARGE_PAGE_BASE_ADDR_SET(pa >> 16);
}

static ALT_STATUS_CODE alt_mmu_ttb2_init(uint32_t * ttb2)
{
    // For TTB2 (page tables), the page table base address in TTB1 is
    // bits[31:10]. Thus it must be 2^10 byte aligned or 1 KiB.
    // Source: ARMv7-A,R, section B3.5.1.

    if ((uintptr_t)ttb2 & ((1 << 10) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    memset(ttb2, 0, ALT_MMU_TTB2_SIZE);
    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_mmu_va_space_create(uint32_t** ttb1,
                                        const ALT_MMU_MEM_REGION_t* mem_regions,
                                        const size_t num_mem_regions,
                                        alt_mmu_ttb_alloc_t ttb_alloc,
                                        void * ttb_alloc_context)
{
    char vregion[ALT_MMU_TTB1_SECTION_COUNT];

    size_t reqsize = alt_mmu_va_space_storage_required_internal(mem_regions,
                                                                num_mem_regions,
                                                                vregion);
    if (reqsize == 0)
    {
        return ALT_E_ERROR;
    }

    char * memory    = ttb_alloc(reqsize, ttb_alloc_context);
    size_t allocated = 0;

    // Verify allocation

    if (memory == NULL)
    {
        return ALT_E_ERROR;
    }

    // Verify alignment

    // For TTBR0, the translation table must be aligned to 2^x bytes, where
    // x = (14 - TTBCR.N). Because VA space sets TTBCR.N = 0, x = 14, and the
    // table must be aligned to 2^14 or 16 KiB.
    // Source: ARMv7-A,R, section B4.1.154.

    // For TTB2 (page tables), the page table base address in TTB1 is
    // bits[31:10]. Thus it must be 2^10 byte aligned or 1 KiB.
    // Source: ARMv7-A,R, section B3.5.1.

    // The stricter of the two alignment is 16 KiB.

    if ((uintptr_t)memory & ((1 << 14) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    // "allocate" space for the TTB1.
    if (allocated + ALT_MMU_TTB1_SIZE > reqsize)
    {
        return ALT_E_ERROR;
    }
    *ttb1 = (uint32_t *)memory;
    allocated += ALT_MMU_TTB1_SIZE;

    if (alt_mmu_ttb1_init(*ttb1) != ALT_E_SUCCESS)
    {
        return ALT_E_ERROR;
    }

    // "allocate" space for each pagetable in [vregion]
    for (int i = 0; i < ALT_MMU_TTB1_SECTION_COUNT; ++i)
    {
        if (vregion[i] != ALT_VREGION_1MIB)
        {
            if (allocated + ALT_MMU_TTB2_SIZE > reqsize)
            {
                return ALT_E_ERROR;
            }
            uint32_t * pagetable = (uint32_t *)(memory + allocated);
            allocated += ALT_MMU_TTB2_SIZE;
            alt_mmu_ttb2_init(pagetable);

            ALT_MMU_MEM_REGION_t mem_region;
            mem_region.attributes = ALT_MMU_ATTR_STRONG; // Any non-FAULT will work.
            mem_region.security   = (ALT_MMU_TTB_NS_t)vregion[i];
            uint32_t desc = alt_mmu_va_space_gen_pagetable((uintptr_t)pagetable, &mem_region);

            (*ttb1)[i] = desc;
        }
    }

    // The allocated size should match the requested size. If not, this means
    // that the regions descriptor changed between calling
    // alt_mmu_va_space_storage_required() and alt_mmu_va_space_create().
    if (reqsize != allocated)
    {
        return ALT_E_ERROR;
    }

    // Iterate through all region descriptors

    for (size_t i = 0; i < num_mem_regions; ++i)
    {
        uintptr_t va   = (uintptr_t)mem_regions[i].va;
        uintptr_t pa   = (uintptr_t)mem_regions[i].pa;
        uint32_t  size = mem_regions[i].size;

        // Determine the va/pa relative alignment: 4 KiB, 64 KiB, 1 MiB, 16 MiB

        uint32_t alignopt[] =
        {
            ALT_MMU_SUPERSECTION_SIZE,
            ALT_MMU_SECTION_SIZE,
            ALT_MMU_LARGE_PAGE_SIZE
        };

        // Relative alignment of [va] and [pa].
        int relalign = ALT_MMU_SMALL_PAGE_SIZE;

        for (int j = 0; j < ARRAY_COUNT(alignopt); ++j)
        {
            if ( (va & (alignopt[j] - 1)) ==
                 (pa & (alignopt[j] - 1)) )
            {
                relalign = alignopt[j];
                break;
            }
        }

        // Page the 1 MiB unaligned segment of [va]. Areas requiring page tables
        // should already have those page tables created previously in this
        // function.
        if (va & (ALT_MMU_SECTION_SIZE - 1))
        {
            // This is the size of the memory segment after paging which will cause the [va] to align to a 1 MiB,
            // or up to the size of the region being processed, whichever is smaller.
            uint32_t segsize = MIN(ALT_MMU_SECTION_SIZE - (va & (ALT_MMU_SECTION_SIZE - 1)), size);

            if (relalign >= ALT_MMU_LARGE_PAGE_SIZE)
            {
                // Because of the 64 KiB relative alignment, try to use large pages.

                // Use small pages until [va] is 64KiB aligned.
                while (((va & (ALT_MMU_LARGE_PAGE_SIZE - 1)) != 0) && (segsize >= ALT_MMU_SMALL_PAGE_SIZE))
                {
                    uint32_t desc = alt_mmu_va_space_gen_smallpage(pa, &mem_regions[i]);

                    uint32_t * pagetable = (uint32_t *)((*ttb1)[va >> 20] & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);
                    uint32_t ptindex = ALT_MMU_PAGE_TABLE_INDEX(va);

                    // Detect if an existing non-fault region has already been created.
                    // We cannot detect if a fault region is requested and a region description is already a fault,
                    // which it is by default.
                    if (pagetable[ptindex] != 0)
                    {
                        return ALT_E_ERROR;
                    }

                    pagetable[ptindex] = desc;

                    va      += ALT_MMU_SMALL_PAGE_SIZE;
                    pa      += ALT_MMU_SMALL_PAGE_SIZE;
                    segsize -= ALT_MMU_SMALL_PAGE_SIZE;
                    size    -= ALT_MMU_SMALL_PAGE_SIZE;
                }

                // Use large pages for the rest of the 64 KiB aligned areas.
                while (segsize >= ALT_MMU_LARGE_PAGE_SIZE)
                {
                    uint32_t desc = alt_mmu_va_space_gen_largepage(pa, &mem_regions[i]);

                    uint32_t * pagetable = (uint32_t *)((*ttb1)[va >> 20] & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);
                    uint32_t ptindex = ALT_MMU_PAGE_TABLE_INDEX(va);

                    for (int j = 0; j < 16; ++j)
                    {
                        if (pagetable[ptindex + j] != 0)
                        {
                            return ALT_E_ERROR;
                        }

                        pagetable[ptindex + j] = desc;
                    }

                    va      += ALT_MMU_LARGE_PAGE_SIZE;
                    pa      += ALT_MMU_LARGE_PAGE_SIZE;
                    segsize -= ALT_MMU_LARGE_PAGE_SIZE;
                    size    -= ALT_MMU_LARGE_PAGE_SIZE;
                }

                // There is a chance that the segment is so small that it does cause the progress to align to the 1 MiB.
                // If this is the case, page out the rest of segsize using small pages, and the remaining size to be 0.
                while (segsize >= ALT_MMU_SMALL_PAGE_SIZE)
                {
                    uint32_t desc = alt_mmu_va_space_gen_smallpage(pa, &mem_regions[i]);

                    uint32_t * pagetable = (uint32_t *)((*ttb1)[va >> 20] & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);
                    uint32_t ptindex = ALT_MMU_PAGE_TABLE_INDEX(va);

                    if (pagetable[ptindex] != 0)
                    {
                        return ALT_E_ERROR;
                    }

                    pagetable[ptindex] = desc;

                    va      += ALT_MMU_SMALL_PAGE_SIZE;
                    pa      += ALT_MMU_SMALL_PAGE_SIZE;
                    segsize -= ALT_MMU_SMALL_PAGE_SIZE;
                    size    -= ALT_MMU_SMALL_PAGE_SIZE;
                }
            }
            else
            {
                // No large pages possible, Use small pages only.
                while (segsize >= ALT_MMU_SMALL_PAGE_SIZE)
                {
                    uint32_t desc = alt_mmu_va_space_gen_smallpage(pa, &mem_regions[i]);

                    uint32_t * pagetable = (uint32_t *)((*ttb1)[va >> 20] & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);
                    uint32_t ptindex = ALT_MMU_PAGE_TABLE_INDEX(va);

                    if (pagetable[ptindex] != 0)
                    {
                        return ALT_E_ERROR;
                    }

                    pagetable[ptindex] = desc;

                    va      += ALT_MMU_SMALL_PAGE_SIZE;
                    pa      += ALT_MMU_SMALL_PAGE_SIZE;
                    segsize -= ALT_MMU_SMALL_PAGE_SIZE;
                    size    -= ALT_MMU_SMALL_PAGE_SIZE;
                }
            }
        }

        // Page each the larger 1 MiB aligned, 1 MiB sized segments.

        // If [va] and [pa] are relatively 16 MiB aligned and the size remaining
        // to be described is greater than 16 MiB, use supersections.

        // If [va] and [pa] are relatively 1 MiB aligned and the size remaining
        // to be described is greater than 1 MiB, use sections.

        // Otherwise use pagetables for everything remaining.

        if (   (relalign >= ALT_MMU_SUPERSECTION_SIZE)
            && (size     >= ALT_MMU_SUPERSECTION_SIZE))
        {
            // Attempt to use supersections. This may not always be possible.

            // Use regular sections for the areas before supersections that does not align to 16 MiB
            while (((va & (ALT_MMU_SUPERSECTION_SIZE - 1)) != 0) && (size >= ALT_MMU_SECTION_SIZE))
            {
                uint32_t desc = alt_mmu_va_space_gen_section(pa, &mem_regions[i]);

                if ((*ttb1)[va >> 20] != 0)
                {
                    return ALT_E_ERROR;
                }

                (*ttb1)[va >> 20] = desc;

                va   += ALT_MMU_SECTION_SIZE;
                pa   += ALT_MMU_SECTION_SIZE;
                size -= ALT_MMU_SECTION_SIZE;
            }

            // Use supersections for the 16 MiB aligned areas
            while (size >= ALT_MMU_SUPERSECTION_SIZE)
            {
                uint32_t desc = alt_mmu_va_space_gen_supersection(pa, &mem_regions[i]);

                for (int j = 0; j < 16; ++j)
                {
                    if ((*ttb1)[(va >> 20) + j] != 0)
                    {
                        return ALT_E_ERROR;
                    }

                    (*ttb1)[(va >> 20) + j] = desc;
                }

                va   += ALT_MMU_SUPERSECTION_SIZE;
                pa   += ALT_MMU_SUPERSECTION_SIZE;
                size -= ALT_MMU_SUPERSECTION_SIZE;
            }

            // Use regular sections for the areas after supersections that does not align to 16 MiB.
            while (size >= ALT_MMU_SECTION_SIZE)
            {
                uint32_t desc = alt_mmu_va_space_gen_section(pa, &mem_regions[i]);

                if ((*ttb1)[va >> 20] != 0)
                {
                    return ALT_E_ERROR;
                }

                (*ttb1)[va >> 20] = desc;

                va   += ALT_MMU_SECTION_SIZE;
                pa   += ALT_MMU_SECTION_SIZE;
                size -= ALT_MMU_SECTION_SIZE;
            }
        }
        else if (   (relalign >= ALT_MMU_SECTION_SIZE)
                 && (size     >= ALT_MMU_SECTION_SIZE))
        {
            // No supersection possible. Use regular sections only.

            while (size >= ALT_MMU_SECTION_SIZE)
            {
                uint32_t desc = alt_mmu_va_space_gen_section(pa, &mem_regions[i]);

                if ((*ttb1)[va >> 20] != 0)
                {
                    return ALT_E_ERROR;
                }

                (*ttb1)[va >> 20] = desc;

                va   += ALT_MMU_SECTION_SIZE;
                pa   += ALT_MMU_SECTION_SIZE;
                size -= ALT_MMU_SECTION_SIZE;
            }
        }

        // The remainder should be [va] 1 MiB aligned segment not able to use
        // sections or supersections. Mark that region as pagetable.

        // Use large pages if it is suitable.
        if ((relalign >= ALT_MMU_LARGE_PAGE_SIZE) && (size >= ALT_MMU_LARGE_PAGE_SIZE))
        {
            while (size >= ALT_MMU_LARGE_PAGE_SIZE)
            {
                uint32_t desc = alt_mmu_va_space_gen_largepage(pa, &mem_regions[i]);

                uint32_t * pagetable = (uint32_t *)((*ttb1)[va >> 20] & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);
                uint32_t ptindex = ALT_MMU_PAGE_TABLE_INDEX(va);

                for (int j = 0; j < 16; ++j)
                {
                    if (pagetable[ptindex + j] != 0)
                    {
                        return ALT_E_ERROR;
                    }

                    pagetable[ptindex + j] = desc;
                }

                va   += ALT_MMU_LARGE_PAGE_SIZE;
                pa   += ALT_MMU_LARGE_PAGE_SIZE;
                size -= ALT_MMU_LARGE_PAGE_SIZE;
            }
        }

        while (size >= ALT_MMU_SMALL_PAGE_SIZE)
        {
            uint32_t desc = alt_mmu_va_space_gen_smallpage(pa, &mem_regions[i]);

            uint32_t * pagetable = (uint32_t *)((*ttb1)[va >> 20] & ALT_MMU_TTB1_PAGE_TBL_BASE_ADDR_MASK);
            uint32_t ptindex = ALT_MMU_PAGE_TABLE_INDEX(va);

            if (pagetable[ptindex] != 0)
            {
                return ALT_E_ERROR;
            }

            pagetable[ptindex] = desc;

            va   += ALT_MMU_SMALL_PAGE_SIZE;
            pa   += ALT_MMU_SMALL_PAGE_SIZE;
            size -= ALT_MMU_SMALL_PAGE_SIZE;
        }

    } // for (size_t i = 0; i < num_mem_regions; ++i)

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_mmu_va_space_enable(const uint32_t * ttb1)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Set TTBCR to use N=0
    if (status == ALT_E_SUCCESS)
    {
        status = alt_mmu_TTBCR_set(true,
                                   true,
                                   0);
        if (status != ALT_E_SUCCESS)
        {
            dprintf("DEBUG[MMU:VA]: Failure on line %d.\n", __LINE__);
        }
    }

    // Set TTBR0 to use ttb1

    if (status == ALT_E_SUCCESS)
    {
        status = alt_mmu_TTBR0_set(ttb1);
        if (status != ALT_E_SUCCESS)
        {
            dprintf("DEBUG[MMU:VA]: Failure on line %d.\n", __LINE__);
        }
    }

    // Configure DACRs to be client domain.

    if (status == ALT_E_SUCCESS)
    {
        ALT_MMU_DAP_t domain_ap[16];
        for (int i = 0; i < 16; ++i)
        {
            domain_ap[i] = ALT_MMU_DAP_CLIENT;
        }

        status = alt_mmu_DACR_set(domain_ap, 16);
        if (status != ALT_E_SUCCESS)
        {
            dprintf("DEBUG[MMU:VA]: Failure on line %d.\n", __LINE__);
        }
    }

    // Enable MMU (implicitly invalidates TLBs)

    if (status == ALT_E_SUCCESS)
    {
        status = alt_mmu_enable();
        if (status != ALT_E_SUCCESS)
        {
            dprintf("DEBUG[MMU:VA]: Failure on line %d.\n", __LINE__);
        }
    }

    return status;
}
