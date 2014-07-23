/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES// LOSS OF USE, DATA,
 * OR PROFITS// OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */


/** \file */


/** \file */
/**
 * \addtogroup cp15_cache Cache Operations
 *
 * \section Usage
 *
 * They are performed as MCR instructions and only operate on a level 1 cache associated with
 * ATM v7 processor.
 * The supported operations are:
 * <ul>
 * <li> Any of these operations can be applied to
 *  -# any data cache
 *  -# any unified cache.
 * <li> Invalidate by MVA
 *   Performs an invalidate of a data or unified cache line based on the address it contains.
 * <li> Invalidate by set/way
 *   Performs an invalidate of a data or unified cache line based on its location in the cache hierarchy.
 * <li> Clean by MVA
 *   Performs a clean of a data or unified cache line based on the address it contains.
 * <li> Clean by set/way
 *   Performs a clean of a data or unified cache line based on its location in the cache hierarchy.
 * <li> Clean and Invalidate by MVA
 *   Performs a clean and invalidate of a data or unified cache line based on the address it contains.
 * <li> Clean and Invalidate by set/way
 *   Performs a clean and invalidate of a data or unified cache line based on its location in the cache hierarchy.
 * </ul>
 *
 * Related files:\n
 * \ref cp15.h\n
 * \ref cp15_arm_iar.s \n
 */


        MODULE  ?cp15

        //// Forward declaration of sections.
        SECTION IRQ_STACK:DATA:NOROOT(2)
        SECTION CSTACK:DATA:NOROOT(3)

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/


/*----------------------------------------------------------------------------
 *        Functions to access CP15 coprocessor register
 *----------------------------------------------------------------------------*/
        PUBLIC  CP15_ReadID
        PUBLIC  CP15_ReadControl
        PUBLIC  CP15_WriteControl
        PUBLIC  CP15_WriteDomainAccessControl
        PUBLIC  CP15_WriteTTB
        PUBLIC  CP15_InvalidateIcacheInnerSharable
        PUBLIC  CP15_InvalidateBTBinnerSharable
        PUBLIC  CP15_InvalidateIcache
        PUBLIC  CP15_InvalidateIcacheByMva
        PUBLIC  CP15_FlushBTB
        PUBLIC  CP15_FlushBTBbyMva
        PUBLIC  CP15_InvalidateDcacheLineByMva
        PUBLIC  CP15_InvalidateDcacheLineBySetWay
        PUBLIC  CP15_CleanDCacheByMva
        PUBLIC  CP15_CleanDCacheBySetWay
        PUBLIC  CP15_CleanDCacheMva
        PUBLIC  CP15_CleanInvalidateDcacheLineByMva
        PUBLIC  CP15_CleanInvalidateDcacheLine
        PUBLIC  CP15_coherent_dcache_for_dma
        PUBLIC  CP15_invalidate_dcache_for_dma
        PUBLIC  CP15_clean_dcache_for_dma
        PUBLIC  CP15_flush_dcache_for_dma
        PUBLIC  CP15_flush_kern_dcache_for_dma

/**
 * \brief Register c0 accesses the ID Register, Cache Type Register, and TCM Status Registers.
 *  Reading from this register returns the device ID, the cache type, or the TCM status
 *   depending on the value of Opcode_2 used.
 */
        SECTION .CP15_ReadID:DATA:NOROOT(2)
        PUBLIC   CP15_ReadID
CP15_ReadID:
        mov     r0, #0
        mrc     p15, 0, r0, c0, c0, 0
        bx      lr

/**
 * \brief Register c1 is the Control Register for the ARM926EJ-S processor.
 * This register specifies the configuration used to enable and disable the
 * caches and MMU. It is recommended that you access this register using a
 * read-modify-write sequence
 */
        SECTION .CP15_ReadControl:CODE:NOROOT(2)
        PUBLIC   CP15_ReadControl
CP15_ReadControl:
        mov     r0, #0
        mrc     p15, 0, r0, c1, c0, 0
        bx      lr

        SECTION .CP15_WriteControl:CODE:NOROOT(2)
        PUBLIC   CP15_WriteControl
CP15_WriteControl:
        mcr     p15, 0, r0, c1, c0, 0
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        bx      lr

       SECTION .CP15_WriteDomainAccessControl:CODE:NOROOT(2)
       PUBLIC   CP15_WriteDomainAccessControl
CP15_WriteDomainAccessControl:
        mcr     p15, 0, r0, c3, c0, 0
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        bx      lr

/**
 * \brief  ARMv7A architecture supports two translation tables
 * Configure translation table base (TTB) control register cp15,c2
 * to a value of all zeros, indicates we are using TTB register 0.
 * write the address of our page table base to TTB register 0.
 */
        SECTION .CP15_WriteTTB:CODE:NOROOT(2)
        PUBLIC   CP15_WriteTTB
CP15_WriteTTB:
       mcr     p15, 0, r0, c2, c0, 0
       nop
       nop
       nop
       nop
       nop
       nop
       nop
       nop
       bx     lr

/**
 * \brief Invalidate I cache predictor array inner Sharable
 */
        SECTION .CP15_InvalidateIcacheInnerSharable:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateIcacheInnerSharable
CP15_InvalidateIcacheInnerSharable:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c1, 0
        bx      lr

/**
 * \brief Invalidate entire branch predictor array inner Sharable
 */
        SECTION .CP15_InvalidateBTBinnerSharable:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateBTBinnerSharable
CP15_InvalidateBTBinnerSharable:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c1, 6
        bx      lr

/**
 * \brief Invalidate all instruction caches to PoU, also flushes branch target cache
 */
        SECTION .CP15_InvalidateIcache:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateIcache
CP15_InvalidateIcache:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c5, 0
        bx      lr

/**
 * \brief Invalidate instruction caches by VA to PoU
 */
        SECTION .CP15_InvalidateIcacheByMva:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateIcacheByMva
CP15_InvalidateIcacheByMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c5, 1
        bx      lr

/**
 * \brief Flush entire branch predictor array
 */
        SECTION .CP15_FlushBTB:CODE:NOROOT(2)
        PUBLIC   CP15_FlushBTB
CP15_FlushBTB:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c5, 6
        bx      lr

/**
 * \brief Flush branch predictor array entry by MVA
 */
        SECTION .CP15_FlushBTBbyMva:CODE:NOROOT(2)
        PUBLIC   CP15_FlushBTBbyMva
CP15_FlushBTBbyMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c5, 7
        bx      lr

/**
 * \brief Invalidate data cache line by VA to Poc
 */
        SECTION .CP15_InvalidateDcacheLineByMva:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateDcacheLineByMva
CP15_InvalidateDcacheLineByMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c6, 1
        bx      lr

/**
 * \brief Invalidate data cache line by set/way
 */
        SECTION .CP15_InvalidateDcacheLineBySetWay:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateDcacheLineBySetWay
CP15_InvalidateDcacheLineBySetWay:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c6, 2
        bx      lr

/**
 * \brief Clean data cache line by MVA
 */
        SECTION .CP15_CleanDCacheByMva:CODE:NOROOT(2)
        PUBLIC   CP15_CleanDCacheByMva
CP15_CleanDCacheByMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c10, 1
        bx      lr

/**
 * \brief Clean data cache line by Set/way
 */
        SECTION .CP15_CleanDCacheBySetWay:CODE:NOROOT(2)
        PUBLIC   CP15_CleanDCacheBySetWay
CP15_CleanDCacheBySetWay:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c10, 2
        bx      lr

/**
 * \brief Clean unified cache line by MVA
 */
        SECTION .CP15_CleanDCacheMva:CODE:NOROOT(2)
        PUBLIC   CP15_CleanDCacheMva
CP15_CleanDCacheMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c11, 1
        bx      lr

/**
 * \brief Clean and invalidate data cache line by VA to PoC
 */
        SECTION .CP15_CleanInvalidateDcacheLineByMva:CODE:NOROOT(2)
        PUBLIC   CP15_CleanInvalidateDcacheLineByMva
CP15_CleanInvalidateDcacheLineByMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c14, 1
        bx      lr

/**
 * \brief Clean and Incalidate data cache line by Set/Way
 */
        SECTION .CP15_CleanInvalidateDcacheLine:CODE:NOROOT(2)
        PUBLIC   CP15_CleanInvalidateDcacheLine
CP15_CleanInvalidateDcacheLine:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c14, 2
        bx      lr

/**
 * \brief Ensure that the I and D caches are coherent within specified
 *      region.  This is typically used when code has been written to
 *      a memory region, and will be executed.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
        SECTION .CP15_coherent_dcache_for_dma:CODE:NOROOT(2)
        PUBLIC   CP15_coherent_dcache_for_dma
CP15_coherent_dcache_for_dma:
//      dcache_line_size r2, r3

        mrc     p15, 0, r3, c0, c0, 1         // read ctr
        lsr     r3, r3, #16
        and     r3, r3, #0xf                  // cache line size encoding
        mov     r2, #4                        // bytes per word
        mov     r2, r2, lsl r3                // actual cache line size

        sub     r3, r2, #1
        bic     r12, r0, r3
loop1:
        mcr     p15, 0, r12, c7, c11, 1       // clean D line to the point of unification
        add     r12, r12, r2
        cmp     r12, r1
        blo     loop1
        dsb

// .macro  icache_line_size, reg, tmp
        mrc     p15, 0, r3, c0, c0, 1         // read ctr
        and     r3, r3, #0xf                  // cache line size encoding
        mov     r2, #4                        // bytes per word
        mov     r2, r2, lsl r3                // actual cache line size

        sub     r3, r2, #1
        bic     r12, r0, r3
loop2:
        mcr     p15, 0, r12, c7, c5, 1        // invalidate I line
        add     r12, r12, r2
        cmp     r12, r1
        blo     loop2
        mov     r0, #0
        mcr     p15, 0, r0, c7, c1, 6         //invalidate BTB Inner Shareable
        mcr      p15, 0, r0, c7, c5, 6        // invalidate BTB
        dsb
        isb
        bx      lr


/**
 * \brief Invalidate the data cache within the specified region; we will
 *      be performing a DMA operation in this region and we want to
 *      purge old data in the cache.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
        SECTION .CP15_invalidate_dcache_for_dma:CODE:NOROOT(2)
        PUBLIC   CP15_invalidate_dcache_for_dma
CP15_invalidate_dcache_for_dma:

//      dcache_line_size r2, r3
        mrc     p15, 0, r3, c0, c0, 1         // read ctr
        lsr     r3, r3, #16
        and     r3, r3, #0xf                  // cache line size encoding
        mov     r2, #4                        // bytes per word
        mov     r2, r2, lsl r3                // actual cache line size

        sub     r3, r2, #1
        tst     r0, r3
        bic     r0, r0, r3

        mcrne   p15, 0, r0, c7, c14, 1         // clean & invalidate D / U line

        tst     r1, r3
        bic     r1, r1, r3
        mcrne   p15, 0, r1, c7, c14, 1         // clean & invalidate D / U line
loop3:
        mcr     p15, 0, r0, c7, c6, 1          // invalidate D / U line
        add     r0, r0, r2
        cmp     r0, r1
        blo     loop3
        dsb
        bx      lr


/**
 * \brief Clean the data cache within the specified region
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
        SECTION .CP15_clean_dcache_for_dma:CODE:NOROOT(2)
        PUBLIC   CP15_clean_dcache_for_dma
CP15_clean_dcache_for_dma:
//      dcache_line_size r2, r3
        mrc     p15, 0, r3, c0, c0, 1         // read ctr
        lsr     r3, r3, #16
        and     r3, r3, #0xf                  // cache line size encoding
        mov     r2, #4                        // bytes per word
        mov     r2, r2, lsl r3                // actual cache line size

        sub     r3, r2, #1
        bic     r0, r0, r3
loop4:
        mcr     p15, 0, r0, c7, c10, 1        // clean D / U line
        add     r0, r0, r2
        cmp     r0, r1
        blo     loop4
        dsb
        bx      lr


/**
 * \brief Flush the data cache within the specified region
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
        SECTION .CP15_flush_dcache_for_dma:CODE:NOROOT(2)
        PUBLIC   CP15_flush_dcache_for_dma
CP15_flush_dcache_for_dma:
//        dcache_line_size r2, r3
        mrc     p15, 0, r3, c0, c0, 1         // read ctr
        lsr     r3, r3, #16
        and     r3, r3, #0xf                  // cache line size encoding
        mov     r2, #4                        // bytes per word
        mov     r2, r2, lsl r3                // actual cache line size
        sub     r3, r2, #1
        bic     r0, r0, r3
loop5:
        mcr     p15, 0, r0, c7, c14, 1         // clean & invalidate D / U line
        add     r0, r0, r2
        cmp     r0, r1
        blo     loop5
        dsb
        bx      lr


/**
 * \brief CP15_flush_kern_dcache_for_dma
 * Ensure that the data held in the page kaddr is written back to the page in question.
 * \param start virtual start address of region
 * \param end virtual end address of region
 */
        SECTION .CP15_flush_kern_dcache_for_dma:CODE:NOROOT(2)
        PUBLIC   CP15_flush_kern_dcache_for_dma
CP15_flush_kern_dcache_for_dma:
//       dcache_line_size r2, r3
        mrc     p15, 0, r3, c0, c0, 1         // read ctr
        lsr     r3, r3, #16
        and     r3, r3, #0xf                  // cache line size encoding
        mov     r2, #4                        // bytes per word
        mov     r2, r2, lsl r3                // actual cache line size

        add     r1, r0, r1
        sub     r3, r2, #1
        bic     r0, r0, r3

        mcr     p15, 0, r0, c7, c14, 1        // clean & invalidate D line / unified line
        add     r0, r0, r2
        cmp     r0, r1
        blo     1b
        dsb
        bx      lr
        END

