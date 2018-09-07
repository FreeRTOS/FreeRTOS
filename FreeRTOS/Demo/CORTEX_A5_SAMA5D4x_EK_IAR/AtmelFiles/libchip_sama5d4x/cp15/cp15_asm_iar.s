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
#define __ASSEMBLY__


/*----------------------------------------------------------------------------
 *        Functions to access CP15 coprocessor register
 *----------------------------------------------------------------------------*/
        PUBLIC  CP15_ReadID
        PUBLIC  CP15_ExclusiveCache
        PUBLIC  CP15_NonExclusiveCache
        PUBLIC  CP15_ISB
        PUBLIC  CP15_DSB
        PUBLIC  CP15_DMB        
        PUBLIC  CP15_SelectICache
        PUBLIC  CP15_SelectDCache
        PUBLIC  CP15_ReadControl
        PUBLIC  CP15_WriteControl
        PUBLIC  CP15_WriteDomainAccessControl
        PUBLIC  CP15_WriteTTB
        PUBLIC  CP15_InvalidateIcacheInnerSharable
        PUBLIC  CP15_InvalidateBTBinnerSharable
        PUBLIC  CP15_InvalidateIcache
        PUBLIC  CP15_InvalidateIcacheByMva
        PUBLIC  CP15_InvalidateBTB
        PUBLIC  CP15_InvalidateBTBbyMva
        
        PUBLIC  CP15_InvalidateDcacheBySetWay
        PUBLIC  CP15_CleanDCacheBySetWay
        PUBLIC  CP15_CleanInvalidateDCacheBySetWay
        
        PUBLIC  CP15_InvalidateDcacheByMva        
        PUBLIC  CP15_CleanDCacheByMva             
        PUBLIC  CP15_CleanDCacheUMva
        PUBLIC  CP15_CleanInvalidateDcacheByMva
        PUBLIC  CP15_InvalidateTranslationTable
        
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
 * \brief Register c7 accesses the ACTLR Register, to indicate cpu that L2 is in exclusive mode
 */
        SECTION .CP15_ISB:DATA:NOROOT(2)
        PUBLIC   CP15_ISB
CP15_ISB:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c5, 4
        nop
        bx      lr
        
/** 
 * \brief Register c7 accesses the ACTLR Register, to indicate cpu that L2 is in exclusive mode
 */
        SECTION .CP15_DSB:DATA:NOROOT(2)
        PUBLIC   CP15_DSB
CP15_DSB:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c10, 4
        nop
        bx      lr

/** 
 * \brief Register c7 accesses the ACTLR Register, to indicate cpu that L2 is in exclusive mode
 */
        SECTION .CP15_DMB:DATA:NOROOT(2)
        PUBLIC   CP15_DMB
CP15_DMB:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c10, 5
        nop
        bx      lr

/** 
 * \brief Register c1 accesses the ACTLR Register, to indicate cpu that L2 is in exclusive mode
 */
        SECTION .CP15_ExclusiveCache:DATA:NOROOT(2)
        PUBLIC   CP15_ExclusiveCache
CP15_ExclusiveCache:
        mov     r0, #0
        mrc     p15, 0, r0, c1, c0, 1 ; Read ACTLR
        orr     r0, r0, #0x00000080
        mcr     p15, 0, r0, c1, c0, 1 ; Write ACTLR
        nop
        bx      lr
       
       
/** 
 * \brief Register c1 accesses the ACTLR Register, to indicate cpu that L2 is in exclusive mode
 */
        SECTION .CP15_NonExclusiveCache:DATA:NOROOT(2)
        PUBLIC   CP15_NonExclusiveCache
CP15_NonExclusiveCache:
        mov     r0, #0
        mrc     p15, 0, r0, c1, c0, 1 ; Read ACTLR
        bic     r0, r0, #0x00000080
        mcr     p15, 0, r0, c1, c0, 1 ; Write ACTLR
        nop
        bx      lr       
        
/** 
 * \brief Register c1 accesses the CSSELR Register, to select ICache 
 */
        SECTION .CP15_SelectICache:DATA:NOROOT(2)
        PUBLIC   CP15_SelectICache
CP15_SelectICache:
        mrc     p15, 2, r0, c0, c0, 0           ; Read CSSELR
        orr     r0,  r0, #0x1                   ; Change 0th bit to ICache
        mcr     p15, 2, r0, c0, c0, 0           ; Write CSSELR
        nop
        bx      lr
        
/** 
 * \brief Register c1 accesses the CSSELR Register, to select DCache
 */
        SECTION .CP15_SelectDCache:DATA:NOROOT(2)
        PUBLIC   CP15_SelectDCache
CP15_SelectDCache:
        mrc     p15, 2, r0, c0, c0, 0           ; Read CSSELR
        and     r0,  r0, #0xFFFFFFFE            ; Change 0th bit to ICache
        mcr     p15, 2, r0, c0, c0, 0           ; Write CSSELR
        nop
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
        dsb
        isb
        bx      lr

       SECTION .CP15_WriteDomainAccessControl:CODE:NOROOT(2)
       PUBLIC   CP15_WriteDomainAccessControl
CP15_WriteDomainAccessControl:
        mcr     p15, 0, r0, c3, c0, 0
        dsb
        isb
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
       dsb
       isb
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
        isb
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
 * \brief Invalidate entire branch predictor array
 */
        SECTION .CP15_InvalidateBTB:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateBTB
CP15_InvalidateBTB:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c5, 6
        dsb
        isb
        bx      lr

/**
 * \brief Invalidate branch predictor array entry by MVA
 */
        SECTION .CP15_InvalidateBTBbyMva:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateBTBbyMva
CP15_InvalidateBTBbyMva:
        mcr     p15, 0, r0, c7, c5, 7
        bx      lr

/***********************************************************
*
*       ===Data Cache related maintenance functions===
*
**************************************************************/


//      ===Data Cache maintenance by SetWay  === 

/**
 * \brief Invalidate entire data cache by set/way
 */
        SECTION .CP15_InvalidateDcacheBySetWay:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateDcacheBySetWay
CP15_InvalidateDcacheBySetWay:
        mrc     p15, 1, r0, c0, c0, 0
        mov     r1, r0, lsr #3          ; Num of ways
        and     r1, r1, #3              ; 3 is specific to CortexA5 with 32 KB
        mov     r2, r0, lsr #13         ; Num of stes
        and     r2, r2, #0xFF           ; 8bit is specific to CortexA5 with 32 KB        
        mov     r0, #0                  ; 0:SHL:5
inv_way_loop
        lsl     r4, r1, #30
        sub     r1, r1, #1              ; 
        mov     r3, r2
inv_line_loop
        orr     r0, r4, r3, lsl #5
        mcr     p15, 0, r0, c7, c6, 2
        sub     r3, r3, #1              ; 1:SHL:30
        cmp     r3, #0
        bpl     inv_line_loop
        cmp     r1, #-1
        bne     inv_way_loop
        nop
        bx      lr        
        
        
/**
 * \brief Clean entire data cache by set/way
 */
        SECTION .CP15_CleanDCacheBySetWay:CODE:NOROOT(2)
        PUBLIC   CP15_CleanDCacheBySetWay
CP15_CleanDCacheBySetWay:
        mrc     p15, 1, r0, c0, c0, 0
        mov     r1, r0, lsr #3          ; Num of ways
        and     r1, r1, #3              ; 3 is specific to CortexA5 with 32 KB
        mov     r2, r0, lsr #13         ; Num of stes
        and     r2, r2, #0xFF           ; 8bit is specific to CortexA5 with 32 KB        
        mov     r0, #0                  ; 0:SHL:5
clean_way_loop
        lsl     r4, r1, #30
        sub     r1, r1, #1              ; 
        mov     r3, r2
clean_line_loop
        orr     r0, r4, r3, lsl #5
        mcr     p15, 0, r0, c7, c10, 2
        sub     r3, r3, #1              ; 1:SHL:30
        cmp     r3, #0
        bpl     clean_line_loop
        cmp     r1, #-1
        bne     clean_way_loop
        nop
        bx      lr 
        
/**
 * \brief Clean and Invalidate entire data cache by set/way
 */
        SECTION .CP15_CleanInvalidateDCacheBySetWay:CODE:NOROOT(2)
        PUBLIC   CP15_CleanInvalidateDCacheBySetWay
CP15_CleanInvalidateDCacheBySetWay:
        mrc     p15, 1, r0, c0, c0, 0
        mov     r1, r0, lsr #3          ; Num of ways
        and     r1, r1, #3              ; 3 is specific to CortexA5 with 32 KB
        mov     r2, r0, lsr #13         ; Num of stes
        and     r2, r2, #0xFF           ; 8bit is specific to CortexA5 with 32 KB        
        mov     r0, #0                  ; 0:SHL:5
clinv_way_loop
        lsl     r4, r1, #30
        sub     r1, r1, #1              ; 
        mov     r3, r2
clinv_line_loop
        orr     r0, r4, r3, lsl #5
        mcr     p15, 0, r0, c7, c10, 2
        sub     r3, r3, #1              ; 1:SHL:30
        cmp     r3, #0
        bpl     clinv_line_loop
        cmp     r1, #-1
        bne     clinv_way_loop
        dsb
        isb
        bx      lr    
        
        
        
//      ===Data Cache maintenance by VA  === 


/**
 * \brief Invalidate data cache by VA to Poc
 */
        SECTION .CP15_InvalidateDcacheByMva:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateDcacheByMva
CP15_InvalidateDcacheByMva: 
        mov     r2, #0x20                          ;Eight words per line, Cortex-A5 L1 Line Size 32 Bytes
        mov     r3, r0
inv_loop
        mcr     p15, 0, r0, c7, c6, 1
        add     r3, r3, r2
        cmp     r3, r1        
        bls     inv_loop        
        bx      lr


/**
 * \brief Clean data cache by MVA
 */
        SECTION .CP15_CleanDCacheByMva:CODE:NOROOT(2)
        PUBLIC   CP15_CleanDCacheByMva
CP15_CleanDCacheByMva:   
        mov     r2, #0x20                          ;Eight words per line, Cortex-A5 L1 Line Size 32 Bytes
        mov     r3, r0
clean_loop
        mcr     p15, 0, r0, c7, c10, 1
        add     r3, r3, r2
        cmp     r3, r1        
        bls     clean_loop        
        bx      lr
       
/**
 * \brief Clean unified cache by MVA 
 */
        SECTION .CP15_CleanDCacheUMva:CODE:NOROOT(2)
        PUBLIC   CP15_CleanDCacheUMva
CP15_CleanDCacheUMva:
        mov     r0, #0
        mcr     p15, 0, r0, c7, c11, 1
        bx      lr

/**
 * \brief Clean and invalidate data cache by VA to PoC
 */
        SECTION .CP15_CleanInvalidateDcacheByMva:CODE:NOROOT(2)
        PUBLIC   CP15_CleanInvalidateDcacheByMva
CP15_CleanInvalidateDcacheByMva:
        mov     r2, #0x20                          ;Eight words per line, Cortex-A5 L1 Line Size 32 Bytes
        mov     r3, r0
clinv_loop
        mcr     p15, 0, r0, c7, c14, 1
        add     r3, r3, r2
        cmp     r3, r1        
        bls     clinv_loop        
        bx      lr
        
        
/**
 * \brief Invalidate translation table
 */
        SECTION .CP15_InvalidateTranslationTable:CODE:NOROOT(2)
        PUBLIC   CP15_InvalidateTranslationTable
CP15_InvalidateTranslationTable:
        mcr      p15, 0, r0, c8, c3,  0
        dsb
        isb
        mcr      p15, 0, r0, c8, c7,  0
        dsb
        isb   
        bx      lr        
        
/**
 * \brief flush translation table
 */
        SECTION .CP15_FlushTranslationTable:CODE:NOROOT(2)
        PUBLIC   CP15_FlushTranslationTable
CP15_FlushTranslationTable:
        mcr      p15, 0, r0, c8, c3,  0
        dsb
        isb    
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

