/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define CP15_L4_BIT 15 // Determines if the T bit is set when load instructions
                       // change the PC:
                       // 0 = loads to PC set the T bit
                       // 1 = loads to PC do not set T bit

#define CP15_RR_BIT 14 // RR bit Replacement strategy for Icache and Dcache:
                       // 0 = Random replacement
                       // 1 = Round-robin replacement.

#define CP15_V_BIT  13 // V bit Location of exception vectors:
                       // 0 = Normal exception vectors selected address range = 0x0000 0000 to 0x0000 001C
                       // 1 = High exception vect selected, address range = 0xFFFF 0000 to 0xFFFF 001C

#define CP15_I_BIT  12 // I bit Icache enable/disable:
                       // 0 = Icache disabled
                       // 1 = Icache enabled

#define CP15_R_BIT   9 // R bit ROM protection

#define CP15_S_BIT   8 // S bit System protection

#define CP15_B_BIT   7 // B bit Endianness:
                       // 0 = Little-endian operation
                       // 1 = Big-endian operation.

#define CP15_C_BIT   2 // C bit Dcache enable/disable:
                       // 0 = cache disabled
                       // 1 = cache enabled

#define CP15_A_BIT   1 // A bit Alignment fault enable/disable:
                       // 0 = Data address alignment fault checking disabled
                       // 1 = Data address alignment fault checking enabled

#define CP15_M_BIT   0 // M bit MMU enable/disable: 0 = disabled 1 = enabled.
                       // 0 = disabled
                       // 1 = enabled

/** No access Any access generates a domain fault. */
#define CP15_DOMAIN_NO_ACCESS      0x00
/** Client Accesses are checked against the access permission bits in the section or page descriptor. */
#define CP15_DOMAIN_CLIENT_ACCESS  0x01
/** Manager Accesses are not checked against the access permission bits so a permission fault cannot be generated. */
#define CP15_DOMAIN_MANAGER_ACCESS 0x03


/*------------------------------------------------------------------------------ */
/*         Exported functions */
/*------------------------------------------------------------------------------ */
extern unsigned int CP15_ReadID(void);
extern unsigned int CP15_ReadControl(void);
extern void         CP15_WriteControl(unsigned int value);
extern void         CP15_WriteTTB(unsigned int value);
extern void         CP15_WriteDomainAccessControl(unsigned int value);

extern void CP15_InvalidateIcacheInnerSharable(void);
extern void CP15_InvalidateBTBinnerSharable(void);
extern void CP15_InvalidateIcache(void);
extern void CP15_InvalidateIcacheByMva(void);
extern void CP15_FlushBTB(void);
extern void CP15_FlushBTBbyMva(void);
extern void CP15_InvalidateDcacheLineByMva(void);
extern void CP15_InvalidateDcacheLineBySetWay(void);
extern void CP15_CleanDCacheByMva(void);
extern void CP15_CleanDCacheBySetWay(void);
extern void CP15_CleanDCacheMva(void);
extern void CP15_CleanInvalidateDcacheLineByMva(void);
extern void CP15_CleanInvalidateDcacheLine(void);

extern void CP15_coherent_dcache_for_dma (uint32_t startAddr, uint32_t endAddr );
extern void CP15_invalidate_dcache_for_dma (uint32_t startAddr, uint32_t endAddr );
extern void CP15_clean_dcache_for_dma (uint32_t startAddr, uint32_t endAddr );
extern void CP15_flush_dcache_for_dma (uint32_t startAddr, uint32_t endAddr );
extern void CP15_flush_kern_dcache_for_dma (uint32_t startAddr, uint32_t size );


/*------------------------------------------------------------------------------ */
/*         Exported functions  from CP15.c                                       */
/*------------------------------------------------------------------------------ */

/** MMU (Status/Enable/Disable) */
extern unsigned int CP15_IsMMUEnabled(void);
extern void         CP15_EnableMMU(void);
extern void         CP15_DisableMMU(void);

/** I cache (Status/Enable/Disable) */
extern unsigned int CP15_IsIcacheEnabled(void);
extern void         CP15_EnableIcache(void);
extern void         CP15_DisableIcache(void);

/** D cache (Status/Enable/Disable) */
extern unsigned int CP15_IsDcacheEnabled(void);
extern void         CP15_EnableDcache(void);
extern void         CP15_DisableDcache(void);

#endif // #ifndef _CP15_H

