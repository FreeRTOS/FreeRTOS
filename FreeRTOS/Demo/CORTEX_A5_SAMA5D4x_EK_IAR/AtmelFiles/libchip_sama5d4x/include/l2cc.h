/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/**
 * \file
 *
 * Interface for Level 2 cache (L2CC) controller.
 *
 */

/** \addtogroup L2cc_module
 * @{
 * \section L2cc_usage Usage
 * - L2CC_IsEnabled: Check if L2CC is enable
 * - L2CC_Enable: Enable L2 cache controller with default parameters
 * - ISI_DisableInterrupt: disable one or more interrupts
 * - ISI_Enable: enable isi module
 * - ISI_Disable: disable isi module
 * - ISI_CodecPathFull: enable codec path
 * - ISI_SetFrame: set frame rate
 * - ISI_BytesForOnePixel: return number of byte for one pixel
 * - ISI_StatusRegister: return ISI status register
 * - ISI_Reset: make a software reset
 */
/**@}*/
#ifndef _L2CC_H
#define _L2CC_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <assert.h>

#ifdef __cplusplus
 extern "C" {
#endif

   
#define ENABLE          1
#define DISABLE         0   
   
#define OFFSET_BIT      5
#define INDEX_BIT       9
#define TAG_BIT         18          
   
#define DCACHE_CLEAN            0
#define DCACHE_INVAL            1
#define DCACHE_FLUSH            2   
   
#define RESET_EVCOUNTER0        0
#define RESET_EVCOUNTER1        1   
#define RESET_BOTH_COUNTER      3

#define FWA_DEFAULT             0
#define FWA_NO_ALLOCATE         1
#define FWA_FORCE_ALLOCATE      2
#define FWA_INTERNALLY_MAPPED   3
 /*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

typedef struct
{
  uint8_t  SetupLAT;
  uint8_t  ReadLAT;
  uint8_t  WriteLAT;
}Latency;

typedef struct
{
  Latency       TagRAM;
  Latency       DataRAM;  
}RAMLatencyControl;
   
/** L2CC structur */
typedef struct
{
    /** High Priority for SO and Dev Reads Enable */
    uint32_t HPSO_Val;
    /** Store Buffer Device Limitation Enable */
    uint32_t SBDLE_Val;
    /** Shared Attribute Invalidate Enable */
    uint32_t SAIE_Val;
    /** Event Monitor Bus Enable */
    uint32_t EMBEN_Val;
    /** Parity Enable */    
    uint32_t PEN_Val;
    /** Shared Attribute Override Enable */    
    uint32_t SAOEN_Val;
    /** Force Write Allocate */    
    uint32_t FWA_Val;
    /** Cache Replacement Policy */    
    uint32_t CRPOL_Val;
    /** Non-Secure Lockdown Enable*/    
    uint32_t NSLEN_Val;
    /** Non-Secure Interrupt Access Control */    
    uint32_t NSIAC_Val;
     /** Data Prefetch Enable*/
    uint32_t DPEN_Val;
    /** Instruction Prefetch Enable */
    uint32_t IPEN_Val;
    /** Prefetch Offset */
    uint32_t OFFSET_Val;
    /** Not Same ID on Exclusive Sequence Enable */
    uint32_t NSIDEN_Val;
    /** INCR Double Linefill Enable */
    uint32_t IDLEN_Val;
    /** Prefetch Drop Enable*/
    uint32_t PDEN_Val;
    /** Double Linefill on WRAP Read Disable */
    uint32_t DLFWRDIS_Val;
    /** Double linefill Enable */
    uint32_t DLEN_Val;
    /** Standby Mode Enable */
    uint32_t STBYEN_Val;
    /** Dynamic Clock Gating Enable */
    uint32_t DCKGATEN_Val;
    /** Disable Cache Linefill*/
    uint32_t DCL_Val;
    /** Disable Write-back, Force Write-through */
    uint32_t DWB_Val;
}L2CC_Control;
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/


extern unsigned int L2CC_IsEnabled(L2cc* pL2CC);
extern void L2CC_Enable(L2cc* pL2CC);
extern void L2CC_Disable(L2cc* pL2CC);
extern void L2CC_ExclusiveCache(L2cc* pL2CC, uint8_t Enable);
extern void L2CC_ConfigLatRAM(L2cc* pL2CC, RAMLatencyControl  *pLat);
extern void L2CC_Config(L2cc* pL2CC, L2CC_Control L2cc_Config);
extern void L2CC_DataPrefetchEnable(L2cc* pL2CC );
extern void L2CC_InstPrefetchEnable(L2cc* pL2CC );
extern void L2CC_EnableResetCounter(L2cc* pL2CC , uint8_t EvenetCounter);
extern void L2CC_EventConfig(L2cc* pL2CC, uint8_t EventCounter, uint8_t Source, uint8_t IntGen);
extern unsigned int L2CC_EventCounterValue(L2cc* pL2CC, uint8_t EventCounter);
extern void L2CC_EnableIT(L2cc* pL2CC, uint16_t ITSource);
extern void L2CC_DisableIT(L2cc* pL2CC, uint16_t ITSource);
extern unsigned short L2CC_ITStatusRaw(L2cc* pL2CC, uint16_t ITSource);
extern unsigned short L2CC_ITStatusMask(L2cc* pL2CC, uint16_t ITSource);
extern void L2CC_ITClear(L2cc* pL2CC, uint16_t ITSource);
uint8_t L2CC_PollSPNIDEN(L2cc* pL2CC);
extern void L2CC_CacheSync(L2cc* pL2CC);
extern void L2CC_InvalidateWay(L2cc* pL2CC, uint8_t Way);
extern void L2CC_CleanWay(L2cc* pL2CC, uint8_t Way);
extern void L2CC_InvalidatePAL(L2cc* pL2CC, uint32_t P_Address);
extern void L2CC_CleanPAL(L2cc* pL2CC, uint32_t P_Address);
extern void L2CC_CleanIx(L2cc* pL2CC, uint32_t P_Address);

extern void L2CC_CleanIndex(L2cc* pL2CC, uint32_t P_Address, uint8_t Way);
extern void L2CC_CleanInvalidateIndex(L2cc* pL2CC, uint32_t P_Address, uint8_t Way);
extern void L2CC_DataLockdown(L2cc* pL2CC, uint8_t Way);
extern void L2CC_InstructionLockdown(L2cc* pL2CC, uint8_t Way);
extern void L2CC_CacheMaintenance(uint8_t Maint_Op);
extern void Enable_L2CC(void);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _L2CC_ */
