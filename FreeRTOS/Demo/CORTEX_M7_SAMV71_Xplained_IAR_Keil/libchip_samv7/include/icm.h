/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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

#ifndef _ICM_
#define _ICM_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"


/*------------------------------------------------------------------------------*/
/*         Definition                                                           */
/*------------------------------------------------------------------------------*/
#define ICM_RCFG_CDWBN (0x1u << 0) /**< \brief (ICM_RCFG) Compare Digest or Write Back Digest */
#define ICM_RCFG_WRAP (0x1u << 1) /**< \brief (ICM_RCFG) Wrap Command */
#define ICM_RCFG_EOM (0x1u << 2) /**< \brief (ICM_RCFG) End Of Monitoring */
#define ICM_RCFG_RHIEN (0x1u << 4) /**< \brief (ICM_RCFG) Region Hash Completed interrupt enable */
#define ICM_RCFG_DMIEN (0x1u << 5) /**< \brief (ICM_RCFG) Digest Mismatch interrupt enable */
#define ICM_RCFG_BEIEN (0x1u << 6) /**< \brief (ICM_RCFG) Bus error interrupt enable  */
#define ICM_RCFG_WCIEN (0x1u << 7) /**< \brief (ICM_RCFG) Warp condition interrupt enable  */
#define ICM_RCFG_ECIEN (0x1u << 8) /**< \brief (ICM_RCFG) End bit condition interrupt enable  */
#define ICM_RCFG_SUIEN (0x1u << 9) /**< \brief (ICM_RCFG) Monitoring Status Updated Condition Interrupt Enable  */
#define ICM_RCFG_PROCDLY (0x1u << 10) /**< \brief (ICM_RCFG) Processing Delay*/
#define ICM_RCFG_UALGO_Pos 12
#define ICM_RCFG_UALGO_Msk (0x7u << ICM_RCFG_UALGO_Pos) /**< \brief (ICM_RCFG) User SHA Algorithm */
#define   ICM_RCFG_ALGO_SHA1 (0x0u << 12) /**< \brief (ICM_RCFG) SHA1 algorithm processed */
#define   ICM_RCFG_ALGO_SHA256 (0x1u << 12) /**< \brief (ICM_RCFG) SHA256 algorithm processed */
#define   ICM_RCFG_ALGO_SHA224 (0x4u << 12) /**< \brief (ICM_RCFG) SHA224 algorithm processed */
#define ICM_RCFG_MRPROT_Pos 24
#define ICM_RCFG_MRPROT_Msk (0x3fu << ICM_RCFG_MRPROT_Pos) /**< \brief (ICM_RCFG) Memory Region AHB Protection */
#define ICM_RCFG_MRPROT(value) ((ICM_RCFG_MRPROT_Msk & ((value) << ICM_RCFG_MRPROT_Pos)))

/*------------------------------------------------------------------------------*/
/*         Type                                                                 */
/*------------------------------------------------------------------------------*/

/** \brief Structure ICM region descriptor area. */
typedef struct _LinkedListDescriporIcmRegion
{
    /** the first byte address of the Region. */
    uint32_t icm_raddr;
    /** Configuration Structure Member. */
    uint32_t icm_rcfg;
    /** Control Structure Member. */
    uint32_t icm_rctrl;
    /** Next Address Structure Member. */
    uint32_t icm_rnext;
}LinkedListDescriporIcmRegion;

/*------------------------------------------------------------------------------*/
/*         Exported functions                                                   */
/*------------------------------------------------------------------------------*/
extern void ICM_Enable(void);
extern void ICM_Disable(void);
extern void ICM_SoftReset(void);
extern void ICM_ReComputeHash(uint8_t region);
extern void ICM_EnableMonitor(uint8_t region);
extern void ICM_DisableMonitor(uint8_t region);
extern void ICM_Configure(uint32_t mode);
extern void ICM_EnableIt(uint32_t sources);
extern void ICM_DisableIt(uint32_t sources);
extern uint32_t ICM_GetIntStatus(void);
extern uint32_t ICM_GetStatus(void);
extern uint32_t ICM_GetUStatus(void);
extern void ICM_SetDescStartAddress(uint32_t addr);
extern void ICM_SetHashStartAddress(uint32_t addr);
extern void ICM_SetInitHashValue(uint32_t val);
#endif /* #ifndef _ICM_ */
