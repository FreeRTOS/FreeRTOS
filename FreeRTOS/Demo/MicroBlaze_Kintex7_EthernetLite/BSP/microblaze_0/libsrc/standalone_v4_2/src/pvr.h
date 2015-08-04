/******************************************************************************
*
* Copyright (C) 2006 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file pvr.h
*
* This header file contains defines for structures used by the microblaze
* PVR routines
*
******************************************************************************/

#ifndef _PVR_H
#define _PVR_H

#include "xil_types.h"
#include "xil_assert.h"
#include "xparameters.h"
#include "mb_interface.h"
#include "bspconfig.h"

#ifdef __cplusplus
extern "C" {
#endif


/* Defs */
typedef struct pvr_s {
#ifdef MICROBLAZE_PVR_FULL
  unsigned int  pvr[16];
#else
  unsigned int  pvr[1];
#endif
} pvr_t;


#define getpvr(pvrid, val)      asm volatile ("mfs\t%0,rpvr" stringify(pvrid) "\n\t" : "=d" (val))

/* Basic PVR mask */
#define MICROBLAZE_PVR0_PVR_FULL_MASK               0x80000000
#define MICROBLAZE_PVR0_USE_BARREL_MASK             0x40000000
#define MICROBLAZE_PVR0_USE_DIV_MASK                0x20000000
#define MICROBLAZE_PVR0_USE_HW_MUL_MASK             0x10000000
#define MICROBLAZE_PVR0_USE_FPU_MASK                0x08000000
#define MICROBLAZE_PVR0_USE_EXCEPTION_MASK          0x04000000
#define MICROBLAZE_PVR0_USE_ICACHE_MASK             0x02000000
#define MICROBLAZE_PVR0_USE_DCACHE_MASK             0x01000000
#define MICROBLAZE_PVR0_USE_MMU_MASK                0x00800000
#define MICROBLAZE_PVR0_USE_BTC_MASK                0x00400000
#define MICROBLAZE_PVR0_ENDIANNESS_MASK             0x00200000
#define MICROBLAZE_PVR0_FAULT_TOLERANT_MASK         0x00100000
#define MICROBLAZE_PVR0_STACK_PROTECTION_MASK       0x00080000
#define MICROBLAZE_PVR0_MICROBLAZE_VERSION_MASK     0x0000FF00
#define MICROBLAZE_PVR0_USER1_MASK                  0x000000FF

/* User 2 PVR mask */
#define MICROBLAZE_PVR1_USER2_MASK                  0xFFFFFFFF

/* Configuration PVR masks */
#define MICROBLAZE_PVR2_D_AXI_MASK                  0x80000000
#define MICROBLAZE_PVR2_D_LMB_MASK                  0x40000000
#define MICROBLAZE_PVR2_D_PLB_MASK                  0x02000000
#define MICROBLAZE_PVR2_I_AXI_MASK                  0x20000000
#define MICROBLAZE_PVR2_I_LMB_MASK                  0x10000000
#define MICROBLAZE_PVR2_I_PLB_MASK                  0x01000000
#define MICROBLAZE_PVR2_INTERRUPT_IS_EDGE_MASK      0x08000000
#define MICROBLAZE_PVR2_EDGE_IS_POSITIVE_MASK       0x04000000
#define MICROBLAZE_PVR2_INTERCONNECT_MASK           0x00800000
#define MICROBLAZE_PVR2_STREAM_INTERCONNECT_MASK    0x00400000
#define MICROBLAZE_PVR2_USE_EXTENDED_FSL_INSTR_MASK 0x00080000
#define MICROBLAZE_PVR2_USE_MSR_INSTR_MASK          0x00020000
#define MICROBLAZE_PVR2_USE_PCMP_INSTR_MASK         0x00010000
#define MICROBLAZE_PVR2_AREA_OPTIMIZED_MASK         0x00008000
#define MICROBLAZE_PVR2_USE_BARREL_MASK             0x00004000
#define MICROBLAZE_PVR2_USE_DIV_MASK                0x00002000
#define MICROBLAZE_PVR2_USE_HW_MUL_MASK             0x00001000
#define MICROBLAZE_PVR2_USE_FPU_MASK                0x00000800
#define MICROBLAZE_PVR2_USE_FPU2_MASK               0x00000200
#define MICROBLAZE_PVR2_USE_MUL64_MASK              0x00000400
#define MICROBLAZE_PVR2_OPCODE_0x0_ILLEGAL_MASK     0x00000040
#define MICROBLAZE_PVR2_UNALIGNED_EXCEPTION_MASK    0x00000020
#define MICROBLAZE_PVR2_ILL_OPCODE_EXCEPTION_MASK   0x00000010
#define MICROBLAZE_PVR2_M_AXI_I_BUS_EXCEPTION_MASK  0x00000008
#define MICROBLAZE_PVR2_M_AXI_D_BUS_EXCEPTION_MASK  0x00000004
#define MICROBLAZE_PVR2_IPLB_BUS_EXCEPTION_MASK     0x00000100
#define MICROBLAZE_PVR2_DPLB_BUS_EXCEPTION_MASK     0x00000080
#define MICROBLAZE_PVR2_DIV_ZERO_EXCEPTION_MASK     0x00000002
#define MICROBLAZE_PVR2_FPU_EXCEPTION_MASK          0x00000001
#define MICROBLAZE_PVR2_FSL_EXCEPTION_MASK          0x00040000

/* Debug and exception PVR masks */
#define MICROBLAZE_PVR3_DEBUG_ENABLED_MASK          0x80000000
#define MICROBLAZE_PVR3_NUMBER_OF_PC_BRK_MASK       0x1E000000
#define MICROBLAZE_PVR3_NUMBER_OF_RD_ADDR_BRK_MASK  0x00380000
#define MICROBLAZE_PVR3_NUMBER_OF_WR_ADDR_BRK_MASK  0x0000E000
#define MICROBLAZE_PVR3_FSL_LINKS_MASK              0x00000380
#define MICROBLAZE_PVR3_BTC_SIZE_MASK               0x00000007

/* ICache config PVR masks */
#define MICROBLAZE_PVR4_USE_ICACHE_MASK              0x80000000
#define MICROBLAZE_PVR4_ICACHE_ADDR_TAG_BITS_MASK    0x7C000000
#define MICROBLAZE_PVR4_ICACHE_ALLOW_WR_MASK         0x01000000
#define MICROBLAZE_PVR4_ICACHE_LINE_LEN_MASK         0x00E00000
#define MICROBLAZE_PVR4_ICACHE_BYTE_SIZE_MASK        0x001F0000
#define MICROBLAZE_PVR4_ICACHE_ALWAYS_USED_MASK      0x00008000
#define MICROBLAZE_PVR4_ICACHE_INTERFACE_MASK        0x00002000
#define MICROBLAZE_PVR4_ICACHE_VICTIMS_MASK          0x00001C00
#define MICROBLAZE_PVR4_ICACHE_STREAMS_MASK          0x00000300
#define MICROBLAZE_PVR4_ICACHE_FORCE_TAG_LUTRAM_MASK 0x00000080
#define MICROBLAZE_PVR4_ICACHE_DATA_WIDTH_MASK       0x00000040

/* DCache config PVR masks */
#define MICROBLAZE_PVR5_USE_DCACHE_MASK              0x80000000
#define MICROBLAZE_PVR5_DCACHE_ADDR_TAG_BITS_MASK    0x7C000000
#define MICROBLAZE_PVR5_DCACHE_ALLOW_WR_MASK         0x01000000
#define MICROBLAZE_PVR5_DCACHE_LINE_LEN_MASK         0x00E00000
#define MICROBLAZE_PVR5_DCACHE_BYTE_SIZE_MASK        0x001F0000
#define MICROBLAZE_PVR5_DCACHE_ALWAYS_USED_MASK      0x00008000
#define MICROBLAZE_PVR5_DCACHE_USE_WRITEBACK_MASK    0x00004000
#define MICROBLAZE_PVR5_DCACHE_INTERFACE_MASK        0x00002000
#define MICROBLAZE_PVR5_DCACHE_VICTIMS_MASK          0x00001C00
#define MICROBLAZE_PVR5_DCACHE_FORCE_TAG_LUTRAM_MASK 0x00000080
#define MICROBLAZE_PVR5_DCACHE_DATA_WIDTH_MASK       0x00000040

/* ICache base address PVR mask */
#define MICROBLAZE_PVR6_ICACHE_BASEADDR_MASK        0xFFFFFFFF

/* ICache high address PVR mask */
#define MICROBLAZE_PVR7_ICACHE_HIGHADDR_MASK        0xFFFFFFFF

/* DCache base address PVR mask */
#define MICROBLAZE_PVR8_DCACHE_BASEADDR_MASK        0xFFFFFFFF

/* DCache high address PVR mask */
#define MICROBLAZE_PVR9_DCACHE_HIGHADDR_MASK        0xFFFFFFFF

/* Target family PVR mask */
#define MICROBLAZE_PVR10_TARGET_FAMILY_MASK         0xFF000000

/* MSR Reset value PVR mask */
#define MICROBLAZE_PVR11_MSR_RESET_VALUE_MASK       0x000007FF

/* MMU value PVR mask */
#define MICROBLAZE_PVR11_MMU_MASK                   0xC0000000
#define MICROBLAZE_PVR11_MMU_ITLB_SIZE_MASK         0x38000000
#define MICROBLAZE_PVR11_MMU_DTLB_SIZE_MASK         0x07000000
#define MICROBLAZE_PVR11_MMU_TLB_ACCESS_MASK        0x00C00000
#define MICROBLAZE_PVR11_MMU_ZONES_MASK             0x003E0000
#define MICROBLAZE_PVR11_MMU_PRIVILEGED_INSTR_MASK  0x00010000

/* PVR access macros */
#define MICROBLAZE_PVR_IS_FULL(_pvr)                 (_pvr.pvr[0] & MICROBLAZE_PVR0_PVR_FULL_MASK)
#define MICROBLAZE_PVR_USE_BARREL(_pvr)              (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_BARREL_MASK)
#define MICROBLAZE_PVR_USE_DIV(_pvr)                 (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_DIV_MASK)
#define MICROBLAZE_PVR_USE_HW_MUL(_pvr)              (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_HW_MUL_MASK)
#define MICROBLAZE_PVR_USE_FPU(_pvr)                 (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_FPU_MASK)
#define MICROBLAZE_PVR_USE_ICACHE(_pvr)              (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_ICACHE_MASK)
#define MICROBLAZE_PVR_USE_DCACHE(_pvr)              (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_DCACHE_MASK)
#define MICROBLAZE_PVR_USE_MMU(_pvr)                 (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_MMU_MASK)
#define MICROBLAZE_PVR_USE_BTC(_pvr)                 (_pvr.pvr[0] & MICROBLAZE_PVR0_USE_BTC_MASK)
#define MICROBLAZE_PVR_ENDIANNESS(_pvr)              (_pvr.pvr[0] & MICROBLAZE_PVR0_ENDIANNESS_MASK)
#define MICROBLAZE_PVR_FAULT_TOLERANT(_pvr)          (_pvr.pvr[0] & MICROBLAZE_PVR0_FAULT_TOLERANT_MASK)
#define MICROBLAZE_PVR_STACK_PROTECTION(_pvr)        (_pvr.pvr[0] & MICROBLAZE_PVR0_STACK_PROTECTION_MASK)
#define MICROBLAZE_PVR_MICROBLAZE_VERSION(_pvr)      ((_pvr.pvr[0] & MICROBLAZE_PVR0_MICROBLAZE_VERSION_MASK) >> 8)
#define MICROBLAZE_PVR_USER1(_pvr)                   (_pvr.pvr[0] & MICROBLAZE_PVR0_USER1_MASK)

#define MICROBLAZE_PVR_USER2(_pvr)                   (_pvr.pvr[1] & MICROBLAZE_PVR1_USER2_MASK)

#define MICROBLAZE_PVR_D_AXI(_pvr)                   (_pvr.pvr[2] & MICROBLAZE_PVR2_D_AXI_MASK)
#define MICROBLAZE_PVR_D_LMB(_pvr)                   (_pvr.pvr[2] & MICROBLAZE_PVR2_D_LMB_MASK)
#define MICROBLAZE_PVR_D_PLB(_pvr)                   (_pvr.pvr[2] & MICROBLAZE_PVR2_D_PLB_MASK)
#define MICROBLAZE_PVR_I_AXI(_pvr)                   (_pvr.pvr[2] & MICROBLAZE_PVR2_I_AXI_MASK)
#define MICROBLAZE_PVR_I_LMB(_pvr)                   (_pvr.pvr[2] & MICROBLAZE_PVR2_I_LMB_MASK)
#define MICROBLAZE_PVR_I_PLB(_pvr)                   (_pvr.pvr[2] & MICROBLAZE_PVR2_I_PLB_MASK)
#define MICROBLAZE_PVR_INTERRUPT_IS_EDGE(_pvr)       (_pvr.pvr[2] & MICROBLAZE_PVR2_INTERRUPT_IS_EDGE_MASK)
#define MICROBLAZE_PVR_EDGE_IS_POSITIVE(_pvr)        (_pvr.pvr[2] & MICROBLAZE_PVR2_EDGE_IS_POSITIVE_MASK)
#define MICROBLAZE_PVR_INTERCONNECT(_pvr)            (_pvr.pvr[2] & MICROBLAZE_PVR2_INTERCONNECT_MASK)
#define MICROBLAZE_PVR_STREAM_INTERCONNECT(_pvr)     (_pvr.pvr[2] & MICROBLAZE_PVR2_STREAM_INTERCONNECT_MASK)
#define MICROBLAZE_PVR_USE_EXTENDED_FSL_INSTR(_pvr)  (_pvr.pvr[2] & MICROBLAZE_PVR2_USE_EXTENDED_FSL_INSTR_MASK)
#define MICROBLAZE_PVR_USE_MSR_INSTR(_pvr)           (_pvr.pvr[2] & MICROBLAZE_PVR2_USE_MSR_INSTR_MASK)
#define MICROBLAZE_PVR_USE_PCMP_INSTR(_pvr)          (_pvr.pvr[2] & MICROBLAZE_PVR2_USE_PCMP_INSTR_MASK)
#define MICROBLAZE_PVR_AREA_OPTIMIZED(_pvr)          (_pvr.pvr[2] & MICROBLAZE_PVR2_AREA_OPTIMIZED_MASK)
#define MICROBLAZE_PVR_USE_MUL64(_pvr)               (_pvr.pvr[2] & MICROBLAZE_PVR2_USE_MUL64_MASK)
#define MICROBLAZE_PVR_OPCODE_0x0_ILLEGAL(_pvr)      (_pvr.pvr[2] & MICROBLAZE_PVR2_OPCODE_0x0_ILLEGAL_MASK)
#define MICROBLAZE_PVR_UNALIGNED_EXCEPTION(_pvr)     (_pvr.pvr[2] & MICROBLAZE_PVR2_UNALIGNED_EXCEPTION_MASK)
#define MICROBLAZE_PVR_ILL_OPCODE_EXCEPTION(_pvr)    (_pvr.pvr[2] & MICROBLAZE_PVR2_ILL_OPCODE_EXCEPTION_MASK)
#define MICROBLAZE_PVR_M_AXI_I_BUS_EXCEPTION(_pvr)   (_pvr.pvr[2] & MICROBLAZE_PVR2_M_AXI_I_BUS_EXCEPTION_MASK)
#define MICROBLAZE_PVR_IPLB_BUS_EXCEPTION(_pvr)      (_pvr.pvr[2] & MICROBLAZE_PVR2_IPLB_BUS_EXCEPTION_MASK)
#define MICROBLAZE_PVR_M_AXI_D_BUS_EXCEPTION(_pvr)   (_pvr.pvr[2] & MICROBLAZE_PVR2_M_AXI_D_BUS_EXCEPTION_MASK)
#define MICROBLAZE_PVR_DPLB_BUS_EXCEPTION(_pvr)      (_pvr.pvr[2] & MICROBLAZE_PVR2_DPLB_BUS_EXCEPTION_MASK)
#define MICROBLAZE_PVR_DIV_ZERO_EXCEPTION(_pvr)      (_pvr.pvr[2] & MICROBLAZE_PVR2_DIV_ZERO_EXCEPTION_MASK)
#define MICROBLAZE_PVR_FPU_EXCEPTION(_pvr)           (_pvr.pvr[2] & MICROBLAZE_PVR2_FPU_EXCEPTION_MASK)
#define MICROBLAZE_PVR_FSL_EXCEPTION(_pvr)           (_pvr.pvr[2] & MICROBLAZE_PVR2_FSL_EXCEPTION_MASK)

#define MICROBLAZE_PVR_DEBUG_ENABLED(_pvr)           (_pvr.pvr[3] & MICROBLAZE_PVR3_DEBUG_ENABLED_MASK)
#define MICROBLAZE_PVR_NUMBER_OF_PC_BRK(_pvr)        ((_pvr.pvr[3] & MICROBLAZE_PVR3_NUMBER_OF_PC_BRK_MASK) >> 25)
#define MICROBLAZE_PVR_NUMBER_OF_RD_ADDR_BRK(_pvr)   ((_pvr.pvr[3] & MICROBLAZE_PVR3_NUMBER_OF_RD_ADDR_BRK_MASK) >> 19)
#define MICROBLAZE_PVR_NUMBER_OF_WR_ADDR_BRK(_pvr)   ((_pvr.pvr[3] & MICROBLAZE_PVR3_NUMBER_OF_WR_ADDR_BRK_MASK) >> 13)
#define MICROBLAZE_PVR_FSL_LINKS(_pvr)               ((_pvr.pvr[3] & MICROBLAZE_PVR3_FSL_LINKS_MASK) >> 7)
#define MICROBLAZE_PVR_BTC_SIZE(_pvr)                (_pvr.pvr[3] & MICROBLAZE_PVR3_BTC_SIZE_MASK)

#define MICROBLAZE_PVR_ICACHE_ADDR_TAG_BITS(_pvr)    ((_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_ADDR_TAG_BITS_MASK) >> 26)
#define MICROBLAZE_PVR_ICACHE_ALLOW_WR(_pvr)         (_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_ALLOW_WR_MASK)
#define MICROBLAZE_PVR_ICACHE_LINE_LEN(_pvr)         (1 << ((_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_LINE_LEN_MASK) >> 21))
#define MICROBLAZE_PVR_ICACHE_BYTE_SIZE(_pvr)        (1 << ((_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_BYTE_SIZE_MASK) >> 16))
#define MICROBLAZE_PVR_ICACHE_ALWAYS_USED(_pvr)      (_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_ALWAYS_USED_MASK)
#define MICROBLAZE_PVR_ICACHE_INTERFACE(_pvr)        (_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_INTERFACE_MASK)
#define MICROBLAZE_PVR_ICACHE_VICTIMS(_pvr)          ((_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_VICTIMS_MASK) >> 10)
#define MICROBLAZE_PVR_ICACHE_STREAMS(_pvr)          ((_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_STREAMS_MASK) >> 8)
#define MICROBLAZE_PVR_ICACHE_FORCE_TAG_LUTRAM(_pvr) (_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_FORCE_TAG_LUTRAM_MASK)
#define MICROBLAZE_PVR_ICACHE_DATA_WIDTH(_pvr)       (_pvr.pvr[4] & MICROBLAZE_PVR4_ICACHE_DATA_WIDTH_MASK)

#define MICROBLAZE_PVR_DCACHE_ADDR_TAG_BITS(_pvr)    ((_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_ADDR_TAG_BITS_MASK) >> 26)
#define MICROBLAZE_PVR_DCACHE_ALLOW_WR(_pvr)         (_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_ALLOW_WR_MASK)
#define MICROBLAZE_PVR_DCACHE_LINE_LEN(_pvr)         (1 << ((_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_LINE_LEN_MASK) >> 21))
#define MICROBLAZE_PVR_DCACHE_BYTE_SIZE(_pvr)        (1 << ((_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_BYTE_SIZE_MASK) >> 16))
#define MICROBLAZE_PVR_DCACHE_ALWAYS_USED(_pvr)      (_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_ALWAYS_USED_MASK)
#define MICROBLAZE_PVR_DCACHE_USE_WRITEBACK(_pvr)    (_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_USE_WRITEBACK_MASK)
#define MICROBLAZE_PVR_DCACHE_INTERFACE(_pvr)        (_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_INTERFACE_MASK)
#define MICROBLAZE_PVR_DCACHE_VICTIMS(_pvr)          ((_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_VICTIMS_MASK) >> 10)
#define MICROBLAZE_PVR_DCACHE_FORCE_TAG_LUTRAM(_pvr) (_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_FORCE_TAG_LUTRAM_MASK)
#define MICROBLAZE_PVR_DCACHE_DATA_WIDTH(_pvr)       (_pvr.pvr[5] & MICROBLAZE_PVR5_DCACHE_DATA_WIDTH_MASK)

#define MICROBLAZE_PVR_ICACHE_BASEADDR(_pvr)         (_pvr.pvr[6] & MICROBLAZE_PVR6_ICACHE_BASEADDR_MASK)
#define MICROBLAZE_PVR_ICACHE_HIGHADDR(_pvr)         (_pvr.pvr[7] & MICROBLAZE_PVR7_ICACHE_HIGHADDR_MASK)

#define MICROBLAZE_PVR_DCACHE_BASEADDR(_pvr)         (_pvr.pvr[8] & MICROBLAZE_PVR8_DCACHE_BASEADDR_MASK)
#define MICROBLAZE_PVR_DCACHE_HIGHADDR(_pvr)         (_pvr.pvr[9] & MICROBLAZE_PVR9_DCACHE_HIGHADDR_MASK)

#define MICROBLAZE_PVR_TARGET_FAMILY(_pvr)           ((_pvr.pvr[10] & MICROBLAZE_PVR10_TARGET_FAMILY_MASK) >> 24)

#define MICROBLAZE_PVR_MSR_RESET_VALUE(_pvr)         (_pvr.pvr[11] & MICROBLAZE_PVR11_MSR_RESET_VALUE_MASK)

#define MICROBLAZE_PVR_MMU_TYPE(_pvr)                ((_pvr.pvr[11] & MICROBLAZE_PVR11_MMU_MASK) >> 30)
#define MICROBLAZE_PVR_MMU_ITLB_SIZE(_pvr)           ((_pvr.pvr[11] & MICROBLAZE_PVR11_MMU_ITLB_SIZE_MASK) >> 27)
#define MICROBLAZE_PVR_MMU_DTLB_SIZE(_pvr)           ((_pvr.pvr[11] & MICROBLAZE_PVR11_MMU_DTLB_SIZE_MASK) >> 24)
#define MICROBLAZE_PVR_MMU_TLB_ACCESS(_pvr)          ((_pvr.pvr[11] & MICROBLAZE_PVR11_MMU_TLB_ACCESS_MASK) >> 22)
#define MICROBLAZE_PVR_MMU_ZONES(_pvr)               ((_pvr.pvr[11] & MICROBLAZE_PVR11_MMU_ZONES_MASK) >> 17)
#define MICROBLAZE_PVR_MMU_PRIVILEGED_INSTR(_pvr)    ((_pvr.pvr[11] & MICROBLAZE_PVR11_MMU_PRIVILEGED_INSTR_MASK) >> 16)

/* Protos */
int microblaze_get_pvr (pvr_t *pvr);

#ifdef __cplusplus
}
#endif
#endif /* _PVR_H */

