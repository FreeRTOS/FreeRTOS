//*****************************************************************************
//
// hw_udma.h - Macros for use in accessing the UDMA registers.
//
// Copyright (c) 2007-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_UDMA_H__
#define __HW_UDMA_H__

//*****************************************************************************
//
// The following are defines for the Micro Direct Memory Access (uDMA) offsets.
//
//*****************************************************************************
#define UDMA_STAT               0x400FF000  // DMA Status
#define UDMA_CFG                0x400FF004  // DMA Configuration
#define UDMA_CTLBASE            0x400FF008  // DMA Channel Control Base Pointer
#define UDMA_ALTBASE            0x400FF00C  // DMA Alternate Channel Control
                                            // Base Pointer
#define UDMA_WAITSTAT           0x400FF010  // DMA Channel Wait on Request
                                            // Status
#define UDMA_SWREQ              0x400FF014  // DMA Channel Software Request
#define UDMA_USEBURSTSET        0x400FF018  // DMA Channel Useburst Set
#define UDMA_USEBURSTCLR        0x400FF01C  // DMA Channel Useburst Clear
#define UDMA_REQMASKSET         0x400FF020  // DMA Channel Request Mask Set
#define UDMA_REQMASKCLR         0x400FF024  // DMA Channel Request Mask Clear
#define UDMA_ENASET             0x400FF028  // DMA Channel Enable Set
#define UDMA_ENACLR             0x400FF02C  // DMA Channel Enable Clear
#define UDMA_ALTSET             0x400FF030  // DMA Channel Primary Alternate
                                            // Set
#define UDMA_ALTCLR             0x400FF034  // DMA Channel Primary Alternate
                                            // Clear
#define UDMA_PRIOSET            0x400FF038  // DMA Channel Priority Set
#define UDMA_PRIOCLR            0x400FF03C  // DMA Channel Priority Clear
#define UDMA_ERRCLR             0x400FF04C  // DMA Bus Error Clear

//*****************************************************************************
//
// Micro Direct Memory Access (uDMA) offsets.
//
//*****************************************************************************
#define UDMA_O_SRCENDP          0x00000000  // DMA Channel Source Address End
                                            // Pointer
#define UDMA_O_DSTENDP          0x00000004  // DMA Channel Destination Address
                                            // End Pointer
#define UDMA_O_CHCTL            0x00000008  // DMA Channel Control Word

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_O_SRCENDP register.
//
//*****************************************************************************
#define UDMA_SRCENDP_ADDR_M     0xFFFFFFFF  // Source Address End Pointer.
#define UDMA_SRCENDP_ADDR_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_STAT register.
//
//*****************************************************************************
#define UDMA_STAT_DMACHANS_M    0x001F0000  // Available DMA Channels Minus 1.
#define UDMA_STAT_STATE_M       0x000000F0  // Control State Machine State.
#define UDMA_STAT_STATE_IDLE    0x00000000  // Idle
#define UDMA_STAT_STATE_RD_CTRL 0x00000010  // Reading channel controller data
#define UDMA_STAT_STATE_RD_SRCENDP \
                                0x00000020  // Reading source end pointer
#define UDMA_STAT_STATE_RD_DSTENDP \
                                0x00000030  // Reading destination end pointer
#define UDMA_STAT_STATE_RD_SRCDAT \
                                0x00000040  // Reading source data
#define UDMA_STAT_STATE_WR_DSTDAT \
                                0x00000050  // Writing destination data
#define UDMA_STAT_STATE_WAIT    0x00000060  // Waiting for DMA request to clear
#define UDMA_STAT_STATE_WR_CTRL 0x00000070  // Writing channel controller data
#define UDMA_STAT_STATE_STALL   0x00000080  // Stalled
#define UDMA_STAT_STATE_DONE    0x00000090  // Done
#define UDMA_STAT_STATE_UNDEF   0x000000A0  // Undefined
#define UDMA_STAT_MASTEN        0x00000001  // Master Enable.
#define UDMA_STAT_DMACHANS_S    16

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_O_DSTENDP register.
//
//*****************************************************************************
#define UDMA_DSTENDP_ADDR_M     0xFFFFFFFF  // Destination Address End Pointer.
#define UDMA_DSTENDP_ADDR_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_CFG register.
//
//*****************************************************************************
#define UDMA_CFG_MASTEN         0x00000001  // Controller Master Enable.

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_CTLBASE register.
//
//*****************************************************************************
#define UDMA_CTLBASE_ADDR_M     0xFFFFFC00  // Channel Control Base Address.
#define UDMA_CTLBASE_ADDR_S     10

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_O_CHCTL register.
//
//*****************************************************************************
#define UDMA_CHCTL_DSTINC_M     0xC0000000  // Destination Address Increment.
#define UDMA_CHCTL_DSTINC_8     0x00000000  // Byte
#define UDMA_CHCTL_DSTINC_16    0x40000000  // Half-word
#define UDMA_CHCTL_DSTINC_32    0x80000000  // Word
#define UDMA_CHCTL_DSTINC_NONE  0xC0000000  // No increment
#define UDMA_CHCTL_DSTSIZE_M    0x30000000  // Destination Data Size.
#define UDMA_CHCTL_DSTSIZE_8    0x00000000  // Byte
#define UDMA_CHCTL_DSTSIZE_16   0x10000000  // Half-word
#define UDMA_CHCTL_DSTSIZE_32   0x20000000  // Word
#define UDMA_CHCTL_SRCINC_M     0x0C000000  // Source Address Increment.
#define UDMA_CHCTL_SRCINC_8     0x00000000  // Byte
#define UDMA_CHCTL_SRCINC_16    0x04000000  // Half-word
#define UDMA_CHCTL_SRCINC_32    0x08000000  // Word
#define UDMA_CHCTL_SRCINC_NONE  0x0C000000  // No increment
#define UDMA_CHCTL_SRCSIZE_M    0x03000000  // Source Data Size.
#define UDMA_CHCTL_SRCSIZE_8    0x00000000  // Byte
#define UDMA_CHCTL_SRCSIZE_16   0x01000000  // Half-word
#define UDMA_CHCTL_SRCSIZE_32   0x02000000  // Word
#define UDMA_CHCTL_ARBSIZE_M    0x0003C000  // Arbitration Size.
#define UDMA_CHCTL_ARBSIZE_1    0x00000000  // 1 Transfer
#define UDMA_CHCTL_ARBSIZE_2    0x00004000  // 2 Transfers
#define UDMA_CHCTL_ARBSIZE_4    0x00008000  // 4 Transfers
#define UDMA_CHCTL_ARBSIZE_8    0x0000C000  // 8 Transfers
#define UDMA_CHCTL_ARBSIZE_16   0x00010000  // 16 Transfers
#define UDMA_CHCTL_ARBSIZE_32   0x00014000  // 32 Transfers
#define UDMA_CHCTL_ARBSIZE_64   0x00018000  // 64 Transfers
#define UDMA_CHCTL_ARBSIZE_128  0x0001C000  // 128 Transfers
#define UDMA_CHCTL_ARBSIZE_256  0x00020000  // 256 Transfers
#define UDMA_CHCTL_ARBSIZE_512  0x00024000  // 512 Transfers
#define UDMA_CHCTL_ARBSIZE_1024 0x00028000  // 1024 Transfers
#define UDMA_CHCTL_XFERSIZE_M   0x00003FF0  // Transfer Size (minus 1).
#define UDMA_CHCTL_NXTUSEBURST  0x00000008  // Next Useburst.
#define UDMA_CHCTL_XFERMODE_M   0x00000007  // DMA Transfer Mode.
#define UDMA_CHCTL_XFERMODE_STOP \
                                0x00000000  // Stop
#define UDMA_CHCTL_XFERMODE_BASIC \
                                0x00000001  // Basic
#define UDMA_CHCTL_XFERMODE_AUTO \
                                0x00000002  // Auto-Request
#define UDMA_CHCTL_XFERMODE_PINGPONG \
                                0x00000003  // Ping-Pong
#define UDMA_CHCTL_XFERMODE_MEM_SG \
                                0x00000004  // Memory Scatter-Gather
#define UDMA_CHCTL_XFERMODE_MEM_SGA \
                                0x00000005  // Alternate Memory Scatter-Gather
#define UDMA_CHCTL_XFERMODE_PER_SG \
                                0x00000006  // Peripheral Scatter-Gather
#define UDMA_CHCTL_XFERMODE_PER_SGA \
                                0x00000007  // Alternate Peripheral
                                            // Scatter-Gather
#define UDMA_CHCTL_XFERSIZE_S   4

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_ALTBASE register.
//
//*****************************************************************************
#define UDMA_ALTBASE_ADDR_M     0xFFFFFFFF  // Alternate Channel Address
                                            // Pointer.
#define UDMA_ALTBASE_ADDR_S     0

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_WAITSTAT register.
//
//*****************************************************************************
#define UDMA_WAITSTAT_WAITREQ_M 0xFFFFFFFF  // Channel [n] Wait Status.
#define UDMA_WAITSTAT_WAITREQ_S 0

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_SWREQ register.
//
//*****************************************************************************
#define UDMA_SWREQ_M            0xFFFFFFFF  // Channel [n] Software Request.
#define UDMA_SWREQ_S            0

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_USEBURSTSET
// register.
//
//*****************************************************************************
#define UDMA_USEBURSTSET_SET_M  0xFFFFFFFF  // Channel [n] Useburst Set.
#define UDMA_USEBURSTSET_SET__0 0x00000000  // No Effect
#define UDMA_USEBURSTSET_SET__1 0x00000001  // Burst Only

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_USEBURSTCLR
// register.
//
//*****************************************************************************
#define UDMA_USEBURSTCLR_CLR_M  0xFFFFFFFF  // Channel [n] Useburst Clear.
#define UDMA_USEBURSTCLR_CLR__0 0x00000000  // No Effect
#define UDMA_USEBURSTCLR_CLR__1 0x00000001  // Single and Burst

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_REQMASKSET
// register.
//
//*****************************************************************************
#define UDMA_REQMASKSET_SET_M   0xFFFFFFFF  // Channel [n] Request Mask Set.
#define UDMA_REQMASKSET_SET__0  0x00000000  // No Effect
#define UDMA_REQMASKSET_SET__1  0x00000001  // Masked

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_REQMASKCLR
// register.
//
//*****************************************************************************
#define UDMA_REQMASKCLR_CLR_M   0xFFFFFFFF  // Channel [n] Request Mask Clear.
#define UDMA_REQMASKCLR_CLR__0  0x00000000  // No Effect
#define UDMA_REQMASKCLR_CLR__1  0x00000001  // Clear Mask

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_ENASET register.
//
//*****************************************************************************
#define UDMA_ENASET_SET_M       0xFFFFFFFF  // Channel [n] Enable Set.
#define UDMA_ENASET_SET__0      0x00000000  // Disabled
#define UDMA_ENASET_SET__1      0x00000001  // Enabled
#define UDMA_ENASET_CHENSET_M   0xFFFFFFFF  // Channel [n] Enable Set.
#define UDMA_ENASET_CHENSET__0  0x00000000  // No Effect
#define UDMA_ENASET_CHENSET__1  0x00000001  // Enable

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_ENACLR register.
//
//*****************************************************************************
#define UDMA_ENACLR_CLR_M       0xFFFFFFFF  // Clear Channel [n] Enable.
#define UDMA_ENACLR_CLR__0      0x00000000  // No Effect
#define UDMA_ENACLR_CLR__1      0x00000001  // Disable

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_ALTSET register.
//
//*****************************************************************************
#define UDMA_ALTSET_SET_M       0xFFFFFFFF  // Channel [n] Alternate Set.
#define UDMA_ALTSET_SET__0      0x00000000  // No Effect
#define UDMA_ALTSET_SET__1      0x00000001  // Alternate

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_ALTCLR register.
//
//*****************************************************************************
#define UDMA_ALTCLR_CLR_M       0xFFFFFFFF  // Channel [n] Alternate Clear.
#define UDMA_ALTCLR_CLR__0      0x00000000  // No Effect
#define UDMA_ALTCLR_CLR__1      0x00000001  // Primary

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_PRIOSET register.
//
//*****************************************************************************
#define UDMA_PRIOSET_SET_M      0xFFFFFFFF  // Channel [n] Priority Set.
#define UDMA_PRIOSET_SET__0     0x00000000  // No Effect
#define UDMA_PRIOSET_SET__1     0x00000001  // High Priority

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_PRIOCLR register.
//
//*****************************************************************************
#define UDMA_PRIOCLR_CLR_M      0xFFFFFFFF  // Channel [n] Priority Clear.
#define UDMA_PRIOCLR_CLR__0     0x00000000  // No Effect
#define UDMA_PRIOCLR_CLR__1     0x00000001  // Default Priority

//*****************************************************************************
//
// The following are defines for the bit fields in the UDMA_ERRCLR register.
//
//*****************************************************************************
#define UDMA_ERRCLR_ERRCLR      0x00000001  // DMA Bus Error Status.

#endif // __HW_UDMA_H__
