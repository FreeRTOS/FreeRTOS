/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/***************************************************************************
 *
 * @file mss_seg.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief segmentation block defines
 *
 * These blocks allow the DDR memory to be allocated to cached, non-cached
 * regions and trace depending on the amount of DDR memory physically connected.
 * Conceptually an address offset is added/subtracted from the DDR address
 * provided by the Core Complex to point at a base address in the DDR memory.
 *
 * The AXI bus simply passes through the segmentation block, and the address
 * is modified.
 *
 * There are two segmentation blocks, they are grouped into the same address
 * ranges as the MPU blocks. Each one has seven 32-segmentation registers, but
 * only two in SEG0 and five in SEG1 are actually implemented.
 *
 * DDRC blocker - blocks writes to DDR before it is set-up
 * SEG0.CFG[7]
 * Is cleared at reset. When written to '1' disables the blocker function
 * Is allowing the L2 cache controller to access the DDRC.
 * Is Once written to '1' the register cannot be written to 0, only an MSS reset
 * Is will clear the register
 *
 */

#ifndef MSS_SEG_H
#define MSS_SEG_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    union {
        struct {
            volatile int32_t    offset : 15;
            volatile int32_t    rsrvd  : 16;
            volatile int32_t    locked : 1;
        } CFG;
        uint32_t raw;
    } u[8u];

    uint32_t fill[64U-8U];

} seg_t;

#define SEG ((seg_t*) 0x20005d00)

#ifdef __cplusplus
}
#endif

#endif /*MSS_SEG_H*/
