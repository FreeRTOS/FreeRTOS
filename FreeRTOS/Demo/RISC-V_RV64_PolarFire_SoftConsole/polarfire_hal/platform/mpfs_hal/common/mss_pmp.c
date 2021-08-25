/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_pmp.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS PMP configuration using MSS configurator values.
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#include <stdio.h>
#include <string.h>
#include "mpfs_hal/mss_hal.h"

/**
 * \brief PMP configuration from Libero
 *
 */
const uint64_t pmp_values[][18] = {
        /* hart 0 */
        {LIBERO_SETTING_HART0_CSR_PMPCFG0,
        LIBERO_SETTING_HART0_CSR_PMPCFG2,
        LIBERO_SETTING_HART0_CSR_PMPADDR0,
        LIBERO_SETTING_HART0_CSR_PMPADDR1,
        LIBERO_SETTING_HART0_CSR_PMPADDR2,
        LIBERO_SETTING_HART0_CSR_PMPADDR3,
        LIBERO_SETTING_HART0_CSR_PMPADDR4,
        LIBERO_SETTING_HART0_CSR_PMPADDR5,
        LIBERO_SETTING_HART0_CSR_PMPADDR6,
        LIBERO_SETTING_HART0_CSR_PMPADDR7,
        LIBERO_SETTING_HART0_CSR_PMPADDR8,
        LIBERO_SETTING_HART0_CSR_PMPADDR9,
        LIBERO_SETTING_HART0_CSR_PMPADDR10,
        LIBERO_SETTING_HART0_CSR_PMPADDR11,
        LIBERO_SETTING_HART0_CSR_PMPADDR12,
        LIBERO_SETTING_HART0_CSR_PMPADDR13,
        LIBERO_SETTING_HART0_CSR_PMPADDR14,
        LIBERO_SETTING_HART0_CSR_PMPADDR15},
        /* hart 1 */
        {LIBERO_SETTING_HART1_CSR_PMPCFG0,
        LIBERO_SETTING_HART1_CSR_PMPCFG2,
        LIBERO_SETTING_HART1_CSR_PMPADDR0,
        LIBERO_SETTING_HART1_CSR_PMPADDR1,
        LIBERO_SETTING_HART1_CSR_PMPADDR2,
        LIBERO_SETTING_HART1_CSR_PMPADDR3,
        LIBERO_SETTING_HART1_CSR_PMPADDR4,
        LIBERO_SETTING_HART1_CSR_PMPADDR5,
        LIBERO_SETTING_HART1_CSR_PMPADDR6,
        LIBERO_SETTING_HART1_CSR_PMPADDR7,
        LIBERO_SETTING_HART1_CSR_PMPADDR8,
        LIBERO_SETTING_HART1_CSR_PMPADDR9,
        LIBERO_SETTING_HART1_CSR_PMPADDR10,
        LIBERO_SETTING_HART1_CSR_PMPADDR11,
        LIBERO_SETTING_HART1_CSR_PMPADDR12,
        LIBERO_SETTING_HART1_CSR_PMPADDR13,
        LIBERO_SETTING_HART1_CSR_PMPADDR14,
        LIBERO_SETTING_HART1_CSR_PMPADDR15},
        /* hart 2 */
        {LIBERO_SETTING_HART2_CSR_PMPCFG0,
        LIBERO_SETTING_HART2_CSR_PMPCFG2,
        LIBERO_SETTING_HART2_CSR_PMPADDR0,
        LIBERO_SETTING_HART2_CSR_PMPADDR1,
        LIBERO_SETTING_HART2_CSR_PMPADDR2,
        LIBERO_SETTING_HART2_CSR_PMPADDR3,
        LIBERO_SETTING_HART2_CSR_PMPADDR4,
        LIBERO_SETTING_HART2_CSR_PMPADDR5,
        LIBERO_SETTING_HART2_CSR_PMPADDR6,
        LIBERO_SETTING_HART2_CSR_PMPADDR7,
        LIBERO_SETTING_HART2_CSR_PMPADDR8,
        LIBERO_SETTING_HART2_CSR_PMPADDR9,
        LIBERO_SETTING_HART2_CSR_PMPADDR10,
        LIBERO_SETTING_HART2_CSR_PMPADDR11,
        LIBERO_SETTING_HART2_CSR_PMPADDR12,
        LIBERO_SETTING_HART2_CSR_PMPADDR13,
        LIBERO_SETTING_HART2_CSR_PMPADDR14,
        LIBERO_SETTING_HART2_CSR_PMPADDR15},
        /* hart 3 */
        {LIBERO_SETTING_HART3_CSR_PMPCFG0,
        LIBERO_SETTING_HART3_CSR_PMPCFG2,
        LIBERO_SETTING_HART3_CSR_PMPADDR0,
        LIBERO_SETTING_HART3_CSR_PMPADDR1,
        LIBERO_SETTING_HART3_CSR_PMPADDR2,
        LIBERO_SETTING_HART3_CSR_PMPADDR3,
        LIBERO_SETTING_HART3_CSR_PMPADDR4,
        LIBERO_SETTING_HART3_CSR_PMPADDR5,
        LIBERO_SETTING_HART3_CSR_PMPADDR6,
        LIBERO_SETTING_HART3_CSR_PMPADDR7,
        LIBERO_SETTING_HART3_CSR_PMPADDR8,
        LIBERO_SETTING_HART3_CSR_PMPADDR9,
        LIBERO_SETTING_HART3_CSR_PMPADDR10,
        LIBERO_SETTING_HART3_CSR_PMPADDR11,
        LIBERO_SETTING_HART3_CSR_PMPADDR12,
        LIBERO_SETTING_HART3_CSR_PMPADDR13,
        LIBERO_SETTING_HART3_CSR_PMPADDR14,
        LIBERO_SETTING_HART3_CSR_PMPADDR15},
        /* hart 4 */
        {LIBERO_SETTING_HART4_CSR_PMPCFG0,
        LIBERO_SETTING_HART4_CSR_PMPCFG2,
        LIBERO_SETTING_HART4_CSR_PMPADDR0,
        LIBERO_SETTING_HART4_CSR_PMPADDR1,
        LIBERO_SETTING_HART4_CSR_PMPADDR2,
        LIBERO_SETTING_HART4_CSR_PMPADDR3,
        LIBERO_SETTING_HART4_CSR_PMPADDR4,
        LIBERO_SETTING_HART4_CSR_PMPADDR5,
        LIBERO_SETTING_HART4_CSR_PMPADDR6,
        LIBERO_SETTING_HART4_CSR_PMPADDR7,
        LIBERO_SETTING_HART4_CSR_PMPADDR8,
        LIBERO_SETTING_HART4_CSR_PMPADDR9,
        LIBERO_SETTING_HART4_CSR_PMPADDR10,
        LIBERO_SETTING_HART4_CSR_PMPADDR11,
        LIBERO_SETTING_HART4_CSR_PMPADDR12,
        LIBERO_SETTING_HART4_CSR_PMPADDR13,
        LIBERO_SETTING_HART4_CSR_PMPADDR14,
        LIBERO_SETTING_HART4_CSR_PMPADDR15},
};

/**
 * pmp_configure()
 * Set PMP's up with configuration from Libero
 * @param hart_id hart Id
 * @return
 */
uint8_t pmp_configure(uint8_t hart_id) /* set-up with settings from Libero */
{
#if ((LIBERO_SETTING_MEM_CONFIGS_ENABLED & PMP_ENABLED_MASK) == PMP_ENABLED_MASK)
    uint64_t pmp0cfg;
#endif
	/* make sure enables are off */
    write_csr(pmpcfg0, 0);
    write_csr(pmpcfg2, 0);
	/* set required addressing */
    write_csr(pmpaddr0, pmp_values[hart_id][2]);
    write_csr(pmpaddr1, pmp_values[hart_id][3]);
    write_csr(pmpaddr2, pmp_values[hart_id][4]);
    write_csr(pmpaddr3, pmp_values[hart_id][5]);
    write_csr(pmpaddr4, pmp_values[hart_id][6]);
    write_csr(pmpaddr5, pmp_values[hart_id][7]);
    write_csr(pmpaddr6, pmp_values[hart_id][8]);
    write_csr(pmpaddr7, pmp_values[hart_id][9]);
    write_csr(pmpaddr8, pmp_values[hart_id][10]);
    write_csr(pmpaddr9, pmp_values[hart_id][11]);
    write_csr(pmpaddr10, pmp_values[hart_id][12]);
    write_csr(pmpaddr11, pmp_values[hart_id][13]);
    write_csr(pmpaddr12, pmp_values[hart_id][14]);
    write_csr(pmpaddr13, pmp_values[hart_id][15]);
    write_csr(pmpaddr14, pmp_values[hart_id][16]);
    write_csr(pmpaddr15, pmp_values[hart_id][17]);
#if ((LIBERO_SETTING_MEM_CONFIGS_ENABLED & PMP_ENABLED_MASK) == PMP_ENABLED_MASK)
    pmp0cfg = pmp_values[hart_id][0];
    pmp_master_configs(hart_id, &pmp0cfg);
    write_csr(pmpcfg0, pmp0cfg);
    write_csr(pmpcfg2, pmp_values[hart_id][1]);
#endif

    return(0);
}

/*-------------------------------------------------------------------------*//**
  Please note the first four PMP's are set to zero by MSS Configurator v2021.1
  These will need to be set by the HSS. The first three relate to HSS footprint
  The PMP4 is used to open a hole for debug region.

  | PMP | cfg  | L  | XWR | Detail                                             |
  |-----|-----------|-----|----------------------------------------------------|
  |  0  | 0x18 | N  |     | 256KB | Closes access for s and U mode             |
  |  1  | 0x98 | Y  | X R | 256KB | Opens up area for m-mode only              |
  |  2  | 0x98 | Y  | XRW |  64KB | OpenSBI scratch per scratch                |
  |  3  | 0x98 | Y  | XRW |   4KB | Open window for debug                      |
  |  .. | ..   | .. | ..  |  ..   | ..                                         |
  |  15 | 0x18 | Y  |     |   -   | Close everything not opened                |

 @param pmp0cfg return with config for first four PMP's

 */
__attribute__((weak))  void pmp_master_configs(uint8_t hart_id, uint64_t * pmp0cfg)
{
    if ( hart_id == 0U )
    {
        *pmp0cfg = LIBERO_SETTING_HART0_CSR_PMPCFG0;
        write_csr(pmpaddr0, pmp_values[hart_id][2]);
        write_csr(pmpaddr1, pmp_values[hart_id][3]);
        write_csr(pmpaddr2, pmp_values[hart_id][4]);
        write_csr(pmpaddr3, pmp_values[hart_id][5]);
    }
    else
    {
        /*
         * Example of closed memory map, must be created based on HSS footprint
         */
#define CLOSE_S_U_ACCESS_HSS_PMP0_LIM_EG0          0x2007FFFULL   /* 256K LIM */
#define CLOSE_S_U_ACCESS_HSS_PMP0_LIM_EG1          0x200FFFFULL   /* 512K LIM */
#define OPEN_M_ACCESS_HSS_PMP1_LIM_EG0             0x2007FFFULL   /* 256K LIM */
#define OPEN_M_ACCESS_HSS_PMP1_LIM_EG1             0x200FFFFULL   /* 512K LIM */
#define OPEN_M_ACCESS_HSS_PMP1_SCRATCH_EG          0x280FFFFULL   /* 512K SCRATCHPAD */
#define OPEN_CONTEXT_ACCESS_LIM_PMP2_H1            0x2011FFFULL   /*  64K LIM */
#define OPEN_CONTEXT_ACCESS_LIM_PMP2_H2            0x2015FFFULL   /*  64K LIM */
#define OPEN_DEBUG_ACCESS_PMP3                     0x1FFULL
#define HSS_CLOSED_CFG_MASK                        ~0xFFFFFFFFULL
#define HSS_CLOSED_CFG                             0x9F9F9D18ULL
        /*
         * We will open 512K LIM and scratchpad in weak pmp_master_configs()
         * for all harts.
         */
#define  LIM_512K_FROM_BASE                        0x200FFFFULL   /* 512K LIM */
#define  SCRATCH_512K_FROM_BASE                    0x280FFFFULL   /* 512K LIM */
        *pmp0cfg &= HSS_CLOSED_CFG_MASK;
        *pmp0cfg |= 0x9F009F9FULL;  /* open 0,1 and 3 to allow open access */
        write_csr(pmpaddr0, OPEN_M_ACCESS_HSS_PMP1_LIM_EG1);
        write_csr(pmpaddr1, OPEN_M_ACCESS_HSS_PMP1_SCRATCH_EG);
        write_csr(pmpaddr2, 0ULL);
        write_csr(pmpaddr3, OPEN_DEBUG_ACCESS_PMP3);
    }

    /*
     *
     */
#define LOCAL_PMP_SETTINGS
#ifdef LOCAL_PMP_SETTINGS

#endif
    return;
}
