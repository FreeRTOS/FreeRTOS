/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 *
 * @file mss_h2f.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief H2F access data structures and functions.
 *
 * Definitions and functions associated with host to fabric interrupt controller.
 *
 */

#ifndef MSS_H2F_H
#define MSS_H2F_H

#include "mpfs_hal_config/mss_sw_config.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
H2F line     Group      Ored (no of interrupts ored to one output line)
0            GPIO            41
1            MMUART,SPI,CAN  9
2            I2C             6
3            MAC0            6
4            MAC1            6
5            WATCHDOGS       10
6            Maintenance     3
7            SCB             1
8            G5C-Message     1
9            DDRC            1
10           G5C-DEVRST      2
11           RTC/USOC        4
12           TIMER           2
13           ENVM, QSPI      2
14           USB             2
15           MMC/SDIO        2
*/

/*==============================================================================
 * Host to Fabric interrupt controller
 *
 * For an interrupt to activate the PENABLE and appropriate HENABLE and PENABLE bits must be set.
 *
 * Note. Since Interrupts 127:94 are not used in the system the enable registers are non-write-able and always read as zeros.
 *
 */

typedef struct
{
    volatile uint32_t ENABLE;     /* bit o: Enables all the H2FINT outputs, bit 31:16 Enables individual H2F outputs */
    volatile uint32_t H2FSTATUS;   /* 15:0 Read back of the 16-bit H2F Interrupts before the H2F and global enable */
    uint32_t filler[2U];        /* fill the gap in the memory map */
    volatile uint32_t PLSTATUS[4U];   /* Indicates that the PLINT interrupt is active before the PLINT enable
                                        i.e. direct read of the PLINT inputs [31:0] from PLSTATUS[0]
                                        direct read of the PLINT inputs [63:32] from PLSTATUS[1]
                                        etc  */
    volatile uint32_t PLENABLE[4U];   /* Enables PLINT interrupts PLENABLE[0] 31:0, PLENABLE[1] 63:32, 95:64, 127:96 */
} H2F_CONTROLLER_Type;

#ifndef H2F_BASE_ADDRESS
#if (LIBERO_SETTING_APBBUS_CR & (1U<<23U))
#define H2F_BASE_ADDRESS 0x28126000     
#else
#define H2F_BASE_ADDRESS 0x20126000     
#endif
#endif

#define H2F_CONTROLLER    ((H2F_CONTROLLER_Type *)H2F_BASE_ADDRESS)

void reset_h2f(void);
void enable_h2f_int_output(uint32_t source_int);
void disable_h2f_int_output(uint32_t source_int);

#ifdef __cplusplus
}
#endif

#endif /* MSS_H2F_H */
