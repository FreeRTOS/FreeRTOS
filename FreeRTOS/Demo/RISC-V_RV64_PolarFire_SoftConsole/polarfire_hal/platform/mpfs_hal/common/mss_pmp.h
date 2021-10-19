/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_pmp.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS PMP configuration using MSS configurator values.
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#ifndef MSS_PMP_H
#define MSS_PMP_H


#ifdef __cplusplus
extern "C" {
#endif

#if !defined (LIBERO_SETTING_MEM_CONFIGS_ENABLED)
#define LIBERO_SETTING_MEM_CONFIGS_ENABLED      0ULL
/* Enabled when bit set to 1                               */
/* PMP                               [0:0]   RW value= 0x0 */
/* MPU                               [1:0]   RW value= 0x0 */
#endif
#define PMP_ENABLED_MASK      1UL
#define MPU_ENABLED_MASK      2UL

/*
 * Bit offsets associated with LIBERO_SETTING_CONTEXT_A_HART_EN and
 * LIBERO_SETTING_CONTEXT_B_HART_EN
 */
#define CONTEXT_EN_MASK_MMUART0        (1U<<0)
#define CONTEXT_EN_MASK_MMUART1        (1U<<1)
#define CONTEXT_EN_MASK_MMUART2        (1U<<2)
#define CONTEXT_EN_MASK_MMUART3        (1U<<3)
#define CONTEXT_EN_MASK_MMUART4        (1U<<4)
#define CONTEXT_EN_MASK_WDOG0          (1U<<5)
#define CONTEXT_EN_MASK_WDOG1          (1U<<6)
#define CONTEXT_EN_MASK_WDOG2          (1U<<7)
#define CONTEXT_EN_MASK_WDOG3          (1U<<8)
#define CONTEXT_EN_MASK_WDOG4          (1U<<9)
#define CONTEXT_EN_MASK_SPI0           (1U<<10)
#define CONTEXT_EN_MASK_SPI1           (1U<<11)
#define CONTEXT_EN_MASK_I2C0           (1U<<12)
#define CONTEXT_EN_MASK_I2C1           (1U<<13)
#define CONTEXT_EN_MASK_CAN0           (1U<<14)
#define CONTEXT_EN_MASK_CAN1           (1U<<15)
#define CONTEXT_EN_MASK_MAC0           (1U<<16)
#define CONTEXT_EN_MASK_MAC1           (1U<<17)
#define CONTEXT_EN_MASK_TIMER          (1U<<18)
#define CONTEXT_EN_MASK_GPIO0          (1U<<19)
#define CONTEXT_EN_MASK_GPIO1          (1U<<20)
#define CONTEXT_EN_MASK_GPIO2          (1U<<21)
#define CONTEXT_EN_MASK_RTC            (1U<<22)
#define CONTEXT_EN_MASK_H2FINT         (1U<<23)
#define CONTEXT_EN_MASK_CRYPTO         (1U<<24)
#define CONTEXT_EN_MASK_USB            (1U<<25)
#define CONTEXT_EN_MASK_QSPIXIP        (1U<<26)
#define CONTEXT_EN_MASK_ATHENA         (1U<<27)
#define CONTEXT_EN_MASK_TRACE          (1U<<28)
#define CONTEXT_EN_MASK_MAILBOX_SC     (1U<<29)
#define CONTEXT_EN_MASK_MMC            (1U<<30)
#define CONTEXT_EN_MASK_CFM            (1U<<31)

/*
 * Bit offsets associated with LIBERO_SETTING_CONTEXT_A_FIC_EN and
 * LIBERO_SETTING_CONTEXT_B_FIC_EN
 */
#define CONTEXT_EN_MASK_FIC0            (1U<<0)
#define CONTEXT_EN_MASK_FIC1            (1U<<1)
#define CONTEXT_EN_MASK_FIC2            (1U<<2)
#define CONTEXT_EN_MASK_FIC3            (1U<<3)


uint8_t pmp_configure(uint8_t hart_id);
void pmp_master_configs(uint8_t hart_id, uint64_t * pmp0cfg);

#ifdef __cplusplus
}
#endif


#endif /* MSS_PMP_H */
