/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_mpu.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS MPU driver for configuring access regions for the
 * external masters.
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#include <stdio.h>
#include <string.h>
#include "mpfs_hal/mss_hal.h"

#ifndef SIFIVE_HIFIVE_UNLEASHED

static uint64_t pmp_get_napot_base_and_range(uint64_t reg, uint64_t *range);

uint8_t num_pmp_lut[10U] = {16U,16U,8U,4U,8U,8U,4U,4U,8U,2U};

/**
 * \brief MPU configuration from Libero for FIC0
 *
 */
const uint64_t    mpu_fic0_values[] = {
    LIBERO_SETTING_FIC0_MPU_CFG_PMP0,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP1,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP2,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP3,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP4,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP5,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP6,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP7,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP8,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP9,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP10,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP11,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP12,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP13,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP14,
    LIBERO_SETTING_FIC0_MPU_CFG_PMP15
};

/**
 * \brief MPU configuration from Libero for FIC1
 *
 */
const uint64_t    mpu_fic1_values[] = {
    LIBERO_SETTING_FIC1_MPU_CFG_PMP0,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP1,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP2,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP3,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP4,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP5,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP6,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP7,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP8,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP9,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP10,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP11,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP12,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP13,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP14,
    LIBERO_SETTING_FIC1_MPU_CFG_PMP15
};

/**
 * \brief MPU configuration from Libero for FIC2
 *
 */
const uint64_t    mpu_fic2_values[] = {
    LIBERO_SETTING_FIC2_MPU_CFG_PMP0,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP1,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP2,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP3,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP4,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP5,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP6,
    LIBERO_SETTING_FIC2_MPU_CFG_PMP7,
};

/**
 * \brief MPU configuration from Libero for ATHENA
 *
 */
const uint64_t    mpu_crypto_values[] = {
    LIBERO_SETTING_CRYPTO_MPU_CFG_PMP0,
    LIBERO_SETTING_CRYPTO_MPU_CFG_PMP1,
    LIBERO_SETTING_CRYPTO_MPU_CFG_PMP2,
    LIBERO_SETTING_CRYPTO_MPU_CFG_PMP3,
};

/**
 * \brief MPU configuration from Libero for GEM0
 *
 */
const uint64_t    mpu_gem0_values[] = {
    LIBERO_SETTING_GEM0_MPU_CFG_PMP0,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP1,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP2,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP3,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP4,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP5,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP6,
    LIBERO_SETTING_GEM0_MPU_CFG_PMP7,
};

/**
 * \brief MPU configuration from Libero for GEM1
 *
 */
const uint64_t    mpu_gem1_values[] = {
    LIBERO_SETTING_GEM1_MPU_CFG_PMP0,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP1,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP2,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP3,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP4,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP5,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP6,
    LIBERO_SETTING_GEM1_MPU_CFG_PMP7,
};

/**
 * \brief MPU configuration from Libero for MMC
 *
 */
const uint64_t    mpu_mmc_values[] = {
    LIBERO_SETTING_MMC_MPU_CFG_PMP0,
    LIBERO_SETTING_MMC_MPU_CFG_PMP1,
    LIBERO_SETTING_MMC_MPU_CFG_PMP2,
    LIBERO_SETTING_MMC_MPU_CFG_PMP3,
};

/**
 * \brief MPU configuration from Libero for SCB
 *
 */
const uint64_t    mpu_scb_values[] = {
    LIBERO_SETTING_SCB_MPU_CFG_PMP0,
    LIBERO_SETTING_SCB_MPU_CFG_PMP1,
    LIBERO_SETTING_SCB_MPU_CFG_PMP2,
    LIBERO_SETTING_SCB_MPU_CFG_PMP3,
    LIBERO_SETTING_SCB_MPU_CFG_PMP4,
    LIBERO_SETTING_SCB_MPU_CFG_PMP5,
    LIBERO_SETTING_SCB_MPU_CFG_PMP6,
    LIBERO_SETTING_SCB_MPU_CFG_PMP7,
};

/**
 * \brief MPU configuration from Libero for USB
 *
 */
const uint64_t    mpu_usb_values[] = {
    LIBERO_SETTING_USB_MPU_CFG_PMP0,
    LIBERO_SETTING_USB_MPU_CFG_PMP1,
    LIBERO_SETTING_USB_MPU_CFG_PMP2,
    LIBERO_SETTING_USB_MPU_CFG_PMP3,
};

/**
 * \brief MPU configuration from Libero for TRACE
 *
 */
const uint64_t    mpu_trace_values[] = {
    LIBERO_SETTING_TRACE_MPU_CFG_PMP0,
    LIBERO_SETTING_TRACE_MPU_CFG_PMP1,
};


/***************************************************************************//**
 * MSS_MPU_auto_configure()
 * Set MPU's up with configuration from Libero
 *
 *
 * @return
 */
uint8_t mpu_configure(void)
{
    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_FIC0)->PMPCFG)),
                 &(mpu_fic0_values),
                 sizeof(mpu_fic0_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_FIC1)->PMPCFG)),
                &(mpu_fic1_values),
                sizeof(mpu_fic1_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_FIC2)->PMPCFG)),
                &(mpu_fic2_values),
                sizeof(mpu_fic2_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_CRYPTO)->PMPCFG)),
                &(mpu_crypto_values),
                sizeof(mpu_crypto_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_GEM0)->PMPCFG)),
                &(mpu_gem0_values),
                sizeof(mpu_gem0_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_GEM1)->PMPCFG)),
                &(mpu_gem1_values),
                sizeof(mpu_gem1_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_USB)->PMPCFG)),
                &(mpu_usb_values),
                sizeof(mpu_usb_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_MMC)->PMPCFG)),
                &(mpu_mmc_values),
                sizeof(mpu_mmc_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_SCB)->PMPCFG)),
                &(mpu_scb_values),
                sizeof(mpu_scb_values));

    config_64_copy((void *)(&(MSS_MPU(MSS_MPU_TRACE)->PMPCFG)),
                &(mpu_trace_values),
                sizeof(mpu_trace_values));

    return(0);
}





/***************************************************************************//**
*/
uint8_t MSS_MPU_configure(mss_mpu_mport_t master_port,
                                        mss_mpu_pmp_region_t pmp_region,
                                        uint64_t base,
                                        uint64_t size,
                                        uint8_t permission,
                                        mss_mpu_addrm_t matching_mode,
                                        uint8_t lock_en)
{
    uint64_t temp = size, cnt=0ULL;
    uint64_t range;

    /*size must be minimum 4k
      Size must be power of 2
      different masters have different number of regions*/
    if((size >= 4096ULL) && (0U == (size & (size - 1U))) && (pmp_region < num_pmp_lut[master_port]))
    {
        while((0 == (temp & 0x01U)))
        {
            cnt++;
            temp >>= 1U;
        }

        range = (1ULL << (cnt-1U))-1U;

        MSS_MPU(master_port)->PMPCFG[pmp_region].raw = (base | range) >> 2U;

        MSS_MPU(master_port)->PMPCFG[pmp_region].MPUCFG_TypeDef.mode = (uint8_t)(permission |
                                              (uint8_t)(matching_mode << 3U) |
                                                        (lock_en << 0x7U));

        return ((uint8_t)0);
    }
    else
    {
        return ((uint8_t)1);
    }
}

uint8_t MSS_MPU_get_config(mss_mpu_mport_t master_port,
                           mss_mpu_pmp_region_t pmp_region,
                           uint64_t* base,
                           uint64_t* size,
                           uint8_t* permission,
                           mss_mpu_addrm_t* matching_mode,
                           uint8_t* lock_en)
{
    uint64_t reg;

    /*All AXI external masters dont have same number of PMP regions*/
    if(pmp_region < num_pmp_lut[master_port])
    {
        reg = MSS_MPU(master_port)->PMPCFG[pmp_region].MPUCFG_TypeDef.pmp;
        *base = pmp_get_napot_base_and_range(reg, size);

        reg = MSS_MPU(master_port)->PMPCFG[pmp_region].MPUCFG_TypeDef.mode;
        *lock_en = ( reg >> 0x7U) & 0x1U;
        *matching_mode = (mss_mpu_addrm_t)( (reg >> 3ULL) & 0x3U);
        *permission = reg & 0x7U;

        return ((uint8_t)0);
    }
    else
    {
        return ((uint8_t)1);
    }
}

static uint64_t pmp_get_napot_base_and_range(uint64_t reg, uint64_t *range)
{
    /* construct a mask of all bits bar the top bit */
    uint64_t mask = 0U;
    uint64_t base = reg;
    uint64_t numbits = (sizeof(uint64_t) * 8U) + 2U;
    mask = (mask - 1U) >> 1U;

    while (mask)
    {
        if ((reg & mask) == mask)
        {
            /* this is the mask to use */
            base = reg & ~mask;
            break;
        }
        mask >>= 1U;
        numbits--;
    }

    *range = (1LU << numbits);
    return (base << 2U);
}

#endif
