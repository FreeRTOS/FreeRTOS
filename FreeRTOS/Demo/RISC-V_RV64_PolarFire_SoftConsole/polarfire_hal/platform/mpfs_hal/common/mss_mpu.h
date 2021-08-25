/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_mpu.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS MPU driver APIs for configuring access regions for
 * the external masters.
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#ifndef MSS_MPU_H
#define MSS_MPU_H

#include <stdint.h>


#ifdef __cplusplus
extern "C" {
#endif

#ifndef SIFIVE_HIFIVE_UNLEASHED

/***************************************************************************//**

 */
#define MPU_MODE_READ_ACCESS       (1U << 0U)
#define MPU_MODE_WRITE_ACCESS      (1U << 1U)
#define MPU_MODE_EXEC_ACCESS       (1U << 2U)

typedef enum {
    MSS_MPU_FIC0    = 0x00,
    MSS_MPU_FIC1,
    MSS_MPU_FIC2,
    MSS_MPU_CRYPTO,
    MSS_MPU_GEM0,
    MSS_MPU_GEM1,
    MSS_MPU_USB,
    MSS_MPU_MMC,
    MSS_MPU_SCB,
    MSS_MPU_TRACE,
    MSS_MPU_SEG0,
    MSS_MPU_SEG1,
} mss_mpu_mport_t;

typedef enum {
    MSS_MPU_AM_OFF    = 0x00U,
    MSS_MPU_AM_NAPOT  = 0x03U,
} mss_mpu_addrm_t;

typedef enum {
    MSS_MPU_PMP_REGION0    = 0x00,
    MSS_MPU_PMP_REGION1,
    MSS_MPU_PMP_REGION2,
    MSS_MPU_PMP_REGION3,
    MSS_MPU_PMP_REGION4,
    MSS_MPU_PMP_REGION5,
    MSS_MPU_PMP_REGION6,
    MSS_MPU_PMP_REGION7,
    MSS_MPU_PMP_REGION8,
    MSS_MPU_PMP_REGION9,
    MSS_MPU_PMP_REGION10,
    MSS_MPU_PMP_REGION11,
    MSS_MPU_PMP_REGION12,
    MSS_MPU_PMP_REGION13,
    MSS_MPU_PMP_REGION14,
    MSS_MPU_PMP_REGION15,
} mss_mpu_pmp_region_t;

extern uint8_t num_pmp_lut[10];

#ifndef __I
#define __I  const volatile
#endif
#ifndef __IO
#define __IO volatile
#endif
#ifndef __O
#define __O volatile
#endif


typedef struct {
    union {
        struct
        {
            __IO uint64_t  pmp   : 38;
            __IO uint64_t  rsrvd : 18;
            __IO uint64_t  mode  : 8;
        } MPUCFG_TypeDef;
        uint64_t raw;
    };
} MPU_CFG;

typedef struct
{
    __IO uint64_t  addr   : 38;
    __IO uint64_t  rw     : 1;
    __IO uint64_t  id     : 4;
    __IO uint64_t  failed : 1;
    __IO uint64_t  padding : (64-44);
} MPU_FailStatus_TypeDef;

typedef struct
{
    MPU_CFG               PMPCFG[16U];
    __IO MPU_FailStatus_TypeDef  STATUS;
} MPU_TypeDef;



#define MSS_MPU(master)                ( (MPU_TypeDef*) (0x20005000UL + ((master) << 8U)))


uint8_t mpu_configure(void);


uint8_t MSS_MPU_configure(mss_mpu_mport_t master_port,
                                        mss_mpu_pmp_region_t pmp_region,
                                        uint64_t base,
                                        uint64_t size,
                                        uint8_t permission,
                                        mss_mpu_addrm_t matching_mode,
                                        uint8_t lock_en);

uint8_t MSS_MPU_get_config(mss_mpu_mport_t master_port,
                           mss_mpu_pmp_region_t pmp_region,
                           uint64_t* base,
                           uint64_t* size,
                           uint8_t* permission,
                           mss_mpu_addrm_t* matching_mode,
                           uint8_t* lock_en);

static inline uint8_t MSS_MPU_lock_region(mss_mpu_mport_t master_port,
                                        mss_mpu_pmp_region_t pmp_region)
{
    if(pmp_region < num_pmp_lut[master_port])
    {
        MSS_MPU(master_port)->PMPCFG[pmp_region].MPUCFG_TypeDef.mode |= (0x1U << 7U);
        return (0U);
    }
    else
    {
        return (1U);
    }
}

/*permission value could be bitwise or of:
 * MPU_MODE_READ_ACCESS
 * MPU_MODE_WRITE_ACCESS
 * MPU_MODE_EXEC_ACCESS
 *
 * */
static inline uint8_t MSS_MPU_set_permission(mss_mpu_mport_t master_port,
                                             mss_mpu_pmp_region_t pmp_region,
                                             uint8_t permission)
{
    if(pmp_region < num_pmp_lut[master_port])
    {
        MSS_MPU(master_port)->PMPCFG[pmp_region].MPUCFG_TypeDef.mode |= permission;
        return (0U);
    }
    else
    {
        return (1U);
    }
}

static inline uint8_t MSS_MPU_get_permission(mss_mpu_mport_t master_port,
                                             mss_mpu_pmp_region_t pmp_region,
                                             uint8_t* permission)
{
    if(pmp_region < num_pmp_lut[master_port])
    {
        *permission = MSS_MPU(master_port)->PMPCFG[pmp_region].MPUCFG_TypeDef.mode & 0x7U;
        return (0U);
    }
    else
    {
        return (1U);
    }
}

/*read the Fail status register when there is a MPU access failure.
 See the return type MPU_FailStatus_TypeDef for the details of the STATUS bitfield.
 The status failed bit(offset 42) needs to be reset using the corresponding bit
 in SYSREG->mpu_violation_sr
 */
static inline MPU_FailStatus_TypeDef MSS_MPU_get_failstatus(mss_mpu_mport_t master_port)
{
    return (MSS_MPU(master_port)->STATUS);
}

#endif /* ! SIFIVE_HIFIVE_UNLEASHED */

#ifdef __cplusplus
}
#endif


#endif /* MSS_MPU_H */
