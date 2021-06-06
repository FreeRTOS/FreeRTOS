/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */


/******************************************************************************
 * @file     system.c
 * @brief    CSI Device System Source File
 * @version  V1.0
 * @date     02. Oct 2018
 ******************************************************************************/

#include <csi_config.h>
#include <soc.h>
#include <csi_core.h>
#include <drv_irq.h>

#ifndef CONFIG_SYSTICK_HZ
#define CONFIG_SYSTICK_HZ 100
#endif

int g_system_clock = IHS_VALUE;
extern int32_t g_top_irqstack;
extern void irq_vectors_init(void);
extern void mm_heap_initialize(void);

int32_t drv_get_cpu_id(void)
{
    return 0;
}

#ifdef CONFIG_KERNEL_NONE
static void _system_init_for_baremetal(void)
{
    /* enable mexstatus SPUSHEN */
#if ((CONFIG_CPU_E902 != 1) && (CONFIG_CPU_E902M != 1))
    uint32_t mexstatus = __get_MEXSTATUS();
    mexstatus |= (1 << 16);
    __set_MEXSTATUS(mexstatus);
#endif
    __enable_excp_irq();

    csi_coret_config(drv_get_sys_freq() / CONFIG_SYSTICK_HZ, CORET_IRQn);    //10ms

    mm_heap_initialize();
}
#endif

#ifndef CONFIG_KERNEL_NONE
static void _system_init_for_kernel(void)
{
     /* enable mexstatus SPUSHEN and SPSWAPEN */
#if ((CONFIG_CPU_E902 != 1) && (CONFIG_CPU_E902M != 1))
    uint32_t mexstatus = __get_MEXSTATUS();
    mexstatus |= (0x3 << 16);
    __set_MEXSTATUS(mexstatus);
#endif
    irq_vectors_init();

    csi_coret_config(drv_get_sys_freq() / CONFIG_SYSTICK_HZ, CORET_IRQn);    //10ms
    drv_irq_enable(CORET_IRQn);

#ifndef CONFIG_KERNEL_RHINO
#ifndef CONFIG_NUTTXMM_NONE
    mm_heap_initialize();
#endif
#endif
}
#endif

/**
  * @brief  initialize system map
  * @param  None
  * @return None
  */
void systemmap_config(void)
{
   csi_sysmap_config_region(0, 0x20000000, SYSMAP_SYSMAPCFG_B_Msk | SYSMAP_SYSMAPCFG_C_Msk);
   csi_sysmap_config_region(1, 0x40000000, SYSMAP_SYSMAPCFG_B_Msk | SYSMAP_SYSMAPCFG_C_Msk);
   csi_sysmap_config_region(2, 0x50000000, SYSMAP_SYSMAPCFG_SO_Msk);
   csi_sysmap_config_region(3, 0x50700000, SYSMAP_SYSMAPCFG_B_Msk | SYSMAP_SYSMAPCFG_C_Msk);
   csi_sysmap_config_region(4, 0x60000000, SYSMAP_SYSMAPCFG_SO_Msk);
   csi_sysmap_config_region(5, 0x80000000, SYSMAP_SYSMAPCFG_B_Msk | SYSMAP_SYSMAPCFG_C_Msk);
   csi_sysmap_config_region(6, 0x90000000, SYSMAP_SYSMAPCFG_B_Msk | SYSMAP_SYSMAPCFG_C_Msk);
   csi_sysmap_config_region(7, 0xf0000000, SYSMAP_SYSMAPCFG_SO_Msk);
}

/**
  * @brief  initialize the system
  *         Initialize the psr and vbr.
  * @param  None
  * @return None
  */
void SystemInit(void)
{
    int i;
    systemmap_config();
    /* enable mstatus FS */
#if (__riscv_flen)
    uint32_t mstatus = __get_MSTATUS();
    mstatus |= (1 << 13);
    __set_MSTATUS(mstatus);
#endif

    /* get interrupt level from info */
    CLIC->CLICCFG = (((CLIC->CLICINFO & CLIC_INFO_CLICINTCTLBITS_Msk) >> CLIC_INFO_CLICINTCTLBITS_Pos) << CLIC_CLICCFG_NLBIT_Pos);

    for (i = 0; i < 64; i++) {
        CLIC->CLICINT[i].IP = 0;
        CLIC->CLICINT[i].ATTR = 1; /* use vector interrupt */
    }

    /* tspend use positive interrupt */
    CLIC->CLICINT[Machine_Software_IRQn].ATTR = 0x3;

#if ((CONFIG_CPU_E902 != 1) && (CONFIG_CPU_E902M != 1))
    csi_dcache_enable();
#endif
    csi_icache_enable();
    drv_irq_enable(Machine_Software_IRQn);

#ifdef CONFIG_KERNEL_NONE
    _system_init_for_baremetal();
#else
    _system_init_for_kernel();
#endif
}
