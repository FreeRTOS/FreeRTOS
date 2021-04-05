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
#if ((CONFIG_CPU_E906==1) || (CONFIG_CPU_E906F==1) || (CONFIG_CPU_E906FD==1))
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
#if 0//((CONFIG_CPU_E906==1) || (CONFIG_CPU_E906F==1) || (CONFIG_CPU_E906FD==1))
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
  * @brief  initialize the system
  *         Initialize the psr and vbr.
  * @param  None
  * @return None
  */
void SystemInit(void)
{
    int i;
    /* enable mstatus FS */
#if ((CONFIG_CPU_E906F==1) || (CONFIG_CPU_E906FD==1))
    uint32_t mstatus = __get_MSTATUS();
    mstatus |= (1 << 13);
    __set_MSTATUS(mstatus);
#endif

    /* enable mxstatus THEADISAEE */
    uint32_t mxstatus = __get_MXSTATUS();
    mxstatus |= (1 << 22);
    /* enable mxstatus MM */
#if ((CONFIG_CPU_E906==1) || (CONFIG_CPU_E906F==1) || (CONFIG_CPU_E906FD==1))
    mxstatus |= (1 << 15);
#endif
    __set_MXSTATUS(mxstatus);


    /* get interrupt level from info */
    CLIC->CLICCFG = (((CLIC->CLICINFO & CLIC_INFO_CLICINTCTLBITS_Msk) >> CLIC_INFO_CLICINTCTLBITS_Pos) << CLIC_CLICCFG_NLBIT_Pos);

    for (i = 0; i < 64; i++) {
        CLIC->CLICINT[i].IP = 0;
        CLIC->CLICINT[i].ATTR = 1; /* use vector interrupt */
    }

    /* tspend use positive interrupt */
    CLIC->CLICINT[Machine_Software_IRQn].ATTR = 0x3;

    csi_dcache_enable();
    csi_icache_enable();
    drv_irq_enable(Machine_Software_IRQn);

#ifdef CONFIG_KERNEL_NONE
    _system_init_for_baremetal();
#else
    _system_init_for_kernel();
#endif
}
