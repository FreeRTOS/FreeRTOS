/*
 * Copyright (c) 2015-2016, Freescale Semiconductor, Inc.
 * Copyright 2016-2019 NXP
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_common.h"
#define SDK_MEM_MAGIC_NUMBER 12345U

typedef struct _mem_align_control_block
{
    uint16_t identifier; /*!< Identifier for the memory control block. */
    uint16_t offset;     /*!< offset from aligned address to real address */
} mem_align_cb_t;

/* Component ID definition, used by tools. */
#ifndef FSL_COMPONENT_ID
#define FSL_COMPONENT_ID "platform.drivers.common"
#endif

#ifndef __GIC_PRIO_BITS
#if defined(ENABLE_RAM_VECTOR_TABLE)
uint32_t InstallIRQHandler(IRQn_Type irq, uint32_t irqHandler)
{
/* Addresses for VECTOR_TABLE and VECTOR_RAM come from the linker file */
#if defined(__CC_ARM) || defined(__ARMCC_VERSION)
    extern uint32_t Image$$VECTOR_ROM$$Base[];
    extern uint32_t Image$$VECTOR_RAM$$Base[];
    extern uint32_t Image$$RW_m_data$$Base[];

#define __VECTOR_TABLE Image$$VECTOR_ROM$$Base
#define __VECTOR_RAM Image$$VECTOR_RAM$$Base
#define __RAM_VECTOR_TABLE_SIZE (((uint32_t)Image$$RW_m_data$$Base - (uint32_t)Image$$VECTOR_RAM$$Base))
#elif defined(__ICCARM__)
    extern uint32_t __RAM_VECTOR_TABLE_SIZE[];
    extern uint32_t __VECTOR_TABLE[];
    extern uint32_t __VECTOR_RAM[];
#elif defined(__GNUC__)
    extern uint32_t __VECTOR_TABLE[];
    extern uint32_t __VECTOR_RAM[];
    extern uint32_t __RAM_VECTOR_TABLE_SIZE_BYTES[];
    uint32_t __RAM_VECTOR_TABLE_SIZE = (uint32_t)(__RAM_VECTOR_TABLE_SIZE_BYTES);
#endif /* defined(__CC_ARM) || defined(__ARMCC_VERSION) */
    uint32_t n;
    uint32_t ret;
    uint32_t irqMaskValue;

    irqMaskValue = DisableGlobalIRQ();
    if (SCB->VTOR != (uint32_t)__VECTOR_RAM)
    {
        /* Copy the vector table from ROM to RAM */
        for (n = 0; n < ((uint32_t)__RAM_VECTOR_TABLE_SIZE) / sizeof(uint32_t); n++)
        {
            __VECTOR_RAM[n] = __VECTOR_TABLE[n];
        }
        /* Point the VTOR to the position of vector table */
        SCB->VTOR = (uint32_t)__VECTOR_RAM;
    }

    ret = __VECTOR_RAM[irq + 16];
    /* make sure the __VECTOR_RAM is noncachable */
    __VECTOR_RAM[irq + 16] = irqHandler;

    EnableGlobalIRQ(irqMaskValue);

/* Add for ARM errata 838869, affects Cortex-M4, Cortex-M4F Store immediate overlapping
  exception return operation might vector to incorrect interrupt */
#if defined __CORTEX_M && (__CORTEX_M == 4U)
    __DSB();
#endif

    return ret;
}
#endif /* ENABLE_RAM_VECTOR_TABLE. */
#endif /* __GIC_PRIO_BITS. */

#if (defined(FSL_FEATURE_SOC_SYSCON_COUNT) && (FSL_FEATURE_SOC_SYSCON_COUNT > 0))
#if !(defined(FSL_FEATURE_SYSCON_STARTER_DISCONTINUOUS) && FSL_FEATURE_SYSCON_STARTER_DISCONTINUOUS)

void EnableDeepSleepIRQ(IRQn_Type interrupt)
{
    uint32_t intNumber = (uint32_t)interrupt;

    uint32_t index = 0;

    while (intNumber >= 32u)
    {
        index++;
        intNumber -= 32u;
    }

    SYSCON->STARTERSET[index] = 1u << intNumber;
    EnableIRQ(interrupt); /* also enable interrupt at NVIC */
}

void DisableDeepSleepIRQ(IRQn_Type interrupt)
{
    uint32_t intNumber = (uint32_t)interrupt;

    DisableIRQ(interrupt); /* also disable interrupt at NVIC */
    uint32_t index = 0;

    while (intNumber >= 32u)
    {
        index++;
        intNumber -= 32u;
    }

    SYSCON->STARTERCLR[index] = 1u << intNumber;
}
#endif /* FSL_FEATURE_SYSCON_STARTER_DISCONTINUOUS */
#endif /* FSL_FEATURE_SOC_SYSCON_COUNT */

void *SDK_Malloc(size_t size, size_t alignbytes)
{
    mem_align_cb_t *p_cb = NULL;
    uint32_t alignedsize = SDK_SIZEALIGN(size, alignbytes) + alignbytes + sizeof(mem_align_cb_t);
    union
    {
        void *pointer_value;
        uint32_t unsigned_value;
    } p_align_addr, p_addr;

    p_addr.pointer_value = malloc(alignedsize);

    if (p_addr.pointer_value == NULL)
    {
        return NULL;
    }

    p_align_addr.unsigned_value = SDK_SIZEALIGN(p_addr.unsigned_value + sizeof(mem_align_cb_t), alignbytes);

    p_cb             = (mem_align_cb_t *)(p_align_addr.unsigned_value - 4U);
    p_cb->identifier = SDK_MEM_MAGIC_NUMBER;
    p_cb->offset     = (uint16_t)(p_align_addr.unsigned_value - p_addr.unsigned_value);

    return p_align_addr.pointer_value;
}

void SDK_Free(void *ptr)
{
    union
    {
        void *pointer_value;
        uint32_t unsigned_value;
    } p_free;
    p_free.pointer_value = ptr;
    mem_align_cb_t *p_cb = (mem_align_cb_t *)(p_free.unsigned_value - 4U);

    if (p_cb->identifier != SDK_MEM_MAGIC_NUMBER)
    {
        return;
    }

    p_free.unsigned_value = p_free.unsigned_value - p_cb->offset;

    free(p_free.pointer_value);
}

/*!
 * @brief Delay function bases on while loop, every loop includes three instructions.
 *
 * @param count  Counts of loop needed for dalay.
 */
#ifndef __XCC__
#if defined(__CC_ARM) /* This macro is arm v5 specific */
/* clang-format off */
__ASM static void DelayLoop(uint32_t count)
{
loop
    SUBS R0, R0, #1
    CMP  R0, #0
    BNE  loop
    BX   LR
}
/* clang-format on */
#elif defined(__ARMCC_VERSION) || defined(__ICCARM__) || defined(__GNUC__)
/* Cortex-M0 has a smaller instruction set, SUBS isn't supported in thumb-16 mode reported from __GNUC__ compiler,
 * use SUB and CMP here for compatibility */
static void DelayLoop(uint32_t count)
{
    __ASM volatile("    MOV    R0, %0" : : "r"(count));
    __ASM volatile(
        "loop:                          \n"
#if defined(__GNUC__) && !defined(__ARMCC_VERSION)
        "    SUB    R0, R0, #1          \n"
#else
        "    SUBS   R0, R0, #1          \n"
#endif
        "    CMP    R0, #0              \n"

        "    BNE    loop                \n");
}
#endif /* defined(__CC_ARM) */

/*!
 * @brief Delay at least for some time.
 *  Please note that, this API uses while loop for delay, different run-time environments make the time not precise,
 *  if precise delay count was needed, please implement a new delay function with hardware timer.
 *
 * @param delay_us  Delay time in unit of microsecond.
 * @param coreClock_Hz  Core clock frequency with Hz.
 */
void SDK_DelayAtLeastUs(uint32_t delay_us, uint32_t coreClock_Hz)
{
    assert(0U != delay_us);
    uint64_t count = USEC_TO_COUNT(delay_us, coreClock_Hz);
    assert(count <= UINT32_MAX);

    /* Divide value may be different in various environment to ensure delay is precise.
     * Every loop count includes three instructions, due to Cortex-M7 sometimes executes
     * two instructions in one period, through test here set divide 2. Other M cores use
     * divide 4. By the way, divide 2 or 4 could let odd count lost precision, but it does
     * not matter because other instructions outside while loop is enough to fill the time.
     */
#if (__CORTEX_M == 7)
    count = count / 2U;
#else
    count = count / 4U;
#endif
    DelayLoop((uint32_t)count);
}
#endif
