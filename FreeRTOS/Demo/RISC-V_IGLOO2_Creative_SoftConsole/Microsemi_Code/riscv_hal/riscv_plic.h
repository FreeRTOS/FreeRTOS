/*******************************************************************************
 * (c) Copyright 2016-2018 Microsemi SoC Products Group.  All rights reserved.
 *
 * @file riscv_plic.h
 * @author Microsemi SoC Products Group
 * @brief Mi-V soft processor PLIC and PRCI access data structures and functions.
 *
 * SVN $Revision: 9838 $
 * SVN $Date: 2018-03-19 19:22:54 +0530 (Mon, 19 Mar 2018) $
 */
#ifndef RISCV_PLIC_H
#define RISCV_PLIC_H

#include <stdint.h>

#include "encoding.h"

#ifdef __cplusplus
extern "C" {
#endif

#define PLIC_NUM_SOURCES 31
#define PLIC_NUM_PRIORITIES 0

/*==============================================================================
 * Interrupt numbers:
 */
typedef enum
{
    NoInterrupt_IRQn = 0,
    External_1_IRQn  = 1,
    External_2_IRQn  = 2,
    External_3_IRQn  = 3, 
    External_4_IRQn  = 4,
    External_5_IRQn  = 5,
    External_6_IRQn  = 6,
    External_7_IRQn  = 7,
    External_8_IRQn  = 8,
    External_9_IRQn  = 9,
    External_10_IRQn = 10,
    External_11_IRQn = 11,
    External_12_IRQn = 12,
    External_13_IRQn = 13,
    External_14_IRQn = 14,
    External_15_IRQn = 15,
    External_16_IRQn = 16,
    External_17_IRQn = 17,
    External_18_IRQn = 18,
    External_19_IRQn = 19,
    External_20_IRQn = 20,
    External_21_IRQn = 21,
    External_22_IRQn = 22,
    External_23_IRQn = 23,
    External_24_IRQn = 24,
    External_25_IRQn = 25,
    External_26_IRQn = 26,
    External_27_IRQn = 27,
    External_28_IRQn = 28,
    External_29_IRQn = 29,
    External_30_IRQn = 30,
    External_31_IRQn = 31
} IRQn_Type;


/*==============================================================================
 * PLIC: Platform Level Interrupt Controller
 */
#define PLIC_BASE_ADDR 0x40000000UL

typedef struct
{
    volatile uint32_t PRIORITY_THRESHOLD;
    volatile uint32_t CLAIM_COMPLETE;
    volatile uint32_t reserved[1022];
} IRQ_Target_Type;

typedef struct
{
    volatile uint32_t ENABLES[32];
} Target_Enables_Type;

typedef struct
{
    /*-------------------- Source Priority --------------------*/
    volatile uint32_t SOURCE_PRIORITY[1024];
    
    /*-------------------- Pending array --------------------*/
    volatile const uint32_t PENDING_ARRAY[32];
    volatile uint32_t RESERVED1[992];
    
    /*-------------------- Target enables --------------------*/
    volatile Target_Enables_Type TARGET_ENABLES[15808];

    volatile uint32_t RESERVED2[16384];
    
    /*--- Target Priority threshold and claim/complete---------*/
    IRQ_Target_Type TARGET[15872];
    
} PLIC_Type;


#define PLIC    ((PLIC_Type *)PLIC_BASE_ADDR)

/*==============================================================================
 * PRCI: Power, Reset, Clock, Interrupt
 */
#define PRCI_BASE   0x44000000UL

typedef struct
{
    volatile uint32_t MSIP[4095];
    volatile uint32_t reserved;
    volatile uint64_t MTIMECMP[4095];
    volatile const uint64_t MTIME;
} PRCI_Type;

#define PRCI    ((PRCI_Type *)PRCI_BASE) 

/*==============================================================================
 * The function PLIC_init() initializes the PLIC controller and enables the 
 * global external interrupt bit.
 */
static inline void PLIC_init(void)
{
    uint32_t inc;
    unsigned long hart_id = read_csr(mhartid);

    /* Disable all interrupts for the current hart. */
    for(inc = 0; inc < ((PLIC_NUM_SOURCES + 32u) / 32u); ++inc)
    {
        PLIC->TARGET_ENABLES[hart_id].ENABLES[inc] = 0;
    }

    /* Set priorities to zero. */
    /* Should this really be done??? Calling PLIC_init() on one hart will cause
    * the priorities previously set by other harts to be messed up. */
    for(inc = 0; inc < PLIC_NUM_SOURCES; ++inc)
    {
        PLIC->SOURCE_PRIORITY[inc] = 0;
    }

    /* Set the threshold to zero. */
    PLIC->TARGET[hart_id].PRIORITY_THRESHOLD = 0;

    /* Enable machine external interrupts. */
    set_csr(mie, MIP_MEIP);
}

/*==============================================================================
 * The function PLIC_EnableIRQ() enables the external interrupt for the interrupt
 * number indicated by the parameter IRQn.
 */
static inline void PLIC_EnableIRQ(IRQn_Type IRQn)
{
    unsigned long hart_id = read_csr(mhartid);
    uint32_t current = PLIC->TARGET_ENABLES[hart_id].ENABLES[IRQn / 32];
    current |= (uint32_t)1 << (IRQn % 32);
    PLIC->TARGET_ENABLES[hart_id].ENABLES[IRQn / 32] = current;
}

/*==============================================================================
 * The function PLIC_DisableIRQ() disables the external interrupt for the interrupt
 * number indicated by the parameter IRQn.

 * NOTE:
 * 	This function can be used to disable the external interrupt from outside
 * 	external interrupt handler function.
 * 	This function MUST NOT be used from within the External Interrupt handler.
 * 	If you wish to disable the external interrupt while the interrupt handler
 * 	for that external interrupt is executing then you must use the return value
 * 	EXT_IRQ_DISABLE to return from the extern interrupt handler.
 */
static inline void PLIC_DisableIRQ(IRQn_Type IRQn)
{
    unsigned long hart_id = read_csr(mhartid);
    uint32_t current = PLIC->TARGET_ENABLES[hart_id].ENABLES[IRQn / 32];

    current &= ~((uint32_t)1 << (IRQn % 32));

    PLIC->TARGET_ENABLES[hart_id].ENABLES[IRQn / 32] = current;
}

/*==============================================================================
 * The function PLIC_SetPriority() sets the priority for the external interrupt 
 * for the interrupt number indicated by the parameter IRQn.
 */
static inline void PLIC_SetPriority(IRQn_Type IRQn, uint32_t priority) 
{
    PLIC->SOURCE_PRIORITY[IRQn] = priority;
}

/*==============================================================================
 * The function PLIC_GetPriority() returns the priority for the external interrupt 
 * for the interrupt number indicated by the parameter IRQn.
 */
static inline uint32_t PLIC_GetPriority(IRQn_Type IRQn)
{
    return PLIC->SOURCE_PRIORITY[IRQn];
}

/*==============================================================================
 * The function PLIC_ClaimIRQ() claims the interrupt from the PLIC controller.
 */
static inline uint32_t PLIC_ClaimIRQ(void)
{
    unsigned long hart_id = read_csr(mhartid);

    return PLIC->TARGET[hart_id].CLAIM_COMPLETE;
}

/*==============================================================================
 * The function PLIC_CompleteIRQ() indicates to the PLIC controller the interrupt
 * is processed and claim is complete.
 */
static inline void PLIC_CompleteIRQ(uint32_t source)
{
    unsigned long hart_id = read_csr(mhartid);

    PLIC->TARGET[hart_id].CLAIM_COMPLETE = source;
}

/*==============================================================================
 * The function raise_soft_interrupt() raises a synchronous software interrupt by
 * writing into the MSIP register.
 */
static inline void raise_soft_interrupt()
{
    unsigned long hart_id = read_csr(mhartid);

    /*You need to make sure that the global interrupt is enabled*/
    set_csr(mie, MIP_MSIP);       /*Enable software interrupt bit */
    PRCI->MSIP[hart_id] = 0x01;   /*raise soft interrupt for hart0*/
}

/*==============================================================================
 * The function clear_soft_interrupt() clears a synchronous software interrupt by
 * clearing the MSIP register.
 */
static inline void clear_soft_interrupt()
{
    unsigned long hart_id = read_csr(mhartid);
    PRCI->MSIP[hart_id] = 0x00;   /*clear soft interrupt for hart0*/
}

#ifdef __cplusplus
}
#endif

#endif  /* RISCV_PLIC_H */
