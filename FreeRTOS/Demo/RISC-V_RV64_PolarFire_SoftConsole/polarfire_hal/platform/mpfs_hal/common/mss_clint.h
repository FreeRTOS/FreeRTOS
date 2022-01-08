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
 * @file mss_clint.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief CLINT access data structures and functions.
 *
 */
#ifndef MSS_CLINT_H
#define MSS_CLINT_H

#include <stdint.h>
#include "encoding.h"
#include "atomic.h"

#ifdef __cplusplus
extern "C" {
#endif

#define RTC_PRESCALER 100U
#define SUCCESS 0U
#define ERROR   1U


/*==============================================================================
 * CLINT: Core Local Interrupter
 */
typedef struct CLINT_Type_t
{
    volatile uint32_t MSIP[5];
    volatile uint32_t reserved1[(0x4000U - 0x14U)/4U];
    volatile uint64_t MTIMECMP[5];  /* mtime compare value for each hart. When mtime equals this value, interrupt is generated for particular hart */
    volatile uint32_t reserved2[((0xbff8U - 0x4028U)/4U)];
    volatile uint64_t MTIME;    /* contains the current mtime value */
} CLINT_Type;

#define CLINT    ((CLINT_Type *)CLINT_BASE)


/*==============================================================================
 * The function raise_soft_interrupt() raises a synchronous software interrupt by
 * writing into the MSIP register.
 */
static inline void raise_soft_interrupt(unsigned long hart_id)
{
    /*You need to make sure that the global interrupt is enabled*/
    /*Note:  set_csr(mie, MIP_MSIP) needs to be set on hart you are setting sw interrupt */
    CLINT->MSIP[hart_id] = 0x01U;   /*raise soft interrupt for hart(x) where x== hart ID*/
    mb();
}

/*==============================================================================
 * The function clear_soft_interrupt() clears a synchronous software interrupt by
 * clearing the MSIP register.
 */
static inline void clear_soft_interrupt(void)
{
    volatile uint32_t reg;
    uint64_t hart_id = read_csr(mhartid);
    CLINT->MSIP[hart_id] = 0x00U;   /*clear soft interrupt for hart0*/
    reg = CLINT->MSIP[hart_id];     /* we read back to make sure it has been written before moving on */
                                    /* todo: verify line above guaranteed and best way to achieve result */
    (void)reg;                      /* use reg to avoid compiler warning */
}

/*
 * return mtime
 */
uint64_t readmtime(void);

/**
 * call once at startup
 * @return
 */
void reset_mtime(void);

/**
 * Configure system tick
 * @return SUCCESS or FAIL
 */
uint32_t SysTick_Config(void);

/**
 * Disable system tick interrupt
 */
void disable_systick(void);

/*------------------------------------------------------------------------------
 * RISC-V interrupt handler for machine timer interrupts.
 */
void handle_m_timer_interrupt(void);

/**
 *
 */
void handle_m_soft_interrupt(void);

#ifdef __cplusplus
}
#endif

#endif  /*  MSS_CLINT_H */
