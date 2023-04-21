// Copyright 2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#include "rtos_support.h"

/*
 * Ensure that these normally inline functions exist
 * when compiler optimizations are disabled.
 */
extern inline uint32_t rtos_interrupt_mask_get(void);
extern inline uint32_t rtos_interrupt_mask_all(void);
extern inline void rtos_interrupt_unmask_all(void);
extern inline void rtos_interrupt_mask_set(uint32_t mask);
extern inline uint32_t rtos_isr_running(void);
