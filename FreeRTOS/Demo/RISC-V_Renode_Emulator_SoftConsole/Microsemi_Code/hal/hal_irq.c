/***************************************************************************//**
 * (c) Copyright 2007-2018 Microsemi SoC Products Group. All rights reserved.
 * 
 * Legacy interrupt control functions for the Microsemi driver library hardware
 * abstraction layer.
 *
 * SVN $Revision: 9661 $
 * SVN $Date: 2018-01-15 16:13:33 +0530 (Mon, 15 Jan 2018) $
 */
#include "hal.h"
#include "riscv_hal.h"

/*------------------------------------------------------------------------------
 * 
 */
void HAL_enable_interrupts(void) {
    __enable_irq();
}

/*------------------------------------------------------------------------------
 * 
 */
psr_t HAL_disable_interrupts(void) {
    psr_t psr;
    psr = read_csr(mstatus);
    __disable_irq();
    return(psr);
}

/*------------------------------------------------------------------------------
 * 
 */
void HAL_restore_interrupts(psr_t saved_psr) {
    write_csr(mstatus, saved_psr);
}

