/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
* \file
*
* Implementation of Analog Comparator Controller (ACC).
*
*/

#ifndef _ACC_H
#define _ACC_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initialize the Analog Comparator Controller.
 * \param p_acc  Pointer to an Acc instance.
 * \param select_plus  Input connected to inp, 0~7.
 * \param select_minus  Input connected to inm, 0~7.
 * \param edge_type  CF flag triggering mode
 * Use pattern defined in the device header file.
 * \param invert  Invert comparator output.
 */
extern void acc_init(Acc *p_acc, uint32_t select_plus, uint32_t select_minus,
                     uint32_t edge_type, uint32_t invert);

/**
 * \brief Enable the ACC.
 * \param p_acc  Pointer to ACC registers set instance.
 */
extern void acc_enable(Acc *p_acc);

/**
 * \brief Disable the ACC.
 * \param p_acc  Pointer to ACC registers set instance.
 */
extern void acc_disable(Acc *p_acc);

/**
 * \brief Reset the ACC.
 * \param p_acc  Pointer to ACC registers set instance.
 */
extern void acc_reset(Acc *p_acc);

/**
 * \brief Set the input source.
 * \param p_acc  Pointer to ACC registers set instance.
 * \param select_minus  Selection for minus comparator input.
 * \param select_plus  Selection for plus comparator input.
 */
extern void acc_set_input(Acc *p_acc, uint32_t select_minus,
                          uint32_t select_plus);

/**
 * \brief Set the output of the ACC.
 * \param p_acc  Pointer to ACC registers set instance.
 * \param invert  Invert comparator output, 0 for disable, 1 for enable.
 * \param fault_enable  Fault enable, 0 for disable, 1 for enable.
 * \param fault_source  Selection of fault source, 0 for CF, 1 for output.
 */
extern void acc_set_output(Acc *p_acc, uint32_t invert, uint32_t fault_enable,
                           uint32_t fault_source);

/**
 * \brief Get the comparison result.
 * \param p_acc  Pointer to ACC registers set instance.
 * \return Result of the comparison, 0 for inn > inp, 1 for inp > inn.
 */
extern uint32_t acc_get_comparison_result(Acc *p_acc);

/**
 * \brief Enable the interrupt.
 * \param p_acc  Pointer to ACC registers set instance.
 */
extern void acc_enable_interrupt(Acc *p_acc);

/**
 * \brief Disable the interrupt.
 * \param p_acc  Pointer to ACC registers set instance.
 */
extern void acc_disable_interrupt(Acc *p_acc);

/**
 * \brief Get the interrupt status.
 * \param p_acc  Pointer to ACC registers set instance.
 * \return Contents of the Interrupt Status Register.
 */
extern uint32_t acc_get_interrupt_status(Acc *p_acc);

/**
 * \brief Write-protect the Mode Register and the Analog Control Register.
 * \param p_acc  Pointer to ACC registers set instance.
 * \param enable  1 to enable, 0 to disable.
 */
extern void acc_set_write_protect(Acc *p_acc, uint32_t enable);

/**
 * \brief Return write protect status.
 * \param p_acc  Pointer to ACC registers set instance.
 * \retval 0 No write protection violation occurred.
 * \retval 1 At least one write attempt to a write-protected register has been
 * detected, since the previous call to this function.
 */
extern uint32_t acc_get_write_protect_status(Acc *p_acc);

#endif /* _ACC_H */
