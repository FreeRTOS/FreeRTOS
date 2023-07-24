// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#ifndef RTOS_IRQ_H_
#define RTOS_IRQ_H_

#include <xcore/chanend.h>

/**
 * IRQ ISR callback function pointer type.
 *
 * ISRs registered with the RTOS IRQ system must be
 * compatible with this type.
 */
typedef void (*rtos_irq_isr_t)( void *param );

/**
 * This macro must precede the definition of ISRs that
 * get registered with the RTOS IRQ system.
 *
 * It adds the function to the rtos_irq_isr function pointer
 * group which allows the compiler to correctly calculate
 * the stack size for ISRs.
 */
#define RTOS_IRQ_ISR_ATTR __attribute__((fptrgroup("rtos_irq_isr")))

/**
 * This function sends an IRQ to an RTOS core. It may be called both by
 * RTOS cores and non-RTOS cores. It must be called by a core on the
 * same tile as the core being interrupted.
 *
 * \param core_id        The core ID of the RTOS core to interrupt. The core must have
 *                       previously called rtos_irq_enable.
 * \param source_id      The ID of source of the IRQ. When called by an RTOS core,
 *                       this must be the core ID of the calling core.
 *                       When called by a non-RTOS core then this must be an ID returned
 *                       by rtos_irq_source_register().
 */
void rtos_irq(int core_id, int source_id);


/**
 * This function sends an IRQ to a peripheral on a non-RTOS core.
 * It must be called by an RTOS core. The non-RTOS core does not
 * need to be on the same tile as the RTOS core.
 *
 * \param dest_chanend  The channel end used by the peripheral to receive
 *                      the interrupt.
 */
void rtos_irq_peripheral(chanend_t dest_chanend);

/**
 * This function registers a non-RTOS IRQ source. The source ID
 * returned must be passed to the non-RTOS peripheral that will be
 * generating the IRQs. The peripheral can then subsequently send
 * IRQs with rtos_irq().
 *
 * \param isr            The interrupt service routine to run when the IRQ is received.
 * \param param          A pointer to user data to pass to the ISR.
 * \param source_chanend The channel end to use to send the IRQ.
 *
 * \returns the IRQ source ID that may be passed to rtos_irq() when the
 * peripheral needs to send an IRQ.
 */

int rtos_irq_register(rtos_irq_isr_t isr, void *data, chanend_t source_chanend);

/**
 * This function enables the calling core to receive RTOS IRQs. It
 * should be called once during initialization by each RTOS core
 * after calling rtos_core_register().
 *
 * \param The total number of cores used by the RTOS.
 */
void rtos_irq_enable(int total_rtos_cores);

/**
 * This function checks to see if the IRQ system is ready.
 *
 * \returns true if all of the cores have enabled IRQs. Otherwise false.
 */
int rtos_irq_ready(void);

#endif /* RTOS_IRQ_H_ */
