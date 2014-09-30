/*!
 * Altera - SoC Interrupt Manager - Secure interface
 */

/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

#ifndef __ALT_INT_H__
#define __ALT_INT_H__

#ifdef __ALT_INT_NS_H__
#error Secure and Non-Secure interrupt API cannot be used together.
#endif

#include "alt_interrupt_common.h"

#ifdef __cplusplus
extern "C"
{
#endif /* __cplusplus */

/*!
 * \addtogroup INT_LL Interrupt Controller Low-Level API [Secure]
 *
 * This module defines the Interrupt Low-Level API for accessing, configuring,
 * and controlling interrupts for SoC.
 *
 * The following reference materials was used in the design of this API:
 *  * Cortex&trade;-A9 Technical Reference Manual
 *  * Cortex&trade;-A9 MPCore&reg; Technical Reference Manual
 *  * ARM&reg; Generic Interrupt Controller Architecture, Version 1.0
 *    Architecture Specification
 *
 * @{
 */

/*!
 * \addtogroup INT_LL_DEFINE Interrupt Controller Preprocessor Defines \
 *                           [Secure]
 *
 * This group of APIs configures the compile time options for the Interrupt
 * API or provides information about the Interrupt API. It allows the
 * interrupt API to be integrated with operating systems which already
 * provides interrupt support.
 *
 * @{
 */

/*!
 * This preprocessor definition determines if the Mentor toolchain's interrupt
 * vector table symbol should be used. If a vector table is already provided
 * somewhere else, it is not necessary to have multiple vector tables.
 *
 * To use another interrupt vector, define ALT_INT_PROVISION_CPU_COUNT=(0) in
 * the Makefile. To connect to the interrupt handling system, configure the
 * ARM IRQ interrupt to call alt_int_handler_irq() in the custom solution. In
 * this case, compiler support for interrupt handler entry and exit sequences
 * will not be added.
 */
#ifndef ALT_INT_PROVISION_VECTOR_SUPPORT
#define ALT_INT_PROVISION_VECTOR_SUPPORT    (1)
#endif

/*!
 * This preprocessor definition determines if the stack space for interrupts
 * should be configured by the Interrupt API. If that space is already
 * configured somewhere else, it is not necessary to provide another stack
 * space.
 *
 * If the interrupt stack is already configured, define
 * ALT_INT_PROVISION_STACK_SUPPORT=(0) in the Makefile.
 */
#ifndef ALT_INT_PROVISION_STACK_SUPPORT
#define ALT_INT_PROVISION_STACK_SUPPORT     (1)
#endif

/*!
 * This preprocessor definition determines the size of the interrupt stack if
 * interrupt stack provisioning is requested. The same stack size will be
 * provisioned for each CPU if multiple CPUs are provisioned. While the
 * default should provide more than adequate space for most use cases, if
 * interrupt servicing routines are complicated or uses a lot of stack, the
 * stack provisioned can be adjusted to be larger. The stack size can also be
 * adjust smaller to reduce the memory used. Stack sizes should be a multiple
 * of 32.
 *
 * To specify another interrupt stack size, ALT_INT_PROVISION_STACK_SIZE
 * should be defined to a multiple of 32 in the Makefile.
 */
#ifndef ALT_INT_PROVISION_STACK_SIZE
#define ALT_INT_PROVISION_STACK_SIZE        (4096)
#endif

/*!
 * This preprocessor definition determines the total number of interrupts that
 * the Interrupt API should support. The default value is corresponds to the
 * number of interrupts defined in the hardware. Valid values are multiples of
 * 16.
 *
 * This preprocessor definition should not be redefined in the Makefile.
 */
#define ALT_INT_PROVISION_INT_COUNT         (256)

/*!
 * This preprocessor definition determines the total number of CPUs that the
 * Interrupt API should support. For the SoC FPGA, the definition should be
 * limited to values of 1 or 2 as it is a dual CPU ARM core. Provisioning more
 * CPUs than is used trivially impact performance but may impact the amount of
 * memory used more.
 *
 * To control the number of CPUs to provision for, define
 * ALT_INT_PROVISION_CPU_COUNT in the Makefile.
 */
#ifndef ALT_INT_PROVISION_CPU_COUNT
#define ALT_INT_PROVISION_CPU_COUNT         (1)
#endif

/*!
 * @}
 */

/*!
 * \addtogroup INT_LL_GLOBAL Interrupt Controller Global Interface [Secure]
 *
 * This group of APIs provide access, configuration, and control of the
 * interrupt controller global functions when in the Secure state.
 *
 * @{
 */

/*!
 * Performs the initialization steps needed by the interrupt controller
 * system. This should be the first API calls made when using the interrupt
 * controller API.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_init(void);

/*!
 * Performs the uninitialization steps needed by the interrupt controller
 * system.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_uninit(void);

/*!
 * Enables all secure interrupt forwarding from the interrupt controller to
 * the CPU interfaces.
 *
 * The interrupt controller monitors all secure interrupt signals and forwards
 * pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_enable(void);

/*!
 * Disables all secure interrupt forwarding from the interrupt controller to
 * the CPU interfaces.
 *
 * The interrupt controller ignores all secure interrupt signals and does not
 * forward pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_disable(void);

/*!
 * Enables all non-secure interrupt forwarding from the interrupt controller to
 * the CPU interfaces using the secure interface.
 *
 * The interrupt controller monitors all non-secure interrupt signals and
 * forwards pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_enable_ns(void);

/*!
 * Disables all non-secure interrupt forwarding from the interrupt controller to
 * the CPU interfaces using the secure interface.
 *
 * The interrupt controller ignores all non-secure interrupt signals and does
 * not forward pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_disable_ns(void);

/*!
 * Enables all secure and non-secure interrupt forwarding from the interrupt
 * controller to the CPU interfaces using the secure interface.
 *
 * The interrupt controller monitors all secure and non-secure interrupt
 * signals and forwards pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_enable_all(void);

/*!
 * Disables all secure and non-secure interrupt forwarding from the interrupt
 * controller to the CPU interfaces using the secure interface.
 *
 * The interrupt controller ignores all secure and non-secure interrupt
 * signals and does not forward pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_global_disable_all(void);

/*!
 * @}
 */

/*!
 * \addtogroup INT_LL_DIST Interrupt Controller Distributor Interface [Secure]
 *
 * This group of APIs provide access, configuration, and control of the
 * Generic Interrupt Controller (GIC) Distributor interface when in the
 * Secure state.
 *
 * @{
 */

/*!
 * Enable the specified interrupt for secure operation.
 *
 * This function configures the interrupt as Secure.
 *
 * All interrupts are secure by default.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_secure_enable(ALT_INT_INTERRUPT_t int_id);

/*!
 * Disable the specified interrupt from secure operation.
 *
 * This function configures the interrupt as non-secure.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_secure_disable(ALT_INT_INTERRUPT_t int_id);

/*!
 * Returns \b true if the specified interrupt is enabled for secure operation
 * and \b false otherwise.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_TRUE      Interrupt is Secure.
 * \retval      ALT_E_FALSE     Interrupt is Non-Secure.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE  alt_int_dist_is_secure(ALT_INT_INTERRUPT_t int_id);


/*!
 * Enable the specified interrupt to be forwarded to the CPU interface.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), interrupts must be enabled
 * on each CPU that will service the interrupt. This is done by calling this
 * API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_enable(ALT_INT_INTERRUPT_t int_id);

/*!
 * Disables the specified interrupt from being forwarded to the CPU interface.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), interrupts must be
 * disabled on each CPU that will no longer service the interrupt. This is
 * done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_disable(ALT_INT_INTERRUPT_t int_id);

/*!
 * Return \b true if the specified interrupt is enabled and \b false
 * otherwise.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), interrupts must be
 * queried on each CPU that may service the interrupt. This is done by
 * calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_TRUE      Interrupt is enabled.
 * \retval      ALT_E_FALSE     Interrupt is disabled.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_is_enabled(ALT_INT_INTERRUPT_t int_id);


/*!
 * Set the pending status of the specified peripheral interrupt.
 *
 * This API is not valid for Software Generated Interrupts (SGI)
 * (interrupts 0 - 15).
 *
 * For Private Peripheral Interrupt (PPI) (interrupts 16 - 32), pending is set
 * on a per CPU basis. This is done by calling this API when executing on that
 * CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All peripheral interrupts are valid,
 *              16 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_pending_set(ALT_INT_INTERRUPT_t int_id);

/*!
 * Clear the pending status of the specified peripheral interrupt.
 *
 * This API is not valid for Software Generated Interrupts (SGI)
 * (interrupts 0 - 15).
 *
 * For Private Peripheral Interrupt (PPI) (interrupts 16 - 32), pending is
 * cleared on a per CPU basis. This is done by calling this API when executing
 * on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 16 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_pending_clear(ALT_INT_INTERRUPT_t int_id);

/*!
 * Returns \b true if the specified interrupt is pending or active and
 * pending, otherwise returns \b false.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), is pending is queried on a
 * per CPU basis. This is done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_TRUE      The specified interrupt is pending or active
 *                              and pending.
 * \retval      ALT_E_FALSE     The specified interrupt is not pending and is
 *                              not active and pending.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_is_pending(ALT_INT_INTERRUPT_t int_id);

/*!
 * Returns \b true if the specified interrupt is active or active and pending,
 * otherwise returns \b false.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), is active is queried on a
 * per CPU basis. This is done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_TRUE      The specified interrupt is active or active
 *                              and pending.
 * \retval      ALT_E_FALSE     The specified interrupt is not active and is
 *                              not active and pending.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_is_active(ALT_INT_INTERRUPT_t int_id);


/*!
 * Get the priority field value of the specified interrupt.
 *
 * Higher priority corresponds to a lower priority field value.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), priority is queried on a
 * per CPU basis. This is done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \param       priority
 *              [out] Pointer to an output parameter that contains the
 *              interrupt priority.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_priority_get(ALT_INT_INTERRUPT_t int_id,
                                          uint32_t * priority);

/*!
 * Sets the priority field value of the specified interrupt.
 *
 * Higher priority corresponds to a lower priority field value.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), priority is set on a per
 * CPU basis. This is done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \param       priority
 *              The interrupt priority. Valid values are 0 - 255.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier and / or
 *                              priority value is invalid.
 */
ALT_STATUS_CODE alt_int_dist_priority_set(ALT_INT_INTERRUPT_t int_id, 
                                          uint32_t priority);


/*!
 * Get the processor target list for the specified interrupt.
 *
 * For Software Generated Interrupts (SGI) (interrupts 0 - 15) and Private
 * Peripheral Interrupt (PPI) (interrupts 16 - 32), get target will return a
 * set corresponding to the current CPU.
 *
 * \param       int_id
 *              The interrupt identifier. All interrupts are valid, 0 - 1019.
 *
 * \param       target
 *              [out] Pointer to an output parameter that contains the set of
 *              CPU(s) servicing the interrupt.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_target_get(ALT_INT_INTERRUPT_t int_id,
                                        alt_int_cpu_target_t * target);

/*!
 * Sets the the list of processors that the interrupt is sent to if it is
 * asserted. This function is only valid for Shared Peripheral Interrupts
 * (SPI).
 *
 * \param       int_id
 *              The interrupt identifier. Only SPI are valid, 32 - 1019.
 *
 * \param       target
 *              The set of CPUs which will handle the interrupt.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier and / or target
 *                              list is invalid.
 */
ALT_STATUS_CODE alt_int_dist_target_set(ALT_INT_INTERRUPT_t int_id,
                                        alt_int_cpu_target_t target);


/*!
 * Get the configured trigger type for the specified Private Peripheral
 * Interrupt (PPI) or Shared Peripheral Interrupt (SPI).
 *
 * For PPI (interrupts 16 - 32), triggering is queried on a per CPU basis.
 * This is done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. Only PPI and SPI are valid,
 *              16 - 1019.
 *
 * \param       trigger_type
 *              [out] Pointer to an output parameter that contains the trigger
 *              type of the interrupt.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier is invalid.
 */
ALT_STATUS_CODE alt_int_dist_trigger_get(ALT_INT_INTERRUPT_t int_id,
                                         ALT_INT_TRIGGER_t * trigger_type);

/*!
 * Sets the trigger type for the specified interrupt Private Peripheral
 * Interrupt (PPI) or Shared Peripheral Interrupt (SPI).
 *
 * For PPI (interrupts 16 - 32), triggering is set on a per CPU basis. This is
 * done by calling this API when executing on that CPU.
 *
 * \param       int_id
 *              The interrupt identifier. Only PPI and SPI are valid,
 *              16 - 1019.
 *
 * \param       trigger_type
 *              A parameter value which specifies the type of triggering to
 *              configure the given interrupt as.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier and / or other
 *                              configuration is invalid.
 */
ALT_STATUS_CODE alt_int_dist_trigger_set(ALT_INT_INTERRUPT_t int_id,
                                         ALT_INT_TRIGGER_t trigger_type);

/*!
 * @}
 */

/*!
 * \addtogroup INT_LL_SGI Software Generated Interrupts [Secure]
 *
 * Software Generated Interrupts (SGI)
 *
 * An SGI can specify multiple processors in its target list. The target list
 * may be further refined by a target filter that designates:
 *  * interrupting only the processor that initiates the SGI
 *  * interrupting all processors other than the one that initiates the SGI
 *  * interrupting the processor initiating the SGI
 * 
 * SGIs from different processors use the same interrupt IDs. Therefore, any
 * target processor can receive SGIs with the same interrupt ID from different
 * processors. On the CPU interface of the target processor, the pending
 * status of each of these interrupts is independent of the pending status of
 * any other interrupt, but only one interrupt with this ID can be active.
 * Reading the Interrupt Controller CPU Interrupt Acknowledge Register
 * (ICCIAR) for an SGI returns both the interrupt ID and the CPU ID of the
 * processor that generated the interrupt, uniquely identifying the interrupt.
 * In a multiprocessor implementation, the interrupt priority of each SGI 
 * interrupt ID is defined independently for each CPU interface. This means
 * that, for each CPU interface, all SGIs with a particular interrupt ID that
 * are pending on that interface have the same priority and must be handled
 * serially.
 *
 * @{
 */

/*!
 * Triggers the generation of a Software Generated Interrupts (SGI).
 *
 * \param       int_id
 *              The interrupt identifier to send. Only SGI are valid,
 *              0 - 15.
 *
 * \param       target_filter
 *              The filtering parameter.
 *
 * \param       target_list
 *              The set of CPUs which will receive the interrupt.
 *
 * \param       secure_only
 *              If \b true, then send the SGI to the target processor(s) only if
 *              the SGI is configured as Secure on that interface. If \b false,
 *              then send the SGI to the target processor(s) only if the SGI is
 *              configured as Non-Secure on that interface.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given interrupt identifier, target filter,
 *                              and / or target list is invalid.
 */
ALT_STATUS_CODE alt_int_sgi_trigger(ALT_INT_INTERRUPT_t int_id,
                                    ALT_INT_SGI_TARGET_t target_filter,
                                    alt_int_cpu_target_t target_list,
                                    bool secure_only);

/*!
 * @}
 */

/*!
 * \addtogroup INT_LL_CPU Interrupt Controller CPU Interface [Secure]
 *
 * This group of APIs provide access, configuration, and control of the
 * individual CPU interfaces.
 *
 * @{
 */

/*!
 * Performs the initialization steps needed by the interrupt controller CPU
 * interface. This should be the first CPU API call made when using the CPU
 * interface.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_init(void);

/*!
 * Performs the uninitialization steps needed by the interrupt controller CPU
 * interface.
 */
ALT_STATUS_CODE alt_int_cpu_uninit(void);

/*!
 * Enables all secure interrupt forwarding from the interrupt controller to
 * the target CPU.
 *
 * The CPU interrupt monitors all secure interrupt signals and forwards
 * pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_enable(void);

/*!
 * Disables all secure interrupt forwarding from the interrupt controller to
 * the target CPU.
 *
 * The CPU interface ignores all secure interrupt signals and does not forward
 * pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_disable(void);

/*!
 * Enables all non-secure interrupt forwarding from the interrupt controller
 * to the target CPU using the secure interface.
 *
 * The CPU interrupt monitors all non-secure interrupt signals and forwards
 * pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_enable_ns(void);

/*!
 * Disables all non-secure interrupt forwarding from the interrupt controller
 * to the target CPU using the secure interface.
 *
 * The CPU interface ignores all non-secure interrupt signals and does not
 * forward pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_disable_ns(void);

/*!
 * Enables all secure and non-secure interrupt forwarding from the interrupt
 * controller to the target CPU.
 *
 * The CPU interrupt monitors all secure and non-secure interrupt signals and
 * forwards pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_enable_all(void);

/*!
 * Disables all secure and non-secure interrupt forwarding from the interrupt
 * controller to the target CPU.
 *
 * The CPU interface ignores all secure and non-secure interrupt signals and
 * does not forward pending interrupts to the processors.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_disable_all(void);


/*!
 * Gets the configuration of the signaling interface between the GIC and the
 * CPU.
 *
 * Secure Binary Point for Preemption
 * ----------------------------------
 * The binary point is point at which the priority value fields split into two
 * parts, the group priority field and the subpriority field. The group
 * priority field is used to determine interrupt preemption.
 *
 * On systems where secure and non-secure interrupts coexist, preemption can
 * be determined by using secure binary point for secure interrupts and
 * non-secure binary point for non-secure interrupts, or by using the secure
 * binary point for both secure and non-secure interrupts.
 *
 * FIQ for Secure Interrupts
 * -------------------------
 * FIQ or Fast Interrupt reQuest is a special interrupt signal specific to ARM
 * CPUs. The CPU supports two interrupt signals for interrupts, the IRQ and
 * FIQ. The FIQ is a separate interrupt signal which has lower latency and
 * different preemption characteristics than regular interrupts.
 *
 * Secure acknowledgement for all interrupts
 * -----------------------------------------
 * When in the secure mode, modifying the non-secure states can be seen as
 * undesireable. One area which this may be problematic is the secure read of
 * the Interrupt Controller CPU Interrupt Acknowledgement Register (ICCIAR)
 * when the next pending interrupt is a non-secure. To prevent this scenario,
 * the CPU can be configured to return a special interrupt ID (1022) and leave
 * the non-secure interrupt in the pending state.
 *
 * \param       use_secure_binary_point
 *              [out] Pointer to an output parameter that contains whether the
 *              Secure Binary Point Register is used for both secure and
 *              non-secure interrupts.  If \b true then use the Secure Binary
 *              Point Register for both Secure and Non-secure interrupts. If \b
 *              false then use Secure Binary Point Register for secure
 *              interrupts and non-secure Binary Point Register for non-secure
 *              interrupts.
 *
 * \param       use_FIQ_for_secure_interrupts
 *              [out] Pointer to an output parameter that contains whether
 *              Secure interrupts use the FIQ signal or not.  If \b true then
 *              signal Secure interrupts using the FIQ signal. If \b false then
 *              signal Secure interrupts using the IRQ signal.
 *
 * \param       allow_secure_ack_all_interrupts
 *              [out] Pointer to an output parameter that contains whether
 *              Secure acknowledgement of a Non-Secure interrupt is completed or
 *              not.  If \b true then a Secure acknowledgement of the interrupt
 *              is not completed and the Interrupt ID of the Non-secure
 *              interrupt is returned. If \b false then a Secure acknowledgement
 *              of the interrupt is not completed and the Interrupt ID of 1022
 *              is returned.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_config_get(bool* use_secure_binary_point,
                                       bool* use_FIQ_for_secure_interrupts,
                                       bool* allow_secure_ack_all_interrupts);

/*!
 * Sets the configuration of the signaling interface between the GIC and the
 * CPU.
 *
 * Secure Binary Point for Preemption
 * ----------------------------------
 * The binary point is point at which the priority value fields split into two
 * parts, the group priority field and the subpriority field. The group
 * priority field is used to determine interrupt preemption.
 *
 * On systems where secure and non-secure interrupts coexist, preemption can
 * be determined by using secure binary point for secure interrupts and
 * non-secure binary point for non-secure interrupts, or by using the secure
 * binary point for both secure and non-secure interrupts.
 *
 * FIQ for Secure Interrupts
 * -------------------------
 * FIQ or Fast Interrupt reQuest is a special interrupt signal specific to ARM
 * CPUs. The CPU supports two interrupt signals for interrupts, the IRQ and
 * FIQ. The FIQ is a separate interrupt signal which has lower latency and
 * different preemption characteristics than regular interrupts.
 *
 * Secure acknowledgement for all interrupts
 * -----------------------------------------
 * When in the secure mode, modifying the non-secure states can be seen as
 * undesireable. One area which this may be problematic is the secure read of
 * the Interrupt Controller CPU Interrupt Acknowledgement Register (ICCIAR)
 * when the next pending interrupt is a non-secure. To prevent this scenario,
 * the CPU can be configured to return a special interrupt ID (1022) and leave
 * the non-secure interrupt in the pending state.
 *
 * \param       use_secure_binary_point
 *              If \b true then use the Secure Binary Point Register for both
 *              secure and non-secure interrupts. If \b false then use Secure
 *              Binary Point Register for secure interrupts and non-secure
 *              Binary Point Register for non-secure interrupts.
 *
 * \param       use_FIQ_for_secure_interrupts
 *              If \b true then signal secure interrupts using the FIQ
 *              signal. If \b false then signal secure interrupts using the IRQ
 *              signal.
 *
 * \param       allow_secure_ack_all_interrupts
 *              Controls whether a secure acknowledgement of an interrupt, when
 *              the highest priority pending interrupt is non-secure, causes the
 *              CPU interface to acknowledge the interrupt. If \b true then a
 *              secure acknowledgement of the interrupt is not completed and the
 *              Interrupt ID of the Non-secure interrupt is returned. If \b
 *              false then a secure acknowledgement of the interrupt is not
 *              completed and the Interrupt ID of 1022 is returned.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_cpu_config_set(bool use_secure_binary_point,
                                       bool use_FIQ_for_secure_interrupts,
                                       bool allow_secure_ack_all_interrupts);


/*!
 * Gets the secure interrupt priority mask for the current CPU. Only
 * interrupts with a higher priority than the priority mask can be forwarded
 * to the CPU.
 *
 * \returns     The interrupt priority mask used to determine interrupt
 *              preemption.
 */
uint32_t alt_int_cpu_priority_mask_get(void);

/*!
 * Sets the secure interrupt priority mask for the current CPU. Only
 * interrupts with a higher priority than the priority mask can be forwarded
 * to the CPU.
 *
 * \param       priority_mask
 *              The interrupt priority mask is the group priority needed to
 *              instruct the GIC to preempt lower priority interrupt. The
 *              valid range for this value is 0 - 255.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given priority mask is invalid.
 */
ALT_STATUS_CODE alt_int_cpu_priority_mask_set(uint32_t priority_mask);

/*!
 * Gets the binary point value for the current CPU.
 *
 * The binary point is point at which the priority value fields split into two
 * parts, the group priority field and the subpriority field. The group
 * priority field is used to determine interrupt preemption.
 *
 * \returns     The configured binary point value.
 */
uint32_t alt_int_cpu_binary_point_get(void);

/*!
 * Sets the binary point value for the current CPU.
 *
 * The binary point is point at which the priority value fields split into two
 * parts, the group priority field and the subpriority field. The group
 * priority field is used to determine interrupt preemption.
 *
 * \param       binary_point
 *              The binary point to use. The valid range for the value is
 *              0 - 7.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given binary point value is invalid.
 */
ALT_STATUS_CODE alt_int_cpu_binary_point_set(uint32_t binary_point);

/*!
 * Gets the non-secure binary point value for the current CPU using the secure
 * interface.
 *
 * The binary point is point at which the priority value fields split into two
 * parts, the group priority field and the subpriority field. The group
 * priority field is used to determine interrupt preemption.
 *
 * \returns     The configured binary point value.
 */
uint32_t alt_int_cpu_binary_point_get_ns(void);

/*!
 * Sets the non-secure binary point value for the current CPU using the secure
 * interface. 
 *
 * The binary point is point at which the priority value fields split into two
 * parts, the group priority field and the subpriority field. The group
 * priority field is used to determine interrupt preemption.
 *
 * \param       binary_point
 *              The binary point to use. The valid range for the value is
 *              0 - 7.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given binary point value is invalid.
 */
ALT_STATUS_CODE alt_int_cpu_binary_point_set_ns(uint32_t binary_point);

/*!
 * @}
 */

/*!
 * \addtogroup INT_LL_ISR Interrupt Service Routine [Secure]
 *
 * This group of APIs performs Interrupt Service Routine (ISR) related
 * functions.
 *
 * @{
 */

/*!
 * Registers a callback for the specified secure interrupt for the CPU
 * interface.
 *
 * This API only registers a callback for secure interrupts. If a callback is
 * registered for a non-secure interrupt, the behaviour is undefined.
 *
 * \param       int_id
 *              The interrupt identifier to register the handler for. All
 *              defined interrupts are valid, 0 - 1019.
 *
 * \param       callback
 *              The callback to use when the given interrupt is issued.
 *
 * \param       context
 *              The callback context to use for the above callback. When the
 *              callback is issued, this parameter will be provided to the
 *              callback.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_isr_register(ALT_INT_INTERRUPT_t int_id,
                                     alt_int_callback_t callback,
                                     void * context);

/*!
 * Unregisters the callback for the specified secure interrupt for the CPU
 * interface.
 *
 * This API only unregisters a callback for secure interrupts. If a callback
 * is unregistered for a non-secure interrupt, the behaviour is undefined.
 *
 * \param       int_id
 *              The interrupt identifier to register the handler for. All
 *              defined interrupts are valid, 0 - 1019.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_int_isr_unregister(ALT_INT_INTERRUPT_t int_id);

/*!
 * @}
 */

/*!
 * \addtogroup INT_LL_UTIL Interrupt Utility Functions [Secure]
 *
 * This group of APIs provide utilities to query the system properties.
 *
 * @{
 */

/*!
 * Gets the number of CPUs in the system.
 *
 * \returns     The CPU count of the system.
 */
uint32_t alt_int_util_cpu_count(void);

/*!
 * Gets the number of supported interrupts in the system.
 *
 * \returns     The supported interrupt count of the system.
 */
uint32_t alt_int_util_int_count(void);

/*!
 * Gets the CPU indentifier of the current CPU interface.
 *
 * \returns     The set of CPUs representing the current CPU interface.
 */
alt_int_cpu_target_t alt_int_util_cpu_current(void);

/*!
 * @}
 */

/*!
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __ALT_INT_H__ */
