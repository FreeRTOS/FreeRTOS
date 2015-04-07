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

#ifndef __ALT_CACHE_H__
#define __ALT_CACHE_H__

#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif

/*!
 * \addtogroup CACHE_MGR Cache Management API
 *
 * This module defines the cache management API for enabling and disabling L1
 * data cache, L1 instruction cache, L1 dynamic branch prediction caches, L1
 * TLB cache, and L2 cache in the SoC. As well, many it allows users to perform
 * cache maintenance operations on these caches. This includes the following
 * operations:
 *  * Invalidate: Marks the cache line as being invalid, freeing up the space
 *    to cache other data. All APIs which enable caches invalidates the memory
 *    before being enabling the cache.
 *  * Clean: If the cache line is dirty, it synchronizes the cache line data
 *    with the upper level memory system and marks that line as clean. All APIs
 *    which disable caches cleans the memory before disabling the cache.
 *  * Purge: A term used in this API as a short form for clean and invalidate.
 *    This operation cleans and invalidates a cache line in that order, as a
 *    single command to the cache controller.
 *
 * The following reference materials were used in the design of this API:
 *  * ARM&reg; Architecture Reference Manual, ARMv7-A and ARMv7-R edition
 *  * Cortex&trade;-A9 Technical Reference Manual
 *  * Cortex&trade;-A9 MPCore Technical Reference Manual
 *  * CoreLink&trade; Level 2 Cache Controller L2C-310 Technical Reference
 *    Manual
 *
 * @{
 */

/*!
 * \addtogroup CACHE_SYS System Level Cache Management API
 *
 * This API group provides cache maintenance operations which affects multiple
 * cache levels.
 *
 * The enable and disable functions enables and disables all caches in the
 * system respectively. For caches shared by the CPU core(s), particularly the
 * L2 cache, once that cache is enabled or disabled it will not be invalidated
 * or cleaned again respectively. This allows the safe system-wide enable and
 * disable to be used in single-core and multi-core scenarios.
 *
 * For cache maintenance operations, this API implements the procedures
 * outlined in the L2C-310 Technical Reference Manual, section 3.3.10,
 * subsection "System cache maintenance considerations". This allows for a
 * convenient way to invalidate, clean, or clean and invalidate cache data from
 * the L1 to L2 to L3 while avoiding any potential race conditions in
 * mutli-core or multi-master scenarios. It assumes that the L1 and L2 cache is
 * set in "non-exclusive" mode. This means a segment of data can reside in both
 * the L1 and L2 simultaneously. This is the default mode for caches in the
 * system.
 *
 * The current implementation of the system cache APIs assumes that the MMU is
 * configured with a flat memory mapping or that every virtual address matches
 * perfectly with the physical address. This restriction may be lifted in a
 * future release of the cache API implementation.
 *
 * @{
 */

/*!
 * Enables support for a non-flat virtual memory. A flat virtual memory is
 * where every virtual address matches exactly to the physical address, making
 * the virtual to physical translation trivial. Adding support for non-flat
 * adds some overhead for the VA to PA translation and error detection.
 *
 * To enable non-flat virtual memory support, defined
 * ALT_CACHE_SUPPORT_NON_FLAT_VIRTUAL_MEMORY=1 in your Makefile when compiling
 * HWLibs.
 */
#ifndef ALT_CACHE_SUPPORT_NON_FLAT_VIRTUAL_MEMORY
#define ALT_CACHE_SUPPORT_NON_FLAT_VIRTUAL_MEMORY (0)
#endif

/*!
 * This is the system wide cache line size, given in bytes.
 */
#define ALT_CACHE_LINE_SIZE         32

/*!
 * Enables all caches and features which improve reliability and speed on all
 * cache controllers visible to the current CPU core. This includes parity
 * error detection. Cache controllers visible to multiple CPU cores, for
 * example the L2, will first be checked to be disabled before being enabled.
 * All necessary cache maintenance operations will be done automatically.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_system_enable(void);

/*!
 * Disables all cache controllers visible to the current CPU core. Cache
 * controllers visible to multiple CPU cores, for example the L2, will first
 * be checked to be enabled before being disabled. All necessary cache
 * maintenance operations will be done automatically.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_system_disable(void);

/*!
 * Invalidates the specified contents of all cache levels visible to the
 * current CPU core for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * The following pseudocode outlines the operations carried out by this
 * function:
 *  -# L2 invalidate address(es)
 *  -# L2 cache sync
 *  -# L1 invalidate address(es)
 *  -# DSB instruction
 *
 * The current implementation of the system cache APIs assumes that the MMU is
 * configured with a flat memory mapping or that every virtual address matches
 * perfectly with the physical address. This restriction may be lifted in a
 * future release of the cache API implementation.
 *
 * \param       vaddress
 *              The virtual address of the memory segment to be invalidated.
 *
 * \param       length
 *              The length of the memory segment to be invalidated.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_system_invalidate(void * vaddress, size_t length);

/*!
 * Cleans the specified contents of all cache levels visible to the current
 * CPU core for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * The following pseudocode outlines the operations carried out by this
 * function:
 *  -# L1 clean address(es)
 *  -# DSB instruction
 *  -# L2 clean address(es)
 *  -# L2 cache sync
 *
 * The current implementation of the system cache APIs assumes that the MMU is
 * configured with a flat memory mapping or that every virtual address matches
 * perfectly with the physical address. This restriction may be lifted in a
 * future release of the cache API implementation.
 *
 * \param       vaddress
 *              The virtual address of the memory segment to be cleaned.
 *
 * \param       length
 *              The length of the memory segment to be cleaned.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_system_clean(void * vaddress, size_t length);

/*!
 * Cleans and invalidates the specified contents of all cache levels visible
 * to the current CPU core for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * The following pseudocode outlines the operations carried out by this
 * function:
 *  -# L1 clean address(es)
 *  -# DSB instruction
 *  -# L2 clean and invalidate address(es)
 *  -# L2 cache sync
 *  -# L1 invalidate address(es)
 *  -# DSB instruction
 *
 * The current implementation of the system cache APIs assumes that the MMU is
 * configured with a flat memory mapping or that every virtual address matches
 * perfectly with the physical address. This restriction may be lifted in a
 * future release of the cache API implementation.
 *
 * \param       vaddress
 *              The virtual address of the memory segment to be purged.
 *
 * \param       length
 *              The length of the memory segment to be purged.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_system_purge(void * vaddress, size_t length);

/*!
 * @}
 */

/*!
 * \addtogroup CACHE_L1 L1 Cache Management API
 *
 * This API group provides functions to interact with various components of the
 * L1 cache on the SoCFPGA. This includes the following cache components:
 *  * Instruction Cache
 *  * Data Cache
 *  * Parity error detection
 *  * Dynamic branch prediction
 *  * Data prefetching
 *
 * The API within this group only affects the L1 cache on the current CPU. To
 * interact the L1 cache on another CPU, the API must be called from that other
 * CPU.
 *
 * With respect to bring-up, the L1 and L2 cache controller setups are fully
 * independent. The L2 can be setup at any time, before or after the L1 is setup.
 * \internal
 * Source: Cortex-A9 MPCore TRM, section 5.3.4 "Multiprocessor bring-up".
 * \endinternal
 *
 * @{
 */

/*!
 * Enables all L1 caches and features on the current CPU core. This includes
 * the instruction cache, data cache, parity error detection, branch target
 * address cache, global history buffer, and data prefetching. All necessary
 * maintenance tasks will be taken care of.
 *
 * This function should not be mixed with other L1 cache related functions
 * which enable or disable caches individually.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_enable_all(void);

/*!
 * Disables all L1 caches and features on the current CPU core. This includes
 * the instruction cache, data cache, parity error detection, branch target
 * address cache, global history buffer, and data prefetching. All necessary
 * maintenance tasks will be taken care of.
 *
 * This function should not be mixed with other L1 cache related functions
 * which enable or disable caches individually.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_disable_all(void);

/*!
 * Enables the L1 instruction cache on the current CPU core. If the cache is
 * already enabled, nothing is done. Otherwise the instruction cache is first
 * invalidated before being enabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_instruction_enable(void);

/*!
 * Disables the L1 instruction cache on the current CPU core.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_instruction_disable(void);

/*!
 * Returns \b true when the L1 instruction cache is enabled and \b false when
 * it is disabled on the current CPU core.
 *
 * \retval      true            The L1 instruction cache is enabled.
 * \retval      false           The L1 instruction cache is disabled.
 */
bool alt_cache_l1_instruction_is_enabled(void);

/*!
 * Invalidates the contents of the L1 instruction cache on the current CPU
 * core.
 *
 * Normally this is done automatically as part of
 * alt_cache_l1_instruction_enable(), but in certain circumstances it may be
 * necessary to invalidate it manually. An example of this situation is when
 * the address space is remapped and the processor executes instructions from
 * the new memory area.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_instruction_invalidate(void);

/*!
 * Enables the L1 data cache on the current CPU core.
 *
 * If the cache is already enabled nothing is done. Otherwise the data cache is
 * first invalidated before being enabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_data_enable(void);

/*!
 * Disables the L1 data cache on the current CPU core.
 *
 * If the cache is already disabled nothing is done. Otherwise the data cache
 * is first cleaned before being disabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_data_disable(void);

/*!
 * Returns \b true when the L1 data cache is enabled and \b false when it is
 * disabled on the current CPU core.
 *
 * \retval      true            The L1 data cache is enabled.
 * \retval      false           The L1 data cache is disabled.
 */
bool alt_cache_l1_data_is_enabled(void);

/*!
 * Invalidates the specified contents of the L1 data cache on the current CPU
 * core for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * \param       vaddress
 *              The virtual address of the memory segment to be invalidated.
 *
 * \param       length
 *              The length of the memory segment to be invalidated.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 */
ALT_STATUS_CODE alt_cache_l1_data_invalidate(void * vaddress, size_t length);

/*!
 * Invalidates the entire contents of the L1 data cache on the current CPU
 * core.
 *
 * Normally this is done automatically as part of alt_cache_l1_data_enable(),
 * but in certain circumstances it may be necessary to invalidate it manually.
 * An example of this situation is when the address space is remapped and the
 * processor accesses memory from the new memory area.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_data_invalidate_all(void);

/*!
 * Cleans the specified contents of the L1 data cache on the current CPU core
 * for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * \param       vaddress
 *              The virtual address of the memory segment to be cleaned.
 *
 * \param       length
 *              The length of the memory segment to be cleaned.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 */
ALT_STATUS_CODE alt_cache_l1_data_clean(void * vaddress, size_t length);

/*!
 * Cleans the entire L1 data cache for the current CPU core.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_data_clean_all(void);

/*!
 * Cleans and invalidates the specified contents of the L1 data cache on the
 * current CPU core for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * Normally this is done automatically as part of alt_cache_l1_data_disable(),
 * but in certain circumstances it may be necessary to purged it manually.
 * An example of this situation is when the address space is remapped and the
 * processor accesses memory from the new memory area.
 *
 * \param       vaddress
 *              The virtual address of the memory segment to be purged.
 *
 * \param       length
 *              The length of the memory segment to be purged.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 */
ALT_STATUS_CODE alt_cache_l1_data_purge(void * vaddress, size_t length);

/*!
 * Cleans and invalidates the entire L1 data cache for the current CPU core.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_data_purge_all(void);

/*!
 * Enables the parity error detection feature in the L1 caches on the current
 * CPU core.
 *
 * Ideally parity should be enabled before any L1 caches are enabled. If the
 * instruction, data, and / or dynamic branch predictor caches are already
 * enabled, they will first be cleaned (if needed) and disabled before parity
 * is enabled in hardware. Afterwards, the affected caches will be invalidated
 * and enabled.
 *
 * Parity and TLB interaction deserves special attention. The TLB is considered
 * to be a L1 cache but is enabled when the MMU, which is grouped in another
 * API, is enabled. Due to the system-wide influence of the MMU, it cannot be
 * disabled and enabled with impunity as the other L1 caches, which are
 * designed to operate as transparently as possible. Thus parity error
 * detection must be enabled before the L1 TLB cache, and by extension the MMU,
 * is enabled.
 *
 * For a parity error to be reported, the appropriate CPU PARITYFAIL interrupt
 * for the current CPU core must be enabled using the interrupt controller API.
 * For CPU0, ALT_INT_INTERRUPT_CPU0_PARITYFAIL is asserted if any parity error
 * is detected while the other PARITYFAIL interrupts are for parity errors in a
 * specific memory. Refer to the interrupt controller API for more details
 * about programming the interrupt controller.
 *
 * In the event of a parity error is detected, the appropriate CPU parity
 * interrupt will be raised. CPU parity interrupts are all edge triggered and
 * are cleared by acknowledging them in the interrupt controller API.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_parity_enable(void);

/*!
 * Disables parity error detection in the L1 caches.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_parity_disable(void);

/*!
 * Returns \b true when parity error detection is enabled and \b false when it
 * is disabled on the current CPU core.
 *
 * \retval      true            Parity error detection for L1 caches is
 *                              enabled.
 * \retval      false           Parity error detection for L1 caches is
 *                              disabled.
 */
bool alt_cache_l1_parity_is_enabled(void);

/*!
 * Enables the dynamic branch predictor features on the current CPU core.
 *
 * This operation enables both the Branch Target Address Cache (BTAC) and
 * the Global History Buffer (GHB). Affected caches are automatically
 * invalidated before use.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_branch_enable(void);

/*!
 * Disables the dynamic branch predictor features on the current CPU core.
 *
 * This operation disables both the Branch Target Address Cache (BTAC) and
 * the Global History Buffer (GHB).
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_branch_disable(void);

/*!
 * Returns \b true when both the dynamic predictor features are enabled and
 * \b false when they are disabled on the current CPU core.
 *
 * \retval      true            The L1 branch predictor caches are all enabled.
 * \retval      false           Some or all L1 branch predictor caches are
 *                              disabled.
 */
bool alt_cache_l1_branch_is_enabled(void);

/*!
 * Invalidates the dynamic branch predictor feature caches on the current CPU
 * core.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_branch_invalidate(void);

/*!
 * Enables the L1 cache data prefetch feature on the current CPU core.
 *
 * This allows data to be prefetched into the data cache before it is to be
 * used. For example in a loop the current iteration may want to preload the
 * data which will be used in the next teration. This is done by using the PLD
 * instructions.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_prefetch_enable(void);

/*!
 * Disables the L1 cache data prefetch feature on the current CPU core.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l1_prefetch_disable(void);

/*!
 * Returns \b true if the L1 cache data prefetch feature is enabled and
 * \b false if it is disabled on the current CPU core.
 *
 * \retval      true            The L1 data cache prefetch feature is enabled.
 * \retval      false           The L1 data cache prefetch feature is disabled.
 */
bool alt_cache_l1_prefetch_is_enabled(void);

/*!
 * @}
 */

/*!
 * \addtogroup CACHE_L2 L2 Cache Management API
 *
 * This API group provides functions to interact with various features of the
 * L2 cache on the SoCFPGA. This includes the following features:
 *  * L2 cache
 *  * Parity error detection
 *  * Data prefetching
 *  * Interrupt Management
 *
 * \internal
 * Additional features that may be implemented in the future:
 *  * Lockdown
 *  * Event counter
 * \endinternal
 *
 * The API within this group affects the L2 cache which is visible to all CPUs
 * on the system.
 *
 * With respect to bring-up, the L1 and L2 cache controller setups are fully
 * independent. The L2 can be setup at any time, before or after the L1 is setup.
 * \internal
 * Source: Cortex-A9 MPCore TRM, section 5.3.4 "Multiprocessor bring-up".
 * \endinternal
 *
 * @{
 */

/*!
 * Initializes the L2 cache controller.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_cache_l2_init(void);

/*!
 * Uninitializes the L2 cache controller.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_cache_l2_uninit(void);

/*!
 * Enables the L2 cache features for data and instruction prefetching.
 *
 * Prefetching can be enabled or disabled while the L2 cache is enabled.
 * \internal
 * Source: Use the Prefetch Control Register.
 * \endinternal
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_prefetch_enable(void);

/*!
 * Disables the L2 cache features for data and instruction prefetching.
 *
 * Prefetching can be enabled or disabled while the L2 cache is enabled.
 * \internal
 * Source: Use the Prefetch Control Register.
 * \endinternal
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_prefetch_disable(void);

/*!
 * Returns \b true if either L2 cache data or instruction prefetch features are
 * enabled and \b false if no prefetching features are enabled.
 *
 * \retval      true            The L2 data and instruction prefetch features
 *                              are enabled.
 * \retval      false           Some L2 data and instruction prefetch features
 *                              are disabled.
 */
bool alt_cache_l2_prefetch_is_enabled(void);

/*!
 * Enables parity error detection in the L2 cache.
 *
 * Ideally parity should be enabled before the L2 cache is enabled. If the
 * cache is already enabled, it will first be cleaned and disabled before
 * parity is enabled in hardware. Afterwards, the cache will be invalidated and
 * enabled.
 *
 * For a parity error to be reported, the ALT_CACHE_L2_INTERRUPT_PARRD and / or
 * ALT_CACHE_L2_INTERRUPT_PARRT interrupt condition(s) must be enabled. This is
 * done by calling alt_cache_l2_int_enable(). As well, the L2 cache interrupt
 * must be enabled using the interrupt controller API. Refer to the interrupt
 * controller API for more details about programming the interrupt controller.
 *
 * In the event of a parity error is detected, the appropriate L2 cache parity
 * interrupt will be raised. To clear the parity interrupt(s), the appropriate
 * L2 cache parity interrupt must be cleared by calling
 * alt_cache_l2_int_status_clear().
 *
 * For ECC support, refer to the ECC related API documentation for more
 * information.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_parity_enable(void);

/*!
 * Disables parity error detection in the L2 cache.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_parity_disable(void);

/*!
 * Returns \b true when parity error detection is enabled and \b false when it
 * is disabled.
 *
 * \retval      true            The L2 cache parity error detection feature is
 *                              enabled.
 * \retval      false           The L2 cache parity error detection feature is
 *                              disabled.
 */
bool alt_cache_l2_parity_is_enabled(void);

/*!
 * Enables the L2 cache.
 *
 * If the L2 cache is already enabled, nothing is done. Otherwise the entire
 * contents of the cache is first invalidated before being enabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_enable(void);

/*!
 * Disables the L2 cache.
 *
 * If the L2 cache is already disabled, nothing is done. Otherwise the entire
 * contents of the cache is first cleaned before being disabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_disable(void);

/*!
 * Returns \b true when the L2 cache is enabled and \b false when it is
 * disabled.
 *
 * \retval      true            The L2 cache is enabled.
 * \retval      false           The L2 cache is disabled.
 */
bool alt_cache_l2_is_enabled(void);

/*!
 * Flushes the L2 cache controller hardware buffers.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_l2_sync(void);

/*!
 * Invalidates the specified contents of the L2 cache for the given memory
 * segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * \param       paddress
 *              The physical address of the memory segment to be invalidated.
 *
 * \param       length
 *              The length of the memory segment to be invalidated.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_l2_invalidate(void * paddress, size_t length);

/*!
 * Invalidates th entire contents of the L2 cache.
 *
 * Normally this is done automatically as part of alt_cache_l2_enable(), but
 * in certain circumstances it may be necessary to invalidate it manually. An
 * example of this situation is when the address space is remapped and the
 * processor accesses memory from the new memory area.

 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_l2_invalidate_all(void);

/*!
 * Cleans the specified contents of the L2 cache for the given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * \param       paddress
 *              The physical address of the memory segment to be cleaned.
 *
 * \param       length
 *              The length of the memory segment to be cleaned.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_l2_clean(void * paddress, size_t length);

/*!
 * Cleans the entire L2 cache. All L2 cache controller interrupts will be
 * temporarily disabled while the clean operation is in progress and restored
 * once the it is finished.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_l2_clean_all(void);

/*!
 * Cleans and invalidates the specified contents of the L2 cache for the
 * given memory segment.
 *
 * The memory segment address and length specified must align to the
 * characteristics of the cache line. This means the address and length must be
 * multiples of the cache line size. To determine the cache line size, use the
 * \b ALT_CACHE_LINE_SIZE macro.
 *
 * \param       paddress
 *              The physical address of the memory segment to be purged.
 *
 * \param       length
 *              The length of the memory segment to be purged.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The memory segment is invalid.
 */
ALT_STATUS_CODE alt_cache_l2_purge(void * paddress, size_t length);

/*!
 * Cleans and invalidates the entire L2 cache. All L2 cache controller
 * interrupts will be temporarily disabled while the clean and invalidate
 * operation is in progress and restored once the it is finished.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_TMO       The memory operation timed out.
 */
ALT_STATUS_CODE alt_cache_l2_purge_all(void);

/*!
 * This type definition enumerates all the interrupt conditions that can be
 * generated by the L2 cache controller as register mask values.
 */
enum ALT_CACHE_L2_INTERRUPT_e
{
    /*! Decode error received on the master ports from L3. */
    ALT_CACHE_L2_INTERRUPT_DECERR = 1 << 8,

    /*! Slave error received on the master ports from L3.  */
    ALT_CACHE_L2_INTERRUPT_SLVERR = 1 << 7,

    /*! Error on the L2 data RAM read.                     */
    ALT_CACHE_L2_INTERRUPT_ERRRD  = 1 << 6,

    /*! Error on the L2 tag RAM read.                      */
    ALT_CACHE_L2_INTERRUPT_ERRRT  = 1 << 5,

    /*! Error on the L2 data RAM write.                    */
    ALT_CACHE_L2_INTERRUPT_ERRWD  = 1 << 4,

    /*! Error on the L2 tag RAM write.                     */
    ALT_CACHE_L2_INTERRUPT_ERRWT  = 1 << 3,

    /*! Parity error on the L2 data RAM read.              */
    ALT_CACHE_L2_INTERRUPT_PARRD  = 1 << 2,

    /*! Parity error on the L2 tag RAM read.               */
    ALT_CACHE_L2_INTERRUPT_PARRT  = 1 << 1,

    /*! Event counter overflow or increment.               */
    ALT_CACHE_L2_INTERRUPT_ECNTR  = 1 << 0
};
typedef enum ALT_CACHE_L2_INTERRUPT_e ALT_CACHE_L2_INTERRUPT_t;

/*!
 * Enables the L2 cache controller interrupts for the specified set of
 * condition(s).
 *
 * \param       interrupt
 *              A register mask of the selected L2 cache controller
 *              interrupting conditions.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_int_enable(uint32_t interrupt);

/*!
 * Disables the L2 cache controller interrupts for the specified set of
 * condition(s).
 *
 * \param       interrupt
 *              A register mask of the selected L2 cache controller
 *              interrupting conditions.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_int_disable(uint32_t interrupt);

/*!
 * Gets the condition(s) causing the L2 cache controller to interrupt as a
 * register mask.
 *
 * \returns     A register mask of the currently asserted and enabled
 *              conditions resulting in an interrupt being generated.
 */
uint32_t alt_cache_l2_int_status_get(void);

/*!
 * Clears the specified conditon(s) causing the L2 cache controller to
 * interrupt as a mask. Condition(s) specified which are not causing an
 * interrupt or condition(s) specified which are not enabled are ignored.
 *
 * \param       interrupt
 *              A register mask of the selected L2 cache controller
 *              interrupting conditions.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_cache_l2_int_status_clear(uint32_t interrupt);

/*!
 * @}
 */

/*!
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __ALT_CACHE_H__ */
