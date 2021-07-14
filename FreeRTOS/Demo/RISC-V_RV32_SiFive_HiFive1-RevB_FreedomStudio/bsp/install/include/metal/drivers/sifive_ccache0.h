/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_CCACHE0_H
#define METAL__DRIVERS__SIFIVE_CCACHE0_H

/*!
 * @file sifive_ccache0.h
 *
 * @brief API for configuring the SiFive L2 cache controller
 */

#include <metal/interrupt.h>
#include <stdint.h>

/*! @brief Cache configuration data */
typedef struct {
    uint32_t num_bank;
    uint32_t num_ways;
    uint32_t num_sets;
    uint32_t block_size;
} sifive_ccache0_config;

/*! @brief Set of values for ECC error type */
typedef enum {
    SIFIVE_CCACHE0_DATA = 0,
    SIFIVE_CCACHE0_DIR = 1,
} sifive_ccache0_ecc_errtype_t;

/*! @brief Initialize cache controller, enables all available
 *         cache-ways.
 *         Note: If LIM is in use, corresponding cache ways are not enabled.
 * @param None.
 * @return 0 If no error.*/
int sifive_ccache0_init(void);

/*! @brief Get cache configuration data.
 * @param config User specified data buffer.
 * @return None.*/
void sifive_ccache0_get_config(sifive_ccache0_config *config);

/*! @brief Get currently active cache ways.
 * @param None.
 * @return Number of cache ways enabled.*/
uint32_t sifive_ccache0_get_enabled_ways(void);

/*! @brief Enable specified cache ways.
 * @param ways Number of ways to be enabled.
 * @return 0 If no error.*/
int sifive_ccache0_set_enabled_ways(uint32_t ways);

/*! @brief Inject ECC error into data or meta-data.
 * @param bitindex Bit index to be corrupted on next cache operation.
 * @param type ECC error target location.
 * @return None.*/
void sifive_ccache0_inject_ecc_error(uint32_t bitindex,
                                     sifive_ccache0_ecc_errtype_t type);

/*! @brief Flush out entire cache block containing given address.
 * @param flush_addr Address for the cache block to be flushed.
 * @return None.*/
void sifive_ccache0_flush(uintptr_t flush_addr);

/*! @brief Get most recently ECC corrected address.
 * @param type ECC error target location.
 * @return Last corrected ECC address.*/
uintptr_t sifive_ccache0_get_ecc_fix_addr(sifive_ccache0_ecc_errtype_t type);

/*! @brief Get number of times ECC errors were corrected.
 *         Clears related ECC interrupt signals.
 * @param type ECC error target location.
 * @return Corrected ECC error count.*/
uint32_t sifive_ccache0_get_ecc_fix_count(sifive_ccache0_ecc_errtype_t type);

/*! @brief Get address location of most recent uncorrected ECC error.
 * @param type ECC error target location.
 * @return Last uncorrected ECC address.*/
uintptr_t sifive_ccache0_get_ecc_fail_addr(sifive_ccache0_ecc_errtype_t type);

/*! @brief Get number of times ECC errors were not corrected.
 *         Clears related ECC interrupt signals.
 * @param type ECC error target location.
 * @return Uncorrected ECC error count.*/
uint32_t sifive_ccache0_get_ecc_fail_count(sifive_ccache0_ecc_errtype_t type);

/*! @brief Get currently active way enable mask value for the given master ID.
 * @param master_id Cache controller master ID.
 * @return Way enable mask. */
uint64_t sifive_ccache0_get_way_mask(uint32_t master_id);

/*! @brief Set way enable mask for the given master ID.
 * @param master_id Cache controller master ID.
 * @param waymask Specify ways to be enabled.
 * @return 0 If no error.*/
int sifive_ccache0_set_way_mask(uint32_t master_id, uint64_t waymask);

/*! @brief Select cache performance events to be counted.
 * @param counter Cache performance monitor counter index.
 * @param mask Event selection mask.
 * @return None.*/
void sifive_ccache0_set_pmevent_selector(uint32_t counter, uint64_t mask);

/*! @brief Get currently set events for the given counter index.
 * @param counter Cache performance monitor counter index.
 * @return Event selection mask.*/
uint64_t sifive_ccache0_get_pmevent_selector(uint32_t counter);

/*! @brief Clears specified cache performance counter.
 * @param counter Cache performance monitor counter index.
 * @return None.*/
void sifive_ccache0_clr_pmevent_counter(uint32_t counter);

/*! @brief Reads specified cache performance counter.
 * @param counter Cache performance monitor counter index.
 * @return Counter value.*/
uint64_t sifive_ccache0_get_pmevent_counter(uint32_t counter);

/*! @brief Select cache clients to be excluded from performance monitoring.
 * @param mask Client disable mask.
 * @return None.*/
void sifive_ccache0_set_client_filter(uint64_t mask);

/*! @brief Get currently set cache client disable mask.
 * @param None.
 * @return Client disable mask.*/
uint64_t sifive_ccache0_get_client_filter(void);

/*! @brief Get interrupt IDs for the cache controller.
 * @param src Interrupt trigger source index.
 * @return Interrupt id.*/
int sifive_ccache0_get_interrupt_id(uint32_t src);

/*! @brief Get interrupt controller of the cache.
 * The interrupt controller must be initialized before any interrupts can be
 * registered or enabled with it.
 * @param None.
 * @return Handle for the interrupt controller.*/
struct metal_interrupt *sifive_ccache0_interrupt_controller(void);

#endif
