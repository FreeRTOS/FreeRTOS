/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_BUSERROR0_H
#define METAL__DRIVERS__SIFIVE_BUSERROR0_H

/*!
 * @file sifive_buserror0.h
 *
 * @brief API for configuring the SiFive Bus Error Unit
 */

#include <metal/compiler.h>
#include <stdbool.h>
#include <stdint.h>

/*!
 * @brief The set of possible events handled by a SiFive Bus Error Unit
 */
typedef enum {
    /*! @brief No event or error has been detected */
    METAL_BUSERROR_EVENT_NONE = 0,

    /*! @brief A correctable ECC error has occurred in the I$ or ITIM */
    METAL_BUSERROR_EVENT_INST_CORRECTABLE_ECC_ERROR = (1 << 2),
    /*! @brief An uncorrectable ECC error has occurred in the I$ or ITIM */
    METAL_BUSERROR_EVENT_INST_UNCORRECTABLE_ECC_ERROR = (1 << 3),
    /*! @brief A TileLink load or store bus error has occurred */
    METAL_BUSERROR_EVENT_LOAD_STORE_ERROR = (1 << 5),
    /*! @brief A correctable ECC error has occurred in the D$ or DTIM */
    METAL_BUSERROR_EVENT_DATA_CORRECTABLE_ECC_ERROR = (1 << 6),
    /*! @brief An uncorrectable ECC error has occurred in the D$ or DTIM */
    METAL_BUSERROR_EVENT_DATA_UNCORRECTABLE_ECC_ERROR = (1 << 7),

    /*! @brief Used to set/clear all interrupts or query/clear all accrued
       events */
    METAL_BUSERROR_EVENT_ALL =
        METAL_BUSERROR_EVENT_INST_CORRECTABLE_ECC_ERROR |
        METAL_BUSERROR_EVENT_INST_UNCORRECTABLE_ECC_ERROR |
        METAL_BUSERROR_EVENT_LOAD_STORE_ERROR |
        METAL_BUSERROR_EVENT_DATA_CORRECTABLE_ECC_ERROR |
        METAL_BUSERROR_EVENT_DATA_UNCORRECTABLE_ECC_ERROR,
    /*! @brief A synonym of METAL_BUSERROR_EVENT_ALL */
    METAL_BUSERROR_EVENT_ANY = METAL_BUSERROR_EVENT_ALL,

    /*! @brief A value which is impossible for the bus error unit to report.
     * Indicates an error has occurred if provided as a return value. */
    METAL_BUSERROR_EVENT_INVALID = (1 << 8),
} metal_buserror_event_t;

/*!
 * @brief The handle for a bus error unit
 */
struct metal_buserror {
    uint8_t __no_empty_structs;
};

/*!
 * @brief Enable bus error events
 *
 * Enabling bus error events causes them to be registered as accrued and,
 * if the corresponding interrupt is inabled, trigger interrupts.
 *
 * @param beu The bus error unit handle
 * @param events A mask of error events to enable
 * @param enabled True if the mask should be enabled, false if they should be
 * disabled
 * @return 0 upon success
 */
int metal_buserror_set_event_enabled(struct metal_buserror *beu,
                                     metal_buserror_event_t events,
                                     bool enabled);

/*!
 * @brief Get enabled bus error events
 * @param beu The bus error unit handle
 * @return A mask of all enabled events
 */
metal_buserror_event_t
metal_buserror_get_event_enabled(struct metal_buserror *beu);

/*!
 * @brief Enable or disable the platform interrupt
 *
 * @param beu The bus error unit handle
 * @param event The error event which would trigger the interrupt
 * @param enabled True if the interrupt should be enabled
 * @return 0 upon success
 */
int metal_buserror_set_platform_interrupt(struct metal_buserror *beu,
                                          metal_buserror_event_t events,
                                          bool enabled);

/*!
 * @brief Enable or disable the hart-local interrupt
 *
 * @param beu The bus error unit handle
 * @param event The error event which would trigger the interrupt
 * @param enabled True if the interrupt should be enabled
 * @return 0 upon success
 */
int metal_buserror_set_local_interrupt(struct metal_buserror *beu,
                                       metal_buserror_event_t events,
                                       bool enabled);

/*!
 * @brief Get the error event which caused the most recent interrupt
 *
 * This method should be called from within the interrupt handler for the bus
 * error unit interrupt
 *
 * @param beu The bus error unit handle
 * @return The event which caused the interrupt
 */
metal_buserror_event_t metal_buserror_get_cause(struct metal_buserror *beu);

/*!
 * @brief Clear the cause register for the bus error unit
 *
 * This method should be called from within the interrupt handler for the bus
 * error unit to un-latch the cause register for the next event
 *
 * @param beu The bus error unit handle
 * @return 0 upon success
 */
int metal_buserror_clear_cause(struct metal_buserror *beu);

/*!
 * @brief Get the physical address of the error event
 *
 * This method should be called from within the interrupt handler for the bus
 * error unit.
 *
 * @param beu The bus error unit handle
 * @return The address of the error event
 */
uintptr_t metal_buserror_get_event_address(struct metal_buserror *beu);

/*!
 * @brief Returns true if the event is set in the accrued register
 *
 * @param beu The bus error unit handle
 * @param event The event to query
 * @return True if the event is set in the accrued register
 */
bool metal_buserror_is_event_accrued(struct metal_buserror *beu,
                                     metal_buserror_event_t events);

/*!
 * @brief Clear the given event from the accrued register
 *
 * @param beu The bus error unit handle
 * @param event The event to clear
 * @return 0 upon success
 */
int metal_buserror_clear_event_accrued(struct metal_buserror *beu,
                                       metal_buserror_event_t events);

/*!
 * @brief get the platform-level interrupt parent of the bus error unit
 *
 * @param beu The bus error unit handle
 * @return A pointer to the interrupt parent
 */
struct metal_interrupt *
metal_buserror_get_platform_interrupt_parent(struct metal_buserror *beu);

/*!
 * @brief Get the platform-level interrupt id for the bus error unit interrupt
 *
 * @param beu The bus error unit handle
 * @return The interrupt id
 */
int metal_buserror_get_platform_interrupt_id(struct metal_buserror *beu);

/*!
 * @brief Get the hart-local interrupt id for the bus error unit interrupt
 *
 * @param beu The bus error unit handle
 * @return The interrupt id
 */
int metal_buserror_get_local_interrupt_id(struct metal_buserror *beu);

#endif
