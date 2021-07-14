/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_L2PF0_H
#define METAL__DRIVERS__SIFIVE_L2PF0_H

/*!
 * @file sifive_l2pf0.h
 *
 * @brief API for configuring the SiFive L2 prefetcher.
 */

#include <stdint.h>

/*! @brief L2 prefetcher configuration */
typedef struct {
    /* Enable L2 hardware prefetcher */
    uint8_t HwPrefetchEnable;

    /* Only works when CrossPageEn === 0.
        Cross Page optimization disable:
        0 -> Entry goes into Pause state while crossing Page boundary.
        Next time when the demand miss happens on the same page, it doesn’t need
       to train again. 1 -> The entry is invalidated in case of a cross page. */
    uint8_t CrossPageOptmDisable;

    /* Enable prefetches to cross pages */
    uint8_t CrossPageEn;

    /* Age-out mechanism enable */
    uint8_t AgeOutEn;

    uint32_t PrefetchDistance;

    uint32_t MaxAllowedDistance;

    /* Linear to exponential threshold */
    uint32_t LinToExpThreshold;

    /* No. of non-matching loads to edge out an entry */
    uint32_t NumLdsToAgeOut;

    /* Threshold no. of Fullness (L2 MSHRs used/ total available) to stop
     * sending hits */
    uint32_t QFullnessThreshold;

    /* Threshold no. of CacheHits for evicting SPF entry */
    uint32_t HitCacheThreshold;

    /* Threshold no. of MSHR hits for increasing SPF distance */
    uint32_t hitMSHRThreshold;

    /* Size of the comparison window for address matching */
    uint32_t Window;

} sifive_l2pf0_config;

/*! @brief Enable L2 hardware prefetcher unit.
 * @param None.
 * @return None.*/
void sifive_l2pf0_enable(void);

/*! @brief Disable L2 hardware prefetcher unit.
 * @param None.
 * @return None.*/
void sifive_l2pf0_disable(void);

/*! @brief Get currently active L2 prefetcher configuration.
 * @param config Pointer to user specified configuration structure.
 * @return None.*/
void sifive_l2pf0_get_config(sifive_l2pf0_config *config);

/*! @brief Enables fine grain access to L2 prefetcher configuration.
 * @param config Pointer to user structure with values to be set.
 * @return None.*/
void sifive_l2pf0_set_config(sifive_l2pf0_config *config);

#endif
