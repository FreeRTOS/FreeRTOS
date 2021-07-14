/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__SCRUB_H
#define METAL__SCRUB_H

/*! @brief Writes specified memory region with zeros.
 * @param address Start memory address for zero-scrub.
 * @param size Memory region size in bytes.
 * @return None.*/
void metal_mem_scrub(void *address, int size);

#endif
