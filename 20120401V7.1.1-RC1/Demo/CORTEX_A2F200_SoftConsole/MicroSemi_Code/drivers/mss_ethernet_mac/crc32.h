/***************************************************************************//**
 * @file
 * crc32 header file.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2369 $
 * SVN $Date: 2010-03-01 18:31:45 +0000 (Mon, 01 Mar 2010) $
 ******************************************************************************/
 
#ifndef __MSS_ETHERNET_MAC_CRC32_H
#define __MSS_ETHERNET_MAC_CRC32_H	1

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif 

/**
 * Calculates 32 bits CRC value of given data.
 */
uint32_t
mss_mac_crc32
(
    uint32_t value,
    const uint8_t *data,
    uint32_t data_length
);

/**
 * Calculates 32 bits CRC value of given data, using standart Ethernet CRC 
 * function.
 */
uint32_t
mss_ethernet_crc
(
    const uint8_t *data,
    uint32_t data_length
);

#ifdef __cplusplus
}
#endif

#endif	/* __MSS_ETHERNET_MAC_CRC32_H */
