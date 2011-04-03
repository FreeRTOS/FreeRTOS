/***************************************************************************//**
 * @file
 * SmartFusion MSS Ethenet MAC configuration header file.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2299 $
 * SVN $Date: 2010-02-24 21:21:12 +0000 (Wed, 24 Feb 2010) $
 *******************************************************************************/
#ifndef __MSS_ETHERNET_MAC_CONF_H
#define __MSS_ETHERNET_MAC_CONF_H	1

#ifdef __cplusplus
extern "C" {
#endif 

/**
 * Default MAC address
 */
#define DEFAULT_MAC_ADDRESS             0xC0u,0xB1u,0x3Cu,0x88u,0x88u,0x88u
#define BROADCAST_MAC_ADDRESS 			0xFFu,0xFFu,0xFFu,0xFFu,0xFFu,0xFFu

/**
 * Descriptor byte ordering mode.
 * 1 - Big-endian mode used for data descriptors <br>
 * 0 - Little-endian mode used for data descriptors <br>
 */
#define DESCRIPTOR_BYTE_ORDERING_MODE   LITTLEENDIAN

/**
 * Big/little endian.
 * Selects the byte-ordering mode used by the data buffers.
 * 1 - Big-endian mode used for the data buffers
 * 0 - Little-endian mode used for the data buffers
 */
#define BUFFER_BYTE_ORDERING_MODE       LITTLEENDIAN

#ifdef __cplusplus
}
#endif

#endif	/* __MSS_ETHERNET_MAC_CONF_H */

