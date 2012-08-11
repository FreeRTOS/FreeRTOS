/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * This file contains the addresses and size of the various blocks of data
 * stored in eNVM.
 *
 * SVN $Revision: 1113 $
 * SVN $Date: 2009-07-01 11:11:29 +0100 (Wed, 01 Jul 2009) $
 */
#ifndef ENVM_LAYOUT_HEADER
#define ENVM_LAYOUT_HEADER

#ifdef __cplusplus
extern "C" {
#endif 

/*==============================================================================
 * Address of the manufacturing test data.
 */
#define MTD_ADDRESS 0x60080010

/*==============================================================================
 * MSS configuration location.
 */
#define MSS_CONFIG_ADDRESS        0x60081618

/*==============================================================================
 * Analog configuration location and size.
 */
#define ANALOG_CONFIG_ADDRESS     0x60081600
#define ANALOG_CONFIG_BYTE_SIZE   24

#ifdef __cplusplus
}
#endif

#endif  /* ENVM_LAYOUT_HEADER */
