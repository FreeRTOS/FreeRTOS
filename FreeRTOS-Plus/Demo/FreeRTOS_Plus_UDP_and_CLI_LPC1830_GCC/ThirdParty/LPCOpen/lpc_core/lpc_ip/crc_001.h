/*
 * @brief Cyclic Redundancy Check (CRC) registers and driver functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __CRC_001_H_
#define __CRC_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_CRC_001 IP: CRC register block and driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief CRC register block structure
 */
typedef struct {					/*!< CRC Structure */
	__IO    uint32_t    MODE;		/*!< CRC Mode Register */
	__IO    uint32_t    SEED;		/*!< CRC SEED Register */
	union {
		__I     uint32_t    SUM;	/*!< CRC Checksum Register. */
		__O     uint32_t    WRDATA32;	/*!< CRC Data Register: write size 32-bit*/
		__O     uint16_t    WRDATA16;	/*!< CRC Data Register: write size 16-bit*/
		__O     uint8_t     WRDATA8;	/*!< CRC Data Register: write size 8-bit*/
	};

} IP_CRC_001_T;

/**
 * @brief CRC MODE register description
 */
#define CRC_MODE_POLY_BITMASK   ((0x03))	/** CRC polynomial Bit mask */
#define CRC_MODE_POLY_CCITT     (0x00)		/** Select CRC-CCITT polynomial */
#define CRC_MODE_POLY_CRC16     (0x01)		/** Select CRC-16 polynomial */
#define CRC_MODE_POLY_CRC32     (0x02)		/** Select CRC-32 polynomial */
#define CRC_MODE_WRDATA_BITMASK (0x03 << 2)	/** CRC WR_Data Config Bit mask */
#define CRC_MODE_WRDATA_BIT_RVS (1 << 2)	/** Select Bit order reverse for WR_DATA (per byte) */
#define CRC_MODE_WRDATA_CMPL    (1 << 3)	/** Select One's complement for WR_DATA */
#define CRC_MODE_SUM_BITMASK    (0x03 << 4)	/** CRC Sum Config Bit mask */
#define CRC_MODE_SUM_BIT_RVS    (1 << 4)	/** Select Bit order reverse for CRC_SUM */
#define CRC_MODE_SUM_CMPL       (1 << 5)	/** Select One's complement for CRC_SUM */

#define MODE_CFG_CCITT      (0x00)	/** Pre-defined mode word for default CCITT setup */
#define MODE_CFG_CRC16      (0x15)	/** Pre-defined mode word for default CRC16 setup */
#define MODE_CFG_CRC32      (0x36)	/** Pre-defined mode word for default CRC32 setup */

#define CRC_SEED_CCITT  (0x0000FFFF)/** Initial seed value for CCITT mode */
#define CRC_SEED_CRC16  (0x00000000)/** Initial seed value for CRC16 mode */
#define CRC_SEED_CRC32  (0xFFFFFFFF)/** Initial seed value for CRC32 mode */

/*
 * @brief CRC polynomial
 */
typedef enum IP_CRC_001_POLY {
	CRC_POLY_CCITT = CRC_MODE_POLY_CCITT,	/**< CRC-CCIT polynomial */
	CRC_POLY_CRC16 = CRC_MODE_POLY_CRC16,	/**< CRC-16 polynomial */
	CRC_POLY_CRC32 = CRC_MODE_POLY_CRC32,	/**< CRC-32 polynomial */
	CRC_POLY_LAST,
} IP_CRC_001_POLY_T;

/**
 * @brief	Initializes the CRC Engine
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_Init(IP_CRC_001_T *pCRC) {}

/**
 * @brief	De-initializes the CRC Engine
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_DeInit(IP_CRC_001_T *pCRC) {}

/**
 * @brief	Select polynomial for CRC Engine
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	poly	: CRC polynomial selection
 * @param	flags	: An Or'ed value of flags that setup the mode
 * @return	Nothing
 * @note	Flags for setting up the mode word include CRC_MODE_WRDATA_BIT_RVS,
 * CRC_MODE_WRDATA_CMPL, CRC_MODE_SUM_BIT_RVS, and CRC_MODE_SUM_CMPL.
 */
STATIC INLINE void IP_CRC_SetPoly(IP_CRC_001_T *pCRC, IP_CRC_001_POLY_T poly,
								  uint32_t flags)
{
	pCRC->MODE = (uint32_t) poly | flags;
}

/**
 * @brief	Sets up the CRC engine with defaults based on the polynomial to be used
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	poly	: The enumerated polynomial to be used
 * @return	Nothing
 */
void IP_CRC_UseDefaultConfig(IP_CRC_001_T *pCRC, IP_CRC_001_POLY_T poly);

/**
 * @brief	Get mode register of CRC Engine
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @return	Current CRC Mode register (Or-ed bits value of CRC_MODE_*)
 */
STATIC INLINE uint32_t IP_CRC_GetMode(IP_CRC_001_T *pCRC)
{
	return pCRC->MODE;
}

/**
 * @brief	Set mode register of CRC Engine
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	mode	: mode value to be set in mode register
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_SetMode(IP_CRC_001_T *pCRC, uint32_t mode)
{
	pCRC->MODE = mode;
}

/**
 * @brief	Set Seed value
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	Seed	: selected seed value
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_SetSeed(IP_CRC_001_T *pCRC, uint32_t Seed)
{
	pCRC->SEED = Seed;
}

/**
 * @brief	Get Seed value.
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @return	current seed value
 */
STATIC INLINE uint32_t IP_CRC_GetSeed(IP_CRC_001_T *pCRC)
{
	return pCRC->SEED;
}

/**
 * @brief	Write 8-bit data to CRC WR Data register.
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	data	: data to be written
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_Write8(IP_CRC_001_T *pCRC, uint8_t data)
{
	pCRC->WRDATA8 = data;
}

/**
 * @brief	Write 16-bit data to CRC WR Data register.
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	data	: data to be written
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_Write16(IP_CRC_001_T *pCRC, uint16_t data)
{
	pCRC->WRDATA16 = (uint32_t) data;
}

/**
 * @brief	Write 32-bit data to CRC WR Data register.
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	data	: data to be written
 * @return	Nothing
 */
STATIC INLINE void IP_CRC_Write32(IP_CRC_001_T *pCRC, uint32_t data)
{
	pCRC->WRDATA32 = data;
}

/**
 * @brief	Read current calculated checksum from CRC Engine
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @return	Check sum value
 */
STATIC INLINE uint32_t IP_CRC_ReadSum(IP_CRC_001_T *pCRC)
{
	return pCRC->SUM;
}

/**
 * @brief	Convenience function for computing a standard CCITT checksum from an 8-bit data block
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	data	: Pointer to the block of 8 bit data
 * @param   bytes	: The number of bytes pointed to by data
 * @return	Computed checksum for the block
 */
uint32_t IP_CRC_CRC8(IP_CRC_001_T *pCRC, const uint8_t *data, uint32_t bytes);

/**
 * @brief	Convenience function for computing a standard CRC16 checksum from 16-bit data block
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	data	: Pointer to the block of 16-bit data
 * @param   hwords	: The number of halfword entries pointed to by data
 * @return	Computed checksum for the block
 */
uint32_t IP_CRC_CRC16(IP_CRC_001_T *pCRC, const uint16_t *data, uint32_t hwords);

/**
 * @brief	Convenience function for computing a standard CRC32 checksum from 32-bit data block
 * @param	pCRC	: Pointer to selected CRC Engine register block structure
 * @param	data	: Pointer to the block of 32-bit data
 * @param   words	: The number of 32-bit entries pointed to by data
 * @return	Computed checksum for the block
 */
uint32_t IP_CRC_CRC32(IP_CRC_001_T *pCRC, const uint32_t *data, uint32_t words);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __CRC_001_H_ */
