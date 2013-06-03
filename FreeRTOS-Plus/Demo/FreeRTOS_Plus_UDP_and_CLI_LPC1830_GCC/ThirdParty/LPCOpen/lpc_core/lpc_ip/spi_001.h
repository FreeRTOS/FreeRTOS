/*
 * @brief SPI registers and control functions
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

#ifndef __SPI_001_H_
#define __SPI_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_SPI_001 IP: SPI register block and driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief SPI register block structure
 */
typedef struct {					/*!< SPI Structure          */
	__IO uint32_t  CR;				/*!< SPI Control Register. This register controls the operation of the SPI. */
	__I  uint32_t  SR;				/*!< SPI Status Register. This register shows the status of the SPI. */
	__IO uint32_t  DR;				/*!< SPI Data Register. This bi-directional register provides the transmit and receive data for the SPI. Transmit data is provided to the SPI0 by writing to this register. Data received by the SPI0 can be read from this register. */
	__IO uint32_t  CCR;				/*!< SPI Clock Counter Register. This register controls the frequency of a master's SCK0. */
	__I  uint32_t  RESERVED0[3];
	__IO uint32_t  INT;				/*!< SPI Interrupt Flag. This register contains the interrupt flag for the SPI interface. */
} IP_SPI_001_T;

/*
 * Macro defines for SPI Control register
 */
/* SPI CFG Register BitMask */
#define SPI_CR_BITMASK       ((uint32_t) 0xFFC)
/** Enable of controlling the number of bits per transfer  */
#define SPI_CR_BIT_EN         ((uint32_t) (1 << 2))
/** Mask of field of bit controlling */
#define SPI_CR_BITS_MASK      ((uint32_t) 0xF00)
/** Set the number of bits per a transfer */
#define SPI_CR_BITS(n)        ((uint32_t) ((n << 8) & 0xF00))	/* n is in range 8-16 */
/** SPI Clock Phase Select*/
#define SPI_CR_CPHA_FIRST     ((uint32_t) (0))	/*Capture data on the first edge, Change data on the following edge*/
#define SPI_CR_CPHA_SECOND    ((uint32_t) (1 << 3))	/*Change data on the first edge, Capture data on the following edge*/
/** SPI Clock Polarity Select*/
#define SPI_CR_CPOL_LO        ((uint32_t) (0))	/* The rest state of the clock (between frames) is low.*/
#define SPI_CR_CPOL_HI        ((uint32_t) (1 << 4))	/* The rest state of the clock (between frames) is high.*/
/** SPI Slave Mode Select */
#define SPI_CR_SLAVE_EN       ((uint32_t) 0)
/** SPI Master Mode Select */
#define SPI_CR_MASTER_EN      ((uint32_t) (1 << 5))
/** SPI MSB First mode enable */
#define SPI_CR_MSB_FIRST_EN   ((uint32_t) 0)	/*Data will be transmitted and received in standard order (MSB first).*/
/** SPI LSB First mode enable */
#define SPI_CR_LSB_FIRST_EN   ((uint32_t) (1 << 6))	/*Data will be transmitted and received in reverse order (LSB first).*/
/** SPI interrupt enable */
#define SPI_CR_INT_EN         ((uint32_t) (1 << 7))

/*
 * Macro defines for SPI Status register
 */
/** SPI STAT Register BitMask */
#define SPI_SR_BITMASK        ((uint32_t) 0xF8)
/** Slave abort Flag */
#define SPI_SR_ABRT           ((uint32_t) (1 << 3))	/* When 1, this bit indicates that a slave abort has occurred. */
/* Mode fault Flag */
#define SPI_SR_MODF           ((uint32_t) (1 << 4))	/* when 1, this bit indicates that a Mode fault error has occurred. */
/** Read overrun flag*/
#define SPI_SR_ROVR           ((uint32_t) (1 << 5))	/* When 1, this bit indicates that a read overrun has occurred. */
/** Write collision flag. */
#define SPI_SR_WCOL           ((uint32_t) (1 << 6))	/* When 1, this bit indicates that a write collision has occurred.. */
/** SPI transfer complete flag. */
#define SPI_SR_SPIF           ((uint32_t) (1 << 7))		/* When 1, this bit indicates when a SPI data transfer is complete.. */
/** SPI error flag */
#define SPI_SR_ERROR          (SPI_SR_ABRT | SPI_SR_MODF | SPI_SR_ROVR | SPI_SR_WCOL)
/*
 * Macro defines for SPI Test Control Register register
 */
/*Enable SPI Test Mode */
#define SPI_TCR_TEST(n)       ((uint32_t) ((n & 0x3F) << 1))

/*
 * Macro defines for SPI Interrupt register
 */
/** SPI interrupt flag */
#define SPI_INT_SPIF          ((uint32_t) (1 << 0))

/**
 * Macro defines for SPI Data register
 */
/** Receiver Data  */
#define SPI_DR_DATA(n)        ((uint32_t) ((n) & 0xFFFF))

/** @brief SPI Mode*/
typedef enum IP_SPI_MODE {
	SPI_MODE_MASTER = SPI_CR_MASTER_EN,			/* Master Mode */
	SPI_MODE_SLAVE = SPI_CR_SLAVE_EN,			/* Slave Mode */
} IP_SPI_MODE_T;

/** @brief SPI Clock Mode*/
typedef enum IP_SPI_CLOCK_MODE {
	SPI_CLOCK_CPHA0_CPOL0 = SPI_CR_CPOL_LO | SPI_CR_CPHA_FIRST,		/**< CPHA = 0, CPOL = 0 */
	SPI_CLOCK_CPHA0_CPOL1 = SPI_CR_CPOL_HI | SPI_CR_CPHA_FIRST,		/**< CPHA = 0, CPOL = 1 */
	SPI_CLOCK_CPHA1_CPOL0 = SPI_CR_CPOL_LO | SPI_CR_CPHA_SECOND,	/**< CPHA = 1, CPOL = 0 */
	SPI_CLOCK_CPHA1_CPOL1 = SPI_CR_CPOL_HI | SPI_CR_CPHA_SECOND,	/**< CPHA = 1, CPOL = 1 */
	SPI_CLOCK_MODE0 = SPI_CLOCK_CPHA0_CPOL0,/**< alias */
	SPI_CLOCK_MODE1 = SPI_CLOCK_CPHA1_CPOL0,/**< alias */
	SPI_CLOCK_MODE2 = SPI_CLOCK_CPHA0_CPOL1,/**< alias */
	SPI_CLOCK_MODE3 = SPI_CLOCK_CPHA1_CPOL1,/**< alias */
} IP_SPI_CLOCK_MODE_T;

/** @brief SPI Data Order Mode*/
typedef enum IP_SPI_DATA_ORDER {
	SPI_DATA_MSB_FIRST = SPI_CR_MSB_FIRST_EN,			/* Standard Order */
	SPI_DATA_LSB_FIRST = SPI_CR_LSB_FIRST_EN,			/* Reverse Order */
} IP_SPI_DATA_ORDER_T;

/*
 * @brief Number of bits per frame
 */
typedef enum IP_SPI_BITS {
	SPI_BITS_8 = SPI_CR_BITS(8),		/**< 8 bits/frame */
	SPI_BITS_9 = SPI_CR_BITS(9),		/**< 9 bits/frame */
	SPI_BITS_10 = SPI_CR_BITS(10),		/**< 10 bits/frame */
	SPI_BITS_11 = SPI_CR_BITS(11),		/**< 11 bits/frame */
	SPI_BITS_12 = SPI_CR_BITS(12),		/**< 12 bits/frame */
	SPI_BITS_13 = SPI_CR_BITS(13),		/**< 13 bits/frame */
	SPI_BITS_14 = SPI_CR_BITS(14),		/**< 14 bits/frame */
	SPI_BITS_15 = SPI_CR_BITS(15),		/**< 15 bits/frame */
	SPI_BITS_16 = SPI_CR_BITS(16),		/**< 16 bits/frame */
} IP_SPI_BITS_T;

/**
 * @brief	Get the current status of SPI controller
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @return	SPI Status (Or-ed bit value of SPI_SR_*)
 * @note	 See user manual about how status bits are cleared.
 */
STATIC INLINE uint32_t IP_SPI_GetStatus(IP_SPI_001_T *pSPI)
{
	return pSPI->SR;
}

/**
 * @brief	Enable the interrupt for the SPI
 * @param	pSPI		: The base of SPI peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void IP_SPI_IntEnable(IP_SPI_001_T *pSPI)
{
	pSPI->CR |= SPI_CR_INT_EN;
}

/**
 * @brief	Disable the interrupt for the SPI
 * @param	pSPI		: The base of SPI peripheral on the chip
 * @return	Nothing
 */
STATIC INLINE void IP_SPI_IntDisable(IP_SPI_001_T *pSPI)
{
	pSPI->CR &= ~SPI_CR_INT_EN;
}

/**
 * @brief	Get the interrupt status
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @return	SPI interrupt Status (Or-ed bit value of SPI_INT_*)
 */
STATIC INLINE uint32_t IP_SPI_GetIntStatus(IP_SPI_001_T *pSPI)
{
	return pSPI->INT;
}

/**
 * @brief	Clear the interrupt status
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @param	mask	: SPI interrupt mask (Or-ed bit value of SPI_INT_*)
 * @return	Nothing
 */
STATIC INLINE void IP_SPI_ClearIntStatus(IP_SPI_001_T *pSPI, uint32_t mask)
{
	pSPI->INT = mask;
}

/**
 * @brief	Send SPI 16-bit data
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @param	data	: Transmit Data
 * @return	Nothing
 */
STATIC INLINE void IP_SPI_SendFrame(IP_SPI_001_T *pSPI, uint16_t data)
{
	pSPI->DR = SPI_DR_DATA(data);
}

/**
 * @brief	Get received SPI data
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @return	receive data
 */
STATIC INLINE uint16_t IP_SPI_ReceiveFrame(IP_SPI_001_T *pSPI)
{
	return SPI_DR_DATA(pSPI->DR);
}

/**
 * @brief	Set up output clocks per bit for SPI bus
 * @param	pSPI		: The base of SPI peripheral on the chip
 * @param	counter	: the number of SPI peripheral clock cycles that make up an SPI clock
 * @return	 Nothing
 * @note	The counter must be an even number greater than or equal to 8. <br>
 *		The SPI SCK rate = PCLK_SPI / counter.
 */
STATIC INLINE void IP_SPI_SetClockCounter(IP_SPI_001_T *pSPI, uint32_t counter)
{
	pSPI->CCR = counter;
}

/**
 * @brief	Set up the SPI frame format
 * @param	pSPI		: The base of SPI peripheral on the chip
 * @param	bits		: The number of bits transferred in each frame.
 * @param	clockMode	: Select Clock polarity and Clock phase, should be : <br>
 *							- SPI_CLOCK_CPHA0_CPOL0<br>
 *							- SPI_CLOCK_CPHA0_CPOL1<br>
 *							- SPI_CLOCK_CPHA1_CPOL0<br>
 *							- SPI_CLOCK_CPHA1_CPOL1<br>
 *							or SPI_CLOCK_MODE*
 * @param	order	: Data order (MSB first/LSB first).
 * @return	 Nothing
 * @note	Note: The clockFormat is only used in SPI mode
 */
STATIC INLINE void IP_SPI_SetFormat(IP_SPI_001_T *pSPI, IP_SPI_BITS_T bits,
									IP_SPI_CLOCK_MODE_T clockMode, IP_SPI_DATA_ORDER_T order)
{
	pSPI->CR = (pSPI->CR & (~0xF1C)) | SPI_CR_BIT_EN | bits | clockMode | order;
}

/**
 * @brief	Get the number of bits transferred in each frame
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @return	 the number of bits transferred in each frame
 */
STATIC INLINE IP_SPI_BITS_T IP_SPI_GetDataSize(IP_SPI_001_T *pSPI)
{
	return (pSPI->CR & SPI_CR_BIT_EN) ? ((IP_SPI_BITS_T) (pSPI->CR & SPI_CR_BITS_MASK)) : SPI_BITS_8;
}

/**
 * @brief	Get the current CPHA & CPOL setting
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @return	CPHA & CPOL setting
 */
STATIC INLINE IP_SPI_CLOCK_MODE_T IP_SPI_GetClockMode(IP_SPI_001_T *pSPI)
{
	return (IP_SPI_CLOCK_MODE_T) (pSPI->CR & (3 << 3));
}

/**
 * @brief	Set the SPI working as master or slave mode
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @param	mode	: Operating mode
 * @return	 Nothing
 */
STATIC INLINE void IP_SPI_SetMode(IP_SPI_001_T *pSPI, IP_SPI_MODE_T mode)
{
	pSPI->CR = (pSPI->CR & (~(1 << 5))) | mode;
}

/**
 * @brief	Set the SPI working as master or slave mode
 * @param	pSPI	: The base of SPI peripheral on the chip
 * @return	 Operating mode
 */
STATIC INLINE IP_SPI_MODE_T IP_SPI_GetMode(IP_SPI_001_T *pSPI)
{
	return (IP_SPI_MODE_T) (pSPI->CR & (1 << 5));
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __SPI_001_H_ */
