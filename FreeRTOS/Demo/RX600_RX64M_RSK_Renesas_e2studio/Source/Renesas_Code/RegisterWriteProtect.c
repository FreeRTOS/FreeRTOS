/*
 * RegisterWriteProtect.c
 *
 *  Created on: 4 Mar 2014
 *      Author: WarnerR
 */

#include "../iodefine.h"
#include "stdint.h"

#define	PRC0_BIT	0x0001
#define	PRC1_BIT	0x0002
#define	PRC3_BIT	0x0008


void EnablePRCR( uint16_t protect )
{
	/*
	 * PRCR 	Bit Register to be Protected
	 * -----------------------------------------------------------------------------------------------------------------------------------------
	 * PRC0 	Registers related to the clock generation circuit:
	 * 			SCKCR, SCKCR2, SCKCR3, PLLCR, PLLCR2, BCKCR, MOSCCR, SOSCCR, LOCOCR, ILOCOCR, HOCOCR, HOCOCR2, OSTDCR, OSTDSR
	 *
	 * PRC1 	Registers related to the operating modes:
	 * 			SYSCR0, SYSCR1
	 *
	 * 			Registers related to the low power consumption functions:
	 * 			SBYCR, MSTPCRA, MSTPCRB, MSTPCRC, MSTPCRD, OPCCR, RSTCKCR, DPSBYCR, DPSIER0 to DPSIER3, DPSIFR0 to DPSIFR3, DPSIEGR0 to DPSIEGR3
	 *
	 * 			Registers related to clock generation circuit:
	 * 			MOSCWTCR, SOSCWTCR, MOFCR, HOCOPCR
	 *
	 * 			Software reset register:
	 * 			SWRR
	 *
	 * PRC3 	Registers related to the LVD:
	 * 			LVCMPCR, LVDLVLR, LVD1CR0, LVD1CR1, LVD1SR, LVD2CR0, LVD2CR1, LVD2SR
	 */
	SYSTEM.PRCR.WORD = (uint16_t)( 0xA500 | protect );
}

void DisablePRCR( uint16_t protect )
{
	/*
	 * PRCR 	Bit Register to be Protected
	 * -----------------------------------------------------------------------------------------------------------------------------------------
	 * PRC0 	Registers related to the clock generation circuit:
	 * 			SCKCR, SCKCR2, SCKCR3, PLLCR, PLLCR2, BCKCR, MOSCCR, SOSCCR, LOCOCR, ILOCOCR, HOCOCR, HOCOCR2, OSTDCR, OSTDSR
	 *
	 * PRC1 	Registers related to the operating modes:
	 * 			SYSCR0, SYSCR1
	 *
	 * 			Registers related to the low power consumption functions:
	 * 			SBYCR, MSTPCRA, MSTPCRB, MSTPCRC, MSTPCRD, OPCCR, RSTCKCR, DPSBYCR, DPSIER0 to DPSIER3, DPSIFR0 to DPSIFR3, DPSIEGR0 to DPSIEGR3
	 *
	 * 			Registers related to clock generation circuit:
	 * 			MOSCWTCR, SOSCWTCR, MOFCR, HOCOPCR
	 *
	 * 			Software reset register:
	 * 			SWRR
	 *
	 * PRC3 	Registers related to the LVD:
	 * 			LVCMPCR, LVDLVLR, LVD1CR0, LVD1CR1, LVD1SR, LVD2CR0, LVD2CR1, LVD2SR
	 */
	uint16_t current_value;

	current_value = (uint16_t)( SYSTEM.PRCR.WORD & 0x00ff );
	current_value = (uint16_t)( current_value & ~protect );

	SYSTEM.PRCR.WORD = (uint16_t)( 0xA500 | current_value );
}

