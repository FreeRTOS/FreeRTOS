/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/** \addtogroup dmad_module
 *
 * \section DmaHw Dma Hardware Interface Usage
 * <ul>
 * <li> The DMA controller can handle the transfer between peripherals and memory 
 * and so receives the triggers from the peripherals. The hardware interface 
 * number are getting from DMAIF_Get_ChannelNumber().</li>

 * <li> DMAIF_IsValidatedPeripherOnDma() helps to check if the given DMAC has  
 * associated peripheral identifier coded by the given  peripheral.</li>
 * 
 * </ul>
 */
/*@{*/
/*@}*/

/** \file */
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/
/** Array of DMA Channel definition for SAMv7 chip*/
static const XdmaHardwareInterface xdmaHwIf[] = {
/* xdmac, peripheral,  T/R, HW interface number*/
	{0,   ID_HSMCI,     0,      0},
	{0,   ID_HSMCI,     1,      0},
	{0,   ID_SPI0,      0,      1},
	{0,   ID_SPI0,      1,      2},
	{0,   ID_SPI1,      0,      3},
	{0,   ID_SPI1,      1,      4},
	{0,   ID_QSPI,      0,      5},
	{0,   ID_QSPI,      1,      6},
	{0,   ID_USART0,    0,      7},
	{0,   ID_USART0,    1,      8},
	{0,   ID_USART1,    0,      9},
	{0,   ID_USART1,    1,      10},
	{0,   ID_USART2,    0,      11},
	{0,   ID_USART2,    1,      12},
	{0,   ID_PWM0,      0,      13},
	{0,   ID_TWIHS0,    0,      14},
	{0,   ID_TWIHS0,    1,      15},
	{0,   ID_TWIHS1,    0,      16},
	{0,   ID_TWIHS1,    1,      17},
	{0,   ID_TWIHS2,    0,      18},
	{0,   ID_TWIHS2,    1,      19},
	{0,   ID_UART0,     0,      20},
	{0,   ID_UART0,     1,      21},
	{0,   ID_UART1,     0,      22},
	{0,   ID_UART1,     1,      23},
	{0,   ID_UART2,     0,      24},
	{0,   ID_UART2,     1,      25},
	{0,   ID_UART3,     0,      26},
	{0,   ID_UART3,     1,      27},
	{0,   ID_UART4,     0,      28},
	{0,   ID_UART4,     1,      29},
	{0,   ID_DACC,      0,      30},
	{0,   ID_DACC,      0,      31},
	{0,   ID_SSC,       0,      32},
	{0,   ID_SSC,       1,      33},
	{0,   ID_PIOA,      1,      34},
	{0,   ID_AFEC0,     1,      35},
	{0,   ID_AFEC1,     1,      36},
	{0,   ID_AES,       0,      37},
	{0,   ID_AES,       1,      38},
	{0,   ID_PWM1,      0,      39},
	{0,   ID_TC0,       1,      40},
	{0,   ID_TC1,       1,      41},
	{0,   ID_TC2,       1,      42},
	{0,   ID_TC3,       1,      43},
};


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Get peripheral identifier coded for hardware handshaking interface
 *
 * \param bDmac      DMA Controller number.
 * \param bPeriphID  Peripheral ID.
 * \param bTransfer  Transfer type 0: Tx, 1 :Rx.
 * \return 0-15 peripheral identifier coded.
 *         0xff : no associated peripheral identifier coded.
 */
uint8_t XDMAIF_Get_ChannelNumber (uint8_t bPeriphID,
		uint8_t bTransfer)
{
	uint8_t i;
	uint8_t NumOfPeripheral = ((XDMAC_GetType(XDMAC) & 0x00FF0000) >> 16);
	for (i = 0; i <=NumOfPeripheral; i++)
	{
		if ( (xdmaHwIf[i].bPeriphID == bPeriphID) && 
				(xdmaHwIf[i].bTransfer == bTransfer)) {
			return xdmaHwIf[i].bIfID;
		}
	}
	return 0xff;
}

/**
 * \brief Check if the given DMAC has associated peripheral identifier coded by
 * the given  peripheral.
 *
 * \param bDmac      DMA Controller number.
 * \param bPeriphID  Peripheral ID (0xff : memory only).
 * \return 1:  Is a validated peripheral. 0: no associated peripheral identifier 
 * coded.
 */
uint8_t XDMAIF_IsValidatedPeripherOnDma( uint8_t bPeriphID)
{
	uint8_t i;
	uint8_t NumOfPeripheral = ((XDMAC_GetType(XDMAC) & 0x00FF0000) >> 16);
	/* It is always validated when transfer to memory */
	if (bPeriphID == 0xFF) {
		return 1;
	}

	for (i = 0; i <=NumOfPeripheral; i++) {
		if ((xdmaHwIf[i].bPeriphID == bPeriphID)) {
			return 1;
		}
	}
	return 0;
}
