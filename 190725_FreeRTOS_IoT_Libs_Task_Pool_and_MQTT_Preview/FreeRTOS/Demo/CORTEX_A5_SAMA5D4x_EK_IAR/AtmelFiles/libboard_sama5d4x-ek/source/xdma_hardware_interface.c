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
 * and so receives the triggers from the peripherals. The hardware interface number
 * are getting from DMAIF_Get_ChannelNumber().</li>
 
 * <li> DMAIF_IsValidatedPeripherOnDma() helps to check if the given DMAC has associated 
 * peripheral identifier coded by the given  peripheral.</li>
 * 
 * </ul>
*/
/*@{*/
/*@}*/

/** \file */
 /*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <board.h>

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/
/** Array of DMA Channel definition for SAMA5 chip*/
static const XdmaHardwareInterface xdmaHwIf[] = {
    /* dmac, peripheral,  T/R, Channel Number*/
       {0,   ID_HSMCI0,   0,   0},
       {0,   ID_HSMCI0,   1,   0},
       {0,   ID_HSMCI1,   0,   1},
       {0,   ID_HSMCI1,   1,   1},
       {0,   ID_TWI0,     0,   2},
       {0,   ID_TWI0,     1,   3},
       {0,   ID_TWI1,     0,   4},
       {0,   ID_TWI1,     1,   5},
       {0,   ID_TWI2,     0,   6},
       {0,   ID_TWI2,     1,   7},
       {0,   ID_TWI3,     0,   8},
       {0,   ID_TWI3,     1,   9},
       {0,   ID_SPI0,     0,   10},
       {0,   ID_SPI0,     1,   11},
       {0,   ID_SPI1,     0,   12},
       {0,   ID_SPI1,     1,   13},
       {0,   ID_SPI2,     0,   14},
       {0,   ID_SPI2,     1,   15},
       {0,   ID_USART2,   0,   16},
       {0,   ID_USART2,   1,   17},
       {0,   ID_USART3,   0,   18},
       {0,   ID_USART3,   1,   19},
       {0,   ID_USART4,   0,   20},
       {0,   ID_USART4,   1,   21},
       {0,   ID_UART0,    0,   22},
       {0,   ID_UART0,    1,   23},
       {0,   ID_UART1,    0,   24},
       {0,   ID_UART1,    1,   25},
       {0,   ID_SSC0,     0,   26},
       {0,   ID_SSC0,     1,   27},
       {0,   ID_SSC1,     0,   28},
       {0,   ID_SSC1,     1,   29},
       {0,   ID_DBGU,     0,   30},
       {0,   ID_DBGU,     1,   31},
       {0,   ID_ADC,      1,   32},
       {0,   ID_SMD,      1,   33},
       {0,   ID_SMD,      1,   34},
       {0,   ID_MSADCC,   1,   35},
       {0,   ID_USART0,   0,   36},
       {0,   ID_USART0,   1,   37},
       {0,   ID_USART1,   0,   38},
       {0,   ID_USART1,   1,   39},
       {0,   ID_AES,      1,   40},
       {0,   ID_AES,      0,   41},
       {0,   ID_TDES,     0,   42},
       {0,   ID_TDES,     1,   43},
       {0,   ID_SHA,      0,   44},
//     {0,   ID_CTB,      1,   45},
       {0,   ID_CATB,     0,   46},
       {0,   ID_CATB,     1,   47},
    /* dmac 1 */
       {1,   ID_HSMCI0,   0,   0},
       {1,   ID_HSMCI0,   1,   0},
       {1,   ID_HSMCI1,   0,   1},
       {1,   ID_HSMCI1,   1,   1},
       {1,   ID_TWI0,     0,   2},
       {1,   ID_TWI0,     1,   3},
       {1,   ID_TWI1,     0,   4},
       {1,   ID_TWI1,     1,   5},
       {1,   ID_TWI2,     0,   6},
       {1,   ID_TWI2,     1,   7},
       {1,   ID_TWI3,     0,   8},
       {1,   ID_TWI3,     1,   9},
       {1,   ID_SPI0,     0,   10},
       {1,   ID_SPI0,     1,   11},
       {1,   ID_SPI1,     0,   12},
       {1,   ID_SPI1,     1,   13},
       {1,   ID_SPI2,     0,   14},
       {1,   ID_SPI2,     1,   15},
       {1,   ID_USART2,   0,   16},
       {1,   ID_USART2,   1,   17},
       {1,   ID_USART3,   0,   18},
       {1,   ID_USART3,   1,   19},
       {1,   ID_USART4,   0,   20},
       {1,   ID_USART4,   1,   21},
       {1,   ID_UART0,    0,   22},
       {1,   ID_UART0,    1,   23},
       {1,   ID_UART1,    0,   24},
       {1,   ID_UART1,    1,   25},
       {1,   ID_SSC0,     0,   26},
       {1,   ID_SSC0,     1,   27},
       {1,   ID_SSC1,     0,   28},
       {1,   ID_SSC1,     1,   29},
       {1,   ID_DBGU,     0,   30},
       {1,   ID_DBGU,     1,   31},
       {1,   ID_ADC,      1,   32},
       {1,   ID_SMD,      1,   33},
       {1,   ID_SMD,      1,   34},
};

/*----------------------------------------------------------------------------
 *        Consts
 *----------------------------------------------------------------------------*/
 /** Number of recognized peripheral identifier code for DMA0/1. */
#define NUMPERIPHERAL   (sizeof(xdmaHwIf) / sizeof (XdmaHardwareInterface))

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
uint8_t XDMAIF_Get_ChannelNumber (uint8_t bXdmac,
                                 uint8_t bPeriphID,
                                 uint8_t bTransfer)
{
    uint8_t i;
    for (i = 0; i < NUMPERIPHERAL; i++)
    {
        if ((xdmaHwIf[i].bXdmac == bXdmac) && (xdmaHwIf[i].bPeriphID == bPeriphID) && (xdmaHwIf[i].bTransfer == bTransfer))
        {
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
 * \return 1:  Is a validated peripher. 0: no associated peripheral identifier coded.
 */
uint8_t XDMAIF_IsValidatedPeripherOnDma( uint8_t bXdmac, uint8_t bPeriphID)
{
    uint8_t i;
    /* It is always validated when transfer to memory */
    if (bPeriphID == 0xFF) {
        return 1;
    }
    for (i = 0; i < NUMPERIPHERAL; i++)
    {
        if ((xdmaHwIf[i].bXdmac == bXdmac) && (xdmaHwIf[i].bPeriphID == bPeriphID))
        {
            return 1;
        }
    }
    return 0;
}


