/**********************************************************************
* $Id$		lpc18xx_gpdma.c		2011-06-02
*//**
* @file		lpc18xx_gpdma.c
* @brief	Contains all functions support for GPDMA firmware library
* 			on LPC18xx
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @addtogroup GPDMA
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_gpdma.h"
//#include "lpc18xx_cgu.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */

#ifdef _GPDMA

/** GPDMA Mux definitions */
#define DMAMUX_ADDRESS		0x4004311C

/* Private Functions ----------------------------------------------------------- */
/** @
 * @{
 */
uint8_t DMAMUX_Config(uint32_t gpdma_peripheral_connection_number);
/**
 * @}
 */

/* Private Variables ---------------------------------------------------------- */
/** @defgroup GPDMA_Private_Variables GPDMA Private Variables
 * @{
 */

/**
 * @brief Lookup Table of Connection Type matched with
 * Peripheral Data (FIFO) register base address
 */
#ifdef __ICCARM__
volatile const void *GPDMA_LUTPerAddr[] = {
		(&LPC_SPIFI->DAT),			// SPIFI
		(&LPC_TIMER0->MR),				// MAT0.0
		(&LPC_USART0->/*RBTHDLR.*/THR),	// UART0 Tx
		((uint32_t*)&LPC_TIMER0->MR + 1),				// MAT0.1
		(&LPC_USART0->/*RBTHDLR.*/RBR),	// UART0 Rx
		(&LPC_TIMER1->MR),				// MAT1.0
		(&LPC_UART1->/*RBTHDLR.*/THR),	// UART1 Tx
		((uint32_t*)&LPC_TIMER1->MR + 1),				// MAT1.1
		(&LPC_UART1->/*RBTHDLR.*/RBR),	// UART1 Rx
		(&LPC_TIMER2->MR),				// MAT2.0
		(&LPC_USART2->/*RBTHDLR.*/THR),	// UART2 Tx
		((uint32_t*)&LPC_TIMER2->MR + 1),				// MAT2.1
		(&LPC_USART2->/*RBTHDLR.*/RBR),	// UART2 Rx
		(&LPC_TIMER3->MR),				// MAT3.0
		(&LPC_USART3->/*RBTHDLR.*/THR),	// UART3 Tx
		0,	// to be defined: SCT DMA request 0
		((uint32_t*)&LPC_TIMER3->MR + 1),				// MAT3.1
		(&LPC_USART3->/*RBTHDLR.*/RBR),	// UART3 Rx
		0,	// to be defined: SCT DMA request 1
		(&LPC_SSP0->DR),				// SSP0 Rx
		(&LPC_I2S0->TXFIFO),			// I2S channel 0
		(&LPC_SSP0->DR),				// SSP0 Tx
		(&LPC_I2S0->RXFIFO),			// I2S channel 1
		(&LPC_SSP1->DR),				// SSP1 Rx
		(&LPC_SSP1->DR),				// SSP1 Tx
		(&LPC_ADC0->GDR),				// ADC 0
		(&LPC_ADC1->GDR),				// ADC 1
		(&LPC_DAC->CR)				// DAC
};
#else
const uint32_t GPDMA_LUTPerAddr[] = {
//		((uint32_t)&LPC_SPIFI->DAT),			// SPIFI
		((uint32_t)0),			// SPIFI
		((uint32_t)&LPC_TIMER0->MR[0]),				// MAT0.0
		((uint32_t)&LPC_USART0->/*RBTHDLR.*/THR),	// UART0 Tx
		((uint32_t)&LPC_TIMER0->MR[1]),				// MAT0.1
		((uint32_t)&LPC_USART0->/*RBTHDLR.*/RBR),	// UART0 Rx
		((uint32_t)&LPC_TIMER1->MR[0]),				// MAT1.0
		((uint32_t)&LPC_UART1->/*RBTHDLR.*/THR),	// UART1 Tx
		((uint32_t)&LPC_TIMER1->MR[1]),				// MAT1.1
		((uint32_t)&LPC_UART1->/*RBTHDLR.*/RBR),	// UART1 Rx
		((uint32_t)&LPC_TIMER2->MR[0]),				// MAT2.0
		((uint32_t)&LPC_USART2->/*RBTHDLR.*/THR),	// UART2 Tx
		((uint32_t)&LPC_TIMER2->MR[1]),				// MAT2.1
		((uint32_t)&LPC_USART2->/*RBTHDLR.*/RBR),	// UART2 Rx
		((uint32_t)&LPC_TIMER3->MR[0]),				// MAT3.0
		((uint32_t)&LPC_USART3->/*RBTHDLR.*/THR),	// UART3 Tx
		0,	// to be defined: SCT DMA request 0
		((uint32_t)&LPC_TIMER3->MR[1]),				// MAT3.1
		((uint32_t)&LPC_USART3->/*RBTHDLR.*/RBR),	// UART3 Rx
		0,	// to be defined: SCT DMA request 1
		((uint32_t)&LPC_SSP0->DR),				// SSP0 Rx
		((uint32_t)&LPC_I2S0->TXFIFO),			// I2S channel 0
		((uint32_t)&LPC_SSP0->DR),				// SSP0 Tx
		((uint32_t)&LPC_I2S0->RXFIFO),			// I2S channel 1
		((uint32_t)&LPC_SSP1->DR),				// SSP1 Rx
		((uint32_t)&LPC_SSP1->DR),				// SSP1 Tx
		((uint32_t)&LPC_ADC0->GDR),				// ADC 0
		((uint32_t)&LPC_ADC1->GDR),				// ADC 1
		((uint32_t)&LPC_DAC->CR)				// DAC
};
#endif
/**
 * @brief Lookup Table of GPDMA Channel Number matched with
 * GPDMA channel pointer
 */
const LPC_GPDMACH_TypeDef *pGPDMACh[8] = {
		LPC_GPDMACH0,	// GPDMA Channel 0
		LPC_GPDMACH1,	// GPDMA Channel 1
		LPC_GPDMACH2,	// GPDMA Channel 2
		LPC_GPDMACH3,	// GPDMA Channel 3
		LPC_GPDMACH4,	// GPDMA Channel 4
		LPC_GPDMACH5,	// GPDMA Channel 5
		LPC_GPDMACH6,	// GPDMA Channel 6
		LPC_GPDMACH7,	// GPDMA Channel 7
};
/**
 * @brief Optimized Peripheral Source and Destination burst size
 */
const uint8_t GPDMA_LUTPerBurst[] = {
		GPDMA_BSIZE_4,				// SPIFI
		GPDMA_BSIZE_1,				// MAT0.0
		GPDMA_BSIZE_1,				// UART0 Tx
		GPDMA_BSIZE_1,				// MAT0.1
		GPDMA_BSIZE_1,				// UART0 Rx
		GPDMA_BSIZE_1,				// MAT1.0
		GPDMA_BSIZE_1,				// UART1 Tx
		GPDMA_BSIZE_1,				// MAT1.1
		GPDMA_BSIZE_1,				// UART1 Rx
		GPDMA_BSIZE_1,				// MAT2.0
		GPDMA_BSIZE_1,				// UART2 Tx
		GPDMA_BSIZE_1,				// MAT2.1
		GPDMA_BSIZE_1,				// UART2 Rx
		GPDMA_BSIZE_1,				// MAT3.0
		GPDMA_BSIZE_1,				// UART3 Tx
		0,	// to be defined: SCT DMA request 0
		GPDMA_BSIZE_1,				// MAT3.1
		GPDMA_BSIZE_1,				// UART3 Rx
		0,	// to be defined: SCT DMA request 1
		GPDMA_BSIZE_4,				// SSP0 Rx
		GPDMA_BSIZE_32,				// I2S channel 0
		GPDMA_BSIZE_4,				// SSP0 Tx
		GPDMA_BSIZE_32,				// I2S channel 1
		GPDMA_BSIZE_4,				// SSP1 Rx
		GPDMA_BSIZE_4,				// SSP1 Tx
		GPDMA_BSIZE_4,				// ADC 0
		GPDMA_BSIZE_4,				// ADC 1
		GPDMA_BSIZE_1,				// DAC
};
/**
 * @brief Optimized Peripheral Source and Destination transfer width
 */
const uint8_t GPDMA_LUTPerWid[] = {
		GPDMA_WIDTH_WORD,				// SPIFI
		GPDMA_WIDTH_WORD,				// MAT0.0
		GPDMA_WIDTH_BYTE,				// UART0 Tx
		GPDMA_WIDTH_WORD,				// MAT0.1
		GPDMA_WIDTH_BYTE,				// UART0 Rx
		GPDMA_WIDTH_WORD,				// MAT1.0
		GPDMA_WIDTH_BYTE,				// UART1 Tx
		GPDMA_WIDTH_WORD,				// MAT1.1
		GPDMA_WIDTH_BYTE,				// UART1 Rx
		GPDMA_WIDTH_WORD,				// MAT2.0
		GPDMA_WIDTH_BYTE,				// UART2 Tx
		GPDMA_WIDTH_WORD,				// MAT2.1
		GPDMA_WIDTH_BYTE,				// UART2 Rx
		GPDMA_WIDTH_WORD,				// MAT3.0
		GPDMA_WIDTH_BYTE,				// UART3 Tx
		0,	// to be defined: SCT DMA request 0
		GPDMA_WIDTH_WORD,				// MAT3.1
		GPDMA_WIDTH_BYTE,				// UART3 Rx
		0,	// to be defined: SCT DMA request 1
		GPDMA_WIDTH_BYTE,				// SSP0 Rx
		GPDMA_WIDTH_WORD,				// I2S channel 0
		GPDMA_WIDTH_BYTE,				// SSP0 Tx
		GPDMA_WIDTH_WORD,				// I2S channel 1
		GPDMA_WIDTH_BYTE,				// SSP1 Rx
		GPDMA_WIDTH_BYTE,				// SSP1 Tx
		GPDMA_WIDTH_WORD,				// ADC 0
		GPDMA_WIDTH_WORD,				// ADC 1
		GPDMA_WIDTH_WORD,				// DAC
};

/**
 * @}
 */

/* Private Functions ----------------------------------------------------------- */
/** @
 * @{
 */

/********************************************************************//**
 * @brief		Control which set of peripherals is connected to the
 * 				DMA controller
 * @param[in]	gpdma_peripheral_connection_number	GPDMA peripheral
 * 				connection number, should be:
 * 					- GPDMA_CONN_SPIFI			:SPIFI
 * 					- GPDMA_CONN_MAT0_0			:Timer 0, match channel 0
 * 					- GPDMA_CONN_MAT0_1			:Timer 0, match channel 1
 * 					- GPDMA_CONN_MAT1_0			:Timer 1, match channel 0
 * 					- GPDMA_CONN_MAT1_1			:Timer 1, match channel 1
 * 					- GPDMA_CONN_MAT2_0			:Timer 2, match channel 0
 * 					- GPDMA_CONN_MAT2_1			:Timer 2, match channel 1
 * 					- GPDMA_CONN_MAT3_0			:Timer 3, match channel 0
 * 					- GPDMA_CONN_MAT3_1			:Timer 3, match channel 1
 * 					- GPDMA_CONN_UART0_Tx		:USART 0 transmit
 * 					- GPDMA_CONN_UART0_Rx		:USART 0 receive
 * 					- GPDMA_CONN_UART1_Tx		:USART 1 transmit
 * 					- GPDMA_CONN_UART1_Rx		:USART 1 receive
 * 					- GPDMA_CONN_UART2_Tx		:USART 2 transmit
 * 					- GPDMA_CONN_UART2_Rx		:USART 2 receive
 * 					- GPDMA_CONN_UART3_Tx		:USART 3 transmit
 * 					- GPDMA_CONN_UART3_Rx		:USART 3 receive
 * 					- GPDMA_CONN_SCT_0			:SCT output 0
 * 					- GPDMA_CONN_SCT_1			:SCT output 1
 * 					- GPDMA_CONN_I2S_Channel_0	:I2S channel 0
 * 					- GPDMA_CONN_I2S_Channel_1	:I2S channel 1
 * 					- GPDMA_CONN_SSP0_Tx		:SSP0 transmit
 * 					- GPDMA_CONN_SSP0_Rx		:SSP0 receive
 * 					- GPDMA_CONN_SSP1_Tx		:SSP1 transmit
 * 					- GPDMA_CONN_SSP1_Rx		:SSP1 receive
 * 					- GPDMA_CONN_ADC_0			:ADC0
 * 					- GPDMA_CONN_ADC_1			:ADC1
 * 					- GPDMA_CONN_DAC			:DAC
 * @return	channel number, could be in range: 0..16
 *********************************************************************/
uint8_t DMAMUX_Config(uint32_t gpdma_peripheral_connection_number)
{
	uint32_t *dmamux_reg = (uint32_t*)DMAMUX_ADDRESS;
	uint8_t function, channel;

	switch(gpdma_peripheral_connection_number)
	{
		case GPDMA_CONN_SPIFI:  	function = 0; channel = 0; break;
		case GPDMA_CONN_MAT0_0: 	function = 0; channel = 1; break;
		case GPDMA_CONN_UART0_Tx:	function = 1; channel = 1; break;
		case GPDMA_CONN_MAT0_1:		function = 0; channel = 2; break;
		case GPDMA_CONN_UART0_Rx:	function = 1; channel = 2; break;
		case GPDMA_CONN_MAT1_0:		function = 0; channel = 3; break;
		case GPDMA_CONN_UART1_Tx:	function = 1; channel = 3; break;
		case GPDMA_CONN_MAT1_1:		function = 0; channel = 4; break;
		case GPDMA_CONN_UART1_Rx:	function = 1; channel = 4; break;
		case GPDMA_CONN_MAT2_0:		function = 0; channel = 5; break;
		case GPDMA_CONN_UART2_Tx:	function = 1; channel = 5; break;
		case GPDMA_CONN_MAT2_1:		function = 0; channel = 6; break;
		case GPDMA_CONN_UART2_Rx:	function = 1; channel = 6; break;
		case GPDMA_CONN_MAT3_0:		function = 0; channel = 7; break;
		case GPDMA_CONN_UART3_Tx:	function = 1; channel = 7; break;
		case GPDMA_CONN_SCT_0:		function = 2; channel = 7; break;
		case GPDMA_CONN_MAT3_1:		function = 0; channel = 8; break;
		case GPDMA_CONN_UART3_Rx:	function = 1; channel = 8; break;
		case GPDMA_CONN_SCT_1:		function = 2; channel = 8; break;
		case GPDMA_CONN_SSP0_Rx:	function = 0; channel = 9; break;
		case GPDMA_CONN_I2S_Channel_0:function = 1; channel = 9; break;
		case GPDMA_CONN_SSP0_Tx:	function = 0; channel = 10; break;
		case GPDMA_CONN_I2S_Channel_1:function = 1; channel = 10; break;
		case GPDMA_CONN_SSP1_Rx:	function = 0; channel = 11; break;
		case GPDMA_CONN_SSP1_Tx:	function = 0; channel = 12; break;
		case GPDMA_CONN_ADC_0:		function = 0; channel = 13; break;
		case GPDMA_CONN_ADC_1:		function = 0; channel = 14; break;
		case GPDMA_CONN_DAC:		function = 0; channel = 15; break;
		default:					function = 3; channel = 15; break;
	}
	//Set select function to dmamux register
	*dmamux_reg &= ~(0x03<<(2*channel));
	*dmamux_reg |= (function<<(2*channel));

	return channel;
}
/**
 * @}
 */

/* Public Functions ----------------------------------------------------------- */
/** @addtogroup GPDMA_Public_Functions
 * @{
 */

/********************************************************************//**
 * @brief 		Initialize GPDMA controller
 * @param[in] 	None
 * @return 		None
 *********************************************************************/
void GPDMA_Init(void)
{
	/* to be defined Enable GPDMA clock */
	// enabled default on reset

	// Reset all channel configuration register
	LPC_GPDMACH0->CConfig = 0;
	LPC_GPDMACH1->CConfig = 0;
	LPC_GPDMACH2->CConfig = 0;
	LPC_GPDMACH3->CConfig = 0;
	LPC_GPDMACH4->CConfig = 0;
	LPC_GPDMACH5->CConfig = 0;
	LPC_GPDMACH6->CConfig = 0;
	LPC_GPDMACH7->CConfig = 0;

	/* Clear all DMA interrupt and error flag */
	LPC_GPDMA->INTTCCLEAR = 0xFF;
	LPC_GPDMA->INTERRCLR = 0xFF;
}

/********************************************************************//**
 * @brief 		Setup GPDMA channel peripheral according to the specified
 *              parameters in the GPDMAChannelConfig.
 * @param[in]	GPDMAChannelConfig Pointer to a GPDMA_CH_CFG_Type structure
 * 				that contains the configuration information for the specified
 * 				GPDMA channel peripheral.
 * @return		Setup status, could be:
 * 					- ERROR		:if selected channel is enabled before
 * 					- SUCCESS 	:if channel is configured successfully
 *********************************************************************/
Status GPDMA_Setup(GPDMA_Channel_CFG_Type *GPDMAChannelConfig)
{
	LPC_GPDMACH_TypeDef *pDMAch;
	uint8_t SrcPeripheral=0, DestPeripheral=0;

	if (LPC_GPDMA->ENBLDCHNS & (GPDMA_DMACEnbldChns_Ch(GPDMAChannelConfig->ChannelNum))) {
		// This channel is enabled, return ERROR, need to release this channel first
		return ERROR;
	}

	// Get Channel pointer
	pDMAch = (LPC_GPDMACH_TypeDef *) pGPDMACh[GPDMAChannelConfig->ChannelNum];

	// Reset the Interrupt status
	LPC_GPDMA->INTTCCLEAR = GPDMA_DMACIntTCClear_Ch(GPDMAChannelConfig->ChannelNum);
	LPC_GPDMA->INTERRCLR = GPDMA_DMACIntErrClr_Ch(GPDMAChannelConfig->ChannelNum);

	// Clear DMA configure
	pDMAch->CControl = 0x00;
	pDMAch->CConfig = 0x00;

	/* Assign Linker List Item value */
	pDMAch->CLLI = GPDMAChannelConfig->DMALLI;

	/* Set value to Channel Control Registers */
	switch (GPDMAChannelConfig->TransferType)
	{
	// Memory to memory
	case GPDMA_TRANSFERTYPE_M2M_CONTROLLER_DMA:
		// Assign physical source and destination address
		pDMAch->CSrcAddr = GPDMAChannelConfig->SrcMemAddr;
		pDMAch->CDestAddr = GPDMAChannelConfig->DstMemAddr;
		pDMAch->CControl
				= GPDMA_DMACCxControl_TransferSize(GPDMAChannelConfig->TransferSize) \
						| GPDMA_DMACCxControl_SBSize(GPDMA_BSIZE_32) \
						| GPDMA_DMACCxControl_DBSize(GPDMA_BSIZE_32) \
						| GPDMA_DMACCxControl_SWidth(GPDMAChannelConfig->TransferWidth) \
						| GPDMA_DMACCxControl_DWidth(GPDMAChannelConfig->TransferWidth) \
						| GPDMA_DMACCxControl_SI \
						| GPDMA_DMACCxControl_DI \
						| GPDMA_DMACCxControl_I;
		break;
	// Memory to peripheral
	case GPDMA_TRANSFERTYPE_M2P_CONTROLLER_DMA:
		// Assign physical source
		pDMAch->CSrcAddr = GPDMAChannelConfig->SrcMemAddr;
		// Assign peripheral destination address
		pDMAch->CDestAddr = (uint32_t)GPDMA_LUTPerAddr[GPDMAChannelConfig->DstConn];
		pDMAch->CControl
				= GPDMA_DMACCxControl_TransferSize((uint32_t)GPDMAChannelConfig->TransferSize) \
						| GPDMA_DMACCxControl_SBSize((uint32_t)GPDMA_LUTPerBurst[GPDMAChannelConfig->DstConn]) \
						| GPDMA_DMACCxControl_DBSize((uint32_t)GPDMA_LUTPerBurst[GPDMAChannelConfig->DstConn]) \
						| GPDMA_DMACCxControl_SWidth((uint32_t)GPDMA_LUTPerWid[GPDMAChannelConfig->DstConn]) \
						| GPDMA_DMACCxControl_DWidth((uint32_t)GPDMA_LUTPerWid[GPDMAChannelConfig->DstConn]) \
						| GPDMA_DMACCxControl_DestTransUseAHBMaster1 \
						| GPDMA_DMACCxControl_SI \
						| GPDMA_DMACCxControl_I;
		DestPeripheral = DMAMUX_Config(GPDMAChannelConfig->DstConn);
		break;
	// Peripheral to memory
	case GPDMA_TRANSFERTYPE_P2M_CONTROLLER_DMA:
		// Assign peripheral source address
		pDMAch->CSrcAddr = (uint32_t)GPDMA_LUTPerAddr[GPDMAChannelConfig->SrcConn];
		// Assign memory destination address
		pDMAch->CDestAddr = GPDMAChannelConfig->DstMemAddr;
		pDMAch->CControl
				= GPDMA_DMACCxControl_TransferSize((uint32_t)GPDMAChannelConfig->TransferSize) \
						| GPDMA_DMACCxControl_SBSize((uint32_t)GPDMA_LUTPerBurst[GPDMAChannelConfig->SrcConn]) \
						| GPDMA_DMACCxControl_DBSize((uint32_t)GPDMA_LUTPerBurst[GPDMAChannelConfig->SrcConn]) \
						| GPDMA_DMACCxControl_SWidth((uint32_t)GPDMA_LUTPerWid[GPDMAChannelConfig->SrcConn]) \
						| GPDMA_DMACCxControl_DWidth((uint32_t)GPDMA_LUTPerWid[GPDMAChannelConfig->SrcConn]) \
						| GPDMA_DMACCxControl_SrcTransUseAHBMaster1 \
						| GPDMA_DMACCxControl_DI \
						| GPDMA_DMACCxControl_I;
		SrcPeripheral = DMAMUX_Config(GPDMAChannelConfig->SrcConn);
		break;
	// Peripheral to peripheral
	case GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DMA:
		// Assign peripheral source address
		pDMAch->CSrcAddr = (uint32_t)GPDMA_LUTPerAddr[GPDMAChannelConfig->SrcConn];
		// Assign peripheral destination address
		pDMAch->CDestAddr = (uint32_t)GPDMA_LUTPerAddr[GPDMAChannelConfig->DstConn];
		pDMAch->CControl
				= GPDMA_DMACCxControl_TransferSize((uint32_t)GPDMAChannelConfig->TransferSize) \
						| GPDMA_DMACCxControl_SBSize((uint32_t)GPDMA_LUTPerBurst[GPDMAChannelConfig->SrcConn]) \
						| GPDMA_DMACCxControl_DBSize((uint32_t)GPDMA_LUTPerBurst[GPDMAChannelConfig->DstConn]) \
						| GPDMA_DMACCxControl_SWidth((uint32_t)GPDMA_LUTPerWid[GPDMAChannelConfig->SrcConn]) \
						| GPDMA_DMACCxControl_DWidth((uint32_t)GPDMA_LUTPerWid[GPDMAChannelConfig->DstConn]) \
						| GPDMA_DMACCxControl_SrcTransUseAHBMaster1 \
						| GPDMA_DMACCxControl_DestTransUseAHBMaster1 \
						| GPDMA_DMACCxControl_I;
		SrcPeripheral = DMAMUX_Config(GPDMAChannelConfig->SrcConn);
		DestPeripheral = DMAMUX_Config(GPDMAChannelConfig->DstConn);
		break;

	case GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DestPERIPHERAL:
	case GPDMA_TRANSFERTYPE_M2P_CONTROLLER_PERIPHERAL:
	case GPDMA_TRANSFERTYPE_P2M_CONTROLLER_PERIPHERAL:
	case GPDMA_TRANSFERTYPE_P2P_CONTROLLER_SrcPERIPHERAL:
		//to be defined
	// Do not support any more transfer type, return ERROR
	default:
		return ERROR;
	}

	/* Enable DMA channels, little endian */
	LPC_GPDMA->CONFIG = GPDMA_DMACConfig_E;
	while (!(LPC_GPDMA->CONFIG & GPDMA_DMACConfig_E));

	// Configure DMA Channel, enable Error Counter and Terminate counter
	pDMAch->CConfig = GPDMA_DMACCxConfig_IE | GPDMA_DMACCxConfig_ITC /*| GPDMA_DMACCxConfig_E*/ \
		| GPDMA_DMACCxConfig_TransferType((uint32_t)GPDMAChannelConfig->TransferType) \
		| GPDMA_DMACCxConfig_SrcPeripheral(SrcPeripheral) \
		| GPDMA_DMACCxConfig_DestPeripheral(DestPeripheral);

	return SUCCESS;
}


/*********************************************************************//**
 * @brief		Enable/Disable DMA channel
 * @param[in]	channelNum	GPDMA channel, should be in range from 0 to 15
 * @param[in]	NewState	New State of this command, should be:
 * 					- ENABLE.
 * 					- DISABLE.
 * @return		None
 **********************************************************************/
void GPDMA_ChannelCmd(uint8_t channelNum, FunctionalState NewState)
{
	LPC_GPDMACH_TypeDef *pDMAch;

	// Get Channel pointer
	pDMAch = (LPC_GPDMACH_TypeDef *) pGPDMACh[channelNum];

	if (NewState == ENABLE) {
		pDMAch->CConfig |= GPDMA_DMACCxConfig_E;
	} else {
		pDMAch->CConfig &= ~GPDMA_DMACCxConfig_E;
	}
}


/*********************************************************************//**
 * @brief		Check if corresponding channel does have an active interrupt
 * 				request or not
 * @param[in]	type		type of status, should be:
 * 					- GPDMA_STAT_INT		:GPDMA Interrupt Status
 * 					- GPDMA_STAT_INTTC		:GPDMA Interrupt Terminal Count Request Status
 * 					- GPDMA_STAT_INTERR		:GPDMA Interrupt Error Status
 * 					- GPDMA_STAT_RAWINTTC	:GPDMA Raw Interrupt Terminal Count Status
 * 					- GPDMA_STAT_RAWINTERR	:GPDMA Raw Error Interrupt Status
 * 					- GPDMA_STAT_ENABLED_CH	:GPDMA Enabled Channel Status
 * @param[in]	channel		GPDMA channel, should be in range from 0 to 7
 * @return		IntStatus	status of DMA channel interrupt after masking
 * 				Should be:
 * 					- SET	:the corresponding channel has no active interrupt request
 * 					- RESET	:the corresponding channel does have an active interrupt request
 **********************************************************************/
IntStatus GPDMA_IntGetStatus(GPDMA_Status_Type type, uint8_t channel)
{
	CHECK_PARAM(PARAM_GPDMA_STAT(type));
	CHECK_PARAM(PARAM_GPDMA_CHANNEL(channel));

	switch (type)
	{
	case GPDMA_STAT_INT: //check status of DMA channel interrupts
		if (LPC_GPDMA->INTSTAT & (GPDMA_DMACIntStat_Ch(channel)))
			return SET;
		return RESET;
	case GPDMA_STAT_INTTC: // check terminal count interrupt request status for DMA
		if (LPC_GPDMA->INTTCSTAT & GPDMA_DMACIntTCStat_Ch(channel))
			return SET;
		return RESET;
	case GPDMA_STAT_INTERR: //check interrupt status for DMA channels
		if (LPC_GPDMA->INTERRSTAT & GPDMA_DMACIntTCClear_Ch(channel))
			return SET;
		return RESET;
	case GPDMA_STAT_RAWINTTC: //check status of the terminal count interrupt for DMA channels
		if (LPC_GPDMA->RAWINTERRSTAT & GPDMA_DMACRawIntTCStat_Ch(channel))
			return SET;
		return RESET;
	case GPDMA_STAT_RAWINTERR: //check status of the error interrupt for DMA channels
		if (LPC_GPDMA->RAWINTTCSTAT & GPDMA_DMACRawIntErrStat_Ch(channel))
			return SET;
		return RESET;
	default: //check enable status for DMA channels
		if (LPC_GPDMA->ENBLDCHNS & GPDMA_DMACEnbldChns_Ch(channel))
			return SET;
		return RESET;
	}
}

/*********************************************************************//**
 * @brief		Clear one or more interrupt requests on DMA channels
 * @param[in]	type		type of interrupt request, should be:
 * 					- GPDMA_STATCLR_INTTC	:GPDMA Interrupt Terminal Count Request Clear
 * 					- GPDMA_STATCLR_INTERR	:GPDMA Interrupt Error Clear
 * @param[in]	channel		GPDMA channel, should be in range from 0 to 15
 * @return		None
 **********************************************************************/
void GPDMA_ClearIntPending(GPDMA_StateClear_Type type, uint8_t channel)
{
	CHECK_PARAM(PARAM_GPDMA_STATCLR(type));
	CHECK_PARAM(PARAM_GPDMA_CHANNEL(channel));

	if (type == GPDMA_STATCLR_INTTC) // clears the terminal count interrupt request on DMA channel
		LPC_GPDMA->INTTCCLEAR = GPDMA_DMACIntTCClear_Ch(channel);
	else // clear the error interrupt request
		LPC_GPDMA->INTERRCLR = GPDMA_DMACIntErrClr_Ch(channel);
}

/**
 * @}
 */

#endif /* _GPDMA */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */

