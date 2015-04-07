/**********************************************************************
* $Id$		lpc18xx_gpdma.h		2011-06-02
*//**
* @file		lpc18xx_gpdma.h
* @brief	Contains all macro definitions and function prototypes
* 			support for GPDMA firmware library on LPC18xx
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
/** @defgroup GPDMA GPDMA (General Purpose DMA)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_GPDMA_H_
#define LPC18XX_GPDMA_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif

/* Public Macros -------------------------------------------------------------- */
/** @defgroup GPDMA_Public_Macros GPDMA Public Macros
 * @{
 */

/** DMA Connection number definitions */
#define GPDMA_CONN_SPIFI 			((0UL)) 		/**< SPIFI 				*/
#define GPDMA_CONN_MAT0_0 			((1UL)) 		/**< MAT0.0 			*/
#define GPDMA_CONN_UART0_Tx			((2UL)) 		/**< UART0 Tx 			*/
#define GPDMA_CONN_MAT0_1 			((3UL)) 		/**< MAT0.1 			*/
#define GPDMA_CONN_UART0_Rx			((4UL)) 		/**< UART0 Rx 			*/
#define GPDMA_CONN_MAT1_0 			((5UL)) 		/**< MAT1.0 			*/
#define GPDMA_CONN_UART1_Tx			((6UL)) 		/**< UART1 Tx 			*/
#define GPDMA_CONN_MAT1_1   		((7UL)) 		/**< MAT1.1 			*/
#define GPDMA_CONN_UART1_Rx			((8UL)) 		/**< UART1 Rx 			*/
#define GPDMA_CONN_MAT2_0   		((9UL)) 		/**< MAT2.0 			*/
#define GPDMA_CONN_UART2_Tx			((10UL)) 		/**< UART2 Tx 			*/
#define GPDMA_CONN_MAT2_1   		((11UL)) 		/**< MAT2.1 			*/
#define GPDMA_CONN_UART2_Rx			((12UL)) 		/**< UART2 Rx 			*/
#define GPDMA_CONN_MAT3_0 			((13UL)) 		/**< MAT3.0 			*/
#define GPDMA_CONN_UART3_Tx			((14UL)) 		/**< UART3 Tx 			*/
#define GPDMA_CONN_SCT_0			((15UL)) 		/**< SCT timer channel 0*/
#define GPDMA_CONN_MAT3_1   		((16UL)) 		/**< MAT3.1 			*/
#define GPDMA_CONN_UART3_Rx			((17UL)) 		/**< UART3 Rx 			*/
#define GPDMA_CONN_SCT_1			((18UL)) 		/**< SCT timer channel 1*/
#define GPDMA_CONN_SSP0_Rx 			((19UL)) 		/**< SSP0 Rx 			*/
#define GPDMA_CONN_I2S_Channel_0 	((20UL)) 		/**< I2S channel 0 		*/
#define GPDMA_CONN_SSP0_Tx 			((21UL)) 		/**< SSP0 Tx 			*/
#define GPDMA_CONN_I2S_Channel_1 	((22UL)) 		/**< I2S channel 1		*/
#define GPDMA_CONN_SSP1_Rx 			((23UL)) 		/**< SSP1 Rx 			*/
#define GPDMA_CONN_SSP1_Tx 			((24UL)) 		/**< SSP1 Tx 			*/
#define GPDMA_CONN_ADC_0			((25UL)) 		/**< ADC 0 				*/
#define GPDMA_CONN_ADC_1			((26UL)) 		/**< ADC 1 				*/
#define GPDMA_CONN_DAC 				((27UL)) 		/**< DAC 				*/

/** GPDMA Transfer type definitions */
#define GPDMA_TRANSFERTYPE_M2M_CONTROLLER_DMA 				((0UL)) 	/**< Memory to memory - DMA control */
#define GPDMA_TRANSFERTYPE_M2P_CONTROLLER_DMA 				((1UL)) 	/**< Memory to peripheral - DMA control */
#define GPDMA_TRANSFERTYPE_P2M_CONTROLLER_DMA 				((2UL)) 	/**< Peripheral to memory - DMA control */
#define GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DMA 				((3UL)) 	/**< Source peripheral to destination peripheral - DMA control */
#define GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DestPERIPHERAL 	((4UL)) 	/**< Source peripheral to destination peripheral - destination peripheral control */
#define GPDMA_TRANSFERTYPE_M2P_CONTROLLER_PERIPHERAL 		((5UL)) 	/**< Memory to peripheral - peripheral control */
#define GPDMA_TRANSFERTYPE_P2M_CONTROLLER_PERIPHERAL 		((6UL)) 	/**< Peripheral to memory - peripheral control */
#define GPDMA_TRANSFERTYPE_P2P_CONTROLLER_SrcPERIPHERAL		((7UL)) 	/**< Source peripheral to destination peripheral - source peripheral control */

/** Burst size in Source and Destination definitions */
#define GPDMA_BSIZE_1 	((0UL)) /**< Burst size = 1 */
#define GPDMA_BSIZE_4 	((1UL)) /**< Burst size = 4 */
#define GPDMA_BSIZE_8 	((2UL)) /**< Burst size = 8 */
#define GPDMA_BSIZE_16 	((3UL)) /**< Burst size = 16 */
#define GPDMA_BSIZE_32 	((4UL)) /**< Burst size = 32 */
#define GPDMA_BSIZE_64 	((5UL)) /**< Burst size = 64 */
#define GPDMA_BSIZE_128 ((6UL)) /**< Burst size = 128 */
#define GPDMA_BSIZE_256 ((7UL)) /**< Burst size = 256 */

/** Width in Source transfer width and Destination transfer width definitions */
#define GPDMA_WIDTH_BYTE 		((0UL)) /**< Width = 1 byte */
#define GPDMA_WIDTH_HALFWORD 	((1UL)) /**< Width = 2 bytes */
#define GPDMA_WIDTH_WORD 		((2UL)) /**< Width = 4 bytes */

/** LPC_GPDMA base addresses 	*/
#define LPC_GPDMACH0_BASE	0x40002100
#define LPC_GPDMACH1_BASE	0x40002120
#define LPC_GPDMACH2_BASE	0x40002140
#define LPC_GPDMACH3_BASE	0x40002160
#define LPC_GPDMACH4_BASE	0x40002180
#define LPC_GPDMACH5_BASE	0x400021A0
#define LPC_GPDMACH6_BASE	0x400021C0
#define LPC_GPDMACH7_BASE	0x400021E0

/* LPC_GPDMA channels definitions 	*/
#define LPC_GPDMACH0          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH0_BASE )
#define LPC_GPDMACH1          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH1_BASE )
#define LPC_GPDMACH2          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH2_BASE )
#define LPC_GPDMACH3          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH3_BASE )
#define LPC_GPDMACH4          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH4_BASE )
#define LPC_GPDMACH5          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH5_BASE )
#define LPC_GPDMACH6          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH6_BASE )
#define LPC_GPDMACH7          ((LPC_GPDMACH_TypeDef   *) LPC_GPDMACH7_BASE )
/**
 * @}
 */


/* Private Macros ------------------------------------------------------------- */
/** @defgroup GPDMA_Private_Macros GPDMA Private Macros
 * @{
 */

/* --------------------- BIT DEFINITIONS -------------------------------------- */
/*********************************************************************//**
 * Macro defines for DMA Interrupt Status register
 **********************************************************************/
#define GPDMA_DMACIntStat_Ch(n)			(((1UL<<n)&0xFF))
#define GPDMA_DMACIntStat_BITMASK		((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Interrupt Terminal Count Request Status register
 **********************************************************************/
#define GPDMA_DMACIntTCStat_Ch(n)		(((1UL<<n)&0xFF))
#define GPDMA_DMACIntTCStat_BITMASK		((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Interrupt Terminal Count Request Clear register
 **********************************************************************/
#define GPDMA_DMACIntTCClear_Ch(n)		(((1UL<<n)&0xFF))
#define GPDMA_DMACIntTCClear_BITMASK	((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Interrupt Error Status register
 **********************************************************************/
#define GPDMA_DMACIntErrStat_Ch(n)		(((1UL<<n)&0xFF))
#define GPDMA_DMACIntErrStat_BITMASK	((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Interrupt Error Clear register
 **********************************************************************/
#define GPDMA_DMACIntErrClr_Ch(n)		(((1UL<<n)&0xFF))
#define GPDMA_DMACIntErrClr_BITMASK		((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Raw Interrupt Terminal Count Status register
 **********************************************************************/
#define GPDMA_DMACRawIntTCStat_Ch(n)	(((1UL<<n)&0xFF))
#define GPDMA_DMACRawIntTCStat_BITMASK	((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Raw Error Interrupt Status register
 **********************************************************************/
#define GPDMA_DMACRawIntErrStat_Ch(n)	(((1UL<<n)&0xFF))
#define GPDMA_DMACRawIntErrStat_BITMASK	((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Enabled Channel register
 **********************************************************************/
#define GPDMA_DMACEnbldChns_Ch(n)		(((1UL<<n)&0xFF))
#define GPDMA_DMACEnbldChns_BITMASK		((0xFF))

/*********************************************************************//**
 * Macro defines for DMA Software Burst Request register
 **********************************************************************/
#define	GPDMA_DMACSoftBReq_Src(n)		(((1UL<<n)&0xFFFF))
#define GPDMA_DMACSoftBReq_BITMASK		((0xFFFF))

/*********************************************************************//**
 * Macro defines for DMA Software Single Request register
 **********************************************************************/
#define GPDMA_DMACSoftSReq_Src(n) 		(((1UL<<n)&0xFFFF))
#define GPDMA_DMACSoftSReq_BITMASK		((0xFFFF))

/*********************************************************************//**
 * Macro defines for DMA Software Last Burst Request register
 **********************************************************************/
#define GPDMA_DMACSoftLBReq_Src(n)		(((1UL<<n)&0xFFFF))
#define GPDMA_DMACSoftLBReq_BITMASK		((0xFFFF))

/*********************************************************************//**
 * Macro defines for DMA Software Last Single Request register
 **********************************************************************/
#define GPDMA_DMACSoftLSReq_Src(n) 		(((1UL<<n)&0xFFFF))
#define GPDMA_DMACSoftLSReq_BITMASK		((0xFFFF))

/*********************************************************************//**
 * Macro defines for DMA Configuration register
 **********************************************************************/
#define GPDMA_DMACConfig_E				((0x01))	 /**< DMA Controller enable*/
#define GPDMA_DMACConfig_M0				((0x02))	 /**< AHB Master 0 endianness configuration*/
#define GPDMA_DMACConfig_M1				((0x04))	 /**< AHB Master 1 endianness configuration*/
#define GPDMA_DMACConfig_BITMASK		((0x07))

/*********************************************************************//**
 * Macro defines for DMA Synchronization register
 **********************************************************************/
#define GPDMA_DMACSync_Src(n)			(((1UL<<n)&0xFFFF))
#define GPDMA_DMACSync_BITMASK			((0xFFFF))

/*********************************************************************//**
 * Macro defines for DMA Channel Linked List Item registers
 **********************************************************************/
/** DMA Channel Linked List Item registers bit mask*/
#define GPDMA_DMACCxLLI_BITMASK 		((0xFFFFFFFC))

/*********************************************************************//**
 * Macro defines for DMA channel control registers
 **********************************************************************/
#define GPDMA_DMACCxControl_TransferSize(n) (((n&0xFFF)<<0)) 	/**< Transfer size*/
#define GPDMA_DMACCxControl_SBSize(n)		(((n&0x07)<<12)) 	/**< Source burst size*/
#define GPDMA_DMACCxControl_DBSize(n)		(((n&0x07)<<15)) 	/**< Destination burst size*/
#define GPDMA_DMACCxControl_SWidth(n)		(((n&0x07)<<18)) 	/**< Source transfer width*/
#define GPDMA_DMACCxControl_DWidth(n)		(((n&0x07)<<21)) 	/**< Destination transfer width*/
#define GPDMA_DMACCxControl_SrcTransUseAHBMaster1	((1UL<<24)) /**< Source AHB master select*/
#define GPDMA_DMACCxControl_DestTransUseAHBMaster1	((1UL<<25)) /**< Destination AHB master select*/
#define GPDMA_DMACCxControl_SI				((1UL<<26)) 		/**< Source increment*/
#define GPDMA_DMACCxControl_DI				((1UL<<27)) 		/**< Destination increment*/
#define GPDMA_DMACCxControl_Prot1			((1UL<<28)) 		/**< Indicates that the access is in user mode or privileged mode*/
#define GPDMA_DMACCxControl_Prot2			((1UL<<29)) 		/**< Indicates that the access is bufferable or not bufferable*/
#define GPDMA_DMACCxControl_Prot3			((1UL<<30)) 		/**< Indicates that the access is cacheable or not cacheable*/
#define GPDMA_DMACCxControl_I				((1UL<<31)) 		/**< Terminal count interrupt enable bit */
/** DMA channel control registers bit mask */
#define GPDMA_DMACCxControl_BITMASK			((0xFCFFFFFF))

/*********************************************************************//**
 * Macro defines for DMA Channel Configuration registers
 **********************************************************************/
#define GPDMA_DMACCxConfig_E 					((1UL<<0))			/**< DMA control enable*/
#define GPDMA_DMACCxConfig_SrcPeripheral(n) 	(((n&0x1F)<<1)) 	/**< Source peripheral*/
#define GPDMA_DMACCxConfig_DestPeripheral(n) 	(((n&0x1F)<<6)) 	/**< Destination peripheral*/
#define GPDMA_DMACCxConfig_TransferType(n) 		(((n&0x7)<<11)) 	/**< This value indicates the type of transfer*/
#define GPDMA_DMACCxConfig_IE 					((1UL<<14))			/**< Interrupt error mask*/
#define GPDMA_DMACCxConfig_ITC 					((1UL<<15)) 		/**< Terminal count interrupt mask*/
#define GPDMA_DMACCxConfig_L 					((1UL<<16)) 		/**< Lock*/
#define GPDMA_DMACCxConfig_A 					((1UL<<17)) 		/**< Active*/
#define GPDMA_DMACCxConfig_H 					((1UL<<18)) 		/**< Halt*/
/** DMA Channel Configuration registers bit mask */
#define GPDMA_DMACCxConfig_BITMASK				((0x7FFFF))

/* ---------------- CHECK PARAMETER DEFINITIONS ---------------------------- */
/* Macros check GPDMA channel */
#define PARAM_GPDMA_CHANNEL(n)	(n<=7)

/* Macros check GPDMA connection type */
#define PARAM_GPDMA_CONN(n)		((n==GPDMA_CONN_SPIFI) || (n==GPDMA_CONN_DAC) \
|| (n==GPDMA_CONN_SSP0_Tx) || (n==GPDMA_CONN_SSP0_Rx) \
|| (n==GPDMA_CONN_SSP1_Tx) || (n==GPDMA_CONN_SSP1_Rx) \
|| (n==GPDMA_CONN_ADC_0)   || (n==GPDMA_CONN_ADC_1) \
|| (n==GPDMA_CONN_I2S_Channel_0) || (n==GPDMA_CONN_I2S_Channel_1) \
|| (n==GPDMA_CONN_SCT_0)   || (n==GPDMA_CONN_SCT_1) \
|| (n==GPDMA_CONN_UART0_Tx) || (n==GPDMA_CONN_UART0_Rx) \
|| (n==GPDMA_CONN_UART1_Tx) || (n==GPDMA_CONN_UART1_Rx) \
|| (n==GPDMA_CONN_UART2_Tx) || (n==GPDMA_CONN_UART2_Rx) \
|| (n==GPDMA_CONN_UART3_Tx) || (n==GPDMA_CONN_UART3_Rx) \
|| (n==GPDMA_CONN_MAT0_0) || (n==GPDMA_CONN_MAT0_1) \
|| (n==GPDMA_CONN_MAT1_0) || (n==GPDMA_CONN_MAT1_1) \
|| (n==GPDMA_CONN_MAT2_0) || (n==GPDMA_CONN_MAT2_1) \
|| (n==GPDMA_CONN_MAT3_0) || (n==GPDMA_CONN_MAT3_1))

/* Macros check GPDMA burst size type */
#define PARAM_GPDMA_BSIZE(n)	((n==GPDMA_BSIZE_1) || (n==GPDMA_BSIZE_4) \
|| (n==GPDMA_BSIZE_8) || (n==GPDMA_BSIZE_16) \
|| (n==GPDMA_BSIZE_32) || (n==GPDMA_BSIZE_64) \
|| (n==GPDMA_BSIZE_128) || (n==GPDMA_BSIZE_256))

/* Macros check GPDMA width type */
#define PARAM_GPDMA_WIDTH(n) ((n==GPDMA_WIDTH_BYTE) || (n==GPDMA_WIDTH_HALFWORD) \
|| (n==GPDMA_WIDTH_WORD))

/* Macros check GPDMA status type */
#define PARAM_GPDMA_STAT(n)	((n==GPDMA_STAT_INT) || (n==GPDMA_STAT_INTTC) \
|| (n==GPDMA_STAT_INTERR) || (n==GPDMA_STAT_RAWINTTC) \
|| (n==GPDMA_STAT_RAWINTERR) || (n==GPDMA_STAT_ENABLED_CH))

/* Macros check GPDMA transfer type */
#define PARAM_GPDMA_TRANSFERTYPE(n) ((n==GPDMA_TRANSFERTYPE_M2M_CONTROLLER_DMA)||(n==GPDMA_TRANSFERTYPE_M2P_CONTROLLER_DMA) \
||(n==GPDMA_TRANSFERTYPE_P2M_CONTROLLER_DMA)||(n==GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DMA)\
||(n==GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DestPERIPHERAL)||(n==GPDMA_TRANSFERTYPE_M2P_CONTROLLER_PERIPHERAL)\
||(n==GPDMA_TRANSFERTYPE_P2M_CONTROLLER_PERIPHERAL)||(n==GPDMA_TRANSFERTYPE_P2P_CONTROLLER_SrcPERIPHERAL))

/* Macros check GPDMA state clear type */
#define PARAM_GPDMA_STATCLR(n)	((n==GPDMA_STATCLR_INTTC) || (n==GPDMA_STATCLR_INTERR))

/**
 * @}
 */


/* Public Types --------------------------------------------------------------- */
/** @defgroup GPDMA_Public_Types GPDMA Public Types
 * @{
 */

/**
 * @brief GPDMA Channel Registers
 */
typedef struct
{
  __IO uint32_t CSrcAddr;
  __IO uint32_t CDestAddr;
  __IO uint32_t CLLI;
  __IO uint32_t CControl;
  __IO uint32_t CConfig;
} LPC_GPDMACH_TypeDef;

/**
 * @brief GPDMA Status enumeration
 */
typedef enum {
	GPDMA_STAT_INT,			/**< GPDMA Interrupt Status */
	GPDMA_STAT_INTTC,		/**< GPDMA Interrupt Terminal Count Request Status */
	GPDMA_STAT_INTERR,		/**< GPDMA Interrupt Error Status */
	GPDMA_STAT_RAWINTTC,	/**< GPDMA Raw Interrupt Terminal Count Status */
	GPDMA_STAT_RAWINTERR,	/**< GPDMA Raw Error Interrupt Status */
	GPDMA_STAT_ENABLED_CH	/**< GPDMA Enabled Channel Status */
} GPDMA_Status_Type;

/**
 * @brief GPDMA Interrupt clear status enumeration
 */
typedef enum{
	GPDMA_STATCLR_INTTC,	/**< GPDMA Interrupt Terminal Count Request Clear */
	GPDMA_STATCLR_INTERR	/**< GPDMA Interrupt Error Clear */
}GPDMA_StateClear_Type;

/**
 * @brief GPDMA Channel configuration structure type definition
 */
typedef struct {
	uint32_t ChannelNum; 	/**< DMA channel number, should be in
								range from 0 to 7.
								Note: DMA channel 0 has the highest priority
								and DMA channel 7 the lowest priority.
								*/
	uint32_t TransferSize;	/**< Length/Size of transfer */
	uint32_t TransferWidth;	/**< Transfer width - used for TransferType is GPDMA_TRANSFERTYPE_M2M only */
	uint32_t SrcMemAddr;	/**< Physical Source Address, used in case TransferType is chosen as
								 GPDMA_TRANSFERTYPE_M2M or GPDMA_TRANSFERTYPE_M2P */
	uint32_t DstMemAddr;	/**< Physical Destination Address, used in case TransferType is chosen as
								 GPDMA_TRANSFERTYPE_M2M or GPDMA_TRANSFERTYPE_P2M */
	uint32_t TransferType;	/**< Transfer Type, should be one of the following:
							- GPDMA_TRANSFERTYPE_M2M_CONTROLLER_DMA: Memory to memory - DMA control
							- GPDMA_TRANSFERTYPE_M2P_CONTROLLER_DMA: Memory to peripheral - DMA control
							- GPDMA_TRANSFERTYPE_P2M_CONTROLLER_DMA: Peripheral to memory - DMA control
							- GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DMA: Source peripheral to destination peripheral - DMA control
							- GPDMA_TRANSFERTYPE_P2P_CONTROLLER_DestPERIPHERAL: Source peripheral to destination peripheral - destination peripheral control
							- GPDMA_TRANSFERTYPE_M2P_CONTROLLER_PERIPHERAL: Memory to peripheral - peripheral control
							- GPDMA_TRANSFERTYPE_P2M_CONTROLLER_PERIPHERAL: Peripheral to memory - peripheral control
							- GPDMA_TRANSFERTYPE_P2P_CONTROLLER_SrcPERIPHERAL:	Source peripheral to destination peripheral - source peripheral control
							*/
	uint32_t SrcConn;		/**< Peripheral Source Connection type, used in case TransferType is chosen as
							GPDMA_TRANSFERTYPE_P2M or GPDMA_TRANSFERTYPE_P2P, should be one of
							following:
							 - GPDMA_CONN_SSP0_Tx: SSP0, Tx
							 - GPDMA_CONN_SSP0_Rx: SSP0, Rx
							 - GPDMA_CONN_SSP1_Tx: SSP1, Tx
							 - GPDMA_CONN_SSP1_Rx: SSP1, Rx
							 - GPDMA_CONN_ADC_0: ADC0
							 - GPDMA_CONN_ADC_1: ADC1
							 - GPDMA_CONN_SCT_0: SCT0
							 - GPDMA_CONN_SCT_1: SCT1
							 - GPDMA_CONN_I2S_Channel_0: I2S Channel 0
							 - GPDMA_CONN_I2S_Channel_1: I2S Channel 1
							 - GPDMA_CONN_DAC: DAC
							 - GPDMA_CONN_SPIFI: SPIFI
							 - GPDMA_CONN_UART0_Tx_MAT0_0: UART0 Tx / MAT0.0
							 - GPDMA_CONN_UART0_Rx_MAT0_1: UART0 Rx / MAT0.1
							 - GPDMA_CONN_UART1_Tx_MAT1_0: UART1 Tx / MAT1.0
							 - GPDMA_CONN_UART1_Rx_MAT1_1: UART1 Rx / MAT1.1
							 - GPDMA_CONN_UART2_Tx_MAT2_0: UART2 Tx / MAT2.0
							 - GPDMA_CONN_UART2_Rx_MAT2_1: UART2 Rx / MAT2.1
							 - GPDMA_CONN_UART3_Tx_MAT3_0: UART3 Tx / MAT3.0
							 - GPDMA_CONN_UART3_Rx_MAT3_1: UART3 Rx / MAT3.1
							 */
	uint32_t DstConn;		/**< Peripheral Destination Connection type, used in case TransferType is chosen as
							GPDMA_TRANSFERTYPE_M2P or GPDMA_TRANSFERTYPE_P2P, should be one of
							following:
							 - GPDMA_CONN_SSP0_Tx: SSP0, Tx
							 - GPDMA_CONN_SSP0_Rx: SSP0, Rx
							 - GPDMA_CONN_SSP1_Tx: SSP1, Tx
							 - GPDMA_CONN_SSP1_Rx: SSP1, Rx
							 - GPDMA_CONN_ADC_0: ADC0
							 - GPDMA_CONN_ADC_1: ADC1
							 - GPDMA_CONN_SCT_0: SCT0
							 - GPDMA_CONN_SCT_1: SCT1
							 - GPDMA_CONN_I2S_Channel_0: I2S Channel 0
							 - GPDMA_CONN_I2S_Channel_1: I2S Channel 1
							 - GPDMA_CONN_DAC: DAC
							 - GPDMA_CONN_SPIFI: SPIFI
							 - GPDMA_CONN_UART0_Tx_MAT0_0: UART0 Tx / MAT0.0
							 - GPDMA_CONN_UART0_Rx_MAT0_1: UART0 Rx / MAT0.1
							 - GPDMA_CONN_UART1_Tx_MAT1_0: UART1 Tx / MAT1.0
							 - GPDMA_CONN_UART1_Rx_MAT1_1: UART1 Rx / MAT1.1
							 - GPDMA_CONN_UART2_Tx_MAT2_0: UART2 Tx / MAT2.0
							 - GPDMA_CONN_UART2_Rx_MAT2_1: UART2 Rx / MAT2.1
							 - GPDMA_CONN_UART3_Tx_MAT3_0: UART3 Tx / MAT3.0
							 - GPDMA_CONN_UART3_Rx_MAT3_1: UART3 Rx / MAT3.1
							 */
	uint32_t DMALLI;		/**< Linker List Item structure data address
							if there's no Linker List, set as '0'
							*/
} GPDMA_Channel_CFG_Type;

/**
 * @brief GPDMA Linker List Item structure type definition
 */
typedef struct {
	uint32_t SrcAddr;	/**< Source Address */
	uint32_t DstAddr;	/**< Destination address */
	uint32_t NextLLI;	/**< Next LLI address, otherwise set to '0' */
	uint32_t Control;	/**< GPDMA Control of this LLI */
} GPDMA_LLI_Type;


/**
 * @}
 */

/* Public Functions ----------------------------------------------------------- */
/** @defgroup GPDMA_Public_Functions GPDMA Public Functions
 * @{
 */

void GPDMA_Init(void);

Status GPDMA_Setup(GPDMA_Channel_CFG_Type *GPDMAChannelConfig);
IntStatus GPDMA_IntGetStatus(GPDMA_Status_Type type, uint8_t channel);
void GPDMA_ClearIntPending(GPDMA_StateClear_Type type, uint8_t channel);
void GPDMA_ChannelCmd(uint8_t channelNum, FunctionalState NewState);

/**
 * @}
 */


#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_GPDMA_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
