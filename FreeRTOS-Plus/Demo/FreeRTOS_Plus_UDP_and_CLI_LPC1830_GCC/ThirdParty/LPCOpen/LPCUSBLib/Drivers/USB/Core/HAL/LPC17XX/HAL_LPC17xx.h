/*
 * @brief HAL USB functions for the LPC17xx microcontrollers
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

/** @ingroup Group_HAL_LPC
 *  @defgroup Group_HAL_LPC17xx Hardware Abstraction Layer LPC17XX
 *  @{
 */
#ifndef __HAL_LPC17XX_H__
#define __HAL_LPC17XX_H__

#include "chip.h"

#define  __INCLUDE_FROM_USB_DRIVER
#include "../../USBMode.h"

#define USBRAM_SECTION  RAM2

#if defined(__LPC177X_8X__) || defined(__LPC407X_8X__)
/** This macro is used to declare a variable in a defined section. */
#if defined(__CC_ARM)
	#define __BSS(x)   __attribute__ ((section("usbram")))
#endif
#if defined(__ICCARM__)
	#define __BSS(x)   @ ".sram"
#endif
#else 
#if defined(__CC_ARM) || defined(__ICCARM__)
	#define __BSS(x)
#endif
#endif

#define USB_REG(CoreID)         LPC_USB

/**
 * @brief	Interrupt Handler (Host side).
 * 			This handler is known as interrupt service routine of USB Host.
 *
 * @param	HostID		: Host ID
 * @return	Nothing.
 */
extern void HcdIrqHandler(uint8_t HostID);

#ifdef USB_CAN_BE_DEVICE

/* Device Interrupt Bit Definitions */
#define FRAME_INT           0x00000001
#define EP_FAST_INT         0x00000002
#define EP_SLOW_INT         0x00000004
#define DEV_STAT_INT        0x00000008
#define CCEMTY_INT          0x00000010
#define CDFULL_INT          0x00000020
#define RxENDPKT_INT        0x00000040
#define TxENDPKT_INT        0x00000080
#define EP_RLZED_INT        0x00000100
#define ERR_INT             0x00000200

/* Rx & Tx Packet Length Definitions */
#define PKT_LNGTH_MASK      0x000003FF
#define PKT_DV              0x00000400
#define PKT_RDY             0x00000800

/* USB Control Definitions */
#define CTRL_RD_EN          0x00000001
#define CTRL_WR_EN          0x00000002

/* Command Codes */
#define CMD_SET_ADDR        0x00D00500
#define CMD_CFG_DEV         0x00D80500
#define CMD_SET_MODE        0x00F30500
#define CMD_RD_FRAME        0x00F50500
#define DAT_RD_FRAME        0x00F50200
#define CMD_RD_TEST         0x00FD0500
#define DAT_RD_TEST         0x00FD0200
#define CMD_SET_DEV_STAT    0x00FE0500
#define CMD_GET_DEV_STAT    0x00FE0500
#define DAT_GET_DEV_STAT    0x00FE0200
#define CMD_GET_ERR_CODE    0x00FF0500
#define DAT_GET_ERR_CODE    0x00FF0200
#define CMD_RD_ERR_STAT     0x00FB0500
#define DAT_RD_ERR_STAT     0x00FB0200
#define DAT_WR_BYTE(x)     (0x00000100 | ((x) << 16))
#define CMD_SEL_EP(x)      (0x00000500 | ((x) << 16))
#define DAT_SEL_EP(x)      (0x00000200 | ((x) << 16))
#define CMD_SEL_EP_CLRI(x) (0x00400500 | ((x) << 16))
#define DAT_SEL_EP_CLRI(x) (0x00400200 | ((x) << 16))
#define CMD_SET_EP_STAT(x) (0x00400500 | ((x) << 16))
#define CMD_CLR_BUF         0x00F20500
#define DAT_CLR_BUF         0x00F20200
#define CMD_VALID_BUF       0x00FA0500

/* Device Address Register Definitions */
#define DEV_ADDR_MASK       0x7F
#define DEV_EN              0x80

/* Device Configure Register Definitions */
#define CONF_DVICE          0x01

/* Device Mode Register Definitions */
#define AP_CLK              0x01
#define INAK_CI             0x02
#define INAK_CO             0x04
#define INAK_II             0x08
#define INAK_IO             0x10
#define INAK_BI             0x20
#define INAK_BO             0x40

/* Device Status Register Definitions */
#define DEV_CON             0x01
#define DEV_CON_CH          0x02
#define DEV_SUS             0x04
#define DEV_SUS_CH          0x08
#define DEV_RST             0x10

/* Error Code Register Definitions */
#define ERR_EC_MASK         0x0F
#define ERR_EA              0x10

/* Error Status Register Definitions */
#define ERR_PID             0x01
#define ERR_UEPKT           0x02
#define ERR_DCRC            0x04
#define ERR_TIMOUT          0x08
#define ERR_EOP             0x10
#define ERR_B_OVRN          0x20
#define ERR_BTSTF           0x40
#define ERR_TGL             0x80

/* Endpoint Select Register Definitions */
#define EP_SEL_F            0x01
#define EP_SEL_ST           0x02
#define EP_SEL_STP          0x04
#define EP_SEL_PO           0x08
#define EP_SEL_EPN          0x10
#define EP_SEL_B_1_FULL     0x20
#define EP_SEL_B_2_FULL     0x40

/* Endpoint Status Register Definitions */
#define EP_STAT_ST          0x01
#define EP_STAT_DA          0x20
#define EP_STAT_RF_MO       0x40
#define EP_STAT_CND_ST      0x80

/* Clear Buffer Register Definitions */
#define CLR_BUF_PO          0x01

/* DMA Interrupt Bit Definitions */
#define EOT_INT             0x01
#define NDD_REQ_INT         0x02
#define SYS_ERR_INT         0x04

void HAL_Reset (uint8_t corenum);

/**
 * @brief	Set device address
 * @param	Address		: Address to be set
 * @return	Nothing.
 */
void HAL_SetDeviceAddress (uint8_t Address);

/**
 * @brief	Send connect SIE command
 * @param	con		: connect or disconnect status
 * @return	Nothing.
 */
void HAL17XX_USBConnect (uint32_t con);

/**
 * @brief	Read SIE command data
 * @param	cmd		: command code
 * @return	Data.
 */
uint32_t SIE_ReadCommandData (uint32_t cmd);/* Device_LPC17xx */

/*---------- DMA Descriptor ----------*/
typedef struct {
	/*---------- Word 0 ----------*/
	uint32_t NextDD;

	/*---------- Word 1 ----------*/
	/* 1st half word */
	uint16_t Mode : 2;
	uint16_t NextDDValid : 1;
	uint16_t : 1;
	uint16_t Isochronous : 1;
	uint16_t MaxPacketSize : 11;
	/* 2nd half word */
	__IO uint16_t BufferLength;

	/*---------- Word 2 ----------*/
	__IO uint8_t *BufferStartAddr;

	/*---------- Word 3 ----------*/
	/* 1st half word */
	__IO uint16_t Retired : 1;
	uint16_t Status : 4;
	uint16_t IsoPacketValid : 1;
	uint16_t LSByteExtracted : 1;	/* ATLE mode */
	uint16_t MSByteExtracted : 1;	/* ATLE mode */
	uint16_t MessageLengthPosition : 6;
	uint16_t : 2;
	/* 2st half word */
	uint16_t PresentCount;

	/*---------- Word 4 ----------*/
	uint32_t IsoBufferAddr;		/* Iso transfer exclusive */
} DMADescriptor, *PDMADescriptor;
#endif

#endif	// __HAL_LPC17XX_H__

/**
 * @}
 */
