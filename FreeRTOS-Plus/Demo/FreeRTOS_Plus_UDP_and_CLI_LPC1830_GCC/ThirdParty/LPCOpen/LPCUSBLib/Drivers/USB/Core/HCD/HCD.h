/*
 * @brief Host Controller Driver functions
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

/** @ingroup Group_Host
 *  @defgroup Group_HCD Host Controller Drivers
 *  @{
 */
#ifndef __LPC_HCD_H__
#define __LPC_HCD_H__

#include "../../../../Common/Common.h"
#include "../StdRequestType.h"	// FIXME should be USBTask.h instead
#include "../HAL/HAL.h"
#include <string.h>
#include <stdio.h>

/** Used with \ref HcdDataTransfer() to set maximum endpoint size for transfer length
 */
#define HCD_ENDPOINT_MAXPACKET_XFER_LEN                 0xFFEEFFEE

/** Similar to boolean type
 */
#define YES                                 1

/** Similar to boolean type
 */
#define NO                                  0

/** Maximum number of endpoints/pipes that a single USB host core can support
 */
#define HCD_MAX_ENDPOINT                    8

/** Pre-defined counter value for reseting USB host core
 */
#define HC_RESET_TIMEOUT                    10

/** Pre-defined counter value for transferring
 */
#define TRANSFER_TIMEOUT_MS                 1000

/** Pre-defined counter value for reseting USB port
 */
#define PORT_RESET_PERIOD_MS                100

/* Control / Bulk transfer is always enabled     */
/** Flag to enable processing for interrupt transfer
 *  Select \ref YES to enable or \ref NO if disable
 */
#define INTERRUPT_LIST_ENABLE               YES

/** Flag to enable processing for isochronous transfer
 *  Select \ref YES to enable or \ref NO if disable
 */
#define ISO_LIST_ENABLE                     YES

/** Declare labels for all USB transfer types
 */
typedef enum {
	CONTROL_TRANSFER,
	ISOCHRONOUS_TRANSFER,
	BULK_TRANSFER,
	INTERRUPT_TRANSFER
} HCD_TRANSFER_TYPE;

/** Declare labels for all USB transfer direction
 */
typedef enum {
	SETUP_TRANSFER,
	IN_TRANSFER,
	OUT_TRANSFER
} HCD_TRANSFER_DIR;

/** Declare labels for supported USB transfer speeds
 */
typedef enum {
	FULL_SPEED = 0,
	LOW_SPEED,
	HIGH_SPEED
} HCD_USB_SPEED;

/** Declare status/completion code for host processing
 */
typedef enum {
	HCD_STATUS_OK = 0,						/**< Transfer/process completion normal*/

	HCD_STATUS_TRANSFER_CRC,				/**< Transfer/process completion fail: CRC error */
	HCD_STATUS_TRANSFER_BitStuffing,		/**< Transfer/process completion fail: bit stuffing error */
	HCD_STATUS_TRANSFER_DataToggleMismatch,	/**< Transfer/process completion fail: data toggle error */
	HCD_STATUS_TRANSFER_Stall,				/**< Transfer/process completion fail: endpoint stall */
	HCD_STATUS_TRANSFER_DeviceNotResponding,/**< Transfer/process completion fail: connected device hung or ... */

	HCD_STATUS_TRANSFER_PIDCheckFailure,	/**< Transfer/process completion fail: PID error */
	HCD_STATUS_TRANSFER_UnexpectedPID,		/**< Transfer/process completion fail: PID error */
	HCD_STATUS_TRANSFER_DataOverrun,		/**< Transfer/process completion fail: data over run */
	HCD_STATUS_TRANSFER_DataUnderrun,		/**< Transfer/process completion fail: data under run */
	HCD_STATUS_TRANSFER_CC_Reserved1,		/**< Transfer/process completion fail: Reserved */

	HCD_STATUS_TRANSFER_CC_Reserved2,		/**< Transfer/process completion fail: Reserved */
	HCD_STATUS_TRANSFER_BufferOverrun,		/**< Transfer/process completion fail: buffer over run */
	HCD_STATUS_TRANSFER_BufferUnderrun,		/**< Transfer/process completion fail: buffer under run */
	HCD_STATUS_TRANSFER_NotAccessed,		/**< Transfer/process completion fail: Reserved */
	HCD_STATUS_TRANSFER_Reserved,			/**< Transfer/process completion fail: Reserved */

	HCD_STATUS_STRUCTURE_IS_FREE,			/**< USB transfer status: USB data structure is free to use */
	HCD_STATUS_TO_BE_REMOVED,				/**< USB transfer status: USB data structure need to be freed */
	HCD_STATUS_TRANSFER_QUEUED,				/**< USB transfer status: transfer descriptor has been set up and queued */
	HCD_STATUS_TRANSFER_COMPLETED,			/**< USB transfer status: transfer descriptor finished */
	HCD_STATUS_TRANSFER_ERROR,				/**< USB transfer status: transfer descriptor finished with error */

	HCD_STATUS_NOT_ENOUGH_MEMORY,			/**< USB transfer set up status: not enough memory */
	HCD_STATUS_NOT_ENOUGH_ENDPOINT,			/**< USB transfer set up status: not enough endpoint */
	HCD_STATUS_NOT_ENOUGH_GTD,				/**< USB transfer set up status: not enough general transfer descriptor (OHCI)*/
	HCD_STATUS_NOT_ENOUGH_ITD,				/**< USB transfer set up status: not enough isochronous transfer descriptor */
	HCD_STATUS_NOT_ENOUGH_QTD,				/**< USB transfer set up status: not enough queue transfer descrptor (EHCI) */

	HCD_STATUS_NOT_ENOUGH_HS_ITD,			/**< USB transfer set up status: not enough high speed isochronous trsfer descriptor */
	HCD_STATUS_NOT_ENOUGH_SITD,				/**< USB transfer set up status: not enough split isochronous transfer descriptor */
	HCD_STATUS_DATA_OVERFLOW,				/**< USB transfer set up status: data over flow */
	HCD_STATUS_DEVICE_DISCONNECTED,			/**< USB transfer set up status: device disconnected */
	HCD_STATUS_TRANSFER_TYPE_NOT_SUPPORTED,	/**< USB transfer set up status: transfer is not supported */

	HCD_STATUS_PIPEHANDLE_INVALID,			/**< USB transfer set up status: pipe handle information is not valid */
	HCD_STATUS_PARAMETER_INVALID			/**< USB transfer set up status: wrong supply parameters */
} HCD_STATUS;

/**
 * @brief  Initiate host driver
 *
 * @param  HostID		: USB port number
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdInitDriver (uint8_t HostID);

/**
 * @brief  De-initiate host driver
 *
 * @param  HostID		: USB port number
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdDeInitDriver(uint8_t HostID);

/**
 * @brief  Interrupt service routine for host mode
 * 		   This function must be called in chip's USB interrupt routine
 *
 * @param  HostID		: USB port number
 * @return nothing
 */
void HcdIrqHandler(uint8_t HostID);

/**
 * @brief  Perform USB bus reset
 *
 * @param  HostID		: USB port number
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdRhPortReset(uint8_t HostID);

/**
 * @brief  Turn on 5V USB VBUS
 *
 * @param  HostID		: USB port number
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdRhPortEnable(uint8_t HostID);

/**
 * @brief  Turn off 5V USB VBUS
 *
 * @param  HostID		: USB port number
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdRhPortDisable(uint8_t HostID);

/**
 * @brief  Get operation speed of connected device
 *
 * @param  HostID		: USB port number
 * @param  DeviceSpeed	: return device speed through pointer of type \ref HCD_USB_SPEED
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdGetDeviceSpeed(uint8_t HostID, HCD_USB_SPEED *DeviceSpeed);

/**
 * @brief  Get current frame number
 *
 * @param  HostID		: USB port number
 * @return frame number
 */
uint32_t HcdGetFrameNumber(uint8_t HostID);

/**
 * @brief  Setup a pipe to connect to device's logical endpoint
 *
 * @param  HostID		: USB port number
 * @param  DeviceAddr	: address of connected device
 * @param  DeviceSpeed	: speed of connected device in format \ref HCD_USB_SPEED
 * @param  EndpointNo	: connected logical endpoint number
 * @param  TransferType	: transfer type of this link in format \ref HCD_TRANSFER_TYPE
 * @param  TransferDir	: direction of this link in format \ref HCD_TRANSFER_DIR
 * @param  MaxPacketSize: maximum size of connected endpoint
 * @param  Interval		: polling frequency for this transfer type, only apply for period transfer
 * @param  Mult			: used for isochronous transfer to determine number of packets sent in one transaction
 * @param  HSHubDevAddr	: currently not use this parameter
 * @param  HSHubPortNum	: currently not use this parameter
 * @param  PipeHandle	: pointer to return pipe handle information
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdOpenPipe(uint8_t HostID,
					   uint8_t DeviceAddr,
					   HCD_USB_SPEED DeviceSpeed,
					   uint8_t EndpointNo,
					   HCD_TRANSFER_TYPE TransferType,
					   HCD_TRANSFER_DIR TransferDir,
					   uint16_t MaxPacketSize,
					   uint8_t Interval,
					   uint8_t Mult,
					   uint8_t HSHubDevAddr,
					   uint8_t HSHubPortNum,
					   uint32_t *const PipeHandle);

/**
 * @brief  Delete the link between USB host and device's logical endpoint
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdClosePipe(uint32_t PipeHandle);

/**
 * @brief  Cancel a processing transfer
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdCancelTransfer(uint32_t PipeHandle);

/**
 * @brief  Clear stall status for connected endpoint
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdClearEndpointHalt(uint32_t PipeHandle);

/**
 * @brief  Perform a control transfer
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @param  pDeviceRequest: pointer to \ref USB_Request_Header_t structure
 * @param  buffer		: pointer to share buffer used in data phase
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdControlTransfer(uint32_t PipeHandle,
							  const USB_Request_Header_t *const pDeviceRequest,
							  uint8_t *const buffer);

/**
 * @brief  Perform a non-control transfer
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @param  buffer		: pointer to transferred data buffer
 * @param  length		: size of this transfer
 * @param  pActualTransferred: return actual transfer bytes through pointer
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdDataTransfer(uint32_t PipeHandle,
						   uint8_t *const buffer,
						   uint32_t const length,
						   uint16_t *const pActualTransferred);

/**
 * @brief  Get current pipe status
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @return \ref HCD_STATUS code
 */
HCD_STATUS HcdGetPipeStatus(uint32_t PipeHandle);

/**
 * @brief  Set size of each packet in a continuous data transfer
 *
 * @param  PipeHandle	: encoded pipe handle information
 * @param  packetsize	: packet size
 * @return \ref HCD_STATUS code
 */
void HcdSetStreamPacketSize(uint32_t PipeHandle, uint16_t packetsize);

#ifdef LPCUSBlib_DEBUG
	#define hcd_printf          printf
void assert_status_ok_message(HCD_STATUS status,
							  char const *mess,
							  char const *func,
							  char const *file,
							  uint32_t const line);

#else
	#define hcd_printf(...)
	#define assert_status_ok_message(...)
#endif

#define ASSERT_STATUS_OK_MESSAGE(sts, message) \
	do { \
		HCD_STATUS status = (sts); \
		assert_status_ok_message(status, message, __func__, __FILE__, __LINE__); \
		if (HCD_STATUS_OK != status) { \
			return status; \
		} \
	} while (0)

#define ASSERT_STATUS_OK(sts)       ASSERT_STATUS_OK_MESSAGE(sts, NULL)

#if defined(__LPC_OHCI_C__) || defined(__LPC_EHCI_C__)

void  HcdDelayUS (uint32_t  delay);

void  HcdDelayMS (uint32_t  delay);

/**
 * @brief  Verify if input parameters are supported
 *
 * @param  HostID		: USB port number
 * @param  DeviceAddr	: address of connected device
 * @param  DeviceSpeed	: speed of connected device in format \ref HCD_USB_SPEED
 * @param  EndpointNumber: connected logical endpoint number
 * @param  TransferType	: transfer type of this link in format \ref HCD_TRANSFER_TYPE
 * @param  TransferDir	: direction of this link in format \ref HCD_TRANSFER_DIR
 * @param  MaxPacketSize: maximum size of connected endpoint
 * @param  Interval		: polling frequency for this transfer type, only apply for period transfer
 * @param  Mult			: used for isochronous transfer to determine number of packets sent in one transaction
 * @return \ref HCD_STATUS code
 */
HCD_STATUS OpenPipe_VerifyParameters(uint8_t HostID,
									 uint8_t DeviceAddr,
									 HCD_USB_SPEED DeviceSpeed,
									 uint8_t EndpointNumber,
									 HCD_TRANSFER_TYPE TransferType,
									 HCD_TRANSFER_DIR TransferDir,
									 uint16_t MaxPacketSize,
									 uint8_t Interval,
									 uint8_t Mult);

/**
 * @brief  Modify an address to a desired alignment
 *
 * @param  Value		: input address
 * @return output aligned address
 */
static INLINE uint32_t Align32(uint32_t Value)
{
	return Value & 0xFFFFFFE0UL;	/* Bit 31 .. 5 */
}

/**
 * @brief  Modify an address to a desired alignment
 *
 * @param  alignment	: alignment desired value
 * @param  Value		: input address
 * @return output aligned address
 */
static INLINE uint32_t Aligned(uint32_t alignment, uint32_t Value)
{
	return Value & (~(alignment - 1));
}

/**
 * @brief  Modify an address to desired alignment
 *
 * @param  Value		: input address
 * @return output aligned address
 */
static INLINE uint32_t Align4k(uint32_t Value)
{
	return Value & 0xFFFFF000;	/* Bit 31 .. 5 */
}

/**
 * @brief  Modify an address to desired offset
 *
 * @param  Value		: input address
 * @return output offset address
 */
static INLINE uint32_t Offset4k(uint32_t Value)
{
	return Value & 0xFFF;
}

#endif

#endif

/** @} */
