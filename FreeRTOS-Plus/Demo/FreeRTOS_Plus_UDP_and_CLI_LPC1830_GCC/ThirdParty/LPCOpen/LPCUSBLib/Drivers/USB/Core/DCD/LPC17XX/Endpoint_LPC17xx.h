/*
 * @brief USB Endpoint definitions for the LPC17xx microcontrollers
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

/** @ingroup Group_EndpointRW
 *  @defgroup Group_EndpointRW_LPC17xx Endpoint Data Reading and Writing (LPC17xx)
 *  @brief Endpoint data read/write definitions for the LPC architecture.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing from and to endpoints.
 */

/** @ingroup Group_EndpointPrimitiveRW
 *  @defgroup Group_EndpointPrimitiveRW_LPC17xx Read/Write of Primitive Data Types (LPC17xx)
 *  @brief Endpoint primitive read/write definitions for the LPC17xx architecture.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing of primitive data types
 *  from and to endpoints.
 */

/** @ingroup Group_EndpointPacketManagement
 *  @defgroup Group_EndpointPacketManagement_LPC17xx Endpoint Packet Management (LPC17xx)
 *  @brief Endpoint packet management definitions for the NXP LPC17xx architecture.
 *
 *  Functions, macros, variables, enums and types related to packet management of endpoints.
 */

/** @ingroup Group_EndpointManagement
 *  @defgroup Group_EndpointManagement_LPC17xx Endpoint Management (LPC17xx)
 *  @brief Endpoint management definitions for the LPC17xx architecture.
 *
 *  Functions, macros and enums related to endpoint management when in USB Device mode. This
 *  module contains the endpoint management macros, as well as endpoint interrupt and data
 *  send/receive functions for various data types.
 *
 *  @{
 */

#ifndef __ENDPOINT_LPC17XX_H__
#define __ENDPOINT_LPC17XX_H__

		#include "../EndpointCommon.h"

		#if defined(__cplusplus)
extern "C" {
		#endif

		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	#if !defined(__DOXYGEN__)

			#define ENDPOINT_DETAILS_MAXEP      6							/* Maximum of supported endpoint */
			#define USED_PHYSICAL_ENDPOINTS     (ENDPOINT_DETAILS_MAXEP * 2)	/* This macro effect memory size of the DCD */
			#define ENDPOINT_DETAILS_MAXEP0		ENDPOINT_DETAILS_MAXEP
			#define ENDPOINT_DETAILS_MAXEP1		ENDPOINT_DETAILS_MAXEP

extern volatile bool SETUPReceived;
extern DMADescriptor dmaDescriptor[USED_PHYSICAL_ENDPOINTS];

void SIE_WriteCommandData (uint32_t cmd, uint32_t val);

void SIE_WriteCommand (uint32_t cmd);

extern volatile bool isOutReceived;
extern volatile bool isInReady;

void WriteControlEndpoint(uint8_t *pData, uint32_t cnt);

void ReadControlEndpoint(uint8_t *pData);

void DcdDataTransfer(uint8_t PhyEP, uint8_t *pData, uint32_t cnt);

void Endpoint_Streaming(uint8_t corenum, uint8_t *buffer, uint16_t packetsize,
						uint16_t totalpackets, uint16_t dummypackets);

void Endpoint_ClearEndpoints(uint8_t corenum);

bool Endpoint_ConfigureEndpoint_Prv(uint8_t corenum,
									const uint8_t Number,
									const uint8_t UECFG0XData,
									const uint8_t UECFG1XData);

	#endif
			/** 
			 * 	@brief	Configures the specified endpoint number with the given endpoint type, direction, bank size
			 *  		and banking mode. Once configured, the endpoint may be read from or written to, depending
			 *  		on its direction.
			 *
			 * 	@param  corenum        	: 	ID Number of USB Core to be processed.
			 *  @param 	Number     		:	Endpoint number to configure. This must be more than 0 and less than
			 *                        		@ref ENDPOINT_TOTAL_ENDPOINTS.
			 *
			 *  @param 	Type       		:	Type of endpoint to configure, a \c EP_TYPE_* mask. Not all endpoint types
			 *                        		are available on Low Speed USB devices - refer to the USB 2.0 specification.
			 *
			 *  @param 	Direction  		:	Endpoint data direction, either @ref ENDPOINT_DIR_OUT or @ref ENDPOINT_DIR_IN.
			 *                        		All endpoints (except Control type) are unidirectional - data may only be read
			 *                        		from or written to the endpoint bank based on its direction, not both.
			 *
			 *  @param 	Size       		:	Size of the endpoint's bank, where packets are stored before they are transmitted
			 *                        		to the USB host, or after they have been received from the USB host (depending on
			 *                        		the endpoint's data direction). The bank size must indicate the maximum packet size
			 *                        		that the endpoint can handle.
			 *
			 *  @param	Banks      		:	Number of banks to use for the endpoint being configured, an \c ENDPOINT_BANK_* mask.
			 *                        		More banks uses more USB DPRAM, but offers better performance. Isochronous type
			 *                        		endpoints <b>must</b> have at least two banks.
			 *  @return Boolean \c true if the configuration succeeded, \c false otherwise.
			 */
/*static inline */ bool Endpoint_ConfigureEndpoint(uint8_t corenum,
												   const uint8_t Number,
												   const uint8_t Type,
												   const uint8_t Direction,
												   const uint16_t Size,
												   const uint8_t Banks)	/*ATTR_ALWAYS_INLINE*/;

static inline uint16_t USB_Device_GetFrameNumber(void) ATTR_ALWAYS_INLINE ATTR_WARN_UNUSED_RESULT;

static inline uint16_t USB_Device_GetFrameNumber(void)
{
	uint32_t val;

	SIE_WriteCommand(CMD_RD_FRAME);
	val = SIE_ReadCommandData(DAT_RD_FRAME);
	val = val | (SIE_ReadCommandData(DAT_RD_FRAME) << 8);

	return val;
}

static inline void USB_Device_SetDeviceAddress(uint8_t corenum, const uint8_t Address) ATTR_ALWAYS_INLINE;

static inline void USB_Device_SetDeviceAddress(uint8_t corenum, const uint8_t Address)
{
	SIE_WriteCommandData(CMD_SET_ADDR, DAT_WR_BYTE(DEV_EN | Address));
	SIE_WriteCommandData(CMD_SET_ADDR, DAT_WR_BYTE(DEV_EN | Address));
}

/**
 * @brief  Resets the endpoint bank FIFO. This clears all the endpoint banks and resets the USB controller's
 *  data In and Out pointers to the bank's contents.
 *
 * @param  EndpointNumber : Endpoint number whose FIFO buffers are to be reset.
 * @return Nothing.
 */
static inline void Endpoint_ResetEndpoint(const uint8_t EndpointNumber) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ResetEndpoint(const uint8_t EndpointNumber)
{}

/**
 *  @brief  Enables the currently selected endpoint so that data can be sent and received through it to
 *  and from a host.
 *
 *  @note Endpoints must first be configured properly via @ref Endpoint_ConfigureEndpoint().
 *  @return Nothing.
 */
static inline void Endpoint_EnableEndpoint(void) ATTR_ALWAYS_INLINE;

static inline void Endpoint_EnableEndpoint(void)
{}

/**
 *  @brief  Disables the currently selected endpoint so that data cannot be sent and received through it
 *  to and from a host.
 *  @return Nothing.
 */
static inline void Endpoint_DisableEndpoint(void) ATTR_ALWAYS_INLINE;

static inline void Endpoint_DisableEndpoint(void)
{}

/**
 * @brief  Determines if the currently selected endpoint is enabled, but not necessarily configured
 * @return Boolean \c true if the currently selected endpoint is enabled, \c false otherwise.
 */
static inline bool Endpoint_IsEnabled(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsEnabled(void)
{
	return true;
}

/**
 *  @brief  Retrieves the number of busy banks in the currently selected endpoint, which have been queued for
 *  transmission via the @ref Endpoint_ClearIN() command, or are awaiting acknowledgement via the
 *  @ref Endpoint_ClearOUT() command.
 *
 *  @ingroup Group_EndpointPacketManagement_LPC18xx
 *
 *  @return Total number of busy banks in the selected endpoint.
 */
static inline uint8_t Endpoint_GetBusyBanks(void) ATTR_ALWAYS_INLINE ATTR_WARN_UNUSED_RESULT;

static inline uint8_t Endpoint_GetBusyBanks(void)
{
	return 0;
}

/** @brief Aborts all pending IN transactions on the currently selected endpoint, once the bank
 *  has been queued for transmission to the host via @ref Endpoint_ClearIN(). This function
 *  will terminate all queued transactions, resetting the endpoint banks ready for a new
 *  packet.
 *
 *  @ingroup Group_EndpointPacketManagement_LPC18xx
 *  @return Nothing.
 */
static inline void Endpoint_AbortPendingIN(void)
{}

/**
 * @brief  Determines if the currently selected endpoint is configured.
 *
 *  @return Boolean \c true if the currently selected endpoint has been configured, \c false otherwise.
 */
static inline bool Endpoint_IsConfigured(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsConfigured(void)
{
	return true;
}

/**
 *  @brief  Returns a mask indicating which INTERRUPT type endpoints have interrupted - i.e. their
 *  interrupt duration has elapsed. Which endpoints have interrupted can be determined by
 *  masking the return value against <tt>(1 << <i>{Endpoint Number}</i>)</tt>.
 *
 *  @return Mask whose bits indicate which endpoints have interrupted.
 */
static inline uint8_t Endpoint_GetEndpointInterrupts(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline uint8_t Endpoint_GetEndpointInterrupts(void)
{
	return 0;
}

/**
 * @brief  Determines if the specified endpoint number has interrupted (valid only for INTERRUPT type
 *		   endpoints).
 * @param  EndpointNumber : Index of the endpoint whose interrupt flag should be tested
 * @return Boolean \c true if the specified endpoint has interrupted, \c false otherwise.
 */
static inline bool Endpoint_HasEndpointInterrupted(const uint8_t EndpointNumber) ATTR_WARN_UNUSED_RESULT
ATTR_ALWAYS_INLINE;

static inline bool Endpoint_HasEndpointInterrupted(const uint8_t EndpointNumber)
{
	return (Endpoint_GetEndpointInterrupts() & (1 << EndpointNumber)) ? true : false;
}

/**
 * @brief  Indicates the number of bytes currently stored in the current endpoint's selected bank.
 *
 * @note The return width of this function may differ, depending on the maximum endpoint bank size
 *        of the selected LPC model.
 * @ingroup Group_EndpointRW_LPC17xx
 * @param  corenum :        ID Number of USB Core to be processed.
 * @return Total number of bytes in the currently selected Endpoint's FIFO buffer
 */
static inline uint16_t Endpoint_BytesInEndpoint(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline uint16_t Endpoint_BytesInEndpoint(uint8_t corenum)
{
	if (endpointselected == ENDPOINT_CONTROLEP) {
		return usb_data_buffer_size[corenum];
	}
	else {
		// return (dmaDescriptor[ endpointhandle[endpointselected] ].PresentCount);
		return usb_data_buffer_OUT_size[corenum];
	}
}

/**
 * @brief  Determines if the selected IN endpoint is ready for a new packet to be sent to the host.
 *
 * @ingroup Group_EndpointPacketManagement_LPC17xx
 *
 * @param  corenum :        ID Number of USB Core to be processed.
 * @return Boolean \c true if the current endpoint is ready for an IN packet, \c false otherwise.
 */
static inline bool Endpoint_IsINReady(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsINReady(uint8_t corenum)
{
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {

		return isInReady;
	}
	else {
		uint8_t SelEP_Data;
		if (dmaDescriptor[endpointhandle(corenum)[endpointselected[corenum]]].Retired == true) {
 			SIE_WriteCommand(CMD_SEL_EP(endpointhandle(corenum)[endpointselected[corenum]]) );
 			SelEP_Data = SIE_ReadCommandData(DAT_SEL_EP(endpointhandle(corenum)[endpointselected[corenum]]) );
 			if ((SelEP_Data & 1) == 0) {
 				return true;
 			}
		}
		return false;
	}

}

/**
 * @brief  Determines if the selected OUT endpoint has received new packet from the host.
 *
 * @ingroup Group_EndpointPacketManagement_LPC17xx
 *
 * @param  corenum :        ID Number of USB Core to be processed.
 * @return Boolean \c true if current endpoint is has received an OUT packet, \c false otherwise.
 */
static inline bool Endpoint_IsOUTReceived(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsOUTReceived(uint8_t corenum)
{
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {

		return isOutReceived;
	}
	else {
		return (dmaDescriptor[endpointhandle(corenum)[endpointselected[corenum]]].Retired &&
				(dmaDescriptor[endpointhandle(corenum)[endpointselected[corenum]]].Status == 2 ||
				 dmaDescriptor[endpointhandle(corenum)[endpointselected[corenum]]].Status == 3)
				) ? true : false;
	}
}

/**
 * @brief  Determines if the current CONTROL type endpoint has received a SETUP packet.
 *
 * @ingroup Group_EndpointPacketManagement_LPC17xx
 *
 * @param  corenum :        ID Number of USB Core to be processed.
 * @return Boolean \c true if the selected endpoint has received a SETUP packet, \c false otherwise.
 */
static inline bool Endpoint_IsSETUPReceived(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsSETUPReceived(uint8_t corenum)
{
	return SETUPReceived;
}

/**
 *  @brief  Clears a received SETUP packet on the currently selected CONTROL type endpoint, freeing up the
 *  		endpoint for the next packet.
 *
 *  @ingroup Group_EndpointPacketManagement_LPC17xx
 *
 *  @param  corenum :        ID Number of USB Core to be processed.
 *  @return Nothing.
 *  @note 	This is not applicable for non CONTROL type endpoints.
 */
static inline void Endpoint_ClearSETUP(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearSETUP(uint8_t corenum)
{
	SETUPReceived = FALSE;
	usb_data_buffer_index[corenum] = 0;
	usb_data_buffer_size[corenum] = 0;
	SIE_WriteCommand(CMD_SEL_EP(ENDPOINT_CONTROLEP));
	SIE_WriteCommand(CMD_CLR_BUF);
}

/**
 *  @brief  Sends an IN packet to the host on the currently selected endpoint, freeing up the endpoint for the
 *  		next packet and switching to the alternative endpoint bank if double banked.
 *
 *  @ingroup Group_EndpointPacketManagement_LPC17xx
 *  @param  corenum :        ID Number of USB Core to be processed.
 *  @return Nothing.
 */
static inline void Endpoint_ClearIN(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearIN(uint8_t corenum)
{
	uint8_t PhyEP = (endpointselected[corenum] == ENDPOINT_CONTROLEP ? 1 : endpointhandle(corenum)[endpointselected[corenum]]);

	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
		WriteControlEndpoint(usb_data_buffer[corenum], usb_data_buffer_index[corenum]);
		usb_data_buffer_index[corenum] = 0;
		usb_data_buffer_size[corenum] = 0;
	}
	else {
		DcdDataTransfer(PhyEP, usb_data_buffer_IN[corenum], usb_data_buffer_IN_index[corenum]);
		LPC_USB->DMARSet = _BIT(PhyEP);
		usb_data_buffer_IN_index[corenum] = 0;
	}
}

/**
 * @brief  	Acknowledges an OUT packet to the host on the currently selected endpoint, freeing up the endpoint
 *  		for the next packet and switching to the alternative endpoint bank if double banked.
 *
 * @ingroup Group_EndpointPacketManagement_LPC17xx
 * @param  corenum :        ID Number of USB Core to be processed.
 * @return Nothing.
 */
static inline void Endpoint_ClearOUT(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearOUT(uint8_t corenum)
{
	usb_data_buffer_index[corenum] = 0;
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {				/* Control only */
		SIE_WriteCommand(CMD_SEL_EP(ENDPOINT_CONTROLEP));
		SIE_WriteCommand(CMD_CLR_BUF);
		isOutReceived = false;
	}
	else {
		usb_data_buffer_OUT_index[corenum] = 0;
		usb_data_buffer_OUT_size[corenum] = 0;
		dmaDescriptor[endpointhandle(corenum)[endpointselected[corenum]]].Status = 0;
		LPC_USB->DMAIntEn |= (1 << 1);
	}
}

/**
 *  @brief  Stalls the current endpoint, indicating to the host that a logical problem occurred with the
 *  		indicated endpoint and that the current transfer sequence should be aborted. This provides a
 *  		way for devices to indicate invalid commands to the host so that the current transfer can be
 *  		aborted and the host can begin its own recovery sequence.
 *
 *  		The currently selected endpoint remains stalled until either the @ref Endpoint_ClearStall() macro
 *  		is called, or the host issues a CLEAR FEATURE request to the device for the currently selected
 *  		endpoint.
 *
 *  @ingroup Group_EndpointPacketManagement_LPC17xx
 *  @param  corenum :        ID Number of USB Core to be processed.
 *  @return Nothing.
 */
// static inline void Endpoint_StallTransaction(void) ATTR_ALWAYS_INLINE;
void Endpoint_StallTransaction(uint8_t corenum);

/**
 *  @brief  Clears the STALL condition on the currently selected endpoint.
 *
 *  @ingroup Group_EndpointPacketManagement_LPC17xx
 *  @param  corenum :        ID Number of USB Core to be processed.
 *  @return Nothing.
 */
static inline void Endpoint_ClearStall(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearStall(uint8_t corenum)
{
	uint8_t PhysicalEp = endpointhandle(corenum)[endpointselected[corenum]] + (endpointselected[corenum] == ENDPOINT_CONTROLEP ? 1 : 0);

	HAL_DisableUSBInterrupt(corenum);
	SIE_WriteCommandData(CMD_SET_EP_STAT(PhysicalEp), DAT_WR_BYTE(0));
	HAL_EnableUSBInterrupt(corenum);
}

/**
 * @brief  	Determines if the currently selected endpoint is stalled, false otherwise.
 *
 * @ingroup Group_EndpointPacketManagement_LPC17xx
 *
 * @param  	corenum :        ID Number of USB Core to be processed.
 * @return 	Boolean \c true if the currently selected endpoint is stalled, \c false otherwise.
 */
static inline bool Endpoint_IsStalled(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsStalled(uint8_t corenum)
{
	bool isStalled;

	HAL_DisableUSBInterrupt(corenum);
	SIE_WriteCommand(CMD_SEL_EP(endpointhandle(corenum)[endpointselected[corenum]]) );
	isStalled = SIE_ReadCommandData(DAT_SEL_EP(endpointhandle(corenum)[endpointselected[corenum]]) ) & EP_SEL_ST ? true : false;
	HAL_EnableUSBInterrupt(corenum);

	return isStalled;					/* Device Status */
}

/** Resets the data toggle of the currently selected endpoint. */
static inline void Endpoint_ResetDataToggle(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ResetDataToggle(uint8_t corenum)
{}

			#if (!defined(FIXED_CONTROL_ENDPOINT_SIZE) || defined(__DOXYGEN__))
extern uint8_t USB_Device_ControlEndpointSize;
			#else
				#define USB_Device_ControlEndpointSize FIXED_CONTROL_ENDPOINT_SIZE
			#endif

/**
 * @brief 	Completes the status stage of a control transfer on a CONTROL type endpoint automatically,
 *  		with respect to the data direction. This is a convenience function which can be used to
 *  		simplify user control request handling.
 * @param  	corenum :        ID Number of USB Core to be processed.
 * @return 	Nothing.
 */
void Endpoint_ClearStatusStage(uint8_t corenum);

uint8_t Endpoint_WaitUntilReady(void);

		#if defined(__cplusplus)
}
		#endif

#endif

/** @} */

