/*
 * @brief USB Endpoint definitions for the LPC11Uxx microcontrollers
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
 *  @defgroup Group_EndpointRW_LPC11Uxx Endpoint Data Reading and Writing (LPC11Uxx, LPC1347)
 *  @brief Endpoint data read/write definitions for the LPC11Uxx and LPC1347 architecture.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing from and to endpoints.
 */

/** @ingroup Group_EndpointPrimitiveRW
 *  @defgroup Group_EndpointPrimitiveRW_LPC11Uxx Read/Write of Primitive Data Types (LPC11Uxx, LPC1347)
 *  @brief Endpoint primitive read/write definitions for the LPC11Uxx and LPC1347 architecture.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing of primitive data types
 *  from and to endpoints.
 */

/** @ingroup Group_EndpointPacketManagement
 *  @defgroup Group_EndpointPacketManagement_LPC11Uxx Endpoint Packet Management (LPC11Uxx, LPC1347)
 *  @brief Endpoint packet management definitions for the NXP LPC11Uxx and LPC1347 architecture.
 *
 *  Functions, macros, variables, enums and types related to packet management of endpoints.
 */

/** @ingroup Group_EndpointManagement
 *  @defgroup Group_EndpointManagement_LPC11Uxx Endpoint Management (LPC11Uxx, LPC1347)
 *  @brief Endpoint management definitions for the NXP LPC11Uxx and LPC1347 architecture.
 *
 *  Functions, macros and enums related to endpoint management when in USB Device mode. This
 *  module contains the endpoint management macros, as well as endpoint interrupt and data
 *  send/receive functions for various data types.
 *
 *  @{
 */

#ifndef __ENDPOINT_LPC11UXX_H__
#define __ENDPOINT_LPC11UXX_H__

		#include "../EndpointCommon.h"

		#if defined(__cplusplus)
extern "C" {
		#endif

		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	#if !defined(__DOXYGEN__)

				#define ENDPOINT_DETAILS_MAXEP             5
				#define ENDPOINT_DETAILS_MAXEP0		ENDPOINT_DETAILS_MAXEP
				#define ENDPOINT_DETAILS_MAXEP1		ENDPOINT_DETAILS_MAXEP
	
		#if defined(USB_DEVICE_ROM_DRIVER)

typedef struct _ROM {
	const unsigned p_usbd;
	const unsigned p_clib;
	const unsigned p_cand;
			#ifdef PWRROMD_PRESENT
	const PWRD *pPWRD;
			#else
	const unsigned p_pwrd;
			#endif /* PWRROMD_PRESENT */
			#ifdef DIVROMD_PRESENT
	const LPC_ROM_DIV_STRUCT *pROMDiv;
			#else
	const unsigned p_dev1;
			#endif /* DIVROMD_PRESENT */
	const unsigned p_dev2;
	const unsigned p_dev3;
	const unsigned p_dev4;
}  ROM_FUNCTION_TABLE;

			#define ROM_FUNCTION_TABLE_PTR_ADDR         (0x1FFF1FF8UL)
			#define ROM_USBD_PTR ((*(ROM_FUNCTION_TABLE * *) (ROM_FUNCTION_TABLE_PTR_ADDR))->p_usbd)

			#define ROMDRIVER_USB0_BASE LPC_USB0_BASE
			#define ROMDRIVER_USB1_BASE LPC_USB0_BASE
			#define ROMDRIVER_MEM_SIZE  0x500
extern uint8_t usb_RomDriver_buffer[ROMDRIVER_MEM_SIZE];

			#define ROMDRIVER_MSC_MEM_SIZE  0x100
extern uint8_t usb_RomDriver_MSC_buffer[ROMDRIVER_MSC_MEM_SIZE];

			#define ROMDRIVER_CDC_MEM_SIZE  0x8
extern uint8_t usb_RomDriver_CDC_buffer[ROMDRIVER_CDC_MEM_SIZE];

			#if (USB_FORCED_FULLSPEED)
				#define CDC_MAX_BULK_EP_SIZE            64
			#else
				#define CDC_MAX_BULK_EP_SIZE            512
			#endif
extern uint8_t UsbdCdc_EPIN_buffer[CDC_MAX_BULK_EP_SIZE];
extern uint8_t UsbdCdc_EPOUT_buffer[CDC_MAX_BULK_EP_SIZE];

			#define ROMDRIVER_HID_MEM_SIZE  0x8
extern uint8_t usb_RomDriver_HID_buffer[ROMDRIVER_HID_MEM_SIZE];

		#endif

void Endpoint_ClearEndpoints(uint8_t corenum);

bool Endpoint_ConfigureEndpoint_Prv(uint8_t corenum,
									const uint8_t Number,
									const uint8_t UECFG0XData,
									const uint8_t UECFG1XData);

	#endif
			#define USED_PHYSICAL_ENDPOINTS (ENDPOINT_DETAILS_MAXEP * 2)/* This macro effect memory size of the DCD */

			#define USB_EN              (0x1 << 7)	/* Device Enable */
			#define USB_SETUP_RCVD      (0x1 << 8)	/* SETUP token received */
			#define USB_PLL_ON          (0x1 << 9)	/* PLL is always ON */
			#define USB_LPM             (0x1 << 11)	/* LPM is supported */
			#define USB_IntOnNAK_AO     (0x1 << 12)	/* Device Interrupt on NAK BULK OUT */
			#define USB_IntOnNAK_AI     (0x1 << 13)	/* Device Interrupt on NAK BULK IN */
			#define USB_IntOnNAK_CO     (0x1 << 14)	/* Device Interrupt on NAK CTRL OUT */
			#define USB_IntOnNAK_CI     (0x1 << 15)	/* Device Interrupt on NAK CTRL IN */
			#define USB_DCON            (0x1 << 16)	/* Device connect */
			#define USB_DSUS            (0x1 << 17)	/* Device Suspend */
			#define USB_LPM_SUS         (0x1 << 19)	/* LPM suspend */
			#define USB_REMOTE_WAKE     (0x1 << 20)	/* LPM Remote Wakeup */
			#define USB_DCON_C          (0x1 << 24)	/* Device connection change */
			#define USB_DSUS_C          (0x1 << 25)	/* Device SUSPEND change */
			#define USB_DRESET_C        (0x1 << 26)	/* Device RESET */
			#define USB_VBUS_DBOUNCE    (0x1 << 28)	/* Device VBUS detect */

			#define EP0_INT             (0x1 << 0)
			#define EP1_INT             (0x1 << 1)
			#define EP2_INT             (0x1 << 2)
			#define EP3_INT             (0x1 << 3)
			#define EP4_INT             (0x1 << 4)
			#define EP5_INT             (0x1 << 5)
			#define EP6_INT             (0x1 << 6)
			#define EP7_INT             (0x1 << 7)
			#define EP8_INT             (0x1 << 8)
			#define EP9_INT             (0x1 << 9)
			#define FRAME_INT           (0x1 << 30)
			#define DEV_STAT_INT        (0x80000000)

			#define PKT_LNGTH_MASK      0x000003FF

			#define ERR_NOERROR         0x00
			#define ERR_PID_ENCODE      0x01
			#define ERR_UNKNOWN_PID     0x02
			#define ERR_UNEXPECT_PKT    0x03
			#define ERR_TCRC            0x04
			#define ERR_DCRC            0x05
			#define ERR_TIMEOUT         0x06
			#define ERR_BABBIE          0x07
			#define ERR_EOF_PKT         0x08
			#define ERR_TX_RX_NAK       0x09
			#define ERR_SENT_STALL      0x0A
			#define ERR_BUF_OVERRUN     0x0B
			#define ERR_SENT_EPT_PKT    0x0C
			#define ERR_BIT_STUFF       0x0D
			#define ERR_SYNC            0x0E
			#define ERR_TOGGLE_BIT      0x0F
extern void WrCmdDat (uint32_t cmd, uint32_t val);

extern void WrCmd (uint32_t cmd);

void HAL11UXX_WriteEndPoint(uint8_t EPNum, uint8_t *pData, uint32_t cnt);

void DcdDataTransfer(uint8_t EPNum, uint8_t *pData, uint32_t length);

void Endpoint_Streaming(uint8_t corenum, uint8_t *buffer, uint16_t packetsize,
						uint16_t totalpackets, uint16_t dummypackets);

extern USB_CMD_STAT EndPointCmdStsList[10][2];

/*static inline */ bool Endpoint_ConfigureEndpoint(uint8_t corenum,
													 const uint8_t Number,
												   const uint8_t Type,
												   const uint8_t Direction,
												   const uint16_t Size,
												   const uint8_t Banks)	/*ATTR_ALWAYS_INLINE*/;

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_ResetEndpoint(const uint8_t EndpointNumber) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ResetEndpoint(const uint8_t EndpointNumber)
{}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_EnableEndpoint(void) ATTR_ALWAYS_INLINE;

static inline void Endpoint_EnableEndpoint(void)
{}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_DisableEndpoint(void) ATTR_ALWAYS_INLINE;

static inline void Endpoint_DisableEndpoint(void)
{}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_IsEnabled(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsEnabled(void)
{
	return true;
}

PRAGMA_ALWAYS_INLINE
static inline uint8_t Endpoint_GetBusyBanks(void) ATTR_ALWAYS_INLINE ATTR_WARN_UNUSED_RESULT;

static inline uint8_t Endpoint_GetBusyBanks(void)
{
	return 0;
}

static inline void Endpoint_AbortPendingIN(void)
{}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_IsConfigured(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsConfigured(void)
{
	//				return ((UESTA0X & (1 << CFGOK)) ? true : false);
	return true;
}

PRAGMA_ALWAYS_INLINE
static inline uint8_t Endpoint_GetEndpointInterrupts(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline uint8_t Endpoint_GetEndpointInterrupts(void)
{
	return 0;				// TODO not yet implemented
}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_HasEndpointInterrupted(const uint8_t EndpointNumber) ATTR_WARN_UNUSED_RESULT
ATTR_ALWAYS_INLINE;

static inline bool Endpoint_HasEndpointInterrupted(const uint8_t EndpointNumber)
{
	return (Endpoint_GetEndpointInterrupts() & (1 << EndpointNumber)) ? true : false;
}

PRAGMA_ALWAYS_INLINE
static inline uint16_t Endpoint_BytesInEndpoint(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline uint16_t Endpoint_BytesInEndpoint(uint8_t corenum)
{
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
		return usb_data_buffer_size[corenum];
	}
	else {
		return usb_data_buffer_OUT_size[corenum];
	}
}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_IsINReady(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsINReady(uint8_t corenum)
{
	uint32_t PhyEP =
		(endpointselected[corenum] == ENDPOINT_CONTROLEP) ? (ENDPOINT_CONTROLEP + 1) : endpointhandle(corenum)[endpointselected[corenum]];
	return EndPointCmdStsList[PhyEP][0].Active ? false : true;
}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_IsOUTReceived(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsOUTReceived(uint8_t corenum)
{
	return				/*EndPointCmdStsList[ endpointhandle(corenum)[endpointselected] ][0].Active == 0 &&*/
		   EndPointCmdStsList[endpointhandle(corenum)[endpointselected[corenum]]][0].NBytes != 0x200;
}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_IsSETUPReceived(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsSETUPReceived(uint8_t corenum)
{
	return LPC_USB->DEVCMDSTAT & USB_SETUP_RCVD ? true : false;
}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_ClearSETUP(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearSETUP(uint8_t corenum)
{
	LPC_USB->DEVCMDSTAT |= USB_SETUP_RCVD;
	usb_data_buffer_index[corenum] = 0;
}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_ClearIN(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearIN(uint8_t corenum)
{
	uint8_t PhyEP = (endpointselected[corenum] == ENDPOINT_CONTROLEP ? 1 : endpointhandle(corenum)[endpointselected[corenum]]);
	if (PhyEP == 1) {
		DcdDataTransfer(PhyEP, usb_data_buffer[corenum], usb_data_buffer_index[corenum]);
		usb_data_buffer_index[corenum] = 0;
	}
	else {
		DcdDataTransfer(PhyEP, usb_data_buffer_IN[corenum], usb_data_buffer_IN_index[corenum]);
		usb_data_buffer_IN_index[corenum] = 0;
	}
}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_ClearOUT(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearOUT(uint8_t corenum)
{
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
		usb_data_buffer_index[corenum] = 0;
	}
	else {usb_data_buffer_OUT_index[corenum] = 0; }

	EndPointCmdStsList[endpointhandle(corenum)[endpointselected[corenum]]][0].NBytes = 0x200;
}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_StallTransaction(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_StallTransaction(uint8_t corenum)
{
	EndPointCmdStsList[endpointhandle(corenum)[endpointselected[corenum]]][0].Stall = 1;
	if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
		EndPointCmdStsList[1][0].Stall = 1;
	}
}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_ClearStall(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ClearStall(uint8_t corenum)
{
	EndPointCmdStsList[endpointhandle(corenum)[endpointselected[corenum]]][0].Stall = 0;
}

PRAGMA_ALWAYS_INLINE
static inline bool Endpoint_IsStalled(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

static inline bool Endpoint_IsStalled(uint8_t corenum)
{
	return EndPointCmdStsList[endpointhandle(corenum)[endpointselected[corenum]]][0].Stall ? true : false;
}

PRAGMA_ALWAYS_INLINE
static inline void Endpoint_ResetDataToggle(uint8_t corenum) ATTR_ALWAYS_INLINE;

static inline void Endpoint_ResetDataToggle(uint8_t corenum)
{
	EndPointCmdStsList[endpointhandle(corenum)[endpointselected[corenum]]][0].ToogleReset = 1;
}

			#if (!defined(FIXED_CONTROL_ENDPOINT_SIZE) || defined(__DOXYGEN__))
extern uint8_t USB_Device_ControlEndpointSize;
			#else
				#define USB_Device_ControlEndpointSize FIXED_CONTROL_ENDPOINT_SIZE
			#endif

void Endpoint_ClearStatusStage(uint8_t corenum);

uint8_t Endpoint_WaitUntilReady(void);

		#if defined(__cplusplus)
}
		#endif

#endif

/** @} */

