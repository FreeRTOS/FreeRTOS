/*
 * @brief USB Device definitions for the LPC17xx microcontrollers
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

/** @ingroup Group_Device
 *  @defgroup Group_Device_LPC17xx Device Management (LPC17xx)
 *  @brief USB Device definitions for the LPC17xx microcontrollers.
 *
 *  Architecture specific USB Device definitions for the LPC microcontrollers.
 *
 *  @{
 */

#ifndef __USBDEVICE_LPC17XX_H__
#define __USBDEVICE_LPC17XX_H__

		#include "../../../../../Common/Common.h"
		#include "../../USBController.h"
		#include "../../StdDescriptors.h"
		#include "../../USBInterrupt.h"
		#include "../../HAL/HAL.h"
		#include "../../Endpoint.h"

		#if defined(__cplusplus)
extern "C" {
		#endif

		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

		#if (defined(USE_RAM_DESCRIPTORS) && defined(USE_EEPROM_DESCRIPTORS))
			#error USE_RAM_DESCRIPTORS and USE_EEPROM_DESCRIPTORS are mutually exclusive.
		#endif

			#if defined(__DOXYGEN__)
				/** Mask for the Options parameter of the @ref USB_Init() function. This indicates that the
				 *  USB interface should be initialized in low speed (1.5Mb/s) mode.
				 */
				#define USB_DEVICE_OPT_LOWSPEED            (1 << 0)
			#endif
			/** Mask for the Options parameter of the @ref USB_Init() function. This indicates that the
			 *  USB interface should be initialized in full speed (12Mb/s) mode.
			 */
			#define USB_DEVICE_OPT_FULLSPEED               (0 << 0)

			#if (!defined(NO_INTERNAL_SERIAL) && \
	(defined(__DOXYGEN__)) )
				/** String descriptor index for the device's unique serial number string descriptor within the device.
				 *  This unique serial number is used by the host to associate resources to the device (such as drivers or COM port
				 *  number allocations) to a device regardless of the port it is plugged in to on the host. Some microcontrollers contain
				 *  a unique serial number internally, and setting the device descriptors serial number string index to this value
				 *  will cause it to use the internal serial number.
				 *
				 *  On unsupported devices, this will evaluate to @ref NO_DESCRIPTOR and so will force the host to create a pseudo-serial
				 *  number for the device.
				 */
				#define USE_INTERNAL_SERIAL            0xDC
				/** Length of the device's unique internal serial number, in bits, if present on the selected microcontroller
				 *  model.
				 */
				#define INTERNAL_SERIAL_LENGTH_BITS    80
				/** Start address of the internal serial number, in the appropriate address space, if present on the selected microcontroller
				 *  model.
				 */
				#define INTERNAL_SERIAL_START_ADDRESS  0x0E
			#else
				#define USE_INTERNAL_SERIAL            NO_DESCRIPTOR

				#define INTERNAL_SERIAL_LENGTH_BITS    0
				#define INTERNAL_SERIAL_START_ADDRESS  0
			#endif

/** Sends a Remote Wakeup request to the host. This signals to the host that the device should
 *  be taken out of suspended mode, and communications should resume.
 */
void USB_Device_SendRemoteWakeup(void);

//Move to Endpoint_LPC17xx
/*static inline uint16_t USB_Device_GetFrameNumber(void) ATTR_ALWAYS_INLINE ATTR_WARN_UNUSED_RESULT;

static inline uint16_t USB_Device_GetFrameNumber(void)
{
	uint32_t val;

	SIE_WriteCommand(CMD_RD_FRAME);
	val = SIE_ReadCommandData(DAT_RD_FRAME);
	val = val | (SIE_ReadCommandData(DAT_RD_FRAME) << 8);

	return val;
}*/

			#if !defined(NO_SOF_EVENTS)
/** Enables the device mode Start Of Frame events. When enabled, this causes the
*  @ref EVENT_USB_Device_StartOfFrame() event to fire once per millisecond, synchronized to the USB bus,
*  at the start of each USB frame when enumerated in device mode.
*/
static inline void USB_Device_EnableSOFEvents(void) ATTR_ALWAYS_INLINE;

static inline void USB_Device_EnableSOFEvents(void)
{}

/** Disables the device mode Start Of Frame events. When disabled, this stops the firing of the
*  @ref EVENT_USB_Device_StartOfFrame() event when enumerated in device mode.
*/
static inline void USB_Device_DisableSOFEvents(void) ATTR_ALWAYS_INLINE;

static inline void USB_Device_DisableSOFEvents(void)
{}

			#endif

	#if !defined(__DOXYGEN__)
			#if defined(USB_DEVICE_OPT_LOWSPEED)
static inline void USB_Device_SetLowSpeed(void) ATTR_ALWAYS_INLINE;

static inline void USB_Device_SetLowSpeed(void)
{}

static inline void USB_Device_SetFullSpeed(void) ATTR_ALWAYS_INLINE;

static inline void USB_Device_SetFullSpeed(void)
{}

			#endif

//Move to Endpoint_LPC17XX
/*static inline void USB_Device_SetDeviceAddress(uint8_t corenum, const uint8_t Address) ATTR_ALWAYS_INLINE;

static inline void USB_Device_SetDeviceAddress(uint8_t corenum, const uint8_t Address)
{
	SIE_WriteCommandData(CMD_SET_ADDR, DAT_WR_BYTE(DEV_EN | Address));				 Don't wait for next
	SIE_WriteCommandData(CMD_SET_ADDR, DAT_WR_BYTE(DEV_EN | Address));				  Setup Status Phase
}*/

static inline bool USB_Device_IsAddressSet(void) ATTR_ALWAYS_INLINE ATTR_WARN_UNUSED_RESULT;

static inline bool USB_Device_IsAddressSet(void)
{
	return true;			/* TODO temporarily */
}

			#if (USE_INTERNAL_SERIAL != NO_DESCRIPTOR)
static inline void USB_Device_GetSerialString(uint16_t *const UnicodeString) ATTR_NON_NULL_PTR_ARG(1);

static inline void USB_Device_GetSerialString(uint16_t *const UnicodeString)
{
	uint_reg_t CurrentGlobalInt = GetGlobalInterruptMask();
	GlobalInterruptDisable();

	uint8_t SigReadAddress = INTERNAL_SERIAL_START_ADDRESS;

	for (uint8_t SerialCharNum = 0; SerialCharNum < (INTERNAL_SERIAL_LENGTH_BITS / 4); SerialCharNum++) {
		uint8_t SerialByte = boot_signature_byte_get(SigReadAddress);

		if (SerialCharNum & 0x01) {
			SerialByte >>= 4;
			SigReadAddress++;
		}

		SerialByte &= 0x0F;

		UnicodeString[SerialCharNum] = cpu_to_le16((SerialByte >= 10) ?
												   (('A' - 10) + SerialByte) : ('0' + SerialByte));
	}

	SetGlobalInterruptMask(CurrentGlobalInt);
}

			#endif

	#endif

		#if defined(__cplusplus)
}
		#endif

#endif

/** @} */

