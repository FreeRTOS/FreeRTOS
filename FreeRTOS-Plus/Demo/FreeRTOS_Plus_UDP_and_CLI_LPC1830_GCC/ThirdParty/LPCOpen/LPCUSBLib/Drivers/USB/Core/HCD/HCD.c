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

#define  __INCLUDE_FROM_USB_DRIVER
#include "../USBMode.h"

#ifdef USB_CAN_BE_HOST

#if !defined(__LPC_OHCI__) && !defined(__LPC_EHCI__)
	#error "Either __LPC_OHCI__ or __LPC_EHCI__ must be defined"
#endif

#include "../USBTask.h"


#ifdef LPCUSBlib_DEBUG
void assert_status_ok_message(HCD_STATUS status,
							  char const *mess,
							  char const *func,
							  char const *file,
							  uint32_t const line)
{
	if (HCD_STATUS_OK != status) {
		hcd_printf("%s\r\n", func);
		hcd_printf("\t%s: %d\r\n", file, line);
		hcd_printf("\tEvaluated HCD_STATUS = %d\r\n", (uint32_t) status);
		if (mess != NULL) {
			hcd_printf("\t%s\r\n", mess);
		}
	}
}

#endif

void  HcdDelayUS(uint32_t  delay)
{
	volatile  uint32_t  i;

	for (i = 0; i < (4 * delay); i++)	/* This logic was tested. It gives app. 1 micro sec delay        */
		;
}

void  HcdDelayMS(uint32_t  delay)
{
	volatile  uint32_t  i;

	for (i = 0; i < delay; i++)
		HcdDelayUS(1000);
}

HCD_STATUS OpenPipe_VerifyParameters(uint8_t HostID,
									 uint8_t DeviceAddr,
									 HCD_USB_SPEED DeviceSpeed,
									 uint8_t EndpointNumber,
									 HCD_TRANSFER_TYPE TransferType,
									 HCD_TRANSFER_DIR TransferDir,
									 uint16_t MaxPacketSize,
									 uint8_t Interval,
									 uint8_t Mult)
{
	if  ((HostID >= MAX_USB_CORE) ||
		 ( DeviceAddr > 127) ||
		 ( DeviceSpeed > HIGH_SPEED) ||
		 (EndpointNumber & 0x70) ||
		 ( TransferType > INTERRUPT_TRANSFER) ||
		 ( TransferDir > OUT_TRANSFER) ) {
		ASSERT_STATUS_OK(HCD_STATUS_PARAMETER_INVALID);
	}

	/* XXX by USB specs Low speed device should not have packet size > 8, but many market devices does */
	if ((DeviceSpeed == LOW_SPEED) && ((TransferType == BULK_TRANSFER) || (TransferType == ISOCHRONOUS_TRANSFER)) ) {
		ASSERT_STATUS_OK(HCD_STATUS_PARAMETER_INVALID);
	}

	switch (TransferType) {
	case CONTROL_TRANSFER:
		if (MaxPacketSize > 64) {
			ASSERT_STATUS_OK(HCD_STATUS_PARAMETER_INVALID);
		}
		break;

	case BULK_TRANSFER:
		if (((DeviceSpeed == FULL_SPEED) && (MaxPacketSize > 64)) ||
			((DeviceSpeed == HIGH_SPEED) && (MaxPacketSize > 512)) ) {
			ASSERT_STATUS_OK(HCD_STATUS_PARAMETER_INVALID);
		}
		break;

	case INTERRUPT_TRANSFER:
		if ((Interval == 0) ||
			((DeviceSpeed == FULL_SPEED) && (MaxPacketSize > 64)) ||
			((DeviceSpeed == HIGH_SPEED) && ((MaxPacketSize > 1024) || (Interval > 16) || (Mult == 0))) ) {
			ASSERT_STATUS_OK(HCD_STATUS_PARAMETER_INVALID);
		}
		break;

	case ISOCHRONOUS_TRANSFER:
		if ((Interval == 0) || (Interval > 16) ||
			((DeviceSpeed == FULL_SPEED) && (MaxPacketSize > 1023)) ||
			((DeviceSpeed == HIGH_SPEED) && ((MaxPacketSize > 1024) || (Mult == 0))) ) {
			ASSERT_STATUS_OK(HCD_STATUS_PARAMETER_INVALID);
		}
		break;
	}
	return HCD_STATUS_OK;
}

#endif
