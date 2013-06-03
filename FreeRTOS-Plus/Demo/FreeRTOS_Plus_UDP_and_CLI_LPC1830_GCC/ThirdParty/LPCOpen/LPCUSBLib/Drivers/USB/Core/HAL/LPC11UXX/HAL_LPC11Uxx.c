/*
 * @brief HAL USB functions for the LPC11Uxx microcontrollers
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

#if (defined(__LPC11U1X__) || defined(__LPC11U2X_3X__) || defined(__LPC1347__))

#include "../HAL.h"
#include "../../USBTask.h"

void HAL_USBInit(uint8_t corenum)
{
	/* power UP USB Phy and USB PLL */
	Chip_SYSCTL_PowerUp(SYSCTL_POWERDOWN_USBPAD_PD);
	Chip_SYSCTL_PowerUp(SYSCTL_POWERDOWN_USBPLL_PD);
        #if defined(__LPC1347__)
        Chip_Clock_SetUSBPllSource(SYSCTL_PLLCLKSRC_SYSOSC);
        #else
	Chip_Clock_SetUSBPllSource(SYSCTL_PLLCLKSRC_MAINOSC);
        #endif
	//while (!(LPC_SYSCTL->USBPLLCLKUEN & 0x01));
	Chip_Clock_SetupUSBPLL(3,1);
	while (!Chip_Clock_IsUSBPLLLocked()) {}
	Chip_Clock_SetUSBClockSource(SYSCTL_USBCLKSRC_PLLOUT, 1);
	
/* Enable AHB clock to the USB block and USB RAM. */
	LPC_SYSCTL->SYSAHBCLKCTRL |= ((0x1 << 14) | (0x1 << 27));
		
	LPC_USB->EPBUFCFG = 0x3FC;

	/* configure usb_soft connect */
	LPC_IOCON->PIO0[6] = 0x01;

#if !defined(USB_DEVICE_ROM_DRIVER)
	HAL_Reset();
#endif
}

void HAL_USBDeInit(uint8_t corenum, uint8_t mode)
{
	NVIC_DisableIRQ(USB0_IRQn);								/* disable USB interrupt */
	LPC_SYSCTL->SYSAHBCLKCTRL &= ~((0x1 << 14) | (0x1 << 27));	/* disable USB clock     */
}

void HAL_EnableUSBInterrupt(uint8_t corenum)
{
	NVIC_EnableIRQ(USB0_IRQn);
}

void HAL_DisableUSBInterrupt(uint8_t corenum)
{
	NVIC_DisableIRQ(USB0_IRQn);
}

void HAL_SetDeviceAddress(uint8_t Address)
{
#ifdef USB_CAN_BE_DEVICE
	LPC_USB->DEVCMDSTAT &= ~0x7F;
	LPC_USB->DEVCMDSTAT |= (USB_EN | Address);
#endif
}

void HAL_USBConnect(uint8_t corenum, uint32_t con)
{
#ifdef USB_CAN_BE_DEVICE
	if ( con ) {
		LPC_USB->DEVCMDSTAT |= USB_DCON;
	}
	else {
		LPC_USB->DEVCMDSTAT &= ~USB_DCON;
	}
#endif
}

#endif /*CHIP_LPC11UXX*/
