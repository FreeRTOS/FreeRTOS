/*
 * @brief HAL USB functions for the LPC18xx microcontrollers
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

#if defined(__LPC18XX__) || defined(__LPC43XX__)

#include "../HAL.h"
#include "../../USBTask.h"

#if defined(USB_CAN_BE_DEVICE)
#include "../../Device.h"

void HAL_USBConnect(uint8_t corenum, uint32_t con)
{
#if defined(USB_DEVICE_ROM_DRIVER)
	if (con) {
		USBD_API->hw->Connect(UsbHandle, 1);
	}
	else {
		USBD_API->hw->Connect(UsbHandle, 0);
	}
#else
	if (con) {
		USB_REG(corenum)->USBCMD_D |= (1 << 0);
	}
	else {
		USB_REG(corenum)->USBCMD_D &= ~(1 << 0);
	}
#endif
}

#endif

IP_USBHS_001_T * const USB_REG_BASE_ADDR[LPC18_43_MAX_USB_CORE] = {LPC_USB0, LPC_USB1};

/* Support for USB0 and USB1, 2 cores */
static bool coreEnabled[2];

void HAL_USBInit(uint8_t corenum)
{
	/* Just exit if already enabled */
	if (!coreEnabled[corenum]) {
		/* if other code is not enabled, the enable USB PLL */
		if (!coreEnabled[1 - corenum]) {
			/* Neither core is enabled, so enable USB PLL first */
			Chip_Clock_EnablePLL(CGU_USB_PLL);

			/* Wait for PLL lock */
			while (!(Chip_Clock_GetPLLStatus(CGU_USB_PLL) & CGU_PLL_LOCKED));
		}

		if (corenum == 0) {
			/* For core 0, enable USB0 base clock */
			Chip_Clock_EnableBaseClock(CLK_BASE_USB0);
			Chip_Clock_EnableOpts(CLK_MX_USB0, true, true, 1);

			/* Turn on the phy */
			Chip_CREG_EnableUSB0Phy(true);
		}
		else {
			/* For core 1, enable USB1 base clock */
			Chip_Clock_EnableBaseClock(CLK_BASE_USB1);
			Chip_Clock_EnableOpts(CLK_MX_USB1, true, true, 1);

			/* Turn on the phy */
			Chip_CREG_EnableUSB0Phy(true);
#if defined(USB_CAN_BE_HOST)
			/* enable USB1_DP and USB1_DN on chip FS phy */
			if (corenum && USB_CurrentMode[corenum] == USB_MODE_Host)LPC_SCU->SFSUSB = 0x16;
#endif
#if defined(USB_CAN_BE_DEVICE)
			/* enable USB1_DP and USB1_DN on chip FS phy */
			if (corenum && USB_CurrentMode[corenum] == USB_MODE_Device)LPC_SCU->SFSUSB = 0x12;
#endif
			LPC_USB1->PORTSC1_D |= (1 << 24);
		}

		coreEnabled[corenum] = true;
	}

#if defined(USB_CAN_BE_DEVICE) && (!defined(USB_DEVICE_ROM_DRIVER))
	/* reset the controller */
	USB_REG(corenum)->USBCMD_D = USBCMD_D_Reset;
	/* wait for reset to complete */
	while (USB_REG(corenum)->USBCMD_D & USBCMD_D_Reset) ;

	/* Program the controller to be the USB device controller */
	USB_REG(corenum)->USBMODE_D =   (0x2 << 0) /*| (1<<4)*//*| (1<<3)*/;
	if (corenum == 0) {
		/* set OTG transcever in proper state, device is present
		   on the port(CCS=1), port enable/disable status change(PES=1). */
		LPC_USB0->OTGSC = (1 << 3) | (1 << 0) /*| (1<<16)| (1<<24)| (1<<25)| (1<<26)| (1<<27)| (1<<28)| (1<<29)| (1<<30)*/;
		#if (USB_FORCED_FULLSPEED)
		LPC_USB0->PORTSC1_D |= (1 << 24);
		#endif
	}
	HAL_Reset(corenum);
#endif
}

void HAL_USBDeInit(uint8_t corenum, uint8_t mode)
{
	HAL_DisableUSBInterrupt(corenum);
	if (mode == USB_MODE_Device) {
		#if defined(USB_CAN_BE_HOST)
		USB_REG(corenum)->USBSTS_H = 0xFFFFFFFF;				/* clear all current interrupts */
		USB_REG(corenum)->PORTSC1_H &= ~(1 << 12);					/* clear port power */
		USB_REG(corenum)->USBMODE_H =   (1 << 0);				/* set USB mode reserve */
		#endif
	}
	else if (mode == USB_MODE_Host) {
		#if defined(USB_CAN_BE_DEVICE)
		/* Clear all pending interrupts */
		USB_REG(corenum)->USBSTS_D   = 0xFFFFFFFF;
		USB_REG(corenum)->ENDPTNAK   = 0xFFFFFFFF;
		USB_REG(corenum)->ENDPTNAKEN = 0;
		USB_REG(corenum)->ENDPTSETUPSTAT = USB_REG(corenum)->ENDPTSETUPSTAT;
		USB_REG(corenum)->ENDPTCOMPLETE  = USB_REG(corenum)->ENDPTCOMPLETE;
		while (USB_REG(corenum)->ENDPTPRIME) ;						/* Wait until all bits are 0 */
		USB_REG(corenum)->ENDPTFLUSH = 0xFFFFFFFF;
		while (USB_REG(corenum)->ENDPTFLUSH) ;		/* Wait until all bits are 0 */
		#endif
	}

	/* Disable USB PHY if both USB cores are disabled */
	if (coreEnabled[1 - corenum]) {
		/* Turn off the phy (prior to PLL disabled) */
		Chip_CREG_EnableUSB0Phy(false);
	}

	/* Power down USB clocking */
	if (corenum == 0) {
		Chip_Clock_Disable(CLK_MX_USB0);
		Chip_Clock_DisableBaseClock(CLK_BASE_USB0);
	}
	else {
		Chip_Clock_Disable(CLK_MX_USB1);
		Chip_Clock_DisableBaseClock(CLK_BASE_USB1);
	}

	/* Disable USB PLL if both USB cores are disabled */
	if (coreEnabled[1 - corenum]) {
		/* Disable USB PLL */
		Chip_Clock_DisablePLL(CGU_USB_PLL);
	}

	coreEnabled[corenum] = false;
}

void HAL_EnableUSBInterrupt(uint8_t corenum)
{
	NVIC_EnableIRQ((corenum) ? USB1_IRQn : USB0_IRQn);	//  enable USB interrupts
}

void HAL_DisableUSBInterrupt(uint8_t corenum)
{
	NVIC_DisableIRQ((corenum) ? USB1_IRQn : USB0_IRQn);	//  disable USB interrupts
}

void USB0_IRQHandler(void)
{
	if (USB_CurrentMode[0] == USB_MODE_Host) {
		#ifdef USB_CAN_BE_HOST
		HcdIrqHandler(0);
		#endif
	}
	if (USB_CurrentMode[0] == USB_MODE_Device) {
		#ifdef USB_CAN_BE_DEVICE
			#ifdef USB_DEVICE_ROM_DRIVER
		UsbdRom_IrqHandler();
			#else
		DcdIrqHandler(0);
			#endif
		#endif
	}
}

void USB1_IRQHandler(void)
{
	if (USB_CurrentMode[1] == USB_MODE_Host) {
		#ifdef USB_CAN_BE_HOST
		HcdIrqHandler(1);
		#endif
	}
	if (USB_CurrentMode[1] == USB_MODE_Device) {
		#ifdef USB_CAN_BE_DEVICE
			#ifdef USB_DEVICE_ROM_DRIVER
		UsbdRom_IrqHandler();
			#else
		DcdIrqHandler(1);
			#endif
		#endif
	}
}

#endif /*__LPC18XX__*/
