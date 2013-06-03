/*
 * @brief Audio device class ROM based application's specific functions supporting audio class layer
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

#ifndef __ADC_USER_H__
#define __ADC_USER_H__

//#include "error.h"
//#include "usbd.h"
#include "usbd_adc.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup Audio_Input_Device_ROM_Based_Audio_Device_Class ROM based class audio
 * @ingroup Audio_Input_Device_ROM_Based
 * @{
 */


/**
 * @brief	Initialize ROM based audio device class
 * @return	Nothing
 */
extern void UsbdAdc_Init(USB_ClassInfo_Audio_Device_t* AudioInterface);

/**
 * @brief	Start streaming audio data
 * @return	Nothing
 */
extern void UsbdAdc_start_xfr(void);

/**
 * @brief	Stop streaming audio data
 * @return	Nothing
 */
extern void UsbdAdc_stop_xfr(void);

/**
 * @brief	Determind start or stop transfer audio data
 * @param	hUsb			: Global USB ROM based handle variable
 * @return	ErrorCode_t		: LPC_OK for success
 */
extern ErrorCode_t USB_Interface_Event (USBD_HANDLE_T hUsb);

/**
 * @brief	Handle response to IN isochronous coming packets
 * @param	hUsb		: Global USB ROM based handle variable
 * @param	data		: Pointer point to buffer storing received data
 * @param	event		: USB_EVT_IN only acceptable value
 * @return	ErrorCode_t	: LPC_OK for success
 */
extern ErrorCode_t UsbdAdc_ISO_Hdlr (USBD_HANDLE_T hUsb, void* data, uint32_t event);

/**
 * @brief	Handle response to standard requests (chapter9) from host
 * @param	hUsb		: Global USB ROM based handle variable
 * @param	data		: no used
 * @param	event		: USB_EVT_OUT, USB_EVT_SETUP
 * @return	ErrorCode_t	: LPC_OK for success, ERR_USBD_UNHANDLED otherwise
 */
extern ErrorCode_t UsbdAdc_ep0_hdlr(USBD_HANDLE_T hUsb, void* data, uint32_t event);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif  /* __ADC_USER_H__ */
