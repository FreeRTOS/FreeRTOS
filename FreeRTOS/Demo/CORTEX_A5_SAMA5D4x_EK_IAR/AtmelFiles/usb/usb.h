/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 *  \file usb.h
 *
 *  Definition of SAM9XX5-EK usb library
 *
 */

#ifndef _usb_
#define _usb_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"

#include "include/USBD.h"
#include "include/USBD_HAL.h"

#include "include/USBDescriptors.h"

#include "include/USBDDriver.h"

#include "include/AUDDescriptors.h"
#include "include/AUDDFunction.h"
#include "include/AUDDSpeakerDriver.h"
#include "include/AUDDSpeakerPhone.h"
#include "include/AUDDSpeakerPhoneDriver.h"
#include "include/AUDDStream.h"
#include "include/AUDRequests.h"

#include "include/CDCAUDDDriver.h"
#include "include/CDCDescriptors.h"
#include "include/CDCDSerial.h"
#include "include/CDCDSerialDriver.h"
#include "include/CDCDSerialPort.h"
#include "include/CDCHIDDDriver.h"
#include "include/CDCMSDDriver.h"
#include "include/CDCNotifications.h"
#include "include/CDCRequests.h"

#include "include/DUALCDCDDriver.h"

#include "include/HIDAUDDDriver.h"
#include "include/HIDDescriptors.h"
#include "include/HIDDFunction.h"
#include "include/HIDDKeyboard.h"
#include "include/HIDDKeyboardDriver.h"
#include "include/HIDDMouseDriver.h"
#include "include/HIDDTransferDriver.h"
#include "include/HIDMSDDriver.h"
#include "include/HIDReports.h"
#include "include/HIDRequests.h"
#include "include/HIDUsages.h"

#include "include/MSD.h"
#include "include/MSDDriver.h"
#include "include/MSDDStateMachine.h"
#include "include/MSDescriptors.h"
#include "include/MSDFunction.h"
#include "include/MSDIOFifo.h"
#include "include/MSDLun.h"

#include "include/SBC.h"
#include "include/SBCMethods.h"

#include "include/USBVideo.h"

#include "include/USBLib_Types.h"
#include "include/USBRequests.h"

#endif /* #ifndef _usb_ */
