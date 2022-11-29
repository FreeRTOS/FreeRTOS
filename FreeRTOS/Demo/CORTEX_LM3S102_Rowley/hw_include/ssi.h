//*****************************************************************************
//
// ssi.h - Prototypes for the Synchronous Serial Interface Driver.
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
// This is part of revision 523 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __SSI_H__
#define __SSI_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Values that can be passed to SSIIntEnable, SSIIntDisable, and SSIIntClear
// as the ulIntFlags parameter, and returned by SSIIntStatus.
//
//*****************************************************************************
#define SSI_TXFF                0x00000008  // TX FIFO half empty or less
#define SSI_RXFF                0x00000004  // RX FIFO half full or less
#define SSI_RXTO                0x00000002  // RX timeout
#define SSI_RXOR                0x00000001  // RX overrun

//*****************************************************************************
//
// Values that can be passed to SSIConfig.
//
//*****************************************************************************
#define SSI_FRF_MOTO_MODE_0     0x00000000  // Moto fmt, polarity 0, phase 0
#define SSI_FRF_MOTO_MODE_1     0x00000002  // Moto fmt, polarity 0, phase 1
#define SSI_FRF_MOTO_MODE_2     0x00000001  // Moto fmt, polarity 1, phase 0
#define SSI_FRF_MOTO_MODE_3     0x00000003  // Moto fmt, polarity 1, phase 1
#define SSI_FRF_TI              0x00000010  // TI frame format
#define SSI_FRF_NMW             0x00000020  // National MicroWire frame format

#define SSI_MODE_MASTER         0x00000000  // SSI master
#define SSI_MODE_SLAVE          0x00000001  // SSI slave
#define SSI_MODE_SLAVE_OD       0x00000002  // SSI slave with output disabled

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern void SSIConfig(unsigned long ulBase, unsigned long ulProtocol,
                      unsigned long ulMode, unsigned long ulBitRate,
                      unsigned long ulDataWidth);
extern void SSIDataGet(unsigned long ulBase, unsigned long *ulData);
extern long SSIDataNonBlockingGet(unsigned long ulBase, unsigned long *ulData);
extern void SSIDataPut(unsigned long ulBase, unsigned long ulData);
extern long SSIDataNonBlockingPut(unsigned long ulBase, unsigned long ulData);
extern void SSIDisable(unsigned long ulBase);
extern void SSIEnable(unsigned long ulBase);
extern void SSIIntClear(unsigned long ulBase, unsigned long ulIntFlags);
extern void SSIIntDisable(unsigned long ulBase, unsigned long ulIntFlags);
extern void SSIIntEnable(unsigned long ulBase, unsigned long ulIntFlags);
extern void SSIIntRegister(unsigned long ulBase, void(*pfnHandler)(void));
extern unsigned long SSIIntStatus(unsigned long ulBase, tBoolean bMasked);
extern void SSIIntUnregister(unsigned long ulBase);

#ifdef __cplusplus
}
#endif

#endif // __SSI_H__
