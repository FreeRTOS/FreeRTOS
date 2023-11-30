//*****************************************************************************
//
// uart.h - Defines and Macros for the UART.
//
// Copyright (c) 2005-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __UART_H__
#define __UART_H__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Values that can be passed to UARTIntEnable, UARTIntDisable, and UARTIntClear
// as the ulIntFlags parameter, and returned from UARTIntStatus.
//
//*****************************************************************************
#define UART_INT_OE             0x400       // Overrun Error Interrupt Mask
#define UART_INT_BE             0x200       // Break Error Interrupt Mask
#define UART_INT_PE             0x100       // Parity Error Interrupt Mask
#define UART_INT_FE             0x080       // Framing Error Interrupt Mask
#define UART_INT_RT             0x040       // Receive Timeout Interrupt Mask
#define UART_INT_TX             0x020       // Transmit Interrupt Mask
#define UART_INT_RX             0x010       // Receive Interrupt Mask

//*****************************************************************************
//
// Values that can be passed to UARTConfigSetExpClk as the ulConfig parameter
// and returned by UARTConfigGetExpClk in the pulConfig parameter.
// Additionally, the UART_CONFIG_PAR_* subset can be passed to
// UARTParityModeSet as the ulParity parameter, and are returned by
// UARTParityModeGet.
//
//*****************************************************************************
#define UART_CONFIG_WLEN_MASK   0x00000060  // Mask for extracting word length
#define UART_CONFIG_WLEN_8      0x00000060  // 8 bit data
#define UART_CONFIG_WLEN_7      0x00000040  // 7 bit data
#define UART_CONFIG_WLEN_6      0x00000020  // 6 bit data
#define UART_CONFIG_WLEN_5      0x00000000  // 5 bit data
#define UART_CONFIG_STOP_MASK   0x00000008  // Mask for extracting stop bits
#define UART_CONFIG_STOP_ONE    0x00000000  // One stop bit
#define UART_CONFIG_STOP_TWO    0x00000008  // Two stop bits
#define UART_CONFIG_PAR_MASK    0x00000086  // Mask for extracting parity
#define UART_CONFIG_PAR_NONE    0x00000000  // No parity
#define UART_CONFIG_PAR_EVEN    0x00000006  // Even parity
#define UART_CONFIG_PAR_ODD     0x00000002  // Odd parity
#define UART_CONFIG_PAR_ONE     0x00000086  // Parity bit is one
#define UART_CONFIG_PAR_ZERO    0x00000082  // Parity bit is zero

//*****************************************************************************
//
// Values that can be passed to UARTFIFOLevelSet as the ulTxLevel parameter and
// returned by UARTFIFOLevelGet in the pulTxLevel.
//
//*****************************************************************************
#define UART_FIFO_TX1_8         0x00000000  // Transmit interrupt at 1/8 Full
#define UART_FIFO_TX2_8         0x00000001  // Transmit interrupt at 1/4 Full
#define UART_FIFO_TX4_8         0x00000002  // Transmit interrupt at 1/2 Full
#define UART_FIFO_TX6_8         0x00000003  // Transmit interrupt at 3/4 Full
#define UART_FIFO_TX7_8         0x00000004  // Transmit interrupt at 7/8 Full

//*****************************************************************************
//
// Values that can be passed to UARTFIFOLevelSet as the ulRxLevel parameter and
// returned by UARTFIFOLevelGet in the pulRxLevel.
//
//*****************************************************************************
#define UART_FIFO_RX1_8         0x00000000  // Receive interrupt at 1/8 Full
#define UART_FIFO_RX2_8         0x00000008  // Receive interrupt at 1/4 Full
#define UART_FIFO_RX4_8         0x00000010  // Receive interrupt at 1/2 Full
#define UART_FIFO_RX6_8         0x00000018  // Receive interrupt at 3/4 Full
#define UART_FIFO_RX7_8         0x00000020  // Receive interrupt at 7/8 Full

//*****************************************************************************
//
// Values that can be passed to UARTDMAEnable() and UARTDMADisable().
//
//*****************************************************************************
#define UART_DMA_ERR_RXSTOP     0x00000004  // Stop DMA receive if UART error
#define UART_DMA_TX             0x00000002  // Enable DMA for transmit
#define UART_DMA_RX             0x00000001  // Enable DMA for receive

//*****************************************************************************
//
// API Function prototypes
//
//*****************************************************************************
extern void UARTParityModeSet(unsigned long ulBase, unsigned long ulParity);
extern unsigned long UARTParityModeGet(unsigned long ulBase);
extern void UARTFIFOLevelSet(unsigned long ulBase, unsigned long ulTxLevel,
                             unsigned long ulRxLevel);
extern void UARTFIFOLevelGet(unsigned long ulBase, unsigned long *pulTxLevel,
                             unsigned long *pulRxLevel);
extern void UARTConfigSetExpClk(unsigned long ulBase, unsigned long ulUARTClk,
                                unsigned long ulBaud, unsigned long ulConfig);
extern void UARTConfigGetExpClk(unsigned long ulBase, unsigned long ulUARTClk,
                                unsigned long *pulBaud,
                                unsigned long *pulConfig);
extern void UARTEnable(unsigned long ulBase);
extern void UARTDisable(unsigned long ulBase);
extern void UARTEnableSIR(unsigned long ulBase, tBoolean bLowPower);
extern void UARTDisableSIR(unsigned long ulBase);
extern tBoolean UARTCharsAvail(unsigned long ulBase);
extern tBoolean UARTSpaceAvail(unsigned long ulBase);
extern long UARTCharGetNonBlocking(unsigned long ulBase);
extern long UARTCharGet(unsigned long ulBase);
extern tBoolean UARTCharPutNonBlocking(unsigned long ulBase,
                                       unsigned char ucData);
extern void UARTCharPut(unsigned long ulBase, unsigned char ucData);
extern void UARTBreakCtl(unsigned long ulBase, tBoolean bBreakState);
extern void UARTIntRegister(unsigned long ulBase, void(*pfnHandler)(void));
extern void UARTIntUnregister(unsigned long ulBase);
extern void UARTIntEnable(unsigned long ulBase, unsigned long ulIntFlags);
extern void UARTIntDisable(unsigned long ulBase, unsigned long ulIntFlags);
extern unsigned long UARTIntStatus(unsigned long ulBase, tBoolean bMasked);
extern void UARTIntClear(unsigned long ulBase, unsigned long ulIntFlags);
extern void UARTDMAEnable(unsigned long ulBase, unsigned long ulDMAFlags);
extern void UARTDMADisable(unsigned long ulBase, unsigned long ulDMAFlags);

//*****************************************************************************
//
// Several UART APIs have been renamed, with the original function name being
// deprecated.  These defines provide backward compatibility.
//
//*****************************************************************************
#ifndef DEPRECATED
#include "sysctl.h"
#define UARTConfigSet(a, b, c)                         \
        UARTConfigSetExpClk(a, SysCtlClockGet(), b, c)
#define UARTConfigGet(a, b, c)                         \
        UARTConfigGetExpClk(a, SysCtlClockGet(), b, c)
#define UARTCharNonBlockingGet(a) \
        UARTCharGetNonBlocking(a)
#define UARTCharNonBlockingPut(a, b) \
        UARTCharPutNonBlocking(a, b)
#endif

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif //  __UART_H__
