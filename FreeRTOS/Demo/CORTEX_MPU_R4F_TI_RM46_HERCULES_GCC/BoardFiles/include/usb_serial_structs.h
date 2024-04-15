/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/**
 *  @file       usb_serial_structs.h
 *
 *  @brief      Data structures defining this USB CDC device.
 *
 */

#ifndef _USB_SERIAL_STRUCTS_H_
#define _USB_SERIAL_STRUCTS_H_

/******************************************************************************
 *
 * The size of the transmit and receive buffers used for the redirected UART.
 * This number should be a power of 2 for best performance.  256 is chosen
 * pretty much at random though the buffer should be at least twice the size of
 * a maxmum-sized USB packet.
 *
 *****************************************************************************/
#define UART_BUFFER_SIZE 0x0001

/** ***************************************************************************
 *
 * CDC device callback function prototypes.
 *
 *****************************************************************************/
uint32 RxHandler( void * pvCBData, uint32 ulEvent, uint32 ulMsgValue, void * pvMsgData );
uint32 TxHandler( void * pvCBData, uint32 ulEvent, uint32 ulMsgValue, void * pvMsgData );
uint32 ControlHandler( void * pvCBData,
                       uint32 ulEvent,
                       uint32 ulMsgValue,
                       void * pvMsgData );

extern const tUSBBuffer g_sTxBuffer;
extern const tUSBBuffer g_sRxBuffer;
extern const tUSBDCDCDevice g_sCDCDevice;
extern uint8 g_pucUSBTxBuffer[];
extern uint8 g_pucUSBRxBuffer[];

#endif /* ifndef _USB_SERIAL_STRUCTS_H_ */
