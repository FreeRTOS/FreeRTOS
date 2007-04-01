/* This header file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief EMAC abstraction layer for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */



#ifndef AVR32_EMAC_H
#define AVR32_EMAC_H

#if __GNUC__
#  include <avr32/io.h>
#elif __ICCAVR32__
#  include <avr32/iouc3a0512.h>
#else
#  error Unknown compiler
#endif

#include <arch/sys_arch.h>

#include "conf_eth.h"


/* Receive Transfer descriptor structure */
typedef struct  _AVR32_RxTdDescriptor {
  unsigned int addr;
  union
  {
    unsigned int status;
    struct {
      unsigned int BroadCast:1;
      unsigned int MultiCast:1;
      unsigned int UniCast:1;
      unsigned int ExternalAdd:1;
      unsigned int Res1:1;
      unsigned int Sa1Match:1;
      unsigned int Sa2Match:1;
      unsigned int Sa3Match:1;
      unsigned int Sa4Match:1;
      unsigned int TypeID:1;
      unsigned int VlanTag:1;
      unsigned int PriorityTag:1;
      unsigned int VlanPriority:3;
      unsigned int Cfi:1;
      unsigned int EndOfFrame:1;
      unsigned int StartOfFrame:1;
      unsigned int Rxbuf_off:2;
      unsigned int Res0:1;
      unsigned int Length:11;
    }S_Status;
  }U_Status;
}AVR32_RxTdDescriptor, *AVR32P_RxTdDescriptor;


/* Transmit Transfer descriptor structure */
typedef struct _AVR32_TxTdDescriptor {
  unsigned int addr;
  union
  {
    unsigned int status;
    struct {
      unsigned int BuffUsed:1;
      unsigned int Wrap:1;
      unsigned int TransmitError:1;
      unsigned int TransmitUnderrun:1;
      unsigned int BufExhausted:1;
      unsigned int Res1:10;
      unsigned int NoCrc:1;
      unsigned int LastBuff:1;
      unsigned int Res0:4;
      unsigned int Length:11;
    }S_Status;
  }U_Status;
}AVR32_TxTdDescriptor, *AVR32P_TxTdDescriptor;

#define AVR32_OWNERSHIP_BIT   0x00000001

/* Receive status defintion */
#define AVR32_BROADCAST_ADDR  ((unsigned int) (1 << 31))  //* Broadcat address detected
#define AVR32_MULTICAST_HASH  ((unsigned int) (1 << 30))  //* MultiCast hash match
#define AVR32_UNICAST_HASH    ((unsigned int) (1 << 29))  //* UniCast hash match
#define AVR32_EXTERNAL_ADDR   ((unsigned int) (1 << 28))  //* External Address match
#define AVR32_SA1_ADDR        ((unsigned int) (1 << 26))  //* Specific address 1 match
#define AVR32_SA2_ADDR        ((unsigned int) (1 << 25))  //* Specific address 2 match
#define AVR32_SA3_ADDR        ((unsigned int) (1 << 24))  //* Specific address 3 match
#define AVR32_SA4_ADDR        ((unsigned int) (1 << 23))  //* Specific address 4 match
#define AVR32_TYPE_ID         ((unsigned int) (1 << 22))  //* Type ID match
#define AVR32_VLAN_TAG        ((unsigned int) (1 << 21))  //* VLAN tag detected
#define AVR32_PRIORITY_TAG    ((unsigned int) (1 << 20))  //* PRIORITY tag detected
#define AVR32_VLAN_PRIORITY   ((unsigned int) (7 << 17))  //* PRIORITY Mask
#define AVR32_CFI_IND         ((unsigned int) (1 << 16))  //* CFI indicator
#define AVR32_EOF             ((unsigned int) (1 << 15))  //* EOF
#define AVR32_SOF             ((unsigned int) (1 << 14))  //* SOF
#define AVR32_RBF_OFFSET      ((unsigned int) (3 << 12))  //* Receive Buffer Offset Mask
#define AVR32_LENGTH_FRAME    ((unsigned int) 0x0FFF)     //* Length of frame

/* Transmit Status definition */
#define AVR32_TRANSMIT_OK     ((unsigned int) (1 << 31))  //*
#define AVR32_TRANSMIT_WRAP   ((unsigned int) (1 << 30))  //* Wrap bit: mark the last descriptor
#define AVR32_TRANSMIT_ERR    ((unsigned int) (1 << 29))  //* RLE:transmit error
#define AVR32_TRANSMIT_UND    ((unsigned int) (1 << 28))  //* Transmit Underrun
#define AVR32_BUF_EX          ((unsigned int) (1 << 27))  //* Buffers exhausted in mid frame
#define AVR32_TRANSMIT_NO_CRC ((unsigned int) (1 << 16))  //* No CRC will be appended to the current frame
#define AVR32_LAST_BUFFER     ((unsigned int) (1 << 15))  //*

#define AVR32_EMAC_CLKEN      0x2

/*
 * Initialise the EMAC driver.  If successful a semaphore is returned that
 * is used by the EMAC ISR to indicate that Rx packets have been received.
 * If the initialisation fails then NULL is returned.
 */
xSemaphoreHandle xEMACInit( void );

/*
 * Send ulLength bytes from pcFrom.  This copies the buffer to one of the
 * EMAC Tx buffers, then indicates to the EMAC that the buffer is ready.
 * If lEndOfFrame is true then the data being copied is the end of the frame
 * and the frame can be transmitted.
 */
portLONG lEMACSend( portCHAR *pcFrom, unsigned portLONG ulLength, portLONG lEndOfFrame );

/*
 * Frames can be read from the EMAC in multiple sections.
 * Read ulSectionLength bytes from the EMAC receive buffers to pcTo.
 * ulTotalFrameLength is the size of the entire frame.  Generally vEMACRead
 * will be repetedly called until the sum of all the ulSectionLenths totals
 * the value of ulTotalFrameLength.
 */
void vEMACRead( portCHAR *pcTo, unsigned portLONG ulSectionLength, unsigned portLONG ulTotalFrameLength );

/*
 * The EMAC driver and interrupt service routines are defined in different
 * files as the driver is compiled to THUMB, and the ISR to ARM.  This function
 * simply passes the semaphore used to communicate between the two.
 */
void vPassEMACSemaphore( xSemaphoreHandle xCreatedSemaphore );

/*
 * Called by the Tx interrupt, this function traverses the buffers used to
 * hold the frame that has just completed transmission and marks each as
 * free again.
 */
void vClearEMACTxBuffer( void );

/*
 * Suspend on a semaphore waiting either for the semaphore to be obtained
 * or a timeout.  The semaphore is used by the EMAC ISR to indicate that
 * data has been received and is ready for processing.
 */
void vEMACWaitForInput( void );

/*
 * Return the length of the next frame in the receive buffers.
 */
unsigned portLONG ulEMACInputLength( void );

/*
 * Set the MACB Physical address (SA1B & SA1T registers).
 */
void vEMACSetMACAddress(const portCHAR * EMACAddress);

/*
 * Get the MACB Physical address (SA1B & SA1T registers).
 */
void vEMACGetMACAddress(portCHAR * EMACAddress);

#endif
