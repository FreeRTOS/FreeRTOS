/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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
 * \file
 *
 * \section Purpose
 *
 * Collection of methods for using the USB device controller on AT91
 * microcontrollers.
 *
 * \section Usage
 *
 * Please refer to the corresponding application note.
 * - \ref usbd_framework AT91 USB device framework
 * - \ref usbd_api USBD API
 *
 */

#ifndef USBD_H
#define USBD_H

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/


#include "USBDescriptors.h"
#include "USBRequests.h"

#include "USBLib_Types.h"

#include <stdio.h>

/*------------------------------------------------------------------------------
 *      Definitions
 *------------------------------------------------------------------------------*/

/* Define attribute */
#if defined   ( __CC_ARM   ) /* Keil ¦ÌVision 4 */
    #define WEAK __attribute__ ((weak))
#elif defined ( __ICCARM__ ) /* IAR Ewarm 5.41+ */
    #define WEAK __weak
#elif defined (  __GNUC__  ) /* GCC CS3 2009q3-68 */
    #define WEAK __attribute__ ((weak))
#endif

/* Define NO_INIT attribute */
#if defined   ( __CC_ARM   )
    #define NO_INIT
#elif defined ( __ICCARM__ )
    #define NO_INIT __no_init
#elif defined (  __GNUC__  )
    #define NO_INIT
#endif


/** \addtogroup usbd_interface
 *@{*/

/**
 * \addtogroup usbd_rc USB device API return codes
 *  @{
 * This section lists the return codes for the USB device driver API
 * - \ref USBD_STATUS_SUCCESS
 * - \ref USBD_STATUS_LOCKED
 * - \ref USBD_STATUS_ABORTED
 * - \ref USBD_STATUS_RESET
 */

/** Indicates the operation was successful. */
#define USBD_STATUS_SUCCESS             USBRC_SUCCESS
/** Endpoint/device is already busy. */
#define USBD_STATUS_LOCKED              USBRC_BUSY
/** Operation has been aborted (error or stall). */
#define USBD_STATUS_ABORTED             USBRC_ABORTED
/** Operation has been canceled (by user). */
#define USBD_STATUS_CANCELED            USBRC_CANCELED
/** Operation has been aborted because the device init/reset/un-configure. */
#define USBD_STATUS_RESET               USBRC_RESET
/** Part ot operation successfully done. */
#define USBD_STATUS_PARTIAL_DONE        USBRC_PARTIAL_DONE
/** Operation failed because parameter error */
#define USBD_STATUS_INVALID_PARAMETER   USBRC_PARAM_ERR
/** Operation failed because in unexpected state */
#define USBD_STATUS_WRONG_STATE         USBRC_STATE_ERR
/** Operation failed because SW not supported */
#define USBD_STATUS_SW_NOT_SUPPORTED    USBRC_SW_NOT_SUPPORTED
/** Operation failed because HW not supported */
#define USBD_STATUS_HW_NOT_SUPPORTED    USBRC_HW_NOT_SUPPORTED
/** @}*/

/** \addtogroup usbd_states USB device states
 *  @{
 * This section lists the device states of the USB device driver.
 * - \ref USBD_STATE_SUSPENDED
 * - \ref USBD_STATE_ATTACHED
 * - \ref USBD_STATE_POWERED
 * - \ref USBD_STATE_DEFAULT
 * - \ref USBD_STATE_ADDRESS
 * - \ref USBD_STATE_CONFIGURED
 */

/** The device is currently suspended. */
#define USBD_STATE_SUSPENDED            0
/** USB cable is plugged into the device. */
#define USBD_STATE_ATTACHED             1
/** Host is providing +5V through the USB cable. */
#define USBD_STATE_POWERED              2
/** Device has been reset. */
#define USBD_STATE_DEFAULT              3
/** The device has been given an address on the bus. */
#define USBD_STATE_ADDRESS              4
/** A valid configuration has been selected. */
#define USBD_STATE_CONFIGURED           5
/**  @}*/

/*----------------------------------------------------------------------------
 *         Types
 *----------------------------------------------------------------------------*/

/**
 * \brief Buffer struct used for multi-buffer-listed transfer.
 *
 * The driver can process 255 bytes of buffers or buffer list window.
 */
typedef struct _USBDTransferBuffer {
    /** Pointer to frame buffer */
    uint8_t * pBuffer;
    /** Size of the frame (up to 64K-1) */
    uint16_t size;
    /** Bytes transferred */
    uint16_t transferred;
    /** Bytes in FIFO */
    uint16_t buffered;
    /** Bytes remaining */
    uint16_t remaining;
} USBDTransferBuffer;

#pragma pack(1)
#if defined   ( __CC_ARM   ) /* Keil ¦ÌVision 4 */
#elif defined ( __ICCARM__ ) /* IAR Ewarm 5.41+ */
#define __attribute__(...)
#elif defined (  __GNUC__  ) /* GCC CS3 2009q3-68 */
#endif

/**
 * \brief Struct used for USBD DMA Link List Transfer Descriptor, must be 16-bytes
 * aligned.
 *
 * (For USB, DMA transfer is linked to EPs and FIFO address is EP defined)
 */
typedef struct _USBDDmaDescriptor {
    /** Pointer to Next Descriptor */
    void* pNxtDesc;
    /** Pointer to data buffer address */
    void* pDataAddr;
    /** DMA Control setting register value */
    uint32_t   ctrlSettings:8,      /** Control settings */
                   reserved:8,      /** Not used */
                   bufferLength:16; /** Length of buffer */
    /** Loaded to DMA register, OK to modify */
    uint32_t used;
} __attribute__((aligned(16))) USBDDmaDescriptor;

#pragma pack()

/**
 * Callback used by transfer functions (USBD_Read & USBD_Write) to notify
 * that a transaction is complete.
 */
typedef void (*TransferCallback)(void *pArg,
                                 uint8_t status,
                                 uint32_t transferred,
                                 uint32_t remaining);

/**
 * Callback used by MBL transfer functions (USBD_Read & USBD_Write) to notify
 * that a transaction is complete.
 * \param pArg     Pointer to callback arguments.
 * \param status   USBD status.
 */
typedef void (*MblTransferCallback)(void *pArg,
                                    uint8_t status);

/**@}*/

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

//extern void USBD_IrqHandler(void);

extern void USBD_Init(void);

extern void USBD_ConfigureSpeed(uint8_t forceFS);

extern void USBD_Connect(void);

extern void USBD_Disconnect(void);

extern uint8_t USBD_Write(
    uint8_t bEndpoint,
    const void *pData,
    uint32_t size,
    TransferCallback callback,
    void *pArg);

extern uint8_t USBD_Read(
    uint8_t bEndpoint,
    void *pData,
    uint32_t dLength,
    TransferCallback fCallback,
    void *pArg);

extern uint8_t USBD_Stall(uint8_t bEndpoint);

extern void USBD_Halt(uint8_t bEndpoint);

extern void USBD_Unhalt(uint8_t bEndpoint);

extern void USBD_ConfigureEndpoint(const USBEndpointDescriptor *pDescriptor);

extern uint8_t USBD_IsHalted(uint8_t bEndpoint);

extern void USBD_RemoteWakeUp(void);

extern void USBD_SetAddress(uint8_t address);

extern void USBD_SetConfiguration(uint8_t cfgnum);

extern uint8_t USBD_GetState(void);

extern uint8_t USBD_IsHighSpeed(void);

extern void USBD_Test(uint8_t bIndex);

extern void USBD_SuspendHandler(void);
extern void USBD_ResumeHandler(void);
extern void USBD_ResetHandler(void);
extern void USBD_RequestHandler(uint8_t bEndpoint,
                                const USBGenericRequest * pRequest);


extern void USBDCallbacks_Initialized(void);
extern void USBDCallbacks_Reset(void);
extern void USBDCallbacks_Suspended(void);
extern void USBDCallbacks_Resumed(void);
extern void USBDCallbacks_RequestReceived(const USBGenericRequest *request);

#endif /*#ifndef USBD_H*/

