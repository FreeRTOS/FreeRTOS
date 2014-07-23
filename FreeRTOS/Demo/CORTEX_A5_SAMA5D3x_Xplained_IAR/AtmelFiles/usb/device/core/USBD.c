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

/** \file
 *
 *  \section Purpose
 *
 *  Implementation of USB device functions on a UDP controller.
 *
 *  See \ref usbd_api "USBD API Methods".
 */

/** \addtogroup usbd_interface
 *@{
 */

/*---------------------------------------------------------------------------
 *      Headers
 *---------------------------------------------------------------------------*/

#include "USBD.h"
#include "USBD_HAL.h"

#include <USBLib_Trace.h>

/*---------------------------------------------------------------------------
 *      Definitions
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 *      Internal variables
 *---------------------------------------------------------------------------*/

/** Device current state. */
static uint8_t deviceState;
/** Indicates the previous device state */
static uint8_t previousDeviceState;

/*---------------------------------------------------------------------------
 *      Internal Functions
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 *      Exported functions
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 *      USBD: Event handlers
 *---------------------------------------------------------------------------*/

/**
 *  Handle the USB suspend event, should be invoked whenever
 *  HW reports a suspend signal.
 */
void USBD_SuspendHandler(void)
{
    /* Don't do anything if the device is already suspended */
    if (deviceState != USBD_STATE_SUSPENDED) {

        /* Switch to the Suspended state */
        previousDeviceState = deviceState;
        deviceState = USBD_STATE_SUSPENDED;

        /* Suspend HW interface */
        USBD_HAL_Suspend();

        /* Invoke the User Suspended callback (Suspend System?) */
        if (NULL != USBDCallbacks_Suspended)
            USBDCallbacks_Suspended();
    }
}

/**
 *  Handle the USB resume event, should be invoked whenever
 *  HW reports a resume signal.
 */
void USBD_ResumeHandler(void)
{
    /* Don't do anything if the device was not suspended */
    if (deviceState == USBD_STATE_SUSPENDED) {
        /* Active the device */
        USBD_HAL_Activate();
        deviceState = previousDeviceState;
        if (deviceState >= USBD_STATE_DEFAULT) {
            /* Invoke the Resume callback */
            if (NULL != USBDCallbacks_Resumed)
                USBDCallbacks_Resumed();
        }
    }
}

/**
 *  Handle the USB reset event, should be invoked whenever
 *  HW found USB reset signal on bus, which usually is called
 *  "end of bus reset" status.
 */
void USBD_ResetHandler()
{
    /* The device enters the Default state */
    deviceState = USBD_STATE_DEFAULT;
    /* Active the USB HW */
    USBD_HAL_Activate();
    /* Only EP0 enabled */
    USBD_HAL_ResetEPs(0xFFFFFFFF, USBD_STATUS_RESET, 0);
    USBD_ConfigureEndpoint(0);
    /* Invoke the Reset callback */
    if (NULL != USBDCallbacks_Reset)
        USBDCallbacks_Reset();
}

/**
 *  Handle the USB setup package received, should be invoked
 *  when an endpoint got a setup package as request.
 *  \param bEndpoint Endpoint number.
 *  \param pRequest  Pointer to content of request.
 */
void USBD_RequestHandler(uint8_t bEndpoint,
                         const USBGenericRequest* pRequest)
{
    if (bEndpoint != 0) {
        TRACE_WARNING("EP%d request not supported, default EP only",
                      bEndpoint);
    }
    else if (NULL != USBDCallbacks_RequestReceived) {
        USBDCallbacks_RequestReceived(pRequest);
    }
}

/*---------------------------------------------------------------------------
 *      USBD: Library interface
 *---------------------------------------------------------------------------*/

/**
 * Configures an endpoint according to its Endpoint Descriptor.
 * \param pDescriptor Pointer to an Endpoint descriptor.
 */
void USBD_ConfigureEndpoint(const USBEndpointDescriptor *pDescriptor)
{
    USBD_HAL_ConfigureEP(pDescriptor);
}

/**
 * Sends data through a USB endpoint. Sets up the transfer descriptor,
 * writes one or two data payloads (depending on the number of FIFO bank
 * for the endpoint) and then starts the actual transfer. The operation is
 * complete when all the data has been sent.
 *
 * *If the size of the buffer is greater than the size of the endpoint
 *  (or twice the size if the endpoint has two FIFO banks), then the buffer
 *  must be kept allocated until the transfer is finished*. This means that
 *  it is not possible to declare it on the stack (i.e. as a local variable
 *  of a function which returns after starting a transfer).
 *
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a buffer with the data to send.
 * \param dLength Size of the data buffer.
 * \param fCallback Optional callback function to invoke when the transfer is
 *        complete.
 * \param pArgument Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the transfer has been started;
 *         otherwise, the corresponding error status code.
 */
uint8_t USBD_Write( uint8_t          bEndpoint,
                    const void       *pData,
                    uint32_t         dLength,
                    TransferCallback fCallback,
                    void             *pArgument )
{
    USBD_HAL_SetTransferCallback(bEndpoint, fCallback, pArgument);
    return USBD_HAL_Write(bEndpoint, pData, dLength);
}
#if 0
/**
 * Sends data frames through a USB endpoint. Sets up the transfer descriptor
 * list, writes one or two data payloads (depending on the number of FIFO bank
 * for the endpoint) and then starts the actual transfer. The operation is
 * complete when all the data has been sent.
 *
 * *If the size of the frame is greater than the size of the endpoint
 *  (or twice the size if the endpoint has two FIFO banks), then the buffer
 *  must be kept allocated until the frame is finished*. This means that
 *  it is not possible to declare it on the stack (i.e. as a local variable
 *  of a function which returns after starting a transfer).
 *
 * \param bEndpoint Endpoint number.
 * \param pMbl Pointer to a frame (USBDTransferBuffer) list that describes
 *             the buffer list to send.
 * \param wListSize Size of the frame list.
 * \param bCircList Circle the list.
 * \param wStartNdx For circled list only, the first buffer index to transfer.
 * \param fCallback Optional callback function to invoke when the transfer is
 *        complete.
 * \param pArgument Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the transfer has been started;
 *         otherwise, the corresponding error status code.
 * \see USBDTransferBuffer, MblTransferCallback, USBD_MblReuse
 */
uint8_t USBD_MblWrite( uint8_t       bEndpoint,
                    void                *pMbl,
                    uint16_t      wListSize,
                    uint8_t       bCircList,
                    uint16_t      wStartNdx,
                    MblTransferCallback fCallback,
                    void                *pArgument )
{
    Endpoint    *pEndpoint = &(endpoints[bEndpoint]);
    MblTransfer *pTransfer = (MblTransfer*)&(pEndpoint->transfer);
    uint16_t i;

    /* EP0 is not suitable for Mbl */

    if (bEndpoint == 0) {

        return USBD_STATUS_INVALID_PARAMETER;
    }

    /* Check that the endpoint is in Idle state */

    if (pEndpoint->state != UDP_ENDPOINT_IDLE) {

        return USBD_STATUS_LOCKED;
    }
    pEndpoint->state = UDP_ENDPOINT_SENDINGM;

    TRACE_DEBUG_WP("WriteM%d(0x%x,%d) ", bEndpoint, pMbl, wListSize);

    /* Start from first if not circled list */

    if (!bCircList) wStartNdx = 0;

    /* Setup the transfer descriptor */

    pTransfer->pMbl        = (USBDTransferBuffer*)pMbl;
    pTransfer->listSize    = wListSize;
    pTransfer->fCallback   = fCallback;
    pTransfer->pArgument   = pArgument;
    pTransfer->currBuffer  = wStartNdx;
    pTransfer->freedBuffer = 0;
    pTransfer->pLastLoaded = &(((USBDTransferBuffer*)pMbl)[wStartNdx]);
    pTransfer->circList    = bCircList;
    pTransfer->allUsed     = 0;

    /* Clear all buffer */

    for (i = 0; i < wListSize; i ++) {

        pTransfer->pMbl[i].transferred = 0;
        pTransfer->pMbl[i].buffered   = 0;
        pTransfer->pMbl[i].remaining   = pTransfer->pMbl[i].size;
    }

    /* Send the first packet */

    while((UDP->UDP_CSR[bEndpoint]&UDP_CSR_TXPKTRDY)==UDP_CSR_TXPKTRDY);
    UDP_MblWriteFifo(bEndpoint);
    SET_CSR(bEndpoint, UDP_CSR_TXPKTRDY);

    /* If double buffering is enabled and there is data remaining, */

    /* prepare another packet */

    if ((CHIP_USB_ENDPOINTS_BANKS(bEndpoint) > 1)
        && (pTransfer->pMbl[pTransfer->currBuffer].remaining > 0)) {

        UDP_MblWriteFifo(bEndpoint);
    }

    /* Enable interrupt on endpoint */

    UDP->UDP_IER = 1 << bEndpoint;

    return USBD_STATUS_SUCCESS;
}
#endif
/**
 * Reads incoming data on an USB endpoint This methods sets the transfer
 * descriptor and activate the endpoint interrupt. The actual transfer is
 * then carried out by the endpoint interrupt handler. The Read operation
 * finishes either when the buffer is full, or a short packet (inferior to
 * endpoint maximum  size) is received.
 *
 * *The buffer must be kept allocated until the transfer is finished*.
 * \param bEndpoint Endpoint number.
 * \param pData Pointer to a data buffer.
 * \param dLength Size of the data buffer in bytes.
 * \param fCallback Optional end-of-transfer callback function.
 * \param pArgument Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the read operation has been started;
 *         otherwise, the corresponding error code.
 */
uint8_t USBD_Read(uint8_t          bEndpoint,
                  void             *pData,
                  uint32_t         dLength,
                  TransferCallback fCallback,
                  void             *pArgument)
{
    USBD_HAL_SetTransferCallback(bEndpoint, fCallback, pArgument);
    return USBD_HAL_Read(bEndpoint, pData, dLength);
}
#if 0
/**
 * Reuse first used/released buffer with new buffer address and size to be used
 * in transfer again. Only valid when frame list is ringed. Can be used for
 * both read & write.
 * \param bEndpoint  Endpoint number.
 * \param pNewBuffer Pointer to new buffer with data to send (0 to keep last).
 * \param wNewSize   Size of the data buffer
 */
uint8_t USBD_MblReuse( uint8_t  bEndpoint,
                    uint8_t  *pNewBuffer,
                    uint16_t wNewSize )
{
    Endpoint *pEndpoint = &(endpoints[bEndpoint]);
    MblTransfer *pTransfer = (MblTransfer*)&(pEndpoint->transfer);
    USBDTransferBuffer *pBi = &(pTransfer->pMbl[pTransfer->freedBuffer]);

    TRACE_DEBUG_WP("MblReuse(%d), st%x, circ%d\n\r",
        bEndpoint, pEndpoint->state, pTransfer->circList);

    /* Only for Multi-buffer-circle list */

    if (bEndpoint != 0
        && (pEndpoint->state == UDP_ENDPOINT_RECEIVINGM
            || pEndpoint->state == UDP_ENDPOINT_SENDINGM)
        && pTransfer->circList) {
    }
    else {

        return USBD_STATUS_WRONG_STATE;
    }

    /* Check if there is freed buffer */

    if (pTransfer->freedBuffer == pTransfer->currBuffer
        && !pTransfer->allUsed) {

        return USBD_STATUS_LOCKED;
   }

    /* Update transfer information */

    if ((++ pTransfer->freedBuffer) == pTransfer->listSize)
        pTransfer->freedBuffer = 0;
    if (pNewBuffer) {
        pBi->pBuffer = pNewBuffer;
        pBi->size    = wNewSize;
    }
    pBi->buffered    = 0;
    pBi->transferred = 0;
    pBi->remaining   = pBi->size;

    /* At least one buffer is not processed */

    pTransfer->allUsed = 0;
    return USBD_STATUS_SUCCESS;
}
#endif
/**
 * Sets the HALT feature on the given endpoint (if not already in this state).
 * \param bEndpoint Endpoint number.
 */
void USBD_Halt(uint8_t bEndpoint)
{
    USBD_HAL_Halt(bEndpoint, 1);
}

/**
 * Clears the Halt feature on the given endpoint.
 * \param bEndpoint Index of endpoint
 */
void USBD_Unhalt(uint8_t bEndpoint)
{
    USBD_HAL_Halt(bEndpoint, 0);
}

/**
 * Returns the current Halt status of an endpoint.
 * \param bEndpoint Index of endpoint
 * \return 1 if the endpoint is currently halted; otherwise 0
 */
uint8_t USBD_IsHalted(uint8_t bEndpoint)
{
    return USBD_HAL_Halt(bEndpoint, 0xFF);
}

/**
 * Indicates if the device is running in high or full-speed. Always returns 0
 * since UDP does not support high-speed mode.
 */
uint8_t USBD_IsHighSpeed(void)
{
    return USBD_HAL_IsHighSpeed();
}

/**
 * Causes the given endpoint to acknowledge the next packet it receives
 * with a STALL handshake.
 * \param bEndpoint Endpoint number.
 * \return USBD_STATUS_SUCCESS or USBD_STATUS_LOCKED.
 */
uint8_t USBD_Stall(uint8_t bEndpoint)

{
    return USBD_HAL_Stall(bEndpoint);
}

/**
 * Sets the device address to the given value.
 * \param address New device address.
 */
void USBD_SetAddress(uint8_t address)
{
    TRACE_INFO_WP("SetAddr(%d) ", address);

    USBD_HAL_SetAddress(address);
    if (address == 0) deviceState = USBD_STATE_DEFAULT;
    else              deviceState = USBD_STATE_ADDRESS;
}

/**
 * Sets the current device configuration.
 * \param cfgnum - Configuration number to set.
 */
void USBD_SetConfiguration(uint8_t cfgnum)
{
    TRACE_INFO_WP("SetCfg(%d) ", cfgnum);

    USBD_HAL_SetConfiguration(cfgnum);

    if (cfgnum != 0) {
        deviceState = USBD_STATE_CONFIGURED;
    }
    else {
        deviceState = USBD_STATE_ADDRESS;
        /* Reset all endpoints but Control 0 */
        USBD_HAL_ResetEPs(0xFFFFFFFE, USBD_STATUS_RESET, 0);
    }
}

/*---------------------------------------------------------------------------
 *      USBD: Library API
 *---------------------------------------------------------------------------*/

/**
 * Starts a remote wake-up procedure.
 */
void USBD_RemoteWakeUp(void)
{
    /* Device is NOT suspended */
    if (deviceState != USBD_STATE_SUSPENDED) {

        TRACE_INFO("USBD_RemoteWakeUp: Device is not suspended\n\r");
        return;
    }
    USBD_HAL_Activate();
    USBD_HAL_RemoteWakeUp();
}

/**
 * Connects the pull-up on the D+ line of the USB.
 */
void USBD_Connect(void)
{
    USBD_HAL_Connect();
}

/**
 * Disconnects the pull-up from the D+ line of the USB.
 */
void USBD_Disconnect(void)
{
    USBD_HAL_Disconnect();

    /* Device returns to the Powered state */

    if (deviceState > USBD_STATE_POWERED) {

        deviceState = USBD_STATE_POWERED;
    }

    if (previousDeviceState > USBD_STATE_POWERED) {

        previousDeviceState = USBD_STATE_POWERED;
    }
}

/**
 * Initializes the USB driver.
 */
void USBD_Init(void)
{
    TRACE_INFO_WP("USBD_Init\n\r");

    /* HW Layer Initialize */
    USBD_HAL_Init();

    /* Device is in the Attached state */
    deviceState = USBD_STATE_SUSPENDED;
    previousDeviceState = USBD_STATE_POWERED;

    /* Upper Layer Initialize */
    if (NULL != USBDCallbacks_Initialized)
        USBDCallbacks_Initialized();
}

/**
 * Returns the current state of the USB device.
 * \return Device current state.
 */
uint8_t USBD_GetState(void)
{
    return deviceState;
}

/**
 * Certification test for High Speed device.
 * \param bIndex Test to be done
 */
void USBD_Test(uint8_t bIndex)
{
    USBD_HAL_Test(bIndex);
}

/**@}*/
