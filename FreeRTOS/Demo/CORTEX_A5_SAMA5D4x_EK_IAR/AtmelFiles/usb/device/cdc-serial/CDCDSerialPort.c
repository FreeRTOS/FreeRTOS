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

/**\file
 *  Implementation of the CDCDSerialPort class methods.
 */

/** \addtogroup usbd_cdc
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include <CDCDSerialPort.h>
#include <CDCDescriptors.h>
#include <USBLib_Trace.h>

/*------------------------------------------------------------------------------
 *         Types
 *------------------------------------------------------------------------------*/

/** Parse data extention for descriptor parsing  */
typedef struct _CDCDParseData {
    /** Pointer to CDCDSerialPort instance */
    CDCDSerialPort * pCdcd;
    /** Pointer to found interface descriptor */
    USBInterfaceDescriptor * pIfDesc;
    
} CDCDParseData;

/*------------------------------------------------------------------------------
 *         Internal variables
 *------------------------------------------------------------------------------*/

/** Line coding values */
static CDCLineCoding lineCoding;

/*------------------------------------------------------------------------------
 *         Internal functions
 *------------------------------------------------------------------------------*/

/**
 * Parse descriptors: Interface, Bulk IN/OUT, Interrupt IN.
 * \param desc Pointer to descriptor list.
 * \param arg  Argument, pointer to AUDDParseData instance.
 */
static uint32_t _Interfaces_Parse(USBGenericDescriptor *pDesc,
                                  CDCDParseData * pArg)
{
    CDCDSerialPort *pCdcd = pArg->pCdcd;

    /* Not a valid descriptor */
    if (pDesc->bLength == 0)
        return USBRC_PARAM_ERR;

    /* Find interface descriptor */
    if (pDesc->bDescriptorType == USBGenericDescriptor_INTERFACE) {
        USBInterfaceDescriptor *pIf = (USBInterfaceDescriptor*)pDesc;

        /* Obtain interface from descriptor */
        if (pCdcd->bInterfaceNdx == 0xFF) {
            /* First interface is communication */
            if (pIf->bInterfaceClass ==
                CDCCommunicationInterfaceDescriptor_CLASS) {
                pCdcd->bInterfaceNdx = pIf->bInterfaceNumber;
                pCdcd->bNumInterface = 2;
            }
            /* Only data interface */
            else if(pIf->bInterfaceClass == CDCDataInterfaceDescriptor_CLASS) {
                pCdcd->bInterfaceNdx = pIf->bInterfaceNumber;
                pCdcd->bNumInterface = 1;
            }
            pArg->pIfDesc = pIf;
        }
        else if (pCdcd->bInterfaceNdx <= pIf->bInterfaceNumber
            &&   pCdcd->bInterfaceNdx + pCdcd->bNumInterface
                                       > pIf->bInterfaceNumber) {
            pArg->pIfDesc = pIf;
        }
    }

    /* Parse valid interfaces */
    if (pArg->pIfDesc == 0)
        return 0;

    /* Find endpoint descriptors */
    if (pDesc->bDescriptorType == USBGenericDescriptor_ENDPOINT) {
        USBEndpointDescriptor *pEp = (USBEndpointDescriptor*)pDesc;
        switch(pEp->bmAttributes & 0x3) {
            case USBEndpointDescriptor_INTERRUPT:
                if (pEp->bEndpointAddress & 0x80)
                    pCdcd->bIntInPIPE = pEp->bEndpointAddress & 0x7F;
                break;
            case USBEndpointDescriptor_BULK:
                if (pEp->bEndpointAddress & 0x80)
                    pCdcd->bBulkInPIPE = pEp->bEndpointAddress & 0x7F;
                else
                    pCdcd->bBulkOutPIPE = pEp->bEndpointAddress;
        }
    }

    if (    pCdcd->bInterfaceNdx != 0xFF
        &&  pCdcd->bBulkInPIPE != 0
        &&  pCdcd->bBulkOutPIPE != 0)
        return USBRC_FINISHED;

    return 0;
}

/**
 * Callback function which should be invoked after the data of a
 * SetLineCoding request has been retrieved. Sends a zero-length packet
 * to the host for acknowledging the request.
 * \param pCdcd Pointer to CDCDSerialPort instance.
 */
static void _SetLineCodingCallback(CDCDSerialPort * pCdcd)
{
    uint32_t exec = 1;
    if (pCdcd->fEventHandler) {
        uint32_t rc = pCdcd->fEventHandler(
                                        CDCDSerialPortEvent_SETLINECODING,
                                        (uint32_t)(&lineCoding),
                                        pCdcd->pArg);
        if (rc == USBD_STATUS_SUCCESS) {
            pCdcd->lineCoding.dwDTERate   = lineCoding.dwDTERate;
            pCdcd->lineCoding.bCharFormat = lineCoding.bCharFormat;
            pCdcd->lineCoding.bParityType = lineCoding.bParityType;
            pCdcd->lineCoding.bDataBits   = lineCoding.bDataBits;
        }
        else
            exec = 0;
    }
    if (exec)   USBD_Write(0, 0, 0, 0, 0);
    else        USBD_Stall(0);
}

/**
 * Receives new line coding information from the USB host.
 * \param pCdcd Pointer to CDCDSerialPort instance.
 */
static void _SetLineCoding(CDCDSerialPort * pCdcd)
{
    TRACE_INFO_WP("sLineCoding ");

    USBD_Read(0,
              (void *) & (lineCoding),
              sizeof(CDCLineCoding),
              (TransferCallback)_SetLineCodingCallback,
              (void*)pCdcd);
}

/**
 * Sends the current line coding information to the host through Control
 * endpoint 0.
 * \param pCdcd Pointer to CDCDSerialPort instance.
 */
static void _GetLineCoding(CDCDSerialPort * pCdcd)
{
    TRACE_INFO_WP("gLineCoding ");

    USBD_Write(0,
               (void *) &(pCdcd->lineCoding),
               sizeof(CDCLineCoding),
               0,
               0);
}

/**
 * Changes the state of the serial driver according to the information
 * sent by the host via a SetControlLineState request, and acknowledges
 * the request with a zero-length packet.
 * \param pCdcd Pointer to CDCDSerialPort instance.
 * \param request Pointer to a USBGenericRequest instance.
 */
static void _SetControlLineState(
    CDCDSerialPort * pCdcd,
    const USBGenericRequest *request)
{
  #if (TRACE_LEVEL >= TRACE_LEVEL_INFO)
    uint8_t DTR, RTS;

    DTR = ((request->wValue & CDCControlLineState_DTR) > 0);
    RTS = ((request->wValue & CDCControlLineState_RTS) > 0);
    TRACE_INFO_WP("sControlLineState(%d, %d) ", DTR, RTS);
  #endif

    pCdcd->bControlLineState = (uint8_t)request->wValue;
    USBD_Write(0, 0, 0, 0, 0);

    if (pCdcd->fEventHandler)
        pCdcd->fEventHandler(CDCDSerialPortEvent_SETCONTROLLINESTATE,

                             (uint32_t)pCdcd->bControlLineState,
                             pCdcd->pArg);
}

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 * Initializes the USB Device CDC serial port function.
 * \param pCdcd Pointer to CDCDSerialPort instance.
 * \param pUsbd Pointer to USBDDriver instance.
 * \param fEventHandler Pointer to event handler function.
 * \param firstInterface First interface index for the function
 *                       (0xFF to parse from descriptors).
 * \param numInterface   Number of interfaces for the function.
 */
void CDCDSerialPort_Initialize(CDCDSerialPort * pCdcd,
                               USBDDriver * pUsbd,
                               CDCDSerialPortEventHandler fEventHandler,
                               void * pArg,
                               uint8_t firstInterface,uint8_t numInterface)
{
    TRACE_INFO("CDCDSerialPort_Initialize\n\r");

    /* Initialize event handler */
    pCdcd->fEventHandler = fEventHandler;
    pCdcd->pArg = pArg;

    /* Initialize USB Device Driver interface */
    pCdcd->pUsbd = pUsbd;
    pCdcd->bInterfaceNdx = firstInterface;
    pCdcd->bNumInterface = numInterface;
    pCdcd->bIntInPIPE   = 0;
    pCdcd->bBulkInPIPE  = 0;
    pCdcd->bBulkOutPIPE = 0;

    /* Initialize Abstract Control Model attributes */
    pCdcd->bControlLineState = 0;
    pCdcd->wSerialState      = 0;
    CDCLineCoding_Initialize(&(pCdcd->lineCoding),
                             115200,
                             CDCLineCoding_ONESTOPBIT,
                             CDCLineCoding_NOPARITY,
                             8);
}

/**
 * Parse CDC Serial Port information for CDCDSerialPort instance.
 * Accepted interfaces:
 * - Communication Interface + Data Interface
 * - Data Interface ONLY
 * \param pCdcd        Pointer to CDCDSerialPort instance.
 * \param pDescriptors Pointer to descriptor list.
 * \param dwLength     Descriptor list size in bytes.
 */
USBGenericDescriptor *CDCDSerialPort_ParseInterfaces(
    CDCDSerialPort *pCdcd,
    USBGenericDescriptor *pDescriptors,
    uint32_t dwLength)
{
    CDCDParseData parseData;

    parseData.pCdcd   = pCdcd;
    parseData.pIfDesc = 0;

    return USBGenericDescriptor_Parse(
                    pDescriptors, dwLength,
                    (USBDescriptorParseFunction)_Interfaces_Parse,
                    &parseData);
}


/**
 * Handles CDC-specific SETUP requests. Should be called from a
 * re-implementation of USBDCallbacks_RequestReceived() method.
 * \param pCdcd Pointer to CDCDSerialPort instance.
 * \param request Pointer to a USBGenericRequest instance.
 * \return USBRC_SUCCESS if request handled, otherwise error.
 */
uint32_t CDCDSerialPort_RequestHandler(
    CDCDSerialPort *pCdcd,
    const USBGenericRequest *request)
{
    if (USBGenericRequest_GetType(request) != USBGenericRequest_CLASS)
        return USBRC_PARAM_ERR;

    TRACE_INFO_WP("Cdcs ");

    /* Validate interface */
    if (request->wIndex >= pCdcd->bInterfaceNdx &&
        request->wIndex < pCdcd->bInterfaceNdx + pCdcd->bNumInterface) {
    }
    else {
        return USBRC_PARAM_ERR;
    }

    /* Handle the request */
    switch (USBGenericRequest_GetRequest(request)) {

        case CDCGenericRequest_SETLINECODING:

            _SetLineCoding(pCdcd);
            break;

        case CDCGenericRequest_GETLINECODING:

            _GetLineCoding(pCdcd);
            break;

        case CDCGenericRequest_SETCONTROLLINESTATE:

            _SetControlLineState(pCdcd, request);
            break;

        default:

            return USBRC_PARAM_ERR;
    }

    return USBRC_SUCCESS;
}

/**
 * Receives data from the host through the virtual COM port created by
 * the CDC device serial driver. This function behaves like USBD_Read.
 * \param pCdcd  Pointer to CDCDSerialPort instance.
 * \param pData  Pointer to the data buffer to put received data.
 * \param dwSize Size of the data buffer in bytes.
 * \param fCallback Optional callback function to invoke when the transfer
 *                  finishes.
 * \param pArg      Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the read operation has been started normally;
 *         otherwise, the corresponding error code.
 */
uint32_t CDCDSerialPort_Read(const CDCDSerialPort * pCdcd,
                          void * pData,uint32_t dwSize,
                          TransferCallback fCallback,void * pArg)
{
    if (pCdcd->bBulkOutPIPE == 0)
        return USBRC_PARAM_ERR;

    return USBD_Read(pCdcd->bBulkOutPIPE,
                     pData, dwSize,
                     fCallback, pArg);
}

/**
 * Sends a data buffer through the virtual COM port created by the CDC
 * device serial driver. This function behaves exactly like USBD_Write.
 * \param pCdcd  Pointer to CDCDSerialPort instance.
 * \param pData  Pointer to the data buffer to send.
 * \param dwSize Size of the data buffer in bytes.
 * \param fCallback Optional callback function to invoke when the transfer
 *                  finishes.
 * \param pArg      Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the read operation has been started normally;
 *         otherwise, the corresponding error code.
 */
uint32_t CDCDSerialPort_Write(const CDCDSerialPort * pCdcd,
                                   void * pData, uint32_t dwSize,
                                   TransferCallback fCallback, void * pArg)
{
    if (pCdcd->bBulkInPIPE == 0)
        return USBRC_PARAM_ERR;

    return USBD_Write(pCdcd->bBulkInPIPE,
                      pData, dwSize,
                      fCallback, pArg);
}

/**
 * Returns the current control line state of the RS-232 line.
 * \param pCdcd  Pointer to CDCDSerialPort instance.
 */
uint8_t CDCDSerialPort_GetControlLineState(const CDCDSerialPort * pCdcd)
{
    return pCdcd->bControlLineState;
}

/**
 * Copy current line coding settings to pointered space.
 * \param pCdcd  Pointer to CDCDSerialPort instance.
 * \param pLineCoding Pointer to CDCLineCoding instance.
 */
void CDCDSerialPort_GetLineCoding(const CDCDSerialPort * pCdcd,
                                  CDCLineCoding* pLineCoding)
{
    if (pLineCoding) {
        pLineCoding->dwDTERate   = pCdcd->lineCoding.dwDTERate;
        pLineCoding->bCharFormat = pCdcd->lineCoding.bCharFormat;
        pLineCoding->bParityType = pCdcd->lineCoding.bParityType;
        pLineCoding->bDataBits   = pCdcd->lineCoding.bDataBits;
    }
}

/**
 * Returns the current status of the RS-232 line.
 * \param pCdcd  Pointer to CDCDSerialPort instance.
 */
uint16_t CDCDSerialPort_GetSerialState(const CDCDSerialPort * pCdcd)
{
    return pCdcd->wSerialState;
}

/**
 * Sets the current serial state of the device to the given value.
 * \param pCdcd  Pointer to CDCDSerialPort instance.
 * \param wSerialState  New device state.
 */
void CDCDSerialPort_SetSerialState(CDCDSerialPort * pCdcd,
                                   uint16_t wSerialState)
{
    if (pCdcd->bIntInPIPE == 0)
        return;

    /* If new state is different from previous one, send a notification to the
       host */
    if (pCdcd->wSerialState != wSerialState) {

        pCdcd->wSerialState = wSerialState;
        USBD_Write(pCdcd->bIntInPIPE,
                   &(pCdcd->wSerialState),
                   2,
                   0,
                   0);

        /* Reset one-time flags */
        pCdcd->wSerialState &= ~(CDCSerialState_OVERRUN
                              | CDCSerialState_PARITY
                              | CDCSerialState_FRAMING
                              | CDCSerialState_RINGSIGNAL
                              | CDCSerialState_BREAK);
    }
}

/**@}*/

