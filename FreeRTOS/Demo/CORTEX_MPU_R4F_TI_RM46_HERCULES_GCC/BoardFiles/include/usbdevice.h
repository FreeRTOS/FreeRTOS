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
 *  @file       usbdevice.h
 *
 *  @brief      Types and definitions used during USB enumeration.
 *
 */

#ifndef __USBDEVICE_H__
#define __USBDEVICE_H__

/******************************************************************************
 *
 * If building with a C++ compiler, make all of the definitions in this header
 * have a C binding.
 *
 *****************************************************************************/
#ifdef __cplusplus
extern "C" {
#endif

/** ***************************************************************************
 *
 * \ingroup device_api
 * @{
 *
 *****************************************************************************/

/** ***************************************************************************
 *
 *  @brief  The maximum number of independent interfaces that any single device
 *          implementation can support.  Independent interfaces means interface
 *          descriptors with different bInterfaceNumber values - several
 *          interface descriptors offering different alternative settings but
 *          the same interface number count as a single interface.
 *
 *****************************************************************************/
/*#define USB_MAX_INTERFACES_PER_DEVICE 8u*/

/** ***************************************************************************
 *
 * Close the Doxygen group.
 * @}
 *
 *****************************************************************************/

/** ***************************************************************************
 *
 *  @brief  The default USB endpoint FIFO configuration structure.  This
 *          structure contains definitions to set all USB FIFOs into single
 *          buffered mode with no DMA use.  Each endpoint's FIFO is sized to
 *          hold the largest maximum packet size for any interface alternate
 *          setting in the current config descriptor.  A pointer to this
 *          structure may be passed in the psFIFOConfig field of the
 *          tDeviceInfo structure passed to USBCDCInit if the application does
 *          not require any special handling of the USB controller FIFO.
 *
 *****************************************************************************/
extern const tFIFOConfig g_sUSBDefaultFIFOConfig;

/** ***************************************************************************
 *
 * Public APIs offered by the USB library device control driver.
 *
 *****************************************************************************/
extern void USBDCDInit( uint32 ulIndex, tDeviceInfo * psDevice );
extern void USBDCDTerm( uint32 ulIndex );
extern void USBDCDStallEP0( uint32 ulIndex );
extern void USBDCDRequestDataEP0( uint32 ulIndex, uint8 * pucData, uint32 ulSize );
extern void USBDCDSendDataEP0( uint32 ulIndex, uint8 * pucData, uint32 ulSize );
extern void USBDCDSetDefaultConfiguration( uint32 ulIndex, uint32 ulDefaultConfig );
extern uint32 USBDCDConfigDescGetSize( const tConfigHeader * psConfig );
extern uint32 USBDCDConfigDescGetNum( const tConfigHeader * psConfig, uint32 ulType );
extern tDescriptorHeader * USBDCDConfigDescGet( const tConfigHeader * psConfig,
                                                uint32 ulType,
                                                uint32 ulIndex,
                                                uint32 * pulSection );
extern uint32 USBDCDConfigGetNumAlternateInterfaces( const tConfigHeader * psConfig,
                                                     uint8 ucInterfaceNumber );
extern tInterfaceDescriptor * USBDCDConfigGetInterface( const tConfigHeader * psConfig,
                                                        uint32 ulIndex,
                                                        uint32 ulAltCfg,
                                                        uint32 * pulSection );
extern tEndpointDescriptor * USBDCDConfigGetInterfaceEndpoint(
    const tConfigHeader * psConfig,
    uint32 ulInterfaceNumber,
    uint32 ulAltCfg,
    uint32 ulIndex );
extern void USBDCDPowerStatusSet( uint32 ulIndex, uint8 ucPower );
extern tBoolean USBDCDRemoteWakeupRequest( uint32 ulIndex );

/** ***************************************************************************
 *
 * Early releases of the USB library had the following function named
 * incorrectly.  This macro ensures that any code which used the previous name
 * will still operate as expected.
 *
 *****************************************************************************/
#ifndef DEPRECATED
    #define USBCDCConfigGetInterfaceEndpoint( a, b, c, d ) \
        USBDCDConfigGetInterfaceEndpoint( ( a ), ( b ), ( c ), ( d ) )
#endif

/** ***************************************************************************
 *
 * Mark the end of the C bindings section for C++ compilers.
 *
 *****************************************************************************/
#ifdef __cplusplus
}
#endif

#endif /* __USBENUM_H__ */
