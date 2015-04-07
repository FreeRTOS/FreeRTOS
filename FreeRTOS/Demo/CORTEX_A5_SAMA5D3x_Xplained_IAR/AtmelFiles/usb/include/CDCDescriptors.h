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

/** \file
 *
 *  Definitions and classes for USB CDC class descriptors.
 */

#ifndef _CDCDESCRIPTORS_H_
#define _CDCDESCRIPTORS_H_
/** \addtogroup usb_cdc
 *@{
 */

/*----------------------------------------------------------------------------
 *         Includes
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/** \addtogroup usb_cdc_ver USB CDC Specification Release Numbers
 *      @{
 * This section list the CDC Spec. Release Numbers.
 * - \ref CDCGenericDescriptor_CDC1_10
 */
 
/** Identify CDC specification version 1.10. */
#define CDCGenericDescriptor_CDC1_10                            0x0110
/**     @}*/

/** \addtogroup usb_cdc_desc_type CDC Descriptro Types
 *      @{
 * This section lists CDC descriptor types.
 * - \ref CDCGenericDescriptor_INTERFACE
 * - \ref CDCGenericDescriptor_ENDPOINT
 */
/**Indicates that a CDC descriptor applies to an interface. */
#define CDCGenericDescriptor_INTERFACE                          0x24
/** Indicates that a CDC descriptor applies to an endpoint. */
#define CDCGenericDescriptor_ENDPOINT                           0x25
/**     @}*/

/** \addtogroup usb_cdc_desc_subtype CDC Descriptor Subtypes
 *      @{
 * This section lists CDC descriptor sub types
 * - \ref CDCGenericDescriptor_HEADER
 * - \ref CDCGenericDescriptor_CALLMANAGEMENT
 * - \ref CDCGenericDescriptor_ABSTRACTCONTROLMANAGEMENT
 * - \ref CDCGenericDescriptor_UNION
 */

/** Header functional descriptor subtype. */
#define CDCGenericDescriptor_HEADER                             0x00
/** Call management functional descriptor subtype. */
#define CDCGenericDescriptor_CALLMANAGEMENT                     0x01
/** Abstract control management descriptor subtype. */
#define CDCGenericDescriptor_ABSTRACTCONTROLMANAGEMENT          0x02
/** Union descriptor subtype. */
#define CDCGenericDescriptor_UNION                              0x06
/**    @}*/

/** \addtogroup usb_cdc_descriptor USB CDC Device Descriptor Values
 *  @{
 * This section lists the values for CDC Device Descriptor.
 * - \ref CDCDeviceDescriptor_CLASS
 * - \ref CDCDeviceDescriptor_SUBCLASS
 * - \ref CDCDeviceDescriptor_PROTOCOL
 */
/** Device class code when using the CDC class. */
#define CDCDeviceDescriptor_CLASS               0x02
/** Device subclass code when using the CDC class. */
#define CDCDeviceDescriptor_SUBCLASS            0x00
/** Device protocol code when using the CDC class. */
#define CDCDeviceDescriptor_PROTOCOL            0x00
/** @}*/

/** \addtogroup usb_cdc_if_desc USB CDC Communication Interface Descriptor
 *  @{
 * This section lists the values for CDC Communication Interface Descriptor.
 * - \ref CDCCommunicationInterfaceDescriptor_CLASS
 * - \ref CDCCommunicationInterfaceDescriptor_ABSTRACTCONTROLMODEL
 * - \ref CDCCommunicationInterfaceDescriptor_NOPROTOCOL
 */
/** Interface class code for a CDC communication class interface. */
#define CDCCommunicationInterfaceDescriptor_CLASS                   0x02
/** Interface subclass code for an Abstract Control Model interface descriptor.
 */
#define CDCCommunicationInterfaceDescriptor_ABSTRACTCONTROLMODEL    0x02
/** Interface protocol code when a CDC communication interface does not
    implemenent any particular protocol. */
#define CDCCommunicationInterfaceDescriptor_NOPROTOCOL              0x00
/** @}*/

/** \addtogroup usb_cdc_data_if USB CDC Data Interface Values
 *  @{
 * This section lists the values for CDC Data Interface Descriptor.
 * - \ref CDCDataInterfaceDescriptor_CLASS
 * - \ref CDCDataInterfaceDescriptor_SUBCLASS
 * - \ref CDCDataInterfaceDescriptor_NOPROTOCOL
 */
 
/** Interface class code for a data class interface. */
#define CDCDataInterfaceDescriptor_CLASS        0x0A
/** Interface subclass code for a data class interface. */
#define CDCDataInterfaceDescriptor_SUBCLASS     0x00
/** Protocol code for a data class interface which does not implement any
    particular protocol. */
#define CDCDataInterfaceDescriptor_NOPROTOCOL   0x00
/** @}*/

/** \addtogroup usb_cdc_cb_man_desc USB CDC CallManagement Capabilities
 *  @{
 * This section lists CDC CallManagement Capabilities.
 * - \ref CDCCallManagementDescriptor_SELFCALLMANAGEMENT
 * - \ref CDCCallManagementDescriptor_DATACALLMANAGEMENT
 */
/** Device handles call management itself. */
#define CDCCallManagementDescriptor_SELFCALLMANAGEMENT      (1 << 0)
/** Device can exchange call management information over a Data class interface.
 */
#define CDCCallManagementDescriptor_DATACALLMANAGEMENT      (1 << 1)
/** @}*/

/** \addtogroup usb_cdc_acm USB CDC ACM Capabilities
 *  @{
 *
 * This section lists the capabilities of the CDC ACM.
 * - \ref CDCAbstractControlManagementDescriptor_COMMFEATURE
 * - \ref CDCAbstractControlManagementDescriptor_LINE
 * - \ref CDCAbstractControlManagementDescriptor_SENDBREAK
 * - \ref CDCAbstractControlManagementDescriptor_NETWORKCONNECTION
 */
 
/** Device supports the request combination of SetCommFeature, ClearCommFeature
    and GetCommFeature. */
#define CDCAbstractControlManagementDescriptor_COMMFEATURE          (1 << 0)
/** Device supports the request combination of SetLineCoding, GetLineCoding and
    SetControlLineState. */
#define CDCAbstractControlManagementDescriptor_LINE                 (1 << 1)
/** Device supports the SendBreak request. */
#define CDCAbstractControlManagementDescriptor_SENDBREAK            (1 << 2)
/** Device supports the NetworkConnection notification. */
#define CDCAbstractControlManagementDescriptor_NETWORKCONNECTION    (1 << 3)
/** @}*/

/*----------------------------------------------------------------------------
 *         Types
 *----------------------------------------------------------------------------*/
#pragma pack(1)
#if defined   ( __CC_ARM   ) /* Keil ¦ÌVision 4 */
#elif defined ( __ICCARM__ ) /* IAR Ewarm */
#define __attribute__(...)
#define __packed__  packed
#elif defined (  __GNUC__  ) /* GCC CS3 */
#define __packed__  aligned(1)
#endif
/**
 * \typedef CDCHeaderDescriptor
 * \brief Marks the beginning of the concatenated set of functional descriptors
 *        for the interface.
 */
typedef struct _CDCHeaderDescriptor {

    /** Size of this descriptor in bytes. */
    uint8_t bFunctionLength;
    /** Descriptor type . */
    uint8_t bDescriptorType;
    /** Descriptor sub-type . */
    uint8_t bDescriptorSubtype;
    /** USB CDC specification release number. */
    uint16_t bcdCDC;

} __attribute__ ((__packed__)) CDCHeaderDescriptor; /* GCC */

/**
 * \typedef CDCUnionDescriptor
 * \brief Describes the relationship between a group of interfaces that can
 *        be considered to form a functional unit.
 */
typedef struct _CDCUnionDescriptor {

    /** Size of the descriptor in bytes. */
    uint8_t bFunctionLength;
    /** Descriptor type . */
    uint8_t bDescriptorType;
    /** Descriptor subtype . */
    uint8_t bDescriptorSubtype;
    /** Number of the master interface for this union. */
    uint8_t bMasterInterface;
    /** Number of the first slave interface for this union. */
    uint8_t bSlaveInterface0;

} __attribute__ ((__packed__)) CDCUnionDescriptor; /* GCC */

/**
 * \typedef CDCCallManagementDescriptor
 * \brief Describes the processing of calls for the communication class
 *        interface.
 */
typedef struct _CDCCallManagementDescriptor {

    /** Size of this descriptor in bytes. */
    uint8_t bFunctionLength;
    /** Descriptor type . */
    uint8_t bDescriptorType;
    /** Descriptor sub-type . */
    uint8_t bDescriptorSubtype;
    /** Configuration capabilities
        \sa usb_cdc_cb_man_desc CDC CallManagement Capabilities. */
    uint8_t bmCapabilities;
    /** Interface number of the data class interface used for call management
        (optional). */
    uint8_t bDataInterface;

} __attribute__ ((__packed__)) CDCCallManagementDescriptor; /* GCC */

/**
 * \typedef CDCAbstractControlManagementDescriptor
 * \brief Describes the command supported by the communication interface class
 *        with the Abstract Control Model subclass code.
 */
typedef struct _CDCAbstractControlManagementDescriptor {

    /** Size of this descriptor in bytes. */
    uint8_t bFunctionLength;
    /** Descriptor type . */
    uint8_t bDescriptorType;
    /** Descriptor subtype . */
    uint8_t bDescriptorSubtype;
    /** Configuration capabilities.
        \sa usb_cdc_acm CDC ACM Capabilities. */
    uint8_t bmCapabilities;

} __attribute__ ((__packed__)) CDCAbstractControlManagementDescriptor; /* GCC */

#pragma pack()

/*----------------------------------------------------------------------------
 *         Functions
 *----------------------------------------------------------------------------*/


/**@}*/
#endif /* #ifndef _CDCDESCRIPTORS_H_ */

