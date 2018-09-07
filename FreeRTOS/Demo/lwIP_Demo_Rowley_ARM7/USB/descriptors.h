/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/*
	- DESCRIPTOR DEFINITIONS -
*/

/* String descriptors used during the enumeration process.
These take the form:

{
	Length of descriptor,
	Descriptor type,
	Data
}
*/

const char pxLanguageStringDescriptor[] =
{
	4,
	usbDESCRIPTOR_TYPE_STRING,
	0x09, 0x04
};

const char pxManufacturerStringDescriptor[] = 
{
	18,
	usbDESCRIPTOR_TYPE_STRING,

	'F', 0x00, 'r', 0x00, 'e', 0x00, 'e', 0x00, 'R', 0x00, 'T', 0x00, 'O', 0x00, 'S', 0x00
};

const char pxProductStringDescriptor[] = 
{
	36,
	usbDESCRIPTOR_TYPE_STRING,

	'F', 0x00, 'r', 0x00, 'e', 0x00, 'e', 0x00, 'R', 0x00, 'T', 0x00, 'O', 0x00, 'S', 0x00, ' ', 0x00, 'C', 0x00, 'D', 0x00,
	'C', 0x00, ' ', 0x00, 'D', 0x00, 'E', 0x00, 'M', 0x00, 'O', 0x00
};

const char pxConfigurationStringDescriptor[] = 
{
	38,
	usbDESCRIPTOR_TYPE_STRING,

	'C', 0x00, 'o', 0x00, 'n', 0x00, 'f', 0x00, 'i', 0x00, 'g', 0x00, 'u', 0x00, 'r', 0x00, 'a', 0x00, 't', 0x00, 'i', 0x00,
	'o', 0x00, 'n', 0x00, ' ', 0x00, 'N', 0x00, 'a', 0x00, 'm', 0x00, 'e', 0x00
};

const char pxInterfaceStringDescriptor[] = 
{
	30,
	usbDESCRIPTOR_TYPE_STRING,

	'I', 0x00, 'n', 0x00, 't', 0x00, 'e', 0x00, 'r', 0x00, 'f', 0x00, 'a', 0x00, 'c', 0x00, 'e', 0x00, ' ', 0x00, 'N', 0x00,
	'a', 0x00, 'm', 0x00, 'e', 0x00
};

/* Device should properly be 0x134A:0x9001, using 0x05F9:0xFFFF for Linux testing */
const char pxDeviceDescriptor[] = 
{
	/* Device descriptor */
	0x12,								/* bLength				*/
	0x01,								/* bDescriptorType		*/
	0x10, 0x01,							/* bcdUSBL				*/
	0x02,								/* bDeviceClass:		*/
	0x00,								/* bDeviceSubclass:		*/
	0x00,								/* bDeviceProtocol:		*/
	0x08,								/* bMaxPacketSize0		*/
	0x03, 0xEB,							/* idVendorL			*/
	0x20, 0x09,							/* idProductL			*/
	0x10, 0x01,							/* bcdDeviceL			*/
	usbMANUFACTURER_STRING,  			/* iManufacturer		*/
	usbPRODUCT_STRING,					/* iProduct				*/
	0x00,								/* SerialNumber			*/
	0x01								/* bNumConfigs			*/
};

const char pxConfigDescriptor[] = {

	/* Configuration 1 descriptor
	Here we define two interfaces (0 and 1) and a total of 3 endpoints.
	Interface 0 is a CDC Abstract Control Model interface with one interrupt-in endpoint.
	Interface 1 is a CDC Data Interface class, with a bulk-in and bulk-out endpoint.
	Endpoint 0 gets used as the CDC management element.
	*/
	0x09,				/* CbLength								*/
	0x02,				/* CbDescriptorType					  	*/
	0x43, 0x00,			/* CwTotalLength 2 EP + Control		?	*/
	0x02,				/* CbNumInterfaces			  			*/
	0x01,				/* CbConfigurationValue					*/
	usbCONFIGURATION_STRING,/* CiConfiguration					*/
	usbBUS_POWERED,		/* CbmAttributes Bus powered + Remote Wakeup*/
	0x32,				/* CMaxPower: 100mA						*/

	/* Communication Class Interface Descriptor Requirement		*/
	0x09,				/* bLength								*/
	0x04,				/* bDescriptorType						*/
	0x00,				/* bInterfaceNumber						*/
	0x00,				/* bAlternateSetting					*/
	0x01,				/* bNumEndpoints						*/
	0x02,				/* bInterfaceClass: Comm Interface Class */
	0x02,				/* bInterfaceSubclass: Abstract Control Model*/
	0x00,				/* bInterfaceProtocol					*/
	usbINTERFACE_STRING,/* iInterface							*/

	/* Header Functional Descriptor								*/
	0x05,				/* bLength								*/
	0x24,				/* bDescriptor type: CS_INTERFACE		*/
	0x00,				/* bDescriptor subtype: Header Func Desc*/
	0x10, 0x01,			/* bcdCDC:1.1  							*/

	/* ACM Functional Descriptor								*/
	0x04,				/* bFunctionLength						*/
	0x24,				/* bDescriptor type: CS_INTERFACE		*/
	0x02,				/* bDescriptor subtype: ACM Func Desc	*/
	0x00,				/* bmCapabilities: We don't support squat*/

	/* Union Functional Descriptor								*/
	0x05,				/* bFunctionLength						*/
	0x24,				/* bDescriptor type: CS_INTERFACE		*/
	0x06,				/* bDescriptor subtype: Union Func Desc	*/
	0x00,				/* bMasterInterface: CDC Interface		*/
	0x01,				/* bSlaveInterface0: Data Class Interface*/

	/* Call Management Functional Descriptor
	0 in D1 and D0 indicates that device does not handle call management*/
	0x05,				/* bFunctionLength						*/
	0x24,				/* bDescriptor type: CS_INTERFACE		*/
	0x01,				/* bDescriptor subtype: Call Management Func*/
	0x01,				/* bmCapabilities: D1 + D0				*/
	0x01,				/* bDataInterface: Data Class Interface 1*/

	/* CDC Control - Endpoint 3 descriptor
	This endpoint serves as a notification element.				*/

	0x07,				/* bLength								*/
	0x05,				/* bDescriptorType						*/
	0x83,				/* bEndpointAddress, Endpoint 03 - IN	*/
	0x03,				/* bmAttributes	  INT					*/
	0x08, 0x00,			/* wMaxPacketSize: 8 bytes		   		*/
	0xFF,				/* bInterval							*/

	/* Data Class Interface Descriptor Requirement				*/
	0x09,				/* bLength								*/
	0x04,				/* bDescriptorType						*/
	0x01,				/* bInterfaceNumber						*/
	0x00,				/* bAlternateSetting					*/
	0x02,				/* bNumEndPoints						*/
	0x0A,				/* bInterfaceClass						*/
	0x00,				/* bInterfaceSubclass					*/
	0x00,				/* bInterfaceProtocol					*/
	0x00,				/* iInterface							*/

	/* CDC Data - Endpoint 1 descriptor */
	0x07,				/* bLenght								*/
	0x05,				/* bDescriptorType						*/
	0x01,				/* bEndPointAddress, Endpoint 01 - OUT	*/
	0x02,				/* bmAttributes BULK					*/
	64,					/* wMaxPacketSize						*/
	0x00,
	0x00,				/* bInterval							*/

	/* CDC Data - Endpoint 2 descriptor */
	0x07,				/* bLength								*/
	0x05,				/* bDescriptorType						*/
	0x82,				/* bEndPointAddress, Endpoint 02 - IN	*/
	0x02,				/* bmAttributes BULK					*/
	64,					/* wMaxPacketSize						*/
	0x00,
	0x00				/* bInterval							*/
};

