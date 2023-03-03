/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */
 
#ifndef _PCAP_USB_STRUCTS_H__
#define _PCAP_USB_STRUCTS_H__

/* 
 * possible transfer mode
 */
#define URB_TRANSFER_IN   0x80
#define URB_ISOCHRONOUS   0x0
#define URB_INTERRUPT     0x1
#define URB_CONTROL       0x2
#define URB_BULK          0x3

/*
 * possible event type
 */
#define URB_SUBMIT        'S'
#define URB_COMPLETE      'C'
#define URB_ERROR         'E'

/*
 * USB setup header as defined in USB specification.
 * Appears at the front of each packet in DLT_USB captures.
 */
typedef struct _usb_setup {
	u_int8_t bmRequestType;
	u_int8_t bRequest;
	u_int16_t wValue;
	u_int16_t wIndex;
	u_int16_t wLength;
} pcap_usb_setup;


/*
 * Header prepended by linux kernel to each event.
 * Appears at the front of each packet in DLT_USB_LINUX captures.
 */
typedef struct _usb_header {
	u_int64_t id;
	u_int8_t event_type;
	u_int8_t transfer_type;
	u_int8_t endpoint_number;
	u_int8_t device_address;
	u_int16_t bus_id;
	char setup_flag;/*if !=0 the urb setup header is not present*/
	char data_flag; /*if !=0 no urb data is present*/
	int64_t ts_sec;
	int32_t ts_usec;
	int32_t status;
	u_int32_t urb_len;
	u_int32_t data_len; /* amount of urb data really present in this event*/
	pcap_usb_setup setup;
} pcap_usb_header;


#endif
