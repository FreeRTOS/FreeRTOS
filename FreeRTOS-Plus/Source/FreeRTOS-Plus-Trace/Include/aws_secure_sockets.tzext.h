/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.4.0
 * Percepio AB, www.percepio.com
 *
 * aws_secure_socket.tzext.h
 *
 * An example of a Tracealyzer extension for tracing API calls, in this case
 * for tracing selected functions in Amazon FreeRTOS/aws_secure_sockets.
 * See trcExtensions.h for information on how to use this.
 *
 * To create your own extension, first make sure to read the documentation
 * in trcExtensions.h. Then, to create an extension header file like this
 * one, you need to provide:
 *
 *  - Extension Definitions - name and event codes of the extensions.
 *
 *  - Trace Wrappers - calls the original function and traces the event.
 *
 *  - Function Redefinitions - changes the function calls to the trace wrappers.
 *
 * See the below comments for details about these definitions. Note that you
 * also need a matching .xml file for Tracealyzer to understand the data.
 * See trcExtensions.h for further information.
 *
 * Terms of Use
 * This file is part of the trace recorder library (RECORDER), which is the
 * intellectual property of Percepio AB (PERCEPIO) and provided under a
 * license as follows.
 * The RECORDER may be used free of charge for the purpose of recording data
 * intended for analysis in PERCEPIO products. It may not be used or modified
 * for other purposes without explicit permission from PERCEPIO.
 * You may distribute the RECORDER in its original source code form, assuming
 * this text (terms of use, disclaimer, copyright notice) is unchanged. You are
 * allowed to distribute the RECORDER with minor modifications intended for
 * configuration or porting of the RECORDER, e.g., to allow using it on a
 * specific processor, processor family or with a specific communication
 * interface. Any such modifications should be documented directly below
 * this comment block.
 *
 * Disclaimer
 * The RECORDER is being delivered to you AS IS and PERCEPIO makes no warranty
 * as to its use or performance. PERCEPIO does not and cannot warrant the
 * performance or results you may obtain by using the RECORDER or documentation.
 * PERCEPIO make no warranties, express or implied, as to noninfringement of
 * third party rights, merchantability, or fitness for any particular purpose.
 * In no event will PERCEPIO, its technology partners, or distributors be liable
 * to you for any consequential, incidental or special damages, including any
 * lost profits or lost savings, even if a representative of PERCEPIO has been
 * advised of the possibility of such damages, or for any claim by any third
 * party. Some jurisdictions do not allow the exclusion or limitation of
 * incidental, consequential or special damages, or the exclusion of implied
 * warranties or limitations on how long an implied warranty may last, so the
 * above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2018.
 * www.percepio.com
 ******************************************************************************/

#ifndef _AWS_SECURE_SOCKETS_TZEXT_H
#define _AWS_SECURE_SOCKETS_TZEXT_H

/***** Extension Definitions *****/

/******************************************************************************
 * <EXTENSIONPREFIX>_NAME
 * The name of the extension as a string constant. This name is used by the
 * Tracealyzer host application to find the right XML file for interpreting
 * the events. Assuming the extension name is "aws_secure_sockets", Tracealyzer
 * will look for an XML file named "aws_secure_sockets-<VERSION>.xml", first in
 * the folder of the current trace file, next in the Tracealyzer 4/cfg folder.
 * For the VERSION part, see the TRC_EXT_<ExtName>_VERSION macros below.
 *
 * Note: The extension name displayed in Tracealyzer is defined in the XML file
 * in the EventGroup element (e.g. <EventGroup name="SOCKETS">)
 *
 *****************************************************************************/
#define TRC_EXT_SOCKETS_NAME "aws_secure_sockets"

/******************************************************************************
 * <EXTENSIONPREFIX>_VERSION_MAJOR
 * <EXTENSIONPREFIX>_VERSION_MINOR
 * <EXTENSIONPREFIX>_VERSION_PATCH
 *
 * The version code of the extension (MAJOR.MINOR.PATCH)
 *
 * If you increment the version code when modifying an extension, you can still
 * show old traces recorded using an earlier version of the extension.
 *
 * Assuming the extension name is "aws_secure_sockets", and the below version
 * codes are 1 (MAJOR), 2 (MINOR), 3 (PATCH), Tracealyzer will assume the
 * corresponding XML file is named "aws_secure_sockets-v1.2.3.xml". So if then
 * view a trace recorded with extension version 1.2.2, those traces will look
 * for "aws_secure_sockets-v1.2.2.xml" instead.
 *
 * Note that major and minor are stored as 8 bit values, while patch is stored
 * using 16 bits. They are treated as unsigned integers, so the maximum values
 * are 256, 256 and 65535.
 *****************************************************************************/
#define TRC_EXT_SOCKETS_VERSION_MAJOR 1

#define TRC_EXT_SOCKETS_VERSION_MINOR 0

#define TRC_EXT_SOCKETS_VERSION_PATCH 0


/******************************************************************************
 * <EXTENSIONPREFIX>_<EVENTCODE>
 * The event codes used in the trace wrapper functions. Important that these
 * are relative to <PREFIX>_FIRST.
 *****************************************************************************/
#define EVENTCODE_SOCKETS_Connect (TRC_EXT_BASECODE + 0)

#define EVENTCODE_SOCKETS_Send (TRC_EXT_BASECODE + 1)

#define EVENTCODE_SOCKETS_Recv (TRC_EXT_BASECODE + 2)

/******************************************************************************
 * <EXTENSIONPREFIX>_COUNT
 * The number of event codes used by this extension. Should be at least 1.
 * Tracealyzer allows for events codes up to 4095.
 *****************************************************************************/
#define TRC_EXT_SOCKETS_COUNT 2


/***** Trace Wrappers *****/

#include "aws_secure_sockets.h" /* Including the original header file, so that custom data types are understood. */

static inline int32_t SOCKETS_Connect__trace( Socket_t xSocket, SocketsSockaddr_t * pxAddress, Socklen_t xAddressLength )
{
	int32_t ret = SOCKETS_Connect(xSocket, pxAddress, xAddressLength);

	// Note: The host-side xml file assumes that ret == 0 means OK, otherwise timeout/error.
	prvTraceStoreEvent3(EVENTCODE_SOCKETS_Connect, (uint32_t)xSocket, (uint32_t)pxAddress->ulAddress, (uint32_t)ret);

	return ret;
}

static inline int32_t SOCKETS_Send__trace( Socket_t xSocket, const void * pvBuffer, size_t xDataLength, uint32_t ulFlags )
{
	int32_t ret = SOCKETS_Send(xSocket, pvBuffer, xDataLength, ulFlags);

	// Note: The host-side xml file assumes that ret == 0 means OK, otherwise timeout/error.
	prvTraceStoreEvent2(EVENTCODE_SOCKETS_Send, (uint32_t)xSocket, (uint32_t)ret);

	return ret;
}


static inline int32_t SOCKETS_Recv__trace( Socket_t xSocket, void * pvBuffer, size_t xBufferLength, uint32_t ulFlags )
{
	int32_t ret = SOCKETS_Recv(xSocket, pvBuffer, xBufferLength, ulFlags);

	// Note: The host-side xml file assumes that ret == 0 means OK, otherwise timeout/error.
	prvTraceStoreEvent2(EVENTCODE_SOCKETS_Recv, (uint32_t)xSocket, (uint32_t)ret);

	return ret;
}

/***** Function Redefinitions *****/

#define SOCKETS_Connect SOCKETS_Connect__trace

#define SOCKETS_Send SOCKETS_Send__trace

#define SOCKETS_Recv SOCKETS_Recv__trace

#endif /* _AWS_SECURE_SOCKETS_TZEXT_H */
