/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special
 * License Arrangements heading of the FreeRTOS+TCP license information web
 * page, then it can be used under the terms of the FreeRTOS Open Source
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 *
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
 */

#ifndef FREERTOS_TCP_IP_H
#define FREERTOS_TCP_IP_H

#ifdef __cplusplus
extern "C" {
#endif

BaseType_t xProcessReceivedTCPPacket( NetworkBufferDescriptor_t *pxNetworkBuffer );

typedef enum eTCP_STATE {
	/* Comments about the TCP states are borrowed from the very useful
	 * Wiki page:
	 * http://en.wikipedia.org/wiki/Transmission_Control_Protocol */
	eCLOSED = 0u,	/* 0 (server + client) no connection state at all. */
	eTCP_LISTEN,	/* 1 (server) waiting for a connection request
						 from any remote TCP and port. */
	eCONNECT_SYN,	/* 2 (client) internal state: socket wants to send
						 a connect */
	eSYN_FIRST,		/* 3 (server) Just created, must ACK the SYN request. */
	eSYN_RECEIVED,	/* 4 (server) waiting for a confirming connection request
						 acknowledgement after having both received and sent a connection request. */
	eESTABLISHED,	/* 5 (server + client) an open connection, data received can be
						 delivered to the user. The normal state for the data transfer phase of the connection. */
	eFIN_WAIT_1,	/* 6 (server + client) waiting for a connection termination request from the remote TCP,
						 or an acknowledgement of the connection termination request previously sent. */
	eFIN_WAIT_2,	/* 7 (server + client) waiting for a connection termination request from the remote TCP. */
	eCLOSE_WAIT,	/* 8 (server + client) waiting for a connection termination request from the local user. */
	eCLOSING,		/*   (server + client) waiting for a connection termination request acknowledgement from the remote TCP. */
	eLAST_ACK,		/* 9 (server + client) waiting for an acknowledgement of the connection termination request
						 previously sent to the remote TCP
						 (which includes an acknowledgement of its connection termination request). */
	eTIME_WAIT,		/* 10 (either server or client) waiting for enough time to pass to be sure the remote TCP received the
						 acknowledgement of its connection termination request. [According to RFC 793 a connection can
						 stay in TIME-WAIT for a maximum of four minutes known as a MSL (maximum segment lifetime).] */
} eIPTCPState_t;


#ifdef __cplusplus
} // extern "C"
#endif

#endif /* FREERTOS_TCP_IP_H */













