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


/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

#include "FreeRTOS_HTTP_commands.h"

const struct xWEB_COMMAND xWebCommands[ WEB_CMD_COUNT ] =
{
	{	3,     "GET",		ECMD_GET },
	{	4,    "HEAD",		ECMD_HEAD },
	{	4,    "POST",		ECMD_POST },
	{	3,     "PUT",		ECMD_PUT },
	{	6,  "DELETE",		ECMD_DELETE },
	{	5,   "TRACE",		ECMD_TRACE },
	{	7, "OPTIONS",		ECMD_OPTIONS },
	{	7, "CONNECT",		ECMD_CONNECT },
	{	5,   "PATCH",		ECMD_PATCH },
	{	4,    "UNKN",		ECMD_UNK },
};

const char *webCodename (int aCode)
{
	switch (aCode) {
	case WEB_REPLY_OK:	//  = 200,
		return "OK";
	case WEB_NO_CONTENT:    // 204
		return "No content";
	case WEB_BAD_REQUEST:	//  = 400,
		return "Bad request";
	case WEB_UNAUTHORIZED:	//  = 401,
		return "Authorization Required";
	case WEB_NOT_FOUND:	//  = 404,
		return "Not Found";
	case WEB_GONE:	//  = 410,
		return "Done";
	case WEB_PRECONDITION_FAILED:	//  = 412,
		return "Precondition Failed";
	case WEB_INTERNAL_SERVER_ERROR:	//  = 500,
		return "Internal Server Error";
	}
	return "Unknown";
}
