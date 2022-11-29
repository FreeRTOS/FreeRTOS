/*
 *!
 *! The protocols implemented in this file are intended to be demo quality only,
 *! and not for production devices.
 *!
 *
 * FreeRTOS+TCP V2.0.3
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://aws.amazon.com/freertos
 * https://www.FreeRTOS.org
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
