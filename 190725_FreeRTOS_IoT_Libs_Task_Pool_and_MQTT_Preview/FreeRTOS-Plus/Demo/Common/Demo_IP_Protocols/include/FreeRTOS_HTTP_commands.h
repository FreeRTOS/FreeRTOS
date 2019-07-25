/*
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */
#ifndef FREERTOS_HTTP_COMMANDS_H
#define	FREERTOS_HTTP_COMMANDS_H

enum {
	WEB_REPLY_OK = 200,
	WEB_NO_CONTENT = 204,
	WEB_BAD_REQUEST = 400,
	WEB_UNAUTHORIZED = 401,
	WEB_NOT_FOUND = 404,
	WEB_GONE = 410,
	WEB_PRECONDITION_FAILED = 412,
	WEB_INTERNAL_SERVER_ERROR = 500,
};

enum EWebCommand {
	ECMD_GET,
	ECMD_HEAD,
	ECMD_POST,
	ECMD_PUT,
	ECMD_DELETE,
	ECMD_TRACE,
	ECMD_OPTIONS,
	ECMD_CONNECT,
	ECMD_PATCH,
	ECMD_UNK,
};

struct xWEB_COMMAND
{
	BaseType_t xCommandLength;
	const char *pcCommandName;
	const unsigned char ucCommandType;
};

#define	WEB_CMD_COUNT	(ECMD_UNK+1)

extern const struct xWEB_COMMAND xWebCommands[WEB_CMD_COUNT];

extern const char *webCodename (int aCode);

#endif	/* FREERTOS_HTTP_COMMANDS_H */


