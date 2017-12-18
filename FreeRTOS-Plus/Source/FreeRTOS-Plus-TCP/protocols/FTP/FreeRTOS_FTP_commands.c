/*
 * FreeRTOS+TCP V2.0.1
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_FTP_commands.h"

const FTPCommand_t xFTPCommands[ FTP_CMD_COUNT ] =
{
/* cmdLen cmdName[7]    cmdType  checkLogin checkNullArg */
	{ 4, "USER",		ECMD_USER, pdFALSE, pdFALSE },
	{ 4, "PASS",		ECMD_PASS, pdFALSE, pdFALSE },
	{ 4, "ACCT",		ECMD_ACCT,	pdTRUE, pdFALSE },
	{ 3,  "CWD",		ECMD_CWD,	pdTRUE, pdTRUE },
	{ 4, "CDUP",		ECMD_CDUP,	pdTRUE, pdFALSE },
	{ 4, "SMNT",		ECMD_SMNT,	pdTRUE, pdFALSE },
	{ 4, "QUIT",		ECMD_QUIT,	pdTRUE, pdFALSE },
	{ 4, "REIN",		ECMD_REIN,	pdTRUE, pdFALSE },
	{ 4, "PORT",		ECMD_PORT,	pdTRUE, pdFALSE },
	{ 4, "PASV",		ECMD_PASV,	pdTRUE, pdFALSE },
	{ 4, "TYPE",		ECMD_TYPE,	pdTRUE, pdFALSE },
	{ 4, "STRU",		ECMD_STRU,	pdTRUE, pdFALSE },
	{ 4, "MODE",		ECMD_MODE,	pdTRUE, pdFALSE },
	{ 4, "RETR",		ECMD_RETR,	pdTRUE, pdTRUE },
	{ 4, "STOR",		ECMD_STOR,	pdTRUE, pdTRUE },
	{ 4, "STOU",		ECMD_STOU,	pdTRUE, pdFALSE },
	{ 4, "APPE",		ECMD_APPE,	pdTRUE, pdFALSE },
	{ 4, "ALLO",		ECMD_ALLO,	pdTRUE, pdFALSE },
	{ 4, "REST",		ECMD_REST,	pdTRUE, pdFALSE },
	{ 4, "RNFR",		ECMD_RNFR,	pdTRUE, pdTRUE },
	{ 4, "RNTO",		ECMD_RNTO,	pdTRUE, pdTRUE },
	{ 4, "ABOR",		ECMD_ABOR,	pdTRUE, pdFALSE },
	{ 4, "SIZE",		ECMD_SIZE,	pdTRUE, pdTRUE },
	{ 4, "MDTM",		ECMD_MDTM,	pdTRUE, pdTRUE },
	{ 4, "DELE",		ECMD_DELE,	pdTRUE, pdTRUE },
	{ 3,  "RMD",		ECMD_RMD,	pdTRUE, pdTRUE },
	{ 3,  "MKD",		ECMD_MKD,	pdTRUE, pdTRUE },
	{ 3,  "PWD",		ECMD_PWD,	pdTRUE, pdFALSE },
	{ 4, "LIST",		ECMD_LIST,	pdTRUE, pdFALSE },
	{ 4, "NLST",		ECMD_NLST,	pdTRUE, pdFALSE },
	{ 4, "SITE",		ECMD_SITE,	pdTRUE, pdFALSE },
	{ 4, "SYST",		ECMD_SYST,	pdFALSE, pdFALSE },
	{ 4, "FEAT",		ECMD_FEAT,	pdFALSE, pdFALSE },
	{ 4, "STAT",		ECMD_STAT,	pdTRUE, pdFALSE },
	{ 4, "HELP",		ECMD_HELP,	pdFALSE, pdFALSE },
	{ 4, "NOOP",		ECMD_NOOP,	pdFALSE, pdFALSE },
	{ 4, "EMPT",		ECMD_EMPTY,	pdFALSE, pdFALSE },
	{ 4, "CLOS",		ECMD_CLOSE,	pdTRUE, pdFALSE },
	{ 4, "UNKN",		ECMD_UNKNOWN, pdFALSE, pdFALSE },
};
