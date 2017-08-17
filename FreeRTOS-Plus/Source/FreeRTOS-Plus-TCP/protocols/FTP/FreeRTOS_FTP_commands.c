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
