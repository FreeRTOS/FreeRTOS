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

#ifndef	__FTPCMD_H__

#define	__FTPCMD_H__

#define REPL_110 "110 Restart marker reply.\r\n"
#define REPL_120 "120 Try again in 2 minutes.\r\n"
#define REPL_125 "125 Data connection already open; transfer starting.\r\n"
#define REPL_150 "150 File status okay; about to open data connection.\r\n"
#define REPL_200 "200 NOOP command successful.\r\n"
#define REPL_200_PROGRESS "200 NOOP: data transfer in progress.\r\n"
#define REPL_202 "202 Command not implemented, superfluous at this site.\r\n"
#define REPL_211 "221 System status, or system help reply.\r\n"
#define REPL_211_STATUS "221-status of %s.\r\n"
#define REPL_211_END "221 End of status.\r\n"
#define REPL_212 "212 Directory status.\r\n"
#define REPL_213 "213 File status.\r\n"
#define REPL_214 "214 Help message.\r\n"
#define REPL_214_END "214 End Help message.\r\n"
#define REPL_215 "215 %s system type.\r\n"
#define REPL_220 "220 Service ready for new user.\r\n"
#define REPL_221 "221 Service closing control connection.\r\n"
#define REPL_225 "225 Data connection open; no transfer in progress.\r\n"
#define REPL_226 "226 Closing data connection.\r\n"
#define REPL_227 "227 Entering Passive Mode (%s,%s,%s,%s,%s,%s).\r\n"
#define REPL_227_D "227 Entering Passive Mode (%u,%u,%u,%u,%u,%u).\r\n"
#define REPL_230 "230 User logged in, proceed.\r\n"
#define REPL_250 "250 Requested file action okay, completed.\r\n"
#define REPL_257 "257 %s created.\r\n"
//	#define REPL_257_PWD "257 \"%s\" is current working dir.\r\n"
#define REPL_257_PWD "257 \"%s\"\r\n"
#define REPL_331 "331 Only anonymous user is accepted.\r\n"
#define REPL_331_ANON "331 Anonymous login okay\r\n"
#define REPL_332 "332 Need account for login.\r\n"
#define REPL_350 "350 Requested file action pending further information.\r\n"
#define REPL_421 "421 Service not available, closing control connection.\r\n"
#define REPL_425 "425 Can't open data connection.\r\n"
#define REPL_426 "426 Connection closed; transfer aborted.\r\n"
#define REPL_450 "450 Requested file action not taken.\r\n"
#define REPL_451 "451 Requested action aborted. Local error in processing.\r\n"
#define REPL_452 "452 Requested action not taken.\r\n"
#define REPL_500 "500 Syntax error, command unrecognized.\r\n"
#define REPL_501 "501 Syntax error in parameters or arguments.\r\n"
#define REPL_502 "502 Command not implemented.\r\n"
#define REPL_503 "503 Bad sequence of commands.\r\n"
#define REPL_504 "504 Command not implemented for that parameter.\r\n"
#define REPL_530 "530 Not logged in.\r\n"
#define REPL_532 "532 Need account for storing files.\r\n"
#define REPL_550 "550 Requested action not taken.\r\n"
#define REPL_551 "551 Requested action aborted. Page type unknown.\r\n"
#define REPL_552 "552 Requested file action aborted.\r\n"
#define REPL_553 "553 Requested action not taken.\r\n"
#define REPL_553_READ_ONLY "553 Read-only file-system.\r\n"

enum EFTPCommand {
	ECMD_USER,
	ECMD_PASS,
	ECMD_ACCT,
	ECMD_CWD,
	ECMD_CDUP,
	ECMD_SMNT,
	ECMD_QUIT,
	ECMD_REIN,
	ECMD_PORT,
	ECMD_PASV,
	ECMD_TYPE,
	ECMD_STRU,
	ECMD_MODE,
	ECMD_RETR,
	ECMD_STOR,
	ECMD_STOU,
	ECMD_APPE,
	ECMD_ALLO,
	ECMD_REST,
	ECMD_RNFR,
	ECMD_RNTO,
	ECMD_ABOR,
	ECMD_SIZE,
	ECMD_MDTM,
	ECMD_DELE,
	ECMD_RMD,
	ECMD_MKD,
	ECMD_PWD,
	ECMD_LIST,
	ECMD_NLST,
	ECMD_SITE,
	ECMD_SYST,
	ECMD_FEAT,
	ECMD_STAT,
	ECMD_HELP,
	ECMD_NOOP,
	ECMD_EMPTY,
	ECMD_CLOSE,
	ECMD_UNKNOWN,
};

typedef struct xFTP_COMMAND {
	BaseType_t xCommandLength;
	const char pcCommandName[7];
	const unsigned char ucCommandType;
	const unsigned char checkLogin;
	const unsigned char checkNullArg;
} FTPCommand_t;

#define	FTP_CMD_COUNT	(ECMD_UNKNOWN+1)

extern const FTPCommand_t xFTPCommands[ FTP_CMD_COUNT ];

#endif	// __FTPCMD_H__
