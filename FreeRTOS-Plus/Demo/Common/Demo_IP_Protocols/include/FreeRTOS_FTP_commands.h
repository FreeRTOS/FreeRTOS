/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#ifndef __FTPCMD_H__

#define __FTPCMD_H__

#define REPL_110              "110 Restart marker reply.\r\n"
#define REPL_120              "120 Try again in 2 minutes.\r\n"
#define REPL_125              "125 Data connection already open; transfer starting.\r\n"
#define REPL_150              "150 File status okay; about to open data connection.\r\n"
#define REPL_200              "200 NOOP command successful.\r\n"
#define REPL_200_PROGRESS     "200 NOOP: data transfer in progress.\r\n"
#define REPL_202              "202 Command not implemented, superfluous at this site.\r\n"
#define REPL_211              "221 System status, or system help reply.\r\n"
#define REPL_211_STATUS       "221-status of %s.\r\n"
#define REPL_211_END          "221 End of status.\r\n"
#define REPL_212              "212 Directory status.\r\n"
#define REPL_213              "213 File status.\r\n"
#define REPL_214              "214 Help message.\r\n"
#define REPL_214_END          "214 End Help message.\r\n"
#define REPL_215              "215 %s system type.\r\n"
#define REPL_220              "220 Service ready for new user.\r\n"
#define REPL_221              "221 Service closing control connection.\r\n"
#define REPL_225              "225 Data connection open; no transfer in progress.\r\n"
#define REPL_226              "226 Closing data connection.\r\n"
#define REPL_227              "227 Entering Passive Mode (%s,%s,%s,%s,%s,%s).\r\n"
#define REPL_227_D            "227 Entering Passive Mode (%u,%u,%u,%u,%u,%u).\r\n"
#define REPL_230              "230 User logged in, proceed.\r\n"
#define REPL_250              "250 Requested file action okay, completed.\r\n"
#define REPL_257              "257 %s created.\r\n"
/*	#define REPL_257_PWD "257 \"%s\" is current working dir.\r\n" */
#define REPL_257_PWD          "257 \"%s\"\r\n"
#define REPL_331              "331 Only anonymous user is accepted.\r\n"
#define REPL_331_ANON         "331 Anonymous login okay\r\n"
#define REPL_332              "332 Need account for login.\r\n"
#define REPL_350              "350 Requested file action pending further information.\r\n"
#define REPL_421              "421 Service not available, closing control connection.\r\n"
#define REPL_425              "425 Can't open data connection.\r\n"
#define REPL_426              "426 Connection closed; transfer aborted.\r\n"
#define REPL_450              "450 Requested file action not taken.\r\n"
#define REPL_451              "451 Requested action aborted. Local error in processing.\r\n"
#define REPL_452              "452 Requested action not taken.\r\n"
#define REPL_500              "500 Syntax error, command unrecognized.\r\n"
#define REPL_501              "501 Syntax error in parameters or arguments.\r\n"
#define REPL_502              "502 Command not implemented.\r\n"
#define REPL_503              "503 Bad sequence of commands.\r\n"
#define REPL_504              "504 Command not implemented for that parameter.\r\n"
#define REPL_530              "530 Not logged in.\r\n"
#define REPL_532              "532 Need account for storing files.\r\n"
#define REPL_550              "550 Requested action not taken.\r\n"
#define REPL_551              "551 Requested action aborted. Page type unknown.\r\n"
#define REPL_552              "552 Requested file action aborted.\r\n"
#define REPL_553              "553 Requested action not taken.\r\n"
#define REPL_553_READ_ONLY    "553 Read-only file-system.\r\n"

enum EFTPCommand
{
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

typedef struct xFTP_COMMAND
{
    BaseType_t xCommandLength;
    const char pcCommandName[ 7 ];
    const unsigned char ucCommandType;
    const unsigned char checkLogin;
    const unsigned char checkNullArg;
} FTPCommand_t;

#define FTP_CMD_COUNT    ( ECMD_UNKNOWN + 1 )

extern const FTPCommand_t xFTPCommands[ FTP_CMD_COUNT ];

#endif // __FTPCMD_H__
