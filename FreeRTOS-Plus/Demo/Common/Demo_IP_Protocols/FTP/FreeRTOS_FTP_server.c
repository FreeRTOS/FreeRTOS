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

/*
 *!
 *! The protocols implemented in this file are intended to be demo quality only,
 *! and not for production devices.
 *!
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "portmacro.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Stream_Buffer.h"

/* FreeRTOS Protocol includes. */
#include "FreeRTOS_FTP_commands.h"
#include "FreeRTOS_TCP_server.h"
#include "FreeRTOS_server_private.h"

/* Remove the whole file if FTP is not supported. */
#if ( ipconfigUSE_FTP == 1 )

    #ifndef HTTP_SERVER_BACKLOG
        #define HTTP_SERVER_BACKLOG    ( 12 )
    #endif

    #if !defined( ARRAY_SIZE )
        #define ARRAY_SIZE( x )    ( BaseType_t ) ( sizeof( x ) / sizeof( x )[ 0 ] )
    #endif

    #if defined( __WIN32__ ) && !defined( ipconfigFTP_FS_USES_BACKSLASH )
        #define ipconfigFTP_FS_USES_BACKSLASH    1
    #endif

/* Some defines to make the code more readbale */
    #define pcCOMMAND_BUFFER    pxClient->pxParent->pcCommandBuffer
    #define pcNEW_DIR           pxClient->pxParent->pcNewDir
    #define pcFILE_BUFFER       pxClient->pxParent->pcFileBuffer

/* This FTP server will only do binary transfers */
    #define TMODE_BINARY        1
    #define TMODE_ASCII         2
    #define TMODE_7BITS         3
    #define TMODE_8BITS         4

/* Ascii character definitions. */
    #define ftpASCII_CR         13
    #define ftpASCII_LF         10

    #if defined( FTP_WRITES_ALIGNED ) || defined( ipconfigFTP_WRITES_ALIGNED )
        #error Name change : please rename the define to the new name 'ipconfigFTP_ZERO_COPY_ALIGNED_WRITES'
    #endif

/*
 * ipconfigFTP_ZERO_COPY_ALIGNED_WRITES : experimental optimisation option.
 * If non-zero, receiving data will be done with the zero-copy method and also
 * writes to disk will be done with sector-alignment as much as possible.
 */
    #ifndef ipconfigFTP_ZERO_COPY_ALIGNED_WRITES
        #define ipconfigFTP_ZERO_COPY_ALIGNED_WRITES    0
    #endif

/*
 * This module only has 2 public functions:
 */
    BaseType_t xFTPClientWork( TCPClient_t * pxClient );
    void vFTPClientDelete( TCPClient_t * pxClient );

/*
 * Process a single command.
 */
    static BaseType_t prvProcessCommand( FTPClient_t * pxClient,
                                         BaseType_t xIndex,
                                         char * pcRestCommand );

/*
 * Create a socket for a data connection to the FTP client.
 */
    static BaseType_t prvTransferConnect( FTPClient_t * pxClient,
                                          BaseType_t xDoListen );

/*
 * Either call listen() or connect() to start the transfer connection.
 */
    static BaseType_t prvTransferStart( FTPClient_t * pxClient );

/*
 * See if the socket has got connected or disconnected. Close the socket if
 * necessary.
 */
    static void prvTransferCheck( FTPClient_t * pxClient );

/*
 * Close the data socket and issue some informative logging.
 */
    static void prvTransferCloseSocket( FTPClient_t * pxClient );

/*
 * Close the file handle (pxReadHandle or pxWriteHandle).
 */
    static void prvTransferCloseFile( FTPClient_t * pxClient );

/*
 * Close a directory (-handle).
 */
    static void prvTransferCloseDir( FTPClient_t * pxClient );

/*
 * Translate a string (indicating a transfer type) to a number.
 */
    static BaseType_t prvGetTransferType( const char * pcType );

    #if ( ipconfigHAS_PRINTF != 0 )

/*
 * For nice logging: write an amount (number of bytes), e.g. 3512200 as
 * "3.45 MB"
 */
        static const char * pcMkSize( uint32_t ulAmount,
                                      char * pcBuffer,
                                      BaseType_t xBufferSize );
    #endif

    #if ( ipconfigHAS_PRINTF != 0 )

/*
 * Calculate the average as bytes-per-second, when amount and milliseconds
 * are known.
 */
        static uint32_t ulGetAverage( uint32_t ulAmount,
                                      TickType_t xDeltaMs );
    #endif

/*
 * A port command looks like: PORT h1,h2,h3,h4,p1,p2. Parse it and translate it
 * to an IP-address and a port number.
 */
    static UBaseType_t prvParsePortData( const char * pcCommand,
                                         uint32_t * pulIPAddress );

/*
 * CWD: Change current working directory.
 */

    static BaseType_t prvChangeDir( FTPClient_t * pxClient,
                                    char * pcDirectory );

/*
 * RNFR: Rename from ...
 */
    static BaseType_t prvRenameFrom( FTPClient_t * pxClient,
                                     const char * pcFileName );

/*
 * RNTO: Rename to ...
 */
    static BaseType_t prvRenameTo( FTPClient_t * pxClient,
                                   const char * pcFileName );

/*
 * SITE: Change file permissions.
 */
    static BaseType_t prvSiteCmd( FTPClient_t * pxClient,
                                  char * pcRestCommand );

/*
 * DELE: Delete a file.
 */
    static BaseType_t prvDeleteFile( FTPClient_t * pxClient,
                                     char * pcFileName );

/*
 * SIZE: get the size of a file (xSendDate = 0).
 * MDTM: get data and time properties (xSendDate = 1).
 */
    static BaseType_t prvSizeDateFile( FTPClient_t * pxClient,
                                       char * pcFileName,
                                       BaseType_t xSendDate );

/*
 * MKD: Make / create a directory (xDoRemove = 0).
 * RMD: Remove a directory (xDoRemove = 1).
 */
    static BaseType_t prvMakeRemoveDir( FTPClient_t * pxClient,
                                        const char * pcDirectory,
                                        BaseType_t xDoRemove );

/*
 * The next three commands: LIST, RETR and STOR all require a data socket.
 * The data connection is either started with a 'PORT' or a 'PASV' command.
 * Each of the commands has a prepare- (Prep) and a working- (Work) function.
 * The Work function should be called as long as the data socket is open, and
 * there is data to be transmitted.
 */

/*
 * LIST: Send a directory listing in Unix style.
 */
    static BaseType_t prvListSendPrep( FTPClient_t * pxClient );
    static BaseType_t prvListSendWork( FTPClient_t * pxClient );

/*
 * RETR: Send a file to the FTP client.
 */
    static BaseType_t prvRetrieveFilePrep( FTPClient_t * pxClient,
                                           char * pcFileName );
    static BaseType_t prvRetrieveFileWork( FTPClient_t * pxClient );

/*
 * STOR: Receive a file from the FTP client and store it.
 */
    static BaseType_t prvStoreFilePrep( FTPClient_t * pxClient,
                                        char * pcFileName );
    static BaseType_t prvStoreFileWork( FTPClient_t * pxClient );

/*
 * Print/format a single directory entry in Unix style.
 */
    static BaseType_t prvGetFileInfoStat( FF_DirEnt_t * pxEntry,
                                          char * pcLine,
                                          BaseType_t xMaxLength );

/*
 * Send a reply to a socket, either the command- or the data-socket.
 */
    static BaseType_t prvSendReply( Socket_t xSocket,
                                    const char * pcBuffer,
                                    BaseType_t xLength );

/*
 * Prepend the root directory (if any), plus the current working directory
 * (always), to get an absolute path.
 */
    BaseType_t xMakeAbsolute( FTPClient_t * pxClient,
                              char * pcBuffer,
                              BaseType_t xBufferLength,
                              const char * pcPath );

/*
 *
 ####### ##### ######        #     #                ##
 #   ## # # #  #    #       #     #                 #
 #        #    #    #       #     #                 #
 #        #    #    #       #  #  #  ####  ### ##   #    #
 #####    #    #####        #  #  # #    #  # #  #  #   #
 #   #    #    #            #  #  # #    #  ##   #  ####
 #        #    #             ## ##  #    #  #       #   #
 #        #    #             ## ##  #    #  #       #    #
 ####     #### ####           ## ##   ####  ####    ##   ##
 ####
 *	xFTPClientWork()
 *	will be called by FreeRTOS_TCPServerWork(), after select has expired().
 *	FD_ISSET will not be used.  This work function will always be called at
 *	regular intervals, and also after a select() event has occurred.
 */
    BaseType_t xFTPClientWork( TCPClient_t * pxTCPClient )
    {
        FTPClient_t * pxClient = ( FTPClient_t * ) pxTCPClient;
        BaseType_t xRc;

        if( pxClient->bits.bHelloSent == pdFALSE_UNSIGNED )
        {
            BaseType_t xLength;

            pxClient->bits.bHelloSent = pdTRUE_UNSIGNED;

            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                "220 Welcome to the FreeRTOS+TCP FTP server\r\n" );
            prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
        }

        /* Call recv() in a non-blocking way, to see if there is an FTP command
         * sent to this server. */
        xRc = FreeRTOS_recv( pxClient->xSocket, ( void * ) pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), 0 );

        if( xRc > 0 )
        {
            BaseType_t xIndex;
            const FTPCommand_t * pxCommand;
            char * pcRestCommand;

            if( xRc < ( BaseType_t ) sizeof( pcCOMMAND_BUFFER ) )
            {
                pcCOMMAND_BUFFER[ xRc ] = '\0';
            }

            while( xRc && ( ( pcCOMMAND_BUFFER[ xRc - 1 ] == ftpASCII_CR ) || ( pcCOMMAND_BUFFER[ xRc - 1 ] == ftpASCII_LF ) ) )
            {
                pcCOMMAND_BUFFER[ --xRc ] = '\0';
            }

            /* Now iterate through a list of FTP commands, and look for a match. */
            pxCommand = xFTPCommands;
            pcRestCommand = pcCOMMAND_BUFFER;

            for( xIndex = 0; xIndex < FTP_CMD_COUNT - 1; xIndex++, pxCommand++ )
            {
                BaseType_t xLength;

                /* The length of each command is stored as well, just to be a bit
                 * quicker here. */
                xLength = pxCommand->xCommandLength;

                if( ( xRc >= xLength ) && ( memcmp( ( const void * ) pxCommand->pcCommandName, ( const void * ) pcCOMMAND_BUFFER, xLength ) == 0 ) )
                {
                    /* A match with an existing command is found.  Skip any
                     * whitespace to get the first parameter. */
                    pcRestCommand += xLength;

                    while( ( *pcRestCommand == ' ' ) || ( *pcRestCommand == '\t' ) )
                    {
                        pcRestCommand++;
                    }

                    break;
                }
            }

            /* If the command received was not recognised, xIndex will point to a
             * fake entry called 'ECMD_UNKNOWN'. */
            prvProcessCommand( pxClient, xIndex, pcRestCommand );
        }
        else if( xRc < 0 )
        {
            /* The connection will be closed and the client will be deleted. */
            FreeRTOS_printf( ( "xFTPClientWork: xRc = %ld\n", xRc ) );
        }

        /* Does it have an open data connection? */
        if( pxClient->xTransferSocket != FREERTOS_NO_SOCKET )
        {
            /* See if the connection has changed. */
            prvTransferCheck( pxClient );

            /* "pcConnectionAck" contains a string like:
             * "Response:	150 Accepted data connection from 192.168.2.3:6789"
             * The socket can only be used once this acknowledgement has been sent. */
            if( ( pxClient->xTransferSocket != FREERTOS_NO_SOCKET ) && ( pxClient->pcConnectionAck[ 0 ] == '\0' ) )
            {
                BaseType_t xClientRc = 0;

                if( pxClient->bits1.bDirHasEntry )
                {
                    /* Still listing a directory. */
                    xClientRc = prvListSendWork( pxClient );
                }
                else if( pxClient->pxReadHandle != NULL )
                {
                    /* Sending a file. */
                    xClientRc = prvRetrieveFileWork( pxClient );
                }
                else if( pxClient->pxWriteHandle != NULL )
                {
                    /* Receiving a file. */
                    xClientRc = prvStoreFileWork( pxClient );
                }

                if( xClientRc < 0 )
                {
                    prvTransferCloseSocket( pxClient );
                    prvTransferCloseFile( pxClient );
                }
            }
        }

        return xRc;
    }
/*-----------------------------------------------------------*/

    static void prvTransferCloseDir( FTPClient_t * pxClient )
    {
        /* Nothing to close for +FAT. */
        ( void ) pxClient;
    }
/*-----------------------------------------------------------*/

    void vFTPClientDelete( TCPClient_t * pxTCPClient )
    {
        FTPClient_t * pxClient = ( FTPClient_t * ) pxTCPClient;

        /* Close any directory-listing-handles (not used by +FAT ). */
        prvTransferCloseDir( pxClient );
        /* Close the data-socket. */
        prvTransferCloseSocket( pxClient );
        /* Close any open file handle. */
        prvTransferCloseFile( pxClient );

        /* Close the FTP command socket */
        if( pxClient->xSocket != FREERTOS_NO_SOCKET )
        {
            FreeRTOS_FD_CLR( pxClient->xSocket, pxClient->pxParent->xSocketSet, eSELECT_ALL );
            FreeRTOS_closesocket( pxClient->xSocket );
            pxClient->xSocket = FREERTOS_NO_SOCKET;
        }
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvProcessCommand( FTPClient_t * pxClient,
                                         BaseType_t xIndex,
                                         char * pcRestCommand )
    {
        const FTPCommand_t * pxFTPCommand = &( xFTPCommands[ xIndex ] );
        const char * pcMyReply = NULL;
        BaseType_t xResult = 0;

        if( ( pxFTPCommand->ucCommandType != ECMD_PASS ) && ( pxFTPCommand->ucCommandType != ECMD_PORT ) )
        {
            FreeRTOS_printf( ( "       %s %s\n", pxFTPCommand->pcCommandName, pcRestCommand ) );
        }

        if( ( pxFTPCommand->checkLogin != pdFALSE ) && ( pxClient->bits.bLoggedIn == pdFALSE_UNSIGNED ) )
        {
            pcMyReply = REPL_530; /* Please first log in. */
        }
        else if( ( pxFTPCommand->checkNullArg != pdFALSE ) && ( ( pcRestCommand == NULL ) || ( pcRestCommand[ 0 ] == '\0' ) ) )
        {
            pcMyReply = REPL_501; /* Command needs a parameter. */
        }

        if( pcMyReply == NULL )
        {
            switch( pxFTPCommand->ucCommandType )
            {
                case ECMD_USER: /* User. */
                    /* User name has been entered, expect password. */
                    pxClient->bits.bStatusUser = pdTRUE_UNSIGNED;

                    #if ( ipconfigFTP_HAS_USER_PASSWORD_HOOK != 0 ) /*_RB_ Needs defaulting and adding to the web documentation. */
                    {
                        /* Save the user name in 'pcFileName'. */
                        snprintf( pxClient->pcFileName, sizeof( pxClient->pcFileName ), "%s", pcRestCommand );

                        /* The USER name is presented to the application.  The function
                         * may return a const string like "331 Please enter your
                         * password\r\n". */
                        pcMyReply = pcApplicationFTPUserHook( pxClient->pcFileName );

                        if( pcMyReply == NULL )
                        {
                            pcMyReply = REPL_331_ANON;
                        }
                    }
                    #else /* if ( ipconfigFTP_HAS_USER_PASSWORD_HOOK != 0 ) */
                    {
                        /* No password checks, any password will be accepted. */
                        pcMyReply = REPL_331_ANON;
                    }
                    #endif /* ipconfigFTP_HAS_USER_PASSWORD_HOOK != 0 */

                    #if ( ipconfigFTP_HAS_USER_PROPERTIES_HOOK != 0 ) /*_RB_ Needs defaulting and adding to the web documentation. */
                    {
                        FTPUserProperties_t xProperties;

                        xProperties.pcRootDir = pxClient->pcRootDir;
                        xProperties.xReadOnly = pdFALSE;
                        xProperties.usPortNumber = pxClient->usClientPort;
                        vApplicationFTPUserPropertiesHook( pxClient->pcFileName, &( xProperties ) );

                        if( xProperties.pcRootDir != NULL )
                        {
                            pxClient->pcRootDir = xProperties.pcRootDir;
                        }

                        pxClient->bits.bReadOnly = ( xProperties.xReadOnly != pdFALSE_UNSIGNED );
                    }
                    #endif /* ipconfigFTP_HAS_USER_PROPERTIES_HOOK */
                    break;

                case ECMD_PASS: /* Password. */
                    pxClient->ulRestartOffset = 0;

                    if( pxClient->bits.bStatusUser == pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_503; /* "503 Bad sequence of commands.\r\n". */
                    }
                    else
                    {
                        BaseType_t xAllow;

                        pxClient->bits.bStatusUser = pdFALSE_UNSIGNED;
                        #if ( ipconfigFTP_HAS_USER_PASSWORD_HOOK != 0 )
                        {
                            xAllow = xApplicationFTPPasswordHook( pxClient->pcFileName, pcRestCommand );
                        }
                        #else
                        {
                            xAllow = 1;
                        }
                        #endif /* ipconfigFTP_HAS_USER_PASSWORD_HOOK */

                        if( xAllow > 0 )
                        {
                            pxClient->bits.bLoggedIn = pdTRUE_UNSIGNED; /* Client has now logged in. */
                            pcMyReply = "230 OK.  Current directory is /\r\n";
                        }
                        else
                        {
                            pcMyReply = "530 Login incorrect\r\n"; /* 530 Login incorrect. */
                        }

                        strcpy( pxClient->pcCurrentDir, ( const char * ) "/" );
                    }

                    break;

                case ECMD_SYST: /* System. */
                    snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "215 UNIX Type: L8\r\n" );
                    pcMyReply = pcCOMMAND_BUFFER;
                    break;

                case ECMD_PWD: /* Get working directory. */
                    xMakeRelative( pxClient, pcFILE_BUFFER, sizeof( pcFILE_BUFFER ), pxClient->pcCurrentDir );
                    snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), REPL_257_PWD, pcFILE_BUFFER );
                    pcMyReply = pcCOMMAND_BUFFER;
                    break;

                case ECMD_REST:

                    if( pxClient->bits.bReadOnly != pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_553_READ_ONLY;
                    }
                    else
                    {
                        const char * pcPtr = pcRestCommand;

                        while( *pcPtr == ' ' )
                        {
                            pcPtr++;
                        }

                        if( ( *pcPtr >= '0' ) && ( *pcPtr <= '9' ) )
                        {
                            sscanf( pcPtr, "%lu", &pxClient->ulRestartOffset );
                            snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                      "350 Restarting at %lu. Send STORE or RETRIEVE\r\n", pxClient->ulRestartOffset );
                            pcMyReply = pcCOMMAND_BUFFER;
                        }
                        else
                        {
                            pcMyReply = REPL_500; /* 500 Syntax error, command unrecognised. */
                        }
                    }

                    break;

                case ECMD_NOOP: /* NOP operation */

                    if( pxClient->xTransferSocket != FREERTOS_NO_SOCKET )
                    {
                        pcMyReply = REPL_200_PROGRESS;
                    }
                    else
                    {
                        pcMyReply = REPL_200;
                    }

                    break;

                case ECMD_TYPE: /* Ask or set transfer type. */
                   {
                       /* e.g. "TYPE I" for Images (binary). */
                       BaseType_t xType = prvGetTransferType( pcRestCommand );

                       if( xType < 0 )
                       {
                           /* TYPE not recognised. */
                           pcMyReply = REPL_500;
                       }
                       else
                       {
                           pxClient->xTransType = xType;
                           pcMyReply = REPL_200;
                       }
                   }
                   break;

                case ECMD_PASV: /* Enter passive mode. */

                    /* Connect passive: Server will listen() and wait for a connection.
                     * Start up a new data connection with 'xDoListen' set to true. */
                    if( prvTransferConnect( pxClient, pdTRUE ) != pdTRUE )
                    {
                        pcMyReply = REPL_502;
                    }
                    else
                    {
                        uint32_t ulIP;
                        uint16_t ulPort;
                        struct freertos_sockaddr xLocalAddress;
                        struct freertos_sockaddr xRemoteAddress;

                        FreeRTOS_GetLocalAddress( pxClient->xTransferSocket, &xLocalAddress );
                        FreeRTOS_GetRemoteAddress( pxClient->xSocket, &xRemoteAddress );

                        #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
                        {
                            ulIP = FreeRTOS_ntohl( xLocalAddress.sin_address.ulIP_IPv4 );
                            pxClient->ulClientIP = FreeRTOS_ntohl( xRemoteAddress.sin_address.ulIP_IPv4 );
                        }
                        #else
                        {
                            ulIP = FreeRTOS_ntohl( xLocalAddress.sin_addr );
                            pxClient->ulClientIP = FreeRTOS_ntohl( xRemoteAddress.sin_addr );
                        }
                        #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

                        ulPort = FreeRTOS_ntohs( xLocalAddress.sin_port );

                        pxClient->usClientPort = FreeRTOS_ntohs( xRemoteAddress.sin_port );

                        /* REPL_227_D "227 Entering Passive Mode (%d,%d,%d,%d,%d,%d). */
                        snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), REPL_227_D,
                                  ( unsigned ) ulIP >> 24,
                                  ( unsigned ) ( ulIP >> 16 ) & 0xFF,
                                  ( unsigned ) ( ulIP >> 8 ) & 0xFF,
                                  ( unsigned ) ulIP & 0xFF,
                                  ( unsigned ) ulPort >> 8,
                                  ( unsigned ) ulPort & 0xFF );

                        pcMyReply = pcCOMMAND_BUFFER;
                    }

                    break;

                case ECMD_PORT: /* Active connection to the client. */

                    /* The client uses this command to tell the server to what
                     * client-side port the server should contact; use of this command
                     * indicates an active data transfer. e.g. PORT 192,168,1,2,4,19. */
                   {
                       uint32_t ulIPAddress = 0;
                       UBaseType_t uxPort;

                       uxPort = prvParsePortData( pcRestCommand, &ulIPAddress );
                       FreeRTOS_printf( ( "       PORT %lxip:%ld\n", ulIPAddress, uxPort ) );

                       if( uxPort == 0u )
                       {
                           pcMyReply = REPL_501;
                       }
                       else if( prvTransferConnect( pxClient, pdFALSE ) != pdTRUE )
                       {
                           /* Call prvTransferConnect() with 'xDoListen' = false for an
                            * active connect(). */
                           pcMyReply = REPL_501;
                       }
                       else
                       {
                           pxClient->usClientPort = ( uint16_t ) uxPort;
                           pxClient->ulClientIP = ulIPAddress;
                           FreeRTOS_printf( ( "Client address %lxip:%lu\n", ulIPAddress, uxPort ) );
                           pcMyReply = REPL_200;
                       }
                   }
                   break;

                case ECMD_CWD: /* Change current working directory. */
                    prvChangeDir( pxClient, pcRestCommand );
                    break;

                case ECMD_RNFR:

                    if( pxClient->bits.bReadOnly != pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_553_READ_ONLY;
                    }
                    else
                    {
                        prvRenameFrom( pxClient, pcRestCommand );
                    }

                    break;

                case ECMD_RNTO:

                    if( pxClient->bits.bInRename == pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_503; /* "503 Bad sequence of commands. */
                    }
                    else
                    {
                        prvRenameTo( pxClient, pcRestCommand );
                    }

                    break;

                case ECMD_SITE: /* Set file permissions */

                    if( pxClient->bits.bReadOnly != pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_553_READ_ONLY;
                    }
                    else if( prvSiteCmd( pxClient, pcRestCommand ) == pdFALSE )
                    {
                        pcMyReply = REPL_202;
                    }

                    break;

                case ECMD_DELE:

                    if( pxClient->bits.bReadOnly != pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_553_READ_ONLY;
                    }
                    else
                    {
                        prvDeleteFile( pxClient, pcRestCommand );
                    }

                    break;

                case ECMD_MDTM:
                    prvSizeDateFile( pxClient, pcRestCommand, pdTRUE );
                    break;

                case ECMD_SIZE:

                    if( pxClient->pxWriteHandle != NULL )
                    {
                        /* This SIZE query is probably about a file which is now being
                         * received.  If so, return the value of pxClient->ulRecvBytes,
                         * pcRestCommand points to 'pcCommandBuffer', make it free by
                         * copying it to pcNewDir. */

                        xMakeAbsolute( pxClient, pcNEW_DIR, sizeof( pcNEW_DIR ), pcRestCommand );

                        if( strcmp( pcNEW_DIR, pcRestCommand ) == 0 )
                        {
                            BaseType_t xCount;

                            for( xCount = 0; xCount < 3 && pxClient->pxWriteHandle; xCount++ )
                            {
                                prvStoreFileWork( pxClient );
                            }

                            if( pxClient->pxWriteHandle != NULL )
                            {
                                /* File being queried is still open, return number of
                                 * bytes received until now. */
                                snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "213 %lu\r\n", pxClient->ulRecvBytes );
                                pcMyReply = pcCOMMAND_BUFFER;
                            } /* otherwise, do a normal stat(). */
                        }

                        strcpy( pcRestCommand, pcNEW_DIR );
                    }

                    if( pcMyReply == NULL )
                    {
                        prvSizeDateFile( pxClient, pcRestCommand, pdFALSE );
                    }

                    break;

                case ECMD_MKD:
                case ECMD_RMD:

                    if( pxClient->bits.bReadOnly != pdFALSE_UNSIGNED )
                    {
                        pcMyReply = REPL_553_READ_ONLY;
                    }
                    else
                    {
                        prvMakeRemoveDir( pxClient, pcRestCommand, pxFTPCommand->ucCommandType == ECMD_RMD );
                    }

                    break;

                case ECMD_CDUP:
                    prvChangeDir( pxClient, ".." );
                    break;

                case ECMD_QUIT:
                    prvSendReply( pxClient->xSocket, REPL_221, 0 );
                    pxClient->bits.bLoggedIn = pdFALSE_UNSIGNED;
                    break;

                case ECMD_LIST:
                case ECMD_RETR:
                case ECMD_STOR:

                    if( ( pxClient->xTransferSocket == FREERTOS_NO_SOCKET ) &&
                        ( ( pxFTPCommand->ucCommandType != ECMD_STOR ) ||
                          ( pxClient->bits1.bEmptyFile == pdFALSE_UNSIGNED ) ) )
                    {
                        /* Sending "425 Can't open data connection." :
                         * Before receiving any of these commands, there must have been a
                         * PORT or PASV command, which causes the creation of a data socket. */

                        /* There is one exception: a STOR command is received while the
                         * data connection has already been closed.  This is tested with the
                         * 'bEmptyFile' flag. */
                        pcMyReply = REPL_425;
                    }
                    else
                    {
                        /* In case an empty file was received ( bits1.bEmptyFile ), the
                         * transfer socket never delivered any data.  Check if the transfer
                         * socket is still open: */
                        if( pxClient->xTransferSocket != FREERTOS_NO_SOCKET )
                        {
                            prvTransferCheck( pxClient );
                        }

                        switch( pxFTPCommand->ucCommandType )
                        {
                            case ECMD_LIST:
                                prvListSendPrep( pxClient );
                                break;

                            case ECMD_RETR:
                                prvRetrieveFilePrep( pxClient, pcRestCommand );
                                break;

                            case ECMD_STOR:

                                if( pxClient->bits.bReadOnly != pdFALSE_UNSIGNED )
                                {
                                    pcMyReply = REPL_553_READ_ONLY;
                                }
                                else
                                {
                                    prvStoreFilePrep( pxClient, pcRestCommand );

                                    if( pxClient->bits1.bEmptyFile != pdFALSE_UNSIGNED )
                                    {
                                        /* Although the 'xTransferSocket' is closed already,
                                         * call this function just for the logging. */
                                        prvTransferCloseSocket( pxClient );

                                        /* Close an empty file. */
                                        prvTransferCloseFile( pxClient );
                                    }
                                }

                                break;
                        }
                    }

                    break;

                case ECMD_FEAT:
                   {
                       static const char pcFeatAnswer[] =
                           "211-Features:\x0a"

                           /* The MDTM command is only allowed when
                            * there is support for date&time. */
                           #if ( ffconfigTIME_SUPPORT != 0 )
                               " MDTM\x0a"
                           #endif
                           " REST STREAM\x0a"
                           " SIZE\x0d\x0a"
                           "211 End\x0d\x0a";
                       pcMyReply = pcFeatAnswer;
                   }
                   break;

                case ECMD_UNKNOWN:
                    FreeRTOS_printf( ( "ftp::processCmd: Cmd %s unknown\n", pcRestCommand ) );
                    pcMyReply = REPL_500;
                    break;
            }
        }

        if( pxFTPCommand->ucCommandType != ECMD_RNFR )
        {
            pxClient->bits.bInRename = pdFALSE_UNSIGNED;
        }

        if( pcMyReply != NULL )
        {
            xResult = prvSendReply( pxClient->xSocket, pcMyReply, strlen( pcMyReply ) );
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvTransferConnect( FTPClient_t * pxClient,
                                          BaseType_t xDoListen )
    {
        Socket_t xSocket;
        BaseType_t xResult;

        /* Open a socket for a data connection with the FTP client.
         * Happens after a PORT or a PASV command. */

        /* Make sure the previous socket is deleted and flags reset */
        prvTransferCloseSocket( pxClient );

        pxClient->bits1.bEmptyFile = pdFALSE_UNSIGNED;

        xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );

        if( ( xSocket != FREERTOS_NO_SOCKET ) && ( xSocket != FREERTOS_INVALID_SOCKET ) )
        {
            BaseType_t xSmallTimeout = pdMS_TO_TICKS( 100 );
            struct freertos_sockaddr xAddress;

            #if ( ipconfigFTP_TX_BUFSIZE > 0 )
                WinProperties_t xWinProps;
            #endif

            #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
            {
                xAddress.sin_address.ulIP_IPv4 = FreeRTOS_GetIPAddress(); /* Single NIC, currently not used */
            }
            #else
            {
                xAddress.sin_addr = FreeRTOS_GetIPAddress(); /* Single NIC, currently not used */
            }
            #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

            xAddress.sin_port = FreeRTOS_htons( 0 ); /* Bind to any available port number */
            xAddress.sin_family = FREERTOS_AF_INET;

            BaseType_t xBindResult;
            xBindResult = FreeRTOS_bind( xSocket, &xAddress, sizeof( xAddress ) );

            if( xBindResult != 0 )
            {
                FreeRTOS_printf( ( "FreeRTOS_bind() failed\n" ) );
                return xBindResult;
            }

            #if ( ipconfigFTP_TX_BUFSIZE > 0 )
            {
                /* Fill in the buffer and window sizes that will be used by the
                 * socket. */
                xWinProps.lTxBufSize = ipconfigFTP_TX_BUFSIZE;
                xWinProps.lTxWinSize = ipconfigFTP_TX_WINSIZE;
                xWinProps.lRxBufSize = ipconfigFTP_RX_BUFSIZE;
                xWinProps.lRxWinSize = ipconfigFTP_RX_WINSIZE;

                /* Set the window and buffer sizes. */
                FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &xWinProps, sizeof( xWinProps ) );
            }
            #endif /* if ( ipconfigFTP_TX_BUFSIZE > 0 ) */

            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, ( void * ) &xSmallTimeout, sizeof( BaseType_t ) );
            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, ( void * ) &xSmallTimeout, sizeof( BaseType_t ) );

            /* The same instance of the socket will be used for the connection and
             * data transport. */
            if( xDoListen != pdFALSE )
            {
                BaseType_t xTrueValue = pdTRUE;
                FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_REUSE_LISTEN_SOCKET, ( void * ) &xTrueValue, sizeof( xTrueValue ) );
            }

            pxClient->bits1.bIsListen = xDoListen;
            pxClient->xTransferSocket = xSocket;

            if( xDoListen != pdFALSE )
            {
                FreeRTOS_FD_SET( xSocket, pxClient->pxParent->xSocketSet, eSELECT_EXCEPT | eSELECT_READ );
                /* Calling FreeRTOS_listen( ) */
                xResult = prvTransferStart( pxClient );

                if( xResult >= 0 )
                {
                    xResult = pdTRUE;
                }
            }
            else
            {
                FreeRTOS_FD_SET( xSocket, pxClient->pxParent->xSocketSet, eSELECT_EXCEPT | eSELECT_READ | eSELECT_WRITE );
                xResult = pdTRUE;
            }
        }
        else
        {
            FreeRTOS_printf( ( "FreeRTOS_socket() failed\n" ) );
            xResult = -pdFREERTOS_ERRNO_ENOMEM;
        }

        /* An active socket (PORT) should connect() later. */
        return xResult;
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvTransferStart( FTPClient_t * pxClient )
    {
        BaseType_t xResult;

        /* A transfer socket has been opened, now either call listen() for 'PASV'
         * or connect() for the 'PORT' command. */
        if( pxClient->bits1.bIsListen != pdFALSE_UNSIGNED )
        {
            xResult = FreeRTOS_listen( pxClient->xTransferSocket, 1 );
        }
        else
        {
            struct freertos_sockaddr xAddress;

            #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
            {
                xAddress.sin_address.ulIP_IPv4 = FreeRTOS_htonl( pxClient->ulClientIP );
            }
            #else
            {
                xAddress.sin_addr = FreeRTOS_htonl( pxClient->ulClientIP );
            }
            #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */


            xAddress.sin_port = FreeRTOS_htons( pxClient->usClientPort );
            xAddress.sin_family = FREERTOS_AF_INET;

            /* Start an active connection for this data socket */
            xResult = FreeRTOS_connect( pxClient->xTransferSocket, &xAddress, sizeof( xAddress ) );
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    static void prvTransferCheck( FTPClient_t * pxClient )
    {
        BaseType_t xRxSize;

        /* A data transfer is busy. Check if there are changes in connectedness. */
        xRxSize = FreeRTOS_rx_size( pxClient->xTransferSocket );

        if( pxClient->bits1.bClientConnected == pdFALSE_UNSIGNED )
        {
            /* The time to receive a small file can be so short, that we don't even
             * see that the socket gets connected and disconnected. Therefore, check
             * the sizeof of the RX buffer. */
            {
                struct freertos_sockaddr xAddress;
                Socket_t xNexSocket;
                socklen_t xSocketLength = sizeof( xAddress );

                if( pxClient->bits1.bIsListen != pdFALSE_UNSIGNED )
                {
                    xNexSocket = FreeRTOS_accept( pxClient->xTransferSocket, &xAddress, &xSocketLength );

                    if( ( ( xNexSocket != FREERTOS_NO_SOCKET ) && ( xNexSocket != FREERTOS_INVALID_SOCKET ) ) ||
                        ( xRxSize > 0 ) )
                    {
                        pxClient->bits1.bClientConnected = pdTRUE_UNSIGNED;
                    }
                }
                else
                {
                    if( ( FreeRTOS_issocketconnected( pxClient->xTransferSocket ) > 0 ) ||
                        ( xRxSize > 0 ) )
                    {
                        pxClient->bits1.bClientConnected = pdTRUE_UNSIGNED;
                    }
                }

                if( pxClient->bits1.bClientConnected != pdFALSE_UNSIGNED )
                {
                    pxClient->bits1.bEmptyFile = pdFALSE_UNSIGNED;
                    #if ( ipconfigHAS_PRINTF != 0 )
                    {
                        struct freertos_sockaddr xRemoteAddress, xLocalAddress;
                        FreeRTOS_GetRemoteAddress( pxClient->xTransferSocket, &xRemoteAddress );
                        FreeRTOS_GetLocalAddress( pxClient->xTransferSocket, &xLocalAddress );
                        FreeRTOS_printf( ( "%s Connected from %u to %u\n",
                                           pxClient->bits1.bIsListen != pdFALSE_UNSIGNED ? "PASV" : "PORT",
                                           ( unsigned ) FreeRTOS_ntohs( xLocalAddress.sin_port ),
                                           ( unsigned ) FreeRTOS_ntohs( xRemoteAddress.sin_port ) ) );
                    }
                    #endif /* ipconfigHAS_PRINTF */
                    FreeRTOS_FD_CLR( pxClient->xTransferSocket, pxClient->pxParent->xSocketSet, eSELECT_WRITE );
                    FreeRTOS_FD_SET( pxClient->xTransferSocket, pxClient->pxParent->xSocketSet, eSELECT_READ | eSELECT_EXCEPT );
                }
            }
        }

        if( pxClient->bits1.bClientConnected != pdFALSE_UNSIGNED )
        {
            if( pxClient->pcConnectionAck[ 0 ] != '\0' )
            {
                BaseType_t xLength;
                BaseType_t xRemotePort;
                struct freertos_sockaddr xRemoteAddress;

                FreeRTOS_GetRemoteAddress( pxClient->xTransferSocket, &xRemoteAddress );
                xRemotePort = FreeRTOS_ntohs( xRemoteAddress.sin_port );

                /* Tell on the command port 21 we have a data connection */
                xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                    pxClient->pcConnectionAck, pxClient->ulClientIP, xRemotePort );

                prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
                pxClient->pcConnectionAck[ 0 ] = '\0';
            }

            if( ( FreeRTOS_issocketconnected( pxClient->xTransferSocket ) == pdFALSE ) && ( FreeRTOS_rx_size( pxClient->xTransferSocket ) == 0 ) )
            {
                prvTransferCloseSocket( pxClient );
                prvTransferCloseFile( pxClient );
            }
        }
    }
/*-----------------------------------------------------------*/

    static void prvTransferCloseSocket( FTPClient_t * pxClient )
    {
        if( pxClient->xTransferSocket != FREERTOS_NO_SOCKET )
        {
            /* DEBUGGING ONLY */
            BaseType_t xRxSize = FreeRTOS_rx_size( pxClient->xTransferSocket );

            if( xRxSize > 0 )
            {
                BaseType_t xRxSize2;
                BaseType_t xStatus;
                prvStoreFileWork( pxClient );
                xStatus = FreeRTOS_connstatus( pxClient->xTransferSocket );
                xRxSize2 = FreeRTOS_rx_size( pxClient->xTransferSocket );
                FreeRTOS_printf( ( "FTP: WARNING: %s: RX size = %ld -> %ld (%s)\n",
                                   FreeRTOS_GetTCPStateName( xStatus ),
                                   xRxSize, xRxSize2, pxClient->pcFileName ) );

                if( xRxSize2 > 1 )
                {
                    return;
                }

                /* Remove compiler warnings in case FreeRTOS_printf() is not
                 * defined. */
                ( void ) xStatus;
            }
        }

        if( ( pxClient->pxWriteHandle != NULL ) || ( pxClient->pxReadHandle != NULL ) )
        {
            BaseType_t xLength;
            char pcStrBuf[ 32 ];

            if( pxClient->bits1.bHadError == pdFALSE_UNSIGNED )
            {
                xLength = snprintf( pxClient->pcClientAck, sizeof( pxClient->pcClientAck ),
                                    "226 Closing connection %d bytes transmitted\r\n", ( int ) pxClient->ulRecvBytes );
            }
            else
            {
                xLength = snprintf( pxClient->pcClientAck, sizeof( pxClient->pcClientAck ),
                                    "451 Requested action aborted after %d bytes\r\n", ( int ) pxClient->ulRecvBytes );
            }

            /* Tell on the command socket the data connection is now closed. */
            prvSendReply( pxClient->xSocket, pxClient->pcClientAck, xLength );

            #if ( ipconfigHAS_PRINTF != 0 )
            {
                TickType_t xDelta;
                uint32_t ulAverage;
                xDelta = xTaskGetTickCount() - pxClient->xStartTime;
                ulAverage = ulGetAverage( pxClient->ulRecvBytes, xDelta );

                FreeRTOS_printf( ( "FTP: %s: '%s' %lu Bytes (%s/sec)\n",
                                   pxClient->pxReadHandle ? "sent" : "recv",
                                   pxClient->pcFileName,
                                   pxClient->ulRecvBytes,
                                   pcMkSize( ulAverage, pcStrBuf, sizeof( pcStrBuf ) ) ) );
            }
            #endif /* if ( ipconfigHAS_PRINTF != 0 ) */
        }

        if( pxClient->xTransferSocket != FREERTOS_NO_SOCKET )
        {
            FreeRTOS_FD_CLR( pxClient->xTransferSocket, pxClient->pxParent->xSocketSet, eSELECT_ALL );
            FreeRTOS_closesocket( pxClient->xTransferSocket );
            pxClient->xTransferSocket = FREERTOS_NO_SOCKET;

            if( pxClient->ulRecvBytes == 0ul )
            {
                /* Received zero bytes: an empty file */
                pxClient->bits1.bEmptyFile = pdTRUE_UNSIGNED;
            }
            else
            {
                pxClient->bits1.bEmptyFile = pdFALSE_UNSIGNED;
            }
        }

        pxClient->bits1.bIsListen = pdFALSE_UNSIGNED;
        pxClient->bits1.bDirHasEntry = pdFALSE_UNSIGNED;
        pxClient->bits1.bClientConnected = pdFALSE_UNSIGNED;
        pxClient->bits1.bHadError = pdFALSE_UNSIGNED;
    }
/*-----------------------------------------------------------*/

    static void prvTransferCloseFile( FTPClient_t * pxClient )
    {
        if( pxClient->pxWriteHandle != NULL )
        {
            ff_fclose( pxClient->pxWriteHandle );
            pxClient->pxWriteHandle = NULL;
            #if ( ipconfigFTP_HAS_RECEIVED_HOOK != 0 )
            {
                vApplicationFTPReceivedHook( pxClient->pcFileName, pxClient->ulRecvBytes, pxClient );
            }
            #endif
        }

        if( pxClient->pxReadHandle != NULL )
        {
            ff_fclose( pxClient->pxReadHandle );
            pxClient->pxReadHandle = NULL;
        }

        /* These two field are only used for logging / file-statistics */
        pxClient->ulRecvBytes = 0ul;
        pxClient->xStartTime = 0ul;
    }
/*-----------------------------------------------------------*/

/**
 * Guess the transfer type, given the client requested type.
 * Actually in unix there is no difference between binary and
 * ascii mode when we work with file descriptors.
 * If #type is not recognized as a valid client request, -1 is returned.
 */
    static BaseType_t prvGetTransferType( const char * pcType )
    {
        BaseType_t xResult = -1;

        if( pcType != NULL )
        {
            BaseType_t xLength = strlen( pcType );

            if( xLength == 0 )
            {
                return -1;
            }

            switch( pcType[ 0 ] )
            {
                case 'I':
                    xResult = TMODE_BINARY;
                    break;

                case 'A':
                    xResult = TMODE_ASCII;
                    break;

                case 'L':

                    if( xLength >= 3 )
                    {
                        if( pcType[ 2 ] == '7' )
                        {
                            xResult = TMODE_7BITS;
                        }
                        else if( pcType[ 2 ] == '8' )
                        {
                            xResult = TMODE_7BITS;
                        }
                    }

                    break;
            }
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigHAS_PRINTF != 0 )
        #define SIZE_1_GB    ( 1024ul * 1024ul * 1024ul )
        #define SIZE_1_MB    ( 1024ul * 1024ul )
        #define SIZE_1_KB    ( 1024ul )

        static const char * pcMkSize( uint32_t ulAmount,
                                      char * pcBuffer,
                                      BaseType_t xBufferSize )
        {
            uint32_t ulGB, ulMB, ulKB, ulByte;

            ulGB = ( ulAmount / SIZE_1_GB );
            ulAmount -= ( ulGB * SIZE_1_GB );
            ulMB = ( ulAmount / SIZE_1_MB );
            ulAmount -= ( ulMB * SIZE_1_MB );
            ulKB = ( ulAmount / SIZE_1_KB );
            ulAmount -= ( ulKB * SIZE_1_KB );
            ulByte = ( ulAmount );

            if( ulGB != 0ul )
            {
                snprintf( pcBuffer, xBufferSize, "%lu.%02lu GB", ulGB, ( 100 * ulMB ) / SIZE_1_KB );
            }
            else if( ulMB != 0ul )
            {
                snprintf( pcBuffer, xBufferSize, "%lu.%02lu MB", ulMB, ( 100 * ulKB ) / SIZE_1_KB );
            }
            else if( ulKB != 0ul )
            {
                snprintf( pcBuffer, xBufferSize, "%lu.%02lu KB", ulKB, ( 100 * ulByte ) / SIZE_1_KB );
            }
            else
            {
                snprintf( pcBuffer, xBufferSize, "%lu bytes", ulByte );
            }

            return pcBuffer;
        }
        /*-----------------------------------------------------------*/
    #endif /* ipconfigHAS_PRINTF != 0 */

    #if ( ipconfigHAS_PRINTF != 0 )
        static uint32_t ulGetAverage( uint32_t ulAmount,
                                      TickType_t xDeltaMs )
        {
            uint32_t ulAverage;

            /* Get the average amount of bytes per seconds. Ideally this is
             * calculated by Multiplying with 1000 and dividing by milliseconds:
             *  ulAverage = ( 1000ul * ulAmount ) / xDeltaMs;
             * Now get a maximum precision, while avoiding an arithmetic overflow:
             */
            if( xDeltaMs == 0ul )
            {
                /* Time is zero, there is no average  */
                ulAverage = 0ul;
            }
            else if( ulAmount >= ( ~0ul / 10ul ) )
            {
                /* More than 409 MB has been transferred, do not multiply. */
                ulAverage = ( ulAmount / ( xDeltaMs / 1000ul ) );
            }
            else if( ulAmount >= ( ~0ul / 100ul ) )
            {
                /* Between 409 and 41 MB has been transferred, can multiply by 10. */
                ulAverage = ( ( ulAmount * 10ul ) / ( xDeltaMs / 100ul ) );
            }
            else if( ulAmount >= ( ~0ul / 1000ul ) )
            {
                /* Between 4.1 MB and 41 has been transferred, can multiply by 100. */
                ulAverage = ( ( ulAmount * 100ul ) / ( xDeltaMs / 10ul ) );
            }
            else
            {
                /* Less than 4.1 MB: can multiply by 1000. */
                ulAverage = ( ( ulAmount * 1000ul ) / xDeltaMs );
            }

            return ulAverage;
        }
        /*-----------------------------------------------------------*/
    #endif /* ipconfigHAS_PRINTF != 0 */

    static UBaseType_t prvParsePortData( const char * pcCommand,
                                         uint32_t * pulIPAddress )
    {
/*_HT_ Using 'unsigned' here because when sscanf() sees '%u', it expects a pointer to 'unsigned'.
 * Not sure about the sscanf() format for UBaseType_t ? */
        unsigned h1, h2, h3, h4, p1, p2;
        char sep;
        UBaseType_t uxResult;

        /* Expect PORT h1,h2,h3,h4,p1,p2 */
        if( sscanf( pcCommand, "%u%c%u%c%u%c%u%c%u%c%u", &h1, &sep, &h2, &sep, &h3, &sep, &h4, &sep, &p1, &sep, &p2 ) != 11 )
        {
            uxResult = 0u;
        }
        else
        {
            /* Put in network byte order. */
            *pulIPAddress =
                ( ( uint32_t ) h1 << 24 ) |
                ( ( uint32_t ) h2 << 16 ) |
                ( ( uint32_t ) h3 << 8 ) |
                ( ( uint32_t ) h4 );
            uxResult = ( p1 << 8 ) | p2;
        }

        return uxResult;
    }
/*-----------------------------------------------------------*/

/*
 *
 ####                                  #######   #   ###
 #    #   #                              #   ##   #     #
 #    #   #                              #    #         #
 #      ######  ####  ### ##   ####      #   #  ###     #    ####
 ##      #    #    #  # #  # #    #     #####    #     #   #    #
 ##    #    #    #  ##   # ######     #   #    #     #   ######
 #    #   #    #    #  #      #          #        #     #   #
 #    #   # ## #    #  #      #   ##     #        #     #   #   ##
 ####     ##   ####  ####     ####     ####    ##### #####  ####
 ####
 */

    static BaseType_t prvStoreFilePrep( FTPClient_t * pxClient,
                                        char * pcFileName )
    {
        BaseType_t xResult;
        FF_FILE * pxNewHandle;
        size_t uxFileSize = 0ul;
        int iErrorNo;

        /* Close previous handle (if any) and reset file transfer parameters. */
        prvTransferCloseFile( pxClient );

        xMakeAbsolute( pxClient, pxClient->pcFileName, sizeof( pxClient->pcFileName ), pcFileName );

        pxNewHandle = NULL;

        if( pxClient->ulRestartOffset != 0 )
        {
            size_t uxOffset = pxClient->ulRestartOffset;
            int32_t lRc;

            pxClient->ulRestartOffset = 0ul; /* Only use 1 time. */
            pxNewHandle = ff_fopen( pxClient->pcFileName, "ab" );

            if( pxNewHandle != NULL )
            {
                uxFileSize = pxNewHandle->ulFileSize;

                if( uxOffset <= uxFileSize )
                {
                    lRc = ff_fseek( pxNewHandle, uxOffset, FF_SEEK_SET );
                }
                else
                {
                    /* Won't even try to seek after EOF */
                    lRc = -pdFREERTOS_ERRNO_EINVAL;
                }

                if( lRc != 0 )
                {
                    BaseType_t xLength;

                    xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                        "450 Seek invalid %u length %u\r\n",
                                        ( unsigned ) uxOffset, ( unsigned ) uxFileSize );

                    /* "Requested file action not taken". */
                    prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );

                    FreeRTOS_printf( ( "ftp::storeFile: create %s: Seek %u length %u\n",
                                       pxClient->pcFileName, ( unsigned ) uxOffset, ( unsigned ) uxFileSize ) );

                    ff_fclose( pxNewHandle );
                    pxNewHandle = NULL;
                }
            }
        }
        else
        {
            pxNewHandle = ff_fopen( pxClient->pcFileName, "wb" );
        }

        if( pxNewHandle == NULL )
        {
            iErrorNo = stdioGET_ERRNO();

            if( iErrorNo == pdFREERTOS_ERRNO_ENOSPC )
            {
                prvSendReply( pxClient->xSocket, REPL_552, 0 );
            }
            else
            {
                /* "Requested file action not taken". */
                prvSendReply( pxClient->xSocket, REPL_450, 0 );
            }

            FreeRTOS_printf( ( "ftp::storeFile: create %s: %s (errno %d)\n",
                               pxClient->pcFileName,
                               ( const char * ) strerror( iErrorNo ), iErrorNo ) );

            xResult = pdFALSE;
        }
        else
        {
            if( pxClient->bits1.bIsListen )
            {
                /* True if PASV is used. */
                snprintf( pxClient->pcConnectionAck, sizeof( pxClient->pcConnectionAck ),
                          "150 Accepted data connection from %%xip:%%u\r\n" );
                prvTransferCheck( pxClient );
            }
            else
            {
                BaseType_t xLength;

                xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "150 Opening BIN connection to store file\r\n" );
                prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
                pxClient->pcConnectionAck[ 0 ] = '\0';
                prvTransferStart( pxClient ); /* Now active connect. */
            }

            pxClient->pxWriteHandle = pxNewHandle;

            /* To get some statistics about the performance. */
            pxClient->xStartTime = xTaskGetTickCount();

            xResult = pdTRUE;
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigFTP_ZERO_COPY_ALIGNED_WRITES == 0 )

        static BaseType_t prvStoreFileWork( FTPClient_t * pxClient )
        {
            BaseType_t xRc, xWritten;

            /* Read from the data socket until all has been read or until a negative value
             * is returned. */
            for( ; ; )
            {
                char * pcBuffer;

                /* The "zero-copy" method: */
                xRc = FreeRTOS_recv( pxClient->xTransferSocket, ( void * ) &pcBuffer,
                                     0x20000u, FREERTOS_ZERO_COPY | FREERTOS_MSG_DONTWAIT );

                if( xRc <= 0 )
                {
                    break;
                }

                pxClient->ulRecvBytes += xRc;
                xWritten = ff_fwrite( pcBuffer, 1, xRc, pxClient->pxWriteHandle );
                FreeRTOS_recv( pxClient->xTransferSocket, ( void * ) NULL, xRc, 0 );

                if( xWritten != xRc )
                {
                    xRc = -1;
                    /* bHadError: a transfer got aborted because of an error. */
                    pxClient->bits1.bHadError = pdTRUE_UNSIGNED;
                    break;
                }
            }

            return xRc;
        }

    #else /* ipconfigFTP_ZERO_COPY_ALIGNED_WRITES != 0 */

        #if !defined( ipconfigFTP_PREFERRED_WRITE_SIZE )

/* If you store data on flash, it may be profitable to give 'ipconfigFTP_PREFERRED_WRITE_SIZE'
 * the same size as the size of the flash' erase blocks, e.g. 4KB */
            #define ipconfigFTP_PREFERRED_WRITE_SIZE    512ul
        #endif

        static BaseType_t prvStoreFileWork( FTPClient_t * pxClient )
        {
            BaseType_t xRc, xWritten;

            /* Read from the data socket until all has been read or until a negative
             * value is returned. */
            for( ; ; )
            {
                char * pcBuffer;
                UBaseType_t xStatus;

                /* The "zero-copy" method: */
                xRc = FreeRTOS_recv( pxClient->xTransferSocket, ( void * ) &pcBuffer,
                                     0x20000u, FREERTOS_ZERO_COPY | FREERTOS_MSG_DONTWAIT );

                if( xRc <= 0 )
                {
                    /* There are no data or the connection is closed. */
                    break;
                }

                xStatus = FreeRTOS_connstatus( pxClient->xTransferSocket );

                if( xStatus != eESTABLISHED )
                {
                    /* The connection is not established (any more), therefore
                     * accept any amount of bytes, probably the last few bytes. */
                }
                else
                {
                    if( xRc >= ipconfigFTP_PREFERRED_WRITE_SIZE )
                    {
                        /* More than a sector to write, round down to a multiple of
                         * PREFERRED_WRITE_SIZE bytes. */
                        xRc = ( xRc / ipconfigFTP_PREFERRED_WRITE_SIZE ) * ipconfigFTP_PREFERRED_WRITE_SIZE;
                    }
                    else
                    {
                        const StreamBuffer_t * pxBuffer = FreeRTOS_get_rx_buf( pxClient->xTransferSocket );
                        size_t uxSpace = pxBuffer->LENGTH - pxBuffer->uxTail;

                        if( uxSpace >= ipconfigFTP_PREFERRED_WRITE_SIZE )
                        {
                            /* At this moment there are les than PREFERRED_WRITE_SIZE bytes in the RX
                             * buffer, but there is space for more. Just return and
                             * wait for more. */
                            xRc = 0;
                        }
                        else
                        {
                            /* Now reading beyond the end of the circular buffer,
                             * use a normal read. */
                            pcBuffer = pcFILE_BUFFER;
                            xRc = FreeRTOS_recvcount( pxClient->xTransferSocket );
                            xRc = ( xRc / ipconfigFTP_PREFERRED_WRITE_SIZE ) * ipconfigFTP_PREFERRED_WRITE_SIZE;

                            if( xRc > 0 )
                            {
                                xRc = FreeRTOS_recv( pxClient->xTransferSocket, ( void * ) pcBuffer,
                                                     sizeof( pcFILE_BUFFER ), FREERTOS_MSG_DONTWAIT );
                            }
                        }
                    }
                }

                if( xRc == 0 )
                {
                    break;
                }

                pxClient->ulRecvBytes += xRc;

                xWritten = ff_fwrite( pcBuffer, 1, xRc, pxClient->pxWriteHandle );

                if( pcBuffer != pcFILE_BUFFER )
                {
                    FreeRTOS_recv( pxClient->xTransferSocket, ( void * ) NULL, xRc, 0 );
                }

                if( xWritten != xRc )
                {
                    xRc = -1;
                    /* bHadError: a transfer got aborted because of an error. */
                    pxClient->bits1.bHadError = pdTRUE_UNSIGNED;
                    break;
                }
            }

            return xRc;
        }

    #endif /* ipconfigFTP_ZERO_COPY_ALIGNED_WRITES */
/*-----------------------------------------------------------*/

/*
 ######                          #                           #######   #   ###
 #    #          #              #                            #   ##   #     #
 #    #          #                                           #    #         #
 #    #  ####  ###### ### ##  ###    ####  #    #  ####      #   #  ###     #    ####
 ###### #    #   #     # #  #   #   #    # #    # #    #     #####    #     #   #    #
 #  ##  ######   #     ##   #   #   ###### #    # ######     #   #    #     #   ######
 #   #  #        #     #        #   #      #    # #          #        #     #   #
 #    # #   ##   # ##  #        #   #   ##  #  #  #   ##     #        #     #   #   ##
 ###  ##  ####     ##  ####    #####  ####    ##    ####     ####    ##### #####  ####
 */
    static BaseType_t prvRetrieveFilePrep( FTPClient_t * pxClient,
                                           char * pcFileName )
    {
        BaseType_t xResult = pdTRUE;
        size_t uxFileSize;

        /* Close previous handle (if any) and reset file transfer parameters */
        prvTransferCloseFile( pxClient );

        xMakeAbsolute( pxClient, pxClient->pcFileName, sizeof( pxClient->pcFileName ), pcFileName );

        pxClient->pxReadHandle = ff_fopen( pxClient->pcFileName, "rb" );

        if( pxClient->pxReadHandle == NULL )
        {
            int iErrno = stdioGET_ERRNO();
            /* "Requested file action not taken". */
            prvSendReply( pxClient->xSocket, REPL_450, 0 );
            FreeRTOS_printf( ( "prvRetrieveFilePrep: open '%s': errno %d: %s\n",
                               pxClient->pcFileName, iErrno, ( const char * ) strerror( iErrno ) ) );
            uxFileSize = 0ul;
            xResult = pdFALSE;
        }
        else
        {
            uxFileSize = pxClient->pxReadHandle->ulFileSize;
            pxClient->uxBytesLeft = uxFileSize;

            if( pxClient->ulRestartOffset != 0ul )
            {
                size_t uxOffset = pxClient->ulRestartOffset;
                int32_t iRc;

                /* Only use 1 time. */
                pxClient->ulRestartOffset = 0;

                if( uxOffset < uxFileSize )
                {
                    iRc = ff_fseek( pxClient->pxReadHandle, uxOffset, FF_SEEK_SET );
                }
                else
                {
                    iRc = -pdFREERTOS_ERRNO_EINVAL;
                }

                if( iRc != 0 )
                {
                    BaseType_t xLength;

                    xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                        "450 Seek invalid %u length %u\r\n", ( unsigned ) uxOffset, ( unsigned ) uxFileSize );

                    /* "Requested file action not taken". */
                    prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );

                    FreeRTOS_printf( ( "prvRetrieveFilePrep: create %s: Seek %u length %u\n",
                                       pxClient->pcFileName, ( unsigned ) uxOffset, ( unsigned ) uxFileSize ) );

                    ff_fclose( pxClient->pxReadHandle );
                    pxClient->pxReadHandle = NULL;
                    xResult = pdFALSE;
                }
                else
                {
                    pxClient->uxBytesLeft = uxFileSize - pxClient->ulRestartOffset;
                }
            }
        }

        if( xResult != pdFALSE )
        {
            if( pxClient->bits1.bIsListen != pdFALSE_UNSIGNED )
            {
                /* True if PASV is used. */
                snprintf( pxClient->pcConnectionAck, sizeof( pxClient->pcConnectionAck ),
                          "150%cAccepted data connection from %%xip:%%u\r\n%s",
                          pxClient->xTransType == TMODE_ASCII ? '-' : ' ',
                          pxClient->xTransType == TMODE_ASCII ? "150 NOTE: ASCII mode requested, but binary mode used\r\n" : "" );
            }
            else
            {
                BaseType_t xLength;

                xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "150%cOpening data connection to %lxip:%u\r\n%s",
                                    pxClient->xTransType == TMODE_ASCII ? '-' : ' ',
                                    pxClient->ulClientIP,
                                    pxClient->usClientPort,
                                    pxClient->xTransType == TMODE_ASCII ? "150 NOTE: ASCII mode requested, but binary mode used\r\n" : "" );
                prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
                pxClient->pcConnectionAck[ 0 ] = '\0';
                prvTransferStart( pxClient );
            }

            /* Prepare the ACK which will be sent when all data has been sent. */
            snprintf( pxClient->pcClientAck, sizeof( pxClient->pcClientAck ), "%s", REPL_226 );

            /* To get some statistics about the performance. */
            pxClient->xStartTime = xTaskGetTickCount();

            if( uxFileSize == 0ul )
            {
                FreeRTOS_shutdown( pxClient->xTransferSocket, FREERTOS_SHUT_RDWR );
            }
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvRetrieveFileWork( FTPClient_t * pxClient )
    {
        size_t uxSpace;
        size_t uxCount, uxItemsRead;
        BaseType_t xRc = 0;
        BaseType_t xSetEvent = pdFALSE;

        do
        {
            #if ( ipconfigFTP_TX_ZERO_COPY != 0 )
                char * pcBuffer;
                BaseType_t xBufferLength;
            #endif /* ipconfigFTP_TX_ZERO_COPY */

            /* Take the lesser of the two: tx_space (number of bytes that can be
             * queued for transmission) and uxBytesLeft (the number of bytes left to
             * read from the file) */
            uxSpace = FreeRTOS_tx_space( pxClient->xTransferSocket );

            if( uxSpace == 0 )
            {
                FreeRTOS_FD_SET( pxClient->xTransferSocket, pxClient->pxParent->xSocketSet, eSELECT_WRITE | eSELECT_EXCEPT );
                xRc = FreeRTOS_select( pxClient->pxParent->xSocketSet, 200 );
                uxSpace = FreeRTOS_tx_space( pxClient->xTransferSocket );
            }

            uxCount = FreeRTOS_min_uint32( pxClient->uxBytesLeft, uxSpace );

            if( uxCount == 0 )
            {
                break;
            }

            #if ( ipconfigFTP_TX_ZERO_COPY == 0 )
            {
                if( uxCount > sizeof( pcFILE_BUFFER ) )
                {
                    uxCount = sizeof( pcFILE_BUFFER );
                }

                uxItemsRead = ff_fread( pcFILE_BUFFER, 1, uxCount, pxClient->pxReadHandle );

                if( uxItemsRead != uxCount )
                {
                    FreeRTOS_printf( ( "prvRetrieveFileWork: Got %u Expected %u\n", ( unsigned ) uxItemsRead, ( unsigned ) uxCount ) );
                    xRc = FreeRTOS_shutdown( pxClient->xTransferSocket, FREERTOS_SHUT_RDWR );
                    pxClient->uxBytesLeft = 0u;
                    break;
                }

                pxClient->uxBytesLeft -= uxCount;

                if( pxClient->uxBytesLeft == 0u )
                {
                    BaseType_t xTrueValue = 1;

                    FreeRTOS_setsockopt( pxClient->xTransferSocket, 0, FREERTOS_SO_CLOSE_AFTER_SEND, ( void * ) &xTrueValue, sizeof( xTrueValue ) );
                }

                xRc = FreeRTOS_send( pxClient->xTransferSocket, pcFILE_BUFFER, uxCount, 0 );
            }
            #else /* ipconfigFTP_TX_ZERO_COPY != 0 */
            {
                /* Use zero-copy transmission:
                 * FreeRTOS_get_tx_head() returns a direct pointer to the TX stream and
                 * set xBufferLength to know how much space there is left. */
                pcBuffer = ( char * ) FreeRTOS_get_tx_head( pxClient->xTransferSocket, &xBufferLength );

                if( ( pcBuffer != NULL ) && ( xBufferLength >= 512 ) )
                {
                    /* Will read disk data directly to the TX stream of the socket. */
                    uxCount = FreeRTOS_min_uint32( uxCount, ( uint32_t ) xBufferLength );

                    if( uxCount > ( size_t ) 0x40000u )
                    {
                        uxCount = ( size_t ) 0x40000u;
                    }
                }
                else
                {
                    /* Use the normal file i/o buffer. */
                    pcBuffer = pcFILE_BUFFER;

                    if( uxCount > sizeof( pcFILE_BUFFER ) )
                    {
                        uxCount = sizeof( pcFILE_BUFFER );
                    }
                }

                if( pxClient->uxBytesLeft >= 1024u )
                {
                    uxCount &= ~( ( size_t ) 512u - 1u );
                }

                if( uxCount <= 0u )
                {
                    /* Nothing to send after rounding down to a multiple of a sector size. */
                    break;
                }

                uxItemsRead = ff_fread( pcBuffer, 1, uxCount, pxClient->pxReadHandle );

                if( uxCount != uxItemsRead )
                {
                    FreeRTOS_printf( ( "prvRetrieveFileWork: Got %u Expected %u\n", ( unsigned ) uxItemsRead, ( unsigned ) uxCount ) );
                    xRc = FreeRTOS_shutdown( pxClient->xTransferSocket, FREERTOS_SHUT_RDWR );
                    pxClient->uxBytesLeft = 0u;
                    break;
                }

                pxClient->uxBytesLeft -= uxCount;

                if( pxClient->uxBytesLeft == 0u )
                {
                    BaseType_t xTrueValue = 1;

                    FreeRTOS_setsockopt( pxClient->xTransferSocket, 0, FREERTOS_SO_CLOSE_AFTER_SEND, ( void * ) &xTrueValue, sizeof( xTrueValue ) );
                }

                if( pcBuffer != pcFILE_BUFFER )
                {
                    pcBuffer = NULL;
                }

                xRc = FreeRTOS_send( pxClient->xTransferSocket, pcBuffer, uxCount, 0 );
            }
            #endif /* ipconfigFTP_TX_ZERO_COPY */

            if( xRc < 0 )
            {
                break;
            }

            pxClient->ulRecvBytes += xRc;

            if( pxClient->uxBytesLeft == 0u )
            {
                break;
            }
        } while( uxCount > 0u );

        if( xRc < 0 )
        {
            FreeRTOS_printf( ( "prvRetrieveFileWork: already disconnected\n" ) );
        }
        else if( pxClient->uxBytesLeft <= 0u )
        {
            BaseType_t x;

            for( x = 0; x < 5; x++ )
            {
                xRc = FreeRTOS_recv( pxClient->xTransferSocket, pcFILE_BUFFER, sizeof( pcFILE_BUFFER ), 0 );

                if( xRc < 0 )
                {
                    break;
                }
            }

/*		FreeRTOS_printf( ( "prvRetrieveFileWork: %s all sent: xRc %ld\n", pxClient->pcFileName, xRc ) ); */
        }
        else
        {
            FreeRTOS_FD_SET( pxClient->xTransferSocket, pxClient->pxParent->xSocketSet, eSELECT_WRITE );
            xSetEvent = pdTRUE;
        }

        if( xSetEvent == pdFALSE )
        {
            FreeRTOS_FD_CLR( pxClient->xTransferSocket, pxClient->pxParent->xSocketSet, eSELECT_WRITE );
        }

        return xRc;
    }
/*-----------------------------------------------------------*/

/*
 ###     #####  ####  #####
 #        #   #    # # # #
 #        #   #    #   #
 #        #   #        #
 #        #    ##      #
 #    #   #      ##    #
 #    #   #   #    #   #
 #    #   #   #    #   #
 ####### #####  ####   ####
 */
/* Prepare sending a directory LIST */
    static BaseType_t prvListSendPrep( FTPClient_t * pxClient )
    {
        BaseType_t xFindResult;
        int iErrorNo;

        if( pxClient->bits1.bIsListen != pdFALSE_UNSIGNED )
        {
            /* True if PASV is used */
            snprintf( pxClient->pcConnectionAck, sizeof( pxClient->pcConnectionAck ),
                      "150 Accepted data connection from %%xip:%%u\r\n" );
        }
        else
        {
            BaseType_t xLength;

            /* Here the FTP server is supposed to connect() */
            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                "150 Opening ASCII mode data connection to for /bin/ls \r\n" );

            prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
            /* Clear the current connection acknowledge message */
            pxClient->pcConnectionAck[ 0 ] = '\0';
            prvTransferStart( pxClient );
        }

        pxClient->xDirCount = 0;
        xMakeAbsolute( pxClient, pcNEW_DIR, sizeof( pcNEW_DIR ), pxClient->pcCurrentDir );

        xFindResult = ff_findfirst( pcNEW_DIR, &pxClient->xFindData );

        pxClient->bits1.bDirHasEntry = ( xFindResult >= 0 );

        iErrorNo = stdioGET_ERRNO();

        if( ( xFindResult < 0 ) && ( iErrorNo == pdFREERTOS_ERRNO_ENMFILE ) )
        {
            FreeRTOS_printf( ( "prvListSendPrep: Empty directory? (%s)\n", pxClient->pcCurrentDir ) );
            prvSendReply( pxClient->xTransferSocket, "total 0\r\n", 0 );
            pxClient->xDirCount++;
        }
        else if( xFindResult < 0 )
        {
            FreeRTOS_printf( ( "prvListSendPrep: rc = %ld iErrorNo = %d\n", xFindResult, iErrorNo ) );
            prvSendReply( pxClient->xSocket, REPL_451, 0 );
        }

        pxClient->pcClientAck[ 0 ] = '\0';

        return pxClient->xDirCount;
    }
/*-----------------------------------------------------------*/

    #define MAX_DIR_LIST_ENTRY_SIZE    256

    static BaseType_t prvListSendWork( FTPClient_t * pxClient )
    {
        BaseType_t xTxSpace;

        while( pxClient->bits1.bClientConnected != pdFALSE_UNSIGNED )
        {
            char * pcWritePtr = pcCOMMAND_BUFFER;
            BaseType_t xWriteLength;

            xTxSpace = FreeRTOS_tx_space( pxClient->xTransferSocket );

            if( xTxSpace > ( BaseType_t ) sizeof( pcCOMMAND_BUFFER ) )
            {
                xTxSpace = sizeof( pcCOMMAND_BUFFER );
            }

            while( ( xTxSpace >= MAX_DIR_LIST_ENTRY_SIZE ) && ( pxClient->bits1.bDirHasEntry != pdFALSE_UNSIGNED ) )
            {
                BaseType_t xLength, xEndOfDir;
                int32_t iRc;
                int iErrorNo;

                xLength = prvGetFileInfoStat( &( pxClient->xFindData.xDirectoryEntry ), pcWritePtr, xTxSpace );

                pxClient->xDirCount++;
                pcWritePtr += xLength;
                xTxSpace -= xLength;

                iRc = ff_findnext( &pxClient->xFindData );
                iErrorNo = stdioGET_ERRNO();

                xEndOfDir = ( iRc < 0 ) && ( iErrorNo == pdFREERTOS_ERRNO_ENMFILE );

                pxClient->bits1.bDirHasEntry = ( xEndOfDir == pdFALSE ) && ( iRc >= 0 );

                if( ( iRc < 0 ) && ( xEndOfDir == pdFALSE ) )
                {
                    FreeRTOS_printf( ( "prvListSendWork: %s (rc %08x)\n",
                                       ( const char * ) strerror( iErrorNo ),
                                       ( unsigned ) iRc ) );
                }
            }

            xWriteLength = ( BaseType_t ) ( pcWritePtr - pcCOMMAND_BUFFER );

            if( xWriteLength == 0 )
            {
                break;
            }

            if( pxClient->bits1.bDirHasEntry == pdFALSE_UNSIGNED )
            {
                uint32_t ulTotalCount;
                uint32_t ulFreeCount;
                uint32_t ulPercentage;

                ulTotalCount = 1;
                ulFreeCount = ff_diskfree( pxClient->pcCurrentDir, &ulTotalCount );
                ulPercentage = ( uint32_t ) ( ( 100ULL * ulFreeCount + ulTotalCount / 2 ) / ulTotalCount );

                /* Prepare the ACK which will be sent when all data has been sent. */
                snprintf( pxClient->pcClientAck, sizeof( pxClient->pcClientAck ),
                          "226-Options: -l\r\n"
                          "226-%ld matches total\r\n"
                          "226 Total %lu KB (%lu %% free)\r\n",
                          pxClient->xDirCount, ulTotalCount / 1024, ulPercentage );
            }

            if( xWriteLength )
            {
                if( pxClient->bits1.bDirHasEntry == pdFALSE_UNSIGNED )
                {
                    BaseType_t xTrueValue = 1;

                    FreeRTOS_setsockopt( pxClient->xTransferSocket, 0, FREERTOS_SO_CLOSE_AFTER_SEND, ( void * ) &xTrueValue, sizeof( xTrueValue ) );
                }

                prvSendReply( pxClient->xTransferSocket, pcCOMMAND_BUFFER, xWriteLength );
            }

            if( pxClient->bits1.bDirHasEntry == pdFALSE_UNSIGNED )
            {
                prvSendReply( pxClient->xSocket, pxClient->pcClientAck, 0 );
                break;
            }
        } /* while( pxClient->bits1.bClientConnected )  */

        return 0;
    }
/*-----------------------------------------------------------*/

    static const char * pcMonthAbbrev( BaseType_t xMonth )
    {
        static const char pcMonthList[] = "JanFebMarAprMayJunJulAugSepOctNovDec";

        if( ( xMonth < 1 ) || ( xMonth > 12 ) )
        {
            xMonth = 12;
        }

        return pcMonthList + 3 * ( xMonth - 1 );
    }
/*-----------------------------------------------------------*/

    static BaseType_t prvGetFileInfoStat( FF_DirEnt_t * pxEntry,
                                          char * pcLine,
                                          BaseType_t xMaxLength )
    {
        char date[ 16 ];
        char mode[ 11 ] = "----------";
        BaseType_t st_nlink = 1;
        const char user[ 9 ] = "freertos";
        const char group[ 8 ] = "plusfat";

/*
 *	Creates a unix-style listing, understood by most FTP clients:
 *
 * -rw-rw-r--   1 freertos FreeRTOS+FAT 10564588 Sep 01 00:17 03.  Metaharmoniks - Star (Instrumental).mp3
 * -rw-rw-r--   1 freertos FreeRTOS+FAT 19087839 Sep 01 00:17 04.  Simon Le Grec - Dimitri (Wherever U Are) (Cosmos Mix).mp3
 * -rw-rw-r--   1 freertos FreeRTOS+FAT 11100621 Sep 01 00:16 05.  D-Chill - Mistake (feat. Katy Blue).mp3
 */

        #if ( ffconfigTIME_SUPPORT == 1 )
            const FF_SystemTime_t * pxCreateTime = &( pxEntry->xCreateTime );
        #else
        #warning Do not use this.
            FF_SystemTime_t xCreateTime;
            const FF_SystemTime_t * pxCreateTime = &xCreateTime;
        #endif
        size_t ulSize = ( size_t ) pxEntry->ulFileSize;
        const char * pcFileName = pxEntry->pcFileName;

        mode[ 0 ] = ( ( pxEntry->ucAttrib & FF_FAT_ATTR_DIR ) != 0 ) ? 'd' : '-';
        #if ( ffconfigDEV_SUPPORT != 0 )
        {
            if( ( pxEntry->ucAttrib & FF_FAT_ATTR_DIR ) == 0 )
            {
                switch( pxEntry->ucIsDeviceDir )
                {
                    case FF_DEV_CHAR_DEV:
                        mode[ 0 ] = 'c';
                        break;

                    case FF_DEV_BLOCK_DEV:
                        mode[ 0 ] = 'b';
                        break;
                }
            }
        }
        #endif /* ffconfigDEV_SUPPORT != 0 */

        mode[ 1 ] = 'r'; /* Owner. */
        mode[ 2 ] = ( ( pxEntry->ucAttrib & FF_FAT_ATTR_READONLY ) != 0 ) ? '-' : 'w';
        mode[ 3 ] = '-'; /* x for executable. */

        mode[ 4 ] = 'r'; /* group. */
        mode[ 5 ] = ( ( pxEntry->ucAttrib & FF_FAT_ATTR_READONLY ) != 0 ) ? '-' : 'w';
        mode[ 6 ] = '-'; /* x for executable. */

        mode[ 7 ] = 'r'; /* world. */
        mode[ 8 ] = '-';
        mode[ 9 ] = '-'; /* x for executable. */

        if( pxCreateTime->Month && pxCreateTime->Day )
        {
            snprintf( date, sizeof( date ), "%-3.3s %02d %02d:%02d",
                      pcMonthAbbrev( pxCreateTime->Month ),
                      pxCreateTime->Day,
                      pxCreateTime->Hour,
                      pxCreateTime->Minute );
        }
        else
        {
            snprintf( date, sizeof( date ), "Jan 01 1970" );
        }

        return snprintf( pcLine, xMaxLength, "%s %3ld %-4s %-4s %8d %12s %s\r\n",
                         mode, st_nlink, user, group, ( int ) ulSize, date, pcFileName );
    }
/*-----------------------------------------------------------*/

/*
 ####  #     # #####
 #    # #     #  #   #
 #     # #     #  #    #
 #       #  #  #  #    #
 #       #  #  #  #    #
 #       #  #  #  #    #
 #     #  ## ##   #    #
 #    #  ## ##   #   #
 ####   ## ##  #####
 */
    static BaseType_t prvChangeDir( FTPClient_t * pxClient,
                                    char * pcDirectory )
    {
        BaseType_t xResult;
        BaseType_t xIsRootDir, xLength, xValid;
        BaseType_t xIsDotDir = 0;

        if( pcDirectory[ 0 ] == '.' )
        {
            if( ( pcDirectory[ 1 ] == '.' ) &&
                ( pcDirectory[ 2 ] == '\0' ) )
            {
                xIsDotDir = 2;
            }
            else if( pcDirectory[ 1 ] == '\0' )
            {
                xIsDotDir = 1;
            }
        }

        if( xIsDotDir != 0 )
        {
            strcpy( pcFILE_BUFFER, pxClient->pcCurrentDir );

            if( pcDirectory[ 1 ] == '.' )
            {
                char * p = strrchr( pcFILE_BUFFER, '/' );

                if( p != NULL )
                {
                    if( p == pcFILE_BUFFER )
                    {
                        p[ 1 ] = '\0';
                    }
                    else
                    {
                        p[ 0 ] = '\0';
                    }
                }
            }
        }
        else
        {
            if( pcDirectory[ 0 ] != '/' )
            {
                BaseType_t xCurLength;

                xCurLength = strlen( pxClient->pcCurrentDir );
                snprintf( pcFILE_BUFFER, sizeof( pcFILE_BUFFER ), "%s%s%s",
                          pxClient->pcCurrentDir,
                          pxClient->pcCurrentDir[ xCurLength - 1 ] == '/' ? "" : "/",
                          pcDirectory );
            }
            else
            {
                snprintf( pcFILE_BUFFER, sizeof( pcFILE_BUFFER ), "%s", pcDirectory );
            }
        }

        xIsRootDir = ( pcFILE_BUFFER[ 0 ] == '/' ) && ( pcFILE_BUFFER[ 1 ] == '\0' );
        xMakeAbsolute( pxClient, pcNEW_DIR, sizeof( pcNEW_DIR ), pcFILE_BUFFER );

        if( ( ( xIsRootDir == pdFALSE ) || ( FF_FS_Count() == 0 ) ) && ( ff_finddir( pcNEW_DIR ) == pdFALSE ) )
        {
            xValid = pdFALSE;
        }
        else
        {
            xValid = pdTRUE;
        }

        if( xValid == pdFALSE )
        {
            /* Get the directory cluster, if it exists. */
            FreeRTOS_printf( ( "FTP: chdir \"%s\": No such dir\n", pcNEW_DIR ) );
            /*#define REPL_550 "550 Requested action not taken.\r\n" */
            /*550 /home/hein/arch/h8300: No such file or directory */
            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                "550 %s: No such file or directory\r\n",
                                pcNEW_DIR );
            prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
            xResult = pdFALSE;
        }
        else
        {
            memcpy( pxClient->pcCurrentDir, pcNEW_DIR, sizeof( pxClient->pcCurrentDir ) );

            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "250 Changed to %s\r\n", pcNEW_DIR );
            prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
            xResult = pdTRUE;
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

/*
 ######  ##    # ####### ######
 #    # ##    #  #   ##  #    #
 #    # ##    #  #    #  #    #
 #    # ###   #  #   #   #    #
 ###### # ##  #  #####   ######
 #  ##  #  ## #  #   #   #  ##
 #   #  #   ###  #       #   #
 #    # #    ##  #       #    #
 ###  ## #    ## ####    ###  ##
 */
    static BaseType_t prvRenameFrom( FTPClient_t * pxClient,
                                     const char * pcFileName )
    {
        const char * myReply;
        FF_FILE * fh;

        xMakeAbsolute( pxClient, pxClient->pcFileName, sizeof( pxClient->pcFileName ), pcFileName );

        myReply = NULL;

        fh = ff_fopen( pxClient->pcFileName, "rb" );

        if( fh != NULL )
        {
            ff_fclose( fh );
            /* REPL_350; "350 Requested file action pending further information." */
            snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                      "350 Rename '%s' ...\r\n", pxClient->pcFileName );
            myReply = pcCOMMAND_BUFFER;
            pxClient->bits.bInRename = pdTRUE_UNSIGNED;
        }
        else if( stdioGET_ERRNO() == pdFREERTOS_ERRNO_EISDIR )
        {
            snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                      "350 Rename directory '%s' ...\r\n", pxClient->pcFileName );
            myReply = pcCOMMAND_BUFFER;
            pxClient->bits.bInRename = pdTRUE_UNSIGNED;
        }
        else
        {
            FreeRTOS_printf( ( "ftp::renameFrom[%s]\n%s\n", pxClient->pcFileName, strerror( stdioGET_ERRNO() ) ) );
            myReply = REPL_451; /* "451 Requested action aborted. Local error in processing." */
        }

        if( myReply )
        {
            prvSendReply( pxClient->xSocket, myReply, 0 );
        }

        return pdTRUE;
    }
/*-----------------------------------------------------------*/

/*
 ######  ##    # #####   ###
 #    # ##    # # # #  ## ##
 #    # ##    #   #   ##   ##
 #    # ###   #   #   #     #
 ###### # ##  #   #   #     #
 #  ##  #  ## #   #   #     #
 #   #  #   ###   #   ##   ##
 #    # #    ##   #    ## ##
 ###  ## #    ##  ####   ###
 */
    static BaseType_t prvRenameTo( FTPClient_t * pxClient,
                                   const char * pcFileName )
    {
        const char * myReply = NULL;
        int iResult;

        xMakeAbsolute( pxClient, pcNEW_DIR, sizeof( pcNEW_DIR ), pcFileName );

        /* FreeRTOS+FAT rename has an extra parameter: "remove target if already
         * exists". */
        iResult = ff_rename( pxClient->pcFileName, pcNEW_DIR, pdFALSE );

        if( iResult < 0 )
        {
            iResult = stdioGET_ERRNO();
        }
        else
        {
            iResult = 0;
        }

        switch( iResult )
        {
            case 0:
                FreeRTOS_printf( ( "ftp::renameTo[%s,%s]: Ok\n", pxClient->pcFileName, pcNEW_DIR ) );
                snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                          "250 Rename successful to '%s'\r\n", pcNEW_DIR );
                myReply = pcCOMMAND_BUFFER;
                break;

            case pdFREERTOS_ERRNO_EEXIST:

                /* the destination file already exists.
                 * "450 Requested file action not taken.\r\n"*/
                snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                          "450 Already exists '%s'\r\n", pcNEW_DIR );
                myReply = pcCOMMAND_BUFFER;
                break;

            case pdFREERTOS_ERRNO_EIO: /* FF_ERR_FILE_COULD_NOT_CREATE_DIRENT */

                /* if dirent creation failed (fatal error!).
                 * "553 Requested action not taken.\r\n" */
                FreeRTOS_printf( ( "ftp::renameTo[%s,%s]: Error creating DirEnt\n",
                                   pxClient->pcFileName, pcNEW_DIR ) );
                myReply = REPL_553;
                break;

            case pdFREERTOS_ERRNO_ENXIO:
            case pdFREERTOS_ERRNO_ENOENT:

                /* if the source file was not found.
                 * "450 Requested file action not taken.\r\n" */
                snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                          "450 No such file '%s'\r\n", pxClient->pcFileName );
                myReply = pcCOMMAND_BUFFER;
                break;

            default:
                FreeRTOS_printf( ( "ftp::renameTo[%s,%s]: %s\n", pxClient->pcFileName, pcNEW_DIR,
                                   ( const char * ) strerror( stdioGET_ERRNO() ) ) );
                myReply = REPL_451; /* "451 Requested action aborted. Local error in processing." */
                break;
        }

        prvSendReply( pxClient->xSocket, myReply, 0 );

        return pdTRUE;
    }
/*-----------------------------------------------------------*/

/*
 ####    #
 #    #   #     #
 #    #         #
 #      ###   ######  ####
 ##      #     #    #    #
 ##    #     #    ######
 #    #   #     #    #
 #    #   #     # ## #   ##
 ####  #####    ##   ####
 */
    static BaseType_t prvSiteCmd( FTPClient_t * pxClient,
                                  char * pcRestCommand )
    {
        ( void ) pxClient;
        ( void ) pcRestCommand;

        return 0;
    }
/*-----------------------------------------------------------*/

/*
 #####          ###
 #   #           #            #
 #    #          #            #
 #    #  ####    #    ####  ######  ####
 #    # #    #   #   #    #   #    #    #
 #    # ######   #   ######   #    ######
 #    # #        #   #        #    #
 #   #  #   ##   #   #   ##   # ## #   ##
 #####    ####  #####  ####     ##   ####
 */
    static BaseType_t prvDeleteFile( FTPClient_t * pxClient,
                                     char * pcFileName )
    {
        BaseType_t xResult, xLength;
        int32_t iRc;
        int iErrorNo;

        /* DELE: Delete a file. */
        xMakeAbsolute( pxClient, pxClient->pcFileName, sizeof( pxClient->pcFileName ), pcFileName );

        iRc = ff_remove( pxClient->pcFileName );

        if( iRc >= 0 )
        {
            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                "250 File \"%s\" removed\r\n", pxClient->pcFileName );
            xResult = pdTRUE;
        }
        else
        {
            const char * errMsg = "other error";

            iErrorNo = stdioGET_ERRNO();

            switch( iErrorNo )
            { /*_RB_ What do these negative numbers relate to? */
                case pdFREERTOS_ERRNO_ENOENT:
                    errMsg = "No such file";
                    break; /* -31	File was not found. */

                case pdFREERTOS_ERRNO_EALREADY:
                    errMsg = "File still open";
                    break; /* -30	File is in use. */

                case pdFREERTOS_ERRNO_EISDIR:
                    errMsg = "Is a dir";
                    break; /* -32	Tried to FF_Open() a Directory. */

                case pdFREERTOS_ERRNO_EROFS:
                    errMsg = "Read-only";
                    break; /* -33	Tried to FF_Open() a file marked read only. */

                case pdFREERTOS_ERRNO_ENOTDIR:
                    errMsg = "Invalid path";
                    break; /* -34	The path of the file was not found. */
            }

            FreeRTOS_printf( ( "ftp::delFile: '%s' because %s\n",
                               pxClient->pcFileName, strerror( iErrorNo ) ) );

            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                "521-\"%s\" %s;\r\n"
                                "521 taking no action\r\n",
                                pxClient->pcFileName, errMsg );

            xResult = pdFALSE;
        }

        prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );

        return xResult;
    }
/*-----------------------------------------------------------*/

/*
 ####    #                       #####
 #    #   #                        #   #            #
 #    #                            #    #           #
 #      ###   ######  ####         #    #  ####   ######  ####
 ##      #   #    # #    #        #    #      #    #    #    #
 ##    #       #  ######        #    #  #####    #    ######
 #    #   #     #    #             #    # #    #    #    #
 #    #   #    #     #   ##        #   #  #    #    # ## #   ##
 ####  ##### ######  ####        #####    ### ##    ##   ####
 */
    static BaseType_t prvSizeDateFile( FTPClient_t * pxClient,
                                       char * pcFileName,
                                       BaseType_t xSendDate )
    {
        BaseType_t xResult = pdFALSE;
        char * pcPtr;

        /* SIZE: get the size of a file (xSendDate = 0)
         * MDTM: get data and time properties (xSendDate = 1) */
        xMakeAbsolute( pxClient, pxClient->pcFileName, sizeof( pxClient->pcFileName ), pcFileName );

        pcPtr = strrchr( pxClient->pcFileName, '/' );

        if( ( pcPtr != NULL ) && ( pcPtr[ 1 ] != '\0' ) )
        {
            FF_Stat_t xStatBuf;
            int32_t iRc = ff_stat( pxClient->pcFileName, &xStatBuf );

            if( iRc < 0 )
            {
                FreeRTOS_printf( ( "In %s: %s\n", pxClient->pcFileName,
                                   ( const char * ) strerror( stdioGET_ERRNO() ) ) );
            }

            if( iRc == 0 )
            {
                BaseType_t xLength;

                /* "YYYYMMDDhhmmss" */
                if( xSendDate != pdFALSE )
                {
                    #if ( ffconfigTIME_SUPPORT != 0 )
                    {
                        FF_TimeStruct_t tmStruct;
                        time_t secs = xStatBuf.st_mtime;
                        FreeRTOS_gmtime_r( &secs, &tmStruct );

                        xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "213 %04u%02u%02u%02u%02u%02u\r\n",
                                            tmStruct.tm_year + 1900,
                                            tmStruct.tm_mon + 1,
                                            tmStruct.tm_mday,
                                            tmStruct.tm_hour,
                                            tmStruct.tm_min,
                                            tmStruct.tm_sec );
                    }
                    #else /* if ( ffconfigTIME_SUPPORT != 0 ) */
                    {
                        xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "213 19700101000000\r\n",
}
                    #endif /* if ( ffconfigTIME_SUPPORT != 0 ) */
                }
                else
                {
                    xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "213 %lu\r\n", xStatBuf.st_size );
                }

                prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );
                xResult = pdTRUE;
            }
            else
            {
                FreeRTOS_printf( ( "ftp::sizeDateFile: No such file %s\n", pxClient->pcFileName ) );
            }
        }
        else
        {
            FreeRTOS_printf( ( "ftp::sizeDateFile: Invalid file name: %s ?\n", pxClient->pcFileName ) );
        }

        if( xResult == pdFALSE )
        {
            prvSendReply( pxClient->xSocket, REPL_450, 0 ); /* "Requested file action not taken". */
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

/*
##   ## ##   ## #####      ######  ##   ## #####
### ###  #    #  #   #      #    # ### ###  #   #
# ### #  #   #   #    #     #    # # ### #  #    #
#  #  #  #   #   #    #     #    # #  #  #  #    #
#  #  #  ####    #    #     ###### #  #  #  #    #
#     #  #   #   #    #     #  ##  #     #  #    #
#     #  #   #   #    #     #   #  #     #  #    #
#     #  #    #  #   #      #    # #     #  #   #
#     # ###  ## #####      ###  ## #     # #####
*/
    static BaseType_t prvMakeRemoveDir( FTPClient_t * pxClient,
                                        const char * pcDirectory,
                                        BaseType_t xDoRemove )
    {
        BaseType_t xResult;
        BaseType_t xLength;
        int32_t iRc;
        int iErrorNo;

        /* MKD: Make / create a directory (xDoRemove = 0)
         * RMD: Remove a directory (xDoRemove = 1) */
        xMakeAbsolute( pxClient, pxClient->pcFileName, sizeof( pxClient->pcFileName ), pcDirectory );

        if( xDoRemove )
        {
            iRc = ff_rmdir( pxClient->pcFileName );
        }
        else
        {
            #if ( ffconfigMKDIR_RECURSIVE != 0 )
            {
                iRc = ff_mkdir( pxClient->pcFileName, pdFALSE );
            }
            #else
            {
                iRc = ff_mkdir( pxClient->pcFileName );
            }
            #endif /* ffconfigMKDIR_RECURSIVE */
        }

        xResult = pdTRUE;

        if( iRc >= 0 )
        {
            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), "257 \"%s\" directory %s\r\n",
                                pxClient->pcFileName, xDoRemove ? "removed" : "created" );
        }
        else
        {
            const char * errMsg = "other error";
            BaseType_t xFTPCode = 521;

            xResult = pdFALSE;
            iErrorNo = stdioGET_ERRNO();

            switch( iErrorNo )
            {
                case pdFREERTOS_ERRNO_EEXIST:
                    errMsg = "Directory already exists";
                    break;

                case pdFREERTOS_ERRNO_ENOTDIR:
                    errMsg = "Invalid path";
                    break; /* -34 The path of the file was not found. *//*_RB_ As before, what do these negative numbers relate to? */

                case pdFREERTOS_ERRNO_ENOTEMPTY:
                    errMsg = "Dir not empty";
                    break;

                case pdFREERTOS_ERRNO_EROFS:
                    errMsg = "Read-only";
                    break; /* -33	Tried to FF_Open() a file marked read only. */

                default:
                    errMsg = strerror( iErrorNo );
                    break;
            }

            if( iErrorNo == pdFREERTOS_ERRNO_ENOSPC )
            {
                xFTPCode = 552;
            }

            xLength = snprintf( pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ),
                                "%ld-\"%s\" %s;\r\n"
                                "%ld taking no action\r\n",
                                xFTPCode, pxClient->pcFileName, errMsg, xFTPCode );
            FreeRTOS_printf( ( "%sdir '%s': %s\n", xDoRemove ? "rm" : "mk", pxClient->pcFileName, errMsg ) );
        }

        prvSendReply( pxClient->xSocket, pcCOMMAND_BUFFER, xLength );

        return xResult;
    }
/*-----------------------------------------------------------*/

    static portINLINE BaseType_t IsDigit( char cChar )
    {
        BaseType_t xResult;

        if( ( cChar >= '0' ) && ( cChar <= '9' ) )
        {
            xResult = pdTRUE;
        }
        else
        {
            xResult = pdFALSE;
        }

        return xResult;
    }

    static BaseType_t prvSendReply( Socket_t xSocket,
                                    const char * pcBuffer,
                                    BaseType_t xLength )
    {
        BaseType_t xResult;

        if( xLength == 0 )
        {
            xLength = strlen( pcBuffer );
        }

        xResult = FreeRTOS_send( xSocket, ( const void * ) pcBuffer, ( size_t ) xLength, 0 );

        if( IsDigit( ( int ) pcBuffer[ 0 ] ) &&
            IsDigit( ( int ) pcBuffer[ 1 ] ) &&
            IsDigit( ( int ) pcBuffer[ 2 ] ) &&
            IsDigit( ( int ) pcBuffer[ 3 ] ) )
        {
            const char * last = pcBuffer + strlen( pcBuffer );
            int iLength;

            while( ( last > pcBuffer ) && ( ( last[ -1 ] == ftpASCII_CR ) || ( last[ -1 ] == ftpASCII_LF ) ) )
            {
                last--;
            }

            iLength = ( int ) ( last - pcBuffer );
            FF_PRINTF( "   %-*.*s", iLength, iLength, pcBuffer );
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigFTP_HAS_RECEIVED_HOOK != 0 )

/*
 * The following function is called for every file received:
 *     void vApplicationFTPReceivedHook( pcFileName, ulSize, pxFTPClient );
 * This callback function may do a callback to vFTPReplyMessage() to send messages
 * to the FTP client like:
 *      200-Please wait: Received new firmware
 *      200-Please wait: Please wait a few seconds for reboot
 */
        void vFTPReplyMessage( struct xFTP_CLIENT * pxFTPClient,
                               const char * pcMessage )
        {
            if( ( pxFTPClient != NULL ) && ( pxFTPClient->xSocket != NULL ) )
            {
                prvSendReply( pxFTPClient->xSocket, pcMessage, 0 );
            }
        }
        /*-----------------------------------------------------------*/

    #endif /* ipconfigFTP_HAS_RECEIVED_HOOK != 0 */

/*
 * Some explanation:
 * The FTP client may send: "DELE readme.txt"
 * Here the complete path is constructed consisting of 3 parts:
 *
 * pxClient->pcRootDir  +  pxClient->pcCurrentDir  +  pcFileName
 *
 * 'pcCurrentDir' will not be applied for an absolute path like in "DELE /.htaccess"
 */
    BaseType_t xMakeAbsolute( FTPClient_t * pxClient,
                              char * pcBuffer,
                              BaseType_t xBufferLength,
                              const char * pcFileName )
    {
        BaseType_t xLength = strlen( pxClient->pcRootDir );

        if( pcFileName[ 0 ] != '/' )
        {
            char * pcNewDirBuffer = pcNEW_DIR;
            BaseType_t xCurLength;

            xCurLength = strlen( pxClient->pcCurrentDir );

            if( pcBuffer == pcNEW_DIR )
            {
                /* In one call, the result already goes into pcNEW_DIR.
                 * Use pcFILE_BUFFER in that case */
                pcNewDirBuffer = pcFILE_BUFFER;
            }

            snprintf( pcNewDirBuffer, sizeof( pcNEW_DIR ), "%s%s%s",
                      pxClient->pcCurrentDir,
                      pxClient->pcCurrentDir[ xCurLength - 1 ] == '/' ? "" : "/",
                      pcFileName );
            pcFileName = pcNewDirBuffer;
        }

        if( strncasecmp( pxClient->pcRootDir, pcFileName, xLength ) == 0 )
        {
            xLength = snprintf( pcBuffer, xBufferLength, "%s", pcFileName );
        }
        else
        {
            xLength = snprintf( pcBuffer, xBufferLength, "%s/%s",
                                pxClient->pcRootDir,
                                pcFileName[ 0 ] == '/' ? ( pcFileName + 1 ) : pcFileName );
        }

        #if ( ipconfigFTP_FS_USES_BACKSLASH == 1 )
            for( pcPtr = pcBuffer; *pcPtr; pcPtr++ )
            {
                if( pcPtr[ 0 ] == '/' )
                {
                    pcPtr[ 0 ] = '\\';
                }
            }
        #endif

        return xLength;
    }
/*-----------------------------------------------------------*/

    BaseType_t xMakeRelative( FTPClient_t * pxClient,
                              char * pcBuffer,
                              BaseType_t xBufferLength,
                              const char * pcFileName )
    {
        BaseType_t xLength = strlen( pxClient->pcRootDir );

        if( strncasecmp( pxClient->pcRootDir, pcFileName, xLength ) == 0 )
        {
            xLength = snprintf( pcBuffer, xBufferLength, "%s", pcFileName + xLength );
        }
        else
        {
            xLength = snprintf( pcBuffer, xBufferLength, "%s", pcFileName );
        }

        return xLength;
    }
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_FTP */
