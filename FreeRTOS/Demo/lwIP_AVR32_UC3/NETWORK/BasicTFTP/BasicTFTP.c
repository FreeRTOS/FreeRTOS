/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief Basic TFTP Server for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


/*
  Implements a simplistic TFTP server.
  
  In order to put data on the TFTP server (not over 2048 bytes)
  tftp 192.168.0.2 PUT <src_filename>
  this will copy file from your hard drive to the RAM buffer of the application

  tftp 192.168.0.2 GET <dst_filename>
  this will copy file from the RAM buffer of the application to your hard drive
  You can then check that src_filename and dst_filename are identical    
*/

#if (TFTP_USED == 1)

#include <string.h>


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"
#include "BasicTFTP.h"


/* Demo includes. */
#include "portmacro.h"

/* lwIP includes. */
#include "lwip/api.h"
#include "lwip/tcpip.h"
#include "lwip/memp.h"
#include "lwip/stats.h"
#include "lwip/opt.h"
#include "lwip/api.h"
#include "lwip/arch.h"
#include "lwip/sys.h"
#include "netif/loopif.h"
#include "lwip/sockets.h"

#define O_WRONLY 1
#define O_RDONLY 2


/* The port on which we listen. */
#define TFTP_PORT    ( 69 )

/* Delay on close error. */
#define TFTP_DELAY         ( 10 )

/* Delay on bind error. */
#define TFTP_ERROR_DELAY    ( 40 )

#define TFTP_LED     ( 4 )

char data_out[SEGSIZE+sizeof(struct tftphdr)];
char data_in[SEGSIZE+sizeof(struct tftphdr)];

//struct tftp_server *server;

/*------------------------------------------------------------*/
static char * errmsg[] = {
  "Undefined error code",               // 0 nothing defined
  "File not found",                     // 1 TFTP_ENOTFOUND 
  "Access violation",                   // 2 TFTP_EACCESS   
  "Disk full or allocation exceeded",   // 3 TFTP_ENOSPACE  
  "Illegal TFTP operation",             // 4 TFTP_EBADOP    
  "Unknown transfer ID",                // 5 TFTP_EBADID    
  "File already exists",                // 6 TFTP_EEXISTS   
  "No such user",                       // 7 TFTP_ENOUSER   
};


/* Send an error packet to the client */
static void 
tftpd_send_error(int s, struct tftphdr * reply, int err,
     struct sockaddr_in *from_addr, int from_len)
{
    if ( ( 0 <= err ) && ( sizeof(errmsg)/sizeof(errmsg[0]) > err) ) {
    reply->th_opcode = htons(ERROR);
    reply->th_code = htons(err);
    if ( (0 > err) || (sizeof(errmsg)/sizeof(errmsg[0]) <= err) )
        err = 0; // Do not copy a random string from hyperspace
    strcpy(reply->th_msg, errmsg[err]);
    sendto(s, reply, 4+strlen(reply->th_msg)+1, 0, 
     (struct sockaddr *)from_addr, from_len);
    }
}

char cRamBuffer[2048];
int lCurrentBlock = 0;
int lTotalLength = 0;


int tftpd_close_data_file(int fd)
{
  lCurrentBlock = 0;
  return (5);
}

int tftpd_open_data_file(int fd, int mode)
{
  lCurrentBlock = 0; 
  return (5);
}

int tftpd_read_data_file(int fd, char * buffer, int length)
{
int lReturnValue;

  if ((lTotalLength -= length) >= 0) {
    lReturnValue = length;
  }
  else
  {
    lReturnValue = lTotalLength + length;
    lTotalLength = 0;
  }
  memcpy(buffer, &cRamBuffer[lCurrentBlock * SEGSIZE], lReturnValue);
  lCurrentBlock++;
  return (lReturnValue);
}

//
// callback to store data to the RAM buffer
//
int tftpd_write_data_file(int fd, char * buffer, int length)
{
  lTotalLength += length;
  memcpy(&cRamBuffer[lCurrentBlock * SEGSIZE], buffer, length);
  lCurrentBlock++;
  return (length);
}

//
// Receive a file from the client
//
static void
tftpd_write_file(struct tftphdr *hdr,
                 struct sockaddr_in *from_addr, int from_len)
{

    struct tftphdr *reply = (struct tftphdr *)data_out;
    struct tftphdr *response = (struct tftphdr *)data_in;
    int fd, len, ok, tries, closed, data_len, s;
    unsigned short block;
    struct timeval timeout;
    fd_set fds;
    int total_timeouts = 0;
    struct sockaddr_in client_addr, local_addr;
    int client_len;


    s = socket(AF_INET, SOCK_DGRAM, 0);
    if (s < 0) {
        return;
    }

    memset((char *)&local_addr, 0, sizeof(local_addr));
    local_addr.sin_family = AF_INET;
    local_addr.sin_len = sizeof(local_addr);
    local_addr.sin_addr.s_addr = htonl(INADDR_ANY);
    local_addr.sin_port = htons(INADDR_ANY);

    if (bind(s, (struct sockaddr *)&local_addr, sizeof(local_addr)) < 0) {
        // Problem setting up my end
        close(s);
        return;
    }

    if ((fd = tftpd_open_data_file((int)hdr->th_stuff, O_WRONLY)) < 0) {
        tftpd_send_error(s,reply,TFTP_ENOTFOUND,from_addr, from_len);
        close(s);
        return;
    }

    ok = pdTRUE;
    closed = pdFALSE;
    block = 0;
    while (ok) {
        // Send ACK telling client he can send data
        reply->th_opcode = htons(ACK);
        reply->th_block = htons(block++); // postincrement
        for (tries = 0;  tries < TFTP_RETRIES_MAX;  tries++) {
            sendto(s, reply, 4, 0, (struct sockaddr *)from_addr, from_len);
        repeat_select:
            timeout.tv_sec = TFTP_TIMEOUT_PERIOD;
            timeout.tv_usec = 0;
            FD_ZERO(&fds);
            FD_SET(s, &fds);
           vParTestToggleLED( TFTP_LED );
           if (lwip_select(s+1, &fds, 0, 0, &timeout) <= 0) {
                if (++total_timeouts > TFTP_TIMEOUT_MAX) {
                    tftpd_send_error(s,reply,TFTP_EBADOP,from_addr, from_len);
                    ok = pdFALSE;
                    break;
                }
                continue; // retry the send, using up one retry.
            }
            vParTestToggleLED( TFTP_LED );
            // Some data has arrived
            data_len = sizeof(data_in);
            client_len = sizeof(client_addr);
            if ((data_len = recvfrom(s, data_in, data_len, 0, 
                      (struct sockaddr *)&client_addr, &client_len)) < 0) {
                // What happened?  No data here!
                continue; // retry the send, using up one retry.
            }
            if (ntohs(response->th_opcode) == DATA &&
                ntohs(response->th_block) < block) {
                // Then it is repeat DATA with an old block; listen again,
                // but do not repeat sending the current ack, and do not
                // use up a retry count.  (we do re-send the ack if
                // subsequently we time out)
                goto repeat_select;
            }
            if (ntohs(response->th_opcode) == DATA &&
                ntohs(response->th_block) == block) {
                // Good data - write to file
                len = tftpd_write_data_file(fd, response->th_data, data_len-4);
                if (len < (data_len-4)) {
                    // File is "full"
                    tftpd_send_error(s,reply,TFTP_ENOSPACE,
                                     from_addr, from_len);     
                    ok = pdFALSE;  // Give up
                    break; // out of the retries loop
                }
                if (data_len < (SEGSIZE+4)) {
                    // End of file
                    closed = pdTRUE;
                    ok = pdFALSE;
                    vParTestSetLED( 0 , 0 );

                    if (tftpd_close_data_file(fd) == -1) {
                        tftpd_send_error(s,reply,TFTP_EACCESS,
                                         from_addr, from_len);

                       break;  // out of the retries loop
                    }
                    // Exception to the loop structure: we must ACK the last
                    // packet, the one that implied EOF:
                    reply->th_opcode = htons(ACK);
                    reply->th_block = htons(block++); // postincrement
                    sendto(s, reply, 4, 0, (struct sockaddr *)from_addr, from_len);
                    break; // out of the retries loop
                }
                // Happy!  Break out of the retries loop.
                break;
            }
        } // End of the retries loop.
        if (TFTP_RETRIES_MAX <= tries) {
            tftpd_send_error(s,reply,TFTP_EBADOP,from_addr, from_len);
            ok = pdFALSE;
        }
    }
    close(s);
    if (!closed) {
      tftpd_close_data_file(fd);
    }
}


//
// Send a file to the client
//
static void
tftpd_read_file(struct tftphdr *hdr,
                struct sockaddr_in *from_addr, int from_len)
{
    struct tftphdr *reply = (struct tftphdr *)data_out;
    struct tftphdr *response = (struct tftphdr *)data_in;
    int fd, len, tries, ok, data_len, s;
    unsigned short block;
    struct timeval timeout;
    fd_set fds;
    int total_timeouts = 0;
    struct sockaddr_in client_addr, local_addr;
    int client_len;

    s = socket(AF_INET, SOCK_DGRAM, 0);
    if (s < 0) {
        return;
    }
    memset((char *)&local_addr, 0, sizeof(local_addr));
    local_addr.sin_family = AF_INET;
    local_addr.sin_len = sizeof(local_addr);
    local_addr.sin_addr.s_addr = htonl(INADDR_ANY);
    local_addr.sin_port = htons(INADDR_ANY);
    if (bind(s, (struct sockaddr *)&local_addr, sizeof(local_addr)) < 0) {
        // Problem setting up my end
        close(s);
        return;
    }
    if ((fd = tftpd_open_data_file((int)hdr->th_stuff, O_RDONLY)) < 0) {
        tftpd_send_error(s,reply,TFTP_ENOTFOUND,from_addr, from_len);
        close(s);
        return;
    }
    block = 0;
    ok = pdTRUE;
    while (ok) {
        // Read next chunk of file
        len = tftpd_read_data_file(fd, reply->th_data, SEGSIZE);
        reply->th_block = htons(++block); // preincrement
        reply->th_opcode = htons(DATA);
        for (tries = 0;  tries < TFTP_RETRIES_MAX;  tries++) {
            if (sendto(s, reply, 4+len, 0,
                       (struct sockaddr *)from_addr, from_len) < 0) {
                // Something went wrong with the network!
                ok = pdFALSE;
                break;
            }
        repeat_select:
            timeout.tv_sec = TFTP_TIMEOUT_PERIOD;
            timeout.tv_usec = 0;
            FD_ZERO(&fds);
            FD_SET(s, &fds);
            vParTestToggleLED( TFTP_LED );
            if (select(s+1, &fds, 0, 0, &timeout) <= 0) {
                if (++total_timeouts > TFTP_TIMEOUT_MAX) {
                    tftpd_send_error(s,reply,TFTP_EBADOP,from_addr, from_len);
                    ok = pdFALSE;
                    break;
                }
                continue; // retry the send, using up one retry.
            }
            vParTestToggleLED( TFTP_LED );
            data_len = sizeof(data_in);
            client_len = sizeof(client_addr);
            if ((data_len = recvfrom(s, data_in, data_len, 0, 
                                     (struct sockaddr *)&client_addr,
                                     &client_len)) < 0) {
                // What happened?  Maybe someone lied to us...
                continue; // retry the send, using up one retry.
            }
            if ((ntohs(response->th_opcode) == ACK) &&
                (ntohs(response->th_block) < block)) {
                // Then it is a repeat ACK for an old block; listen again,
                // but do not repeat sending the current block, and do not
                // use up a retry count.  (we do re-send the data if
                // subsequently we time out)
                goto repeat_select;
            }
            if ((ntohs(response->th_opcode) == ACK) &&
                (ntohs(response->th_block) == block)) {
                // Happy!  Break out of the retries loop.
                break;
            }
        } // End of the retries loop.
        if (TFTP_RETRIES_MAX <= tries) {
            tftpd_send_error(s,reply,TFTP_EBADOP,from_addr, from_len);
            ok = pdFALSE;
        }
        if (len < SEGSIZE) {
            break; // That's end of file then.
        }
    }
    close(s);
    tftpd_close_data_file(fd);
}



portTASK_FUNCTION( vBasicTFTPServer, pvParameters )
{
    int lSocket;
    int lDataLen, lRecvLen, lFromLen;
    struct sockaddr_in sLocalAddr, sFromAddr;
    char cData[SEGSIZE+sizeof(struct tftphdr)];
    struct tftphdr *sHdr = (struct tftphdr *)cData;

    // Set up port
    // Network order in info; host order in server:

    for (;;) {
        // Create socket
        lSocket = socket(AF_INET, SOCK_DGRAM, 0);
        if (lSocket < 0) {
            return;
        }
        memset((char *)&sLocalAddr, 0, sizeof(sLocalAddr));
        sLocalAddr.sin_family = AF_INET;
        sLocalAddr.sin_len = sizeof(sLocalAddr);
        sLocalAddr.sin_addr.s_addr = htonl(INADDR_ANY);
        sLocalAddr.sin_port = TFTP_PORT;

        if (bind(lSocket, (struct sockaddr *)&sLocalAddr, sizeof(sLocalAddr)) < 0) {
            // Problem setting up my end
            close(lSocket);
            return;
        }


        lRecvLen = sizeof(cData);
        lFromLen = sizeof(sFromAddr);
        lDataLen = recvfrom(lSocket, sHdr, lRecvLen, 0,
                            (struct sockaddr *)&sFromAddr, &lFromLen);
        vParTestSetLED( TFTP_LED , pdTRUE );
        close(lSocket); // so that other servers can bind to the TFTP socket

        if ( lDataLen < 0) {

        } else {
            switch (ntohs(sHdr->th_opcode)) {
            case WRQ:
                tftpd_write_file(sHdr, &sFromAddr, lFromLen);
                vParTestSetLED( TFTP_LED , pdFALSE );
                break;
            case RRQ:
                tftpd_read_file(sHdr, &sFromAddr, lFromLen);
                vParTestSetLED( TFTP_LED , pdFALSE );
                break;
            case ACK:
            case DATA:
            case ERROR:
                vParTestSetLED( TFTP_LED , pdFALSE );
                // Ignore
                break;
            default:
                for(;;)
                {
                  vParTestToggleLED( TFTP_LED );
                  vTaskDelay(200);                    
                }
             }
        }
    }
}
#endif
