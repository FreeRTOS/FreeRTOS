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


#ifndef BASIC_TFTP_SERVER_H
#define BASIC_TFTP_SERVER_H

#include "portmacro.h"

/* tftp_support.h */

/*
 * File transfer modes
 */
#define TFTP_NETASCII   0              // Text files
#define TFTP_OCTET      1              // Binary files

/*
 * Errors
 */

// These initial 7 are passed across the net in "ERROR" packets.
#define TFTP_ENOTFOUND   1   /* file not found */
#define TFTP_EACCESS     2   /* access violation */
#define TFTP_ENOSPACE    3   /* disk full or allocation exceeded */
#define TFTP_EBADOP      4   /* illegal TFTP operation */
#define TFTP_EBADID      5   /* unknown transfer ID */
#define TFTP_EEXISTS     6   /* file already exists */
#define TFTP_ENOUSER     7   /* no such user */
// These extensions are return codes in our API, *never* passed on the net.
#define TFTP_TIMEOUT     8   /* operation timed out */
#define TFTP_NETERR      9   /* some sort of network error */
#define TFTP_INVALID    10   /* invalid parameter */
#define TFTP_PROTOCOL   11   /* protocol violation */
#define TFTP_TOOLARGE   12   /* file is larger than buffer */

#define TFTP_TIMEOUT_PERIOD  5          // Seconds between retries
#define TFTP_TIMEOUT_MAX    50          // Max timeouts over all blocks
#define TFTP_RETRIES_MAX     5          // retries per block before giving up

/* netdb.h */
// Internet services
struct servent {
char *s_name; /* official service name */
char **s_aliases; /* alias list */
int s_port; /* port number */
char *s_proto; /* protocol to use */
};

/* arpa/tftp.h */

/*
 * Trivial File Transfer Protocol (IEN-133)
 */
#define SEGSIZE   512   /* data segment size */

/*
 * Packet types.
 */

#define th_block  th_u.tu_block
#define th_code   th_u.tu_code
#define th_stuff  th_u.tu_stuff
#define th_msg    th_data

/*
 * Error codes.
 */
#define EUNDEF    0   /* not defined */
#define ENOTFOUND 1   /* file not found */
#define EACCESS   2   /* access violation */
#define ENOSPACE  3   /* disk full or allocation exceeded */
#define EBADOP    4   /* illegal TFTP operation */
#define EBADID    5   /* unknown transfer ID */
#define EEXISTS   6   /* file already exists */
#define ENOUSER   7   /* no such user */



#define RRQ 01      /* read request */
#define WRQ 02      /* write request */
#define DATA  03      /* data packet */
#define ACK 04      /* acknowledgement */
#define ERROR 05      /* error code */

#if __ICCAVR32__
#pragma pack(1)
#endif
struct  tftphdr {
  short th_opcode;    /* packet type */
  union {
    unsigned short  tu_block; /* block # */
    short tu_code;  /* error code */
    char  tu_stuff[1];  /* request packet stuff */
  }
#if __GNUC__
 __attribute__ ((packed))
#endif 
   th_u;
  char  th_data[1];   /* data or error string */
}
#if __GNUC__
__attribute__ ((packed))
#endif 
;
#if __ICCAVR32__
#pragma pack()
#endif

/* The function that implements the TFTP server task. */
portTASK_FUNCTION_PROTO( vBasicTFTPServer, pvParameters );



#endif

