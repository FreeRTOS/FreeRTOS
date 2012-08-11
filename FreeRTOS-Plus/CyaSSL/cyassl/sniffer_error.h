/* sniffer_error.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef CYASSL_SNIFFER_ERROR_H
#define CYASSL_SNIFFER_ERROR_H

/* need to have errors as #defines since .rc files can't handle enums */
/* need to start at 1 and go in order for same reason */

#define MEMORY_STR 1
#define NEW_SERVER_STR 2
#define IP_CHECK_STR 3
#define SERVER_NOT_REG_STR 4
#define TCP_CHECK_STR 5
#define SERVER_PORT_NOT_REG_STR 6
#define RSA_DECRYPT_STR 7
#define RSA_DECODE_STR 8
#define BAD_CIPHER_SPEC_STR 9
#define SERVER_HELLO_INPUT_STR 10

#define BAD_SESSION_RESUME_STR 11
#define SERVER_DID_RESUMPTION_STR 12
#define CLIENT_HELLO_INPUT_STR 13
#define CLIENT_RESUME_TRY_STR 14
#define HANDSHAKE_INPUT_STR 15
#define GOT_HELLO_VERIFY_STR 16
#define GOT_SERVER_HELLO_STR 17
#define GOT_CERT_REQ_STR 18
#define GOT_SERVER_KEY_EX_STR 19
#define GOT_CERT_STR 20

#define GOT_SERVER_HELLO_DONE_STR 21
#define GOT_FINISHED_STR 22
#define GOT_CLIENT_HELLO_STR 23
#define GOT_CLIENT_KEY_EX_STR 24
#define GOT_CERT_VER_STR 25
#define GOT_UNKNOWN_HANDSHAKE_STR 26
#define NEW_SESSION_STR 27
#define BAD_NEW_SSL_STR 28
#define GOT_PACKET_STR 29
#define NO_DATA_STR 30

#define BAD_SESSION_STR 31
#define GOT_OLD_CLIENT_HELLO_STR 32
#define OLD_CLIENT_INPUT_STR 33
#define OLD_CLIENT_OK_STR 34
#define BAD_OLD_CLIENT_STR 35
#define BAD_RECORD_HDR_STR 36
#define RECORD_INPUT_STR 37
#define GOT_HANDSHAKE_STR 38
#define BAD_HANDSHAKE_STR 39
#define GOT_CHANGE_CIPHER_STR 40

#define GOT_APP_DATA_STR 41
#define BAD_APP_DATA_STR 42
#define GOT_ALERT_STR 43
#define ANOTHER_MSG_STR 44
#define REMOVE_SESSION_STR 45
#define KEY_FILE_STR 46
#define BAD_IPVER_STR 47
#define BAD_PROTO_STR 48
#define PACKET_HDR_SHORT_STR 49
#define GOT_UNKNOWN_RECORD_STR 50

#define BAD_TRACE_FILE_STR 51
#define FATAL_ERROR_STR 52
#define PARTIAL_INPUT_STR 53
#define BUFFER_ERROR_STR 54
#define PARTIAL_ADD_STR 55
#define DUPLICATE_STR 56
#define OUT_OF_ORDER_STR 57
#define OVERLAP_DUPLICATE_STR 58
#define OVERLAP_REASSEMBLY_BEGIN_STR 59

#define OVERLAP_REASSEMBLY_END_STR 60
#define MISSED_CLIENT_HELLO_STR 61

/* !!!! also add to msgTable in sniffer.c and .rc file !!!! */


#endif /* CyaSSL_SNIFFER_ERROR_H */

