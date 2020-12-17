/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef TEST_TCP_H
#define TEST_TCP_H

 /* Non-Encrypted Echo Server.
  * Update tcptestECHO_SERVER_ADDR# and
  * tcptestECHO_PORT with IP address
  * and port of unencrypted TCP echo server. */

  /* You can find the code to setup an echo server in the Repo */

  /* Assume ECHO server IP-address A.B.C.D  And   Port Z*/
#define tcptestECHO_SERVER_ADDR0         ( 255 )    /* Replace with Your Echo Server Addr First Byte  i.e. A */
#define tcptestECHO_SERVER_ADDR1         ( 255 )    /* Replace with Your Echo Server Addr Second Byte i.e. B */
#define tcptestECHO_SERVER_ADDR2         ( 255 )    /* Replace with Your Echo Server Addr Third Byte  i.e. C */
#define tcptestECHO_SERVER_ADDR3         ( 255 )    /* Replace with Your Echo Server Addr Fourth Byte i.e. D */
#define tcptestECHO_PORT                 ( 0 )      /* Replace with Your Echo Server Port Number i.e. Z */

#if tcptestECHO_PORT == 0
#error "Use Correct Port number and Correct IP address by setting tcptestECHO_SERVER_ADDR[0-3] and tcptestECHO_PORT in test_tcp.h"
#endif
/* Number of times to retry a connection if it fails. */
#define tcptestRETRY_CONNECTION_TIMES    6

#endif /* ifndef TEST_TCP_H */
