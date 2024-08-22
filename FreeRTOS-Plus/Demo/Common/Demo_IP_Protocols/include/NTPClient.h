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

/* ntpClient.h */

#ifndef __NTPCLIENT_H__

#define __NTPCLIENT_H__

#define NTP_PORT    123

typedef uint32_t           quint32;
typedef int32_t            qint32;
typedef uint8_t            quint8;
typedef int8_t             qint8;

typedef union _SNtpFlags   SNtpFlags;

/**
 * 64-bit NTP timestamp.
 */
struct __attribute__( ( __packed__ ) ) _SNtpTimestamp
{
    /** Number of seconds passed since Jan 1 1900, in big-endian format. */
    quint32 seconds;

    /** Fractional time part, in <tt>1/0xFFFFFFFF</tt>s of a second. */
    quint32 fraction;
};

typedef struct _SNtpTimestamp SNtpTimestamp;

/**
 * Mandatory part of an NTP packet
 */
struct SNtpPacket
{
    /** Flags. */
    unsigned char flags; /* value 0xDB : mode 3 (client), version 3, leap indicator unknown 3 */

    /** Stratum of the clock. */
    quint8 stratum; /* value 0 : unspecified */

    /** Maximum interval between successive messages, in log2 seconds. Note that the value is signed. */
    qint8 poll; /* 10 means 1 << 10 = 1024 seconds */

    /** Precision of the clock, in log2 seconds. Note that the value is signed. */
    qint8 precision; /* 0xFA = 250 = 0.015625 seconds */

    /** Round trip time to the primary reference source, in NTP short format. */
    qint32 rootDelay; /* 0x5D2E = 23854 or (23854/65535)= 0.3640 sec */

    /** Nominal error relative to the primary reference source. */
    qint32 rootDispersion; /* 0x0008 CAC8 = 8.7912  seconds */

    /** Reference identifier (either a 4 character string or an IP address). */
    qint8 referenceID[ 4 ]; /* or just 0000 */

    /** The time at which the clock was last set or corrected. */
    SNtpTimestamp referenceTimestamp; /* Current time */

    /** The time at which the request departed the client for the server. */
    SNtpTimestamp originateTimestamp; /* Keep 0 */

    /** The time at which the request arrived at the server. */
    SNtpTimestamp receiveTimestamp; /* Keep 0 */

    /** The time at which the reply departed the server for client. */
    SNtpTimestamp transmitTimestamp;
};

/* Add this number to get secs since 1-1-1900 */
#define TIME1970    2208988800UL

#endif // __NTPCLIENT_H__
