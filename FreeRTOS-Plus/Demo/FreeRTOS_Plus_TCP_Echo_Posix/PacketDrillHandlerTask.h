/*
 * FreeRTOS V202112.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#ifndef PACKETDRILL_HANDLER_TASK_H
#define PACKETDRILL_HANDLER_TASK_H

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "FreeRTOS_Stream_Buffer.h"
#include "wait_for_event.h"

/*
 * Create the PacketDrill handler task.
 */
void vStartPacketDrillHandlerTask( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority );
void resetPacketDrillTask();


struct AcceptPackage {
    int sockfd;
};

struct BindPackage {
    int sockfd;
    struct sockaddr addr;
    socklen_t addrlen;
};

struct ListenPackage {
    int sockfd;
    int backlog;
};

struct WritePackage {
    int sockfd;
    size_t count;
};

struct ReadPackage {
    int sockfd;
    size_t count;
};

struct ClosePackage {
    int sockfd;
};

struct AcceptResponsePackage {
    struct sockaddr addr;
    socklen_t addrlen;
};

struct SyscallResponsePackage {
    int result;
    union {
        struct AcceptResponsePackage acceptResponse;
    };
};


struct SyscallPackage {
    char syscallId[20];
    int bufferedMessage;
    size_t bufferedCount;
    void *buffer;
    union {
        struct BindPackage bindPackage;
        struct ListenPackage listenPackage;
        struct AcceptPackage acceptPackage;
        struct BindPackage connectPackage;
        struct WritePackage writePackage;
        struct ReadPackage readPackage;
        struct ClosePackage closePackage;
    };
};

#endif /* PACKETDRILL_HANDLER_TASK_H */


