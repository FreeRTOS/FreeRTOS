/*
 * Amazon FreeRTOS POSIX V1.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * @file mqueue.h
 * @brief Message queues.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/basedefs/mqueue.h.html
 */

#ifndef _FREERTOS_POSIX_MQUEUE_H_
#define _FREERTOS_POSIX_MQUEUE_H_

/* FreeRTOS+POSIX includes. */
#include "FreeRTOS_POSIX/time.h"

/**
 * @brief Message queue descriptor.
 */
typedef void * mqd_t;

/**
 * @brief Message queue attributes.
 */
struct mq_attr
{
    long mq_flags;   /**< Message queue flags. */
    long mq_maxmsg;  /**< Maximum number of messages. */
    long mq_msgsize; /**< Maximum message size. */
    long mq_curmsgs; /**< Number of messages currently queued. */
};

/**
 * @brief Close a message queue.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_close.html
 *
 * @retval 0 - Upon successful completion
 * @retval -1 - A error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EBADF - The mqdes argument is not a valid message queue descriptor.
 */
int mq_close( mqd_t mqdes );

/**
 * @brief Get message queue attributes.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_getattr.html
 *
 * @retval 0 - Upon successful completion
 * @retval -1 - A error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * DBADF - The mqdes argument is not a valid message queue descriptor.
 */
int mq_getattr( mqd_t mqdes,
                struct mq_attr * mqstat );

/**
 * @brief Open a message queue.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_open.html
 *
 * @note Supported name pattern: leading &lt;slash&gt; character in name is always required;
 * the maximum length (excluding null-terminator) of the name argument can be NAME_MAX.
 * The default value of NAME_MAX in FreeRTOS_POSIX_portable_default.h is 64, which can be
 * overwritten by user.
 * @note mode argument is not supported.
 * @note Supported oflags: O_RDWR, O_CREAT, O_EXCL, and O_NONBLOCK.
 *
 * @retval Message queue descriptor -- Upon successful completion
 * @retval (mqd_t) - 1 -- An error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EINVAL - name argument is invalid (not following name pattern),
 * OR if O_CREAT is specified in oflag with attr argument not NULL and either mq_maxmsg or mq_msgsize is equal to or less than zero,
 * OR either O_CREAT or O_EXCL is not set and a queue with the same name is unlinked but pending to be removed.
 * <br>
 * EEXIST - O_CREAT and O_EXCL are set and the named message queue already exists.
 * <br>
 * ENOSPC - There is insufficient space for the creation of the new message queue.
 * <br>
 * ENOENT - O_CREAT is not set and the named message queue does not exist.
 */
mqd_t mq_open( const char * name,
               int oflag,
               mode_t mode,
               struct mq_attr * attr );

/**
 * @brief Receive a message from a message queue.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_receive.html
 *
 * @note msg_prio argument is not supported. Messages are not checked for corruption.
 *
 * @retval The length of the selected message in bytes - Upon successful completion.
 * The message is removed from the queue
 * @retval -1 - An error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EBADF - The mqdes argument is not a valid message queue descriptor open for reading.
 * <br>
 * EMSGSIZE - The specified message buffer size, msg_len, is less than the message size attribute of the message queue.
 * <br>
 * ETIMEDOUT - The O_NONBLOCK flag was not set when the message queue was opened,
 * but no message arrived on the queue before the specified timeout expired.
 * <br>
 * EAGAIN - O_NONBLOCK was set in the message description associated with mqdes, and the specified message queue is empty.
 */
ssize_t mq_receive( mqd_t mqdes,
                    char * msg_ptr,
                    size_t msg_len,
                    unsigned int * msg_prio );

/**
 * @brief Send a message to a message queue.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_send.html
 *
 * @note msg_prio argument is not supported.
 *
 * @retval 0 - Upon successful completion.
 * @retval -1 - An error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EBADF - The mqdes argument is not a valid message queue descriptor open for writing.
 * <br>
 * EMSGSIZE - The specified message length, msg_len, exceeds the message size attribute of the message queue,
 * OR insufficient memory for the message to be sent.
 * <br>
 * ETIMEDOUT - The O_NONBLOCK flag was not set when the message queue was opened,
 * but the timeout expired before the message could be added to the queue.
 * <br>
 * EAGAIN - The O_NONBLOCK flag is set in the message queue description associated with mqdes,
 * and the specified message queue is full.
 */
int mq_send( mqd_t mqdes,
             const char * msg_ptr,
             size_t msg_len,
             unsigned msg_prio );

/**
 * @brief Receive a message from a message queue with timeout.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_timedreceive.html
 *
 * @note msg_prio argument is not supported. Messages are not checked for corruption.
 *
 * @retval The length of the selected message in bytes - Upon successful completion.
 * The message is removed from the queue
 * @retval -1 - An error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EBADF - The mqdes argument is not a valid message queue descriptor open for reading.
 * <br>
 * EMSGSIZE - The specified message buffer size, msg_len, is less than the message size attribute of the message queue.
 * <br>
 * EINVAL - The process or thread would have blocked, and the abstime parameter specified a nanoseconds field value
 * less than zero or greater than or equal to 1000 million.
 * <br>
 * ETIMEDOUT - The O_NONBLOCK flag was not set when the message queue was opened,
 * but no message arrived on the queue before the specified timeout expired.
 * <br>
 * EAGAIN - O_NONBLOCK was set in the message description associated with mqdes, and the specified message queue is empty.
 */
ssize_t mq_timedreceive( mqd_t mqdes,
                         char * msg_ptr,
                         size_t msg_len,
                         unsigned * msg_prio,
                         const struct timespec * abstime );

/**
 * @brief Send a message to a message queue with timeout.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_timedsend.html
 *
 * @note msg_prio argument is not supported.
 *
 * @retval 0 - Upon successful completion.
 * @retval -1 - An error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EBADF - The mqdes argument is not a valid message queue descriptor open for writing.
 * <br>
 * EMSGSIZE - The specified message length, msg_len, exceeds the message size attribute of the message queue,
 * OR insufficient memory for the message to be sent.
 * <br>
 * EINVAL - The process or thread would have blocked, and the abstime parameter specified a nanoseconds field
 * value less than zero or greater than or equal to 1000 million.
 * <br>
 * ETIMEDOUT - The O_NONBLOCK flag was not set when the message queue was opened,
 * but the timeout expired before the message could be added to the queue.
 * <br>
 * EAGAIN - The O_NONBLOCK flag is set in the message queue description associated with mqdes,
 * and the specified message queue is full.
 */
int mq_timedsend( mqd_t mqdes,
                  const char * msg_ptr,
                  size_t msg_len,
                  unsigned msg_prio,
                  const struct timespec * abstime );

/**
 * @brief Remove a message queue.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/mq_unlink.html
 *
 * @retval 0 - Upon successful completion.
 * @retval -1 - An error occurred. errno is also set.
 *
 * @sideeffect Possible errno values
 * <br>
 * EINVAL - name argument is invalid. Refer to requirements on name argument in mq_open().
 * <br>
 * ENOENT - The named message queue does not exist.
 */
int mq_unlink( const char * name );

#endif /* ifndef _FREERTOS_POSIX_MQUEUE_H_ */
