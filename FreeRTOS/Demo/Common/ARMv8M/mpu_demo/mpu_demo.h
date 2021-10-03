/*
 * FreeRTOS V202107.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef __MPU_DEMO_H__
#define __MPU_DEMO_H__

/**
 * @brief Creates all the tasks for MPU demo.
 *
 * The MPU demo creates 2 unprivileged tasks - One of which has Read Only access
 * to a shared memory region while the other has Read Write access. The task
 * with Read Only access then tries to write to the shared memory which results
 * in a Memory fault. The fault handler examines that it is the fault generated
 * by the task with Read Only access and if so, it recovers from the fault
 * gracefully by moving the Program Counter to the next instruction to the one
 * which generated the fault. If any other memory access violation occurs, the
 * fault handler will get stuck in an infinite loop.
 */
void vStartMPUDemo( void );

#endif /* __MPU_DEMO_H__ */
