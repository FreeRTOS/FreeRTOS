/*
 * Copyright (c) 2015-2016, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
/*
 *  ======== MutexP_freertos.c ========
 */

#include <ti/drivers/dpl/MutexP.h>

#include <FreeRTOS.h>
#include <semphr.h>
#include <queue.h>


/*
 *  ======== MutexP_create ========
 */
MutexP_Handle MutexP_create(MutexP_Params *params)
{
    SemaphoreHandle_t sem = NULL;

    /*
     *  NOTE:  Documentation in semphr.h says that configUSE_RECURSIVE_MUTEXES
     *  must be set to 1 in FreeRTOSConfig.h  for this to be available, but
     *  the xSemaphore recursive calls are inside a configUSE_RECURSIVE_MUTEXES
     *  block.
     */
    sem = xSemaphoreCreateRecursiveMutex();

    return ((MutexP_Handle)sem);
}

/*
 *  ======== MutexP_delete ========
 */
MutexP_Status MutexP_delete(MutexP_Handle handle)
{
    vSemaphoreDelete((SemaphoreHandle_t)handle);

    return (MutexP_OK);
}

/*
 *  ======== MutexP_lock ========
 */
uintptr_t MutexP_lock(MutexP_Handle handle)
{
    SemaphoreHandle_t xMutex = (SemaphoreHandle_t)handle;

    /* Retry every 10 ticks */
    while (xSemaphoreTakeRecursive(xMutex, (TickType_t)10) == pdFALSE) {
        ;
    }

    return (0);
}

/*
 *  ======== MutexP_Params_init ========
 */
void MutexP_Params_init(MutexP_Params *params)
{
    params->name = NULL;
    params->callback = NULL;
}

/*
 *  ======== MutexP_unlock ========
 */
void MutexP_unlock(MutexP_Handle handle, uintptr_t key)
{
    SemaphoreHandle_t xMutex = (SemaphoreHandle_t)handle;
    xSemaphoreGiveRecursive(xMutex);
}
