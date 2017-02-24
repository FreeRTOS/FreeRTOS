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
 *  ======== SemaphoreP_freertos.c ========
 */

#include <ti/drivers/dpl/SemaphoreP.h>
#include <ti/drivers/dpl/HwiP.h>

#include <FreeRTOS.h>
#include <semphr.h>
#include <queue.h>

/*
 *  ======== SemaphoreP_create ========
 */
SemaphoreP_Handle SemaphoreP_create(unsigned int count,
                                    SemaphoreP_Params *params)
{
    SemaphoreHandle_t sem = NULL;
    SemaphoreP_Params semParams;

    if (params == NULL) {
        params = &semParams;
        SemaphoreP_Params_init(params);
    }

    if (params->mode == SemaphoreP_Mode_COUNTING) {
#if (configUSE_COUNTING_SEMAPHORES == 1)
        sem = xSemaphoreCreateCounting((UBaseType_t)params->maxCount,
                (UBaseType_t)count);
#endif
    }
    else {
        sem = xSemaphoreCreateBinary();
        if (count != 0) {
            xSemaphoreGive(sem);
        }
    }

    return ((SemaphoreP_Handle)sem);
}

/*
 *  ======== SemaphoreP_delete ========
 */
SemaphoreP_Status SemaphoreP_delete(SemaphoreP_Handle handle)
{
    vSemaphoreDelete((SemaphoreHandle_t)handle);
    return (SemaphoreP_OK);
}

/*
 *  ======== SemaphoreP_Params_init ========
 */
void SemaphoreP_Params_init(SemaphoreP_Params *params)
{
    params->mode = SemaphoreP_Mode_BINARY;
    params->name = NULL;
    params->maxCount = 1;
    params->callback = NULL;
}

/*
 *  ======== SemaphoreP_pend ========
 */
SemaphoreP_Status SemaphoreP_pend(SemaphoreP_Handle handle, uint32_t timeout)
{
    BaseType_t status;
    uint32_t ticks;
    uint32_t tickRateMS;

    if (timeout == SemaphoreP_WAIT_FOREVER) {
        ticks = portMAX_DELAY;
    }
    else {
        tickRateMS = (configTICK_RATE_HZ / 1000);
        /*
         * Don't wait if tick rate resolution is greater than 1ms and
         * prevent potential division by 0 when calculating the ticks to
         * delay.
         */
        if (tickRateMS == 0) {
            ticks = 0;
        }
        else {
            ticks = (timeout / tickRateMS);
        }
    }

    status = xSemaphoreTake((SemaphoreHandle_t)handle, ticks);

    if (status == pdTRUE) {
        return (SemaphoreP_OK);
    }

    return (SemaphoreP_TIMEOUT);
}

/*
 *  ======== SemaphoreP_post ========
 */
SemaphoreP_Status SemaphoreP_post(SemaphoreP_Handle handle)
{
       BaseType_t xHigherPriorityTaskWoken;
       BaseType_t result;
       SemaphoreP_Status status;

    if (!HwiP_inISR()) {
        /* Not in ISR */
        xSemaphoreGive((SemaphoreHandle_t)handle);
        status = SemaphoreP_OK;
    }
    else {
        result = xSemaphoreGiveFromISR((SemaphoreHandle_t)handle,
            &xHigherPriorityTaskWoken);

        if (result == pdTRUE) {
            status = SemaphoreP_OK;
        }
        else {
            /* The queue is full */
            status = SemaphoreP_FAILURE;
        }
    }
    return (status);
}

/*
 *  ======== SemaphoreP_postFromClock ========
 */
SemaphoreP_Status SemaphoreP_postFromClock(SemaphoreP_Handle handle)
{
    return (SemaphoreP_post(handle));
}
