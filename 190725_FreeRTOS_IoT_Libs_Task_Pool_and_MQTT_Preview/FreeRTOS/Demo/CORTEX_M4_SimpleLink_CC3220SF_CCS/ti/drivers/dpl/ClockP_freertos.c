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
 *  ======== ClockP_freertos.c ========
 */

#include <ti/drivers/dpl/ClockP.h>
#include <FreeRTOS.h>
#include <timers.h>

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

static TickType_t ticksToWait = portMAX_DELAY;

void ClockP_callbackFxn(uintptr_t arg);

typedef struct ClockP_FreeRTOSObj {
    TimerHandle_t    timer;
    ClockP_Fxn    fxn;
    uintptr_t        arg;
} ClockP_FreeRTOSObj;

/*
 *  ======== ClockP_callbackFxn ========
 */
void ClockP_callbackFxn(uintptr_t arg)
{
    TimerHandle_t    handle = (TimerHandle_t)arg;
    ClockP_FreeRTOSObj *obj;

    obj = (ClockP_FreeRTOSObj *)pvTimerGetTimerID(handle);
    (obj->fxn)(obj->arg);
}

/*
 *  ======== ClockP_create ========
 */
ClockP_Handle ClockP_create(ClockP_Fxn clockFxn, ClockP_Params *params)
{
    ClockP_Params defaultParams;
    ClockP_FreeRTOSObj *pObj;
    TimerHandle_t    handle = NULL;

    if (params == NULL) {
        params = &defaultParams;
        ClockP_Params_init(&defaultParams);
    }

    if ((pObj = pvPortMalloc(sizeof(ClockP_FreeRTOSObj))) == NULL) {
        return (NULL);
    }

    handle = xTimerCreate(params->name, 1, 0, (void *)pObj,
                          (TimerCallbackFunction_t)ClockP_callbackFxn);

    if (handle == NULL) {
        vPortFree(pObj);
        return (NULL);
    }

    pObj->timer = handle;
    pObj->fxn = clockFxn;
    pObj->arg = params->arg;

    return ((ClockP_Handle)pObj);
}

/*
 *  ======== ClockP_delete ========
 */
ClockP_Status ClockP_delete(ClockP_Handle handle)
{
    ClockP_FreeRTOSObj *pObj = (ClockP_FreeRTOSObj *)handle;
    BaseType_t status;

    status = xTimerDelete((TimerHandle_t)pObj->timer, ticksToWait);

    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }

    vPortFree(pObj);

    return (ClockP_OK);
}

/*
 *  ======== ClockP_getCpuFreq ========
 */
void ClockP_getCpuFreq(ClockP_FreqHz *freq)
{
    unsigned long configCpuFreq;

    /*
     *  configCPU_CLOCK_HZ is #define'd in the target's header file,
     *  eg, in FreeRTOS/Demo/ARM7_AT91FR40008_GCC/FreeRTOSConfig.h.
     *  Sometimes configCPU_CLOCK_HZ is #define'd to a specific value,
     *  or to an extern uint32_t variable, eg:
     *
     *  #define configCPU_CLOCK_HZ     ( SystemFrequency )  // extern uint32_t
     *
     *  #define configCPU_CLOCK_HZ     ( ( unsigned long ) 8000000 )
     */

    configCpuFreq = (unsigned long)configCPU_CLOCK_HZ;
    freq->lo = (uint32_t)configCpuFreq;
    freq->hi = 0;
//    freq->hi = (uint32_t)(configCpuFreq >> 32);
}

/*
 *  ======== ClockP_getSystemTickPeriod ========
 */
uint32_t ClockP_getSystemTickPeriod()
{
    uint32_t tickPeriodUs;

    /*
     *  Tick period in microseconds. configTICK_RATE_HZ is defined in the
     *  application's FreeRTOSConfig.h, which is include by FreeRTOS.h
     */
    tickPeriodUs = 1000000 / configTICK_RATE_HZ;

    return (tickPeriodUs);
}

/*
 *  ======== ClockP_getSystemTicks ========
 *  TODO determine if we ever call this from an ISR
 */
uint32_t ClockP_getSystemTicks()
{
    return ((uint32_t)xTaskGetTickCount());
}

/*
 *  ======== ClockP_Params_init ========
 */
void ClockP_Params_init(ClockP_Params *params)
{
    params->name = NULL;
    params->arg = (uintptr_t)0;
}

/*
 *  ======== ClockP_start ========
 */
ClockP_Status ClockP_start(ClockP_Handle handle, uint32_t timeout)
{
    ClockP_FreeRTOSObj *pObj = (ClockP_FreeRTOSObj *)handle;
    BaseType_t status;

    status = xTimerChangePeriod(pObj->timer, (TickType_t)timeout, ticksToWait);

    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }
    status = xTimerStart(pObj->timer, ticksToWait);

    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }

    return (ClockP_OK);
}

/*
 *  ======== ClockP_startFromISR ========
 */
ClockP_Status ClockP_startFromISR(ClockP_Handle handle, uint32_t timeout)
{
    ClockP_FreeRTOSObj *pObj = (ClockP_FreeRTOSObj *)handle;
    BaseType_t xHigherPriorityTaskWoken;
    BaseType_t status;

    status = xTimerChangePeriodFromISR(pObj->timer, (TickType_t)timeout,
                                       &xHigherPriorityTaskWoken);
    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }
    status = xTimerStartFromISR(pObj->timer, &xHigherPriorityTaskWoken);

    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }

    return (ClockP_OK);
}

/*
 *  ======== ClockP_stop ========
 */
ClockP_Status ClockP_stop(ClockP_Handle handle)
{
    ClockP_FreeRTOSObj *pObj = (ClockP_FreeRTOSObj *)handle;
    BaseType_t status;

    status = xTimerStop(pObj->timer, ticksToWait);

    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }
    return (ClockP_OK);
}

/*
 *  ======== ClockP_stopFromISR ========
 */
ClockP_Status ClockP_stopFromISR(ClockP_Handle handle)
{
    ClockP_FreeRTOSObj *pObj = (ClockP_FreeRTOSObj *)handle;
    BaseType_t xHigherPriorityTaskWoken;
    BaseType_t status;

    status = xTimerStopFromISR(pObj->timer, &xHigherPriorityTaskWoken);

    if (status != pdPASS) {
        return (ClockP_FAILURE);
    }
    return (ClockP_OK);
}

/*
 *  ======== ClockP_sleep ========
 */
ClockP_Status ClockP_sleep(uint32_t sec)
{
    uint32_t msecs = sec * 1000;
    TickType_t xDelay;

    /* Take the ceiling */
    xDelay = (msecs + portTICK_PERIOD_MS - 1) / portTICK_PERIOD_MS;

    vTaskDelay(xDelay);

    return (ClockP_OK);
}

/*
 *  ======== ClockP_usleep ========
 */
ClockP_Status ClockP_usleep(uint32_t usec)
{
    uint32_t msecs = (usec + 999) / 1000;
    TickType_t xDelay;

    /* Take the ceiling */
    xDelay = (msecs + portTICK_PERIOD_MS - 1) / portTICK_PERIOD_MS;

    vTaskDelay(xDelay);

    return (ClockP_OK);
}
