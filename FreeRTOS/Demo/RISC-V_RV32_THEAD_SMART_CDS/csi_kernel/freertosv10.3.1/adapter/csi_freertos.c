/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


/******************************************************************************
 * @file     csi_freertos.c
 * @brief    the adapter file for the freertos
 * @version  V1.0
 * @date     20. July 2016
 ******************************************************************************/
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <csi_kernel.h>
#include <csi_config.h>
#include <soc.h>

/* FreeRTOS includes. */
#include <FreeRTOSConfig.h>
#include <FreeRTOS.h>
#include <portmacro.h>
#include <portable.h>
#include <task.h>
#include <timers.h>
#include <list.h>
#include <queue.h>
#include <semphr.h>
#include <event_groups.h>

#include <mm.h>
#include <umm_heap.h>

#define DONT_BLOCK    0
#define VALUE_BEFORE_TIMER_START    1

#define IS_BIT_SET(reg, pos) (((reg) & (1u << (pos))) != 0x0u)

static uint32_t CK_IN_INTRP(void)
{
#ifdef __CSKY__
    uint32_t vec = 0;

    vec = (__get_PSR() & PSR_VEC_Msk) >> PSR_VEC_Pos;

    if (vec >= 32 || (vec == 10)) {
        return 1;
    } else {
        return 0;
    }

#else
    uint32_t val = 0;
    val = __get_MINTSTATUS();

    if (val & 0xFF0000000) {
        return 1;
    } else {
        return 0;
    }

#endif
}


k_status_t csi_kernel_init(void)
{
    return 0;
}

k_status_t csi_kernel_start(void)
{
    vTaskStartScheduler();
    return 0;
}

k_sched_stat_t csi_kernel_get_stat(void)
{
#if ( ( INCLUDE_xTaskGetSchedulerState == 1 ) || ( configUSE_TIMERS == 1 ) )

    switch (xTaskGetSchedulerState()) {
        case 0:
            return KSCHED_ST_SUSPEND;
            break;

        case 1:
            return KSCHED_ST_INACTIVE;
            break;

        case 2:
            return KSCHED_ST_RUNNING;
            break;

        default:
            return KTASK_ST_ERROR;
    }

#endif
}

int32_t csi_kernel_sched_lock(void)
{
    return -EOPNOTSUPP;
}

int32_t csi_kernel_sched_unlock(void)
{
    return -EOPNOTSUPP;
}

int32_t csi_kernel_sched_restore_lock(int32_t lock)
{
    return -EOPNOTSUPP;
}

uint32_t csi_kernel_sched_suspend(void)
{
    vTaskSuspendAll();

    return 0;
}

void csi_kernel_sched_resume(uint32_t sleep_ticks)
{
    __attribute__((unused)) BaseType_t ret;

    ret = xTaskResumeAll();
}

k_status_t csi_kernel_task_new(k_task_entry_t task, const char *name, void *arg,
                               k_priority_t prio, uint32_t time_quanta,
                               void *stack, uint32_t stack_size, k_task_handle_t *task_handle)
{
    if ((task_handle == NULL) || (task == NULL) || (stack_size % 4 != 0) || ((stack_size == 0) && (stack == NULL)) || prio <= KPRIO_IDLE || prio > KPRIO_REALTIME7) {
        return -EINVAL;
    }

    if (name == NULL) {
        name = "default_name";
    }

    TaskHandle_t handle_ret;
    //you can change time_quanta through modifing configTICK_RATE_HZ.
    csi_kernel_sched_suspend();
    BaseType_t ret = xTaskCreate(task, name, stack_size / 4, arg, prio, &handle_ret);

    if (ret == pdPASS) {
        *task_handle = handle_ret;
        csi_kernel_sched_resume(0);
        return 0;
    } else {
        return -EPERM;
    }
}

k_status_t csi_kernel_task_del(k_task_handle_t task_handle)
{
    if (task_handle == NULL) {
        return -EINVAL;
    }

#if ( INCLUDE_vTaskDelete == 1 )
    vTaskDelete(task_handle);
#endif
    return 0;
}

k_task_handle_t csi_kernel_task_get_cur(void)
{
#if ( ( INCLUDE_xTaskGetCurrentTaskHandle == 1 ) || ( configUSE_MUTEXES == 1 ) )
    return xTaskGetCurrentTaskHandle();
#endif
}

k_task_stat_t csi_kernel_task_get_stat(k_task_handle_t task_handle)
{
    if (task_handle  == NULL) {
        return KTASK_ST_ERROR;
    }

#if ( INCLUDE_eTaskGetState == 1 )

    switch (eTaskGetState(task_handle)) {
        case 0:
            return KTASK_ST_RUNNING;
            break;

        case 1:
            return KTASK_ST_READY;
            break;

        case 2:
            return KTASK_ST_BLOCKED;
            break;

        case 3:
            return KTASK_ST_BLOCKED;
            break;

        case 4:
            return KTASK_ST_TERMINATED;
            break;

        default:
            return KTASK_ST_ERROR;
    }

#endif
}

k_status_t csi_kernel_task_set_prio(k_task_handle_t task_handle, k_priority_t priority)
{
    if (task_handle  == NULL || priority <= KPRIO_IDLE || priority > KPRIO_REALTIME7) {
        return -EINVAL;
    }

#if ( INCLUDE_vTaskPrioritySet == 1 )
    vTaskPrioritySet(task_handle, priority);
#endif
    return 0;
}

k_priority_t csi_kernel_task_get_prio(k_task_handle_t task_handle)
{
    if (task_handle  == NULL) {
        return KPRIO_ERROR;
    }

#if ( INCLUDE_uxTaskPriorityGet == 1 )
    return uxTaskPriorityGet(task_handle);
#endif
}

const char *csi_kernel_task_get_name(k_task_handle_t task_handle)
{
#if ( ( configUSE_TRACE_FACILITY == 1 ) && ( configUSE_STATS_FORMATTING_FUNCTIONS > 0 ) )

    if (task_handle == NULL) {
        return NULL;
    }

    const char *name = NULL;
    TaskStatus_t *pxTaskStatusArray;
    volatile UBaseType_t x;

    volatile UBaseType_t uxArraySize = uxTaskGetNumberOfTasks();
    volatile UBaseType_t real = uxArraySize;

    pxTaskStatusArray = pvPortMalloc(uxArraySize * sizeof(TaskStatus_t));
    TaskStatus_t *p = pxTaskStatusArray;

    if (pxTaskStatusArray != NULL) {
        uxTaskGetSystemState(pxTaskStatusArray, real, NULL);

        for (x = 0; x < uxArraySize; x++) {
            if (task_handle == pxTaskStatusArray[x].xHandle) {
                name = pxTaskStatusArray[x].pcTaskName;
                break;
            }
        }

        vPortFree(p);
    }

    return name;
#else
    return NULL;
#endif
}

k_status_t csi_kernel_task_suspend(k_task_handle_t task_handle)
{
    if (task_handle  == NULL) {
        return -EINVAL;
    }

#if ( INCLUDE_vTaskSuspend == 1 )
    vTaskSuspend(task_handle);
#endif
    return 0;
}

k_status_t csi_kernel_task_resume(k_task_handle_t task_handle)
{
    if (task_handle  == NULL) {
        return -EINVAL;
    }

#if ( INCLUDE_vTaskSuspend == 1 )
    vTaskResume(task_handle);
#endif
    return 0;
}

k_status_t csi_kernel_task_terminate(k_task_handle_t task_handle)
{
    return csi_kernel_task_del(task_handle);
}

void csi_kernel_task_exit(void)
{
    csi_kernel_task_del(csi_kernel_task_get_cur());
}

k_status_t csi_kernel_task_yield(void)
{
    taskYIELD();
    return 0;
}

uint32_t csi_kernel_task_get_count(void)
{
    return uxTaskGetNumberOfTasks();
}

uint32_t csi_kernel_task_get_stack_size(k_task_handle_t task_handle)
{
    return 0;
}

uint32_t csi_kernel_task_get_stack_space(k_task_handle_t task_handle)
{
    if (task_handle == NULL) {
        return 0;
    }

#if (INCLUDE_uxTaskGetStackHighWaterMark == 1)
    return 4 * (uxTaskGetStackHighWaterMark(task_handle));
#else
    return 0;
#endif
}

uint32_t csi_kernel_task_list(k_task_handle_t *task_array, uint32_t array_items)
{
#if ( ( configUSE_TRACE_FACILITY == 1 ) && ( configUSE_STATS_FORMATTING_FUNCTIONS > 0 ) )

    if (task_array == NULL || array_items == 0) {
        return 0;
    }

    k_task_handle_t *tk_tmp = task_array;
    TaskStatus_t *pxTaskStatusArray;
    volatile UBaseType_t x;

    volatile UBaseType_t uxArraySize = uxTaskGetNumberOfTasks();
    volatile UBaseType_t real;

    if (array_items < uxArraySize) {
        uxArraySize = array_items;
    }

    real = uxArraySize;
    pxTaskStatusArray = pvPortMalloc(real * sizeof(TaskStatus_t));
    TaskStatus_t *p = pxTaskStatusArray;

    if (pxTaskStatusArray != NULL) {
        uxTaskGetSystemState(pxTaskStatusArray, real, NULL);

        for (x = 0; x < real; x++) {
            *tk_tmp = pxTaskStatusArray[ x ].xHandle;
            tk_tmp ++;
        }

        // The array is no longer needed, free the memory it consumes.
        vPortFree(p);
    }

    return (uint32_t)real;
#endif
    return 0;
}

k_status_t csi_kernel_intrpt_enter(void)
{
    return 0;
}

k_status_t csi_kernel_intrpt_exit(void)
{
    portYIELD_FROM_ISR(pdTRUE);
    return 0;
}

k_status_t csi_kernel_delay(uint32_t ticks)
{
#if ( INCLUDE_vTaskDelay == 1 )
#if ( configUSE_16_BIT_TICKS == 1 )
    ticks = (uint16_t) ticks;
#endif
    vTaskDelay(ticks);
#endif
    return 0;
}

k_status_t csi_kernel_delay_until(uint64_t ticks)
{
#if ( INCLUDE_vTaskDelayUntil == 1 )

    if (ticks > (uint64_t) 0xffffffff) {
        return -EINVAL;
    }

    if (ticks == 0U) {
        return 0;
    }

    uint32_t xLastWakeTime;
    xLastWakeTime = xTaskGetTickCount();

    if (ticks <=  xLastWakeTime) {
        return 0;
    }

    vTaskDelayUntil(&xLastWakeTime, ticks - xLastWakeTime);
#endif
    return 0;
}

uint64_t csi_kernel_tick2ms(uint32_t ticks)
{
    return ((uint64_t)ticks * portTICK_PERIOD_MS);
}

uint64_t csi_kernel_ms2tick(uint32_t ms)
{
    return ((uint64_t)ms / portTICK_PERIOD_MS);
}

k_status_t csi_kernel_delay_ms(uint32_t ms)
{
#if ( INCLUDE_vTaskDelay == 1 )
    uint32_t ms_get = ms;

    if ((ms != 0) && (ms < portTICK_PERIOD_MS)) {
        ms_get = portTICK_PERIOD_MS;
    }

    uint64_t ticks = csi_kernel_ms2tick(ms_get);
    vTaskDelay(ticks);
#endif
    return 0;
}

uint64_t csi_kernel_get_ticks(void)
{
    return xTaskGetTickCount();
}

void csi_kernel_update_tick(uint32_t ms)
{
}

uint32_t csi_kernel_get_tick_freq(void)
{
    return configTICK_RATE_HZ;
}

uint32_t csi_kernel_get_systimer_freq(void)
{
    return drv_get_sys_freq();
}

typedef struct tmr_adapter {
    TimerHandle_t timer;
    k_timer_cb_t func;
    void *func_arg;
    k_timer_type_t type;
    k_timer_stat_t stat;
} tmr_adapter_t;

static void tmr_adapt_cb(TimerHandle_t xTimer)
{
    tmr_adapter_t *id = pvTimerGetTimerID(xTimer);
    id->func(id->func_arg);

    if (id->type == KTIMER_TYPE_ONCE) {
        id->stat = KTIMER_ST_INACTIVE;
    }

    return;
}

k_timer_handle_t csi_kernel_timer_new(k_timer_cb_t func, k_timer_type_t type, void *arg)
{
    if (type < 0 || type > 3 || func == NULL) {
        return NULL;
    }

    tmr_adapter_t *tmr_adapter = pvPortMalloc(sizeof(tmr_adapter_t));

    if (tmr_adapter == NULL) {
        return NULL;
    }

    tmr_adapter->func = func;
    tmr_adapter->func_arg = arg;
    tmr_adapter->type = type;
    tmr_adapter->stat = KTIMER_ST_INACTIVE;

    TimerHandle_t timer = xTimerCreate("Timer", VALUE_BEFORE_TIMER_START, type, tmr_adapter, tmr_adapt_cb);

    if (timer != NULL) {
        tmr_adapter->timer = timer;
        return tmr_adapter;
    } else {
        vPortFree(tmr_adapter);
        return NULL;
    }
}

k_status_t csi_kernel_timer_del(k_timer_handle_t timer_handle)
{
    if (timer_handle == NULL) {
        return -EINVAL;
    }

    tmr_adapter_t *tmr_adapter = timer_handle;

    int ret = xTimerDelete(tmr_adapter->timer, DONT_BLOCK);

    if (!ret) {
        return -EPERM;
    }

    vPortFree(tmr_adapter);

    return 0;
}

k_status_t csi_kernel_timer_start(k_timer_handle_t timer_handle, uint32_t ticks)
{
    if (timer_handle == NULL || ticks == 0) {
        return -EINVAL;
    }

    tmr_adapter_t *tmr_adapter = timer_handle;

    xTimerChangePeriod(tmr_adapter->timer, ticks, DONT_BLOCK);
    int tmp = xTimerStart(tmr_adapter->timer, DONT_BLOCK);

    if (tmp == 0) {
        return -ETIMEDOUT;
    } else if (tmp == 1) {
        tmr_adapter->stat = KTIMER_ST_ACTIVE;
        return 0;
    }

    return 0;
}

k_status_t csi_kernel_timer_stop(k_timer_handle_t timer_handle)
{
    if (timer_handle == NULL) {
        return -EINVAL;
    }

    tmr_adapter_t *tmr_adapter = timer_handle;

    int tmp;
    tmp = xTimerStop(tmr_adapter->timer, DONT_BLOCK);

    if (tmp == 0) {
        return -ETIMEDOUT;
    }

    if (tmp == 1) {
        tmr_adapter->stat = KTIMER_ST_INACTIVE;
        return 0;
    }

    return 0;
}

k_timer_stat_t csi_kernel_timer_get_stat(k_timer_handle_t timer_handle)
{
    if (timer_handle == NULL) {
        return KTIMER_ST_INACTIVE;
    }

    tmr_adapter_t *tmr_adapter = timer_handle;

    return tmr_adapter->stat;
}

k_event_handle_t csi_kernel_event_new(void)
{
    return xEventGroupCreate();
}

k_status_t csi_kernel_event_del(k_event_handle_t ev_handle)
{
    if (ev_handle == NULL) {
        return -EINVAL;
    }

    vEventGroupDelete(ev_handle);
    return 0;
}

k_status_t csi_kernel_event_set(k_event_handle_t ev_handle, uint32_t flags, uint32_t *ret_flags)
{
    if (ev_handle == NULL || ret_flags == NULL) {
        return -EINVAL;
    }

    if ((flags & 0xff000000UL) != 0) {
        return -EPERM;
    }

    EventBits_t ret = xEventGroupSetBits(ev_handle, flags);
    *ret_flags = ret;
    return 0;
}

k_status_t csi_kernel_event_clear(k_event_handle_t ev_handle, uint32_t flags, uint32_t *ret_flags)
{
    if (ev_handle == NULL || ret_flags == NULL) {
        return -EINVAL;
    }

    if ((flags & 0xff000000UL) != 0) {
        return -EPERM;
    }

    EventBits_t ret = xEventGroupClearBits(ev_handle, flags);
    *ret_flags = ret;
    return 0;
}

k_status_t csi_kernel_event_get(k_event_handle_t ev_handle, uint32_t *ret_flags)
{
    if (ev_handle == NULL || ret_flags == NULL) {
        return -EINVAL;
    }

    EventBits_t ret = xEventGroupGetBits(ev_handle);
    *ret_flags = ret;
    return 0;
}

k_status_t csi_kernel_event_wait(k_event_handle_t ev_handle, uint32_t flags,
                                 k_event_opt_t options, uint8_t clr_on_exit,
                                 uint32_t *actl_flags, int32_t timeout)
{
    if (ev_handle == NULL || actl_flags == NULL
        || ((clr_on_exit != 0) && (clr_on_exit != 1))
        || flags == 0u) {
        return -EINVAL;
    }

    if ((xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED) && timeout != 0) {
        return -EPERM;
    }

    if (timeout < 0) {
        timeout = portMAX_DELAY;
    }

    if ((flags & 0xff000000UL) != 0) {
        return -EPERM;
    }

    if (options == KEVENT_OPT_CLR_ANY || options == KEVENT_OPT_CLR_ALL) {
        return -EOPNOTSUPP;
    }

    EventBits_t event_val = 0;

    if (options == KEVENT_OPT_SET_ANY) {
        event_val = xEventGroupWaitBits(ev_handle, flags, clr_on_exit, 0, timeout);
        *actl_flags = event_val;
        uint32_t i = 0, ebit = 0, fbit = 0;

        for (; i < 24; i++) {
            ebit = IS_BIT_SET(event_val, i);
            fbit = IS_BIT_SET(flags, i);

            if (ebit == 1 && fbit == 1) {
                return 0;
            }
        }

        return -ETIMEDOUT;
    } else if (options == KEVENT_OPT_SET_ALL) {
        event_val = xEventGroupWaitBits(ev_handle, flags, clr_on_exit, 1, timeout);
        *actl_flags = event_val;

        if ((event_val & flags) == flags) {
            return 0;
        } else {
            return -ETIMEDOUT;
        }
    }

    *actl_flags = event_val;
    return 0;
}

k_mutex_handle_t csi_kernel_mutex_new(void)
{
#if ( configUSE_MUTEXES == 1 )
    return xSemaphoreCreateMutex();
#endif
}

k_status_t csi_kernel_mutex_del(k_mutex_handle_t mutex_handle)
{
    if (mutex_handle == NULL) {
        return -EINVAL;
    }

    vSemaphoreDelete(mutex_handle);
    return 0;
}

k_status_t csi_kernel_mutex_lock(k_mutex_handle_t mutex_handle, int32_t timeout)
{
    int tmp = 0;

    if (mutex_handle == NULL) {
        return -EINVAL;
    }

    if ((xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED) && timeout != 0) {
        return -EPERM;
    }

    if (timeout < 0) {
        timeout = portMAX_DELAY;
    }

    if (CK_IN_INTRP()) {
        tmp = xSemaphoreTakeFromISR(mutex_handle, NULL);
        goto out;
    }

    tmp = xSemaphoreTake(mutex_handle, timeout);

out:

    if (tmp) {
        return 0;
    } else {
        return -EBUSY;
    }
}

k_status_t csi_kernel_mutex_unlock(k_mutex_handle_t mutex_handle)
{
    int tmp = 0;

    if (mutex_handle == NULL) {
        return -EINVAL;
    }

#if ( ( configUSE_MUTEXES == 1 ) && ( INCLUDE_xSemaphoreGetMutexHolder == 1 ) )
#if ( ( INCLUDE_xTaskGetCurrentTaskHandle == 1 ) || ( configUSE_MUTEXES == 1 ) )

    if (!(xSemaphoreGetMutexHolder(mutex_handle) == xTaskGetCurrentTaskHandle())) {
        return -EPERM;
    }

#endif
#endif

    if (CK_IN_INTRP()) {
        tmp = xSemaphoreGiveFromISR(mutex_handle, NULL);
        goto out;
    }

    tmp = xSemaphoreGive(mutex_handle);

out:

    if (tmp) {
        return 0;
    } else {
        return -EBUSY;
    }
}

k_task_handle_t csi_kernel_mutex_get_owner(k_mutex_handle_t mutex_handle)
{
    if (mutex_handle == NULL) {
        return NULL;
    }

    return xSemaphoreGetMutexHolder(mutex_handle);
}

k_sem_handle_t csi_kernel_sem_new(int32_t max_count, int32_t initial_count)
{
    if (max_count <= 0 || initial_count < 0) {
        return NULL;
    }

    if (max_count < initial_count) {
        return NULL;
    }

    return xSemaphoreCreateCounting(max_count, initial_count);
}

k_status_t csi_kernel_sem_del(k_sem_handle_t sem_handle)
{
    if (sem_handle == NULL) {
        return -EINVAL;
    }

    vSemaphoreDelete(sem_handle);
    return 0;
}

k_status_t csi_kernel_sem_wait(k_sem_handle_t sem_handle, int32_t timeout)
{
    int tmp = 0;

    if (sem_handle == NULL) {
        return -EINVAL;
    }

    if (timeout < 0) {
        timeout = portMAX_DELAY;
    }

    if (CK_IN_INTRP()) {
        tmp = xSemaphoreTakeFromISR(sem_handle, NULL);
        goto out;
    }

    tmp = xSemaphoreTake(sem_handle, timeout);

out:

    if (tmp) {
        return 0;
    } else {
        return -EBUSY;
    }
}

k_status_t csi_kernel_sem_post(k_sem_handle_t sem_handle)
{
    int tmp = 0;

    if (sem_handle == NULL) {
        return -EINVAL;
    }

    if (CK_IN_INTRP()) {
        tmp = xSemaphoreGiveFromISR(sem_handle, NULL);
        goto out;
    }

    tmp = xSemaphoreGive(sem_handle);

out:

    if (tmp) {
        return 0;
    } else {
        return -EBUSY;
    }
}

int32_t csi_kernel_sem_get_count(k_sem_handle_t sem_handle)
{
    if (sem_handle == NULL) {
        return -EINVAL;
    }

    return uxSemaphoreGetCount(sem_handle);
}

k_mpool_handle_t csi_kernel_mpool_new(void *p_addr, int32_t block_count, int32_t block_size)
{
    return NULL;
}

k_status_t csi_kernel_mpool_del(k_mpool_handle_t mp_handle)
{
    return 0;
}

void *csi_kernel_mpool_alloc(k_mpool_handle_t mp_handle, int32_t timeout)
{
    return NULL;
}

k_status_t csi_kernel_mpool_free(k_mpool_handle_t mp_handle, void *block)
{
    return -EOPNOTSUPP;
}

int32_t csi_kernel_mpool_get_count(k_mpool_handle_t mp_handle)
{
    return 0;
}

uint32_t csi_kernel_mpool_get_capacity(k_mpool_handle_t mp_handle)
{
    if (!mp_handle) {
        return 0;
    }

    return 0;
}

uint32_t csi_kernel_mpool_get_block_size(k_mpool_handle_t mp_handle)
{
    if (!mp_handle) {
        return 0;
    }

    return 0;
}

k_msgq_handle_t csi_kernel_msgq_new(int32_t msg_count, int32_t msg_size)
{
    if (msg_count <= 0 || msg_size <= 0) {
        return NULL;
    }

    return xQueueCreate(msg_count, msg_size);
}

k_status_t csi_kernel_msgq_del(k_msgq_handle_t mq_handle)
{
    if (!mq_handle) {
        return -EINVAL;
    }

    vQueueDelete(mq_handle);
    return 0;
}

k_status_t csi_kernel_msgq_put(k_msgq_handle_t mq_handle, const void *msg_ptr, uint8_t front_or_back, int32_t timeout)
{
    int  tmp = 0;

    if ((!mq_handle) || (msg_ptr == NULL) || ((front_or_back != 0) && (front_or_back != 1))) {
        return -EINVAL;
    }

    if (timeout < 0) {
        timeout = portMAX_DELAY;
    }

    if (CK_IN_INTRP()) {
        if (front_or_back == 1) {
            tmp = xQueueSendToFrontFromISR(mq_handle, msg_ptr, NULL);
            goto out;
        } else if (front_or_back == 0) {
            tmp = xQueueSendToBackFromISR(mq_handle, msg_ptr, NULL);
            goto out;
        }
    }

    if (front_or_back == 1) {
        tmp = xQueueSendToFront(mq_handle, msg_ptr, timeout);
    } else if (front_or_back == 0) {
        tmp = xQueueSendToBack(mq_handle, msg_ptr, timeout);
    }

out:

    if (tmp == 1) {
        return 0;
    } else if (tmp == 0) {
        return -EBUSY;
    }

    return 0;
}

k_status_t csi_kernel_msgq_get(k_msgq_handle_t mq_handle, void *msg_ptr, int32_t timeout)
{
    int tmp = 0;
    void *get_ptr = msg_ptr;

    if (mq_handle == NULL || get_ptr == NULL) {
        return -EINVAL;
    }

    if (timeout < 0) {
        timeout = portMAX_DELAY;
    }

    if (CK_IN_INTRP()) {
        tmp = xQueueReceiveFromISR(mq_handle, get_ptr, NULL);
        goto out;
    }

    tmp = xQueueReceive(mq_handle, get_ptr, timeout);

out:

    if (tmp) {
        return 0;
    } else {
        return -EBUSY;
    }
}

int32_t csi_kernel_msgq_get_count(k_msgq_handle_t mq_handle)
{
    if (mq_handle == NULL) {
        return -EINVAL;
    }

    if (CK_IN_INTRP()) {
        return uxQueueMessagesWaitingFromISR(mq_handle);
    }

    return uxQueueMessagesWaiting(mq_handle);
}

uint32_t csi_kernel_msgq_get_capacity(k_msgq_handle_t mq_handle)
{
    if (mq_handle == NULL) {
        return 0;
    }

    return csi_kernel_msgq_get_count(mq_handle) + uxQueueSpacesAvailable(mq_handle);
}

uint32_t csi_kernel_msgq_get_msg_size(k_msgq_handle_t mq_handle)
{
    return 0;
}

k_status_t csi_kernel_msgq_flush(k_msgq_handle_t mq_handle)
{
    if (mq_handle == NULL) {
        return -EINVAL;
    }

    xQueueReset(mq_handle);
    return 0;
}

void *csi_kernel_malloc(int32_t size, void *caller)
{
    if (size == 0 || size >= configTOTAL_HEAP_SIZE) {
        return NULL;
    }

    void *ret;
    ret = pvPortMalloc(size);

    return ret;
}

void csi_kernel_free(void *ptr, void *caller)
{
    if (!ptr) {
        return ;
    }

    vPortFree(ptr);
}

void *csi_kernel_realloc(void *ptr, int32_t size, void *caller)
{
    void *new_ptr;

    new_ptr = csi_kernel_malloc(size, caller);

    if (new_ptr == NULL) {
        return new_ptr;
    }

    if (ptr) {
        memcpy(new_ptr, ptr, size);
        csi_kernel_free(ptr, caller);
    }

    return new_ptr;
}

k_status_t csi_kernel_get_mminfo(int32_t *total, int32_t *used, int32_t *free, int32_t *peak)
{
    return 0;
}

k_status_t csi_kernel_mm_dump(void)
{
    return 0;
}
