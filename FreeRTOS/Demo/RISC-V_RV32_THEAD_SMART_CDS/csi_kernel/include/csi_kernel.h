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
 * @file     csi_kernel.h
 * @brief    header file for kernel definition
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#ifndef _CSI_KERNEL_
#define _CSI_KERNEL_


#include <stdint.h>
#include <errno.h>

#ifdef  __cplusplus
extern "C"
{
#endif


/* =================================================================================== */
/*                         Enumerations, structures, defines                           */
/* =================================================================================== */

/// Status code values returned by CSI-kernel functions. 0 - success, negative represents error code ,see errno.h
typedef int32_t k_status_t;

/// Kernel scheduler state.
typedef enum {
    KSCHED_ST_INACTIVE         =  0,         ///< Inactive: The kernel is not ready yet. csi_kernel_init needs to be executed successfully.
    KSCHED_ST_READY            =  1,         ///< Ready: The kernel is not yet running. csi_kernel_start transfers the kernel to the running state.
    KSCHED_ST_RUNNING          =  2,         ///< Running: The kernel is initialized and running.
    KSCHED_ST_LOCKED           =  3,         ///< Locked: The kernel was locked with csi_kernel_sched_lock. The functions csi_kernel_sched_unlock or csi_kernel_sched_restore_lock unlocks it.
    KSCHED_ST_SUSPEND          =  4,         ///< Suspended: The kernel was suspended using csi_kernel_sched_suspend. The function csi_kernel_sched_resume returns to normal operation
    KSCHED_ST_ERROR            =  5          ///< Error: An error occurred.
} k_sched_stat_t;

/// task state.
typedef enum {
    KTASK_ST_INACTIVE          =  0,         ///< Inactive.
    KTASK_ST_READY             =  1,         ///< Ready.
    KTASK_ST_RUNNING           =  2,         ///< Running.
    KTASK_ST_BLOCKED           =  3,         ///< Blocked.
    KTASK_ST_TERMINATED        =  4,         ///< Terminated.
    KTASK_ST_ERROR             =  5          ///< Error: An error occurred.
} k_task_stat_t;

/// timer state.
typedef enum {
    KTIMER_ST_INACTIVE       = 0,          ///< not running
    KTIMER_ST_ACTIVE         = 1,          ///< running
} k_timer_stat_t;

/// Timer type.
typedef enum {
    KTIMER_TYPE_ONCE         = 0,          ///< One-shot timer.
    KTIMER_TYPE_PERIODIC     = 1           ///< Repeating timer.
} k_timer_type_t;

/// event option.
typedef enum {
    KEVENT_OPT_SET_ANY       = 0,          ///< Check any bit in flags to be 1.
    KEVENT_OPT_SET_ALL       = 1,          ///< Check all bits in flags to be 1.
    KEVENT_OPT_CLR_ANY       = 2,          ///< Check any bit in flags to be 0.
    KEVENT_OPT_CLR_ALL       = 3           ///< Check all bits in flags to be 0.
} k_event_opt_t;

/// Priority definition.
typedef enum  {
    KPRIO_IDLE            = 0,          ///< priority: idle (lowest)
    KPRIO_LOW0               ,          ///< priority: low
    KPRIO_LOW1               ,          ///< priority: low + 1
    KPRIO_LOW2               ,          ///< priority: low + 2
    KPRIO_LOW3               ,          ///< priority: low + 3
    KPRIO_LOW4               ,          ///< priority: low + 4
    KPRIO_LOW5               ,          ///< priority: low + 5
    KPRIO_LOW6               ,          ///< priority: low + 6
    KPRIO_LOW7               ,          ///< priority: low + 7
    KPRIO_NORMAL_BELOW0      ,          ///< priority: below normal
    KPRIO_NORMAL_BELOW1      ,          ///< priority: below normal + 1
    KPRIO_NORMAL_BELOW2      ,          ///< priority: below normal + 2
    KPRIO_NORMAL_BELOW3      ,          ///< priority: below normal + 3
    KPRIO_NORMAL_BELOW4      ,          ///< priority: below normal + 4
    KPRIO_NORMAL_BELOW5      ,          ///< priority: below normal + 5
    KPRIO_NORMAL_BELOW6      ,          ///< priority: below normal + 6
    KPRIO_NORMAL_BELOW7      ,          ///< priority: below normal + 7
    KPRIO_NORMAL             ,          ///< priority: normal (default)
    KPRIO_NORMAL1            ,          ///< priority: normal + 1
    KPRIO_NORMAL2            ,          ///< priority: normal + 2
    KPRIO_NORMAL3            ,          ///< priority: normal + 3
    KPRIO_NORMAL4            ,          ///< priority: normal + 4
    KPRIO_NORMAL5            ,          ///< priority: normal + 5
    KPRIO_NORMAL6            ,          ///< priority: normal + 6
    KPRIO_NORMAL7            ,          ///< priority: normal + 7
    KPRIO_NORMAL_ABOVE0      ,          ///< priority: above normal + 1
    KPRIO_NORMAL_ABOVE1      ,          ///< priority: above normal + 2
    KPRIO_NORMAL_ABOVE2      ,          ///< priority: above normal + 3
    KPRIO_NORMAL_ABOVE3      ,          ///< priority: above normal + 4
    KPRIO_NORMAL_ABOVE4      ,          ///< priority: above normal + 5
    KPRIO_NORMAL_ABOVE5      ,          ///< priority: above normal + 6
    KPRIO_NORMAL_ABOVE6      ,          ///< priority: above normal + 7
    KPRIO_NORMAL_ABOVE7      ,          ///< priority: above normal + 8
    KPRIO_HIGH0              ,          ///< priority: high
    KPRIO_HIGH1              ,          ///< priority: high + 1
    KPRIO_HIGH2              ,          ///< priority: high + 2
    KPRIO_HIGH3              ,          ///< priority: high + 3
    KPRIO_HIGH4              ,          ///< priority: high + 4
    KPRIO_HIGH5              ,          ///< priority: high + 5
    KPRIO_HIGH6              ,          ///< priority: high + 6
    KPRIO_HIGH7              ,          ///< priority: high + 7
    KPRIO_REALTIME0          ,          ///< priority: realtime + 1
    KPRIO_REALTIME1          ,          ///< priority: realtime + 2
    KPRIO_REALTIME2          ,          ///< priority: realtime + 3
    KPRIO_REALTIME3          ,          ///< priority: realtime + 4
    KPRIO_REALTIME4          ,          ///< priority: realtime + 5
    KPRIO_REALTIME5          ,          ///< priority: realtime + 6
    KPRIO_REALTIME6          ,          ///< priority: realtime + 7
    KPRIO_REALTIME7          ,          ///< priority: realtime + 8
    KPRIO_ISR                ,          ///< priority: Reserved for ISR deferred thread
    KPRIO_ERROR                         ///< Illegal priority
} k_priority_t;

/// Entry point of a task.
typedef void (*k_task_entry_t)(void *arg);

/// Entry point of a timer call back function.
typedef void (*k_timer_cb_t)(void *arg);

/// \details Task handle identifies the task.
typedef void *k_task_handle_t;

/// \details Timer handle identifies the timer.
typedef void *k_timer_handle_t;

/// \details Event Flags handle identifies the event flags.
typedef void *k_event_handle_t;

/// \details Mutex handle identifies the mutex.
typedef void *k_mutex_handle_t;

/// \details Semaphore handle identifies the semaphore.
typedef void *k_sem_handle_t;

/// \details Memory Pool handle identifies the memory pool.
typedef void *k_mpool_handle_t;

/// \details Message Queue handle identifies the message queue.
typedef void *k_msgq_handle_t;



/* =================================================================================== */
/*                          Kernel Management Functions                                */
/* =================================================================================== */

/// Initialize the Kernel. Before it is successfully executed, no RTOS function should be called
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_init(void);

/// Start the kernel .It will not return to its calling function in case of success
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_start(void);

/// Get the current kernel state.
/// \return current kernel state \ref k_sched_stat_t .
k_sched_stat_t csi_kernel_get_stat(void);


/* =================================================================================== */
/*                         scheduler Management Functions                              */
/* =================================================================================== */

/// Lock the scheduler.
/// \return previous lock state (1 - locked, 0 - not locked, error code if negative).
int32_t csi_kernel_sched_lock(void);

/// Unlock the scheduler.
/// \return previous lock state (1 - locked, 0 - not locked, error code if negative).
int32_t csi_kernel_sched_unlock(void);

/// Restore the scheduler lock state.
/// \param[in]     lock          lock state obtained by \ref csi_kernel_sched_lock or \ref csi_kernel_sched_unlock.
/// \return new lock state (1 - locked, 0 - not locked, error code if negative).
int32_t csi_kernel_sched_restore_lock(int32_t lock);

/// Suspend the scheduler.
/// \return time in ticks, for how long the system can sleep or power-down.
uint32_t csi_kernel_sched_suspend(void);

/// Resume the scheduler.
/// \param[in]     sleep_ticks   time in ticks for how long the system was in sleep or power-down mode.
void csi_kernel_sched_resume(uint32_t sleep_ticks);


/* =================================================================================== */
/*                             Task Management Functions                               */
/* =================================================================================== */

/// Create a task and add it to Active Tasks.
/// \param[in]     task          task function.
/// \param[in]     name          the name of task.
/// \param[in]     arg           pointer that is passed to the task function as start argument.
/// \param[in]     prio          task priority.
/// \param[in]     time_quanta   the amount of time (in clock ticks) for the time quanta when round robin is enabled,if Zero, then use FIFO sched
/// \param[in]     stack    stack base.
/// \param[in]     stack_size    stack size.
/// \param[in]     task_handle   reference to a task handle.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_new(k_task_entry_t task, const char *name, void *arg,
                      k_priority_t prio, uint32_t time_quanta,
                      void *stack, uint32_t stack_size, k_task_handle_t *task_handle);

/// Delete a task.
/// \param[in]     task_handle      task handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_del(k_task_handle_t task_handle);

/// Return the task handle of the current running task.
/// \return task handle for reference by other functions or NULL in case of error.
k_task_handle_t csi_kernel_task_get_cur(void);

/// Get current task state of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return current task state of the specified task.
k_task_stat_t csi_kernel_task_get_stat(k_task_handle_t task_handle);

/// Change priority of a task.
/// \param[in]     task_handle     task handle to operate.
/// \param[in]     priority      new priority value for the task function.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_set_prio(k_task_handle_t task_handle, k_priority_t priority);

/// Get current priority of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return current priority value of the specified task.negative indicates error code.
k_priority_t csi_kernel_task_get_prio(k_task_handle_t task_handle);

/// Get name of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return name of the task.
const char *csi_kernel_task_get_name(k_task_handle_t task_handle);

/// Suspend execution of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_suspend(k_task_handle_t task_handle);

/// Resume execution of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_resume(k_task_handle_t task_handle);

/// Terminate execution of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_terminate(k_task_handle_t task_handle);

/// Exit from the calling task.
/// \return none
void csi_kernel_task_exit(void);

/// Pass control to next task that is in state \b READY.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_task_yield(void);

/// Get number of active tasks.
/// \return number of active tasks.
uint32_t csi_kernel_task_get_count(void);

/// Get stack size of a task.
/// \param[in]     task_handle     task handle to operate.
/// \return stack size in bytes.
uint32_t csi_kernel_task_get_stack_size(k_task_handle_t task_handle);

/// Get available stack space of a thread based on stack watermark recording during execution.
/// \param[in]     task_handle     task handle to operate.
/// \return remaining stack space in bytes.
uint32_t csi_kernel_task_get_stack_space(k_task_handle_t task_handle);

/// Enumerate active tasks.
/// \param[out]    task_array    pointer to array for retrieving task handles.
/// \param[in]     array_items   maximum number of items in array for retrieving task handles.
/// \return number of enumerated tasks.
uint32_t csi_kernel_task_list(k_task_handle_t *task_array, uint32_t array_items);

/// System enter interrupt status.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_intrpt_enter(void);

/// System exit interrupt status.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_intrpt_exit(void);

/* =================================================================================== */
/*                                Generic time Functions                               */
/* =================================================================================== */

/// Waits for a time period specified in kernel ticks.
/// \param[in]     ticks        time ticks value
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_delay(uint32_t ticks);

/// Waits until an absolute time (specified in kernel ticks) is reached.
/// \param[in]     ticks         absolute time in ticks
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_delay_until(uint64_t ticks);

/// Convert kernel ticks to ms.
/// \param[in]     ticks     ticks which will be converted to ms
/// \return the ms of the ticks.
uint64_t csi_kernel_tick2ms(uint32_t ticks);

/// Convert ms to kernel ticks.
/// \param[in]     ms         ms which will be converted to ticks
/// \return the ticks of the ms.
uint64_t csi_kernel_ms2tick(uint32_t ms);

/// Waits for a time period specified in ms.
/// \param[in]     ms         time to be delayed in ms
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_delay_ms(uint32_t ms);

/// Get kernel ticks.
/// \return kernel ticks number
uint64_t csi_kernel_get_ticks(void);

/// Get the RTOS kernel tick frequency.
/// \return frequency of the kernel tick.
uint32_t csi_kernel_get_tick_freq(void);

/// Get the RTOS kernel system timer frequency.
/// \return frequency of the system timer.
uint32_t csi_kernel_get_systimer_freq(void);

/* =================================================================================== */
/*                              Timer Management Functions                             */
/* =================================================================================== */

/// Create and Initialize a timer.
/// \param[in]     func          start address of a timer call back function.
/// \param[in]     type          time type, \ref k_timer_type_t.
/// \param[in]     arg           argument to the timer call back function.
/// \return timer handle for reference by other functions or NULL in case of error.
k_timer_handle_t csi_kernel_timer_new(k_timer_cb_t func, k_timer_type_t type, void *arg);

/// Delete a timer.
/// \param[in]     timer_handle      timer handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_timer_del(k_timer_handle_t timer_handle);

/// Start or restart a timer.
/// \param[in]     timer_handle      timer handle to operate.
/// \param[in]     ticks         time out value in ticks
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_timer_start(k_timer_handle_t timer_handle, uint32_t ticks);

/// Stop a timer.
/// \param[in]     timer_handle      timer handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_timer_stop(k_timer_handle_t timer_handle);

/// Check if a timer is running.
/// \param[in]     timer_handle      timer handle to operate.
/// \return \ref k_timer_stat_t.
k_timer_stat_t csi_kernel_timer_get_stat(k_timer_handle_t timer_handle);


/* =================================================================================== */
/*                              Event Management Functions                             */
/* =================================================================================== */

/// Create and Initialize an Event Flags object.
/// \return event flags handle for reference by other functions or NULL in case of error.
k_event_handle_t csi_kernel_event_new(void);

/// Delete an Event Flags object.
/// \param[in]     ev_handle     event flags handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_event_del(k_event_handle_t ev_handle);

/// Set the specified Event Flags.
/// \param[in]     ev_handle     event flags handle to operate.
/// \param[in]     flags         specifies the flags that shall be set.
/// \param[out]     ret_flags     The value of the event after setting.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_event_set(k_event_handle_t ev_handle, uint32_t flags, uint32_t *ret_flags);

/// Clear the specified Event Flags.
/// \param[in]     ev_handle     event flags handle to operate.
/// \param[in]     flags         specifies the flags that shall be clear.
/// \param[out]     ret_flags     event flags before clearing.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_event_clear(k_event_handle_t ev_handle, uint32_t flags, uint32_t *ret_flags);

/// Get the current Event Flags. This function allows the user to know “Who did it!”
/// \param[in]     ev_handle     event flags handle to operate.
/// \param[out]     ret_flags     The value of the current event.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_event_get(k_event_handle_t ev_handle, uint32_t *ret_flags);

/// Wait for one or more Event Flags to become signaled.
/// \param[in]     ev_handle     event flags handle to operate.
/// \param[in]     flags         specifies the flags to wait for.
/// \param[in]     options       specifies flags options, \ref k_event_opt_t.
/// \param[in]     clr_on_exit   1 - event flags will be cleared before exit, otherwise event flags are not altered
/// \param[out]     actl_flags    The value of the event at the time either the bits being waited for became set, or the block time expired.
/// \param[in]     timeout       time out value in ticks if > 0, 0 in case of no time-out, negative in case of wait forever
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_event_wait(k_event_handle_t ev_handle, uint32_t flags,
                        k_event_opt_t options, uint8_t clr_on_exit,
                        uint32_t *actl_flags, int32_t timeout);


/* =================================================================================== */
/*                              Mutex Management Functions                             */
/* =================================================================================== */

/// Create and Initialize a Mutex object.
/// \return mutex handle for reference by other functions or NULL in case of error.
k_mutex_handle_t csi_kernel_mutex_new(void);

/// Delete a Mutex object.
/// \param[in]     mutex_handle      mutex handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_mutex_del(k_mutex_handle_t mutex_handle);

/// Acquire a Mutex or timeout if it is locked.
/// \param[in]     mutex_handle      mutex handle to operate.
/// \param[in]     timeout       time out value in ticks if > 0, 0 in case of no time-out, negative in case of wait forever
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_mutex_lock(k_mutex_handle_t mutex_handle, int32_t timeout);

/// Release a Mutex that was acquired by \ref csi_kernel_mutex_new.
/// \param[in]     mutex_handle      mutex handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_mutex_unlock(k_mutex_handle_t mutex_handle);

/// Get Thread which owns a Mutex object.
/// \param[in]     mutex_handle  mutex handle to operate.
/// \return task handle or NULL when mutex was not acquired.
k_task_handle_t csi_kernel_mutex_get_owner(k_mutex_handle_t mutex_handle);

/* =================================================================================== */
/*                            Semaphore Management Functions                           */
/* =================================================================================== */

/// Create and Initialize a Semaphore object.
/// \param[in]     max_count     maximum number of available tokens.
/// \param[in]     initial_count initial number of available tokens.
/// \return semaphore handle for reference by other functions or NULL in case of error.
k_sem_handle_t csi_kernel_sem_new(int32_t max_count, int32_t initial_count);

/// Delete a Semaphore object.
/// \param[in]     sem_handle  semaphore handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_sem_del(k_sem_handle_t sem_handle);

/// Acquire a Semaphore token or timeout if no tokens are available.
/// \param[in]     sem_handle  semaphore handle to operate.
/// \param[in]     timeout       time out value in ticks if > 0, 0 in case of no time-out, negative in case of wait forever
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_sem_wait(k_sem_handle_t sem_handle, int32_t timeout);

/// Release a Semaphore token that was acquired by \ref csi_kernel_sem_wait.
/// \param[in]     sem_handle  semaphore handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_sem_post(k_sem_handle_t sem_handle);

/// Get current Semaphore token count.
/// \param[in]     sem_handle  semaphore handle to operate.
/// \return number of tokens available. negative indicates error code.
int32_t csi_kernel_sem_get_count(k_sem_handle_t sem_handle);


/* =================================================================================== */
/*                          Memory Pool Management Functions                           */
/* =================================================================================== */

/// Create and Initialize a Memory Pool object.
/// \param[in]     p_addr        memory block base address.
/// \param[in]     block_count   maximum number of memory blocks in memory pool.
/// \param[in]     block_size    memory block size in bytes.
/// \return memory pool handle for reference by other functions or NULL in case of error.
k_mpool_handle_t csi_kernel_mpool_new(void *p_addr, int32_t block_count, int32_t block_size);

/// Delete a Memory Pool object.
/// \param[in]     mp_handle     memory pool handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_mpool_del(k_mpool_handle_t mp_handle);

/// Allocate a memory block from a Memory Pool.
/// \param[in]     mp_handle     memory pool handle to operate.
/// \param[in]     timeout       time out value in ticks if > 0, 0 in case of no time-out, negative in case of wait forever
/// \return address of the allocated memory block or NULL in case of no memory is available.
void *csi_kernel_mpool_alloc(k_mpool_handle_t mp_handle, int32_t timeout);

/// Return an allocated memory block back to a Memory Pool.
/// \param[in]     mp_handle     memory pool handle to operate.
/// \param[in]     block         address of the allocated memory block to be returned to the memory pool.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_mpool_free(k_mpool_handle_t mp_handle, void *block);

/// Get number of memory blocks used in a Memory Pool.
/// \param[in]     mp_handle     memory pool handle to operate.
/// \return number of memory blocks used. negative indicates error code.
int32_t csi_kernel_mpool_get_count(k_mpool_handle_t mp_handle);

/// Get maximum number of memory blocks in a Memory Pool.
/// \param[in]     mp_handle     memory pool handle to operate.
/// \return maximum number of memory blocks.
uint32_t csi_kernel_mpool_get_capacity(k_mpool_handle_t mp_handle);

/// Get memory block size in a Memory Pool.
/// \param[in]     mp_handle     memory pool handle to operate.
/// \return memory block size in bytes.
uint32_t csi_kernel_mpool_get_block_size(k_mpool_handle_t mp_handle);

/* =================================================================================== */
/*                          Message Queue Management Functions                         */
/* =================================================================================== */

/// Create and Initialize a Message Queue object.
/// \param[in]     msg_count     maximum number of messages in queue.
/// \param[in]     msg_size      maximum message size in bytes.
/// \return message queue handle for reference by other functions or NULL in case of error.
k_msgq_handle_t csi_kernel_msgq_new(int32_t msg_count, int32_t msg_size);

/// Delete a Message Queue object.
/// \param[in]     mq_handle         message queue handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_msgq_del(k_msgq_handle_t mq_handle);

/// Put a Message into a Queue or timeout if Queue is full.
/// \param[in]     mq_handle         message queue handle to operate.
/// \param[in]     msg_ptr       pointer to buffer with message to put into a queue.
/// \param[in]     front_or_back specify this msg to be put to front or back.   1 - front, 0 -back
/// \param[in]     timeout       time out value in ticks if > 0, 0 in case of no time-out, negative in case of wait forever
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_msgq_put(k_msgq_handle_t mq_handle, const void *msg_ptr, uint8_t front_or_back, int32_t timeout);

/// Get a Message from a Queue or timeout if Queue is empty.
/// \param[in]     mq_handle     message queue handle to operate.
/// \param[out]    msg_ptr       pointer to buffer for message to get from a queue.
/// \param[in]     timeout       time out value in ticks if > 0, 0 in case of no time-out, negative in case of wait forever
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_msgq_get(k_msgq_handle_t mq_handle, void *msg_ptr, int32_t timeout);

/// Get number of queued messages in a message queue.
/// \param[in]     mq_handle         message queue handle to operate.
/// \return number of queued messages.negative indicates error code.
int32_t csi_kernel_msgq_get_count(k_msgq_handle_t mq_handle);

/// Get maximum number of messages in a message queue.
/// \param[in]     mq_handle         message queue handle to operate.
/// \return maximum number of messages.
uint32_t csi_kernel_msgq_get_capacity(k_msgq_handle_t mq_handle);

/// Get maximum message size in a message queue.
/// \param[in]     mq_handle         message queue handle to operate.
/// \return maximum message size in bytes.
uint32_t csi_kernel_msgq_get_msg_size(k_msgq_handle_t mq_handle);

/// Reset a Message Queue to initial empty state.
/// \param[in]     mq_handle         message queue handle to operate.
/// \return execution status code. \ref k_status_t
k_status_t csi_kernel_msgq_flush(k_msgq_handle_t mq_handle);


/* =================================================================================== */
/*                          Heap Management Functions                                  */
/* =================================================================================== */

/// Allocates size bytes and returns a pointer to the allocated memory.
/// \param[in]     size     Allocates size bytes.
/// \param[in]     caller   the function who call this interface or NULL.
/// \return  a pointer to the allocated memory.
void *csi_kernel_malloc(int32_t size, void *caller);

/// Frees the memory space pointed to by ptr
/// \param[in]     ptr      a pointer to memory block, return by csi_kernel_malloc or csi_kernel_realloc.
/// \param[in]     caller   the function who call this interface or NULL.
/// \return void
void csi_kernel_free(void *ptr, void *caller);

/// Changes the size of the memory block pointed to by ptr to size bytes
/// \param[in]     ptr      a pointer to memory block, return by csi_kernel_malloc or csi_kernel_realloc.
/// \param[in]     size     Allocates size bytes.
/// \param[in]     caller   the function who call this interface or NULL.
/// \return  a pointer to the allocated memory.
void *csi_kernel_realloc(void *ptr, int32_t size, void *caller);

/// Get csi memory used info.
/// \param[out]     total    the total memory can be use.
/// \param[out]     used     the used memory by malloc.
/// \param[out]     free     the free memory can be use.
/// \param[out]     peak     the peak memory used.
/// \return execution status code. \ref k_status_t.
k_status_t csi_kernel_get_mminfo(int32_t *total, int32_t *used, int32_t *free, int32_t *peak);

/// Dump csi memory .
/// \param void
/// \return execution status code. \ref k_status_t.
k_status_t csi_kernel_mm_dump(void);

#ifdef  __cplusplus
}
#endif

#endif  // _CSI_KERNEL_
