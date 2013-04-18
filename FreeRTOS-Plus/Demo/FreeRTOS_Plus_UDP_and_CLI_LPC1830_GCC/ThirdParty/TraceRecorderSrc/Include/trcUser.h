/*******************************************************************************
 * FreeRTOS+Trace v2.3.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcUser.h
 * The public API of the trace recorder library.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcPort.c and trcPort.h
 * given that these modification are clearly marked as your own modifications
 * and documented in the initial comment section of these source files. 
 * This software is the intellectual property of Percepio AB and may not be 
 * sold or in other ways commercially redistributed without explicit written 
 * permission by Percepio AB.
 *
 * Disclaimer 
 * The trace tool and recorder library is being delivered to you AS IS and 
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does 
 * not and cannot warrant the performance or results you may obtain by using the 
 * software or documentation. Percepio AB make no warranties, express or 
 * implied, as to noninfringement of third party rights, merchantability, or 
 * fitness for any particular purpose. In no event will Percepio AB, its 
 * technology partners, or distributors be liable to you for any consequential, 
 * incidental or special damages, including any lost profits or lost savings, 
 * even if a representative of Percepio AB has been advised of the possibility 
 * of such damages, or for any claim by any third party. Some jurisdictions do 
 * not allow the exclusion or limitation of incidental, consequential or special 
 * damages, or the exclusion of implied warranties or limitations on how long an 
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * FreeRTOS+Trace is available as Free Edition and in two premium editions.
 * You may use the premium features during 30 days for evaluation.
 * Download FreeRTOS+Trace at http://www.percepio.com/products/downloads/
 *
 * Copyright Percepio AB, 2012.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRCUSER_H
#define TRCUSER_H

#include "FreeRTOS.h"

#include "trcKernel.h"

#if (configUSE_TRACE_FACILITY == 1)

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * uiTraceStart
 *
 * Starts the recorder. The recorder will not be started if an error has been
 * indicated using vTraceError, e.g. if any of the Nx constants in trcConfig.h 
 * has a too small value (NTASK, NQUEUE, etc).
 * 
 * Returns 1 if the recorder was started successfully.
 * Returns 0 if the recorder start was prevented due to a previous internal 
 * error. In that case, check vTraceGetLastError to get the error message.
 * Any error message is also presented when opening a trace file in 
 * FreeRTOS+Trace v2.2.2 or later.
 ******************************************************************************/
uint32_t uiTraceStart(void);

/*******************************************************************************
 * vTraceStart 
 *
 * Starts the recorder. The recorder will not be started if an error has been
 * indicated using vTraceError, e.g. if any of the Nx constants in trcConfig.h 
 * has a too small value (NTASK, NQUEUE, etc).
 * 
 * This function is obsolete, but has been saved for backwards compatibility. 
 * We recommend using uiTraceStart instead.
 ******************************************************************************/
void vTraceStart(void);

/*******************************************************************************
 * vTraceStartStatusMonitor
 *
 * This starts a task to monitor the status of the recorder module. 
 * This task periodically prints a line to the console window, which shows the 
 * recorder status, the number of events recorded and the latest timestamp. 
 * This task calls vTracePortEnd (trcPort.c) when it detects that the recorder 
 * has been stopped. This allows for adding custom actions, e.g., to store the
 * trace to a file in case a file system is available on the device.
 ******************************************************************************/
void vTraceStartStatusMonitor(void);

/*******************************************************************************
 * vTraceStop
 *
 * Stops the recorder. The recording can be resumed by calling vTraceStart.
 * This does not reset the recorder. Use vTraceClear is that is desired.
 ******************************************************************************/
void vTraceStop(void);

/*******************************************************************************
 * vTraceClear
 *
 * Resets the recorder. Only necessary if a restart is desired - this is not 
 * needed in the startup initialization.
 ******************************************************************************/
void vTraceClear(void);

/*******************************************************************************
 * vTraceSetQueueName
 *
 * Assigns a name to a FreeRTOS Queue, Semaphore or Mutex. This function should
 * be called right after creation of the queue/mutex/semaphore. If not using 
 * this function, the queues/mutexes/semaphores will be presented by their
 * numeric handle only.
 *
 * Example:
 *     actuatorQ = xQueueCreate(3, sizeof(QueueMessage));
 *     vTraceSetQueueName(actuatorQ, "ActuatorQueue");
 ******************************************************************************/
void vTraceSetQueueName(void* queue, const char* name);

#if (INCLUDE_ISR_TRACING == 1)

/*******************************************************************************
 * vTraceSetISRProperties
 * 
 * Registers an Interrupt Service Routine in the recorder library, This must be
 * called before using vTraceStoreISRBegin to store ISR events. This is 
 * typically called in the startup of the system, before the scheduler is 
 * started.
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         portENTER_CRITICAL(); // Required if nested ISRs are allowed
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         portEXIT_CRITICAL();
 *         ...
 *         portENTER_CRITICAL(); // Required if nested ISRs are allowed
 *         vTraceStoreISREnd();
 *         portEXIT_CRITICAL();
 *     }
 ******************************************************************************/
void vTraceSetISRProperties(objectHandleType handle, const char* name, char priority);

/*******************************************************************************
 * vTraceStoreISRBegin
 * 
 * Registers the beginning of an Interrupt Service Routine.
 *
 * Note! This may only be used for interrupts affected by portENTER_CRITICAL.
 * In some FreeRTOS ports, such as ARM Cortex M3, this does not disable all
 * interrupts. Interrupts above configMAX_SYSCALL_INTERRUPT_PRIORITY are still 
 * enabled, but may not call the FreeRTOS API. Such may not call the recorder 
 * API, including this function.
 *
 * See http://www.freertos.org/a00110.html
 * 
 * If allowing nested ISRs, this must be called with interrupts disabled. 
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         portENTER_CRITICAL(); // Required if nested ISRs are allowed
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         portEXIT_CRITICAL();
 *         ...
 *         portENTER_CRITICAL(); // Required if nested ISRs are allowed
 *         vTraceStoreISREnd();
 *         portEXIT_CRITICAL();
 *     }
 ******************************************************************************/
void vTraceStoreISRBegin(objectHandleType id);

/*******************************************************************************
 * vTraceStoreISREnd
 * 
 * Registers the end of an Interrupt Service Routine.
 *
 * Note! This may only be used for interrupts affected by portENTER_CRITICAL.
 * In some FreeRTOS ports, such as ARM Cortex M3, this does not disable all
 * interrupts. Interrupts above configMAX_SYSCALL_INTERRUPT_PRIORITY are still 
 * enabled, but may not call the FreeRTOS API. Such may not call the recorder 
 * API, including this function.
 *
 * See http://www.freertos.org/a00110.html
 * 
 * If allowing nested ISRs, this must be called with interrupts disabled. 
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         portENTER_CRITICAL(); // Required if nested ISRs are allowed
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         portEXIT_CRITICAL();
 *         ...
 *         portENTER_CRITICAL(); // Required if nested ISRs are allowed
 *         vTraceStoreISREnd();
 *         portEXIT_CRITICAL();
 *     }
 ******************************************************************************/
void vTraceStoreISREnd(void);

#else
   /* If not including the ISR recording */

void vTraceIncreaseISRActive(void);

void vTraceDecreaseISRActive(void);

#define vTraceSetISRProperties(handle, name, priority)
#define vTraceStoreISRBegin(id) vTraceIncreaseISRActive()
#define vTraceStoreISREnd() vTraceDecreaseISRActive()

#endif

/*******************************************************************************
 * vvTraceTaskSkipDefaultInstanceFinishedEvents
 *
 * This is useful if there are implicit Instance Finish Events, such as 
 * vTaskDelayUntil or xQueueReceive, in a task where an explicit Instance Finish 
 * Event has been defined. This function tells the recorder that only the 
 * explicitly defined functions (using vTraceTaskInstanceIsFinished) should be
 * treated as Instance Finish Events for this task. The implicit Instance Finish 
 * Events are thus disregarded for this task.
 ******************************************************************************/
void vTraceTaskSkipDefaultInstanceFinishedEvents(void);

/*******************************************************************************
 * vTraceTaskInstanceIsFinished
 * 
 * This defines an explicit Instance Finish Event for the current task. It tells 
 * the recorder that the current instance of this task is finished at the next 
 * kernel call of the task, e.g., a taskDelay or a queue receive. This function 
 * should be called right before the api function call considered to be the end 
 * of the task instamce, i.e., the Instance Finish Event.
 ******************************************************************************/
void vTraceTaskInstanceIsFinished(void);

/*******************************************************************************
 * vTraceGetTraceBuffer
 * 
 * Returns a pointer to the recorder data structure. Use this together with 
 * uiTraceGetTraceBufferSize if you wish to implement an own store/upload 
 * solution, e.g., in case a debugger connection is not available for uploading 
 * the data.
 ******************************************************************************/
void* vTraceGetTraceBuffer(void);

/*******************************************************************************
 * uiTraceGetTraceBufferSize
 * 
 * Gets the size of the recorder data structure. For use together with 
 * vTraceGetTraceBuffer if you wish to implement an own store/upload solution, 
 * e.g., in case a debugger connection is not available for uploading the data.
 ******************************************************************************/
uint32_t uiTraceGetTraceBufferSize(void);

#if (INCLUDE_USER_EVENTS == 1)

/*******************************************************************************
 * xTraceOpenLabel
 * 
 * Creates user event labels for user event channels or for individual events.
 * User events can be used to log application events and data for display in
 * the visualization tool. A user event is identified by a label, i.e., a string,
 * which is stored in the recorder's symbol table.
 * When logging a user event, a numeric handle (reference) to this string is
 * used to identify the event. This is obtained by calling 
 * 
 *     xTraceOpenLabel()
 *
 * whihc adds the string to the symbol table (if not already present)
 * and returns the corresponding handle.
 *
 * This can be used in two ways:
 *
 * 1. The handle is looked up every time, when storing the user event.
 *
 * Example:
 *     vTraceUserEvent(xTraceOpenLabel("MyUserEvent"));
 *
 * 2. The label is registered just once, with the handle stored in an
 *  application variable - much like using a file handle.
 *
 * Example:
 *     myEventHandle = xTraceOpenLabel("MyUserEvent");
 *     ...
 *     vTraceUserEvent(myEventHandle);
 *
 * The second option is faster since no lookup is required on each event, and 
 * therefore recommended for user events that are frequently
 * executed and/or located in time-critical code. The lookup operation is
 * however fairly fast due to the design of the symbol table.
 ******************************************************************************/
traceLabel xTraceOpenLabel(const char* label);

 /******************************************************************************
 * vTraceUserEvent
 *
 * Basic user event (Standard and Professional Edition only)
 * 
 * Generates a User Event with a text label. The label is created/looked up
 * in the symbol table using xTraceOpenLabel.
 ******************************************************************************/
void vTraceUserEvent(traceLabel eventLabel);

 /******************************************************************************
 * vTracePrintF 
 * 
 * Advanced user events (Professional Edition only)
 *
 * Generates User Event with formatted text and data, similar to a "printf".
 * It is very fast compared to a normal "printf" since this function only 
 * stores the arguments. The actual formatting is done
 * on the host PC when the trace is displayed in the viewer tool. 
 *
 * User Event labels are created using xTraceOpenLabel.
 * Example:
 *
 *     traceLabel adc_uechannel = xTraceOpenLabel("ADC User Events");
 *     ...
 *     vTracePrint(adc_uechannel, 
 *                 "ADC channel %d: %lf volts", 
 *                 ch, (double)adc_reading/(double)scale);
 *
 * This can be combined into one line, if desired, but this is slower:
 *
 *     vTracePrint(xTraceOpenLabel("ADC User Events"), 
 *                 "ADC channel %d: %lf volts", 
 *                 ch, (double)adc_reading/(double)scale);
 *
 * Calling xTraceOpenLabel multiple times will not create duplicate entries, but
 * it is of course faster to just do it once, and then keep the handle for later 
 * use. If you don´t have any data arguments, only a text label/string, it is 
 * better to use vTraceUserEvent - it is faster.
 *
 * Format specifiers supported:
 *  %d - 32 bit signed integer
 *  %u - 32 bit unsigned integer
 *  %f - 32 bit float
 *  %s - string (is copied to the recorder symbol table)
 *  %hd - 16 bit signed integer
 *  %hu - 16 bit unsigned integer
 *  %bd - 8 bit signed integer
 *  %bu - 8 bit unsigned integer
 *  %lf - double-precision float (Note! See below...)
 * 
 * Up to 15 data arguments are allowed, with a total size of maximum 32 byte.
 * In case this is exceeded, the user event is changed into an error message.
 * 
 * The data is stored in trace buffer, and is packed to allow storing multiple 
 * smaller data entries in the same 4-byte record, e.g., four 8-bit values.
 * A string requires two bytes, as the symbol table is limited to 64K. Storing 
 * a double (%lf) uses two records, so this is quite costly. Use float (%f) 
 * unless the higher precision is really necessary.
 * 
 * Note that the double-precision float (%lf) assumes a 64 bit double 
 * representation. This does not seem to be the case on e.g. PIC24F. 
 * Before using a %lf argument on a 16-bit MCU, please verify that 
 * "sizeof(double)" actually gives 8 as expected. If not, use %f instead.
 ******************************************************************************/ 
void vTracePrintF(traceLabel eventLabel, const char* formatStr, ...);

#else

#define vTracePrintF(eventLabel, formatStr, ...);
#define xTraceOpenLabel(label) 0
#define vTraceUserEvent(eventLabel) 

#endif

/******************************************************************************
 * vTraceExclude______FromTrace
 *
 * Excludes a task or object from the trace.
 * This can be useful if some irrelevant task is very frequent and is "eating
 * up the buffer". This should be called after the task has been created, but 
 * before starting the FreeRTOS scheduler.
 *****************************************************************************/
void vTraceExcludeQueueFromTrace(void* handle);
void vTraceExcludeSemaphoreFromTrace(void* handle);
void vTraceExcludeMutexFromTrace(void* handle);
void vTraceExcludeTaskFromTrace(void* handle);
void vTraceExcludeKernelServiceFromTrace(traceKernelService kernelService);

/******************************************************************************
 * vTraceInclude______InTrace
 *
 * Includes a task, object or kernel service in the trace. This is only
 * necessary if the task or object has been previously exluded.
 *****************************************************************************/
void vTraceIncludeQueueInTrace(void* handle);
void vTraceIncludeSemaphoreInTrace(void* handle);
void vTraceIncludeMutexInTrace(void* handle);
void vTraceIncludeTaskInTrace(void* handle);
void vTraceIncludeKernelServiceInTrace(traceKernelService kernelService);

#ifdef __cplusplus
}
#endif

#else

#include "trcPort.h"

#define vTraceInit()
#define uiTraceStart() (1)
#define vTraceStart()
#define vTraceStop()
#define vTraceClear()
#define vTraceStartStatusMonitor()
#define vTracePortSetOutFile(f)
#define vTraceGetTraceBuffer() ((void*)0)
#define uiTraceGetTraceBufferSize() 0
#define xTraceOpenLabel(label) 0
#define vTraceUserEvent(eventLabel)
#define vTracePrintF(eventLabel,formatStr,...)
#define vTraceExcludeTaskFromSchedulingTrace(name)
#define vTraceSetQueueName(queue, name)

#define vTraceTaskSkipDefaultInstanceFinishedEvents()
#define vTraceSetISRProperties(handle, name, priority)
#define vTraceStoreISRBegin(id)
#define vTraceStoreISREnd()
#endif
#endif

