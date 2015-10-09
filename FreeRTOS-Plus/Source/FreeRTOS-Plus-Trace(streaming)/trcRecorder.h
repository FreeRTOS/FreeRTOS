/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcRecorder.c
 *
 * Public interface and configurations for the trace recorder library.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
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
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/

#ifndef _TRC_RECORDER_H
#define _TRC_RECORDER_H

#ifdef __cplusplus
extern “C” {
#endif

#include "trcConfig.h"
#include "trcKernelPort.h"
#include "trcHardwarePort.h"

#if (USE_TRACEALYZER_RECORDER == 1)

/*** User API *****************************************************************/

/******************************************************************************
 * vTracePrint
 *
 * Generates "User Events", with unformatted text.
 *
 * User Events can be used for very efficient application logging, and are shown
 * as yellow labels in the main trace view.
 *
 * You may group User Events into User Event Channels. The yellow User Event 
 * labels shows the logged string, preceeded by the channel  name within 
 * brackets. For example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using vTraceStoreUserEventChannelName().
 *
 * Example:
 *
 *	 char* error_uechannel = vTraceStoreUserEventChannelName("Errors");
 *	 ...
 *	 vTracePrint(error_uechannel, "Shouldn't reach this code!");
 *
 ******************************************************************************/
void vTracePrint(const char* chn, const char* str);

/******************************************************************************
 * vTracePrintF
 *
 * Generates "User Events", with formatted text and data, similar to a "printf".
 * It is very fast since the actual formatting is done on the host side when the
 * trace is displayed.
 *
 * User Events can be used for very efficient application logging, and are shown
 * as yellow labels in the main trace view.
 * An advantage of User Events is that data can be plotted in the "User Event
 * Signal Plot" view, visualizing any data you log as User Events, discrete
 * states or control system signals (e.g. system inputs or outputs).
 *
 * You may group User Events into User Event Channels. The yellow User Event 
 * labels show the logged string, preceeded by the channel name within brackets.
 * 
 * Example:
 *
 *  "[MyChannel] Hello World!"
 *
 * The User Event Channels are shown in the View Filter, which makes it easy to
 * select what User Events you wish to display. User Event Channels are created
 * using vTraceStoreUserEventChannelName().
 *
 * Example:
 *
 *	 char* adc_uechannel = vTraceStoreUserEventChannelName("ADC User Events");
 *	 ...
 *	 vTracePrint(adc_uechannel,
 *				 "ADC channel %d: %lf volts",
 *				 ch, (double)adc_reading/(double)scale);
 *
 * All data arguments are assumed to be 32 bt wide. The following formats are
 * supported in v2.8:
 * %d - signed integer
 * %u - unsigned integer
 * %X - hexadecimal (uppercase)
 * %x - hexadecimal (lowercase)
 * %s - string (currently, this must be an earlier stored symbol name)
 *
 * Up to 15 data arguments are allowed, with a total size of maximum 60 byte
 * including 8 byte for the base event fields and the format string. So with
 * one data argument, the maximum string length is 48 chars. If this is exceeded
 * the string is truncated (4 bytes at a time).
 *
 ******************************************************************************/
void vTracePrintF(const char* chn, const char* fmt, ...);

/*******************************************************************************
 * vTraceStoreUserEventChannelName(const char* name)
 *
 * Parameter name: the channel name to store (const string literal)
 *
 * Stores a name for a user event channel, returns the handle (just a pointer
 * to the provided string). Typically assigned to a "channel" variable that
 * keeps it for later calls to vTracePrintF();
 ******************************************************************************/
char* vTraceStoreUserEventChannelName(const char* name);

/*******************************************************************************
 * vTraceStoreKernelObjectName(void* object, const char* name)
 *
 * Parameter object: pointer to the kernel object that shall be named
 * Parameter name: the name to store (const string literal)
 *
 * Stores a name for kernel objects (Semaphore, Mailbox, etc.).
 ******************************************************************************/
void vTraceStoreKernelObjectName(void* object, const char* name);

/*******************************************************************************
 * vTraceSetISRProperties(const char* name, char priority)
 *
 * Parameter name: the name to give the the ISR, also serves as handle.
 * Parameter priority: the priority level of the ISR.
 *
 * Stores a name and priority level for an Interrupt Service Routine, to allow
 * for better visualization. The string address is used as a unique handle.
 *
 * Example:
 *
 *	 vTraceSetISRProperties("ISRTimer1", ISRPriorityTimer1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 ******************************************************************************/
void vTraceSetISRProperties(const char* name, char priority);

/*******************************************************************************
 * vTraceStoreISRBegin(void* handle);
 *
 * Parameter handle: ID of the ISR, which is "name" in vTraceSetISRProperties
 *
 * Registers the beginning of an Interrupt Service Routine (ISR), i.e., or an
 * exception handler.
 *
 * Example:
 *
 *	 vTraceSetISRProperties("ISRTimer1", ISRPriorityTimer1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREnd(0);
 *	 }
 ******************************************************************************/
void vTraceStoreISRBegin(void* handle);

/*******************************************************************************
 * vTraceStoreISREnd
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * This function attempts to automatically detect if a task switch will take
 * place when interrupt ends. If this is possible depends on the kernel port.
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREnd();
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISREnd(void);

/*******************************************************************************
 * vTraceStoreISREndManual
 *
 * Registers the end of an Interrupt Service Routine.
 *
 * The parameter isTaskSwitchRequired indicates if the interrupt has requested a
 * task-switch (= 1) or if the interrupt returns to the earlier context (= 0)
 *
 * Example:
 *	 #define PRIO_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	 ...
 *	 vTraceSetISRProperties("ISRTimer1", PRIO_ISR_TIMER1);
 *	 ...
 *	 void ISR_handler()
 *	 {
 *		 vTraceStoreISRBegin("ISRTimer1");
 *		 ...
 *		 vTraceStoreISREndManual(0);
 *	 }
 *
 ******************************************************************************/
void vTraceStoreISREndManual(int isTaskSwitchRequired);

/*******************************************************************************
 * vTraceInstanceFinishNow
 *
 * Creates an event that ends the current task instance at this very instant.
 * This makes the viewer to splits the current fragment at this point and begin
 * a new actor instance, even if no task-switch has occurred.
 *****************************************************************************/
void vTraceInstanceFinishedNow(void);

/*******************************************************************************
 * vTraceInstanceFinishedNext
 *
 * Marks the current "task instance" as finished on the next kernel call.
 *
 * If that kernel call is blocking, the instance ends after the blocking event
 * and the corresponding return event is then the start of the next instance.
 * If the kernel call is not blocking, the viewer instead splits the current
 * fragment right before the kernel call, which makes this call the first event
 * of the next instance.
 *****************************************************************************/
void vTraceInstanceFinishedNext(void);


/******************************************************************************/
/*** INTERNAL FUNCTIONS *******************************************************/
/******************************************************************************/

/* Saves a symbol name (task name etc.) in symbol table */
void vTraceSaveSymbol(void *address, const char *name);

/* Deletes a symbol name (task name etc.) from symbol table */
void vTraceDeleteSymbol(void *address);

/* Saves an object data entry (task base priority) in object data table */
void vTraceSaveObjectData(void *address, uint32_t data);

/* Removes an object data entry (task base priority) from object data table */
void vTraceDeleteObjectData(void *address);

/* Store an event with zero parameters (event ID only) */
void vTraceStoreEvent0(uint16_t eventID);

/* Store an event with one 32-bit parameter (pointer address or an int) */
void vTraceStoreEvent1(uint16_t eventID, uint32_t param1);

/* Store an event with two 32-bit parameters */
void vTraceStoreEvent2(uint16_t eventID, uint32_t param1, uint32_t param2);

/* Store an event with three 32-bit parameters */
void vTraceStoreEvent3(	uint16_t eventID,
						uint32_t param1,
						uint32_t param2,
						uint32_t param3);

/* Stores an event with <nParam> 32-bit integer parameters */
void vTraceStoreEvent(int nParam, uint16_t EventID, ...);

/* Stories an event with a string and <nParam> 32-bit integer parameters */
void vTraceStoreStringEvent(int nArgs, uint16_t eventID, const char* str, ...);

/* The data structure for commands (a bit overkill) */
typedef struct
{
  unsigned char cmdCode;
  unsigned char param1;
  unsigned char param2;
  unsigned char param3;
  unsigned char param4;
  unsigned char param5;
  unsigned char checksumLSB;
  unsigned char checksumMSB;
} TracealyzerCommandType;

/* Checks if the provided command is a valid command */
int isValidCommand(TracealyzerCommandType* cmd);

/* Executed the received command (Start or Stop) */
void processCommand(TracealyzerCommandType* cmd);

/* Backwards compatibility macros with old recorder */
#define vTraceInitTraceData() Trace_Init()
#define uiTraceStart() (1)
#define vTraceStart()
#define vTraceStop()

#else /*(USE_TRACEALYZER_RECORDER == 1)*/

#define vTraceStoreEvent0(e)
#define vTraceStoreEvent1(e, param1)
#define vTraceStoreEvent2(e, param1, param2)
#define vTraceStoreEvent3(e, param1, param2, param3)
#define vTraceStoreUserEventChannelName(x) 0
#define vTracePrint(chn, ...) 
#define vTracePrintF(chn, ...) 
#define vTraceInstanceFinishedNow()
#define vTraceInstanceFinishedNext()
#define vTraceStoreISRBegin(x)
#define vTraceStoreISREnd()
#define vTraceStoreISREndManual(x)
#define vTraceSetISRProperties(a, b) 
#define vTraceStoreKernelObjectName(a, b) 

/* Backwards compatibility macros with old recorder */
#define vTraceInitTraceData()	
#define uiTraceStart() (1)
#define vTraceStart()
#define vTraceStop()

#endif /*(USE_TRACEALYZER_RECORDER == 1)*/

extern void psfError(int errCode);

#define PSF_ASSERT(_assert, _err) if (! (_assert)){ psfError(_err); return; }

#define PSF_ERROR_NONE 0
#define PSF_ERROR_EVENT_CODE_TOO_LARGE 1
#define PSF_ERROR_ISR_NESTING_OVERFLOW 2

#ifdef __cplusplus
}
#endif

#endif /* _TRC_RECORDER_H */
