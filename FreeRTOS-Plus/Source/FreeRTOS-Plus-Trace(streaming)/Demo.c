/*******************************************************************************
 * Tracealyzer v3.0.0 Demo Application
 * Percepio AB, www.percepio.com
 *
 * traceDemoApp.c
 *
 * Demo application for Tracealyzer demo project.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcHardwarePort.c/.h
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
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2014.
 * www.percepio.com
 ******************************************************************************/


/* Standard includes. */
#include <stdio.h>
#include <stdint.h>

/* Kernel includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"
#include "semphr.h"

#if (configUSE_TIMERS == 1)
	#include "timers.h"
#endif

#include "trcRecorder.h"

#define ISR3_PERIOD 18
#define ISR2_PERIOD 24
#define ISR1_PERIOD 30

#define EXECTIME_CONTROLLER 1
#define EXECTIME_SUPERV 2
#define EXECTIME_SENSOR 1

typedef struct
{
	int32_t code;
	int32_t value;
	char data[512]; // Makes the Memory Heap Utilization graph more interresting!
} QueueMessage;

#define MSGCODE_SENSOR_VALUE 1
#define MSGCODE_CONTROL_VALUE 10
#define MSGCODE_CONTROL_DEFAULT_VALUE 99

static portTASK_FUNCTION_PROTO( trcDemoTaskSensor, pvParameters );
static portTASK_FUNCTION_PROTO( trcDemoTaskActuator, pvParameters );
static portTASK_FUNCTION_PROTO( trcDemoTaskController, pvParameters );
static portTASK_FUNCTION( trcDemoTaskSuperv, pvParameters );
static portTASK_FUNCTION( trcDemoISR, pvParameters );

#if (configUSE_TIMERS == 1)
xTimerHandle timer;
void myTimerHandler(xTimerHandle tmr);
#endif

xQueueHandle sensorQ, actuatorQ;
xSemaphoreHandle Sem1, Sem2, Sem3;

void doSomeWork(uint32_t n);

int readSensor(int i);

/******************************************************************************
* doSomeWork
*
* Performs a busy wait for X milliseconds. Used to generate suitable execution
* times in the demo application, in a portable way.
******************************************************************************/
void doSomeWork(uint32_t ms)
{
	portTickType old = xTaskGetTickCount();
	portTickType new = 0;
	while (ms > 0)
	{
		new = xTaskGetTickCount();
		if (old < new)
		{
			/* If uiTraceTickCount has changed, we only reduce 1ms of the wait
				time. This way we do not count time that this task has waited
				for other tasks. This will result in somewhat correct execution
				times. */
			old = new;
			ms--;
		}
	}
}

/******************************************************************************
* readSensor
*
* Simulates a set of sensors/inputs, using a simple physics simulation.
* The values are intentionally ints (rather than floats) to avoid very slow
* execution times on chips without hardware floating point support.
******************************************************************************/
int readSensor(int i)
{
	static int pos[3] = {40, 80, 120};
	static int speed[3] = {0, 0, -3};
	static int acc[3] = {0, 0, 0};

	i--;

	acc[i] = (-pos[i] >> 3);
	speed[i] += acc[i];
	pos[i] += speed[i];

	return (int)pos[i];
}

/******************************************************************************
* trcDemoTaskSensor
*
* The "Sensor" tasks (three instances of this code). Reads data using
* "readSensor" when trigged by the timer interrupt through a semaphore.
******************************************************************************/
static portTASK_FUNCTION( trcDemoTaskSensor, pvParameters )
{
	char name[30] = "SensorX\0";
	QueueMessage sensorReading;
	unsigned char idx = (unsigned char)(*(int*)pvParameters);
	xSemaphoreHandle mySem = NULL;

	/* Change 'X' to the index */
	name[6] = '0' + idx;

	switch (idx)
	{
		case 1: mySem = Sem1; break;
		case 2: mySem = Sem2; break;
		case 3: mySem = Sem3; break;
	}

	vTraceStoreUserEventChannelName(name);

	/* Initialize xNextWakeTime - this only needs to be done once. */

	sensorReading.value = 0;
	sensorReading.code = 0;

	for( ;; )
	{

		xSemaphoreTake(mySem, 0xFFFFFFFF);

		sensorReading.code = idx;
		sensorReading.value = readSensor(idx);

		doSomeWork(EXECTIME_SENSOR);

		vTracePrintF(name , "Sending msg %d", sensorReading.value);

		if (xQueueSend(sensorQ, &sensorReading, 1) != pdTRUE)
		{
			vTracePrint(name, "Sensor queue full. Sample dropped!");
		}
		vTraceInstanceFinishedNow();
	}
}



/******************************************************************************
* trcDemoTaskSuperv
*
* The "Supervisor" task. Performs no action in the simulation, apart from
* preempting other tasks in the scheduling.
******************************************************************************/
static portTASK_FUNCTION( trcDemoTaskSuperv, pvParameters )
{
	int counter = 0;
	
	#if (configUSE_TIMERS == 1)
	static int timerState = 0;
	#endif

	portTickType xNextWakeTime;
	(void)pvParameters;

	xNextWakeTime = xTaskGetTickCount();

	#if (configUSE_TIMERS == 1)
	timer = xTimerCreate("Tmr5", 5, 1, (void*)42, myTimerHandler);
	xTimerChangePeriod(timer, 10, 0);
	#endif

	for( ;; )
	{		
		vTaskDelayUntil( &xNextWakeTime, 40);
		
		counter = (counter + 1) % 16;
		
		if (counter == 8) vTaskPrioritySet(NULL, 2);
		
		if (counter == 0) vTaskPrioritySet(NULL, 3);
				
		doSomeWork(EXECTIME_SUPERV);

		#if (configUSE_TIMERS == 1)
		if (timerState == 0)
		{
			xTimerStart(timer, 0);
			timerState = 1;
		}
		else if (timerState == 1)
		{
			xTimerStop(timer, 0);
			timerState = 0;
		}
		#endif
	}
}

/******************************************************************************
* trcDemoTaskController
*
* The "Controller" task. Periodically reads all accumulated messages in SensorQ
* (i.e., those produced by the Sensor tasks since the last execution of
* the Controller task). Calculates their mean value and send this to Actuator.
******************************************************************************/
static portTASK_FUNCTION( trcDemoTaskController, pvParameters )
{
	portTickType xNextWakeTime;
	QueueMessage* sensorReading;
	QueueMessage actuatorMessage;
	int32_t sum[4];
	int32_t count[4];

	(void)pvParameters;

	vTraceStoreUserEventChannelName("UE TEST");

	/* Initialize xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();
	for(;;)
	{
		sum[1] = 0;
		sum[2] = 0;
		sum[3] = 0;
		count[1] = 0;
		count[2] = 0;
		count[3] = 0;

		vTaskDelayUntil(&xNextWakeTime, 60);

		for(;;)
		{
			// To demostrate malloc/free tracing
			sensorReading = ( QueueMessage * ) pvPortMalloc( sizeof( QueueMessage ) );

			if (xQueueReceive(sensorQ, sensorReading, 0) != pdTRUE)
			{
				vPortFree(sensorReading);
				break;
			}
			else
			{
				if (sensorReading->code >= 1 && sensorReading->code <= 3)
				{
					sum[sensorReading->code] += sensorReading->value;
					count[sensorReading->code]++;
				}
			}
			doSomeWork(EXECTIME_CONTROLLER);
			
			//vTracePrintF(0, "0x%4x", 111);
			//vTracePrintF(0, "0x%04x", 111);
			//vTracePrintF(0, "0x%4X", 111);
			//vTracePrintF(0, "0x%04X", 111);
			//
			//vTracePrint(0, "123456789012345678901234567890123456789012345678901234567890");
			//vTracePrint("UE TEST", "1234567890123456789012345678901234567890123456789012345");
			//vTracePrint("UE TEST", "12345678901234567890123456789012345678901234567890123456");
			//vTracePrint("UE TEST", "123456789012345678901234567890123456789012345678901234567");
			//vTracePrint("UE TEST", "12345678901234567890123456789012345678901234567890");
			//
			//vTracePrintF("UE TEST", "%5d", 42);
			//vTracePrintF("UE TEST", "%05d", 42);
			//vTracePrintF("UE TEST", "%5d", -42);
			//vTracePrintF("UE TEST", "%05d", -42);
			//vTracePrintF("UE TEST", "%05d", -1042);
			//vTracePrintF("UE TEST", "%05d", -11042);
			//
			//vTracePrintF("UE TEST", "%5u", -1);
			//vTracePrintF("UE TEST", "%05u", -1);
			//vTracePrintF("UE TEST", "%5u", 10);
			//vTracePrintF("UE TEST", "%05u", 10);
			//
			//vTracePrintF("UE TEST", "%5u", 11042);
			//vTracePrintF("UE TEST", "%05u", 11042);
			//
			//vTracePrintF("UE TEST", "%5u", 111042);
			//vTracePrintF("UE TEST", "%05u", 111042);
			//
			//vTracePrintF("UE TEST", "%15d", 111042);
			//vTracePrintF("UE TEST", "%015d", 111042);

			vPortFree(sensorReading);
			vTraceInstanceFinishedNow();

		}

		actuatorMessage.code = MSGCODE_CONTROL_VALUE;
		actuatorMessage.value = 0;

		if (count[1] > 0)
			actuatorMessage.value += (int32_t)(0.5 * sum[1]/count[1]);
		if (count[2] > 0)
			actuatorMessage.value += (int32_t)(0.25 * sum[2]/count[2]);
		if (count[3] > 0)
			actuatorMessage.value += (int32_t)(0.25 * sum[3]/count[3]);

		xQueueSend(actuatorQ, &actuatorMessage, 10000);
	}
}

/******************************************************************************
* trcDemoISR
*
* The "FakeISR" task, that simulates the ISRTimer interrupts, which triggers
* the Sensor tasks.
******************************************************************************/
static portTASK_FUNCTION( trcDemoISR, pvParameters )
{
	portTickType xNextWakeTime;
	portBASE_TYPE dummy;
	int i = 0;

	(void)pvParameters;

	/* Initialize xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();
	vTraceSetISRProperties("ISRTimer1", 3);
	vTraceSetISRProperties("ISRTimer2", 2);
	vTraceSetISRProperties("ISRTimer3", 1);
	vTaskDelayUntil( &xNextWakeTime, 1);

	for( ;; )
	{
		i++;

		if (i % ISR3_PERIOD == 0)
		{
			portENTER_CRITICAL();
			vTraceStoreISRBegin((void*)"ISRTimer3");
			xSemaphoreGiveFromISR(Sem3, &dummy);
			vTraceStoreISREndManual(dummy);
			portEXIT_CRITICAL();
		}

		if (i % ISR2_PERIOD == 0)
		{
			portENTER_CRITICAL();
			vTraceStoreISRBegin((void*)"ISRTimer2");
			xSemaphoreGiveFromISR(Sem2, &dummy);
			vTraceStoreISREndManual(dummy);
			portEXIT_CRITICAL();
		}

		if (i % ISR1_PERIOD == 0)
		{
			portENTER_CRITICAL();
			vTraceStoreISRBegin((void*)"ISRTimer1");
			xSemaphoreGiveFromISR(Sem1, &dummy);
			vTraceStoreISREndManual(dummy);
			portEXIT_CRITICAL();


		}

		vTaskDelayUntil( &xNextWakeTime, 1);
	}
}

/******************************************************************************
* trcDemoTaskActuator
*
* The "Actuator" task, just reads the data from Controller and logs it in a
* User Event (i.e., the "vTracePrintF" calls).
******************************************************************************/
static portTASK_FUNCTION( trcDemoTaskActuator, pvParameters )
{
	QueueMessage inMessage;
	(void)pvParameters;
	vTraceStoreUserEventChannelName("Actuator Out Signal");

	for( ;; )
	{
		vTraceInstanceFinishedNow();
		/* Place this task in blocked state until it is time to run again. */
		if (xQueueReceive(actuatorQ, &inMessage, 35) != pdTRUE)
		{
			vTracePrintF("Actuator Out Signal", "No data...");
		}
		else
		{
			if (inMessage.code == MSGCODE_CONTROL_VALUE)
			{
				vTracePrintF("Actuator Out Signal", "Out: %d",
							 inMessage.value);
			}
		}
	}
}

#if (configUSE_TIMERS == 1)
void myTimerHandler(xTimerHandle tmr)
{
	(void) tmr;
	vTracePrintF("Timer", "Timer handler!");
}
#endif

int sensorTaskID1 = 1;
int sensorTaskID2 = 2;
int sensorTaskID3 = 3;

#define vTaskCreateNotTraced( pvTaskCode, pcName, usStackDepth, pvParameters, uxPriority ) \
	{ void* this_pxCreatedTask; \
	vTraceSetReadyEventsEnabled(0); \
	xTaskGenericCreate( ( pvTaskCode ), ( pcName ), ( usStackDepth ), ( pvParameters ), ( uxPriority ), ( &this_pxCreatedTask ), ( NULL ), ( NULL ) ); \
	vTraceSetReadyEventsEnabled(1); \
	if (this_pxCreatedTask != NULL){ vTraceExcludeTaskFromTrace(this_pxCreatedTask); }else{ return -42;} }

/******************************************************************************
* trcDemoTaskActuator
*
* The "Actuator" task, just reads the data from Controller and logs it in a
* User Event (i.e., the "vTracePrintF" calls).
******************************************************************************/
int vStartDemoApplication(void)
{
	void* objectHandle = NULL;

	vTraceStoreUserEventChannelName("Messages");

	vTracePrint("Messages", "Demo starting...");
	vTracePrint("Messages", "vTraceUserEvent creates basic User Events.");
	vTracePrint("Messages", "vTracePrintF creates advanced user events, like printf");
	//vTracePrintF("Messages", "A float: %f (should be 1)", (float)1.0);
	//vTracePrintF("Messages", "A double: %lf (should be 1)", (double)1.0);
	//vTracePrintF("Messages", "A signed 8-bit value: %bd (should be -1)", -1);

	vTraceStoreUserEventChannelName("Timer");
	
	sensorQ = xQueueCreate(15, sizeof(QueueMessage) );
	if( sensorQ == 0 )
	{
		vTracePrint("Messages", "Could not create SensorQ!\n");
		return -1;
	}
	vTraceSetQueueName(sensorQ, "SensorQueue");

	actuatorQ = xQueueCreate(3, sizeof(QueueMessage) );
	if( actuatorQ == 0 )
	{
		vTracePrint("Messages", "Could not create ActuatorQ!\n");
		return -2;
	}
	vTraceSetQueueName(actuatorQ, "ActuatorQueue");

	vSemaphoreCreateBinary(Sem1);
	if( Sem1 == NULL )
	{
		vTracePrint("Messages", "Could not create Sem1!\n");
		return -3;
	}
	vTraceSetSemaphoreName(Sem1, "SemaphSenX");

	vSemaphoreCreateBinary(Sem2);
	if( Sem2 == NULL )
	{
		vTracePrint("Messages", "Could not create Sem2!\n");
		return -4;
	}
	vTraceSetSemaphoreName(Sem2, "SemaphSenY");

	vSemaphoreCreateBinary(Sem3);
	if( Sem3 == NULL )
	{
		vTracePrint("Messages", "Could not create Sem3!\n");
		return -5;
	}
	vTraceSetSemaphoreName(Sem3, "SemaphSenZ");

	xTaskCreate( trcDemoTaskSensor, "SensorX",
				configMINIMAL_STACK_SIZE*2, &sensorTaskID1, 8, &objectHandle );
	if (objectHandle == NULL)
	{
		return -6;
	}

	xTaskCreate( trcDemoTaskSensor, "SensorY",
				configMINIMAL_STACK_SIZE*2, &sensorTaskID2, 7, &objectHandle );
	if (objectHandle == NULL)
	{
		return -7;
	}

	xTaskCreate( trcDemoTaskSensor, "SensorZ",
				configMINIMAL_STACK_SIZE*2, &sensorTaskID3, 6, &objectHandle );
	if (objectHandle == NULL)
	{
		return -8;
	}

	xTaskCreate( trcDemoTaskController, "Control",
				configMINIMAL_STACK_SIZE*2, NULL, 4, &objectHandle );
	if (objectHandle == NULL)
	{
		return -9;
	}

	xTaskCreate( trcDemoTaskActuator, "Actuator",
				configMINIMAL_STACK_SIZE*2, NULL, 5, &objectHandle );
	if (objectHandle == NULL)
	{
		return -10;
	}

	xTaskCreate( trcDemoTaskSuperv, "Superv",
				configMINIMAL_STACK_SIZE*2, NULL, 3, &objectHandle );
	if (objectHandle == NULL)
	{
		return -11;
	}
	
	xTaskCreate( trcDemoISR, "(Hide)FakeISR",
				configMINIMAL_STACK_SIZE*2, NULL, configMAX_PRIORITIES-1, &objectHandle);
	if (objectHandle == NULL)
	{
		return -12;
	}
	
	return 0;
}
