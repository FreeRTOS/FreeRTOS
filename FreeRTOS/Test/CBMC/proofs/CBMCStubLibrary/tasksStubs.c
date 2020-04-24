#include "FreeRTOS.h"
#include "task.h"
#include "tasksStubs.h"

#ifndef TASK_STUB_COUNTER
	#define TASK_STUB_COUNTER 0;
#endif

/* 5 is a magic number, but we need some number here as a default value.
   This value is used to bound any loop depending on xTaskCheckForTimeOut
   as a loop bound. It should be overwritten in the Makefile.json adapting
   to the performance requirements of the harness. */
#ifndef TASK_STUB_COUNTER_LIMIT
	#define TASK_STUB_COUNTER_LIMIT 5;
#endif


static BaseType_t xCounter = TASK_STUB_COUNTER;
static BaseType_t xCounterLimit = TASK_STUB_COUNTER_LIMIT;

BaseType_t xTaskGetSchedulerState( void )
{
	return xState;
}

/* This function is another method apart from overwritting the defines to init the max
   loop bound. */
void vInitTaskCheckForTimeOut(BaseType_t maxCounter, BaseType_t maxCounter_limit)
{
	xCounter = maxCounter;
	xCounterLimit = maxCounter_limit;
}

/* This is mostly called in a loop. For CBMC, we have to bound the loop
   to a max limits of calls. In this stub implementation, some randomization 
   is provided by none fixed value of increment. In the worst case, function 
   returns pdTRUE after 3 entries (increment = 1). */
BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut, TickType_t * const pxTicksToWait ) {
	
	(void *) pxTimeOut;
	(void *) pxTicksToWait;

	static uint8_t time = 0;
	uint8_t increment;

	__CPROVER_assume(increment > 0 && increment < 10);
	time += increment;

	return time > 2 ? pdTRUE : pdFALSE;
}
