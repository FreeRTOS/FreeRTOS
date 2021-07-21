#ifndef INC_TASK_STUBS_H
#define INC_TASK_STUBS_H

#include "FreeRTOS.h"
#include "task.h"

BaseType_t xState;
void vInitTaskCheckForTimeOut( BaseType_t maxCounter,
                               BaseType_t maxCounter_limit );

#endif /* INC_TASK_STUBS_H */
