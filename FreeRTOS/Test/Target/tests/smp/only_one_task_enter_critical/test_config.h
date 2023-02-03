#ifndef TEST_CONFIG_H
#define TEST_CONFIG_H

/* This file must be included at the end of the FreeRTOSConfig.h. It contains
 * any FreeRTOS specific configurations that the test requires. */

#define configRUN_MULTIPLE_PRIORITIES        1
#define configUSE_CORE_AFFINITY              1
#define configUSE_MINIMAL_IDLE_HOOK          0
#define configUSE_TASK_PREEMPTION_DISABLE    0
#define configUSE_TIME_SLICING               1
#define configUSE_PREEMPTION                 1

#endif /* ifndef TEST_CONFIG_H */