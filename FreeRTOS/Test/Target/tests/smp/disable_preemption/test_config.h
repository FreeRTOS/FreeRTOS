#ifndef _TEST_CONFIG_H
#define _TEST_CONFIG_H

#define configUSE_TASK_PREEMPTION_DISABLE       1

extern void test_fr6TASK_SWITCHED_IN(void);
#define traceTASK_SWITCHED_IN() test_fr6TASK_SWITCHED_IN()

#endif
