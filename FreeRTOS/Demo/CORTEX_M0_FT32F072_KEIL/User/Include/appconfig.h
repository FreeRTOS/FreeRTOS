/***************************************************************************
*	应用程序配置
*
*/
#ifndef __APPCONFIG_H__
#define __APPCONFIG_H__

#ifdef __kernel__
#include "FreeRTOSConfig.h"
#endif


//	任务优先级
/****************************************************************************
*	Task Param
*/
#define	TASK_PRIO_HIGH		 5		// 高优先级级别
#define TASK_PRIO_LOW		 4		// 低优先级级别
#define TASK_PRIO_LOWEST	 3		// 最低优先级级别
#define TASK_PRIO_TIME	     2		// 定时器任务
#define TASK_PRIO_INIT		 1		// 初始化任务

/*
*	任务适用的栈深度
*/
//#define	DEFAULT_TASK_STACK_SIZE		128			// 任务默认堆栈大小
#define TASK_STACK_INIT		        128
#define LOWPROTASK_STACK_SIZE		128        // 低优先级任务的堆栈深度
#define LOWESTPROTASK_STACK_SIZE        128
#define HIGHPROTASK_STACK_SIZE		128         // 高优先级任务的堆栈深度

#endif
