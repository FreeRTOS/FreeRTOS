/***************************************************************************
*	Ӧ�ó�������
*
*/
#ifndef __APPCONFIG_H__
#define __APPCONFIG_H__

#ifdef __kernel__
#include "FreeRTOSConfig.h"
#endif


//	�������ȼ�
/****************************************************************************
*	Task Param
*/
#define	TASK_PRIO_HIGH		 5		// �����ȼ�����
#define TASK_PRIO_LOW		 4		// �����ȼ�����
#define TASK_PRIO_LOWEST	 3		// ������ȼ�����
#define TASK_PRIO_TIME	     2		// ��ʱ������
#define TASK_PRIO_INIT		 1		// ��ʼ������

/*
*	�������õ�ջ���
*/
//#define	DEFAULT_TASK_STACK_SIZE		128			// ����Ĭ�϶�ջ��С
#define TASK_STACK_INIT		        128
#define LOWPROTASK_STACK_SIZE		128        // �����ȼ�����Ķ�ջ���
#define LOWESTPROTASK_STACK_SIZE        128
#define HIGHPROTASK_STACK_SIZE		128         // �����ȼ�����Ķ�ջ���

#endif
