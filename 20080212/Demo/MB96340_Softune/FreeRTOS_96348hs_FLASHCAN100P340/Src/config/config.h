/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*---------------------------------------------------------------------------
  config.h
  - This file contains the defines to include or exclude a certain demo
    application function.
/*---------------------------------------------------------------------------*/
/* The below are the defines that includes the corresponding function (those create related
 * tasks) if they are defined aand vice a versa.
 */

#define INCLUDE_StartIntegerMathTasks		1

#define INCLUDE_StartPolledQueueTasks		1
#define INCLUDE_StartSemaphoreTasks			1
#define INCLUDE_StartBlockingQueueTasks		1
#define INCLUDE_StartDynamicPriorityTasks	1

#define INCLUDE_StartHookCoRoutines			1
#define INCLUDE_StartGenericQueueTasks		1
#define INCLUDE_StartQueuePeekTasks			1

#define INCLUDE_CreateSuicidalTasks			1

/*---------------------------------------------------------------------------*/

#if __CONFIG__ == 1
	#define INCLUDE_StartLEDFlashTasks			1
	#define INCLUDE_AltStartComTestTasks		1
	#define INCLUDE_StartMathTasks				0
	#define INCLUDE_StartFlashCoRoutines		0
	#define INCLUDE_CreateBlockTimeTasks		0
	#define INCLUDE_TraceListTasks				1
#elif __CONFIG__ == 2
	#define INCLUDE_StartLEDFlashTasks			0
	#define INCLUDE_AltStartComTestTasks		0
	#define INCLUDE_StartMathTasks				0
	#define INCLUDE_StartFlashCoRoutines		1
	#define INCLUDE_CreateBlockTimeTasks		1
	#define INCLUDE_TraceListTasks				1
#elif __CONFIG__ == 3
	#define INCLUDE_StartLEDFlashTasks			1
	#define INCLUDE_AltStartComTestTasks		1
	#define INCLUDE_StartMathTasks				1
	#define INCLUDE_StartFlashCoRoutines		0
	#define INCLUDE_CreateBlockTimeTasks		1
	#define INCLUDE_TraceListTasks				0
#elif __CONFIG__ == 4
	#define INCLUDE_StartLEDFlashTasks			0
	#define INCLUDE_AltStartComTestTasks		0
	#define INCLUDE_StartMathTasks				1
	#define INCLUDE_StartFlashCoRoutines		1
	#define INCLUDE_CreateBlockTimeTasks		0
	#define INCLUDE_TraceListTasks				1
#else
	#error __CONFIG__ should be defined and it should have value between 1 to 4
#endif

/* vStartFlashCoRoutines() can only be used (by defining INCLUDE_StartFlashCoRoutines as 1) 
 * if vStartLEDFlashTasks() and vAltStartComTestTasks() functions are not used (by defining 
 * INCLUDE_StartLEDFlashTasks and INCLUDE_AltStartComTestTasks both as 0) and vice a versa. 
 * This is because tasks created by these functions shares the LEDs connected to Port 00. The 
 * corresponding code from the function prvCheckOtherTasksAreStillRunning() should also be 
 * commented.
 */
 
/* In order to have vTraceListTasks() the below define INCLUDE_TraceListTasks should be defined
 * as 1. While doing so one have to compromise on some of the other tasks as vTraceListTasks() 
 * requires high amount of memory. It should be noted that if all the task are tried to be inclued
 * then the compiler would give memory overflow error.
 */