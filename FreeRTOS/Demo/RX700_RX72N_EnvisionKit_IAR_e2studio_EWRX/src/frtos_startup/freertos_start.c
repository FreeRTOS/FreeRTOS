/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only 
* intended for use with Renesas products. No other uses are authorized. This 
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE 
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
* Copyright (C) 2018 Renesas Electronics Corporation. All rights reserved.    
*******************************************************************************/
/*******************************************************************************
* File Name    : freertos_start.c
* Version      : 1.0
* Description  : Contains FreeRTOS user-defined functions.
******************************************************************************/
/*****************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 30.06.2016 1.00     First Release
******************************************************************************/

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "platform.h"
#include "freertos_start.h"
#include "demo_main.h"
#include "demo_specific_io.h"

#if (BSP_CFG_RTOS_USED == 1)

#if (RTOS_USB_SUPPORT == 1)
#include "r_usb_basic_if.h"
#include "r_usb_cstd_rtos.h"
#endif

/******************************************************************************
Macro definitions
******************************************************************************/

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Private global variables and functions
******************************************************************************/

/************* semaphore initialization *****************/

/******************************************************************************
Exported global variables (to be accessed by other files)
******************************************************************************/

/******************************************************************************
Exported global functions (to be accessed by other files)
******************************************************************************/

/* FreeRTOS's system timer. */
void vApplicationSetupTimerInterrupt(void);

/* Hook functions used by FreeRTOS. */
void vAssertCalled(void);
void vApplicationIdleHook(void);
void vApplicationTickHook(void);
void vApplicationMallocFailedHook(void);
void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName);

/* FreeRTOS's processing before start the kernel. */
void Processing_Before_Start_Kernel(void);

/* Main task. */
extern void main_task(void *pvParameters);


/******************************************************************************
* Function Name: vApplicationSetupTimerInterrupt
* Description  : Initialize system timer for FreeRTOS with tick interrupt 1ms.
* Arguments    : None.
* Return Value : None.
******************************************************************************/
void vApplicationSetupTimerInterrupt(void)
{
	/* CMT channel 0 is configured as RTOS's system timer. */
#if (BSP_CFG_RTOS_SYSTEM_TIMER == 0)
    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA502;

    /* Enable compare match timer 0. */
    MSTP( CMT0 ) = 0;

    /* Stop counter. */
    CMT.CMSTR0.BIT.STR0 = 0;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    /* Enable interrupt on compare match.
     * Divide the PCLK by 8. */
    CMT0.CMCR.WORD = 0x00C0; // CKS=00b,CMIE=1; PCLK/8,Compare match interrupt (CMIn) enabled @60MHz

    /* Set the compare match value. */
    CMT0.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ )) / 8 - 1);

    /* Clear counter. */
    CMT0.CMCNT = 0;

    /* Clear any previously pending interrupts. */
    IR(CMT0, CMI0)  = 0;

    /* Enable the interrupt. */
    IEN(CMT0, CMI0) = 1;

    /* Set its priority to the application defined kernel priority. */
    IPR(CMT0, CMI0) = configKERNEL_INTERRUPT_PRIORITY;

    /* Start the timer 0. */
    CMT.CMSTR0.BIT.STR0 = 1;
#endif /* (BSP_CFG_RTOS_SYSTEM_TIMER == 0) */

    /* CMT channel 1 is configured as RTOS's system timer. */
#if (BSP_CFG_RTOS_SYSTEM_TIMER == 1)
    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA502;

    /* Enable compare match timer 1. */
    MSTP( CMT1 ) = 0;

    /* Stop counter. */
    CMT.CMSTR0.BIT.STR1 = 0;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    /* Enable interrupt on compare match.
     * Divide the PCLK by 8. */
    CMT1.CMCR.WORD = 0x00C0; // CKS=00b,CMIE=1; PCLK/8,Compare match interrupt (CMIn) enabled @60MHz

    /* Set the compare match value. */
    CMT1.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ )) / 8 - 1);

    /* Clear counter. */
    CMT1.CMCNT = 0;

    /* Clear any previously pending interrupts. */
    IR(CMT1, CMI1)  = 0;

    /* Enable the interrupt. */
    IEN(CMT1, CMI1) = 1;

    /* Set its priority to the application defined kernel priority. */
    IPR(CMT1, CMI1) = configKERNEL_INTERRUPT_PRIORITY;

    /* Start the timer 1. */
    CMT.CMSTR0.BIT.STR1 = 1;
#endif /* (BSP_CFG_RTOS_SYSTEM_TIMER == 1) */

    /* CMT channel 2 is configured as RTOS's system timer. */
#if (BSP_CFG_RTOS_SYSTEM_TIMER == 2)
    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA502;

    /* Enable compare match timer 2. */
    MSTP( CMT2 ) = 0;

    /* Stop counter. */
    CMT.CMSTR1.BIT.STR2 = 0;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    /* Enable interrupt on compare match.
     * Divide the PCLK by 8. */
    CMT2.CMCR.WORD = 0x00C0; // CKS=00b,CMIE=1; PCLK/8,Compare match interrupt (CMIn) enabled @60MHz

    /* Set the compare match value. */
    CMT2.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ )) / 8 - 1);

    /* Clear counter. */
    CMT2.CMCNT = 0;

    /* Clear any previously pending interrupts. */
    IR(CMT2, CMI2)  = 0;

    /* Enable the interrupt. */
    IEN(CMT2, CMI2) = 1;

    /* Set its priority to the application defined kernel priority. */
    IPR(CMT2, CMI2) = configKERNEL_INTERRUPT_PRIORITY;

    /* Start the timer 2. */
    CMT.CMSTR1.BIT.STR2 = 1;
#endif /* (BSP_CFG_RTOS_SYSTEM_TIMER == 2) */

    /* CMT channel 3 is configured as RTOS's system timer. */
#if (BSP_CFG_RTOS_SYSTEM_TIMER == 3)
    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA502;

    /* Enable compare match timer 3. */
    MSTP( CMT3 ) = 0;

    /* Stop counter. */
    CMT.CMSTR1.BIT.STR3 = 0;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    /* Enable interrupt on compare match.
     * Divide the PCLK by 8. */
    CMT3.CMCR.WORD = 0x00C0; // CKS=00b,CMIE=1; PCLK/8,Compare match interrupt (CMIn) enabled @60MHz

    /* Set the compare match value. */
    CMT3.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ )) / 8 - 1);

    /* Clear counter. */
    CMT3.CMCNT = 0;

    /* Clear any previously pending interrupts. */
    IR(CMT3, CMI3)  = 0;

    /* Enable the interrupt. */
    IEN(CMT3, CMI3) = 1;

    /* Set its priority to the application defined kernel priority. */
    IPR(CMT3, CMI3) = configKERNEL_INTERRUPT_PRIORITY;

    /* Start the timer 3. */
    CMT.CMSTR1.BIT.STR3 = 1;
#endif /* (BSP_CFG_RTOS_SYSTEM_TIMER == 3) */

} /* End of function vApplicationSetupTimerInterrupt() */

/******************************************************************************
* Function Name: vAssertCalled
* Description  : This function is used to validate the input parameters.
* Arguments    : None.
* Return Value : None.
******************************************************************************/
void vAssertCalled(void)
{
    volatile unsigned long ul = 0;

    taskENTER_CRITICAL();
    {
        /* Use the debugger to set ul to a non-zero value in order to step out
        of this function to determine why it was called. */
        while( 0 == ul )
        {
            portNOP();
        }
    }
    taskEXIT_CRITICAL();

} /* End of function vAssertCalled() */

/******************************************************************************
* Function Name: vApplicationIdleHook
* Description  : This function will be called on each cycle of the idle task.
*                NOTE: vApplicationIdleHook() MUST NOT CALL A FUNCTION
*                      THAT MIGHT BLOCK UNDER ANY CIRCUMSTANCES.
* Arguments    : None.
* Return Value : None.
******************************************************************************/
void vApplicationIdleHook(void)
{
    volatile size_t xFreeHeapSpace;

    /* This is just a trivial example of an idle hook.  It is called on each
    cycle of the idle task.  It must *NOT* attempt to block.  In this case the
    idle task just queries the amount of FreeRTOS heap that remains.  See the
    memory management section on the http://www.FreeRTOS.org web site for memory
    management options.  If there is a lot of heap memory free then the
    configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
    RAM. */
    xFreeHeapSpace = xPortGetFreeHeapSize();

    /* Remove compiler warning about xFreeHeapSpace being set but never used. */
    ( void ) xFreeHeapSpace;

} /* End of function vApplicationIdleHook() */

/******************************************************************************
* Function Name: vApplicationTickHook
* Description  : This function will be called every tick interrupt.
*                NOTE: vApplicationTickHook() EXECUTES FROM WITHIN AN ISR,
*                      SO MUST BE VERY SHORT AND NOT USE MUCH STACK.
*                      IN ADDITION, NOT CALL ANY APIs WITHOUT "FromISR" OR
*                      "FROM_ISR" AT THE END.
* Arguments    : None.
* Return Value : None.
******************************************************************************/
void vApplicationTickHook(void)
{
    /* The tick hook is not used by the blinky demo, but is by the full demo. */
    #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0
    {
        extern void vFullDemoTickHook( void );

        vFullDemoTickHook();
    }
    #endif

} /* End of function vApplicationTickHook() */

/******************************************************************************
* Function Name: vApplicationMallocFailedHook
* Description  : This function is to capture the failure while
*                memory allocation.
* Arguments    : None.
* Return Value : None.
******************************************************************************/
void vApplicationMallocFailedHook(void)
{
    /* Called if a call to pvPortMalloc() fails because there is insufficient
    free memory available in the FreeRTOS heap.  pvPortMalloc() is called
    internally by FreeRTOS API functions that create tasks, queues, software
    timers, and semaphores.  The size of the FreeRTOS heap is set by the
    configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */

    /* Force an assert. */
    configASSERT( ( volatile void * ) NULL );

    taskDISABLE_INTERRUPTS();
    for( ; ; )
    {
        /* Loop here */
    };

} /* End of function vApplicationMallocFailedHook() */

/******************************************************************************
* Function Name: vApplicationStackOverflowHook
* Description  : Hook function is to capture the failure when the stack size
*                is insufficient for processing.
* Arguments    : pxTask -
*                    Task handler
*                pcTaskName -
*                    Pointer of where to store the task's name
* Return Value : None.
******************************************************************************/
void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName)
{
    ( void ) pcTaskName;
    ( void ) pxTask;

    /* Run time stack overflow checking is performed if
    configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
    function is called if a stack overflow is detected. */

    /* Force an assert. */
    configASSERT( ( volatile void * ) NULL );

    taskDISABLE_INTERRUPTS();
    for( ; ; )
    {
        /* Loop here */
    };

} /* End of function vApplicationStackOverflowHook() */

/******************************************************************************
* Function Name : Processing_Before_Start_Kernel
* Description   : Create a main task, FreeRTOS's objects (e.g. mailbox, task,
*                 semaphore, mutex...) if required.
* Arguments     : None.
* Return value  : None.
******************************************************************************/
void Processing_Before_Start_Kernel(void)
{
#if 0 /* Generated Renesas Code */

    BaseType_t ret;

    /************** semaphore creation ***********************/



    /************** mutex creation ***************************/


    /************** queues creation **************************/


    /************** event groups creation ********************/


    /************** mailbox creation *************************/


    /************** memory pool creation *********************/
    
    /** USB RTOS Configuration **/
#if (RTOS_USB_SUPPORT == 1)
    usb_rtos_err_t err = usb_rtos_configuration();
    if (UsbRtos_Success != err)
    {
        while(1)
        {
            /** Failure of UsbRtos Configuration **/
        }
    }
#endif

    Kernel_Object_init();

    /************** task creation ****************************/
    /* Main task. */
    ret = xTaskCreate(main_task, "MAIN_TASK", 512, NULL, 3, NULL);
    if (pdPASS != ret)
    {
        while(1)
        {
            /* Failed! Task can not be created. */
        }
    }

#else /* Run FreeRTOS Demo */

    demo_main();

#endif

} /* End of function Processing_Before_Start_Kernel() */

/*
 * Configure the hardware as necessary to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
    extern void main_blinky( void );
#else
    extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

void demo_main( void )
{
    /* Configure the hardware ready to run the demo. */
    prvSetupHardware();

    /* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
    of this file. */
    #if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
    {
        main_blinky();
    }
    #else
    {
        main_full();
    }
    #endif

    /* Should never get reached. */
    return;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
    /* Turn on LED0 at start. (The system initialization had been done in the
    src/smc_gen/general/r_cg_hardware_setup.c.) */
    LED0 = LED_ON;
}
/*-----------------------------------------------------------*/

#endif /* (BSP_CFG_RTOS_USED == 1) */

