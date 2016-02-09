/****************************************************************************
* © 2013 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*/

/** @defgroup pwm pwm_c_wrapper
 *  @{
 */
/** @file pwm_c_wrapper.cpp
 \brief the pwm component C wrapper   
 This program is designed to allow the other C programs to be able to use this component

 There are entry points for all C wrapper API implementation

<b>Platform:</b> This is ARC-based component 

<b>Toolset:</b> Metaware IDE(8.5.1)
<b>Reference:</b> smsc_reusable_fw_requirement.doc */

/*******************************************************************************
 *  SMSC version control information (Perforce):
 *
 *  FILE:     $File: //depot_pcs/FWEng/Release/projects/CEC1302_CLIB/release2/Source/hw_blks/common/include/cfg.h $
 *  REVISION: $Revision: #1 $
 *  DATETIME: $DateTime: 2015/12/23 15:37:58 $
 *  AUTHOR:   $Author: akrishnan $
 *
 *  Revision history (latest first):
 *      #1 Branched from //depotAE/projects/Sensor_Fusion/maincodeline/sf01_evb
 *      #2 Updated tasks for smbus driver and smbus application
 *      #3 Added feature, algo and fusion task
 *      #4 Removed smbapp task
 ***********************************************************************************
 */

#ifndef _CFG_H_
#define _CFG_H_


/*
 * TOOLSET  : defines the build tools used
 *          TOOLKEIL - For KEIL Toolset
 *          TOOLPC   - For PC Toolset, ex: MSVC++ 6.0,Borland C..etc.
 *
 */


#define INTERACTIVE_UART 0

/*
 * TASK_XX  : defines the Kernel Task Assignements to Different Application Specific Tasks
 *          : Always TASK_00 is High Priority
 *          : Ex1: To Assign timer task to TASK_00
 *          :     #define TASK_00   timer
 *          : Ex2: To Assign pwm task to TASK_03
 *          :     #define TASK_03   pwm
 *          : Each Task should have Following Function Definitions
 *          : (void) Tasxx_Init_task(void);
 *          : (void) Taskxx_Main_task(enum EVENT_TYPE event);
 *          : Please refer kernel.h for enum EVENT_TYPE
 *          : Ex: If Application needs "tach" task should be added to kernel,
 *          :     tach.c should contain following public calls:
 *          :     (void)tach_init_task(void);
 *          :     (void)tach_main_task(enum EVENT_TYPE event);
 *          :
 *          : Each Task's event ie. EVENT TASK & EVENT TIMEOUT could be assigned the 
 *          : priority level. if it is assigned HIGH, then Task's event will belong to
 *          : HIGH priority group.
 *          : ex: define TASK_04 as pwm and pwm tasks event with following priority list
 *          : PRIORITY_TASK_04_EVENTTASK    LOW  - This means, the pwm task (which is TASK_04) Event Task will be assigned to low priority group
 *          : PRIORITY_TASK_04_EVENTTIMEOUT HIGH - This means, the pwm task Event Timeout will be assigned Hihg priority group
 *
 */
#define LOW     0
#define HIGH    !LOW

#define INTR_ON     1
#define INTR_OFF    0

#define TASK_SCHED_LO   1
#define TASK_SCHED_HI   2

#define MAX_NUM_TASKS	31    // Bits 0 - 30

// !!!! CRITICAL !!!
// You MUST define the following values correctly
//
#define NUMBER_OF_TASKS 18                               /* Total No: of Enabled Tasks           */

#define TASK_00                         timer            /* TASK_00=timer                        */
#define PRIORITY_TASK_00_EVENTTASK      HIGH             /* Timer Event Task HIGH priority       */
#define PRIORITY_TASK_00_EVENTTIMEOUT   HIGH             /* Timer Event Timeout HIGH priority    */
#define ENABLE_TASK_00_EVENTINTR        1                /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_00_EVENTTASK        0
#define ENABLE_TASK_00_EVENTTIMER       0

#define TASK_01                         spi              /* Task_01=spi - for spi                */
#define PRIORITY_TASK_01_EVENTTASK      LOW              /* Event Task HIGH priority             */
#define PRIORITY_TASK_01_EVENTTIMEOUT   LOW              /* Event Timeout LOW priority    	     */
#define ENABLE_TASK_01_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_01_EVENTTASK        0
#define ENABLE_TASK_01_EVENTTIMER       1

#define TASK_02                         smbus            /* Task_02=smbus                          */
#define PRIORITY_TASK_02_EVENTTASK      HIGH             /* temp Event Task HIGH priority          */
#define PRIORITY_TASK_02_EVENTTIMEOUT   HIGH             /* temp Event Timeout LOW priority        */
#define ENABLE_TASK_02_EVENTINTR        1                /* Enable EventTypeInterrupt scheduling   */
#define ENABLE_TASK_02_EVENTTASK        1
#define ENABLE_TASK_02_EVENTTIMER       1

#define TASK_03                         smbus_app        /* TASK_03=smbus_app                      */
#define PRIORITY_TASK_03_EVENTTASK      HIGH             /* Event Task HIGH priority               */
#define PRIORITY_TASK_03_EVENTTIMEOUT   HIGH             /* Event Timeout HIGH priority            */
#define ENABLE_TASK_03_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling   */
#define ENABLE_TASK_03_EVENTTASK        1
#define ENABLE_TASK_03_EVENTTIMER       1

#define TASK_04                         pwm              /* Task_04=pwm                         */
#define PRIORITY_TASK_04_EVENTTASK      LOW              /* Event Task LOW priority         */
#define PRIORITY_TASK_04_EVENTTIMEOUT   LOW              /* Event Timeout LOW priority      */
#define ENABLE_TASK_04_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_04_EVENTTASK        0
#define ENABLE_TASK_04_EVENTTIMER       1

#define TASK_05                         adc             /* TASK_05=adc                         */
#define PRIORITY_TASK_05_EVENTTASK      LOW             /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_05_EVENTTIMEOUT   LOW             /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_05_EVENTINTR        0               /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_05_EVENTTASK        0            
#define ENABLE_TASK_05_EVENTTIMER       1            

#define TASK_06                         gpio            /* TASK_06=gpio                        */
#define PRIORITY_TASK_06_EVENTTASK      LOW             /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_06_EVENTTIMEOUT   HIGH             /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_06_EVENTINTR        0               /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_06_EVENTTASK        0               
#define ENABLE_TASK_06_EVENTTIMER       1               

#define TASK_07                         btimer         /* Task_07=btimer                       */
#define PRIORITY_TASK_07_EVENTTASK      LOW            /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_07_EVENTTIMEOUT   LOW            /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_07_EVENTINTR        0              /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_07_EVENTTASK        0
#define ENABLE_TASK_07_EVENTTIMER       1

#define TASK_08                         led            /* Task_08=led                         */
#define PRIORITY_TASK_08_EVENTTASK      LOW             /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_08_EVENTTIMEOUT   LOW             /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_08_EVENTINTR        0               /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_08_EVENTTASK        0
#define ENABLE_TASK_08_EVENTTIMER       1

#define TASK_09                         wdt             /* Task_09=wdt                         */
#define PRIORITY_TASK_09_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_09_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_09_EVENTINTR        1                /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_09_EVENTTASK        1
#define ENABLE_TASK_09_EVENTTIMER       1

#define TASK_10                         aes            /* Task_10=aes                           */
#define PRIORITY_TASK_10_EVENTTASK      LOW            /* phot Event Task LOW priority          */
#define PRIORITY_TASK_10_EVENTTIMEOUT   LOW            /* phot Event Timeout LOW priority       */
#define ENABLE_TASK_10_EVENTINTR        0              /* Enable EventTypeInterrupt scheduling  */
#define ENABLE_TASK_10_EVENTTASK        0		
#define ENABLE_TASK_10_EVENTTIMER       1
                                        
#define TASK_11                         rnd            /* Task_11=rnd                         */
#define PRIORITY_TASK_11_EVENTTASK      LOW            /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_11_EVENTTIMEOUT   LOW            /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_11_EVENTINTR        0              /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_11_EVENTTASK        0
#define ENABLE_TASK_11_EVENTTIMER       1
                                        
#define TASK_12                         sha            /* Task_12=sha                         */
#define PRIORITY_TASK_12_EVENTTASK      LOW            /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_12_EVENTTIMEOUT   LOW            /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_12_EVENTINTR        0              /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_12_EVENTTASK        0
#define ENABLE_TASK_12_EVENTTIMER       1
                                        
#define TASK_13                         pke            /* Task_13=pke                         */
#define PRIORITY_TASK_13_EVENTTASK      LOW            /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_13_EVENTTIMEOUT   LOW            /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_13_EVENTINTR        0              /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_13_EVENTTASK        0
#define ENABLE_TASK_13_EVENTTIMER       1

#define TASK_14                         tach          /* Task_14=tach                         */
#define PRIORITY_TASK_14_EVENTTASK      LOW           /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_14_EVENTTIMEOUT   LOW           /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_14_EVENTINTR        0             /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_14_EVENTTASK        0
#define ENABLE_TASK_14_EVENTTIMER       1

#define TASK_15                         rtc           /* Task_15=rtc                         */
#define PRIORITY_TASK_15_EVENTTASK      LOW           /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_15_EVENTTIMEOUT   LOW           /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_15_EVENTINTR        1             /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_15_EVENTTASK        0
#define ENABLE_TASK_15_EVENTTIMER       1

#define TASK_16                         htimer            /* TASK_06=htimer                       */
#define PRIORITY_TASK_16_EVENTTASK      LOW               /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_16_EVENTTIMEOUT   LOW               /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_16_EVENTINTR        0                 /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_16_EVENTTASK        0            
#define ENABLE_TASK_16_EVENTTIMER       1     

#define TASK_17                         uart             /* Task_17=uart                          */
#define PRIORITY_TASK_17_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
#define PRIORITY_TASK_17_EVENTTIMEOUT   HIGH              /* Dflt Event Timeout LOW priority      */
#define ENABLE_TASK_17_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
#define ENABLE_TASK_17_EVENTTASK        0           
#define ENABLE_TASK_17_EVENTTIMER       1 

#define TASK_18                         dflt         /* Task_18=dflt                          */
#define PRIORITY_TASK_18_EVENTTASK      LOW          /* Dflt Event Task LOW priority          */
#define PRIORITY_TASK_18_EVENTTIMEOUT   LOW          /* Dflt Event Timeout LOW priority       */
#define ENABLE_TASK_18_EVENTINTR        1            /* Enable EventTypeInterrupt scheduling  */
#define ENABLE_TASK_18_EVENTTASK        1
#define ENABLE_TASK_18_EVENTTIMER       1

//#define TASK_19                         dflt       /* Task_19=dflt                          */
//#define PRIORITY_TASK_19_EVENTTASK      LOW        /* Dflt Event Task LOW priority          */
//#define PRIORITY_TASK_19_EVENTTIMEOUT   LOW        /* Dflt Event Timeout LOW priority       */
//#define ENABLE_TASK_19_EVENTINTR        0          /* Enable EventTypeInterrupt scheduling  */
//#define ENABLE_TASK_19_EVENTTASK        0
//#define ENABLE_TASK_19_EVENTTIMER       0

//#define TASK_20                         dflt             /* Task_20=dflt                         */
//#define PRIORITY_TASK_20_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_20_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_20_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_20_EVENTTASK        0
//#define ENABLE_TASK_20_EVENTTIMER       0

//#define TASK_21                         dflt             /* Task_21=dflt                         */
//#define PRIORITY_TASK_21_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_21_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_21_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_21_EVENTTASK        0
//#define ENABLE_TASK_21_EVENTTIMER       0

//#define TASK_22                         dflt             /* Task_22=dflt                         */
//#define PRIORITY_TASK_22_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_22_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_22_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_22_EVENTTASK        0
//#define ENABLE_TASK_22_EVENTTIMER       0

//#define TASK_23                         dflt             /* Task_23=dflt                         */
//#define PRIORITY_TASK_23_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_23_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_23_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_23_EVENTTASK        0
//#define ENABLE_TASK_23_EVENTTIMER       0

//#define TASK_24                         dflt             /* Task_24=dflt                         */
//#define PRIORITY_TASK_24_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_24_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_24_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_24_EVENTTASK        0
//#define ENABLE_TASK_24_EVENTTIMER       0

//#define TASK_25                         dflt             /* Task_25=dflt                         */
//#define PRIORITY_TASK_25_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_25_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_25_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_25_EVENTTASK        0
//#define ENABLE_TASK_25_EVENTTIMER       0

//#define TASK_26                         dflt             /* Task_26=dflt                         */
//#define PRIORITY_TASK_26_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_26_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_26_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_26_EVENTTASK        0
//#define ENABLE_TASK_26_EVENTTIMER       0

//#define TASK_27                         dflt             /* Task_27=dflt                         */
//#define PRIORITY_TASK_27_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_27_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_27_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_27_EVENTTASK        0
//#define ENABLE_TASK_27_EVENTTIMER       0

//#define TASK_28                         dflt             /* Task_28=dflt                         */
//#define PRIORITY_TASK_28_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_28_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_28_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_28_EVENTTASK        0
//#define ENABLE_TASK_28_EVENTTIMER       0

//#define TASK_29                         dflt             /* Task_29=dflt                         */
//#define PRIORITY_TASK_29_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_29_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_29_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_29_EVENTTASK        0
//#define ENABLE_TASK_29_EVENTTIMER       0

//#define TASK_30                         dflt             /* Task_30=dflt                         */
//#define PRIORITY_TASK_30_EVENTTASK      LOW              /* Dflt Event Task LOW priority         */
//#define PRIORITY_TASK_30_EVENTTIMEOUT   LOW              /* Dflt Event Timeout LOW priority      */
//#define ENABLE_TASK_30_EVENTINTR        0                /* Enable EventTypeInterrupt scheduling */
//#define ENABLE_TASK_30_EVENTTASK        0
//#define ENABLE_TASK_30_EVENTTIMER       0


#endif /*_CFG_H_*/

/**   @}
 */

