/*
 * Copyright (c) 2015-2016, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 *  ======== PowerCC32XX_freertos.c ========
 */

#include <stdint.h>

/* driverlib header files */
#include <ti/devices/cc32xx/inc/hw_types.h>
#include <ti/devices/cc32xx/driverlib/prcm.h>
#include <ti/devices/cc32xx/driverlib/cpu.h>
#include <ti/devices/cc32xx/driverlib/rom.h>
#include <ti/devices/cc32xx/driverlib/rom_map.h>
#include <ti/devices/cc32xx/driverlib/systick.h>

#include <ti/drivers/Power.h>
#include <ti/drivers/power/PowerCC32XX.h>
#include <ti/drivers/dpl/ClockP.h>

#include <FreeRTOS.h>
#include <task.h>
#include <portmacro.h>

/* bitmask of constraints that disallow LPDS */
#define LPDS_DISALLOWED (1 << PowerCC32XX_DISALLOW_LPDS)

/* macro to pick two matching count values */
#define COUNT_WITHIN_TRESHOLD(a, b, c, th) \
        ((((b) - (a)) <= (th)) ? (b) : (c))

#define TRUE    1
#define FALSE   0


static volatile uint32_t idleTime = 0;

void PowerCC32XX_sleepPolicy()
{
#if (configUSE_TICKLESS_IDLE != 0)
    int i = 0;
    bool returnFromSleep = FALSE;
    unsigned long constraintMask;
    unsigned long long ullLowPowerTimeBeforeSleep, ullLowPowerTimeAfterSleep;
    unsigned long long count[3];
    unsigned long long ullSleepTime;
    unsigned long long time;
    unsigned long long remain;
    eSleepModeStatus eSleepStatus;

    /*
     *  Enter a critical section that will not effect interrupts
     *  bringing the MCU out of sleep mode.
     */
    vPortEnterCritical();

    /* query the declared constraints */
    constraintMask = Power_getConstraintMask();

    /* check if we are allowed to go to LPDS */
    if ((constraintMask & LPDS_DISALLOWED) == 0) {
        /*
         *  Read the current time from a time source that will remain
         *  operational while the microcontroller is in a low power state.
         */
        /*
         *  Get the current RTC count, using the fast interface; to use the
         *  fast interface the count must be read three times, and then
         *  the value that matches on at least two of the reads is chosen
         */
        for (i = 0; i < 3; i++) {
            count[i] = MAP_PRCMSlowClkCtrFastGet();
        }
        ullLowPowerTimeBeforeSleep =
            COUNT_WITHIN_TRESHOLD(count[0], count[1], count[2], 1);

        /* Stop the timer that is generating the tick interrupt. */
        MAP_SysTickDisable();

        /* Ensure it is still ok to enter the sleep mode. */
        eSleepStatus = eTaskConfirmSleepModeStatus();

        if (eSleepStatus == eAbortSleep ) {
            /*
             *  A task has been moved out of the Blocked state since this
             *  macro was executed, or a context siwth is being held pending.
             *  Do not enter a sleep state.  Restart the tick and exit the
             *  critical section.
             */
            MAP_SysTickEnable();
            vPortExitCritical();

            returnFromSleep = FALSE;
        }
        else {
            /* convert ticks to microseconds */
            time = idleTime * ClockP_getSystemTickPeriod();

            /* check if can go to LPDS */
            if (time > Power_getTransitionLatency(PowerCC32XX_LPDS,
                        Power_TOTAL)) {
                remain = ((time - PowerCC32XX_TOTALTIMELPDS) * 32768) / 1000000;

                /* set the LPDS wakeup time interval */
                MAP_PRCMLPDSIntervalSet(remain);

                /* enable the wake source to be timer */
                MAP_PRCMLPDSWakeupSourceEnable(PRCM_LPDS_TIMER);

                /* go to LPDS mode */
                Power_sleep(PowerCC32XX_LPDS);

                /* set 'returnFromSleep' to TRUE*/
                returnFromSleep = TRUE;
            }
            else {
                MAP_SysTickEnable();
                vPortExitCritical();

                returnFromSleep = FALSE;
            }
        }
    }
    else {
        /* A constraint was set */
        vPortExitCritical();
    }

    if (returnFromSleep) {
        /*
         *  Determine how long the microcontroller was actually in a low
         *  power state for, which will be less than xExpectedIdleTime if the
         *  microcontroller was brought out of low power mode by an interrupt
         *  other than that configured by the vSetWakeTimeInterrupt() call.
         *  Note that the scheduler is suspended before
         *  portSUPPRESS_TICKS_AND_SLEEP() is called, and resumed when
         *  portSUPPRESS_TICKS_AND_SLEEP() returns.  Therefore no other
         *  tasks will execute until this function completes.
         */
        for (i = 0; i < 3; i++) {
            count[i] = MAP_PRCMSlowClkCtrFastGet();
        }
        ullLowPowerTimeAfterSleep =
            COUNT_WITHIN_TRESHOLD(count[0], count[1], count[2], 1);

        ullSleepTime = ullLowPowerTimeAfterSleep - ullLowPowerTimeBeforeSleep;

        ullSleepTime = ullSleepTime*1000;
        ullSleepTime = ullSleepTime/32768;

        /*
         *  Correct the kernels tick count to account for the time the
         *  microcontroller spent in its low power state.
         */
        vTaskStepTick((unsigned long)ullSleepTime);

        /* Restart the timer that is generating the tick interrupt. */
        MAP_SysTickEnable();

        /*
         *  Exit the critical section - it might be possible to do this
         *  immediately after the prvSleep() calls.
         */
        vPortExitCritical();
    }
    else {
        MAP_PRCMSleepEnter();
    }
#endif
}

/*
 *  ======== PowerCC32XX_initPolicy ========
 */
void PowerCC32XX_initPolicy()
{
}

/* Tickless Hook */
void vPortSuppressTicksAndSleep(TickType_t xExpectedIdleTime)
{
#if (configUSE_TICKLESS_IDLE != 0)
    idleTime = xExpectedIdleTime;
    Power_idleFunc();
#endif
}
