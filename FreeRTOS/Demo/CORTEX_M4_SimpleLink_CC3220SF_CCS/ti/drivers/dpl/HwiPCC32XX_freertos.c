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
 *  ======== HwiP_freertos.c ========
 *  TODO is this the correct license?
 *
 *  Writing an RTOS safe ISR for FreeRTOS is very dependent on the
 *  microcontroller and tool chain port of FreeRTOS being used. Refer to
 *  the documentation page and demo application for the RTOS port being used.
 */

#include <stdbool.h>
#include <ti/drivers/dpl/HwiP.h>
#include <FreeRTOS.h>
#include <task.h>
#include <portmacro.h>

/* Driver lib includes */
#include <ti/devices/cc32xx/inc/hw_types.h>
#include <ti/devices/cc32xx/driverlib/interrupt.h>
#include <ti/devices/cc32xx/driverlib/rom.h>
#include <ti/devices/cc32xx/driverlib/rom_map.h>

#define MAX_INTERRUPTS 256


/* Masks off all bits but the VECTACTIVE bits in the ICSR register. */
#define portVECTACTIVE_MASK  (0xFFUL)

/*
 *  ======== HwiP_DispatchEntry ========
 */
typedef struct HwiP_DispatchEntry {
    HwiP_Fxn entry;
    uintptr_t arg;
} HwiP_DispatchEntry;

HwiP_DispatchEntry HwiP_dispatchTable[MAX_INTERRUPTS] = {{(HwiP_Fxn)0, 0}};

/*
 *  ======== HwiP_disable ========
 */
uintptr_t HwiP_disable(void)
{
    uintptr_t key;

    /*
     *  If we're not in ISR context, use the FreeRTOS macro, since
     *  it handles nesting.
     */
    if ((portNVIC_INT_CTRL_REG & portVECTACTIVE_MASK) == 0) {
        /* Cannot be called from an ISR! */
        portENTER_CRITICAL();
        key = 0;
    }
    else {
#ifdef __TI_COMPILER_VERSION__
        key = _set_interrupt_priority(configMAX_SYSCALL_INTERRUPT_PRIORITY);
#else
#if defined(__IAR_SYSTEMS_ICC__)
        asm volatile (
#else /* !__IAR_SYSTEMS_ICC__ */
            __asm__ __volatile__ (
#endif
                "mrs %0, basepri\n\t"
                "msr basepri, %1"
                : "=&r" (key)
                : "r" (configMAX_SYSCALL_INTERRUPT_PRIORITY)
                );
#endif
    }

    return (key);
}

/*
 *  ======== HwiP_restore ========
 */
void HwiP_restore(uintptr_t key)
{
    if ((portNVIC_INT_CTRL_REG & portVECTACTIVE_MASK) == 0) {
        /* Cannot be called from an ISR! */
        portEXIT_CRITICAL();
    }
    else {
#ifdef __TI_COMPILER_VERSION__
        _set_interrupt_priority(key);
#else
#if defined(__IAR_SYSTEMS_ICC__)
        asm volatile (
#else /* !__IAR_SYSTEMS_ICC__ */
            __asm__ __volatile__ (
#endif
                "msr basepri, %0"
                :: "r" (key)
                );
#endif
    }
}

#ifndef xdc_target__isaCompatible_28

typedef struct Hwi_NVIC {
    uint32_t RES_00;
    uint32_t ICTR;
    uint32_t RES_08;
    uint32_t RES_0C;
    uint32_t STCSR;
    uint32_t STRVR;
    uint32_t STCVR;
    uint32_t STCALIB;
    uint32_t RES_20[56];
    uint32_t ISER[8];
    uint32_t RES_120[24];
    uint32_t ICER[8];
    uint32_t RES_1A0[24];
    uint32_t ISPR[8];
    uint32_t RES_220[24];
    uint32_t ICPR[8];
    uint32_t RES_2A0[24];
    uint32_t IABR[8];
    uint32_t RES_320[56];
    uint8_t IPR[240];
    uint32_t RES_4F0[516];
    uint32_t CPUIDBR;
    uint32_t ICSR;
    uint32_t VTOR;
    uint32_t AIRCR;
    uint32_t SCR;
    uint32_t CCR;
    uint8_t SHPR[12];
    uint32_t SHCSR;
    uint8_t MMFSR;
    uint8_t BFSR;
    uint16_t UFSR;
    uint32_t HFSR;
    uint32_t DFSR;
    uint32_t MMAR;
    uint32_t BFAR;
    uint32_t AFSR;
    uint32_t PFR0;
    uint32_t PFR1;
    uint32_t DFR0;
    uint32_t AFR0;
    uint32_t MMFR0;
    uint32_t MMFR1;
    uint32_t MMFR2;
    uint32_t MMFR3;
    uint32_t ISAR0;
    uint32_t ISAR1;
    uint32_t ISAR2;
    uint32_t ISAR3;
    uint32_t ISAR4;
    uint32_t RES_D74[5];
    uint32_t CPACR;
    uint32_t RES_D8C[93];
    uint32_t STI;
    uint32_t RES_F04[12];
    uint32_t FPCCR;
    uint32_t FPCAR;
    uint32_t FPDSCR;
    uint32_t MVFR0;
    uint32_t MVFR1;
    uint32_t RES_F48[34];
    uint32_t PID4;
    uint32_t PID5;
    uint32_t PID6;
    uint32_t PID7;
    uint32_t PID0;
    uint32_t PID1;
    uint32_t PID2;
    uint32_t PID3;
    uint32_t CID0;
    uint32_t CID1;
    uint32_t CID2;
    uint32_t CID3;
} Hwi_NVIC;

/*
 *  ======== HwiP_clearInterrupt ========
 */
void HwiP_clearInterrupt(int interruptNum)
{
    // TODO: Should driverlib functions be prefixed with MAP_?
    IntPendClear((unsigned long)interruptNum);
}

/*
 *  ======== HwiP_delete ========
 */
HwiP_Status HwiP_delete(HwiP_Handle handle)
{
    IntDisable((int)handle);
    IntUnregister((int)handle);

    return (HwiP_OK);
}

/*
 *  ======== HwiP_disableInterrupt ========
 */
void HwiP_disableInterrupt(int interruptNum)
{
    IntDisable(interruptNum);
}

/*
 *  ======== HwiP_dispatch ========
 */
void HwiP_dispatch(void)
{
    uint32_t intNum;
    Hwi_NVIC *Hwi_nvic = (Hwi_NVIC *)0xE000E000;
    HwiP_DispatchEntry hwi;

    /* Determine which interrupt has fired */
    intNum = (Hwi_nvic->ICSR & 0x000000ff);
    hwi = HwiP_dispatchTable[intNum];
    if (hwi.entry) {
        (hwi.entry)(hwi.arg);
        taskYIELD();
    }
}

/*
 *  ======== HwiP_enableInterrupt ========
 */
void HwiP_enableInterrupt(int interruptNum)
{
    IntEnable(interruptNum);
}

/*
 *  ======== HwiP_create ========
 */
HwiP_Handle HwiP_create(int interruptNum,
                        HwiP_Fxn hwiFxn,
                        HwiP_Params *params)
{
    HwiP_Params defaultParams;

    if (params == NULL) {
        params = &defaultParams;
        HwiP_Params_init(&defaultParams);
    }

    HwiP_dispatchTable[interruptNum].entry = hwiFxn;
    HwiP_dispatchTable[interruptNum].arg = params->arg;

    // TODO: Should driverlib functions be prefixed with MAP_?
    IntRegister(interruptNum, (void(*)(void))HwiP_dispatch);
    IntPrioritySet(interruptNum, params->priority);
    IntEnable(interruptNum);

    return ((HwiP_Handle)interruptNum);
}

/*
 *  ======== HwiP_inISR ========
 */
bool HwiP_inISR(void)
{
    bool stat;

    if ((portNVIC_INT_CTRL_REG & portVECTACTIVE_MASK) == 0) {
        /* Not currently in an ISR */
        stat = false;
    }
    else {
        stat = true;
    }

    return (stat);
}

/*
 *  ======== HwiP_Params_init ========
 */
void HwiP_Params_init(HwiP_Params *params)
{
    params->name = NULL;
    params->arg = 0;
    params->priority = ~0;
}

#endif
