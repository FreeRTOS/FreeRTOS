/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <coretim.h>


void trap(void)
{
    __asm__ __volatile__(
        "bkpt\n"
    );
}

void vectorirq_handler(void)
{
    __asm__ __volatile__(
        "bkpt\n"
    );
}

__attribute__((naked)) void CKTimer1Isr(void)
{
    __asm__ __volatile__(
        "nie   \n"
        "subi    sp, 0x4   \n"
        "stw     lr, (sp, 0x0) \n"
        "ipush \n"

        "subi    sp, 32    \n"
        "stm     r4-r11, (sp)  \n"

        "lrw    r3, pxCurrentTCB    \n"     // save current SP
        "ld.w   r4, (r3)    \n"
        "st.w   sp, (r4)    \n"

        "jbsr   coretim_clr_irq \n"
        "jbsr   xPortSysTickHandler \n"

        "ldm     r4-r11, (sp)   \n"
        "addi    sp, 32 \n"

        "ipop   \n"
        "ldw     lr, (sp, 0x0)  \n"
        "addi    sp, 0x4    \n"
        "nir    \n"
        );
}

__attribute__((naked)) void CKPendSVIsr(void)
{
    __asm__ __volatile__ (
    "subi    sp, 36 \n"
    "stm     r0-r3, (sp)    \n"
    "stw     r12, (sp, 16)  \n"
    "stw     r13, (sp, 20)  \n"
    "stw     r15, (sp, 24)  \n"
    "mfcr    r1, epsr   \n"
    "stw     r1, (sp, 28)   \n"
    "mfcr    r1, epc    \n"
    "addi    r1, 4  \n"
    "stw     r1, (sp, 32)  \n"

    "subi    sp, sp, 32 \n"
    "stm     r4-r11, (sp)   \n"

    "lrw    r2, pxCurrentTCB    \n"         // Save the current task SP in the TCB
    "ld.w   r3, (r2)    \n"
    "st.w   sp, (r3)    \n"

    "jbsr   vTaskSwitchContext  \n"

    "lrw    r4, pxCurrentTCB    \n"
    "ld.w   r4, (r4)    \n"                 // the current task stack pointer is the first member
    "ld.w   sp, (r4)    \n"

    "ldm    r4-r11, (sp)   \n"
    "addi   sp, sp, 32 \n"

    "ldw    r12, (sp, 16)  \n"
    "ldw    r13, (sp, 20)  \n"
    "ldw    r15, (sp, 24)  \n"
    "ldw    r1, (sp, 28)   \n"
    "mtcr   r1, epsr   \n"
    "ldw    r1, (sp, 32)   \n"
    "mtcr   r1, epc    \n"
    "ldm    r0-r3, (sp)    \n"
    "addi   sp, 36 \n"

    "rte    \n"
    );

}


