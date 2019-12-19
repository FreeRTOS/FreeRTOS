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
#ifndef __INCLUDE_HOBBIT_IRQ_H
#define __INCLUDE_HOBBIT_IRQ_H

/****************************************************************************************************
 * Included Files
 ****************************************************************************************************/


/****************************************************************************************************
 * Pre-processor Definitions
 ****************************************************************************************************/

/* IRQ numbers.  The IRQ number corresponds vector number and hence map directly to
 * bits in the NVIC.  This does, however, waste several words of memory in the IRQ
 * to handle mapping tables.
 *
 *
 * External interrupts (vectors >= 16)
 */

#define NR_IRQS               32

#define  VIC_IPR_VALIDBIT     0x00000003
#define  VIC_IRQ_MAXNUM       0x0000001F
/* define irq numbers */
#define PIC_IRQ_BASE                    0

#define PIC_IRQ_GPIO                    (PIC_IRQ_BASE+0)
#define PIC_IRQ_CORETIM                 (PIC_IRQ_BASE+1)
#define PIC_IRQ_TIMER0                  (PIC_IRQ_BASE+2)
#define PIC_IRQ_TIMER1                  (PIC_IRQ_BASE+3)
#define PIC_IRQ_I2S                     (PIC_IRQ_BASE+4)
#define PIC_IRQ_WDT                     (PIC_IRQ_BASE+5)
#define PIC_IRQ_UART1                   (PIC_IRQ_BASE+6)
#define PIC_IRQ_UART2                   (PIC_IRQ_BASE+7)
#define PIC_IRQ_UART3                   (PIC_IRQ_BASE+8)
#define PIC_IRQ_I2C0                    (PIC_IRQ_BASE+9)
#define PIC_IRQ_I2C1                    (PIC_IRQ_BASE+10)
#define PIC_IRQ_SPI0                    (PIC_IRQ_BASE+11)
#define PIC_IRQ_SPI1                    (PIC_IRQ_BASE+12)
#define PIC_IRQ_RTC                     (PIC_IRQ_BASE+13)
#define PIC_IRQ_EXTWAKEUP               (PIC_IRQ_BASE+14)
#define PIC_IRQ_ADC                     (PIC_IRQ_BASE+15)
#define PIC_IRQ_CMP                     (PIC_IRQ_BASE+16)
#define PIC_IRQ_SEUDMAC                 (PIC_IRQ_BASE+17)
#define PIC_IRQ_POWM                    (PIC_IRQ_BASE+18)
#define PIC_IRQ_PWM                     (PIC_IRQ_BASE+19)
#define PIC_IRQ_SYSRESET                (PIC_IRQ_BASE+20)
#define PIC_IRQ_REV                     (PIC_IRQ_BASE+21)
#define PIC_IRQ_NONUSEDMAC              (PIC_IRQ_BASE+22)
#define PIC_IRQ_TIMER2                  (PIC_IRQ_BASE+23)
#define PIC_IRQ_TIMER3                  (PIC_IRQ_BASE+24)
#define PIC_IRQ_RTC1                    (PIC_IRQ_BASE+24)
#define PIC_IRQ_AES                     (PIC_IRQ_BASE+26)
#define PIC_IRQ_TRNG                    (PIC_IRQ_BASE+27)
#define PIC_IRQ_RSA                     (PIC_IRQ_BASE+28)
#define PIC_IRQ_SHA                     (PIC_IRQ_BASE+29)

/* define vic resesters */
#define  HOBBIT_VIC_BASE 0xE000E100

#define  VIC_ISER 0x0000
#define  VIC_IWER 0x0040
#define  VIC_ICER 0x0080
#define  VIC_IWDR 0x00C0
#define  VIC_ISPR 0x0100
#define  VIC_ICPR 0x0180
#define  VIC_IABR 0x0200
#define  VIC_IPR0 0x0300
#define  VIC_IPR1 0x0304
#define  VIC_IPR2 0x0308
#define  VIC_IPR3 0x030C
#define  VIC_IPR4 0x0310
#define  VIC_IPR5 0x0314
#define  VIC_IPR6 0x0318
#define  VIC_IPR7 0x031C
#define  VIC_ISR  0x0B00
#define  VIC_IPTR 0x0B04

#define HOBBIT_VIC_ISER   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_ISER))
#define HOBBIT_VIC_IWER   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IWER))
#define HOBBIT_VIC_ICER   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_ICER))
#define HOBBIT_VIC_IWDR   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IWDR))
#define HOBBIT_VIC_ISPR   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_ISPR))
#define HOBBIT_VIC_ICPR   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_ICPR))
#define HOBBIT_VIC_IABR   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IABR))
#define HOBBIT_VIC_IPR0   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR0))
#define HOBBIT_VIC_IPR1   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR1))
#define HOBBIT_VIC_IPR2   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR2))
#define HOBBIT_VIC_IPR3   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR3))
#define HOBBIT_VIC_IPR4   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR4))
#define HOBBIT_VIC_IPR5   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR5))
#define HOBBIT_VIC_IPR6   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR6))
#define HOBBIT_VIC_IPR7   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPR7))
#define HOBBIT_VIC_ISR    (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_ISR))
#define HOBBIT_VIC_IPTR   (*(volatile unsigned int *)( HOBBIT_VIC_BASE + VIC_IPTR))

/* define vic priority ,smaller priority number higher priority level */
#define PRIORITY_LEVEL1                 0
#define PRIORITY_LEVEL2                 1
#define PRIORITY_LEVEL3                 2
#define PRIORITY_LEVEL4                 3

/****************************************************************************************************
 * Public Types
 ****************************************************************************************************/

/****************************************************************************************************
 * Public Data
 ****************************************************************************************************/

#ifndef __ASSEMBLY__
#ifdef __cplusplus
#define EXTERN extern "C"
extern "C"
{
#else
#define EXTERN extern
#endif

/****************************************************************************************************
 * Public Functions
 ****************************************************************************************************/

#undef EXTERN
#ifdef __cplusplus
}
#endif
#endif

#endif /* __INCLUDE_HOBBIT_IRQ_H */

