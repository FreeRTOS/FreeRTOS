/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_PAD_H__
#define __MCF52235_PAD_H__


/*********************************************************************
*
* Common GPIO Registers
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PAD_PWOR                         (*(vuint16*)(&__IPSBAR[0x100078]))
#define MCF_PAD_PDSR1                        (*(vuint16*)(&__IPSBAR[0x10007A]))
#define MCF_PAD_PDSR0                        (*(vuint32*)(&__IPSBAR[0x10007C]))


/* Bit definitions and macros for MCF_PAD_PWOR */
#define MCF_PAD_PWOR_PWOR0                   (0x1)
#define MCF_PAD_PWOR_PWOR1                   (0x2)
#define MCF_PAD_PWOR_PWOR2                   (0x4)
#define MCF_PAD_PWOR_PWOR3                   (0x8)
#define MCF_PAD_PWOR_PWOR4                   (0x10)
#define MCF_PAD_PWOR_PWOR5                   (0x20)
#define MCF_PAD_PWOR_PWOR6                   (0x40)
#define MCF_PAD_PWOR_PWOR7                   (0x80)
#define MCF_PAD_PWOR_PWOR8                   (0x100)
#define MCF_PAD_PWOR_PWOR9                   (0x200)
#define MCF_PAD_PWOR_PWOR10                  (0x400)
#define MCF_PAD_PWOR_PWOR11                  (0x800)
#define MCF_PAD_PWOR_PWOR12                  (0x1000)
#define MCF_PAD_PWOR_PWOR13                  (0x2000)
#define MCF_PAD_PWOR_PWOR14                  (0x4000)
#define MCF_PAD_PWOR_PWOR15                  (0x8000)

/* Bit definitions and macros for MCF_PAD_PDSR1 */
#define MCF_PAD_PDSR1_PDSR32                 (0x1)
#define MCF_PAD_PDSR1_PDSR33                 (0x2)
#define MCF_PAD_PDSR1_PDSR34                 (0x4)
#define MCF_PAD_PDSR1_PDSR35                 (0x8)
#define MCF_PAD_PDSR1_PDSR36                 (0x10)
#define MCF_PAD_PDSR1_PDSR37                 (0x20)
#define MCF_PAD_PDSR1_PDSR38                 (0x40)
#define MCF_PAD_PDSR1_PDSR39                 (0x80)
#define MCF_PAD_PDSR1_PDSR40                 (0x100)
#define MCF_PAD_PDSR1_PDSR41                 (0x200)
#define MCF_PAD_PDSR1_PDSR42                 (0x400)
#define MCF_PAD_PDSR1_PDSR43                 (0x800)
#define MCF_PAD_PDSR1_PDSR44                 (0x1000)
#define MCF_PAD_PDSR1_PDSR45                 (0x2000)
#define MCF_PAD_PDSR1_PDSR46                 (0x4000)
#define MCF_PAD_PDSR1_PDSR47                 (0x8000)

/* Bit definitions and macros for MCF_PAD_PDSR0 */
#define MCF_PAD_PDSR0_PDSR0                  (0x1)
#define MCF_PAD_PDSR0_PDSR1                  (0x2)
#define MCF_PAD_PDSR0_PDSR2                  (0x4)
#define MCF_PAD_PDSR0_PDSR3                  (0x8)
#define MCF_PAD_PDSR0_PDSR4                  (0x10)
#define MCF_PAD_PDSR0_PDSR5                  (0x20)
#define MCF_PAD_PDSR0_PDSR6                  (0x40)
#define MCF_PAD_PDSR0_PDSR7                  (0x80)
#define MCF_PAD_PDSR0_PDSR8                  (0x100)
#define MCF_PAD_PDSR0_PDSR9                  (0x200)
#define MCF_PAD_PDSR0_PDSR10                 (0x400)
#define MCF_PAD_PDSR0_PDSR11                 (0x800)
#define MCF_PAD_PDSR0_PDSR12                 (0x1000)
#define MCF_PAD_PDSR0_PDSR13                 (0x2000)
#define MCF_PAD_PDSR0_PDSR14                 (0x4000)
#define MCF_PAD_PDSR0_PDSR15                 (0x8000)
#define MCF_PAD_PDSR0_PDSR16                 (0x10000)
#define MCF_PAD_PDSR0_PDSR17                 (0x20000)
#define MCF_PAD_PDSR0_PDSR18                 (0x40000)
#define MCF_PAD_PDSR0_PDSR19                 (0x80000)
#define MCF_PAD_PDSR0_PDSR20                 (0x100000)
#define MCF_PAD_PDSR0_PDSR21                 (0x200000)
#define MCF_PAD_PDSR0_PDSR22                 (0x400000)
#define MCF_PAD_PDSR0_PDSR23                 (0x800000)
#define MCF_PAD_PDSR0_PDSR24                 (0x1000000)
#define MCF_PAD_PDSR0_PDSR25                 (0x2000000)
#define MCF_PAD_PDSR0_PDSR26                 (0x4000000)
#define MCF_PAD_PDSR0_PDSR27                 (0x8000000)
#define MCF_PAD_PDSR0_PDSR28                 (0x10000000)
#define MCF_PAD_PDSR0_PDSR29                 (0x20000000)
#define MCF_PAD_PDSR0_PDSR30                 (0x40000000)
#define MCF_PAD_PDSR0_PDSR31                 (0x80000000)


#endif /* __MCF52235_PAD_H__ */
