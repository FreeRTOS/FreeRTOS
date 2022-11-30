/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/04/17 Revision: 0.2
 *
 * (c) Copyright UNIS, spol. s r.o. 1997-2008
 * UNIS, spol. s r.o.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52259_PAD_H__
#define __MCF52259_PAD_H__


/*********************************************************************
*
* Common GPIO
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PAD_PSRR0                        (*(vuint32*)(0x40100078))
#define MCF_PAD_PDSR0                        (*(vuint32*)(0x4010007C))
#define MCF_PAD_PSRR1                        (*(vuint32*)(0x40100080))
#define MCF_PAD_PSRR2                        (*(vuint16*)(0x40100086))
#define MCF_PAD_PDSR1                        (*(vuint32*)(0x40100088))
#define MCF_PAD_PDSR2                        (*(vuint16*)(0x4010008E))


/* Bit definitions and macros for MCF_PAD_PSRR0 */
#define MCF_PAD_PSRR0_PSRR0                  (0x1)
#define MCF_PAD_PSRR0_PSRR1                  (0x2)
#define MCF_PAD_PSRR0_PSRR2                  (0x4)
#define MCF_PAD_PSRR0_PSRR3                  (0x8)
#define MCF_PAD_PSRR0_PSRR4                  (0x10)
#define MCF_PAD_PSRR0_PSRR5                  (0x20)
#define MCF_PAD_PSRR0_PSRR6                  (0x40)
#define MCF_PAD_PSRR0_PSRR7                  (0x80)
#define MCF_PAD_PSRR0_PSRR8                  (0x100)
#define MCF_PAD_PSRR0_PSRR9                  (0x200)
#define MCF_PAD_PSRR0_PSRR10                 (0x400)
#define MCF_PAD_PSRR0_PSRR11                 (0x800)
#define MCF_PAD_PSRR0_PSRR12                 (0x1000)
#define MCF_PAD_PSRR0_PSRR13                 (0x2000)
#define MCF_PAD_PSRR0_PSRR14                 (0x4000)
#define MCF_PAD_PSRR0_PSRR15                 (0x8000)
#define MCF_PAD_PSRR0_PSRR16                 (0x10000)
#define MCF_PAD_PSRR0_PSRR17                 (0x20000)
#define MCF_PAD_PSRR0_PSRR18                 (0x40000)
#define MCF_PAD_PSRR0_PSRR19                 (0x80000)
#define MCF_PAD_PSRR0_PSRR20                 (0x100000)
#define MCF_PAD_PSRR0_PSRR21                 (0x200000)
#define MCF_PAD_PSRR0_PSRR22                 (0x400000)
#define MCF_PAD_PSRR0_PSRR23                 (0x800000)
#define MCF_PAD_PSRR0_PSRR24                 (0x1000000)
#define MCF_PAD_PSRR0_PSRR25                 (0x2000000)
#define MCF_PAD_PSRR0_PSRR26                 (0x4000000)
#define MCF_PAD_PSRR0_PSRR27                 (0x8000000)
#define MCF_PAD_PSRR0_PSRR28                 (0x10000000)
#define MCF_PAD_PSRR0_PSRR29                 (0x20000000)
#define MCF_PAD_PSRR0_PSRR30                 (0x40000000)
#define MCF_PAD_PSRR0_PSRR31                 (0x80000000)

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

/* Bit definitions and macros for MCF_PAD_PSRR1 */
#define MCF_PAD_PSRR1_PSRR32                 (0x1)
#define MCF_PAD_PSRR1_PSRR33                 (0x2)
#define MCF_PAD_PSRR1_PSRR34                 (0x4)
#define MCF_PAD_PSRR1_PSRR35                 (0x8)
#define MCF_PAD_PSRR1_PSRR36                 (0x10)
#define MCF_PAD_PSRR1_PSRR37                 (0x20)
#define MCF_PAD_PSRR1_PSRR38                 (0x40)
#define MCF_PAD_PSRR1_PSRR39                 (0x80)
#define MCF_PAD_PSRR1_PSRR40                 (0x100)
#define MCF_PAD_PSRR1_PSRR41                 (0x200)
#define MCF_PAD_PSRR1_PSRR42                 (0x400)
#define MCF_PAD_PSRR1_PSRR43                 (0x800)
#define MCF_PAD_PSRR1_PSRR44                 (0x1000)
#define MCF_PAD_PSRR1_PSRR45                 (0x2000)
#define MCF_PAD_PSRR1_PSRR46                 (0x4000)
#define MCF_PAD_PSRR1_PSRR47                 (0x8000)
#define MCF_PAD_PSRR1_PSRR48                 (0x10000)
#define MCF_PAD_PSRR1_PSRR49                 (0x20000)
#define MCF_PAD_PSRR1_PSRR50                 (0x40000)
#define MCF_PAD_PSRR1_PSRR51                 (0x80000)
#define MCF_PAD_PSRR1_PSRR52                 (0x100000)
#define MCF_PAD_PSRR1_PSRR53                 (0x200000)
#define MCF_PAD_PSRR1_PSRR54                 (0x400000)
#define MCF_PAD_PSRR1_PSRR55                 (0x800000)
#define MCF_PAD_PSRR1_PSRR56                 (0x1000000)
#define MCF_PAD_PSRR1_PSRR57                 (0x2000000)
#define MCF_PAD_PSRR1_PSRR58                 (0x4000000)
#define MCF_PAD_PSRR1_PSRR59                 (0x8000000)
#define MCF_PAD_PSRR1_PSRR60                 (0x10000000)
#define MCF_PAD_PSRR1_PSRR61                 (0x20000000)
#define MCF_PAD_PSRR1_PSRR62                 (0x40000000)
#define MCF_PAD_PSRR1_PSRR63                 (0x80000000)

/* Bit definitions and macros for MCF_PAD_PSRR2 */
#define MCF_PAD_PSRR2_PSRR64                 (0x1)
#define MCF_PAD_PSRR2_PSRR65                 (0x2)
#define MCF_PAD_PSRR2_PSRR66                 (0x4)
#define MCF_PAD_PSRR2_PSRR67                 (0x8)
#define MCF_PAD_PSRR2_PSRR68                 (0x10)
#define MCF_PAD_PSRR2_PSRR69                 (0x20)
#define MCF_PAD_PSRR2_PSRR70                 (0x40)
#define MCF_PAD_PSRR2_PSRR71                 (0x80)
#define MCF_PAD_PSRR2_PSRR72                 (0x100)
#define MCF_PAD_PSRR2_PSRR73                 (0x200)
#define MCF_PAD_PSRR2_PSRR74                 (0x400)
#define MCF_PAD_PSRR2_PSRR75                 (0x800)
#define MCF_PAD_PSRR2_PSRR76                 (0x1000)
#define MCF_PAD_PSRR2_PSRR77                 (0x2000)
#define MCF_PAD_PSRR2_PSRR78                 (0x4000)
#define MCF_PAD_PSRR2_PSRR79                 (0x8000)

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
#define MCF_PAD_PDSR1_PDSR48                 (0x10000)
#define MCF_PAD_PDSR1_PDSR49                 (0x20000)
#define MCF_PAD_PDSR1_PDSR50                 (0x40000)
#define MCF_PAD_PDSR1_PDSR51                 (0x80000)
#define MCF_PAD_PDSR1_PDSR52                 (0x100000)
#define MCF_PAD_PDSR1_PDSR53                 (0x200000)
#define MCF_PAD_PDSR1_PDSR54                 (0x400000)
#define MCF_PAD_PDSR1_PDSR55                 (0x800000)
#define MCF_PAD_PDSR1_PDSR56                 (0x1000000)
#define MCF_PAD_PDSR1_PDSR57                 (0x2000000)
#define MCF_PAD_PDSR1_PDSR58                 (0x4000000)
#define MCF_PAD_PDSR1_PDSR59                 (0x8000000)
#define MCF_PAD_PDSR1_PDSR60                 (0x10000000)
#define MCF_PAD_PDSR1_PDSR61                 (0x20000000)
#define MCF_PAD_PDSR1_PDSR62                 (0x40000000)
#define MCF_PAD_PDSR1_PDSR63                 (0x80000000)

/* Bit definitions and macros for MCF_PAD_PDSR2 */
#define MCF_PAD_PDSR2_PDSR64                 (0x1)
#define MCF_PAD_PDSR2_PDSR65                 (0x2)
#define MCF_PAD_PDSR2_PDSR66                 (0x4)
#define MCF_PAD_PDSR2_PDSR67                 (0x8)
#define MCF_PAD_PDSR2_PDSR68                 (0x10)
#define MCF_PAD_PDSR2_PDSR69                 (0x20)
#define MCF_PAD_PDSR2_PDSR70                 (0x40)
#define MCF_PAD_PDSR2_PDSR71                 (0x80)
#define MCF_PAD_PDSR2_PDSR72                 (0x100)
#define MCF_PAD_PDSR2_PDSR73                 (0x200)
#define MCF_PAD_PDSR2_PDSR74                 (0x400)
#define MCF_PAD_PDSR2_PDSR75                 (0x800)
#define MCF_PAD_PDSR2_PDSR76                 (0x1000)
#define MCF_PAD_PDSR2_PDSR77                 (0x2000)
#define MCF_PAD_PDSR2_PDSR78                 (0x4000)
#define MCF_PAD_PDSR2_PDSR79                 (0x8000)


#endif /* __MCF52259_PAD_H__ */
