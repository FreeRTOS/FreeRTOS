/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_PIT_H__
#define __MCF5282_PIT_H__


/*********************************************************************
*
* Programmable Interrupt Timer (PIT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PIT0_PCSR                        (*(vuint16*)(&__IPSBAR[0x150000]))
#define MCF_PIT0_PMR                         (*(vuint16*)(&__IPSBAR[0x150002]))
#define MCF_PIT0_PCNTR                       (*(vuint16*)(&__IPSBAR[0x150004]))

#define MCF_PIT1_PCSR                        (*(vuint16*)(&__IPSBAR[0x160000]))
#define MCF_PIT1_PMR                         (*(vuint16*)(&__IPSBAR[0x160002]))
#define MCF_PIT1_PCNTR                       (*(vuint16*)(&__IPSBAR[0x160004]))

#define MCF_PIT2_PCSR                        (*(vuint16*)(&__IPSBAR[0x170000]))
#define MCF_PIT2_PMR                         (*(vuint16*)(&__IPSBAR[0x170002]))
#define MCF_PIT2_PCNTR                       (*(vuint16*)(&__IPSBAR[0x170004]))

#define MCF_PIT3_PCSR                        (*(vuint16*)(&__IPSBAR[0x180000]))
#define MCF_PIT3_PMR                         (*(vuint16*)(&__IPSBAR[0x180002]))
#define MCF_PIT3_PCNTR                       (*(vuint16*)(&__IPSBAR[0x180004]))

#define MCF_PIT_PCSR(x)                      (*(vuint16*)(&__IPSBAR[0x150000 + ((x)*0x10000)]))
#define MCF_PIT_PMR(x)                       (*(vuint16*)(&__IPSBAR[0x150002 + ((x)*0x10000)]))
#define MCF_PIT_PCNTR(x)                     (*(vuint16*)(&__IPSBAR[0x150004 + ((x)*0x10000)]))


/* Bit definitions and macros for MCF_PIT_PCSR */
#define MCF_PIT_PCSR_EN                      (0x1)
#define MCF_PIT_PCSR_RLD                     (0x2)
#define MCF_PIT_PCSR_PIF                     (0x4)
#define MCF_PIT_PCSR_PIE                     (0x8)
#define MCF_PIT_PCSR_OVW                     (0x10)
#define MCF_PIT_PCSR_HALTED                  (0x20)
#define MCF_PIT_PCSR_DOZE                    (0x40)
#define MCF_PIT_PCSR_PRE(x)                  (((x)&0xF)<<0x8)

/* Bit definitions and macros for MCF_PIT_PMR */
#define MCF_PIT_PMR_PM(x)                    (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_PIT_PCNTR */
#define MCF_PIT_PCNTR_PC(x)                  (((x)&0xFFFF)<<0)


#endif /* __MCF5282_PIT_H__ */
