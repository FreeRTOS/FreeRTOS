/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_QADC_H__
#define __MCF5282_QADC_H__


/*********************************************************************
*
* Queued Analog-to-Digital Converter (QADC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_QADC_QADCMCR                     (*(vuint16*)(&__IPSBAR[0x190000]))
#define MCF_QADC_PORTQA                      (*(vuint8 *)(&__IPSBAR[0x190006]))
#define MCF_QADC_PORTQB                      (*(vuint8 *)(&__IPSBAR[0x190007]))
#define MCF_QADC_DDRQA                       (*(vuint8 *)(&__IPSBAR[0x190008]))
#define MCF_QADC_DDRQB                       (*(vuint8 *)(&__IPSBAR[0x190009]))
#define MCF_QADC_QACR0                       (*(vuint16*)(&__IPSBAR[0x19000A]))
#define MCF_QADC_QACR1                       (*(vuint16*)(&__IPSBAR[0x19000C]))
#define MCF_QADC_QACR2                       (*(vuint16*)(&__IPSBAR[0x19000E]))
#define MCF_QADC_QASR0                       (*(vuint16*)(&__IPSBAR[0x190010]))
#define MCF_QADC_QASR1                       (*(vuint16*)(&__IPSBAR[0x190012]))

/* Other macros */
#define MCF_QADC_CCW(x)                      (*(vuint16*)(&__IPSBAR[0x190200 + (x*2)]))
#define MCF_QADC_CCW_CHAN(x)                 (((x)&0x3F)<<0)
#define MCF_QADC_CCW_IST(x)                  (((x)&0x3)<<0x6)
#define MCF_QADC_CCW_IST_QCLK2               (0)
#define MCF_QADC_CCW_IST_QCLK4               (0x40)
#define MCF_QADC_CCW_IST_QCLK8               (0x80)
#define MCF_QADC_CCW_IST_QCLK16              (0xC0)
#define MCF_QADC_CCW_BYP                     (0x100)
#define MCF_QADC_CCW_P                       (0x200)
#define MCF_QADC_RJURR(x)                    (*(vuint16*)(&__IPSBAR[0x190280 + (x*2)]))
#define MCF_QADC_LJSRR(x)                    (*(vuint16*)(&__IPSBAR[0x190300 + (x*2)]))
#define MCF_QADC_LJURR(x)                    (*(vuint16*)(&__IPSBAR[0x190380 + (x*2)]))


/* Bit definitions and macros for MCF_QADC_QADCMCR */
#define MCF_QADC_QADCMCR_SUPV                (0x80)
#define MCF_QADC_QADCMCR_QDBG                (0x4000)
#define MCF_QADC_QADCMCR_QSTOP               (0x8000)

/* Bit definitions and macros for MCF_QADC_PORTQA */
#define MCF_QADC_PORTQA_PQA0                 (0x1)
#define MCF_QADC_PORTQA_PQA1                 (0x2)
#define MCF_QADC_PORTQA_PQA2                 (0x8)
#define MCF_QADC_PORTQA_PQA3                 (0x10)

/* Bit definitions and macros for MCF_QADC_PORTQB */
#define MCF_QADC_PORTQB_PQB0                 (0x1)
#define MCF_QADC_PORTQB_PQB1                 (0x2)
#define MCF_QADC_PORTQB_PQB2                 (0x4)
#define MCF_QADC_PORTQB_PQB3                 (0x8)

/* Bit definitions and macros for MCF_QADC_DDRQA */
#define MCF_QADC_DDRQA_DDQA0                 (0x1)
#define MCF_QADC_DDRQA_DDQA1                 (0x2)
#define MCF_QADC_DDRQA_DDQA2                 (0x8)
#define MCF_QADC_DDRQA_DDQA3                 (0x10)

/* Bit definitions and macros for MCF_QADC_DDRQB */
#define MCF_QADC_DDRQB_DDQB0                 (0x1)
#define MCF_QADC_DDRQB_DDQB1                 (0x2)
#define MCF_QADC_DDRQB_DDQB2                 (0x4)
#define MCF_QADC_DDRQB_DDQB3                 (0x8)

/* Bit definitions and macros for MCF_QADC_QACR0 */
#define MCF_QADC_QACR0_QPR(x)                (((x)&0x7F)<<0)
#define MCF_QADC_QACR0_TRG                   (0x1000)
#define MCF_QADC_QACR0_MUX                   (0x8000)

/* Bit definitions and macros for MCF_QADC_QACR1 */
#define MCF_QADC_QACR1_MQ1(x)                (((x)&0x1F)<<0x8)
#define MCF_QADC_QACR1_SSE1                  (0x2000)
#define MCF_QADC_QACR1_PIE1                  (0x4000)
#define MCF_QADC_QACR1_CIE1                  (0x8000)

/* Bit definitions and macros for MCF_QADC_QACR2 */
#define MCF_QADC_QACR2_BQ2(x)                (((x)&0x7F)<<0)
#define MCF_QADC_QACR2_RESUME                (0x80)
#define MCF_QADC_QACR2_MQ2(x)                (((x)&0x1F)<<0x8)
#define MCF_QADC_QACR2_SSE2                  (0x2000)
#define MCF_QADC_QACR2_PIE2                  (0x4000)
#define MCF_QADC_QACR2_CIE2                  (0x8000)

/* Bit definitions and macros for MCF_QADC_QASR0 */
#define MCF_QADC_QASR0_CWP(x)                (((x)&0x3F)<<0)
#define MCF_QADC_QASR0_QS(x)                 (((x)&0xF)<<0x6)
#define MCF_QADC_QASR0_TOR2                  (0x400)
#define MCF_QADC_QASR0_TOR1                  (0x800)
#define MCF_QADC_QASR0_PF2                   (0x1000)
#define MCF_QADC_QASR0_CF2                   (0x2000)
#define MCF_QADC_QASR0_PF1                   (0x4000)
#define MCF_QADC_QASR0_CF1                   (0x8000)

/* Bit definitions and macros for MCF_QADC_QASR1 */
#define MCF_QADC_QASR1_CWPQ2(x)              (((x)&0x3F)<<0)
#define MCF_QADC_QASR1_CWPQ1(x)              (((x)&0x3F)<<0x8)


#endif /* __MCF5282_QADC_H__ */
