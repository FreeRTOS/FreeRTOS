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

#ifndef __MCF52259_GPT_H__
#define __MCF52259_GPT_H__


/*********************************************************************
*
* General Purpose Timer Module (GPT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_GPT_GPTIOS                       (*(vuint8 *)(0x401A0000))
#define MCF_GPT_GPTCFORC                     (*(vuint8 *)(0x401A0001))
#define MCF_GPT_GPTOC3M                      (*(vuint8 *)(0x401A0002))
#define MCF_GPT_GPTOC3D                      (*(vuint8 *)(0x401A0003))
#define MCF_GPT_GPTCNT                       (*(vuint16*)(0x401A0004))
#define MCF_GPT_GPTSCR1                      (*(vuint8 *)(0x401A0006))
#define MCF_GPT_GPTTOV                       (*(vuint8 *)(0x401A0008))
#define MCF_GPT_GPTCTL1                      (*(vuint8 *)(0x401A0009))
#define MCF_GPT_GPTCTL2                      (*(vuint8 *)(0x401A000B))
#define MCF_GPT_GPTIE                        (*(vuint8 *)(0x401A000C))
#define MCF_GPT_GPTSCR2                      (*(vuint8 *)(0x401A000D))
#define MCF_GPT_GPTFLG1                      (*(vuint8 *)(0x401A000E))
#define MCF_GPT_GPTFLG2                      (*(vuint8 *)(0x401A000F))
#define MCF_GPT_GPTC0                        (*(vuint16*)(0x401A0010))
#define MCF_GPT_GPTC1                        (*(vuint16*)(0x401A0012))
#define MCF_GPT_GPTC2                        (*(vuint16*)(0x401A0014))
#define MCF_GPT_GPTC3                        (*(vuint16*)(0x401A0016))
#define MCF_GPT_GPTPACTL                     (*(vuint8 *)(0x401A0018))
#define MCF_GPT_GPTPAFLG                     (*(vuint8 *)(0x401A0019))
#define MCF_GPT_GPTPACNT                     (*(vuint16*)(0x401A001A))
#define MCF_GPT_GPTPORT                      (*(vuint8 *)(0x401A001D))
#define MCF_GPT_GPTDDR                       (*(vuint8 *)(0x401A001E))
#define MCF_GPT_GPTC(x)                      (*(vuint16*)(0x401A0010 + ((x)*0x2)))


/* Bit definitions and macros for MCF_GPT_GPTIOS */
#define MCF_GPT_GPTIOS_IOS0                  (0x1)
#define MCF_GPT_GPTIOS_IOS1                  (0x2)
#define MCF_GPT_GPTIOS_IOS2                  (0x4)
#define MCF_GPT_GPTIOS_IOS3                  (0x8)

/* Bit definitions and macros for MCF_GPT_GPTCFORC */
#define MCF_GPT_GPTCFORC_FOC0                (0x1)
#define MCF_GPT_GPTCFORC_FOC1                (0x2)
#define MCF_GPT_GPTCFORC_FOC2                (0x4)
#define MCF_GPT_GPTCFORC_FOC3                (0x8)

/* Bit definitions and macros for MCF_GPT_GPTOC3M */
#define MCF_GPT_GPTOC3M_OC3M0                (0x1)
#define MCF_GPT_GPTOC3M_OC3M1                (0x2)
#define MCF_GPT_GPTOC3M_OC3M2                (0x4)
#define MCF_GPT_GPTOC3M_OC3M3                (0x8)

/* Bit definitions and macros for MCF_GPT_GPTOC3D */
#define MCF_GPT_GPTOC3D_OC3D0                (0x1)
#define MCF_GPT_GPTOC3D_OC3D1                (0x2)
#define MCF_GPT_GPTOC3D_OC3D2                (0x4)
#define MCF_GPT_GPTOC3D_OC3D3                (0x8)

/* Bit definitions and macros for MCF_GPT_GPTCNT */
#define MCF_GPT_GPTCNT_CNTR(x)               (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_GPT_GPTSCR1 */
#define MCF_GPT_GPTSCR1_TFFCA                (0x10)
#define MCF_GPT_GPTSCR1_GPTEN                (0x80)

/* Bit definitions and macros for MCF_GPT_GPTTOV */
#define MCF_GPT_GPTTOV_TOV0                  (0x1)
#define MCF_GPT_GPTTOV_TOV1                  (0x2)
#define MCF_GPT_GPTTOV_TOV2                  (0x4)
#define MCF_GPT_GPTTOV_TOV3                  (0x8)

/* Bit definitions and macros for MCF_GPT_GPTCTL1 */
#define MCF_GPT_GPTCTL1_OL0                  (0x1)
#define MCF_GPT_GPTCTL1_OM0                  (0x2)
#define MCF_GPT_GPTCTL1_OL1                  (0x4)
#define MCF_GPT_GPTCTL1_OM1                  (0x8)
#define MCF_GPT_GPTCTL1_OL2                  (0x10)
#define MCF_GPT_GPTCTL1_OM2                  (0x20)
#define MCF_GPT_GPTCTL1_OL3                  (0x40)
#define MCF_GPT_GPTCTL1_OM3                  (0x80)
#define MCF_GPT_GPTCTL1_OUTPUT0_NOTHING      (0)
#define MCF_GPT_GPTCTL1_OUTPUT0_TOGGLE       (0x1)
#define MCF_GPT_GPTCTL1_OUTPUT0_CLEAR        (0x2)
#define MCF_GPT_GPTCTL1_OUTPUT0_SET          (0x3)
#define MCF_GPT_GPTCTL1_OUTPUT1_NOTHING      (0)
#define MCF_GPT_GPTCTL1_OUTPUT1_TOGGLE       (0x4)
#define MCF_GPT_GPTCTL1_OUTPUT1_CLEAR        (0x8)
#define MCF_GPT_GPTCTL1_OUTPUT1_SET          (0xC)
#define MCF_GPT_GPTCTL1_OUTPUT2_NOTHING      (0)
#define MCF_GPT_GPTCTL1_OUTPUT2_TOGGLE       (0x10)
#define MCF_GPT_GPTCTL1_OUTPUT2_CLEAR        (0x20)
#define MCF_GPT_GPTCTL1_OUTPUT2_SET          (0x30)
#define MCF_GPT_GPTCTL1_OUTPUT3_NOTHING      (0)
#define MCF_GPT_GPTCTL1_OUTPUT3_TOGGLE       (0x40)
#define MCF_GPT_GPTCTL1_OUTPUT3_CLEAR        (0x80)
#define MCF_GPT_GPTCTL1_OUTPUT3_SET          (0xC0)

/* Bit definitions and macros for MCF_GPT_GPTCTL2 */
#define MCF_GPT_GPTCTL2_EDG0A                (0x1)
#define MCF_GPT_GPTCTL2_EDG0B                (0x2)
#define MCF_GPT_GPTCTL2_EDG1A                (0x4)
#define MCF_GPT_GPTCTL2_EDG1B                (0x8)
#define MCF_GPT_GPTCTL2_EDG2A                (0x10)
#define MCF_GPT_GPTCTL2_EDG2B                (0x20)
#define MCF_GPT_GPTCTL2_EDG3A                (0x40)
#define MCF_GPT_GPTCTL2_EDG3B                (0x80)
#define MCF_GPT_GPTCTL2_INPUT0_DISABLED      (0)
#define MCF_GPT_GPTCTL2_INPUT0_RISING        (0x1)
#define MCF_GPT_GPTCTL2_INPUT0_FALLING       (0x2)
#define MCF_GPT_GPTCTL2_INPUT0_ANY           (0x3)
#define MCF_GPT_GPTCTL2_INPUT1_DISABLED      (0)
#define MCF_GPT_GPTCTL2_INPUT1_RISING        (0x4)
#define MCF_GPT_GPTCTL2_INPUT1_FALLING       (0x8)
#define MCF_GPT_GPTCTL2_INPUT1_ANY           (0xC)
#define MCF_GPT_GPTCTL2_INPUT2_DISABLED      (0)
#define MCF_GPT_GPTCTL2_INPUT2_RISING        (0x10)
#define MCF_GPT_GPTCTL2_INPUT2_FALLING       (0x20)
#define MCF_GPT_GPTCTL2_INPUT2_ANY           (0x30)
#define MCF_GPT_GPTCTL2_INPUT3_DISABLED      (0)
#define MCF_GPT_GPTCTL2_INPUT3_RISING        (0x40)
#define MCF_GPT_GPTCTL2_INPUT3_FALLING       (0x80)
#define MCF_GPT_GPTCTL2_INPUT3_ANY           (0xC0)

/* Bit definitions and macros for MCF_GPT_GPTIE */
#define MCF_GPT_GPTIE_CI0                    (0x1)
#define MCF_GPT_GPTIE_CI1                    (0x2)
#define MCF_GPT_GPTIE_CI2                    (0x4)
#define MCF_GPT_GPTIE_CI3                    (0x8)

/* Bit definitions and macros for MCF_GPT_GPTSCR2 */
#define MCF_GPT_GPTSCR2_PR(x)                (((x)&0x7)<<0)
#define MCF_GPT_GPTSCR2_PR_1                 (0)
#define MCF_GPT_GPTSCR2_PR_2                 (0x1)
#define MCF_GPT_GPTSCR2_PR_4                 (0x2)
#define MCF_GPT_GPTSCR2_PR_8                 (0x3)
#define MCF_GPT_GPTSCR2_PR_16                (0x4)
#define MCF_GPT_GPTSCR2_PR_32                (0x5)
#define MCF_GPT_GPTSCR2_PR_64                (0x6)
#define MCF_GPT_GPTSCR2_PR_128               (0x7)
#define MCF_GPT_GPTSCR2_TCRE                 (0x8)
#define MCF_GPT_GPTSCR2_RDPT                 (0x10)
#define MCF_GPT_GPTSCR2_PUPT                 (0x20)
#define MCF_GPT_GPTSCR2_TOI                  (0x80)

/* Bit definitions and macros for MCF_GPT_GPTFLG1 */
#define MCF_GPT_GPTFLG1_CF0                  (0x1)
#define MCF_GPT_GPTFLG1_CF1                  (0x2)
#define MCF_GPT_GPTFLG1_CF2                  (0x4)
#define MCF_GPT_GPTFLG1_CF3                  (0x8)

/* Bit definitions and macros for MCF_GPT_GPTFLG2 */
#define MCF_GPT_GPTFLG2_TOF                  (0x80)

/* Bit definitions and macros for MCF_GPT_GPTC */
#define MCF_GPT_GPTC_CCNT(x)                 (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_GPT_GPTPACTL */
#define MCF_GPT_GPTPACTL_PAI                 (0x1)
#define MCF_GPT_GPTPACTL_PAOVI               (0x2)
#define MCF_GPT_GPTPACTL_CLK(x)              (((x)&0x3)<<0x2)
#define MCF_GPT_GPTPACTL_CLK_GPTPR           (0)
#define MCF_GPT_GPTPACTL_CLK_PACLK           (0x1)
#define MCF_GPT_GPTPACTL_CLK_PACLK_256       (0x2)
#define MCF_GPT_GPTPACTL_CLK_PACLK_65536     (0x3)
#define MCF_GPT_GPTPACTL_PEDGE               (0x10)
#define MCF_GPT_GPTPACTL_PAMOD               (0x20)
#define MCF_GPT_GPTPACTL_PAE                 (0x40)

/* Bit definitions and macros for MCF_GPT_GPTPAFLG */
#define MCF_GPT_GPTPAFLG_PAIF                (0x1)
#define MCF_GPT_GPTPAFLG_PAOVF               (0x2)

/* Bit definitions and macros for MCF_GPT_GPTPACNT */
#define MCF_GPT_GPTPACNT_PACNT(x)            (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_GPT_GPTPORT */
#define MCF_GPT_GPTPORT_PORTT0               (0x1)
#define MCF_GPT_GPTPORT_PORTT1               (0x2)
#define MCF_GPT_GPTPORT_PORTT2               (0x4)
#define MCF_GPT_GPTPORT_PORTT3               (0x8)

/* Bit definitions and macros for MCF_GPT_GPTDDR */
#define MCF_GPT_GPTDDR_DDRT0                 (0x1)
#define MCF_GPT_GPTDDR_DDRT1                 (0x2)
#define MCF_GPT_GPTDDR_DDRT2                 (0x4)
#define MCF_GPT_GPTDDR_DDRT3                 (0x8)


#endif /* __MCF52259_GPT_H__ */
