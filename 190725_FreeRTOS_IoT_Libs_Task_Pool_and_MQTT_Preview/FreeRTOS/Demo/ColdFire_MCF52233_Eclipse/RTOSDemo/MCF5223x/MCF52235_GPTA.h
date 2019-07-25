/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_GPTA_H__
#define __MCF52235_GPTA_H__


/*********************************************************************
*
* General Purpose Timer Module (GPT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_GPTA_GPTIOS                      (*(vuint8 *)(&__IPSBAR[0x1A0000]))
#define MCF_GPTA_GPTCFORC                    (*(vuint8 *)(&__IPSBAR[0x1A0001]))
#define MCF_GPTA_GPTOC3M                     (*(vuint8 *)(&__IPSBAR[0x1A0002]))
#define MCF_GPTA_GPTOC3D                     (*(vuint8 *)(&__IPSBAR[0x1A0003]))
#define MCF_GPTA_GPTCNT                      (*(vuint16*)(&__IPSBAR[0x1A0004]))
#define MCF_GPTA_GPTSCR1                     (*(vuint8 *)(&__IPSBAR[0x1A0006]))
#define MCF_GPTA_GPTTOV                      (*(vuint8 *)(&__IPSBAR[0x1A0008]))
#define MCF_GPTA_GPTCTL1                     (*(vuint8 *)(&__IPSBAR[0x1A0009]))
#define MCF_GPTA_GPTCTL2                     (*(vuint8 *)(&__IPSBAR[0x1A000B]))
#define MCF_GPTA_GPTIE                       (*(vuint8 *)(&__IPSBAR[0x1A000C]))
#define MCF_GPTA_GPTSCR2                     (*(vuint8 *)(&__IPSBAR[0x1A000D]))
#define MCF_GPTA_GPTFLG1                     (*(vuint8 *)(&__IPSBAR[0x1A000E]))
#define MCF_GPTA_GPTFLG2                     (*(vuint8 *)(&__IPSBAR[0x1A000F]))
#define MCF_GPTA_GPTC0                       (*(vuint16*)(&__IPSBAR[0x1A0010]))
#define MCF_GPTA_GPTC1                       (*(vuint16*)(&__IPSBAR[0x1A0012]))
#define MCF_GPTA_GPTC2                       (*(vuint16*)(&__IPSBAR[0x1A0014]))
#define MCF_GPTA_GPTC3                       (*(vuint16*)(&__IPSBAR[0x1A0016]))
#define MCF_GPTA_GPTPACTL                    (*(vuint8 *)(&__IPSBAR[0x1A0018]))
#define MCF_GPTA_GPTPAFLG                    (*(vuint8 *)(&__IPSBAR[0x1A0019]))
#define MCF_GPTA_GPTPACNT                    (*(vuint16*)(&__IPSBAR[0x1A001A]))
#define MCF_GPTA_GPTPORT                     (*(vuint8 *)(&__IPSBAR[0x1A001D]))
#define MCF_GPTA_GPTDDR                      (*(vuint8 *)(&__IPSBAR[0x1A001E]))
#define MCF_GPTA_GPTC(x)                     (*(vuint16*)(&__IPSBAR[0x1A0010 + ((x)*0x2)]))


/* Bit definitions and macros for MCF_GPTA_GPTIOS */
#define MCF_GPTA_GPTIOS_IOS0                 (0x1)
#define MCF_GPTA_GPTIOS_IOS1                 (0x2)
#define MCF_GPTA_GPTIOS_IOS2                 (0x4)
#define MCF_GPTA_GPTIOS_IOS3                 (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTCFORC */
#define MCF_GPTA_GPTCFORC_FOC0               (0x1)
#define MCF_GPTA_GPTCFORC_FOC1               (0x2)
#define MCF_GPTA_GPTCFORC_FOC2               (0x4)
#define MCF_GPTA_GPTCFORC_FOC3               (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTOC3M */
#define MCF_GPTA_GPTOC3M_OC3M0               (0x1)
#define MCF_GPTA_GPTOC3M_OC3M1               (0x2)
#define MCF_GPTA_GPTOC3M_OC3M2               (0x4)
#define MCF_GPTA_GPTOC3M_OC3M3               (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTOC3D */
#define MCF_GPTA_GPTOC3D_OC3D0               (0x1)
#define MCF_GPTA_GPTOC3D_OC3D1               (0x2)
#define MCF_GPTA_GPTOC3D_OC3D2               (0x4)
#define MCF_GPTA_GPTOC3D_OC3D3               (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTCNT */
#define MCF_GPTA_GPTCNT_CNTR(x)              (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_GPTA_GPTSCR1 */
#define MCF_GPTA_GPTSCR1_TFFCA               (0x10)
#define MCF_GPTA_GPTSCR1_GPTEN               (0x80)

/* Bit definitions and macros for MCF_GPTA_GPTTOV */
#define MCF_GPTA_GPTTOV_TOV0                 (0x1)
#define MCF_GPTA_GPTTOV_TOV1                 (0x2)
#define MCF_GPTA_GPTTOV_TOV2                 (0x4)
#define MCF_GPTA_GPTTOV_TOV3                 (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTCTL1 */
#define MCF_GPTA_GPTCTL1_OL0                 (0x1)
#define MCF_GPTA_GPTCTL1_OM0                 (0x2)
#define MCF_GPTA_GPTCTL1_OL1                 (0x4)
#define MCF_GPTA_GPTCTL1_OM1                 (0x8)
#define MCF_GPTA_GPTCTL1_OL2                 (0x10)
#define MCF_GPTA_GPTCTL1_OM2                 (0x20)
#define MCF_GPTA_GPTCTL1_OL3                 (0x40)
#define MCF_GPTA_GPTCTL1_OM3                 (0x80)
#define MCF_GPTA_GPTCTL1_OUTPUT0_NOTHING     (0)
#define MCF_GPTA_GPTCTL1_OUTPUT0_TOGGLE      (0x1)
#define MCF_GPTA_GPTCTL1_OUTPUT0_CLEAR       (0x2)
#define MCF_GPTA_GPTCTL1_OUTPUT0_SET         (0x3)
#define MCF_GPTA_GPTCTL1_OUTPUT1_NOTHING     (0)
#define MCF_GPTA_GPTCTL1_OUTPUT1_TOGGLE      (0x4)
#define MCF_GPTA_GPTCTL1_OUTPUT1_CLEAR       (0x8)
#define MCF_GPTA_GPTCTL1_OUTPUT1_SET         (0xC)
#define MCF_GPTA_GPTCTL1_OUTPUT2_NOTHING     (0)
#define MCF_GPTA_GPTCTL1_OUTPUT2_TOGGLE      (0x10)
#define MCF_GPTA_GPTCTL1_OUTPUT2_CLEAR       (0x20)
#define MCF_GPTA_GPTCTL1_OUTPUT2_SET         (0x30)
#define MCF_GPTA_GPTCTL1_OUTPUT3_NOTHING     (0)
#define MCF_GPTA_GPTCTL1_OUTPUT3_TOGGLE      (0x40)
#define MCF_GPTA_GPTCTL1_OUTPUT3_CLEAR       (0x80)
#define MCF_GPTA_GPTCTL1_OUTPUT3_SET         (0xC0)

/* Bit definitions and macros for MCF_GPTA_GPTCTL2 */
#define MCF_GPTA_GPTCTL2_EDG0A               (0x1)
#define MCF_GPTA_GPTCTL2_EDG0B               (0x2)
#define MCF_GPTA_GPTCTL2_EDG1A               (0x4)
#define MCF_GPTA_GPTCTL2_EDG1B               (0x8)
#define MCF_GPTA_GPTCTL2_EDG2A               (0x10)
#define MCF_GPTA_GPTCTL2_EDG2B               (0x20)
#define MCF_GPTA_GPTCTL2_EDG3A               (0x40)
#define MCF_GPTA_GPTCTL2_EDG3B               (0x80)
#define MCF_GPTA_GPTCTL2_INPUT0_DISABLED     (0)
#define MCF_GPTA_GPTCTL2_INPUT0_RISING       (0x1)
#define MCF_GPTA_GPTCTL2_INPUT0_FALLING      (0x2)
#define MCF_GPTA_GPTCTL2_INPUT0_ANY          (0x3)
#define MCF_GPTA_GPTCTL2_INPUT1_DISABLED     (0)
#define MCF_GPTA_GPTCTL2_INPUT1_RISING       (0x4)
#define MCF_GPTA_GPTCTL2_INPUT1_FALLING      (0x8)
#define MCF_GPTA_GPTCTL2_INPUT1_ANY          (0xC)
#define MCF_GPTA_GPTCTL2_INPUT2_DISABLED     (0)
#define MCF_GPTA_GPTCTL2_INPUT2_RISING       (0x10)
#define MCF_GPTA_GPTCTL2_INPUT2_FALLING      (0x20)
#define MCF_GPTA_GPTCTL2_INPUT2_ANY          (0x30)
#define MCF_GPTA_GPTCTL2_INPUT3_DISABLED     (0)
#define MCF_GPTA_GPTCTL2_INPUT3_RISING       (0x40)
#define MCF_GPTA_GPTCTL2_INPUT3_FALLING      (0x80)
#define MCF_GPTA_GPTCTL2_INPUT3_ANY          (0xC0)

/* Bit definitions and macros for MCF_GPTA_GPTIE */
#define MCF_GPTA_GPTIE_CI0                   (0x1)
#define MCF_GPTA_GPTIE_CI1                   (0x2)
#define MCF_GPTA_GPTIE_CI2                   (0x4)
#define MCF_GPTA_GPTIE_CI3                   (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTSCR2 */
#define MCF_GPTA_GPTSCR2_PR(x)               (((x)&0x7)<<0)
#define MCF_GPTA_GPTSCR2_PR_1                (0)
#define MCF_GPTA_GPTSCR2_PR_2                (0x1)
#define MCF_GPTA_GPTSCR2_PR_4                (0x2)
#define MCF_GPTA_GPTSCR2_PR_8                (0x3)
#define MCF_GPTA_GPTSCR2_PR_16               (0x4)
#define MCF_GPTA_GPTSCR2_PR_32               (0x5)
#define MCF_GPTA_GPTSCR2_PR_64               (0x6)
#define MCF_GPTA_GPTSCR2_PR_128              (0x7)
#define MCF_GPTA_GPTSCR2_TCRE                (0x8)
#define MCF_GPTA_GPTSCR2_RDPT                (0x10)
#define MCF_GPTA_GPTSCR2_PUPT                (0x20)
#define MCF_GPTA_GPTSCR2_TOI                 (0x80)

/* Bit definitions and macros for MCF_GPTA_GPTFLG1 */
#define MCF_GPTA_GPTFLG1_CF0                 (0x1)
#define MCF_GPTA_GPTFLG1_CF1                 (0x2)
#define MCF_GPTA_GPTFLG1_CF2                 (0x4)
#define MCF_GPTA_GPTFLG1_CF3                 (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTFLG2 */
#define MCF_GPTA_GPTFLG2_TOF                 (0x80)

/* Bit definitions and macros for MCF_GPTA_GPTC */
#define MCF_GPTA_GPTC_CCNT(x)                (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_GPTA_GPTPACTL */
#define MCF_GPTA_GPTPACTL_PAI                (0x1)
#define MCF_GPTA_GPTPACTL_PAOVI              (0x2)
#define MCF_GPTA_GPTPACTL_CLK(x)             (((x)&0x3)<<0x2)
#define MCF_GPTA_GPTPACTL_CLK_GPTPR          (0)
#define MCF_GPTA_GPTPACTL_CLK_PACLK          (0x1)
#define MCF_GPTA_GPTPACTL_CLK_PACLK_256      (0x2)
#define MCF_GPTA_GPTPACTL_CLK_PACLK_65536    (0x3)
#define MCF_GPTA_GPTPACTL_PEDGE              (0x10)
#define MCF_GPTA_GPTPACTL_PAMOD              (0x20)
#define MCF_GPTA_GPTPACTL_PAE                (0x40)

/* Bit definitions and macros for MCF_GPTA_GPTPAFLG */
#define MCF_GPTA_GPTPAFLG_PAIF               (0x1)
#define MCF_GPTA_GPTPAFLG_PAOVF              (0x2)

/* Bit definitions and macros for MCF_GPTA_GPTPACNT */
#define MCF_GPTA_GPTPACNT_PACNT(x)           (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_GPTA_GPTPORT */
#define MCF_GPTA_GPTPORT_PORTT0              (0x1)
#define MCF_GPTA_GPTPORT_PORTT1              (0x2)
#define MCF_GPTA_GPTPORT_PORTT2              (0x4)
#define MCF_GPTA_GPTPORT_PORTT3              (0x8)

/* Bit definitions and macros for MCF_GPTA_GPTDDR */
#define MCF_GPTA_GPTDDR_DDRT0                (0x1)
#define MCF_GPTA_GPTDDR_DDRT1                (0x2)
#define MCF_GPTA_GPTDDR_DDRT2                (0x4)
#define MCF_GPTA_GPTDDR_DDRT3                (0x8)


#endif /* __MCF52235_GPTA_H__ */
