/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/05/23 Revision: 0.95
 *
 * (c) Copyright UNIS, a.s. 1997-2008
 * UNIS, a.s.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52221_PWM_H__
#define __MCF52221_PWM_H__


/*********************************************************************
*
* Pulse Width Modulation (PWM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PWM_PWME                         (*(vuint8 *)(0x401B0000))
#define MCF_PWM_PWMPOL                       (*(vuint8 *)(0x401B0001))
#define MCF_PWM_PWMCLK                       (*(vuint8 *)(0x401B0002))
#define MCF_PWM_PWMPRCLK                     (*(vuint8 *)(0x401B0003))
#define MCF_PWM_PWMCAE                       (*(vuint8 *)(0x401B0004))
#define MCF_PWM_PWMCTL                       (*(vuint8 *)(0x401B0005))
#define MCF_PWM_PWMSCLA                      (*(vuint8 *)(0x401B0008))
#define MCF_PWM_PWMSCLB                      (*(vuint8 *)(0x401B0009))
#define MCF_PWM_PWMCNT0                      (*(vuint8 *)(0x401B000C))
#define MCF_PWM_PWMCNT1                      (*(vuint8 *)(0x401B000D))
#define MCF_PWM_PWMCNT2                      (*(vuint8 *)(0x401B000E))
#define MCF_PWM_PWMCNT3                      (*(vuint8 *)(0x401B000F))
#define MCF_PWM_PWMCNT4                      (*(vuint8 *)(0x401B0010))
#define MCF_PWM_PWMCNT5                      (*(vuint8 *)(0x401B0011))
#define MCF_PWM_PWMCNT6                      (*(vuint8 *)(0x401B0012))
#define MCF_PWM_PWMCNT7                      (*(vuint8 *)(0x401B0013))
#define MCF_PWM_PWMPER0                      (*(vuint8 *)(0x401B0014))
#define MCF_PWM_PWMPER1                      (*(vuint8 *)(0x401B0015))
#define MCF_PWM_PWMPER2                      (*(vuint8 *)(0x401B0016))
#define MCF_PWM_PWMPER3                      (*(vuint8 *)(0x401B0017))
#define MCF_PWM_PWMPER4                      (*(vuint8 *)(0x401B0018))
#define MCF_PWM_PWMPER5                      (*(vuint8 *)(0x401B0019))
#define MCF_PWM_PWMPER6                      (*(vuint8 *)(0x401B001A))
#define MCF_PWM_PWMPER7                      (*(vuint8 *)(0x401B001B))
#define MCF_PWM_PWMDTY0                      (*(vuint8 *)(0x401B001C))
#define MCF_PWM_PWMDTY1                      (*(vuint8 *)(0x401B001D))
#define MCF_PWM_PWMDTY2                      (*(vuint8 *)(0x401B001E))
#define MCF_PWM_PWMDTY3                      (*(vuint8 *)(0x401B001F))
#define MCF_PWM_PWMDTY4                      (*(vuint8 *)(0x401B0020))
#define MCF_PWM_PWMDTY5                      (*(vuint8 *)(0x401B0021))
#define MCF_PWM_PWMDTY6                      (*(vuint8 *)(0x401B0022))
#define MCF_PWM_PWMDTY7                      (*(vuint8 *)(0x401B0023))
#define MCF_PWM_PWMSDN                       (*(vuint8 *)(0x401B0024))
#define MCF_PWM_PWMCNT(x)                    (*(vuint8 *)(0x401B000C + ((x)*0x1)))
#define MCF_PWM_PWMPER(x)                    (*(vuint8 *)(0x401B0014 + ((x)*0x1)))
#define MCF_PWM_PWMDTY(x)                    (*(vuint8 *)(0x401B001C + ((x)*0x1)))


/* Bit definitions and macros for MCF_PWM_PWME */
#define MCF_PWM_PWME_PWME0                   (0x1)
#define MCF_PWM_PWME_PWME1                   (0x2)
#define MCF_PWM_PWME_PWME2                   (0x4)
#define MCF_PWM_PWME_PWME3                   (0x8)
#define MCF_PWM_PWME_PWME4                   (0x10)
#define MCF_PWM_PWME_PWME5                   (0x20)
#define MCF_PWM_PWME_PWME6                   (0x40)
#define MCF_PWM_PWME_PWME7                   (0x80)

/* Bit definitions and macros for MCF_PWM_PWMPOL */
#define MCF_PWM_PWMPOL_PPOL0                 (0x1)
#define MCF_PWM_PWMPOL_PPOL1                 (0x2)
#define MCF_PWM_PWMPOL_PPOL2                 (0x4)
#define MCF_PWM_PWMPOL_PPOL3                 (0x8)
#define MCF_PWM_PWMPOL_PPOL4                 (0x10)
#define MCF_PWM_PWMPOL_PPOL5                 (0x20)
#define MCF_PWM_PWMPOL_PPOL6                 (0x40)
#define MCF_PWM_PWMPOL_PPOL7                 (0x80)

/* Bit definitions and macros for MCF_PWM_PWMCLK */
#define MCF_PWM_PWMCLK_PCLK0                 (0x1)
#define MCF_PWM_PWMCLK_PCLK1                 (0x2)
#define MCF_PWM_PWMCLK_PCLK2                 (0x4)
#define MCF_PWM_PWMCLK_PCLK3                 (0x8)
#define MCF_PWM_PWMCLK_PCLK4                 (0x10)
#define MCF_PWM_PWMCLK_PCLK5                 (0x20)
#define MCF_PWM_PWMCLK_PCLK6                 (0x40)
#define MCF_PWM_PWMCLK_PCLK7                 (0x80)

/* Bit definitions and macros for MCF_PWM_PWMPRCLK */
#define MCF_PWM_PWMPRCLK_PCKA(x)             (((x)&0x7)<<0)
#define MCF_PWM_PWMPRCLK_PCKB(x)             (((x)&0x7)<<0x4)

/* Bit definitions and macros for MCF_PWM_PWMCAE */
#define MCF_PWM_PWMCAE_CAE0                  (0x1)
#define MCF_PWM_PWMCAE_CAE1                  (0x2)
#define MCF_PWM_PWMCAE_CAE2                  (0x4)
#define MCF_PWM_PWMCAE_CAE3                  (0x8)
#define MCF_PWM_PWMCAE_CAE4                  (0x10)
#define MCF_PWM_PWMCAE_CAE5                  (0x20)
#define MCF_PWM_PWMCAE_CAE6                  (0x40)
#define MCF_PWM_PWMCAE_CAE7                  (0x80)

/* Bit definitions and macros for MCF_PWM_PWMCTL */
#define MCF_PWM_PWMCTL_PFRZ                  (0x4)
#define MCF_PWM_PWMCTL_PSWAI                 (0x8)
#define MCF_PWM_PWMCTL_CON01                 (0x10)
#define MCF_PWM_PWMCTL_CON23                 (0x20)
#define MCF_PWM_PWMCTL_CON45                 (0x40)
#define MCF_PWM_PWMCTL_CON67                 (0x80)

/* Bit definitions and macros for MCF_PWM_PWMSCLA */
#define MCF_PWM_PWMSCLA_SCALEA(x)            (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_PWM_PWMSCLB */
#define MCF_PWM_PWMSCLB_SCALEB(x)            (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_PWM_PWMCNT */
#define MCF_PWM_PWMCNT_COUNT(x)              (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_PWM_PWMPER */
#define MCF_PWM_PWMPER_PERIOD(x)             (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_PWM_PWMDTY */
#define MCF_PWM_PWMDTY_DUTY(x)               (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_PWM_PWMSDN */
#define MCF_PWM_PWMSDN_SDNEN                 (0x1)
#define MCF_PWM_PWMSDN_PWM7IL                (0x2)
#define MCF_PWM_PWMSDN_PWM7IN                (0x4)
#define MCF_PWM_PWMSDN_LVL                   (0x10)
#define MCF_PWM_PWMSDN_RESTART               (0x20)
#define MCF_PWM_PWMSDN_IE                    (0x40)
#define MCF_PWM_PWMSDN_IF                    (0x80)


#endif /* __MCF52221_PWM_H__ */
