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

#ifndef __MCF52221_RTC_H__
#define __MCF52221_RTC_H__


/*********************************************************************
*
* Real-Time Clock (RTC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_RTC_HOURMIN                      (*(vuint32*)(0x400003C0))
#define MCF_RTC_SECONDS                      (*(vuint32*)(0x400003C4))
#define MCF_RTC_ALRM_HM                      (*(vuint32*)(0x400003C8))
#define MCF_RTC_ALRM_SEC                     (*(vuint32*)(0x400003CC))
#define MCF_RTC_RTCCTL                       (*(vuint32*)(0x400003D0))
#define MCF_RTC_RTCISR                       (*(vuint32*)(0x400003D4))
#define MCF_RTC_RTCIENR                      (*(vuint32*)(0x400003D8))
#define MCF_RTC_STPWCH                       (*(vuint32*)(0x400003DC))
#define MCF_RTC_DAYS                         (*(vuint32*)(0x400003E0))
#define MCF_RTC_ALRM_DAY                     (*(vuint32*)(0x400003E4))


/* Bit definitions and macros for MCF_RTC_HOURMIN */
#define MCF_RTC_HOURMIN_MINUTES(x)           (((x)&0x3F)<<0)
#define MCF_RTC_HOURMIN_HOURS(x)             (((x)&0x1F)<<0x8)

/* Bit definitions and macros for MCF_RTC_SECONDS */
#define MCF_RTC_SECONDS_SECONDS(x)           (((x)&0x3F)<<0)

/* Bit definitions and macros for MCF_RTC_ALRM_HM */
#define MCF_RTC_ALRM_HM_MINUTES(x)           (((x)&0x3F)<<0)
#define MCF_RTC_ALRM_HM_HOURS(x)             (((x)&0x1F)<<0x8)

/* Bit definitions and macros for MCF_RTC_ALRM_SEC */
#define MCF_RTC_ALRM_SEC_SECONDS(x)          (((x)&0x3F)<<0)

/* Bit definitions and macros for MCF_RTC_RTCCTL */
#define MCF_RTC_RTCCTL_SWR                   (0x1)
#define MCF_RTC_RTCCTL_EN                    (0x80)

/* Bit definitions and macros for MCF_RTC_RTCISR */
#define MCF_RTC_RTCISR_SW                    (0x1)
#define MCF_RTC_RTCISR_MIN                   (0x2)
#define MCF_RTC_RTCISR_ALM                   (0x4)
#define MCF_RTC_RTCISR_DAY                   (0x8)
#define MCF_RTC_RTCISR_1HZ                   (0x10)
#define MCF_RTC_RTCISR_HR                    (0x20)

/* Bit definitions and macros for MCF_RTC_RTCIENR */
#define MCF_RTC_RTCIENR_SW                   (0x1)
#define MCF_RTC_RTCIENR_MIN                  (0x2)
#define MCF_RTC_RTCIENR_ALM                  (0x4)
#define MCF_RTC_RTCIENR_DAY                  (0x8)
#define MCF_RTC_RTCIENR_1HZ                  (0x10)
#define MCF_RTC_RTCIENR_HR                   (0x20)

/* Bit definitions and macros for MCF_RTC_STPWCH */
#define MCF_RTC_STPWCH_CNT(x)                (((x)&0x3F)<<0)

/* Bit definitions and macros for MCF_RTC_DAYS */
#define MCF_RTC_DAYS_DAYS(x)                 (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_RTC_ALRM_DAY */
#define MCF_RTC_ALRM_DAY_DAYSAL(x)           (((x)&0xFFFF)<<0)


#endif /* __MCF52221_RTC_H__ */
