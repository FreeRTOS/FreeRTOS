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

#ifndef __MCF52259_RTC_H__
#define __MCF52259_RTC_H__


/*********************************************************************
*
* Real-Time Clock (RTC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_RTC_HOURMIN                      (*(vuint32*)(0x40180000))
#define MCF_RTC_SECONDS                      (*(vuint32*)(0x40180004))
#define MCF_RTC_ALRM_HM                      (*(vuint32*)(0x40180008))
#define MCF_RTC_ALRM_SEC                     (*(vuint32*)(0x4018000C))
#define MCF_RTC_RTCCTL                       (*(vuint32*)(0x40180010))
#define MCF_RTC_RTCISR                       (*(vuint32*)(0x40180014))
#define MCF_RTC_RTCIENR                      (*(vuint32*)(0x40180018))
#define MCF_RTC_STPWCH                       (*(vuint32*)(0x4018001C))
#define MCF_RTC_DAYS                         (*(vuint32*)(0x40180020))
#define MCF_RTC_ALRM_DAY                     (*(vuint32*)(0x40180024))
#define MCF_RTC_RTCGOCU                      (*(vuint32*)(0x40180034))
#define MCF_RTC_RTCGOCL                      (*(vuint32*)(0x40180038))


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

/* Bit definitions and macros for MCF_RTC_RTCGOCU */
#define MCF_RTC_RTCGOCU_RTCGOCNT(x)          (((x)&0xFFFF)<<0)

/* Bit definitions and macros for MCF_RTC_RTCGOCL */
#define MCF_RTC_RTCGOCL_RTCGOCNT(x)          (((x)&0xFFFF)<<0)


#endif /* __MCF52259_RTC_H__ */
