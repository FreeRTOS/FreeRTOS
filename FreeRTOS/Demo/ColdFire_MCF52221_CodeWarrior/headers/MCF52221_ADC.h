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

#ifndef __MCF52221_ADC_H__
#define __MCF52221_ADC_H__


/*********************************************************************
*
* Analog-to-Digital Converter (ADC)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_ADC_CTRL1                        (*(vuint16*)(0x40190000))
#define MCF_ADC_CTRL2                        (*(vuint16*)(0x40190002))
#define MCF_ADC_ADZCC                        (*(vuint16*)(0x40190004))
#define MCF_ADC_ADLST1                       (*(vuint16*)(0x40190006))
#define MCF_ADC_ADLST2                       (*(vuint16*)(0x40190008))
#define MCF_ADC_ADSDIS                       (*(vuint16*)(0x4019000A))
#define MCF_ADC_ADSTAT                       (*(vuint16*)(0x4019000C))
#define MCF_ADC_ADLSTAT                      (*(vuint16*)(0x4019000E))
#define MCF_ADC_ADZCSTAT                     (*(vuint16*)(0x40190010))
#define MCF_ADC_ADRSLT0                      (*(vuint16*)(0x40190012))
#define MCF_ADC_ADRSLT1                      (*(vuint16*)(0x40190014))
#define MCF_ADC_ADRSLT2                      (*(vuint16*)(0x40190016))
#define MCF_ADC_ADRSLT3                      (*(vuint16*)(0x40190018))
#define MCF_ADC_ADRSLT4                      (*(vuint16*)(0x4019001A))
#define MCF_ADC_ADRSLT5                      (*(vuint16*)(0x4019001C))
#define MCF_ADC_ADRSLT6                      (*(vuint16*)(0x4019001E))
#define MCF_ADC_ADRSLT7                      (*(vuint16*)(0x40190020))
#define MCF_ADC_ADLLMT0                      (*(vuint16*)(0x40190022))
#define MCF_ADC_ADLLMT1                      (*(vuint16*)(0x40190024))
#define MCF_ADC_ADLLMT2                      (*(vuint16*)(0x40190026))
#define MCF_ADC_ADLLMT3                      (*(vuint16*)(0x40190028))
#define MCF_ADC_ADLLMT4                      (*(vuint16*)(0x4019002A))
#define MCF_ADC_ADLLMT5                      (*(vuint16*)(0x4019002C))
#define MCF_ADC_ADLLMT6                      (*(vuint16*)(0x4019002E))
#define MCF_ADC_ADLLMT7                      (*(vuint16*)(0x40190030))
#define MCF_ADC_ADHLMT0                      (*(vuint16*)(0x40190032))
#define MCF_ADC_ADHLMT1                      (*(vuint16*)(0x40190034))
#define MCF_ADC_ADHLMT2                      (*(vuint16*)(0x40190036))
#define MCF_ADC_ADHLMT3                      (*(vuint16*)(0x40190038))
#define MCF_ADC_ADHLMT4                      (*(vuint16*)(0x4019003A))
#define MCF_ADC_ADHLMT5                      (*(vuint16*)(0x4019003C))
#define MCF_ADC_ADHLMT6                      (*(vuint16*)(0x4019003E))
#define MCF_ADC_ADHLMT7                      (*(vuint16*)(0x40190040))
#define MCF_ADC_ADOFS0                       (*(vuint16*)(0x40190042))
#define MCF_ADC_ADOFS1                       (*(vuint16*)(0x40190044))
#define MCF_ADC_ADOFS2                       (*(vuint16*)(0x40190046))
#define MCF_ADC_ADOFS3                       (*(vuint16*)(0x40190048))
#define MCF_ADC_ADOFS4                       (*(vuint16*)(0x4019004A))
#define MCF_ADC_ADOFS5                       (*(vuint16*)(0x4019004C))
#define MCF_ADC_ADOFS6                       (*(vuint16*)(0x4019004E))
#define MCF_ADC_ADOFS7                       (*(vuint16*)(0x40190050))
#define MCF_ADC_POWER                        (*(vuint16*)(0x40190052))
#define MCF_ADC_CAL                          (*(vuint16*)(0x40190054))
#define MCF_ADC_ADRSLT(x)                    (*(vuint16*)(0x40190012 + ((x)*0x2)))
#define MCF_ADC_ADLLMT(x)                    (*(vuint16*)(0x40190022 + ((x)*0x2)))
#define MCF_ADC_ADHLMT(x)                    (*(vuint16*)(0x40190032 + ((x)*0x2)))
#define MCF_ADC_ADOFS(x)                     (*(vuint16*)(0x40190042 + ((x)*0x2)))


/* Bit definitions and macros for MCF_ADC_CTRL1 */
#define MCF_ADC_CTRL1_SMODE(x)               (((x)&0x7)<<0)
#define MCF_ADC_CTRL1_CHNCFG(x)              (((x)&0xF)<<0x4)
#define MCF_ADC_CTRL1_HLMTIE                 (0x100)
#define MCF_ADC_CTRL1_LLMTIE                 (0x200)
#define MCF_ADC_CTRL1_ZCIE                   (0x400)
#define MCF_ADC_CTRL1_EOSIE0                 (0x800)
#define MCF_ADC_CTRL1_SYNC0                  (0x1000)
#define MCF_ADC_CTRL1_START0                 (0x2000)
#define MCF_ADC_CTRL1_STOP0                  (0x4000)

/* Bit definitions and macros for MCF_ADC_CTRL2 */
#define MCF_ADC_CTRL2_DIV(x)                 (((x)&0x1F)<<0)
#define MCF_ADC_CTRL2_SIMULT                 (0x20)
#define MCF_ADC_CTRL2_EOSIE1                 (0x800)
#define MCF_ADC_CTRL2_SYNC1                  (0x1000)
#define MCF_ADC_CTRL2_START1                 (0x2000)
#define MCF_ADC_CTRL2_STOP1                  (0x4000)

/* Bit definitions and macros for MCF_ADC_ADZCC */
#define MCF_ADC_ADZCC_ZCE0(x)                (((x)&0x3)<<0)
#define MCF_ADC_ADZCC_ZCE1(x)                (((x)&0x3)<<0x2)
#define MCF_ADC_ADZCC_ZCE2(x)                (((x)&0x3)<<0x4)
#define MCF_ADC_ADZCC_ZCE3(x)                (((x)&0x3)<<0x6)
#define MCF_ADC_ADZCC_ZCE4(x)                (((x)&0x3)<<0x8)
#define MCF_ADC_ADZCC_ZCE5(x)                (((x)&0x3)<<0xA)
#define MCF_ADC_ADZCC_ZCE6(x)                (((x)&0x3)<<0xC)
#define MCF_ADC_ADZCC_ZCE7(x)                (((x)&0x3)<<0xE)

/* Bit definitions and macros for MCF_ADC_ADLST1 */
#define MCF_ADC_ADLST1_SAMPLE0(x)            (((x)&0x7)<<0)
#define MCF_ADC_ADLST1_SAMPLE1(x)            (((x)&0x7)<<0x4)
#define MCF_ADC_ADLST1_SAMPLE2(x)            (((x)&0x7)<<0x8)
#define MCF_ADC_ADLST1_SAMPLE3(x)            (((x)&0x7)<<0xC)

/* Bit definitions and macros for MCF_ADC_ADLST2 */
#define MCF_ADC_ADLST2_SAMPLE4(x)            (((x)&0x7)<<0)
#define MCF_ADC_ADLST2_SAMPLE5(x)            (((x)&0x7)<<0x4)
#define MCF_ADC_ADLST2_SAMPLE6(x)            (((x)&0x7)<<0x8)
#define MCF_ADC_ADLST2_SAMPLE7(x)            (((x)&0x7)<<0xC)

/* Bit definitions and macros for MCF_ADC_ADSDIS */
#define MCF_ADC_ADSDIS_DS0                   (0x1)
#define MCF_ADC_ADSDIS_DS1                   (0x2)
#define MCF_ADC_ADSDIS_DS2                   (0x4)
#define MCF_ADC_ADSDIS_DS3                   (0x8)
#define MCF_ADC_ADSDIS_DS4                   (0x10)
#define MCF_ADC_ADSDIS_DS5                   (0x20)
#define MCF_ADC_ADSDIS_DS6                   (0x40)
#define MCF_ADC_ADSDIS_DS7                   (0x80)

/* Bit definitions and macros for MCF_ADC_ADSTAT */
#define MCF_ADC_ADSTAT_RDY0                  (0x1)
#define MCF_ADC_ADSTAT_RDY1                  (0x2)
#define MCF_ADC_ADSTAT_RDY2                  (0x4)
#define MCF_ADC_ADSTAT_RDY3                  (0x8)
#define MCF_ADC_ADSTAT_RDY4                  (0x10)
#define MCF_ADC_ADSTAT_RDY5                  (0x20)
#define MCF_ADC_ADSTAT_RDY6                  (0x40)
#define MCF_ADC_ADSTAT_RDY7                  (0x80)
#define MCF_ADC_ADSTAT_HLMTI                 (0x100)
#define MCF_ADC_ADSTAT_LLMTI                 (0x200)
#define MCF_ADC_ADSTAT_ZCI                   (0x400)
#define MCF_ADC_ADSTAT_EOSI0                 (0x800)
#define MCF_ADC_ADSTAT_EOSI1                 (0x1000)
#define MCF_ADC_ADSTAT_CIP1                  (0x4000)
#define MCF_ADC_ADSTAT_CIP0                  (0x8000)

/* Bit definitions and macros for MCF_ADC_ADLSTAT */
#define MCF_ADC_ADLSTAT_LLS0                 (0x1)
#define MCF_ADC_ADLSTAT_LLS1                 (0x2)
#define MCF_ADC_ADLSTAT_LLS2                 (0x4)
#define MCF_ADC_ADLSTAT_LLS3                 (0x8)
#define MCF_ADC_ADLSTAT_LLS4                 (0x10)
#define MCF_ADC_ADLSTAT_LLS5                 (0x20)
#define MCF_ADC_ADLSTAT_LLS6                 (0x40)
#define MCF_ADC_ADLSTAT_LLS7                 (0x80)
#define MCF_ADC_ADLSTAT_HLS0                 (0x100)
#define MCF_ADC_ADLSTAT_HLS1                 (0x200)
#define MCF_ADC_ADLSTAT_HLS2                 (0x400)
#define MCF_ADC_ADLSTAT_HLS3                 (0x800)
#define MCF_ADC_ADLSTAT_HLS4                 (0x1000)
#define MCF_ADC_ADLSTAT_HLS5                 (0x2000)
#define MCF_ADC_ADLSTAT_HLS6                 (0x4000)
#define MCF_ADC_ADLSTAT_HLS7                 (0x8000)

/* Bit definitions and macros for MCF_ADC_ADZCSTAT */
#define MCF_ADC_ADZCSTAT_ZCS0                (0x1)
#define MCF_ADC_ADZCSTAT_ZCS1                (0x2)
#define MCF_ADC_ADZCSTAT_ZCS2                (0x4)
#define MCF_ADC_ADZCSTAT_ZCS3                (0x8)
#define MCF_ADC_ADZCSTAT_ZCS4                (0x10)
#define MCF_ADC_ADZCSTAT_ZCS5                (0x20)
#define MCF_ADC_ADZCSTAT_ZCS6                (0x40)
#define MCF_ADC_ADZCSTAT_ZCS7                (0x80)

/* Bit definitions and macros for MCF_ADC_ADRSLT */
#define MCF_ADC_ADRSLT_RSLT(x)               (((x)&0xFFF)<<0x3)
#define MCF_ADC_ADRSLT_SEXT                  (0x8000)

/* Bit definitions and macros for MCF_ADC_ADLLMT */
#define MCF_ADC_ADLLMT_LLMT(x)               (((x)&0xFFF)<<0x3)

/* Bit definitions and macros for MCF_ADC_ADHLMT */
#define MCF_ADC_ADHLMT_HLMT(x)               (((x)&0xFFF)<<0x3)

/* Bit definitions and macros for MCF_ADC_ADOFS */
#define MCF_ADC_ADOFS_OFFSET(x)              (((x)&0xFFF)<<0x3)

/* Bit definitions and macros for MCF_ADC_POWER */
#define MCF_ADC_POWER_PD0                    (0x1)
#define MCF_ADC_POWER_PD1                    (0x2)
#define MCF_ADC_POWER_PD2                    (0x4)
#define MCF_ADC_POWER_APD                    (0x8)
#define MCF_ADC_POWER_PUDELAY(x)             (((x)&0x3F)<<0x4)
#define MCF_ADC_POWER_PSTS0                  (0x400)
#define MCF_ADC_POWER_PSTS1                  (0x800)
#define MCF_ADC_POWER_PSTS2                  (0x1000)
#define MCF_ADC_POWER_ASB                    (0x8000)

/* Bit definitions and macros for MCF_ADC_CAL */
#define MCF_ADC_CAL_SEL_VREFL                (0x4000)
#define MCF_ADC_CAL_SEL_VREFH                (0x8000)


#endif /* __MCF52221_ADC_H__ */
