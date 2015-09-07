/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_s12ad.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for S12AD module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef S12AD_H
#define S12AD_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/*
    A/D control register (ADCSR)
*/
/* Group B scan end interrupt enable (GBADIE) */
#define _AD_GBADI_DISABLE                   (0x0000U) /* Disables S12GBADI interrupt generation upon group B scan
                                                         completion */
#define _AD_GBADI_ENABLE                    (0x0040U) /* Enables S12GBADI interrupt generation upon group B scan
                                                          completion */
/* Double trigger mode select (DBLE) */
#define _AD_DBLTRIGGER_DISABLE              (0x0000U) /* Disable double trigger mode */
#define _AD_DBLTRIGGER_ENABLE               (0x0080U) /* Enable double trigger mode */
/* Trigger select (EXTRG) */
#define _AD_SYNC_TRIGGER                    (0x0000U) /* A/D conversion started by snychronous trigger */
#define _AD_ASYNC_TRIGGER                   (0x0100U) /* A/D conversion started by asynchronous trigger */
/* Trigger start enable (TRGE) */
#define _AD_SYNCASYNCTRG_DISABLE            (0x0000U) /* A/D conversion synchronous or asynchronous trigger disable */
#define _AD_SYNCASYNCTRG_ENABLE             (0x0200U) /* A/D conversion synchronous or asynchronous trigger enable */
/* Scan end interrupt enable (ADIE) */
#define _AD_SCAN_END_INTERRUPT_DISABLE      (0x0000U) /* Disable S12ADI0 interrupt generation upon scan completion */
#define _AD_SCAN_END_INTERRUPT_ENABLE       (0x1000U) /* Enable S12ADI0 interrupt generation upon scan completion */
/* Scan mode select (ADCS) */
#define _AD_SINGLE_SCAN_MODE                (0x0000U) /* Single scan mode */
#define _AD_GROUP_SCAN_MODE                 (0x2000U) /* Group scan mode */
#define _AD_CONTINUOUS_SCAN_MODE            (0x4000U) /* Continuous scan mode */
/* A/D conversion start (ADST) */
#define _AD_CONVERSION_STOP                 (0x0000U) /* Stop A/D conversion */
#define _AD_CONVERSION_START                (0x8000U) /* Start A/D conversion */

/*
    A/D converted value addition count select register (ADADC)
*/
/* Addition Count Select (ADC[1:0]) */
#define _AD_1_TIME_CONVERSION               (0x00U) /* 1-time conversion */
#define _AD_2_TIME_CONVERSION               (0x01U) /* 2-time conversion */
#define _AD_3_TIME_CONVERSION               (0x02U) /* 3-time conversion */
#define _AD_4_TIME_CONVERSION               (0x03U) /* 4-time conversion */
/* Average Mode Enable bit (AVEE) */
#define _AD_ADDITION_MODE                   (0x00U) /* Addition mode */
#define _AD_AVERAGE_MODE                    (0x80U) /* Average mode */

/*
    A/D control extended register (ADCER)
*/
/* A/D Conversion Accuracy Specify (ADPRC) */
#define _AD_RESOLUTION_12BIT                (0x0000U) /* 12 bit resolution */
#define _AD_RESOLUTION_10BIT                (0x0002U) /* 10 bit resolution */
#define _AD_RESOLUTION_8BIT                 (0x0004U) /* 8 bit resolution */
/* Automatic clearing enable (ACE) */
#define _AD_AUTO_CLEARING_DISABLE           (0x0000U) /* Disable auto clearing */
#define _AD_AUTO_CLEARING_ENABLE            (0x0020U) /* Enable auto clearing */
/* A/D Self-diagnosis selection (DIAGVAL) */
#define _AD_SELFTDIAGST_DISABLE             (0x0000U) /* Disable self-diagnosis */
#define _AD_SELFTDIAGST_VREFH0_0            (0x0100U) /* Self-diagnosis using a voltage of 0V */
#define _AD_SELFTDIAGST_VREFH0_HALF         (0x0200U) /* Self-diagnosis using a voltage of VREFH0_1/2*/
#define _AD_SELFTDIAGST_VREFH0              (0x0300U) /* Self-diagnosis using a voltage of VREFH0_1*/
#define _AD_SELFTDIAGST_VREFH1_0            (0x0100U) /* Self-diagnosis using a voltage of 0V */
#define _AD_SELFTDIAGST_VREFH1_HALF         (0x0200U) /* Self-diagnosis using a voltage of VREFH1_1/2*/
#define _AD_SELFTDIAGST_VREFH1              (0x0300U) /* Self-diagnosis using a voltage of VREFH1_1*/
/* A/D Self-diagnostic mode selection (DIAGLD) */
#define _AD_SELFTDIAGST_ROTATION            (0x0000U) /* Rotation mode for self-diagnosis voltage */
#define _AD_SELFTDIAGST_FIX                 (0x0400U) /* Fixed mode for self-diagnosis voltage */
/* A/D Self-diagnostic enable (DIAGM) */
#define _AD_SELFTDIAGST_DISABLE             (0x0000U) /* 12bit self-diagnosis disable */
#define _AD_SELFTDIAGST_ENABLE              (0x0800U) /* 12bit self-diagnosis enable */
/* A/D data register format selection (ADRFMT) */
#define _AD_RIGHT_ALIGNMENT                 (0x0000U) /* Right-alignment for data register format */
#define _AD_LEFT_ALIGNMENT                  (0x8000U) /* Left-alignment for data register format */

/*
    A/D start trigger select register (ADSTRGR)
*/
/* A/D conversion start trigger select for group B (TRSB) */
#define _AD_TRSB_TRGA0N                     (0x0001U) /* Compare match with or input capture to MTU0.TGRA */
#define _AD_TRSB_TRGA1N                     (0x0002U) /* Compare match with or input capture to MTU1.TGRA */
#define _AD_TRSB_TRGA2N                     (0x0003U) /* Compare match with or input capture to MTU2.TGRA */
#define _AD_TRSB_TRGA3N                     (0x0004U) /* Compare match with or input capture to MTU3.TGRA */
#define _AD_TRSB_TRGA4N                     (0x0005U) /* Compare match with or input capture to MTU4.TGRA,or an
                                                            underflow of MTU4.TCNT (in the trough) in complementary
                                                            PWM mode */
#define _AD_TRSB_TRGA6N                     (0x0006U) /* Compare match with or input capture to MTU6.TGRA */
#define _AD_TRSB_TRGA7N                     (0x0007U) /* Compare match with or input capture to MTU7.TGRA,or an
                                                            underflow of MTU7.TCNT (in the trough) in complementary
                                                            PWM mode */
#define _AD_TRSB_TRG0N                      (0x0008U) /* Compare match with MTU0.TGRE */
#define _AD_TRSB_TRG4AN                     (0x0009U) /* Compare match between MTU4.TADCORA and MTU4.TCNT */
#define _AD_TRSB_TRG4BN                     (0x000AU) /* Compare match between MTU4.TADCORB and MTU4.TCNT */
#define _AD_TRSB_TRG4BN_TRG4AN              (0x000BU) /* Compare match between MTU4.TADCORA and MTU4.TCNT, or
                                                            between MTU4.TADCORB and MTU4.TCNT */
#define _AD_TRSB_TRG4ABN                    (0x000CU) /* Compare match between MTU4.TADCORA and MTU4.TCNT, and
                                                            between MTU4.TADCORB and MTU4.TCNT (when interrupt skipping
                                                            function 2 is in use) */
#define _AD_TRSB_TRG7AN                     (0x000DU) /* Compare match between MTU7.TADCORA and MTU7.TCNT */
#define _AD_TRSB_TRG7BN                     (0x000EU) /* Compare match between MTU7.TADCORB and MTU7.TCNT */
#define _AD_TRSB_TRG7AN_TRG7BN              (0x000FU) /* Compare match between MTU7.TADCORA and MTU7.TCNT, or between
                                                            MTU7.TADCORB and MTU7.TCNT */
#define _AD_TRSB_TRG7ABN                    (0x0010U) /* Compare match between MTU7.TADCORA and MTU7.TCNT, and between
                                                            MTU7.TADCORB and MTU7.TCNT (when interrupt skipping function
                                                            2 is in use) */
#define _AD_TRSB_GTADTRA0N                  (0x0011U) /* Compare match with GPT0.GTADTRA */
#define _AD_TRSB_GTADTRB0N                  (0x0012U) /* Compare match with GPT0.GTADTRB */
#define _AD_TRSB_GTADTRA1N                  (0x0013U) /* Compare match with GPT1.GTADTRA */
#define _AD_TRSB_GTADTRB1N                  (0x0014U) /* Compare match with GPT1.GTADTRB */
#define _AD_TRSB_GTADTRA2N                  (0x0015U) /* Compare match with GPT2.GTADTRA */
#define _AD_TRSB_GTADTRB2N                  (0x0016U) /* Compare match with GPT2.GTADTRB */
#define _AD_TRSB_GTADTRA3N                  (0x0017U) /* Compare match with GPT3.GTADTRA */
#define _AD_TRSB_GTADTRB3N                  (0x0018U) /* Compare match with GPT3.GTADTRB */
#define _AD_TRSB_GTADTRA0N_GTADTRB0N        (0x0019U) /* Compare match with GPT0.GTADTRA or with GPT0.GTADTRB */
#define _AD_TRSB_GTADTRA1N_GTADTRB1N        (0x001AU) /* Compare match with GPT1.GTADTRA or with GPT1.GTADTRB */
#define _AD_TRSB_GTADTRA2N_GTADTRB2N        (0x001BU) /* Compare match with GPT2.GTADTRA or with GPT2.GTADTRB*/
#define _AD_TRSB_GTADTRA3N_GTADTRB3N        (0x001CU) /* Compare match with GPT3.GTADTRA or with GPT3.GTADTRB */
#define _AD_TRSB_TPTRGAN_0                  (0x001FU) /* Compare match with or input capture to TPUn.TGRA(n = 0 to 5) */
#define _AD_TRSB_TPTRG0AN_0                 (0x0020U) /* Compare match with or input capture to TPU0.TGRA */
#define _AD_TRSB_TPTRGAN_1                  (0x0021U) /* Compare match with or input capture to TPUn.TGRA(n = 6 to 11) */
#define _AD_TRSB_TPTRG6AN_1                 (0x0022U) /* Compare match with or input capture to TPU6.TGRA */
#define _AD_TRSB_ELCTRG0N_ELCTRG1N          (0x0030U) /* Trigger from ELC */

/* A/D conversion start trigger select for group A (TRSA) */
#define _AD_TRSA_ADTRG                      (0x0000U) /* Input pin for the trigger */
#define _AD_TRSA_TRGA0N                     (0x0100U) /* Compare match with or input capture to MTU0.TGRA */
#define _AD_TRSA_TRGA1N                     (0x0200U) /* Compare match with or input capture to MTU1.TGRA */
#define _AD_TRSA_TRGA2N                     (0x0300U) /* Compare match with or input capture to MTU2.TGRA */
#define _AD_TRSA_TRGA3N                     (0x0400U) /* Compare match with or input capture to MTU3.TGRA */
#define _AD_TRSA_TRGA4N                     (0x0500U) /* Compare match with or input capture to MTU4.TGRA or, in
                                                            complementary PWM mode,an underflow of MTU4.TCNT
                                                            (in the trough)*/
#define _AD_TRSA_TRGA6N                     (0x0600U) /* Compare match with or input capture to MTU6.TGRA */
#define _AD_TRSA_TRGA7N                     (0x0700U) /* Compare match with or input capture to MTU7.TGRA or, in
                                                            complementary PWM mode,an underflow of MTU7.TCNT
                                                            (in the trough)*/
#define _AD_TRSA_TRG0N                      (0x0800U) /* Compare match with MTU0.TGRE */
#define _AD_TRSA_TRG4AN                     (0x0900U) /* Compare match between MTU4.TADCORA and MTU4.TCNT */
#define _AD_TRSA_TRG4BN                     (0x0A00U) /* Compare match between MTU4.TADCORB and MTU4.TCNT */
#define _AD_TRSA_TRG4BN_TRG4AN              (0x0B00U) /* Compare match between MTU4.TADCORA and MTU4.TCNT, or between
                                                            MTU4.TADCORB and MTU4.TCNT */
#define _AD_TRSA_TRG4ABN                    (0x0C00U) /* Compare match between MTU4.TADCORA and MTU4.TCNT, and between
                                                            MTU4.TADCORB and MTU4.TCNT (when interrupt skipping function
                                                            2 is in use) */
#define _AD_TRSA_TRG7AN                     (0x0D00U) /* Compare match between MTU7.TADCORA and MTU7.TCNT */
#define _AD_TRSA_TRG7BN                     (0x0E00U) /* Compare match between MTU7.TADCORB and MTU7.TCNT */
#define _AD_TRSA_TRG7AN_TRG7BN              (0x0F00U) /* Compare match between MTU7.TADCORA and MTU7.TCNT, or between
                                                            MTU7.TADCORB and MTU7.TCNT */
#define _AD_TRSA_TRG7ABN                    (0x1000U) /* Compare match between MTU7.TADCORA and MTU7.TCNT, and between
                                                            MTU7.TADCORB and MTU7.TCNT (when interrupt skipping function
                                                            2 is in use) */
#define _AD_TRSA_GTADTRA0N                  (0x1100U) /* Compare match with GPT0.GTADTRA */
#define _AD_TRSA_GTADTRB0N                  (0x1200U) /* Compare match with GPT0.GTADTRB */
#define _AD_TRSA_GTADTRA1N                  (0x1300U) /* Compare match with GPT1.GTADTRA */
#define _AD_TRSA_GTADTRB1N                  (0x1400U) /* Compare match with GPT1.GTADTRB */
#define _AD_TRSA_GTADTRA2N                  (0x1500U) /* Compare match with GPT2.GTADTRA */
#define _AD_TRSA_GTADTRB2N                  (0x1600U) /* Compare match with GPT2.GTADTRB */
#define _AD_TRSA_GTADTRA3N                  (0x1700U) /* Compare match with GPT3.GTADTRA */
#define _AD_TRSA_GTADTRB3N                  (0x1800U) /* Compare match with GPT3.GTADTRB */
#define _AD_TRSA_GTADTRA0N_GTADTRB0N        (0x1900U) /* Compare match with GPT0.GTADTRA or with GPT0.GTADTRB */
#define _AD_TRSA_GTADTRA1N_GTADTRB1N        (0x1A00U) /* Compare match with GPT1.GTADTRA or with GPT1.GTADTRB */
#define _AD_TRSA_GTADTRA2N_GTADTRB2N        (0x1B00U) /* Compare match with GPT2.GTADTRA or with GPT2.GTADTRB */
#define _AD_TRSA_GTADTRA3N_GTADTRB3N        (0x1C00U) /* Compare match with GPT3.GTADTRA or with GPT3.GTADTRB */
#define _AD_TRSA_TPTRGAN_0                  (0x1F00U) /* Compare match with or input capture to TPUn.TGRA(n= 0 to 5) */
#define _AD_TRSA_TPTRG0AN_0                 (0x2000U) /* Compare match with or input capture to TPU0.TGRA */
#define _AD_TRSA_TPTRGAN_1                  (0x2100U) /* Compare match with or input capture to TPUn.TGRA(n= 6 to 11) */
#define _AD_TRSA_TPTRG6AN_1                 (0x2200U) /* Compare match with or input capture to TPU6.TGRA */
#define _AD_TRSA_ELCTRG0N_ELCTRG1N          (0x3000U) /* Trigger from ELC */

/*
    A/D converted extended input control register (ADEXICR)
*/
/* Temperature sensor output A/D conversion value addition mode selection (TSSAD) */
#define _AD_TEMP_ADDITION_DISABLE           (0x0000U) /* Temperature sensor output A/D converted value addition/average
                                                            mode disabled */
#define _AD_TEMP_ADDITION_ENABLE            (0x0001U) /* Temperature sensor output A/D converted value addition/average
                                                            mode enabled */
/* Temperature sensor output A/D conversion select (TSSA) */
#define _AD_TEMP_GROUPA_DISABLE             (0x0000U) /* A/D conversion of temperature sensor output is disabled in 
                                                            group A  */
#define _AD_TEMP_GROUPA_ENABLE              (0x0100U) /* A/D conversion of temperature sensor output is enabled in 
                                                            group A  */
/* Temperature sensor output A/D conversion select (TSSB) */
#define _AD_TEMP_GROUPB_DISABLE             (0x0000U) /* A/D conversion of temperature sensor output is disabled in 
                                                            group B  */
#define _AD_TEMP_GROUPB_ENABLE              (0x0400U) /* A/D conversion of temperature sensor output is enabled in 
                                                            group B  */
/* Extended analog input selection (EXSEL) */
#define _AD_EXTNANEX1_IN_DISABLE            (0x0000U) /* Extended analog input disable */
#define _AD_EXTNANEX1_IN_ENABLE             (0x2000U) /* Extended analog input enable */
/* Extended analog output control (EXOEN) */
#define _AD_EXTNANEX0_OUT_DISABLE           (0x0000U) /* Extended analog output disable */
#define _AD_EXTNANEX0_IN_ENABLE             (0x8000U) /* Extended analog output enable */

/*
    A/D Group Scan Priority Control Register (ADGSPCR)
*/
/* Group-A Priority Control Setting (PGS) */
#define _AD_GPAPRIORITY_DISABLE             (0x0000U) /* Operation is without group A priority control */
#define _AD_GPAPRIORITY_ENABLE              (0x0001U) /* Operation is with group A priority control */
/* Group B Restart Setting (GBRSCN) */
#define _AD_GPBRESTART_DISABLE              (0x0000U) /* Group B not restart after discontinued due to Group A
                                                     priority */
#define _AD_GPBRESTART_ENABLE               (0x0002U) /* Group B restart after discontinued due to Group A priority */
/* Group B Single Cycle Scan Continuous Start (GBRP) */
#define _AD_GPBSCSCS_DISABLE                (0x0000U) /* Single cycle scan for group B not continuously activated */
#define _AD_GPBSCSCS_ENABLE                 (0x8000U) /* Single cycle scan for group B is continuously activated */

/* 
    A/D Compare Control Register (ADCMPCR)
*/
/* Window Function Setting (WCMPE) */
#define _AD_WINDOWFUNCTION_DISABLE          (0x00U) /* Window function disabled */ 
#define _AD_WINDOWFUNCTION_ENABLE           (0x40U) /* Window function enabled */
/* Compare Interrupt Enable (CMPIE) */
#define _AD_COMPARISON_INTERRUPT_DISABLE    (0x00U) /* S12CMPI interrupt is disabled */ 
#define _AD_COMPARISON_INTERRUPT_ENABLE     (0x80U) /* S12CMPI interrupt is enabled */

/* 
    A/D Compare Channel Select Extended Register (ADCMPANSER)
*/
/* Temperature Sensor Output Compare Select(CMPSTS) */
#define _AD_TEMP_COMPARE_DISABLE            (0x00U) /* Temperature sensor output is not a target for comparison. */ 
#define _AD_TEMP_COMPARE_ENABLE             (0x01U) /* Temperature sensor output is a target for comparison. */

/* 
    A/D Compare Level Extended Register (ADCMPLER)
*/
/* Temperature Sensor Output Compare Level Select(CMPLTS) */
#define _AD_TEMP0_COMPARELEVEL              (0x00U) /* AD-converted value < ADCMPDR0 register value or A/D-converted
                                                            value > ADCMPDR1 register value */ 
#define _AD_TEMP1_COMPARELEVEL              (0x01U) /* ADCMPDR0 register value < A/D-converted value < ADCMPDR1
                                                            register value */

/* 
    A/D Pin-Level Self-Diagnosis Control Register (ADTDCR)
*/
/* Pin-level Self-diagnosis Level Select (TDLV[1:0]) */
#define _AD_EVEN_AVSS0                      (0x00U) /* Input channels with even numbers are discharged to AVSS, 
                                                            and input channels with odd numbers are charged to AVCC. */
#define _AD_EVEN_AVCC0                      (0x01U) /* Input channels with even numbers are charged to AVCC, 
                                                            and input channels with odd numbers are discharged to AVSS. */
#define _AD_ODD_AVCC0_HALF                  (0x02U) /* Input channels with even numbers are discharged to AVSS, 
                                                            and input channels with odd numbers are charged to AVCx1/2. */
#define _AD_EVEN_AVCC0_HALF                 (0x03U) /* Input channels with even numbers are charged to AVCCx1/2, 
                                                            and input channels with odd numbers are discharged to AVSS. */
#define _AD_EVEN_AVSS1                      (0x00U) /* Input channels with even numbers are discharged to AVSS, 
                                                            and input channels with odd numbers are charged to AVCC. */
#define _AD_EVEN_AVCC1                      (0x01U) /* Input channels with even numbers are charged to AVCC, 
                                                            and input channels with odd numbers are discharged to AVSS. */
#define _AD_ODD_AVCC1_HALF                  (0x02U) /* Input channels with even numbers are discharged to AVSS, 
                                                            and input channels with odd numbers are charged to AVCx1/2. */
#define _AD_EVEN_AVCC1_HALF                 (0x03U) /* Input channels with even numbers are charged to AVCCx1/2, 
                                                            and input channels with odd numbers are discharged to AVSS. */
/* Pin-level Self-diagnosis Enable (TDE) */
#define _AD_PINLVL_ENABLE                   (0x00U) /* Enables pin-level self-diagnosis. */
#define _AD_PINLVL_DISABLE                  (0x80U) /* Disables pin-level self-diagnosis. */


/* 
    A/D Error Control Register (ADERCR)
*/
/* Overwrite Error Interrupt Enable (OWEIE) */
#define _AD_ERROR_INT_REQUEST_DISABLE       (0x00U) /* Disables interrupt generation when an overwrite error is detected. */
#define _AD_ERROR_INT_REQUEST_ENABLE        (0x04U) /* Enables interrupt generation when an overwrite error is detected. */

/*
    Interrupt Source Priority Register n (PRLn)
*/
/* Interrupt Priority Level Select (PRL[3:0]) */
#define _AD_PRIORITY_LEVEL0                 (0x00000000UL) /* Level 0 (highest) */
#define _AD_PRIORITY_LEVEL1                 (0x00000001UL) /* Level 1 */
#define _AD_PRIORITY_LEVEL2                 (0x00000002UL) /* Level 2 */
#define _AD_PRIORITY_LEVEL3                 (0x00000003UL) /* Level 3 */
#define _AD_PRIORITY_LEVEL4                 (0x00000004UL) /* Level 4 */
#define _AD_PRIORITY_LEVEL5                 (0x00000005UL) /* Level 5 */
#define _AD_PRIORITY_LEVEL6                 (0x00000006UL) /* Level 6 */
#define _AD_PRIORITY_LEVEL7                 (0x00000007UL) /* Level 7 */
#define _AD_PRIORITY_LEVEL8                 (0x00000008UL) /* Level 8 */
#define _AD_PRIORITY_LEVEL9                 (0x00000009UL) /* Level 9 */
#define _AD_PRIORITY_LEVEL10                (0x0000000AUL) /* Level 10 */
#define _AD_PRIORITY_LEVEL11                (0x0000000BUL) /* Level 11 */
#define _AD_PRIORITY_LEVEL12                (0x0000000CUL) /* Level 12 */
#define _AD_PRIORITY_LEVEL13                (0x0000000DUL) /* Level 13 */
#define _AD_PRIORITY_LEVEL14                (0x0000000EUL) /* Level 14 */
#define _AD_PRIORITY_LEVEL15                (0x0000000FUL) /* Level 15 */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define _AD0_CHANNEL_SELECT_A               (0x0080U)
#define _AD0_ADDAVG_CHANNEL_SELECT          (0x0000U)
#define _AD0_DISCONECT_SETTING              (0x00U)
#define _AD0_COMPARECHANNEL_SELECT          (0x0000U)
#define _AD0_COMPARELEVEL_SELECT            (0x0000U)
#define _AD0_SAMPLING_STATE_7               (0x16U)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
typedef enum
{
    ADCHANNEL0, ADCHANNEL1, ADCHANNEL2, ADCHANNEL3, ADCHANNEL4, ADCHANNEL5, ADCHANNEL6,
    ADCHANNEL7, ADCHANNEL8, ADCHANNEL9, ADCHANNEL10, ADCHANNEL11, ADCHANNEL12,
    ADCHANNEL13, ADCHANNEL14, ADCHANNEL15, ADSELFDIAGNOSIS, ADTEMPSENSOR, ADDATADUPLICATION,
    ADDATADUPLICATIONA, ADDATADUPLICATIONB
} ad_channel_t;

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_S12AD0_Create(void);
void R_S12AD0_Start(void);
void R_S12AD0_Stop(void);
void R_S12AD0_Get_ValueResult(ad_channel_t channel, uint16_t * const buffer);
void R_S12AD0_Set_CompareValue(uint16_t  reg_value0, uint16_t  reg_value1);

/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif