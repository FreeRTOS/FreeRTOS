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
* File Name    : r_cg_tpu.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for TPU module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef TPU_H
#define TPU_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    Timer Control Register (TCR)
*/
/* Time Prescaler Select (TPSC[2:0]) */
#define _TPU_PCLKD_1                    (0x00U) /* Internal clock: counts on PCLKD/1 */
#define _TPU_PCLKD_4                    (0x01U) /* Internal clock: counts on PCLKD/4 */
#define _TPU_PCLKD_16                   (0x02U) /* Internal clock: counts on PCLKD/16 */
#define _TPU_PCLKD_64                   (0x03U) /* Internal clock: counts on PCLKD/64 */
#define _TPU_PCLKD_256                  (0x06U) /* Internal clock: counts on PCLKD/256 */
#define _TPU2_PCLKD_1024                (0x07U) /* TPU2 Internal clock: counts on PCLKD/1024 */
#define _TPU3_PCLKD_1024                (0x05U) /* TPU3 Internal clock: counts on PCLKD/1024 */
#define _TPU4_PCLKD_1024                (0x06U) /* TPU4 Internal clock: counts on PCLKD/1024 */
#define _TPU8_PCLKD_1024                (0x07U) /* TPU8 Internal clock: counts on PCLKD/1024 */
#define _TPU9_PCLKD_1024                (0x05U) /* TPU9 Internal clock: counts on PCLKD/1024 */
#define _TPU10_PCLKD_1024               (0x06U) /* TPU10 Internal clock: counts on PCLKD/1024 */
#define _TPU_PCLKD_4096                 (0x07U) /* Internal clock: counts on PCLKD/4096 */
#define _TPU_TCLKA                      (0x04U) /* External clock: counts on TCLKA pin input */
#define _TPU_TCLKB                      (0x05U) /* External clock: counts on TCLKB pin input */
#define _TPU_TCLKC_06                   (0x06U) /* External clock: counts on TCLKC pin input */
#define _TPU_TCLKC_05                   (0x05U) /* External clock: counts on TCLKC pin input */
#define _TPU_TCLKD                      (0x07U) /* External clock: counts on TCLKD pin input */
#define _TPU_TCLKE                      (0x04U) /* External clock: counts on TCLKE pin input */
#define _TPU_TCLKF                      (0x05U) /* External clock: counts on TCLKF pin input */
#define _TPU_TCLKG_06                   (0x06U) /* External clock: counts on TCLKG pin input */
#define _TPU_TCLKG_05                   (0x05U) /* External clock: counts on TCLKG pin input */
#define _TPU_TCLKH                      (0x07U) /* External clock: counts on TCLKH pin input */
#define _TPU2_COUNT                     (0x07U) /* TPU1: Counts on TPU2.TCNT counter overflow/underflow */
#define _TPU5_COUNT                     (0x07U) /* TPU4: Counts on TPU5.TCNT counter overflow/underflow */
#define _TPU8_COUNT                     (0x07U) /* TPU7: Counts on TPU8.TCNT counter overflow/underflow */
#define _TPU11_COUNT                    (0x07U) /* TPU10: Counts on TPU11.TCNT counter overflow/underflow */
/* Clock Edge Select (CKEG[1:0]) */
#define _TPU_CKEG_IT_F                  (0x00U) /* Internal Clock: Count at falling edge */
#define _TPU_CKEG_EX_R                  (0x00U) /* External Clock: Count at rising edge */
#define _TPU_CKEG_IT_R                  (0x08U) /* Internal Clock: Count at rising edge */
#define _TPU_CKEG_EX_F                  (0x08U) /* External Clock: Count at falling edge */
#define _TPU_CKEG_BOTH                  (0x10U) /* Count at both edge */
/* Counter Clear Select (CCLR[2:0]) */
#define _TPU_CKCL_DIS                   (0x00U) /* TCNT clearing disabled */
#define _TPU_CKCL_A                     (0x20U) /* TCNT cleared by TGRA compare match/input capture */
#define _TPU_CKCL_B                     (0x40U) /* TCNT cleared by TGRB compare match/input capture */
#define _TPU_CKCL_SYN                   (0x60U) /* TCNT cleared by counter clearing in another synchronous channel */
#define _TPU_CKCL_C                     (0xA0U) /* TCNT cleared by TGRC compare match/input capture */
#define _TPU_CKCL_D                     (0xC0U) /* TCNT cleared by TGRD compare match/input capture */

/*
    Timer Mode Register (TMDR)
*/
/* Mode Select (MD[3:0]) */
#define _TPU_NORMAL                     (0x00U)   /* Normal mode */
#define _TPU_PWM1                       (0x02U)   /* PWM mode 1 */
#define _TPU_PWM2                       (0x03U)   /* PWM mode 2 */
#define _TPU_COT1                       (0x04U)   /* Phase counting mode 1 */
#define _TPU_COT2                       (0x05U)   /* Phase counting mode 2 */
#define _TPU_COT3                       (0x06U)   /* Phase counting mode 3 */
#define _TPU_COT4                       (0x07U)   /* Phase counting mode 4 */
/* Buffer Operation A (BFA) */
#define _TPU_BFA_NORMAL                 (0x00U)   /* TPUm.TGRA operates normally (m = 0, 3, 6, 9) */
#define _TPU_BFA_BUFFER                 (0x10U)   /* TPUm.TGRA and TPUm.TGRC used together for buffer operation */
/* Buffer Operation B (BFB) */
#define _TPU_BFB_NORMAL                 (0x00U)   /* TPUm.TGRB operates normally (m = 0, 3, 6, 9) */
#define _TPU_BFB_BUFFER                 (0x20U)   /* TPUm.TGRB and TPUm.TGRD used together for buffer operation */
/* TGRB Input Capture Input Select (ICSELB) */
#define _TPU_ICSELB_BPIN                (0x00U)   /* Input capture input source is TIOCBn pin */
#define _TPU_ICSELB_APIN                (0x40U)   /* Input capture input source is TIOCAn pin (n = 0 to 11) */
/* TGRD Input Capture Input Select (ICSELD) */
#define _TPU_ICSELD_DPIN                (0x00U)   /* Input capture input source is TIOCDn pin */
#define _TPU_ICSELD_CPIN                (0x80U)   /* Input capture input source is TIOCCn pin (n = 0, 3, 6, 9) */

/*
    Timer I/O Control Register (TIOR)
*/
/* I/O Control A (IOA[3:0]) for TPU0.TIORH, TPU1.TIOR, TPU2.TIOR, TPU3.TIORH, TPU4.TIORH, TPU5.TIOR 
                                TPU6.TIORH, TPU7.TIOR, TPU8.TIOR, TPU9.TIORH, TPU10.TIOR, TPU11.TIOR*/
#define _TPU_IOA_DISABLE                (0x00U)   /* Output prohibited */
#define _TPU_IOA_LL                     (0x01U)   /* Initial output is low. Low output at compare match */
#define _TPU_IOA_LH                     (0x02U)   /* Initial output is low. High output at compare match */
#define _TPU_IOA_LT                     (0x03U)   /* Initial output is low. Toggle output at compare match */
#define _TPU_IOA_HL                     (0x05U)   /* Initial output is high. Low output at compare match */
#define _TPU_IOA_HH                     (0x06U)   /* Initial output is high. High output at compare match */
#define _TPU_IOA_HT                     (0x07U)   /* Initial output is high. Toggle output at compare match */
#define _TPU_IOA_IR                     (0x08U)   /* Input capture at rising edge. */
#define _TPU_IOA_IF                     (0x09U)   /* Input capture at falling edge */
#define _TPU_IOA_IB                     (0x0AU)   /* Input capture at both edges */
#define _TPU_IOA_EX                     (0x0CU)   /* Input capture at TPU1.TCNT or TPU4.TCNT up-count/down-count
                                                                   or TPU7.TCNT or TPU10.TCNT up-count/down-count */
#define _TPU_IOA_TGRA                   (0x0DU)   /* Input capture at TPU0.TGRA or TPU3.TGRA compare match/input capture
                                                                   or TPU6.TGRA or TPU9.TGRA compare match/input capture */
/* I/O Control B (IOB[3:0]) for TPU0.TIORH, TPU1.TIOR, TPU2.TIOR, TPU3.TIORH, TPU4.TIORH, TPU5.TIOR 
                                TPU6.TIORH, TPU7.TIOR, TPU8.TIOR, TPU9.TIORH, TPU10.TIOR, TPU11.TIOR*/
#define _TPU_IOB_DISABLE                (0x00U)   /* Output prohibited */
#define _TPU_IOB_LL                     (0x10U)   /* Initial output is low. Low output at compare match */
#define _TPU_IOB_LH                     (0x20U)   /* Initial output is low. High output at compare match */
#define _TPU_IOB_LT                     (0x30U)   /* Initial output is low. Toggle output at compare match */
#define _TPU_IOB_HL                     (0x50U)   /* Initial output is high. Low output at compare match */
#define _TPU_IOB_HH                     (0x60U)   /* Initial output is high. High output at compare match */
#define _TPU_IOB_HT                     (0x70U)   /* Initial output is high. Toggle output at compare match */
#define _TPU_IOB_IR                     (0x80U)   /* Input capture at rising edge */
#define _TPU_IOB_IF                     (0x90U)   /* Input capture at falling edge */
#define _TPU_IOB_IB                     (0xA0U)   /* Input capture at both edges. */
#define _TPU_IOB_EX                     (0xC0U)   /* Input capture at TPU1.TCNT or TPU4.TCNT up-count/down-count
                                                                   or TPU7.TCNT or TPU10.TCNT up-count/down-count*/
#define _TPU_IOB_TGRC                   (0xD0U)   /* Input capture at TPU0.TGRC or TPU3.TGRC compare match/input capture
                                                                   or TPU6.TGRC or TPU9.TGRC compare match/input capture*/
/* I/O Control C (IOC[3:0]) for TPU0.TIORL, TPU3.TIORL, TPU6.TIORL, TPU9.TIORL */
#define _TPU_IOC_DISABLE                (0x00U)   /* Output prohibited */
#define _TPU_IOC_LL                     (0x01U)   /* Initial output is low. Low output at compare match */
#define _TPU_IOC_LH                     (0x02U)   /* Initial output is low. High output at compare match */
#define _TPU_IOC_LT                     (0x03U)   /* Initial output is low. Toggle output at compare match */
#define _TPU_IOC_HL                     (0x05U)   /* Initial output is high. Low output at compare match. */
#define _TPU_IOC_HH                     (0x06U)   /* Initial output is high. High output at compare match. */
#define _TPU_IOC_HT                     (0x07U)   /* Initial output is high. Toggle output at compare match. */
#define _TPU_IOC_IR                     (0x08U)   /* Input capture at rising edge. */
#define _TPU_IOC_IF                     (0x09U)   /* Input capture at falling edge. */
#define _TPU_IOC_IB                     (0x0AU)   /* Input capture at both edges. */
#define _TPU_IOC_EX                     (0x0CU)   /* Input capture at TPU1.TCNT or TPU4.TCNT up-count/down-count
                                                                   or TPU7.TCNT or TPU10.TCNT up-count/down-count. */
/* I/O Control D (IOD[3:0]) for TPU0.TIORL, TPU3.TIORL, TPU6.TIORL, TPU9.TIOR */
#define _TPU_IOD_DISABLE                (0x00U)   /* Output prohibited */
#define _TPU_IOD_LL                     (0x10U)   /* Initial output is low. Low output at compare match */
#define _TPU_IOD_LH                     (0x20U)   /* Initial output is low. High output at compare match */
#define _TPU_IOD_LT                     (0x30U)   /* Initial output is low. Toggle output at compare match */
#define _TPU_IOD_HL                     (0x50U)   /* Initial output is high. Low output at compare match. */
#define _TPU_IOD_HH                     (0x60U)   /* Initial output is high. High output at compare match. */
#define _TPU_IOD_HT                     (0x70U)   /* Initial output is high. Toggle output at compare match. */
#define _TPU_IOD_IR                     (0x80U)   /* Input capture at rising edge. */
#define _TPU_IOD_IF                     (0x90U)   /* Input capture at falling edge. */
#define _TPU_IOD_IB                     (0xA0U)   /* Input capture at both edges. */
#define _TPU_IOD_EX                     (0xC0U)   /* Input capture at TPU1.TCNT or TPU4.TCNT up-count/down-count
                                                                   or TPU7.TCNT or TPU10.TCNT up-count/down-count. */

/*
    Timer Start Registers (TSTRA)
*/
/* Counter Start 0 (CST0) */
#define _TPU_CST0_OFF                   (0x00U) /* TPU0.TCNT performs count stop */
#define _TPU_CST0_ON                    (0x01U) /* TPU0.TCNT performs count operation */
/* Counter Start 1 (CST1) */
#define _TPU_CST1_OFF                   (0x00U) /* TPU1.TCNT performs count stop */
#define _TPU_CST1_ON                    (0x02U) /* TPU1.TCNT performs count operation */
/* Counter Start 2 (CST2) */
#define _TPU_CST2_OFF                   (0x00U) /* TPU3.TCNT performs count stop */
#define _TPU_CST2_ON                    (0x04U) /* TPU3.TCNT performs count operation */
/* Counter Start 3 (CST3) */
#define _TPU_CST3_OFF                   (0x00U) /* TPU3.TCNT performs count stop */
#define _TPU_CST3_ON                    (0x08U) /* TPU3.TCNT performs count operation */
/* Counter Start 4 (CST4) */
#define _TPU_CST4_OFF                   (0x00U) /* TPU4.TCNT performs count stop */
#define _TPU_CST4_ON                    (0x10U) /* TPU4.TCNT performs count operation */
/* Counter Start 5 (CST5) */
#define _TPU_CST5_OFF                   (0x00U) /* TPU5.TCNT performs count stop */
#define _TPU_CST5_ON                    (0x20U) /* TPU5.TCNT performs count operation */

/*
    Timer Start Registers (TSTRB)
*/
/* Counter Start 6 (CST0) */
#define _TPU_CST6_OFF                   (0x00U) /* TPU6.TCNT performs count stop */
#define _TPU_CST6_ON                    (0x01U) /* TPU6.TCNT performs count operation */
/* Counter Start 7 (CST1) */
#define _TPU_CST7_OFF                   (0x00U) /* TPU7.TCNT performs count stop */
#define _TPU_CST7_ON                    (0x02U) /* TPU7.TCNT performs count operation */
/* Counter Start 8 (CST2) */
#define _TPU_CST8_OFF                   (0x00U) /* TPU8.TCNT performs count stop */
#define _TPU_CST8_ON                    (0x04U) /* TPU8.TCNT performs count operation */
/* Counter Start 9 (CST3) */
#define _TPU_CST9_OFF                   (0x00U) /* TPU9.TCNT performs count stop */
#define _TPU_CST9_ON                    (0x08U) /* TPU9.TCNT performs count operation */
/* Counter Start 10 (CST4) */
#define _TPU_CST10_OFF                  (0x00U) /* TPU10.TCNT performs count stop */
#define _TPU_CST10_ON                   (0x10U) /* TPU10.TCNT performs count operation */
/* Counter Start 11 (CST5) */
#define _TPU_CST11_OFF                  (0x00U) /* TPU11.TCNT performs count stop */
#define _TPU_CST11_ON                   (0x20U) /* TPU11.TCNT performs count operation */

/*
    Noise Filter Control Register (NFCR)
*/
/* Noise Filter A Enable Bit (NFAEN) */
#define _TPU_NFAEN_DISABLE              (0x00U)   /* The noise filter for the TIOCAm pin is disabled */
#define _TPU_NFAEN_ENABLE               (0x01U)   /* The noise filter for the TIOCAm pin is enabled */
/* Noise Filter B Enable Bit (NFBEN) */
#define _TPU_NFBEN_DISABLE              (0x00U)   /* The noise filter for the TIOCBm pin is disabled */
#define _TPU_NFBEN_ENABLE               (0x02U)   /* The noise filter for the TIOCBm pin is enabled */
/* Noise Filter C Enable Bit (NFCEN) */
#define _TPU_NFCEN_DISABLE              (0x00U)   /* The noise filter for the TIOCCm pin is disabled */
#define _TPU_NFCEN_ENABLE               (0x04U)   /* The noise filter for the TIOCCm pin is enabled */
/* Noise Filter D Enable Bit (NFDEN) */
#define _TPU_NFDEN_DISABLE              (0x00U)   /* The noise filter for the TIOCDm pin is disabled */
#define _TPU_NFDEN_ENABLE               (0x08U)   /* The noise filter for the TIOCDm pin is enabled */
/* Noise Filter Clock Select (NFCS[1:0]) */
#define _TPU_NFCS_PCLKD_1               (0x00U)   /* PCLKD/1 */
#define _TPU_NFCS_PCLKD_8               (0x10U)   /* PCLKD/8 */
#define _TPU_NFCS_PCLKD_32              (0x20U)   /* PCLKD/32 */
#define _TPU_NFCS_EXCLK                 (0x30U)   /* The clock source for counting is the external clock */

/*
    PWM Feedback Select Register (PWMFBSLR)
*/
/* TPU (Unit 0) Internal PWM Feedback Enable (TPU0EN)*/
#define _TPU_TPU0EN_DISABLE             (0x00000000UL)   /* Internal PWM feedback input function unit 0 is disabled */
#define _TPU_TPU0EN_ENABLE              (0x00000001UL)   /* Internal PWM feedback input function unit 0 is enabled */
/* Internal PWM Feedback Input Source Select 0 (FBSL0[2:0]) */
#define _TPU0_PWM_SIG_MTU34             (0x00000010UL)   /* PWM output signals of MTU3 and MTU4 */
#define _TPU0_PWM_SIG_MTU67             (0x00000014UL)   /* PWM output signals of MTU6 and MTU7 */
#define _TPU0_PWM_SIG_GPT02             (0x00000018UL)   /* PWM output signals of GPT0 to GPT2 */
/* TPU (Unit 1) Internal PWM Feedback Enable (TPU1EN)*/
#define _TPU_TPU1EN_DISABLE             (0x00000000UL)   /* Internal PWM feedback input function unit 1 is disabled */
#define _TPU_TPU1EN_ENABLE              (0x00000100UL)   /* Internal PWM feedback input function unit 1 is enabled */
/* Internal PWM Feedback Input Source Select 1 (FBSL1[2:0]) */
#define _TPU1_PWM_SIG_MTU34             (0x00001000UL)   /* PWM output signals of MTU3 and MTU4 */
#define _TPU1_PWM_SIG_MTU67             (0x00001400UL)   /* PWM output signals of MTU6 and MTU7 */
#define _TPU1_PWM_SIG_GPT02             (0x00001800UL)   /* PWM output signals of GPT0 to GPT2 */
/*
    Timer Interrupt Enable Register (TIER) 
*/
/* TGR Interrupt Enable A (TGIEA) */
#define _TPU_TGIEA_DISABLE              (0x00U)   /* Interrupt requests TGIA disabled */
#define _TPU_TGIEA_ENABLE               (0x01U)   /* Interrupt requests TGIA enabled */
/* TGR Interrupt Enable B (TGIEB) */
#define _TPU_TGIEB_DISABLE              (0x00U)   /* Interrupt requests TGIB disabled */
#define _TPU_TGIEB_ENABLE               (0x02U)   /* Interrupt requests TGIB enabled */
/* TGR Interrupt Enable C (TGIEC) */
#define _TPU_TGIEC_DISABLE              (0x00U)   /* Interrupt requests TGIC disabled */
#define _TPU_TGIEC_ENABLE               (0x04U)   /* Interrupt requests TGIC enabled */
/* TGR Interrupt Enable D (TGIED) */
#define _TPU_TGIED_DISABLE              (0x00U)   /* Interrupt requests TGID disabled */
#define _TPU_TGIED_ENABLE               (0x08U)   /* Interrupt requests TGID enabled */
/* Overflow Interrupt Enable (TCIEV) */
#define _TPU_TCIEV_DISABLE              (0x00U)   /* Interrupt requests TCIV disabled */
#define _TPU_TCIEV_ENABLE               (0x10U)   /* Interrupt requests TCIV enabled */
/* Underflow Interrupt Enable (TCIEU) */
#define _TPU_TCIEU_DISABLE              (0x00U)   /* Interrupt requests TCIU disabled */
#define _TPU_TCIEU_ENABLE               (0x20U)   /* Interrupt requests TCIU enabled */
/* A/D Converter Start Request Enable (TTGE) */
#define _TPU_TTGE_DISABLE               (0x00U)   /* A/D converter start request generation disabled */
#define _TPU_TTGE_ENABLE                (0x80U)   /* A/D converter start request generation enabled */

/*
    Interrupt Source Priority Register n (PRLn)
*/
/* Interrupt Priority Level Select (PRL[3:0]) */
#define _TPU_PRIORITY_LEVEL0            (0x00000000UL) /* Level 0 (highest) */
#define _TPU_PRIORITY_LEVEL1            (0x00000001UL) /* Level 1 */
#define _TPU_PRIORITY_LEVEL2            (0x00000002UL) /* Level 2 */
#define _TPU_PRIORITY_LEVEL3            (0x00000003UL) /* Level 3 */
#define _TPU_PRIORITY_LEVEL4            (0x00000004UL) /* Level 4 */
#define _TPU_PRIORITY_LEVEL5            (0x00000005UL) /* Level 5 */
#define _TPU_PRIORITY_LEVEL6            (0x00000006UL) /* Level 6 */
#define _TPU_PRIORITY_LEVEL7            (0x00000007UL) /* Level 7 */
#define _TPU_PRIORITY_LEVEL8            (0x00000008UL) /* Level 8 */
#define _TPU_PRIORITY_LEVEL9            (0x00000009UL) /* Level 9 */
#define _TPU_PRIORITY_LEVEL10           (0x0000000AUL) /* Level 10 */
#define _TPU_PRIORITY_LEVEL11           (0x0000000BUL) /* Level 11 */
#define _TPU_PRIORITY_LEVEL12           (0x0000000CUL) /* Level 12 */
#define _TPU_PRIORITY_LEVEL13           (0x0000000DUL) /* Level 13 */
#define _TPU_PRIORITY_LEVEL14           (0x0000000EUL) /* Level 14 */
#define _TPU_PRIORITY_LEVEL15           (0x0000000FUL) /* Level 15 */
#define _TPU_PRIORITY_LEVEL16           (0x00000000UL) /* Level 16 */
#define _TPU_PRIORITY_LEVEL17           (0x00000001UL) /* Level 17 */
#define _TPU_PRIORITY_LEVEL18           (0x00000002UL) /* Level 18 */
#define _TPU_PRIORITY_LEVEL19           (0x00000003UL) /* Level 19 */
#define _TPU_PRIORITY_LEVEL20           (0x00000004UL) /* Level 20 */
#define _TPU_PRIORITY_LEVEL21           (0x00000005UL) /* Level 21 */
#define _TPU_PRIORITY_LEVEL22           (0x00000006UL) /* Level 22 */
#define _TPU_PRIORITY_LEVEL23           (0x00000007UL) /* Level 23 */
#define _TPU_PRIORITY_LEVEL24           (0x00000008UL) /* Level 24 */
#define _TPU_PRIORITY_LEVEL25           (0x00000009UL) /* Level 25 */
#define _TPU_PRIORITY_LEVEL26           (0x0000000AUL) /* Level 26 */
#define _TPU_PRIORITY_LEVEL27           (0x0000000BUL) /* Level 27 */
#define _TPU_PRIORITY_LEVEL28           (0x0000000CUL) /* Level 28 */
#define _TPU_PRIORITY_LEVEL29           (0x0000000DUL) /* Level 29 */
#define _TPU_PRIORITY_LEVEL30           (0x0000000EUL) /* Level 30 */
#define _TPU_PRIORITY_LEVEL31           (0x0000000FUL) /* Level 31 (lowest) */


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* TGRA value channel 9 */
#define _TPU9_TCNTA_VALUE                   (0x0726U)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_TPU_Create(void);
void R_TPU9_Start(void);
void R_TPU9_Stop(void);

/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif