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
* File Name    : r_cg_icu.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for ICU module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef ICU_H
#define ICU_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/*
    DMAC Software Activation Register (DMASTG)
*/
/* DMA Unit 0 Software Activation (DMREQ0) */
#define _DMA_UNIT0_SOFTWARE_ACTIVATION_DISABLE      (0x00U) /* DMA transfer is not requested for DMA Unit 0*/
#define _DMA_UNIT0_SOFTWARE_ACTIVATION_ENABLE       (0x01U) /* DMA transfer is requested for DMA Unit 0 */
/* DMA Unit 1 Software Activation (DMREQ1) */
#define _DMA_UNIT1_SOFTWARE_ACTIVATION_DISABLE      (0x00U) /* DMA transfer is not requested for DMA Unit 1*/
#define _DMA_UNIT1_SOFTWARE_ACTIVATION_ENABLE       (0x02U) /* DMA transfer is requested for DMA Unit 1*/

/*
    IRQ Control Register i (IRQCRi) (i = 0 to 15)
*/
/* IRQ Detection Sense Select (IRQMD[1:0]) */
#define _ICU_IRQ_EDGE_LOW_LEVEL                     (0x00U) /* Low level */
#define _ICU_IRQ_EDGE_FALLING                       (0x01U) /* Falling edge */
#define _ICU_IRQ_EDGE_RISING                        (0x02U) /* Rising edge */
#define _ICU_IRQ_EDGE_BOTH                          (0x03U) /* Rising and falling edge */

/*
    IRQ Pin Digital Noise Filter Enable Register 0 (IRQFLTE)
*/
/* IRQn Digital Noise Filter Enable (FLTEN0n) */
#define _ICU_IRQn_FILTER_DISABLE                    (0x00000000UL) /* IRQn digital noise filter is disabled */
#define _ICU_IRQ0_FILTER_ENABLE                     (0x00000001UL) /* IRQ0 digital noise filter is enabled */
#define _ICU_IRQ1_FILTER_ENABLE                     (0x00000002UL) /* IRQ1 digital noise filter is enabled */
#define _ICU_IRQ2_FILTER_ENABLE                     (0x00000004UL) /* IRQ2 digital noise filter is enabled */
#define _ICU_IRQ3_FILTER_ENABLE                     (0x00000008UL) /* IRQ3 digital noise filter is enabled */
#define _ICU_IRQ4_FILTER_ENABLE                     (0x00000010UL) /* IRQ4 digital noise filter is enabled */
#define _ICU_IRQ5_FILTER_ENABLE                     (0x00000020UL) /* IRQ5 digital noise filter is enabled */
#define _ICU_IRQ6_FILTER_ENABLE                     (0x00000040UL) /* IRQ6 digital noise filter is enabled */
#define _ICU_IRQ7_FILTER_ENABLE                     (0x00000080UL) /* IRQ7 digital noise filter is enabled */
#define _ICU_IRQ8_FILTER_ENABLE                     (0x00000100UL) /* IRQ8 digital noise filter is enabled */
#define _ICU_IRQ9_FILTER_ENABLE                     (0x00000200UL) /* IRQ9 digital noise filter is enabled */
#define _ICU_IRQ10_FILTER_ENABLE                    (0x00000400UL) /* IRQ10 digital noise filter is enabled */
#define _ICU_IRQ11_FILTER_ENABLE                    (0x00000800UL) /* IRQ11 digital noise filter is enabled */
#define _ICU_IRQ12_FILTER_ENABLE                    (0x00001000UL) /* IRQ12 digital noise filter is enabled */
#define _ICU_IRQ13_FILTER_ENABLE                    (0x00002000UL) /* IRQ13 digital noise filter is enabled */
#define _ICU_IRQ14_FILTER_ENABLE                    (0x00004000UL) /* IRQ14 digital noise filter is enabled */
#define _ICU_IRQ15_FILTER_ENABLE                    (0x00008000UL) /* IRQ15 digital noise filter is enabled */

/*
    IRQ Pin Digital Filter Setting Register (IRQFLTC)
*/
/* IRQn Digital Filter Sampling Clock (FCLKSELn[1:0]) */
#define _ICU_IRQ0_FILTER_PCLKB                      (0x00U) /* IRQ0 sample clock run at every PCLKB cycle */
#define _ICU_IRQ0_FILTER_PCLKB_8                    (0x01U) /* IRQ0 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ0_FILTER_PCLKB_32                   (0x02U) /* IRQ0 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ0_FILTER_PCLKB_64                   (0x03U) /* IRQ0 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ1_FILTER_PCLKB                      (0x00U) /* IRQ1 sample clock run at every PCLKB cycle */
#define _ICU_IRQ1_FILTER_PCLKB_8                    (0x01U) /* IRQ1 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ1_FILTER_PCLKB_32                   (0x02U) /* IRQ1 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ1_FILTER_PCLKB_64                   (0x03U) /* IRQ1 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ2_FILTER_PCLKB                      (0x00U) /* IRQ2 sample clock run at every PCLKB cycle */
#define _ICU_IRQ2_FILTER_PCLKB_8                    (0x01U) /* IRQ2 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ2_FILTER_PCLKB_32                   (0x02U) /* IRQ2 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ2_FILTER_PCLKB_64                   (0x03U) /* IRQ2 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ3_FILTER_PCLKB                      (0x00U) /* IRQ3 sample clock run at every PCLKB cycle */
#define _ICU_IRQ3_FILTER_PCLKB_8                    (0x01U) /* IRQ3 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ3_FILTER_PCLKB_32                   (0x02U) /* IRQ3 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ3_FILTER_PCLKB_64                   (0x03U) /* IRQ3 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ4_FILTER_PCLKB                      (0x00U) /* IRQ4 sample clock run at every PCLKB cycle */
#define _ICU_IRQ4_FILTER_PCLKB_8                    (0x01U) /* IRQ4 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ4_FILTER_PCLKB_32                   (0x02U) /* IRQ4 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ4_FILTER_PCLKB_64                   (0x03U) /* IRQ4 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ5_FILTER_PCLKB                      (0x00U) /* IRQ5 sample clock run at every PCLKB cycle */
#define _ICU_IRQ5_FILTER_PCLKB_8                    (0x01U) /* IRQ5 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ5_FILTER_PCLKB_32                   (0x02U) /* IRQ5 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ5_FILTER_PCLKB_64                   (0x03U) /* IRQ5 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ6_FILTER_PCLKB                      (0x00U) /* IRQ6 sample clock run at every PCLKB cycle */
#define _ICU_IRQ6_FILTER_PCLKB_8                    (0x01U) /* IRQ6 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ6_FILTER_PCLKB_32                   (0x02U) /* IRQ6 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ6_FILTER_PCLKB_64                   (0x03U) /* IRQ6 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ7_FILTER_PCLKB                      (0x00U) /* IRQ7 sample clock run at every PCLKB cycle */
#define _ICU_IRQ7_FILTER_PCLKB_8                    (0x01U) /* IRQ7 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ7_FILTER_PCLKB_32                   (0x02U) /* IRQ7 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ7_FILTER_PCLKB_64                   (0x03U) /* IRQ7 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ8_FILTER_PCLKB                      (0x00U) /* IRQ8 sample clock run at every PCLKB cycle */
#define _ICU_IRQ8_FILTER_PCLKB_8                    (0x01U) /* IRQ8 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ8_FILTER_PCLKB_32                   (0x02U) /* IRQ8 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ8_FILTER_PCLKB_64                   (0x03U) /* IRQ8 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ9_FILTER_PCLKB                      (0x00U) /* IRQ9 sample clock run at every PCLKB cycle */
#define _ICU_IRQ9_FILTER_PCLKB_8                    (0x01U) /* IRQ9 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ9_FILTER_PCLKB_32                   (0x02U) /* IRQ9 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ9_FILTER_PCLKB_64                   (0x03U) /* IRQ9 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ10_FILTER_PCLKB                     (0x00U) /* IRQ10 sample clock run at every PCLKB cycle */
#define _ICU_IRQ10_FILTER_PCLKB_8                   (0x01U) /* IRQ10 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ10_FILTER_PCLKB_32                  (0x02U) /* IRQ10 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ10_FILTER_PCLKB_64                  (0x03U) /* IRQ10 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ11_FILTER_PCLKB                     (0x00U) /* IRQ11 sample clock run at every PCLKB cycle */
#define _ICU_IRQ11_FILTER_PCLKB_8                   (0x01U) /* IRQ11 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ11_FILTER_PCLKB_32                  (0x02U) /* IRQ11 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ11_FILTER_PCLKB_64                  (0x03U) /* IRQ11 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ12_FILTER_PCLKB                     (0x00U) /* IRQ12 sample clock run at every PCLKB cycle */
#define _ICU_IRQ12_FILTER_PCLKB_8                   (0x01U) /* IRQ12 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ12_FILTER_PCLKB_32                  (0x02U) /* IRQ12 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ12_FILTER_PCLKB_64                  (0x03U) /* IRQ12 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ13_FILTER_PCLKB                     (0x00U) /* IRQ13 sample clock run at every PCLKB cycle */
#define _ICU_IRQ13_FILTER_PCLKB_8                   (0x01U) /* IRQ13 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ13_FILTER_PCLKB_32                  (0x02U) /* IRQ13 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ13_FILTER_PCLKB_64                  (0x03U) /* IRQ13 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ14_FILTER_PCLKB                     (0x00U) /* IRQ14 sample clock run at every PCLKB cycle */
#define _ICU_IRQ14_FILTER_PCLKB_8                   (0x01U) /* IRQ14 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ14_FILTER_PCLKB_32                  (0x02U) /* IRQ14 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ14_FILTER_PCLKB_64                  (0x03U) /* IRQ14 sample clock run at every PCLKB/64 cycle */
#define _ICU_IRQ15_FILTER_PCLKB                     (0x00U) /* IRQ15 sample clock run at every PCLKB cycle */
#define _ICU_IRQ15_FILTER_PCLKB_8                   (0x01U) /* IRQ15 sample clock run at every PCLKB/8 cycle */
#define _ICU_IRQ15_FILTER_PCLKB_32                  (0x02U) /* IRQ15 sample clock run at every PCLKB/32 cycle */
#define _ICU_IRQ15_FILTER_PCLKB_64                  (0x03U) /* IRQ15 sample clock run at every PCLKB/64 cycle */

/*
    Interrupt Source Priority Register n (IPRn)
*/
/* Interrupt Priority Level Select (IPR[3:0]) */
#define _ICU_PRIORITY_LEVEL0                        (0x00000000UL) /* Level 0 (interrupt disabled) */
#define _ICU_PRIORITY_LEVEL1                        (0x00000001UL) /* Level 1 */
#define _ICU_PRIORITY_LEVEL2                        (0x00000002UL) /* Level 2 */
#define _ICU_PRIORITY_LEVEL3                        (0x00000003UL) /* Level 3 */
#define _ICU_PRIORITY_LEVEL4                        (0x00000004UL) /* Level 4 */
#define _ICU_PRIORITY_LEVEL5                        (0x00000005UL) /* Level 5 */
#define _ICU_PRIORITY_LEVEL6                        (0x00000006UL) /* Level 6 */
#define _ICU_PRIORITY_LEVEL7                        (0x00000007UL) /* Level 7 */
#define _ICU_PRIORITY_LEVEL8                        (0x00000008UL) /* Level 8 */
#define _ICU_PRIORITY_LEVEL9                        (0x00000009UL) /* Level 9 */
#define _ICU_PRIORITY_LEVEL10                       (0x0000000AUL) /* Level 10 */
#define _ICU_PRIORITY_LEVEL11                       (0x0000000BUL) /* Level 11 */
#define _ICU_PRIORITY_LEVEL12                       (0x0000000CUL) /* Level 12 */
#define _ICU_PRIORITY_LEVEL13                       (0x0000000DUL) /* Level 13 */
#define _ICU_PRIORITY_LEVEL14                       (0x0000000EUL) /* Level 14 */
#define _ICU_PRIORITY_LEVEL15                       (0x0000000FUL) /* Level 15 (highest) */

/*
    NMI Pin Interrupt Control Register (NMICR)
*/
/* NMI Detection Sense Selection (NMIMD) */
#define _ICU_NMI_DETECTION_SENSE_FALLING            (0x00U) /* Falling edge */
#define _ICU_NMI_DETECTION_SENSE_RISING             (0x08U) /* Rising edge */

/*
    DMA Noise Filter Setting Register (DMAINT)
*/
/* DMA Digital Noise Filter Sampling Clock (DREQFLTC[1:0]) */
#define _ICU_DMAINT0_FILTER_PCLKB                   (0x00U) /* NMI sample clock is run at every PCLKB cycle */
#define _ICU_DMAINT0_FILTER_PCLKB_8                 (0x01U) /* NMI sample clock is run at every PCLKB/8 cycle */
#define _ICU_DMAINT0_FILTER_PCLKB_32                (0x02U) /* NMI sample clock is run at every PCLKB/32 cycle */
#define _ICU_DMAINT0_FILTER_PCLKB_64                (0x03U) /* NMI sample clock is run at every PCLKB/64 cycle */
#define _ICU_DMAINT1_FILTER_PCLKB                   (0x00U) /* NMI sample clock is run at every PCLKB cycle */
#define _ICU_DMAINT1_FILTER_PCLKB_8                 (0x01U) /* NMI sample clock is run at every PCLKB/8 cycle */
#define _ICU_DMAINT1_FILTER_PCLKB_32                (0x02U) /* NMI sample clock is run at every PCLKB/32 cycle */
#define _ICU_DMAINT1_FILTER_PCLKB_64                (0x03U) /* NMI sample clock is run at every PCLKB/64 cycle */
#define _ICU_DMAINT2_FILTER_PCLKB                   (0x00U) /* NMI sample clock is run at every PCLKB cycle */
#define _ICU_DMAINT2_FILTER_PCLKB_8                 (0x01U) /* NMI sample clock is run at every PCLKB/8 cycle */
#define _ICU_DMAINT2_FILTER_PCLKB_32                (0x02U) /* NMI sample clock is run at every PCLKB/32 cycle */
#define _ICU_DMAINT2_FILTER_PCLKB_64                (0x03U) /* NMI sample clock is run at every PCLKB/64 cycle */

/*
    NMI Pin Digital Noise Filter Setting Register (NMIFLTC)
*/
/* NMI Digital Noise Filter Sampling Clock (NFCLKSEL[1:0]) */
#define _ICU_NMI_FILTER_PCLKB                       (0x00U) /* NMI sample clock is run at every PCLKB cycle */
#define _ICU_NMI_FILTER_PCLKB_8                     (0x01U) /* NMI sample clock is run at every PCLKB/8 cycle */
#define _ICU_NMI_FILTER_PCLKB_32                    (0x02U) /* NMI sample clock is run at every PCLKB/32 cycle */
#define _ICU_NMI_FILTER_PCLKB_64                    (0x03U) /* NMI sample clock is run at every PCLKB/64 cycle */

/*
    EtherPHY Control Register i (EPHYCRi) (i = 0 to 2)
*/
/* EtherPHYn interrupt Detection Setting (EPHYMD[1:0]) */
#define _ICU_ETHERPHY0_EDGE_LOW_LEVEL               (0x00U) /* Low level */
#define _ICU_ETHERPHY0_EDGE_FALLING                 (0x01U) /* Falling edge */
#define _ICU_ETHERPHY0_EDGE_RISING                  (0x02U) /* Rising edge */
#define _ICU_ETHERPHY0_EDGE_BOTH                    (0x03U) /* Rising and falling edge */
#define _ICU_ETHERPHY1_EDGE_LOW_LEVEL               (0x00U) /* Low level */
#define _ICU_ETHERPHY1_EDGE_FALLING                 (0x01U) /* Falling edge */
#define _ICU_ETHERPHY1_EDGE_RISING                  (0x02U) /* Rising edge */
#define _ICU_ETHERPHY1_EDGE_BOTH                    (0x03U) /* Rising and falling edge */
#define _ICU_ETHERPHY2_EDGE_LOW_LEVEL               (0x00U) /* Low level */
#define _ICU_ETHERPHY2_EDGE_FALLING                 (0x01U) /* Falling edge */
#define _ICU_ETHERPHY2_EDGE_RISING                  (0x02U) /* Rising edge */
#define _ICU_ETHERPHY2_EDGE_BOTH                    (0x03U) /* Rising and falling edge */

/*
    EtherPHY Interrupt Request Pin Digital Noise Filter Enable Register 0 (EPHYFLTE)
*/
/* EtherPHYn Interrupt Digital Noise Filter Enable (EFLTENn) */
#define _ICU_ETHERPHYn_FILTER_DISABLE              (0x00U) /* ETHER PHY0 digital noise filter is disabled */
#define _ICU_ETHERPHY0_FILTER_ENABLE               (0x01U) /* ETHER PHY0 digital noise filter is enabled */
#define _ICU_ETHERPHY1_FILTER_ENABLE               (0x01U) /* ETHER PHY1 digital noise filter is enabled */
#define _ICU_ETHERPHY2_FILTER_ENABLE               (0x01U) /* ETHER PHY2 digital noise filter is enabled */

/*
    EtherPHY Interrupt Request Pin Digital Filter Setting Register (EPHYFLTC)
*/
/* EtherPHYn Interrupts Digital Noise Filter Sampling Clock (EFCLKSELn[1:0]) */
#define _ICU_ETHPHYI0_FILTER_PCLKB                 (0x00U) /* ETHER PHY0 sample clock is run at every PCLKB cycle */
#define _ICU_ETHPHYI0_FILTER_PCLKB_8               (0x01U) /* ETHER PHY0 sample clock is run at every PCLKB/8 cycle */
#define _ICU_ETHPHYI0_FILTER_PCLKB_32              (0x02U) /* ETHER PHY0 sample clock is run at every PCLKB/32 cycle */
#define _ICU_ETHPHYI0_FILTER_PCLKB_64              (0x03U) /* ETHER PHY0 sample clock is run at every PCLKB/64 cycle */
#define _ICU_ETHPHYI1_FILTER_PCLKB                 (0x00U) /* ETHER PHY1 sample clock is run at every PCLKB cycle */
#define _ICU_ETHPHYI1_FILTER_PCLKB_8               (0x01U) /* ETHER PHY1 sample clock is run at every PCLKB/8 cycle */
#define _ICU_ETHPHYI1_FILTER_PCLKB_32              (0x02U) /* ETHER PHY1 sample clock is run at every PCLKB/32 cycle */
#define _ICU_ETHPHYI1_FILTER_PCLKB_64              (0x03U) /* ETHER PHY1 sample clock is run at every PCLKB/64 cycle */
#define _ICU_ETHPHYI2_FILTER_PCLKB                 (0x00U) /* ETHER PHY2 sample clock is run at every PCLKB cycle */
#define _ICU_ETHPHYI2_FILTER_PCLKB_8               (0x01U) /* ETHER PHY2 sample clock is run at every PCLKB/8 cycle */
#define _ICU_ETHPHYI2_FILTER_PCLKB_32              (0x02U) /* ETHER PHY2 sample clock is run at every PCLKB/32 cycle */
#define _ICU_ETHPHYI2_FILTER_PCLKB_64              (0x03U) /* ETHER PHY2 sample clock is run at every PCLKB/64 cycle */

/*
    External DMA Request Pin Digital Noise Enable Register (DREQFLTE)
*/
/* DREQn Digital Noise Filter Enable (DFLTENn) */
#define _ICU_DREQn_FILTER_DISABLE                 (0x00U) /* Digital noise filter is disabled */
#define _ICU_DREQ0_FILTER_ENABLE                  (0x01U) /* DREQ0 Digital noise filter is enabled */
#define _ICU_DREQ1_FILTER_ENABLE                  (0x01U) /* DREQ1 Digital noise filter is enabled */
#define _ICU_DREQ2_FILTER_ENABLE                  (0x01U) /* DREQ2 Digital noise filter is enabled */

/*
    External DMA Request Pin Digital Noise Setting Register (DREQFLTC)
*/
/* DREQn Digital Noise Filter Sampling Clock (DFCLKSELn[1:0]) */
#define _ICU_DREQ0_FILTER_PCLKB                   (0x00U) /* DREQ0 sample clock is run at every PCLKB cycle */
#define _ICU_DREQ0_FILTER_PCLKB_8                 (0x01U) /* DREQ0 sample clock is run at every PCLKB/8 cycle */
#define _ICU_DREQ0_FILTER_PCLKB_32                (0x02U) /* DREQ0 sample clock is run at every PCLKB/32 cycle */
#define _ICU_DREQ0_FILTER_PCLKB_64                (0x03U) /* DREQ0 sample clock is run at every PCLKB/64 cycle */
#define _ICU_DREQ1_FILTER_PCLKB                   (0x00U) /* DREQ1 sample clock is run at every PCLKB cycle */
#define _ICU_DREQ1_FILTER_PCLKB_8                 (0x01U) /* DREQ1 sample clock is run at every PCLKB/8 cycle */
#define _ICU_DREQ1_FILTER_PCLKB_32                (0x02U) /* DREQ1 sample clock is run at every PCLKB/32 cycle */
#define _ICU_DREQ1_FILTER_PCLKB_64                (0x03U) /* DREQ1 sample clock is run at every PCLKB/64 cycle */
#define _ICU_DREQ2_FILTER_PCLKB                   (0x00U) /* DREQ2 sample clock is run at every PCLKB cycle */
#define _ICU_DREQ2_FILTER_PCLKB_8                 (0x01U) /* DREQ2 sample clock is run at every PCLKB/8 cycle */
#define _ICU_DREQ2_FILTER_PCLKB_32                (0x02U) /* DREQ2 sample clock is run at every PCLKB/32 cycle */
#define _ICU_DREQ2_FILTER_PCLKB_64                (0x03U) /* DREQ2 sample clock is run at every PCLKB/64 cycle */

/*
    User Mode Enable Register 0 (UEN0)
*/
/* Interrupt control register access selection (UE) */
#define _ICU_UEN0_CTRL_REG_ACCESS_DISABLE         (0x00000000UL) /* Disables access in user mode. */
#define _ICU_UEN0_CTRL_REG_ACCESS_ENABLE          (0x00000001UL) /* Enables access in user mode. */

/*
    User Mode Enable Register 1 (UEN1)
*/
/* Interrupt control register access selection (UE) */
#define _ICU_UEN1_CTRL_REG_ACCESS_DISABLE         (0x00000000UL) /* Disables access in user mode. */
#define _ICU_UEN1_CTRL_REG_ACCESS_ENABLE          (0x00000001UL) /* Enables access in user mode. */


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_ICU_Create(void);
void R_ICU_IRQ12_Start(void);
void R_ICU_IRQ12_Stop(void);

/* Start user code for function. Do not edit comment generated here */

#define SW1_PRESS_FLG           (0x01)
#define SW2_PRESS_FLG           (0x02)
#define SW3_PRESS_FLG           (0x04)

#define SW1_HELD_FLG            (0x10)
#define SW2_HELD_FLG            (0x20)
#define SW3_HELD_FLG            (0x40)

#define SW1_SET_FLG_MASK        (0xEE)
#define SW2_SET_FLG_MASK        (0xDD)
#define SW3_SET_FLG_MASK        (0xBB)

#define SW_ALL_OFF              (0xF8)

#define SW1_INPUT_STATE         (PORT3.PIDR.BIT.B5)
#define SW2_INPUT_STATE         (PORTN.PIDR.BIT.B5)
#define SW3_INPUT_STATE         (PORT4.PIDR.BIT.B4)

#define SW1_OUTPUT_PIN          (PORT3.PODR.BIT.B5)
#define SW2_OUTPUT_PIN          (PORTN.PODR.BIT.B5)
#define SW3_OUTPUT_PIN          (PORT4.PODR.BIT.B4)

/* Stores switch states detected via interrupts */
extern volatile uint8_t  g_switch_press_flg;

/* End user code. Do not edit comment generated here */
#endif