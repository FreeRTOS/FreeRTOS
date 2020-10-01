/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
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
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_smc_interrupt.h
* Version      : 1.1.0
* Device(s)    : R5F572NNHxFB
* Description  : This file implements interrupt setting.
***********************************************************************************************************************/

#ifndef SMC_INTERRUPT_H
#define SMC_INTERRUPT_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/* Priority level of interrupt source. 
 * These macro definitions are used to set the IPR register directly
 */
#define _00_ICU_PRIORITY_LEVEL0                    (0x00U) /* Level 0 (disabled)  */
#define _01_ICU_PRIORITY_LEVEL1                    (0x01U) /* Level 1  */
#define _02_ICU_PRIORITY_LEVEL2                    (0x02U) /* Level 2  */
#define _03_ICU_PRIORITY_LEVEL3                    (0x03U) /* Level 3  */
#define _04_ICU_PRIORITY_LEVEL4                    (0x04U) /* Level 4  */
#define _05_ICU_PRIORITY_LEVEL5                    (0x05U) /* Level 5  */
#define _06_ICU_PRIORITY_LEVEL6                    (0x06U) /* Level 6  */
#define _07_ICU_PRIORITY_LEVEL7                    (0x07U) /* Level 7  */
#define _08_ICU_PRIORITY_LEVEL8                    (0x08U) /* Level 8  */
#define _09_ICU_PRIORITY_LEVEL9                    (0x09U) /* Level 9  */
#define _0A_ICU_PRIORITY_LEVEL10                   (0x0AU) /* Level 10  */
#define _0B_ICU_PRIORITY_LEVEL11                   (0x0BU) /* Level 11  */
#define _0C_ICU_PRIORITY_LEVEL12                   (0x0CU) /* Level 12  */
#define _0D_ICU_PRIORITY_LEVEL13                   (0x0DU) /* Level 13  */
#define _0E_ICU_PRIORITY_LEVEL14                   (0x0EU) /* Level 14  */
#define _0F_ICU_PRIORITY_LEVEL15                   (0x0FU) /* Level 15  */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define FAST_INTERRUPT_VECTOR                      (0)

/* The macro definitions below list the full set of priority levels as selected in the Interrupts tab
 * Please do not modify this file manually
 */
#define ICU_BSC_BUSERR_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPIE0_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RAM_RAMERR_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_FCU_FIFERR_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_FCU_FRDYI_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_SWINT2_PRIORITY                    (_01_ICU_PRIORITY_LEVEL1)
#define ICU_ICU_SWINT_PRIORITY                     (_01_ICU_PRIORITY_LEVEL1)
#define ICU_CMT0_CMI0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMT1_CMI1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW0_CMWI0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW1_CMWI1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_USB0_D0FIFO0_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_USB0_D1FIFO0_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RSPI0_SPRI0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RSPI0_SPTI0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RSPI1_SPRI1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RSPI1_SPTI1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_QSPI_SPRI_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_QSPI_SPTI_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SDHI_SBFAI_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MMCIF_MBFAI_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SSIE0_SSITXI0_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SSIE0_SSIRXI0_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SSIE1_SSIRTI1_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RIIC1_RXI1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RIIC1_TXI1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RIIC0_RXI0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RIIC0_TXI0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RIIC2_RXI2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RIIC2_TXI2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI0_RXI0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI0_TXI0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI1_RXI1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI1_TXI1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI2_RXI2_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI2_TXI2_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ0_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ1_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ2_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ3_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ4_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ5_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ6_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ7_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ8_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ9_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ10_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ11_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ12_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ13_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ14_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_IRQ15_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI3_RXI3_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI3_TXI3_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI4_RXI4_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI4_TXI4_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI5_RXI5_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI5_TXI5_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI6_RXI6_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI6_TXI6_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_LVD1_LVD1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_LVD2_LVD2_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_USB0_USBR0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RTC_ALM_PRIORITY                       (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RTC_PRD_PRIORITY                       (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_IWDT_IWUNI_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_WDT_WUNI_PRIORITY                      (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PDC_PCDFI_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI7_RXI7_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI7_TXI7_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI8_RXI8_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI8_TXI8_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI9_RXI9_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI9_TXI9_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI10_RXI10_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI10_TXI10_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPBE0_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPBL2_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RSPI2_SPRI2_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RSPI2_SPTI2_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPBL0_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPBL1_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPAL0_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ICU_GROUPAL1_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI11_RXI11_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI11_TXI11_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI12_RXI12_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_SCI12_TXI12_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_DMAC_DMAC0I_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_DMAC_DMAC1I_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_DMAC_DMAC2I_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_DMAC_DMAC3I_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_DMAC_DMAC74I_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_OST_OSTDI_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_EXDMAC_EXDMAC0I_PRIORITY               (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_EXDMAC_EXDMAC1I_PRIORITY               (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMT2_CMI2_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMT3_CMI3_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU0_TGI0A_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU0_TGI0B_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU0_TGI0C_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU0_TGI0D_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU0_TCI0V_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU1_TGI1B_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU1_TCI1V_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU1_TCI1U_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU2_TGI2A_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU2_TGI2B_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU2_TCI2V_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU2_TCI2U_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU3_TGI3A_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU3_TGI3B_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU1_TGI1A_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU3_TGI3C_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR0_CMIA0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR0_CMIB0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR0_OVI0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR1_CMIA1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR1_CMIB1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR1_OVI1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR2_CMIA2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR2_CMIB2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR2_OVI2_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR3_CMIA3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR3_CMIB3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TMR3_OVI3_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU3_TGI3D_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU3_TCI3V_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU4_TGI4A_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU4_TGI4B_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU4_TCI4V_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU4_TCI4U_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU5_TGI5A_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU5_TGI5B_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU5_TCI5V_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TPU5_TCI5U_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW0_IC0I0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW0_IC1I0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW0_OC0I0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW0_OC1I0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW1_IC0I1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW1_IC1I1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW1_OC0I1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CMTW1_OC1I1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_RTC_CUP_PRIORITY                       (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN0_RXF0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN0_TXF0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN0_RXM0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN0_TXM0_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN1_RXF1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN1_TXF1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN1_RXM1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_CAN1_TXM1_PRIORITY                     (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_USB0_USBI0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_S12AD_S12ADI_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_S12AD_S12GBADI_PRIORITY                (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_S12AD_S12GCADI_PRIORITY                (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_S12AD1_S12ADI1_PRIORITY                (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_S12AD1_S12GBADI1_PRIORITY              (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_S12AD1_S12GCADI1_PRIORITY              (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ELC_ELSR18I_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_ELC_ELSR19I_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_PROC_BUSY_PRIORITY                (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_ROMOK_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_LONG_PLG_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_TEST_BUSY_PRIORITY                (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_WRRDY0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_WRRDY1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_WRRDY4_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_RDRDY0_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_RDRDY1_PRIORITY                   (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_INTEGRATE_WRRDY_PRIORITY          (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_TSIP_INTEGRATE_RDRDY_PRIORITY          (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PERIB_INTB205_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PERIB_INTB206_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PERIB_INTB207_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU1_TGIA1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TGIA0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TGIB0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TGIC0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TGID0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TCIV0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TGIE0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU0_TGIF0_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU1_TGIB1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU1_TCIV1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU1_TCIU1_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU2_TGIA2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU2_TGIB2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU2_TCIV2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU2_TCIU2_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU3_TGIA3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU3_TGIB3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU3_TGIC3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU3_TGID3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU3_TCIV3_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU4_TGIA4_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU4_TGIB4_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU4_TGIC4_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU4_TGID4_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU4_TCIV4_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU5_TGIU5_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU5_TGIV5_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU5_TGIW5_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU6_TGIA6_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU6_TGIB6_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU6_TGIC6_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU6_TGID6_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU6_TCIV6_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU7_TGIA7_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU7_TGIB7_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU7_TGIC7_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU7_TGID7_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU7_TCIV7_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU8_TGIA8_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU8_TGIB8_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU8_TGIC8_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU8_TGID8_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_MTU8_TCIV8_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_EPTPC_IPLS_PRIORITY                    (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PMGI0_PMGI0I_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PMGI1_PMGI1I_PRIORITY                  (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PERIA_INTA254_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)
#define ICU_PERIA_INTA255_PRIORITY                 (_0F_ICU_PRIORITY_LEVEL15)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_Interrupt_Create(void);
#endif
