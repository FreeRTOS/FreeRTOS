/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/**********************************************************************************************************************
* File Name    : r_sci_rx72n_data.c
* Description  : Functions for using SCI on the RX72N device.
***********************************************************************************************************************
* History : DD.MM.YYYY Version Description
*           30.12.2019 1.00    Initial Release.
***********************************************************************************************************************/

/*****************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "platform.h"

#include "r_sci_rx72n_private.h"

/*****************************************************************************
Macro definitions
******************************************************************************/

/*****************************************************************************
Typedef definitions
******************************************************************************/

/*****************************************************************************
Private global variables and functions
******************************************************************************/

/* BAUD DIVISOR INFO */

/* Asynchronous */
/* BRR = (PCLK/(divisor * baud)) - 1 */
/* when abcs=0 & bgdm=0, divisor = 64*pow(2,2n-1) */
/* when abcs=1 & bgdm=0 OR abcs=0 & bgdm=1, divisor = 32*pow(2,2n-1) */
/* when abcs=1 & bgdm=1, divisor = 16*pow(2,2n-1) */

#if (SCI_CFG_ASYNC_INCLUDED)
/* NOTE: diff than SCI async baud table, but should provide same results */
const baud_divisor_t async_baud[NUM_DIVISORS_ASYNC]=
{
    /* divisor result, abcs, bgdm, n */
    {8,    1, 1, 0},
    {16,   0, 1, 0},
    {32,   0, 0, 0},
    {64,   0, 1, 1},
    {128,  0, 0, 1},
    {256,  0, 1, 2},
    {512,  0, 0, 2},
    {1024, 0, 1, 3},
    {2048, 0, 0, 3}
};
#endif

/* Synchronous and Simple SPI */
/* BRR = (PCLK/(divisor * baud)) - 1 */
/* abcs=0, bdgm=0, divisor = 8*pow(2,2n-1) */

#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
/* NOTE: Identical to SCI sync baud table */
const baud_divisor_t sync_baud[NUM_DIVISORS_SYNC]=
{
    /* divisor result, abcs, bgdm, n */
    {4,   0, 0, 0},
    {16,  0, 0, 1},
    {64,  0, 0, 2},
    {256, 0, 0, 3}
};
#endif


/* CHANNEL MEMORY ALLOCATIONS */

#if SCI_CFG_CH0_INCLUDED

/* rom info */
const sci_ch_rom_t  ch0_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI0,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT31_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI0_TEI0, sci0_tei0_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI0_ERI0, sci0_eri0_isr,
                                BIT0_MASK, BIT1_MASK,
                                &ICU.IPR[IPR_SCI0_RXI0].BYTE,
                                &ICU.IPR[IPR_SCI0_TXI0].BYTE,
                                &ICU.IR[IR_SCI0_RXI0].BYTE,
                                &ICU.IR[IR_SCI0_TXI0].BYTE,
                                &ICU.IER[IER_SCI0_RXI0].BYTE,
                                &ICU.IER[IER_SCI0_TXI0].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT2_MASK, BIT3_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch0_ctrl = {&ch0_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif /* End of SCI_CFG_CH0_INCLUDED */


#if SCI_CFG_CH1_INCLUDED

/* rom info */
const sci_ch_rom_t  ch1_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI1,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT30_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI1_TEI1, sci1_tei1_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI1_ERI1, sci1_eri1_isr,
                                BIT2_MASK, BIT3_MASK,
                                &ICU.IPR[IPR_SCI1_RXI1].BYTE,
                                &ICU.IPR[IPR_SCI1_TXI1].BYTE,
                                &ICU.IR[IR_SCI1_RXI1].BYTE,
                                &ICU.IR[IR_SCI1_TXI1].BYTE,
                                &ICU.IER[IER_SCI1_RXI1].BYTE,
                                &ICU.IER[IER_SCI1_TXI1].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT4_MASK, BIT5_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch1_ctrl = {&ch1_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif /* End of SCI_CFG_CH1_INCLUDED */


#if SCI_CFG_CH2_INCLUDED

/* rom info */
const sci_ch_rom_t  ch2_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI2,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT29_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI2_TEI2, sci2_tei2_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI2_ERI2, sci2_eri2_isr,
                                BIT4_MASK, BIT5_MASK,
                                &ICU.IPR[IPR_SCI2_RXI2].BYTE,
                                &ICU.IPR[IPR_SCI2_TXI2].BYTE,
                                &ICU.IR[IR_SCI2_RXI2].BYTE,
                                &ICU.IR[IR_SCI2_TXI2].BYTE,
                                &ICU.IER[IER_SCI2_RXI2].BYTE,
                                &ICU.IER[IER_SCI2_TXI2].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT6_MASK, BIT7_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch2_ctrl = {&ch2_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif /* End of SCI_CFG_CH2_INCLUDED */


#if SCI_CFG_CH3_INCLUDED

/* rom info */
const sci_ch_rom_t  ch3_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI3,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT28_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI3_TEI3, sci3_tei3_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI3_ERI3, sci3_eri3_isr,
                                BIT6_MASK, BIT7_MASK,
                                &ICU.IPR[IPR_SCI3_RXI3].BYTE,
                                &ICU.IPR[IPR_SCI3_TXI3].BYTE,
                                &ICU.IR[IR_SCI3_RXI3].BYTE,
                                &ICU.IR[IR_SCI3_TXI3].BYTE,
                                &ICU.IER[IER_SCI3_RXI3].BYTE,
                                &ICU.IER[IER_SCI3_TXI3].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT0_MASK, BIT1_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch3_ctrl = {&ch3_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif  /* End of SCI_CFG_CH3_INCLUDED */


#if SCI_CFG_CH4_INCLUDED

/* rom info */
const sci_ch_rom_t  ch4_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI4,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT27_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI4_TEI4, sci4_tei4_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI4_ERI4, sci4_eri4_isr,
                                BIT8_MASK, BIT9_MASK,
                                &ICU.IPR[IPR_SCI4_RXI4].BYTE,
                                &ICU.IPR[IPR_SCI4_TXI4].BYTE,
                                &ICU.IR[IR_SCI4_RXI4].BYTE,
                                &ICU.IR[IR_SCI4_TXI4].BYTE,
                                &ICU.IER[IER_SCI4_RXI4].BYTE,
                                &ICU.IER[IER_SCI4_TXI4].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT2_MASK, BIT3_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch4_ctrl = {&ch4_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif  /* End of SCI_CFG_CH4_INCLUDED */


#if SCI_CFG_CH5_INCLUDED

/* rom info */
const sci_ch_rom_t  ch5_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI5,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT26_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI5_TEI5, sci5_tei5_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI5_ERI5, sci5_eri5_isr,
                                BIT10_MASK, BIT11_MASK,
                                &ICU.IPR[IPR_SCI5_RXI5].BYTE,
                                &ICU.IPR[IPR_SCI5_TXI5].BYTE,
                                &ICU.IR[IR_SCI5_RXI5].BYTE,
                                &ICU.IR[IR_SCI5_TXI5].BYTE,
                                &ICU.IER[IER_SCI5_RXI5].BYTE,
                                &ICU.IER[IER_SCI5_TXI5].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT4_MASK, BIT5_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch5_ctrl = {&ch5_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif /* End of SCI_CFG_CH5_INCLUDED */


#if SCI_CFG_CH6_INCLUDED

/* rom info */
const sci_ch_rom_t  ch6_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI6,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT25_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI6_TEI6, sci6_tei6_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI6_ERI6, sci6_eri6_isr,
                                BIT12_MASK, BIT13_MASK,
                                &ICU.IPR[IPR_SCI6_RXI6].BYTE,
                                &ICU.IPR[IPR_SCI6_TXI6].BYTE,
                                &ICU.IR[IR_SCI6_RXI6].BYTE,
                                &ICU.IR[IR_SCI6_TXI6].BYTE,
                                &ICU.IER[IER_SCI6_RXI6].BYTE,
                                &ICU.IER[IER_SCI6_TXI6].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT6_MASK, BIT7_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch6_ctrl = {&ch6_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKB_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , false
                            , 0
                            , 0
                            , 0
                            , 0
                            #endif
                           };
#endif /* End of SCI_CFG_CH6_INCLUDED */


#if SCI_CFG_CH7_INCLUDED

/* rom info */
const sci_ch_rom_t  ch7_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI7,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT24_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_AL0_SCI7_TEI7, sci7_tei7_isr,
                                #endif
                                BSP_INT_SRC_AL0_SCI7_ERI7, sci7_eri7_isr,
                                BIT22_MASK, BIT23_MASK,
                                &ICU.IPR[IPR_SCI7_RXI7].BYTE,
                                &ICU.IPR[IPR_SCI7_TXI7].BYTE,
                                &ICU.IR[IR_SCI7_RXI7].BYTE,
                                &ICU.IR[IR_SCI7_TXI7].BYTE,
                                &ICU.IER[IER_SCI7_RXI7].BYTE,
                                &ICU.IER[IER_SCI7_TXI7].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENAL0.LONG,
                                BIT2_MASK, BIT3_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch7_ctrl = {&ch7_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKA_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , SCI_CFG_CH7_FIFO_INCLUDED
                            , SCI_CFG_CH7_RX_FIFO_THRESH
                            , SCI_CFG_CH7_RX_FIFO_THRESH
                            , SCI_CFG_CH7_TX_FIFO_THRESH
                            , SCI_CFG_CH7_TX_FIFO_THRESH
                            #endif
                           };
#endif /* End of SCI_CFG_CH7_INCLUDED */


#if SCI_CFG_CH8_INCLUDED

/* rom info */
const sci_ch_rom_t  ch8_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI8,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRC.LONG, BIT27_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_AL0_SCI8_TEI8, sci8_tei8_isr,
                                #endif
                                BSP_INT_SRC_AL0_SCI8_ERI8, sci8_eri8_isr,
                                BIT0_MASK, BIT1_MASK,
                                &ICU.IPR[IPR_SCI8_RXI8].BYTE,
                                &ICU.IPR[IPR_SCI8_TXI8].BYTE,
                                &ICU.IR[IR_SCI8_RXI8].BYTE,
                                &ICU.IR[IR_SCI8_TXI8].BYTE,
                                &ICU.IER[IER_SCI8_RXI8].BYTE,
                                &ICU.IER[IER_SCI8_TXI8].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENAL0.LONG,
                                BIT4_MASK, BIT5_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch8_ctrl = {&ch8_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKA_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , SCI_CFG_CH8_FIFO_INCLUDED
                            , SCI_CFG_CH8_RX_FIFO_THRESH
                            , SCI_CFG_CH8_RX_FIFO_THRESH
                            , SCI_CFG_CH8_TX_FIFO_THRESH
                            , SCI_CFG_CH8_TX_FIFO_THRESH
                            #endif
                           };
#endif /* End of SCI_CFG_CH8_INCLUDED */


#if SCI_CFG_CH9_INCLUDED

/* rom info */
const sci_ch_rom_t  ch9_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI9,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRC.LONG, BIT26_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_AL0_SCI9_TEI9, sci9_tei9_isr,
                                #endif
                                BSP_INT_SRC_AL0_SCI9_ERI9, sci9_eri9_isr,
                                BIT4_MASK, BIT5_MASK,
                                &ICU.IPR[IPR_SCI9_RXI9].BYTE,
                                &ICU.IPR[IPR_SCI9_TXI9].BYTE,
                                &ICU.IR[IR_SCI9_RXI9].BYTE,
                                &ICU.IR[IR_SCI9_TXI9].BYTE,
                                &ICU.IER[IER_SCI9_RXI9].BYTE,
                                &ICU.IER[IER_SCI9_TXI9].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENAL0.LONG,
                                BIT6_MASK, BIT7_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch9_ctrl = {&ch9_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                            #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                            , true, 0, 0, false
                            #endif
                            , BSP_PCLKA_HZ
                            #if SCI_CFG_FIFO_INCLUDED
                            , SCI_CFG_CH9_FIFO_INCLUDED
                            , SCI_CFG_CH9_RX_FIFO_THRESH
                            , SCI_CFG_CH9_RX_FIFO_THRESH
                            , SCI_CFG_CH9_TX_FIFO_THRESH
                            , SCI_CFG_CH9_TX_FIFO_THRESH
                            #endif
                           };
#endif /* End of SCI_CFG_CH9_INCLUDED */


#if SCI_CFG_CH10_INCLUDED

/* rom info */
const sci_ch_rom_t  ch10_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI10,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRC.LONG, BIT25_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_AL0_SCI10_TEI10, sci10_tei10_isr,
                                #endif
                                BSP_INT_SRC_AL0_SCI10_ERI10, sci10_eri10_isr,
                                BIT8_MASK, BIT9_MASK,
                                &ICU.IPR[IPR_SCI10_RXI10].BYTE,
                                &ICU.IPR[IPR_SCI10_TXI10].BYTE,
                                &ICU.IR[IR_SCI10_RXI10].BYTE,
                                &ICU.IR[IR_SCI10_TXI10].BYTE,
                                &ICU.IER[IER_SCI10_RXI10].BYTE,
                                &ICU.IER[IER_SCI10_TXI10].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENAL0.LONG,
                                BIT0_MASK, BIT1_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch10_ctrl = {&ch10_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                             #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                             , true, 0, 0, false
                             #endif
                             , BSP_PCLKA_HZ
                             #if SCI_CFG_FIFO_INCLUDED
                             , SCI_CFG_CH10_FIFO_INCLUDED
                             , SCI_CFG_CH10_RX_FIFO_THRESH
                             , SCI_CFG_CH10_RX_FIFO_THRESH
                             , SCI_CFG_CH10_TX_FIFO_THRESH
                             , SCI_CFG_CH10_TX_FIFO_THRESH
                             #endif
                            };
#endif /* End of SCI_CFG_CH10_INCLUDED */


#if SCI_CFG_CH11_INCLUDED

/* rom info */
const sci_ch_rom_t  ch11_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI11,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRC.LONG, BIT24_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_AL0_SCI11_TEI11, sci11_tei11_isr,
                                #endif
                                BSP_INT_SRC_AL0_SCI11_ERI11, sci11_eri11_isr,
                                BIT12_MASK, BIT13_MASK,
                                &ICU.IPR[IPR_SCI11_RXI11].BYTE,
                                &ICU.IPR[IPR_SCI11_TXI11].BYTE,
                                &ICU.IR[IR_SCI11_RXI11].BYTE,
                                &ICU.IR[IR_SCI11_TXI11].BYTE,
                                &ICU.IER[IER_SCI11_RXI11].BYTE,
                                &ICU.IER[IER_SCI11_TXI11].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENAL0.LONG,
                                BIT2_MASK, BIT3_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch11_ctrl = {&ch11_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                             #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                             , true, 0, 0, false
                             #endif
                             , BSP_PCLKA_HZ
                             #if SCI_CFG_FIFO_INCLUDED
                             , SCI_CFG_CH11_FIFO_INCLUDED
                             , SCI_CFG_CH11_RX_FIFO_THRESH
                             , SCI_CFG_CH11_RX_FIFO_THRESH
                             , SCI_CFG_CH11_TX_FIFO_THRESH
                             , SCI_CFG_CH11_TX_FIFO_THRESH
                             #endif
                            };
#endif /* End of SCI_CFG_CH11_INCLUDED */


#if SCI_CFG_CH12_INCLUDED

/* rom info */
const sci_ch_rom_t  ch12_rom = {(volatile struct st_sci7 R_BSP_EVENACCESS_SFR  *)&SCI12,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&SYSTEM.MSTPCRB.LONG, BIT4_MASK,
                                #if SCI_CFG_TEI_INCLUDED
                                    BSP_INT_SRC_BL0_SCI12_TEI12, sci12_tei12_isr,
                                #endif
                                BSP_INT_SRC_BL0_SCI12_ERI12, sci12_eri12_isr,
                                BIT16_MASK, BIT17_MASK,
                                &ICU.IPR[IPR_SCI12_RXI12].BYTE,
                                &ICU.IPR[IPR_SCI12_TXI12].BYTE,
                                &ICU.IR[IR_SCI12_RXI12].BYTE,
                                &ICU.IR[IR_SCI12_TXI12].BYTE,
                                &ICU.IER[IER_SCI12_RXI12].BYTE,
                                &ICU.IER[IER_SCI12_TXI12].BYTE,
                                (volatile uint32_t R_BSP_EVENACCESS_SFR*)&ICU.GENBL0.LONG,
                                BIT4_MASK, BIT5_MASK
                                };

/* channel control block */
sci_ch_ctrl_t   ch12_ctrl = {&ch12_rom, SCI_MODE_OFF, 0, NULL, NULL, NULL, true
                             #if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
                             , true, 0, 0, false
                             #endif
                             , BSP_PCLKB_HZ
                             #if SCI_CFG_FIFO_INCLUDED
                             , false
                             , 0
                             , 0
                             , 0
                             , 0
                             #endif
                            };
#endif /* End of SCI_CFG_CH12_INCLUDED */


/* SCI HANDLE-ARRAY DECLARATION */

const sci_hdl_t g_handles[SCI_NUM_CH] =
{
#if SCI_CFG_CH0_INCLUDED
            &ch0_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH1_INCLUDED
            &ch1_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH2_INCLUDED
            &ch2_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH3_INCLUDED
            &ch3_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH4_INCLUDED
            &ch4_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH5_INCLUDED
            &ch5_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH6_INCLUDED
            &ch6_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH7_INCLUDED
            &ch7_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH8_INCLUDED
            &ch8_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH9_INCLUDED
            &ch9_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH10_INCLUDED
            &ch10_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH11_INCLUDED
            &ch11_ctrl,
#else
            NULL,
#endif
#if SCI_CFG_CH12_INCLUDED
            &ch12_ctrl
#else
            NULL
#endif
};

